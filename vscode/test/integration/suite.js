// What a person would check by hand, asked of VS Code itself: the lenses, hovers and completions it would show,
// the dashboard, and a full build through the extension with the bundled lean2il.
'use strict';
const assert = require('assert');
const path = require('path');
const fs = require('fs');
const vscode = require('vscode');

const root = vscode.workspace.workspaceFolders[0].uri.fsPath;
const leanFile = path.join(root, 'lean', 'Finance', 'Rounding.lean');
const csFile = path.join(root, 'samples', 'Invoice', 'Program.cs');
const proofJson = path.join(root, 'lean', '.lake', 'dotnet', 'Finance.Proven.proof.json');
const sleep = ms => new Promise(r => setTimeout(r, ms));

async function until(what, f, ms = 60000) {
  const end = Date.now() + ms;
  for (;;) {
    const v = await f();
    if (v) return v;
    if (Date.now() > end) throw new Error('timed out waiting for ' + what);
    await sleep(500);
  }
}

const titles = lenses => lenses.map(l => l.command?.title ?? '');
const text = hover => hover.flatMap(h => h.contents).map(c => c.value ?? String(c)).join('\n');

const tests = [
  ['the extension activates', async () => {
    const ext = vscode.extensions.getExtension('keithadler.lean-to-dot-net');
    await ext.activate();
    assert.ok(ext.isActive);
  }],
  ['Lean lenses: the C# signature over each export, and a line for each documented theorem', async () => {
    const uri = vscode.Uri.file(leanFile);
    await vscode.workspace.openTextDocument(uri);
    const lenses = await until('Lean lenses', async () => {
      const l = await vscode.commands.executeCommand('vscode.executeCodeLensProvider', uri);
      return l.some(x => (x.command?.title ?? '').includes('.NET: decimal Round(')) && l;
    });
    const t = titles(lenses);
    assert.ok(t.some(x => x.includes('decimal RoundCents(decimal x)')), 'RoundCents lens');
    assert.ok(t.some(x => x.includes('replayed on the IL: Proven.Round(0.125m, 2, RoundingMode.AwayFromZero) returns 0.13')), 'example lens');
    assert.ok(t.some(x => x.includes('in the .NET docs of Proven.Round')), 'theorem lens');
    const doc = await vscode.workspace.openTextDocument(uri);
    const def = lenses.find(x => (x.command?.title ?? '').includes('.NET: decimal Round('));
    assert.match(doc.lineAt(def.range.start.line).text, /@\[export lean2il_finance_round\]/, 'lens sits on the export line');
  }],
  ['C# lenses and hover on a call', async () => {
    const uri = vscode.Uri.file(csFile);
    const doc = await vscode.workspace.openTextDocument(uri);
    const lenses = await vscode.commands.executeCommand('vscode.executeCodeLensProvider', uri);
    assert.ok(titles(lenses).some(x => x.includes('Proven.Round: proved in Lean, 9 theorems, re-checked by Tenet')));
    const i = doc.getText().indexOf('Proven.Round(0.125m');
    const hover = await vscode.commands.executeCommand('vscode.executeHoverProvider', uri, doc.positionAt(i + 3));
    const h = text(hover);
    assert.match(h, /public static decimal Round\(decimal x, int digits, RoundingMode mode\)/);
    assert.match(h, /Proved examples/);
    assert.match(h, /round_neg/);
  }],
  ['C# completion after Proven. offers the compiled functions with their proofs', async () => {
    const doc = await vscode.workspace.openTextDocument({ language: 'csharp', content: 'using Finance;\nvar x = Proven.' });
    const list = await vscode.commands.executeCommand('vscode.executeCompletionItemProvider', doc.uri, new vscode.Position(1, 15), '.');
    const round = list.items.find(i => (i.label.label ?? i.label) === 'Round');
    assert.ok(round, 'Round offered');
    assert.match(round.label.description, /proved in Lean · 9 theorems/);
    assert.ok(list.items.some(i => (i.label.label ?? i.label) === 'RoundCents'));
  }],
  ['Lean snippets: export and proved-example', async () => {
    const doc = await vscode.workspace.openTextDocument({ language: 'lean4', content: 'expor' });
    const list = await vscode.commands.executeCommand('vscode.executeCompletionItemProvider', doc.uri, new vscode.Position(0, 5));
    assert.ok(list.items.some(i => (i.label.label ?? i.label) === 'Exported function for .NET' || i.kind === vscode.CompletionItemKind.Snippet && /export/.test(i.label.label ?? i.label)), 'export snippet');
  }],
  ['the Proof Dashboard and the Proofs view open', async () => {
    await vscode.commands.executeCommand('lean2dotnet.dashboard');
    await vscode.commands.executeCommand('workbench.view.extension.lean2dotnet');
  }],
  ['after an edit, lenses say they show the last build', async () => {
    const uri = vscode.Uri.file(leanFile);
    const st = fs.statSync(leanFile);
    fs.utimesSync(leanFile, st.atime, new Date(Date.now() + 60000));
    try {
      await vscode.commands.executeCommand('lean2dotnet.refresh');
      const lenses = await until('stale lenses', async () => {
        const l = await vscode.commands.executeCommand('vscode.executeCodeLensProvider', uri);
        return titles(l).some(x => x.startsWith('$(history) last build:')) && l;
      });
      assert.ok(lenses.length > 0);
    } finally {
      fs.utimesSync(leanFile, st.atime, st.mtime);
      await vscode.commands.executeCommand('lean2dotnet.refresh');
    }
  }],
  ['a refused definition lands in the Problems panel on its line', async () => {
    const scratch = path.join(root, 'lean', 'Finance', 'ScratchRec.lean');
    const finance = path.join(root, 'lean', 'Finance.lean');
    const original = fs.readFileSync(finance, 'utf8');
    // Something lean2il still refuses: floating point.
    fs.writeFileSync(scratch, 'namespace Finance\n\n/-- Halves it. -/\n@[export lean2il_scratch_rec]\ndef half (x : Float) : Float := x / 2\n\nend Finance\n');
    fs.writeFileSync(finance, original + 'import Finance.ScratchRec\n');
    const api = vscode.extensions.getExtension('keithadler.lean-to-dot-net').exports;
    try {
      const previous = api.lastBuild;
      await vscode.window.showTextDocument(await vscode.workspace.openTextDocument(vscode.Uri.file(leanFile)));
      await vscode.commands.executeCommand('lean2dotnet.build');
      await until('the failing build', () => api.lastBuild !== previous && api.lastBuild, 300000);
      assert.notEqual(api.lastBuild.code, 0);
      const diags = await until('a diagnostic', () => {
        const d = vscode.languages.getDiagnostics(vscode.Uri.file(scratch));
        return d.length > 0 && d;
      }, 20000);
      assert.match(diags[0].message, /Float is not compiled/);
      assert.equal(diags[0].range.start.line, 3, 'on the @[export] line of half');
    } finally {
      fs.writeFileSync(finance, original);
      fs.rmSync(scratch, { force: true });
    }
  }],
  ['a build through the extension, with the bundled lean2il, writes a new proof.json', async () => {
    const before = fs.statSync(proofJson).mtimeMs;
    await vscode.window.showTextDocument(await vscode.workspace.openTextDocument(vscode.Uri.file(leanFile)));
    const api = vscode.extensions.getExtension('keithadler.lean-to-dot-net').exports;
    const previous = api.lastBuild;
    await vscode.commands.executeCommand('lean2dotnet.build');
    await until('the build', () => api.lastBuild !== previous && api.lastBuild, 300000);
    assert.equal(api.lastBuild.code, 0, api.lastBuild.output.slice(-2000));
    assert.match(api.lastBuild.command, /server[\\/]lean2il\.dll/, 'used the bundled lean2il');
    assert.ok(fs.statSync(proofJson).mtimeMs > before, 'proof.json rewritten');
    const proof = JSON.parse(fs.readFileSync(proofJson, 'utf8'));
    assert.deepEqual(proof.functions.map(f => f.method).sort(), ['Round', 'RoundCents', 'SplitEven']);
    assert.match(proof.differential ?? '', /gave the same answer every time/);
    assert.equal(proof.verdict.Failed, 0);
  }],
];

exports.run = async () => {
  let failed = 0;
  for (const [name, f] of tests) {
    try { await f(); console.log('  ✔ ' + name); }
    catch (e) { failed++; console.log('  ✖ ' + name + '\n      ' + (e.stack || e).toString().split('\n').slice(0, 3).join('\n      ')); }
  }
  console.log(`${tests.length - failed} of ${tests.length} passed`);
  if (failed) throw new Error(`${failed} integration test(s) failed`);
};
