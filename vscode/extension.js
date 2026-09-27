// Lean to .NET: the editor side of lean2il.
//
// lean2il writes <Assembly>.proof.json next to the assembly it emits: which Lean definitions became which .NET
// methods, the documented theorems about each, the proved examples it replayed against the IL, and what Tenet
// said. Everything this extension shows comes from that file, so it shows exactly what the last build proved and
// nothing it merely hopes.
'use strict';
const vscode = require('vscode');
const path = require('path');
const fs = require('fs');
const cp = require('child_process');

/** @type {Map<string, {root: string, dir: string, proof: any}>} Lake project root -> its last build */
const builds = new Map();
let status;
const changed = new vscode.EventEmitter();
const plural = (n, word) => `${n} ${word}${n === 1 ? '' : 's'}`;

function activate(context) {
  status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 50);
  status.command = 'lean2dotnet.openDocs';
  context.subscriptions.push(status, changed);

  context.subscriptions.push(
    vscode.commands.registerCommand('lean2dotnet.build', build),
    vscode.commands.registerCommand('lean2dotnet.openDocs', openDocs),
    vscode.commands.registerCommand('lean2dotnet.reveal', reveal),
    vscode.languages.registerCodeLensProvider({ pattern: '**/*.lean' }, { provideCodeLenses: leanLenses, onDidChangeCodeLenses: changed.event }),
    vscode.languages.registerCodeLensProvider({ language: 'csharp' }, { provideCodeLenses: csharpLenses, onDidChangeCodeLenses: changed.event }),
    vscode.languages.registerHoverProvider({ language: 'csharp' }, { provideHover: csharpHover }),
    vscode.languages.registerHoverProvider({ pattern: '**/*.lean' }, { provideHover: leanHover }),
  );

  const watcher = vscode.workspace.createFileSystemWatcher('**/.lake/dotnet/*.proof.json');
  watcher.onDidCreate(loadAll); watcher.onDidChange(loadAll); watcher.onDidDelete(loadAll);
  context.subscriptions.push(watcher);
  loadAll();
}

// ---------------------------------------------------------------- reading builds

async function lakeRoots() {
  const files = await vscode.workspace.findFiles('**/lakefile.{toml,lean}', '**/.lake/**', 50);
  return [...new Set(files.map(f => path.dirname(f.fsPath)))];
}

async function loadAll() {
  builds.clear();
  for (const root of await lakeRoots()) {
    const dir = path.join(root, '.lake', 'dotnet');
    if (!fs.existsSync(dir)) continue;
    for (const f of fs.readdirSync(dir).filter(f => f.endsWith('.proof.json'))) {
      try {
        builds.set(root, { root, dir, proof: JSON.parse(fs.readFileSync(path.join(dir, f), 'utf8')) });
      } catch { /* a half-written file; the watcher fires again when it is complete */ }
    }
  }
  vscode.commands.executeCommand('setContext', 'lean2dotnet.built', builds.size > 0);
  updateStatus();
  changed.fire();
}

function updateStatus() {
  const b = [...builds.values()][0];
  if (!b) {
    status.text = '$(package) Lean to .NET';
    status.tooltip = 'No assembly built yet. Click to build.';
    status.command = 'lean2dotnet.build';
  } else {
    const v = b.proof.verdict;
    const n = b.proof.functions.length;
    status.text = v.Checked ? `$(verified) ${b.proof.assembly}: Tenet ${v.Declarations.toLocaleString()} ✓` : `$(warning) ${b.proof.assembly}: not re-checked`;
    status.tooltip = new vscode.MarkdownString(
      `**${b.proof.assembly}.dll**: ${n} function${n === 1 ? '' : 's'}, ${b.proof.theorems.length} theorems\n\n` +
      (v.Checked ? `Tenet re-checked ${v.Declarations.toLocaleString()} declarations in ${v.Modules} modules, ${v.Failed} rejected (Lean ${v.lean}, ${v.seconds}s).`
                 : 'Built with --no-check: Tenet did not re-check it.') + '\n\nClick for the API docs.');
    status.command = 'lean2dotnet.openDocs';
  }
  status.show();
}

function allFunctions() {
  return [...builds.values()].flatMap(b => b.proof.functions.map(f => ({ ...f, build: b })));
}

function theorem(b, name) { return b.proof.theorems.find(t => t.name === name); }

// ---------------------------------------------------------------- Lean side

function leanLenses(doc) {
  const lenses = [];
  for (const b of builds.values()) {
    const rel = path.relative(b.root, doc.uri.fsPath).split(path.sep).join('/');
    for (const f of b.proof.functions.filter(f => f.file === rel && f.source)) {
      const line = Math.max(0, f.source.line - 1);
      const range = new vscode.Range(line, 0, line, 0);
      lenses.push(new vscode.CodeLens(range, { title: `$(package) .NET: ${f.signatures[0].replace('public static ', '')}`, command: 'lean2dotnet.openDocs', arguments: [b.root, f.method] }));
      lenses.push(new vscode.CodeLens(range, { title: `$(verified) ${plural(f.theorems.length, 'theorem')} · ${plural(f.examples.length, 'proved example')} replayed on the IL`, command: 'lean2dotnet.openDocs', arguments: [b.root, f.method] }));
    }
    for (const t of b.proof.theorems.filter(t => t.file === rel && t.line && t.about.length)) {
      const range = new vscode.Range(t.line - 1, 0, t.line - 1, 0);
      const calls = b.proof.functions.filter(f => t.about.includes(f.lean)).map(f => f.call).join(', ');
      lenses.push(new vscode.CodeLens(range, { title: `$(verified) in the .NET docs of ${calls}${b.proof.verdict.Checked ? ', re-checked by Tenet' : ''}`, command: 'lean2dotnet.openDocs', arguments: [b.root] }));
    }
  }
  return lenses;
}

function leanHover(doc, pos) {
  const word = doc.getText(doc.getWordRangeAtPosition(pos, /[A-Za-z_][A-Za-z0-9_'.]*/));
  const f = allFunctions().find(f => f.lean === word || f.lean.endsWith('.' + word));
  if (!f || !doc.lineAt(pos.line).text.match(/\bdef\b/)) return;
  return new vscode.Hover(functionMarkdown(f, true));
}

// ---------------------------------------------------------------- C# side

function csharpCalls(doc) {
  const text = doc.getText();
  const out = [];
  for (const f of allFunctions()) {
    const re = new RegExp(`\\b${f.call.replace('.', '\\.')}\\s*\\(`, 'g');
    let m;
    while ((m = re.exec(text))) out.push({ f, offset: m.index, length: f.call.length });
  }
  return out;
}

function csharpLenses(doc) {
  const seen = new Set();
  return csharpCalls(doc).flatMap(({ f, offset }) => {
    const line = doc.positionAt(offset).line;
    if (seen.has(line + f.call)) return [];
    seen.add(line + f.call);
    const v = f.build.proof.verdict;
    return [new vscode.CodeLens(new vscode.Range(line, 0, line, 0), {
      title: `$(verified) ${f.call}: proved in Lean, ${plural(f.theorems.length, 'theorem')}${v.Checked ? ', re-checked by Tenet' : ''}`,
      command: 'lean2dotnet.reveal', arguments: [f.build.root, f.file, f.source && f.source.line],
    })];
  });
}

function csharpHover(doc, pos) {
  const hit = csharpCalls(doc).find(c => {
    const s = doc.positionAt(c.offset), e = doc.positionAt(c.offset + c.length);
    return new vscode.Range(s, e).contains(pos);
  });
  if (!hit) return;
  return new vscode.Hover(functionMarkdown(hit.f, false));
}

// ---------------------------------------------------------------- shared

function functionMarkdown(f, fromLean) {
  const b = f.build;
  const md = new vscode.MarkdownString(undefined, true);
  md.isTrusted = { enabledCommands: ['lean2dotnet.reveal', 'lean2dotnet.openDocs'] };
  md.appendMarkdown(`**${f.call}** · compiled from \`${f.lean}\`\n\n`);
  md.appendCodeblock(f.signatures.join('\n'), 'csharp');
  if (!fromLean && f.doc) md.appendMarkdown(f.doc.split('\n\n')[0] + '\n\n');
  if (f.examples.length) {
    md.appendMarkdown('**Proved examples**, each replayed against the IL:\n');
    md.appendCodeblock(f.examples.map(e => `${e.call}; // ${e.result}`).join('\n'), 'csharp');
  }
  if (f.theorems.length) {
    md.appendMarkdown('**Proved about it**\n\n');
    for (const n of f.theorems) {
      const t = theorem(b, n);
      if (!t) continue;
      const args = encodeURIComponent(JSON.stringify([b.root, t.file, t.line]));
      md.appendMarkdown(`- [\`${n.split('.').pop()}\`](command:lean2dotnet.reveal?${args}): ${t.doc.split('\n\n')[0].replace(/\n/g, ' ')}\n`);
    }
  }
  const v = b.proof.verdict;
  md.appendMarkdown(`\n\n${v.Checked ? `$(verified) Tenet re-checked ${v.Declarations.toLocaleString()} declarations, ${v.Failed} rejected.` : '$(warning) Not re-checked by Tenet (--no-check).'}`);
  return md;
}

async function reveal(root, file, line) {
  if (!file) return;
  const doc = await vscode.workspace.openTextDocument(path.join(root, file));
  const ed = await vscode.window.showTextDocument(doc, { preview: false, viewColumn: vscode.ViewColumn.Beside });
  if (line) {
    const p = new vscode.Position(line - 1, 0);
    ed.selection = new vscode.Selection(p, p);
    ed.revealRange(new vscode.Range(p, p), vscode.TextEditorRevealType.AtTop);
  }
}

async function openDocs(root) {
  const b = (typeof root === 'string' && builds.get(root)) || [...builds.values()][0];
  if (!b) {
    const pick = await vscode.window.showInformationMessage('No .NET assembly has been built from this workspace yet.', 'Build Now');
    if (pick) build();
    return;
  }
  await vscode.commands.executeCommand('markdown.showPreviewToSide', vscode.Uri.file(path.join(b.dir, b.proof.markdown)));
}

// ---------------------------------------------------------------- building

function lean2ilCommand(root) {
  const configured = vscode.workspace.getConfiguration('lean2dotnet').get('lean2ilCommand');
  if (configured) return configured;
  try {
    cp.execSync(process.platform === 'win32' ? 'where lean2il' : 'command -v lean2il', { stdio: 'ignore' });
    return 'lean2il';
  } catch { /* not on the PATH */ }
  for (let d = root; d !== path.dirname(d); d = path.dirname(d)) {
    for (const cfg of ['Release', 'Debug']) {
      const dll = path.join(d, 'src', 'Lean2Il', 'bin', cfg, 'net10.0', 'lean2il.dll');
      if (fs.existsSync(dll)) return `dotnet "${dll}"`;
    }
  }
  return undefined;
}

async function build() {
  const roots = await lakeRoots();
  if (roots.length === 0) {
    vscode.window.showErrorMessage('No Lake project (lakefile.toml or lakefile.lean) in this workspace.');
    return;
  }
  let root = roots[0];
  const active = vscode.window.activeTextEditor?.document.uri.fsPath;
  if (active) root = roots.filter(r => active.startsWith(r + path.sep)).sort((a, b) => b.length - a.length)[0] ?? root;
  const tool = lean2ilCommand(root);
  if (!tool) {
    const pick = await vscode.window.showErrorMessage('lean2il was not found. Install it with ./setup.sh from the lean-to-dot-net repository, or set lean2dotnet.lean2ilCommand.', 'Open Settings');
    if (pick) vscode.commands.executeCommand('workbench.action.openSettings', 'lean2dotnet.lean2ilCommand');
    return;
  }
  const cfg = vscode.workspace.getConfiguration('lean2dotnet');
  const flags = [cfg.get('checkImports') ? '' : '--trust-imports', cfg.get('leanvizUrl') ? `--leanviz "${cfg.get('leanvizUrl')}"` : ''].filter(Boolean).join(' ');
  const task = new vscode.Task({ type: 'shell', task: 'lean2il' }, vscode.TaskScope.Workspace, 'Build .NET assembly', 'Lean to .NET',
    new vscode.ShellExecution(`lake build && ${tool} . ${flags}`, { cwd: root }));
  task.presentationOptions = { reveal: vscode.TaskRevealKind.Always, clear: true, panel: vscode.TaskPanelKind.Dedicated };
  const exec = await vscode.tasks.executeTask(task);
  const done = vscode.tasks.onDidEndTaskProcess(async e => {
    if (e.execution !== exec) return;
    done.dispose();
    await loadAll();
    const b = builds.get(root);
    if (e.exitCode === 0 && b) {
      const ex = b.proof.functions.reduce((n, f) => n + f.examples.length, 0);
      const pick = await vscode.window.showInformationMessage(
        `${b.proof.dll}: ${plural(b.proof.functions.length, 'function')}, ${plural(b.proof.theorems.length, 'theorem')}, ${plural(ex, 'proved example')} replayed on the IL.`, 'Open API Docs');
      if (pick) openDocs(root);
    } else if (e.exitCode !== 0) {
      vscode.window.showErrorMessage('lean2il failed; the terminal says why.');
    }
  });
}

function deactivate() {}

module.exports = { activate, deactivate };
