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
const os = require('os');
const cp = require('child_process');
const lib = require('./lib');

/** @type {Map<string, {root: string, dir: string, proof: any}>} Lake project root -> its last build */
const builds = new Map();
const changed = new vscode.EventEmitter();
const { plural, firstPara, esc, inline } = lib;
let status, diagnostics, tree, dashboard, extensionPath, output, building = false;
/** The last build: what ran, how it ended, what it printed. Returned from activate() for tests and other extensions. */
const api = { lastBuild: undefined };

function activate(context) {
  extensionPath = context.extensionPath;
  output = vscode.window.createOutputChannel('Lean to .NET');
  context.subscriptions.push(output);
  status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 50);
  diagnostics = vscode.languages.createDiagnosticCollection('lean2il');
  tree = new ProofTree();
  context.subscriptions.push(status, diagnostics, changed);

  context.subscriptions.push(
    vscode.window.registerTreeDataProvider('lean2dotnet.proofs', tree),
    vscode.commands.registerCommand('lean2dotnet.build', build),
    vscode.commands.registerCommand('lean2dotnet.dashboard', () => openDashboard(context)),
    vscode.commands.registerCommand('lean2dotnet.openDocs', openDocs),
    vscode.commands.registerCommand('lean2dotnet.refresh', loadAll),
    vscode.commands.registerCommand('lean2dotnet.reveal', reveal),
    vscode.commands.registerCommand('lean2dotnet.copyCall', copyCall),
    vscode.commands.registerCommand('lean2dotnet.openLeanViz', item => item?.url && vscode.env.openExternal(vscode.Uri.parse(item.url))),
    vscode.languages.registerCodeLensProvider({ pattern: '**/*.lean' }, { provideCodeLenses: leanLenses, onDidChangeCodeLenses: changed.event }),
    vscode.languages.registerCodeLensProvider({ language: 'csharp' }, { provideCodeLenses: csharpLenses, onDidChangeCodeLenses: changed.event }),
    vscode.languages.registerHoverProvider({ language: 'csharp' }, { provideHover: csharpHover }),
    vscode.languages.registerHoverProvider({ pattern: '**/*.lean' }, { provideHover: leanHover }),
    vscode.languages.registerCompletionItemProvider({ language: 'csharp' }, { provideCompletionItems: csharpCompletions }, '.'),
    vscode.workspace.onDidSaveTextDocument(doc => {
      if (!doc.fileName.endsWith('.lean')) return;
      for (const b of builds.values()) if (doc.fileName.startsWith(b.root + path.sep)) b.stale = true;
      updateStatus(); tree.refresh(); dashboard?.render(); changed.fire();
      if (vscode.workspace.getConfiguration('lean2dotnet').get('buildOnSave') && !building) build();
    }),
    vscode.workspace.onDidChangeConfiguration(e => e.affectsConfiguration('lean2dotnet') && changed.fire()),
  );

  const watcher = vscode.workspace.createFileSystemWatcher('**/.lake/dotnet/*.proof.json');
  watcher.onDidCreate(loadAll); watcher.onDidChange(loadAll); watcher.onDidDelete(loadAll);
  context.subscriptions.push(watcher);
  loadAll();
  return api;
}

// ---------------------------------------------------------------- reading builds

async function lakeRoots() {
  const files = await vscode.workspace.findFiles('**/lakefile.{toml,lean}', '**/.lake/**', 50);
  return [...new Set(files.map(f => path.dirname(f.fsPath)))];
}

/** @type {Set<string>} roots whose last build from this window failed */
const failed = new Set();

function leanSourceTimes(root) {
  const times = [];
  const walk = dir => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      if (e.name.startsWith('.') || e.name === 'node_modules') continue;
      const p = path.join(dir, e.name);
      if (e.isDirectory()) walk(p);
      else if (e.name.endsWith('.lean')) times.push(fs.statSync(p).mtimeMs);
    }
  };
  try { walk(root); } catch { /* unreadable folders are skipped */ }
  return times;
}

async function loadAll() {
  builds.clear();
  for (const root of await lakeRoots()) {
    const dir = path.join(root, '.lake', 'dotnet');
    if (!fs.existsSync(dir)) continue;
    for (const f of fs.readdirSync(dir).filter(f => f.endsWith('.proof.json'))) {
      try {
        const file = path.join(dir, f);
        const proof = JSON.parse(fs.readFileSync(file, 'utf8'));
        const stale = lib.isStale(fs.statSync(file).mtimeMs, leanSourceTimes(root));
        builds.set(root, { root, dir, proof, stale });
      } catch { /* a half-written file; the watcher fires again when it is complete */ }
    }
  }
  vscode.commands.executeCommand('setContext', 'lean2dotnet.built', builds.size > 0);
  updateStatus();
  tree.refresh();
  dashboard?.render();
  changed.fire();
}

function updateStatus() {
  const b = [...builds.values()][0];
  if (building) {
    status.text = '$(sync~spin) lean2il: re-checking and compiling';
    status.tooltip = 'Tenet is re-checking the proofs; lean2il will then compile and document.';
    status.command = undefined;
  } else if (!b) {
    status.text = '$(package) Lean to .NET';
    status.tooltip = 'No assembly built yet. Click to build.';
    status.command = 'lean2dotnet.build';
  } else if (failed.has(b.root) || b.stale) {
    const why = failed.has(b.root) ? 'the last build failed' : 'the Lean has changed since the last build';
    status.text = `$(history) ${b.proof.assembly}: out of date`;
    status.tooltip = new vscode.MarkdownString(`**${b.proof.dll}** is from an earlier build: ${why}. The lenses, hovers and dashboard show that build.\n\nClick to rebuild.`);
    status.command = 'lean2dotnet.build';
  } else {
    const v = b.proof.verdict;
    status.text = v.Checked ? `$(verified-filled) ${b.proof.assembly}: Tenet ${v.Declarations.toLocaleString()} ✓` : `$(warning) ${b.proof.assembly}: not re-checked`;
    status.tooltip = new vscode.MarkdownString(
      `**${b.proof.dll}**: ${plural(b.proof.functions.length, 'function')}, ${plural(b.proof.theorems.length, 'theorem')}\n\n` +
      verdictText(v) + (b.proof.differential ? '\n\n' + b.proof.differential : '') + '\n\nClick for the Proof Dashboard.');
    status.command = 'lean2dotnet.dashboard';
  }
  status.show();
}

function verdictText(v) {
  return v.Checked
    ? `Tenet, an independent Lean kernel, re-checked ${v.Declarations.toLocaleString()} declarations in ${v.Modules} modules${v.WithImports ? ', Lean\'s own library included' : ''}: ${v.Failed} rejected (Lean ${v.lean}, ${v.seconds}s).`
    : 'Built with --no-check: Tenet did not re-check it.';
}

function allFunctions() {
  return [...builds.values()].flatMap(b => b.proof.functions.map(f => ({ ...f, build: b })));
}

function theoremOf(b, name) { return b.proof.theorems.find(t => t.name === name); }

function exampleTheorems(f) { return new Set(f.examples.map(e => e.theorem)); }

function leanvizUrl(b, t) {
  return t.leanviz || lib.leanvizLink(vscode.workspace.getConfiguration('lean2dotnet').get('leanvizUrl'), t.name);
}

const outOfDate = b => b.stale || failed.has(b.root);

const lensesOn = () => vscode.workspace.getConfiguration('lean2dotnet').get('codeLens');

// ---------------------------------------------------------------- the Proofs view

class ProofTree {
  constructor() { this._e = new vscode.EventEmitter(); this.onDidChangeTreeData = this._e.event; }
  refresh() { this._e.fire(); }

  getTreeItem(n) { return n.item; }

  getChildren(n) {
    if (!n) {
      return [...builds.values()].map(b => {
        const v = b.proof.verdict;
        const item = new vscode.TreeItem(b.proof.dll, vscode.TreeItemCollapsibleState.Expanded);
        item.description = (outOfDate(b) ? 'out of date · ' : '') + (v.Checked ? `Tenet ✓ ${v.Declarations.toLocaleString()} re-checked` : 'not re-checked');
        item.iconPath = v.Checked ? new vscode.ThemeIcon('verified-filled', new vscode.ThemeColor('testing.iconPassed')) : new vscode.ThemeIcon('warning');
        item.tooltip = new vscode.MarkdownString(verdictText(v));
        item.command = { command: 'lean2dotnet.dashboard', title: 'Open Proof Dashboard' };
        return { item, kids: () => b.proof.functions.map(f => functionNode(b, f)) };
      });
    }
    return n.kids ? n.kids() : [];
  }
}

function functionNode(b, f) {
  const ex = exampleTheorems(f);
  const ths = f.theorems.filter(t => !ex.has(t)).sort((a, c) => (theoremOf(b, a)?.line ?? 0) - (theoremOf(b, c)?.line ?? 0));
  const item = new vscode.TreeItem(f.call, vscode.TreeItemCollapsibleState.Expanded);
  item.description = `${plural(ths.length, 'theorem')} · ${plural(f.examples.length, 'example')}`;
  item.iconPath = new vscode.ThemeIcon('symbol-method', new vscode.ThemeColor('symbolIcon.methodForeground'));
  item.tooltip = new vscode.MarkdownString(`**${f.call}** · compiled from \`${f.lean}\`\n\n\`\`\`csharp\n${f.signatures.join('\n')}\n\`\`\`\n\n${firstPara(f.doc)}`);
  item.command = { command: 'lean2dotnet.reveal', title: 'Show in Lean', arguments: [b.root, f.file, f.source?.line] };
  return {
    item,
    kids: () => [
      group(`Proved examples, replayed on the IL`, 'beaker', f.examples.map(e => exampleNode(b, e))),
      group(`Theorems`, 'law', ths.map(n => theoremNode(b, n)).filter(Boolean)),
    ].filter(g => g.count > 0),
  };
}

function group(label, icon, nodes) {
  const item = new vscode.TreeItem(label, vscode.TreeItemCollapsibleState.Expanded);
  item.iconPath = new vscode.ThemeIcon(icon);
  item.description = String(nodes.length);
  return { item, count: nodes.length, kids: () => nodes };
}

function exampleNode(b, e) {
  const t = theoremOf(b, e.theorem);
  const item = new vscode.TreeItem(e.call);
  item.description = `// ${e.result}`;
  item.iconPath = new vscode.ThemeIcon('pass-filled', new vscode.ThemeColor('testing.iconPassed'));
  item.contextValue = 'example';
  item.tooltip = new vscode.MarkdownString(`\`${e.call}\` returns \`${e.result}\`.\n\nProved by \`${e.theorem}\`, and run against the IL on the last build.`);
  item.command = { command: 'lean2dotnet.reveal', title: 'Show in Lean', arguments: [b.root, t?.file, t?.line] };
  return { item, call: e.call };
}

function theoremNode(b, name) {
  const t = theoremOf(b, name);
  if (!t) return undefined;
  const url = leanvizUrl(b, t);
  const item = new vscode.TreeItem(name.split('.').pop());
  item.description = firstPara(t.doc).replace(/\*\*/g, '');
  item.iconPath = new vscode.ThemeIcon('verified', new vscode.ThemeColor('testing.iconPassed'));
  item.contextValue = url ? 'theorem-viz' : 'theorem';
  const md = new vscode.MarkdownString();
  md.appendMarkdown(`**${t.name}**\n\n${firstPara(t.doc)}\n\n`);
  md.appendCodeblock(t.statement, 'lean4');
  md.appendMarkdown(`Rests on: ${t.axioms.length ? t.axioms.map(a => '`' + a + '`').join(', ') : 'no axioms'}`);
  item.tooltip = md;
  item.command = { command: 'lean2dotnet.reveal', title: 'Show in Lean', arguments: [b.root, t.file, t.line] };
  return { item, url };
}

async function copyCall(node) {
  if (!node?.call) return;
  await vscode.env.clipboard.writeText(node.call + ';');
  vscode.window.setStatusBarMessage(`$(copy) Copied ${node.call}`, 2500);
}

// ---------------------------------------------------------------- the Proof Dashboard

function openDashboard(context) {
  if (dashboard) { dashboard.panel.reveal(); dashboard.render(); return; }
  const panel = vscode.window.createWebviewPanel('lean2dotnet.dashboard', 'Proof Dashboard', vscode.ViewColumn.Beside,
    { enableScripts: true, retainContextWhenHidden: true });
  panel.iconPath = vscode.Uri.joinPath(context.extensionUri, 'images', 'icon.png');
  dashboard = { panel, render: () => { panel.webview.html = dashboardHtml(panel.webview); } };
  panel.onDidDispose(() => { dashboard = undefined; });
  panel.webview.onDidReceiveMessage(async m => {
    if (m.type === 'reveal') reveal(m.root, m.file, m.line);
    if (m.type === 'copy') { await vscode.env.clipboard.writeText(m.text); vscode.window.setStatusBarMessage('$(copy) Copied', 2000); }
    if (m.type === 'open') vscode.env.openExternal(vscode.Uri.parse(m.url));
    if (m.type === 'build') build();
    if (m.type === 'docs') openDocs(m.root);
  });
  dashboard.render();
}


function dashboardHtml(webview) {
  const nonce = Math.random().toString(36).slice(2) + Math.random().toString(36).slice(2);
  const csp = `default-src 'none'; style-src 'unsafe-inline'; script-src 'nonce-${nonce}';`;
  const data = (obj) => esc(JSON.stringify(obj));
  let body = '';
  if (builds.size === 0) {
    body = `<div class="empty"><h1>No assembly yet</h1><p>Mark Lean definitions with <code>@[export sym]</code> and build. lean2il re-checks every proof with Tenet, compiles the definitions to IL and writes the docs from the Lean.</p><button data-msg="${data({ type: 'build' })}">Build .NET Assembly</button></div>`;
  }
  for (const b of builds.values()) {
    const p = b.proof, v = p.verdict;
    const nEx = p.functions.reduce((n, f) => n + f.examples.length, 0);
    body += `<header>
      <div class="title"><h1>${esc(p.assembly)}</h1><span class="cls">${esc(p.class)}</span></div>
      <div class="verdict ${v.Checked ? 'ok' : 'warn'}"><span class="dot"></span>${v.Checked ? `Tenet re-checked <b>${v.Declarations.toLocaleString()}</b> declarations in ${v.Modules} modules${v.WithImports ? ', Lean’s library included' : ''}. <b>${v.Failed}</b> rejected.` : 'Not re-checked by Tenet (built with --no-check).'}</div>
      ${p.differential ? `<div class="verdict ok"><span class="dot"></span>${esc(p.differential)}</div>` : ''}
      <div class="stats">
        <div><b>${p.functions.length}</b><span>${p.functions.length === 1 ? 'function' : 'functions'}</span></div>
        <div><b>${p.theorems.length}</b><span>theorems</span></div>
        <div><b>${nEx}</b><span>examples replayed on the IL</span></div>
        <div><b>${esc(v.lean || '')}</b><span>Lean</span></div>
      </div>
      ${outOfDate(b) ? `<div class="verdict warn">This is the last successful build: ${failed.has(b.root) ? 'the latest build failed (see the Problems panel)' : 'the Lean has changed since'}. Rebuild to bring it up to date.</div>` : ''}
      <div class="actions"><button data-msg="${data({ type: 'build' })}">Rebuild</button><button class="secondary" data-msg="${data({ type: 'docs', root: b.root })}">API docs</button></div>
    </header>`;
    for (const f of p.functions) {
      const ex = exampleTheorems(f);
      body += `<section class="fn">
        <div class="fnhead"><h2>${esc(f.call)}</h2><a class="lean" data-msg="${data({ type: 'reveal', root: b.root, file: f.file, line: f.source?.line })}">compiled from <code>${esc(f.lean)}</code></a></div>
        <pre class="sig">${f.signatures.map(esc).join('\n')}</pre>
        <p class="doc">${inline(firstPara(f.doc))}</p>`;
      if (f.examples.length) {
        body += `<h3>Proved examples <span>each run against the DLL when it was built</span></h3><table class="ex">`;
        for (const e of f.examples) {
          const t = theoremOf(b, e.theorem);
          body += `<tr><td class="pass">✓</td><td><code>${esc(e.call)}</code></td><td class="res">${esc(e.result)}</td>
            <td><a data-msg="${data({ type: 'reveal', root: b.root, file: t?.file, line: t?.line })}">${esc(e.theorem.split('.').pop())}</a></td>
            <td><button class="icon" title="Copy" data-msg="${data({ type: 'copy', text: e.call + ';' })}">Copy</button></td></tr>`;
        }
        body += `</table>`;
      }
      const ths = f.theorems.filter(n => !ex.has(n)).map(n => theoremOf(b, n)).filter(Boolean).sort((a, c) => (a.line ?? 0) - (c.line ?? 0));
      if (ths.length) {
        body += `<h3>What is proved about it <span>${ths.length}</span></h3>`;
        for (const t of ths) {
          const url = leanvizUrl(b, t);
          body += `<div class="thm">
            <div class="thmhead"><a class="name" data-msg="${data({ type: 'reveal', root: b.root, file: t.file, line: t.line })}">${esc(t.name.split('.').pop())}</a>
              <span class="axioms">${t.axioms.length ? t.axioms.map(a => `<span class="ax">${esc(a)}</span>`).join('') : '<span class="ax none">no axioms</span>'}</span>
              ${url ? `<a class="viz" data-msg="${data({ type: 'open', url })}">LeanViz ↗</a>` : ''}</div>
            <p>${inline(firstPara(t.doc))}</p>
            <pre class="stmt">${esc(t.statement)}</pre></div>`;
        }
      }
      body += `</section>`;
    }
  }
  return `<!DOCTYPE html><html><head><meta charset="utf-8"><meta http-equiv="Content-Security-Policy" content="${csp}">
<style>
  :root { --ok: var(--vscode-testing-iconPassed, #3fb950); --accent: #9d86ff; }
  body { font-family: var(--vscode-font-family); color: var(--vscode-foreground); background: var(--vscode-editor-background); padding: 20px 28px 60px; max-width: 1100px; line-height: 1.5; }
  code, pre { font-family: var(--vscode-editor-font-family); font-size: calc(var(--vscode-editor-font-size) * 0.95); }
  code { background: var(--vscode-textCodeBlock-background); padding: 1px 5px; border-radius: 4px; }
  a { color: var(--vscode-textLink-foreground); cursor: pointer; text-decoration: none; }
  a:hover { text-decoration: underline; }
  header { border-bottom: 1px solid var(--vscode-panel-border); padding-bottom: 18px; margin-bottom: 8px; }
  .title { display: flex; align-items: baseline; gap: 14px; }
  h1 { font-size: 26px; margin: 0; } .cls { opacity: .6; font-family: var(--vscode-editor-font-family); }
  .verdict { margin: 12px 0; padding: 10px 14px; border-radius: 8px; display: flex; gap: 10px; align-items: center; }
  .verdict.ok { background: color-mix(in srgb, var(--ok) 14%, transparent); border: 1px solid color-mix(in srgb, var(--ok) 45%, transparent); }
  .verdict.warn { background: var(--vscode-inputValidation-warningBackground); }
  .dot { width: 10px; height: 10px; border-radius: 50%; background: var(--ok); flex: none; box-shadow: 0 0 0 4px color-mix(in srgb, var(--ok) 25%, transparent); }
  .stats { display: flex; gap: 12px; margin: 14px 0; flex-wrap: wrap; }
  .stats div { background: var(--vscode-editorWidget-background); border: 1px solid var(--vscode-panel-border); border-radius: 8px; padding: 10px 16px; min-width: 120px; }
  .stats b { display: block; font-size: 22px; } .stats span { opacity: .7; font-size: 12px; }
  .actions { display: flex; gap: 8px; }
  button { background: var(--vscode-button-background); color: var(--vscode-button-foreground); border: none; border-radius: 4px; padding: 6px 14px; cursor: pointer; font-family: inherit; }
  button:hover { background: var(--vscode-button-hoverBackground); }
  button.secondary, button.icon { background: var(--vscode-button-secondaryBackground); color: var(--vscode-button-secondaryForeground); }
  button.icon { padding: 2px 8px; font-size: 11px; }
  section.fn { margin-top: 26px; padding: 18px 20px; border: 1px solid var(--vscode-panel-border); border-radius: 10px; background: var(--vscode-sideBar-background); }
  .fnhead { display: flex; align-items: baseline; gap: 14px; flex-wrap: wrap; } h2 { margin: 0; font-size: 20px; color: var(--accent); }
  .lean { font-size: 12px; }
  pre.sig { background: var(--vscode-textCodeBlock-background); padding: 10px 12px; border-radius: 6px; overflow-x: auto; }
  h3 { font-size: 13px; text-transform: uppercase; letter-spacing: .06em; margin: 20px 0 8px; opacity: .85; }
  h3 span { text-transform: none; letter-spacing: 0; opacity: .6; font-weight: normal; margin-left: 6px; }
  table.ex { border-collapse: collapse; width: 100%; } table.ex td { padding: 5px 8px; border-top: 1px solid var(--vscode-panel-border); }
  td.pass { color: var(--ok); font-weight: bold; width: 18px; } td.res { font-family: var(--vscode-editor-font-family); color: var(--ok); white-space: nowrap; }
  .thm { padding: 10px 0; border-top: 1px solid var(--vscode-panel-border); }
  .thmhead { display: flex; align-items: center; gap: 10px; flex-wrap: wrap; }
  .name { font-family: var(--vscode-editor-font-family); font-weight: 600; }
  .ax { font-size: 11px; padding: 1px 7px; border-radius: 10px; margin-right: 4px; background: var(--vscode-badge-background); color: var(--vscode-badge-foreground); }
  .ax.none { background: color-mix(in srgb, var(--ok) 25%, transparent); color: inherit; }
  .viz { margin-left: auto; font-size: 12px; }
  .thm p { margin: 6px 0; }
  pre.stmt { white-space: pre-wrap; background: var(--vscode-textCodeBlock-background); padding: 8px 10px; border-radius: 6px; margin: 4px 0 0; font-size: 12px; }
  .empty { text-align: center; margin-top: 18vh; } .empty p { max-width: 520px; margin: 12px auto 20px; opacity: .8; }
</style></head><body>${body}
<script nonce="${nonce}">
  const vscode = acquireVsCodeApi();
  document.addEventListener('click', e => {
    const el = e.target.closest('[data-msg]');
    if (el) vscode.postMessage(JSON.parse(el.getAttribute('data-msg')));
  });
</script></body></html>`;
}

// ---------------------------------------------------------------- Lean side

function leanLenses(doc) {
  if (!lensesOn()) return [];
  const lenses = [];
  const text = doc.getText();
  for (const b of builds.values()) {
    const rel = path.relative(b.root, doc.uri.fsPath).split(path.sep).join('/');
    const was = outOfDate(b) ? '$(history) last build: ' : '';
    const at = (name, kinds, fallback) => {
      const i = lib.declarationLine(text, name, kinds);
      const line = i >= 0 ? i : (fallback ? fallback - 1 : -1);
      return line >= 0 ? new vscode.Range(line, 0, line, 0) : undefined;
    };
    for (const f of b.proof.functions.filter(f => f.file === rel)) {
      const range = at(f.lean, 'def|abbrev', f.source?.line);
      if (!range) continue;
      lenses.push(new vscode.CodeLens(range, { title: `${was}$(package) .NET: ${f.signatures[0].replace('public static ', '')}`, command: 'lean2dotnet.dashboard' }));
      const ths = f.theorems.length - f.examples.length;
      lenses.push(new vscode.CodeLens(range, { title: `$(verified) ${plural(ths, 'theorem')} · ${plural(f.examples.length, 'proved example')} replayed on the IL`, command: 'lean2dotnet.dashboard' }));
    }
    const examples = b.proof.functions.flatMap(f => f.examples);
    for (const t of b.proof.theorems.filter(t => t.file === rel && t.about.length)) {
      const range = at(t.name, 'theorem|lemma', t.line);
      if (!range) continue;
      const ex = examples.find(e => e.theorem === t.name);
      const calls = b.proof.functions.filter(f => t.about.includes(f.lean)).map(f => f.call).join(', ');
      const title = ex
        ? `${was}$(pass-filled) replayed on the IL: ${ex.call} returns ${ex.result}`
        : `${was}$(verified) in the .NET docs of ${calls}${b.proof.verdict.Checked ? ' · re-checked by Tenet' : ''}`;
      lenses.push(new vscode.CodeLens(range, { title, command: 'lean2dotnet.dashboard' }));
    }
  }
  return lenses;
}

function leanHover(doc, pos) {
  const range = doc.getWordRangeAtPosition(pos, /[A-Za-z_][A-Za-z0-9_'.]*/);
  if (!range) return;
  const word = doc.getText(range);
  const f = allFunctions().find(f => f.lean === word || f.lean.endsWith('.' + word));
  if (!f || !/\bdef\b/.test(doc.lineAt(pos.line).text)) return;
  return new vscode.Hover(functionMarkdown(f, true));
}

// ---------------------------------------------------------------- C# side

function csharpCalls(doc) {
  const fns = allFunctions();
  return lib.csharpCalls(doc.getText(), fns.map(f => f.call)).map(h => ({ ...h, f: fns.find(f => f.call === h.call) }));
}

function csharpLenses(doc) {
  if (!lensesOn()) return [];
  const seen = new Set();
  return csharpCalls(doc).flatMap(({ f, offset }) => {
    const line = doc.positionAt(offset).line;
    if (seen.has(line + f.call)) return [];
    seen.add(line + f.call);
    const v = f.build.proof.verdict;
    return [new vscode.CodeLens(new vscode.Range(line, 0, line, 0), {
      title: `$(verified) ${f.call}: proved in Lean, ${plural(f.theorems.length - f.examples.length, 'theorem')}${v.Checked ? ', re-checked by Tenet' : ''}`,
      command: 'lean2dotnet.reveal', arguments: [f.build.root, f.file, f.source && f.source.line],
    })];
  });
}

function csharpHover(doc, pos) {
  const hit = csharpCalls(doc).find(c => new vscode.Range(doc.positionAt(c.offset), doc.positionAt(c.offset + c.length)).contains(pos));
  if (hit) return new vscode.Hover(functionMarkdown(hit.f, false));
}

function csharpCompletions(doc, pos) {
  const before = doc.lineAt(pos.line).text.slice(0, pos.character);
  const items = [];
  for (const b of builds.values()) {
    const cls = b.proof.class.split('.').pop();
    if (!new RegExp(`\\b${cls}\\.\\w*$`).test(before)) continue;
    for (const f of b.proof.functions) {
      const f2 = { ...f, build: b };
      const ths = f.theorems.length - f.examples.length;
      const item = new vscode.CompletionItem({ label: f.method, description: `proved in Lean · ${plural(ths, 'theorem')}` }, vscode.CompletionItemKind.Method);
      item.detail = f.signatures[0];
      item.documentation = functionMarkdown(f2, false);
      item.sortText = '0' + f.method;
      items.push(item);
    }
  }
  return items;
}

// ---------------------------------------------------------------- shared

function functionMarkdown(f, fromLean) {
  const b = f.build;
  const md = new vscode.MarkdownString(undefined, true);
  md.isTrusted = { enabledCommands: ['lean2dotnet.reveal', 'lean2dotnet.dashboard'] };
  md.appendMarkdown(`**${f.call}** · compiled from \`${f.lean}\`\n\n`);
  md.appendCodeblock(f.signatures.join('\n'), 'csharp');
  if (!fromLean && f.doc) md.appendMarkdown(firstPara(f.doc) + '\n\n');
  if (f.examples.length) {
    md.appendMarkdown('**Proved examples**, each replayed against the IL:\n');
    md.appendCodeblock(f.examples.map(e => `${e.call}; // ${e.result}`).join('\n'), 'csharp');
  }
  const ex = exampleTheorems(f);
  const ths = f.theorems.filter(n => !ex.has(n));
  if (ths.length) {
    md.appendMarkdown('**Proved about it**\n\n');
    for (const n of ths) {
      const t = theoremOf(b, n);
      if (!t) continue;
      const args = encodeURIComponent(JSON.stringify([b.root, t.file, t.line]));
      md.appendMarkdown(`- [\`${n.split('.').pop()}\`](command:lean2dotnet.reveal?${args}): ${firstPara(t.doc)}\n`);
    }
  }
  md.appendMarkdown(`\n\n$(verified-filled) ${verdictText(b.proof.verdict)} [Proof Dashboard](command:lean2dotnet.dashboard)`);
  return md;
}

async function reveal(root, file, line) {
  if (!root || !file) return;
  const doc = await vscode.workspace.openTextDocument(path.join(root, file));
  const ed = await vscode.window.showTextDocument(doc, { preview: false, viewColumn: vscode.ViewColumn.One });
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

/** VS Code started from the Dock does not see a login shell's PATH; add where Lean and .NET usually live. */
function toolEnv() {
  const home = os.homedir();
  const extra = [path.join(home, '.elan', 'bin'), path.join(home, '.dotnet'), path.join(home, '.dotnet', 'tools'), '/opt/homebrew/bin', '/usr/local/bin', '/usr/local/share/dotnet'];
  const env = { ...process.env, PATH: [...extra.filter(fs.existsSync), process.env.PATH].join(path.delimiter), DOTNET_CLI_TELEMETRY_OPTOUT: '1' };
  if (!env.DOTNET_ROOT && fs.existsSync(path.join(home, '.dotnet', 'dotnet'))) env.DOTNET_ROOT = path.join(home, '.dotnet');
  return env;
}

function lean2ilCommand(root, env) {
  const configured = vscode.workspace.getConfiguration('lean2dotnet').get('lean2ilCommand');
  if (configured) return configured;
  const bundled = path.join(extensionPath, 'server', 'lean2il.dll');
  if (fs.existsSync(bundled)) return `dotnet "${bundled}"`;
  try {
    cp.execSync(process.platform === 'win32' ? 'where lean2il' : 'command -v lean2il', { stdio: 'ignore', env });
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

async function pickRoot() {
  const roots = await lakeRoots();
  if (roots.length === 0) return undefined;
  const active = vscode.window.activeTextEditor?.document.uri.fsPath;
  const inside = active && roots.filter(r => active.startsWith(r + path.sep)).sort((a, b) => b.length - a.length)[0];
  if (inside) return inside;
  if (roots.length === 1) return roots[0];
  return vscode.window.showQuickPick(roots, { placeHolder: 'Which Lake project?' });
}

async function build() {
  if (building) return;
  const root = await pickRoot();
  if (!root) {
    vscode.window.showErrorMessage('No Lake project (lakefile.toml or lakefile.lean) in this workspace.');
    return;
  }
  const env = toolEnv();
  if (!(await prerequisitesMet(env, root))) return;
  const tool = lean2ilCommand(root, env);
  if (!tool) {
    const pick = await vscode.window.showErrorMessage('lean2il was not found. Run ./setup.sh in the lean-to-dot-net repository, or set lean2dotnet.lean2ilCommand.', 'Open Settings', 'Getting Started');
    if (pick === 'Open Settings') vscode.commands.executeCommand('workbench.action.openSettings', 'lean2dotnet.lean2ilCommand');
    if (pick === 'Getting Started') vscode.commands.executeCommand('workbench.action.openWalkthrough', 'keithadler.lean-to-dot-net#lean2dotnet.start');
    return;
  }
  const cfg = vscode.workspace.getConfiguration('lean2dotnet');
  const flags = [cfg.get('checkImports') ? '' : '--trust-imports', cfg.get('leanvizUrl') ? `--leanviz "${cfg.get('leanvizUrl')}"` : ''].filter(Boolean).join(' ');
  const command = `lake build && ${tool} . ${flags}`;
  output.appendLine(`[${new Date().toLocaleTimeString()}] ${root}: ${command}`);

  building = true;
  updateStatus();
  const task = new vscode.Task({ type: 'lean2il' }, vscode.TaskScope.Workspace, 'Build .NET assembly', 'Lean to .NET',
    new vscode.CustomExecution(async () => new BuildTerminal(command, root, env, onBuilt)));
  task.presentationOptions = { reveal: vscode.TaskRevealKind.Always, clear: true, panel: vscode.TaskPanelKind.Dedicated, focus: false };
  await vscode.tasks.executeTask(task);

  async function onBuilt(code, out) {
    building = false;
    if (code === 0) failed.delete(root); else failed.add(root);
    api.lastBuild = { root, command, code, output: out };
    output.appendLine(`[${new Date().toLocaleTimeString()}] exit ${code}`);
    if (code !== 0) output.appendLine(out.split(/\r?\n/).slice(-30).join('\n'));
    publishDiagnostics(root, out);
    await loadAll();
    const b = builds.get(root);
    if (code === 0 && b) {
      const ex = b.proof.functions.reduce((n, f) => n + f.examples.length, 0);
      const pick = await vscode.window.showInformationMessage(
        `$(verified-filled) ${b.proof.dll}: ${plural(b.proof.functions.length, 'function')}, ${plural(b.proof.theorems.length, 'theorem')}, ${plural(ex, 'proved example')} replayed on the IL.`,
        'Open Proof Dashboard', 'Open API Docs');
      if (pick === 'Open Proof Dashboard') vscode.commands.executeCommand('lean2dotnet.dashboard');
      if (pick === 'Open API Docs') openDocs(root);
    } else {
      const pick = await vscode.window.showErrorMessage('The build failed. The Problems panel and the terminal say why.', 'Show Problems');
      if (pick) vscode.commands.executeCommand('workbench.actions.view.problems');
    }
  }
}

/**
 * Lean to .NET needs the .NET 10 runtime and Lean's `lake`. When one is missing, say which, and offer a terminal
 * with the official installer's command typed in but not run: the person presses Enter, or does not.
 */
async function prerequisitesMet(env, root) {
  // From the project folder: its lean-toolchain picks Lean's version, so lake works there even when elan has no
  // default toolchain.
  const run = cmd => { try { return cp.execSync(cmd, { env, cwd: root, stdio: ['ignore', 'pipe', 'ignore'], timeout: 120000 }).toString(); } catch { return undefined; } };
  const win = process.platform === 'win32';
  const missing = [];
  if (!lib.hasRuntime(run('dotnet --list-runtimes'))) {
    missing.push({ what: 'the .NET 10 runtime', url: 'https://dotnet.microsoft.com/download/dotnet/10.0',
      command: win ? '& ([scriptblock]::Create((iwr https://dot.net/v1/dotnet-install.ps1))) -Channel 10.0 -Runtime dotnet'
                   : 'curl -sSfL https://dot.net/v1/dotnet-install.sh | bash -s -- --channel 10.0 --runtime dotnet' });
  }
  if (run('lake --version') === undefined) {
    missing.push({ what: 'Lean (elan and lake)', url: 'https://lean-lang.org/install/',
      command: win ? 'curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1; powershell -ExecutionPolicy Bypass -f elan-init.ps1'
                   : 'curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh' });
  }
  for (const m of missing) {
    output.appendLine(`missing: ${m.what}`);
    const pick = await vscode.window.showErrorMessage(`Lean to .NET needs ${m.what}, which was not found.`, 'Install in Terminal', 'Open Download Page');
    if (pick === 'Install in Terminal') {
      const t = vscode.window.createTerminal({ name: `Install ${m.what}` });
      t.show();
      t.sendText(m.command, false);
      vscode.window.showInformationMessage(`The installer command is typed in the terminal. Press Enter there to run it, then build again.`);
    } else if (pick === 'Open Download Page') {
      vscode.env.openExternal(vscode.Uri.parse(m.url));
    }
  }
  return missing.length === 0;
}

/** A terminal that runs the build and keeps its output, so failures can become diagnostics. */
class BuildTerminal {
  constructor(command, cwd, env, done) {
    this.command = command; this.cwd = cwd; this.env = env; this.done = done; this.output = '';
    this.writeEmitter = new vscode.EventEmitter(); this.onDidWrite = this.writeEmitter.event;
    this.closeEmitter = new vscode.EventEmitter(); this.onDidClose = this.closeEmitter.event;
  }
  open() {
    this.write(`\x1b[1;35m▶ ${this.command}\x1b[0m\r\n\r\n`);
    this.proc = cp.spawn(this.command, { cwd: this.cwd, env: this.env, shell: true });
    const take = d => { const s = d.toString(); this.output += s; this.write(s.replace(/\r?\n/g, '\r\n')); };
    this.proc.stdout.on('data', take);
    this.proc.stderr.on('data', take);
    this.proc.on('close', code => {
      this.write(code === 0 ? '\r\n\x1b[1;32m✓ done\x1b[0m\r\n' : `\r\n\x1b[1;31m✗ exited with ${code}\x1b[0m\r\n`);
      this.done(code, this.output);
      this.closeEmitter.fire(code ?? 1);
    });
  }
  write(s) { this.writeEmitter.fire(s); }
  close() { this.proc?.kill(); }
  handleInput() {}
}

/** Lean's errors, lean2il's refusals and Tenet's rejections, placed on the lines they are about. */
function publishDiagnostics(root, output) {
  diagnostics.clear();
  const byFile = new Map();
  const add = (file, line, col, message, severity) => {
    const uri = vscode.Uri.file(path.isAbsolute(file) ? file : path.join(root, file));
    const d = new vscode.Diagnostic(new vscode.Range(Math.max(0, line - 1), Math.max(0, col), Math.max(0, line - 1), 1000), message,
      severity === 'warning' ? vscode.DiagnosticSeverity.Warning : vscode.DiagnosticSeverity.Error);
    d.source = 'lean2il';
    if (!byFile.has(uri.toString())) byFile.set(uri.toString(), { uri, list: [] });
    byFile.get(uri.toString()).list.push(d);
  };
  for (const p of lib.parseBuildOutput(output)) {
    if (p.kind === 'lean') { add(p.file, p.line, p.column, p.message, p.severity); continue; }
    const loc = p.name && findDeclaration(root, p.name);
    if (loc) add(loc.file, loc.line, 0, p.message, p.severity);
    else vscode.window.showErrorMessage(p.message.replace(/^lean2il cannot compile this: /, 'lean2il: '));
  }
  for (const { uri, list } of byFile.values()) diagnostics.set(uri, list);
}

function findDeclaration(root, name) {
  const walk = dir => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      if (e.name.startsWith('.')) continue;
      const p = path.join(dir, e.name);
      if (e.isDirectory()) { const r = walk(p); if (r) return r; }
      else if (e.name.endsWith('.lean')) {
        const i = lib.declarationLine(fs.readFileSync(p, 'utf8'), name);
        if (i >= 0) return { file: p, line: i + 1 };
      }
    }
  };
  try { return walk(root); } catch { return undefined; }
}

function deactivate() {}

module.exports = { activate, deactivate };
