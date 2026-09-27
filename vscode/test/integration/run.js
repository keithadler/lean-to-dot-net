// Runs the integration tests in a real VS Code, with this extension loaded from source and the official Lean 4
// extension installed, against this repository as the workspace. `npm run test:integration`.
'use strict';
const path = require('path');
const fs = require('fs');
const cp = require('child_process');
const { runTests, downloadAndUnzipVSCode, resolveCliArgsFromVSCodeExecutablePath } = require('@vscode/test-electron');

(async () => {
  const extensionDevelopmentPath = path.resolve(__dirname, '../..');
  const workspace = path.resolve(extensionDevelopmentPath, '..');
  let vscodeExecutablePath = process.env.VSCODE_EXECUTABLE || await downloadAndUnzipVSCode('stable');
  // VS Code 1.13x on macOS renamed Contents/MacOS/Electron to Code; test-electron still expects the old name.
  if (!fs.existsSync(vscodeExecutablePath) && fs.existsSync(path.join(path.dirname(vscodeExecutablePath), 'Code'))) {
    vscodeExecutablePath = path.join(path.dirname(vscodeExecutablePath), 'Code');
  }
  const [cli, ...args] = resolveCliArgsFromVSCodeExecutablePath(vscodeExecutablePath);
  cp.spawnSync(cli, [...args, '--install-extension', 'leanprover.lean4'], { stdio: 'inherit', shell: process.platform === 'win32' });
  await runTests({
    vscodeExecutablePath,
    extensionDevelopmentPath,
    extensionTestsPath: path.resolve(__dirname, 'suite.js'),
    launchArgs: [workspace, '--disable-workspace-trust', '--skip-welcome', '--skip-release-notes'],
  });
})().catch(err => { console.error(err); process.exit(1); });
