'use strict';
const test = require('node:test');
const assert = require('node:assert/strict');
const lib = require('../lib');

const lean = `namespace Finance

/-- Round. -/
@[export lean2il_finance_round]
def round (x : Dec) (digits : Nat) : Dec := x

/-- Cents. -/
def roundCents (x : Dec) : Dec := round x 2

private theorem round_neg' : True := trivial
theorem round_neg (x : Dec) : True := trivial
`;

test('declarationLine finds a definition and puts the lens on its @[export] line', () => {
  assert.equal(lib.declarationLine(lean, 'Finance.round'), 3);
  assert.equal(lib.declarationLine(lean, 'Finance.roundCents'), 7);
});

test('declarationLine does not confuse a name with a longer one', () => {
  assert.equal(lib.declarationLine(lean, 'Finance.round_neg'), 10);
  assert.equal(lib.declarationLine(lean, "Finance.round_neg'"), 9);
  assert.equal(lib.declarationLine(lean, 'Finance.nothing'), -1);
});

test('csharpCalls finds calls and skips line comments', () => {
  const cs = `var a = Proven.Round(1m, 2, m); // Proven.Round(9m) in a comment
var b = Proven.RoundCents(x) + Proven.Round (y, 1, m);
var c = NotProven.Round(1);`;
  const hits = lib.csharpCalls(cs, ['Proven.Round', 'Proven.RoundCents']);
  assert.deepEqual(hits.map(h => h.call), ['Proven.Round', 'Proven.RoundCents', 'Proven.Round']);
});

test('parseBuildOutput reads Lean errors with their message lines', () => {
  const out = `✖ [2/4] Building Finance.Rounding
trace: .> LEAN_PATH=... lean Finance/Rounding.lean
error: Finance/Rounding.lean:189:14: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 1
warning: Finance/Rounding.lean:12:0: declaration uses 'sorry'
error: Lean exited with code 1`;
  const p = lib.parseBuildOutput(out);
  assert.equal(p.length, 2);
  assert.deepEqual([p[0].file, p[0].line, p[0].column, p[0].severity], ['Finance/Rounding.lean', 189, 14, 'error']);
  assert.match(p[0].message, /counterexample/);
  assert.equal(p[1].severity, 'warning');
});

test('parseBuildOutput reads lean2il refusals and Tenet rejections', () => {
  const out = `lean2il: 3 modules in /x (Lean 4.33.1)
lean2il: Finance.sumTo: it is defined by structural recursion (Nat.brecOn), which lean2il does not compile yet
  REJECTED Finance.Bad: Finance.bad: type mismatch
lean2il: nothing is marked @[export]; mark each definition to compile with @[export some_symbol]`;
  const p = lib.parseBuildOutput(out);
  assert.deepEqual(p.map(x => [x.kind, x.name]), [['lean2il', 'Finance.sumTo'], ['tenet', 'Finance.bad'], ['lean2il', undefined]]);
  assert.match(p[0].message, /structural recursion/);
});

test('parseBuildOutput places a refusal that names a parameter on its function', () => {
  const p = lib.parseBuildOutput("lean2il: Finance.half, parameter x: Float is not compiled yet: Lean's kernel does not model floating point");
  assert.deepEqual(p.map(x => [x.kind, x.name]), [['lean2il', 'Finance.half']]);
  assert.match(p[0].message, /parameter x: Float is not compiled/);
});

test('parseBuildOutput places a differential failure on the function it names', () => {
  const p = lib.parseBuildOutput(`lean2il: the IL disagrees with Lean's own compiler on Rec.chars "a😀": Lean gives 2, the IL gives 3`);
  assert.equal(p.length, 1);
  assert.equal(p[0].name, 'Rec.chars');
  assert.match(p[0].message, /Lean gives 2, the IL gives 3/);
});

test('hasRuntime reads dotnet --list-runtimes', () => {
  const rt = `Microsoft.AspNetCore.App 9.0.1 [/x]
Microsoft.NETCore.App 9.0.1 [/usr/local/share/dotnet/shared/Microsoft.NETCore.App]
Microsoft.NETCore.App 10.0.12 [/Users/k/.dotnet/shared/Microsoft.NETCore.App]`;
  assert.equal(lib.hasRuntime(rt), true);
  assert.equal(lib.hasRuntime(rt.split('\n').slice(0, 2).join('\n')), false);
  assert.equal(lib.hasRuntime(''), false);
});

test('leanvizLink handles a site URL with and without a project query', () => {
  assert.equal(lib.leanvizLink('https://x.io/viz/?p=finance', 'Finance.round_neg'), 'https://x.io/viz/?p=finance#/d/Finance.round_neg');
  assert.equal(lib.leanvizLink('https://x.io/viz', 'A.b'), 'https://x.io/viz/#/d/A.b');
  assert.equal(lib.leanvizLink('', 'A.b'), undefined);
});

test('isStale compares the build with its sources', () => {
  assert.equal(lib.isStale(10_000, [5_000, 9_000]), false);
  assert.equal(lib.isStale(10_000, [5_000, 20_000]), true);
});

test('inline escapes HTML and keeps code and bold', () => {
  assert.equal(lib.inline('**Half** a `x < y` <b>'), '<b>Half</b> a <code>x &lt; y</code> &lt;b&gt;');
  assert.equal(lib.plural(1, 'theorem'), '1 theorem');
  assert.equal(lib.plural(2, 'theorem'), '2 theorems');
});
