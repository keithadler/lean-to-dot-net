// The parts of the extension that do not need VS Code: parsing, matching, formatting. Kept apart so that
// `npm test` can check them with Node alone.
'use strict';

const plural = (n, word) => `${n} ${word}${n === 1 ? '' : 's'}`;

/** The first paragraph of a docstring, on one line. */
const firstPara = s => (s || '').split('\n\n')[0].replace(/\n/g, ' ').trim();

const esc = s => String(s ?? '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');

/** Docstring Markdown to safe HTML: `code` and **bold**, everything else escaped. */
const inline = s => esc(s).replace(/`([^`]+)`/g, '<code>$1</code>').replace(/\*\*([^*]+)\*\*/g, '<b>$1</b>');

const reEscape = s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

/** A line that declares `name` (its last component), with or without attributes and modifiers before it. */
function declarationRegex(name, kinds = 'def|theorem|lemma|abbrev|structure|inductive|instance') {
  const short = name.split('.').pop();
  return new RegExp(`^\\s*(?:@\\[[^\\]]*\\]\\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\\s+)*(?:${kinds})\\s+(?:[\\w.']*\\.)?${reEscape(short)}(?![\\w'])`);
}

/**
 * The 0-based line where `name` is declared in `text`, or -1. When the declaration is a definition marked
 * `@[export ...]` on the line above, that line is returned, so a lens sits over the whole header.
 */
function declarationLine(text, name, kinds) {
  const lines = text.split(/\r?\n/);
  const re = declarationRegex(name, kinds);
  const i = lines.findIndex(l => re.test(l));
  if (i > 0 && /^\s*@\[[^\]]*\]\s*$/.test(lines[i - 1])) return i - 1;
  return i;
}

/** Every call `Class.Method(` of the compiled functions in C# source, skipping line comments. */
function csharpCalls(text, calls) {
  const out = [];
  const lineComment = [];
  const re = /\/\/[^\n]*/g;
  let m;
  while ((m = re.exec(text))) lineComment.push([m.index, m.index + m[0].length]);
  const inComment = i => lineComment.some(([a, b]) => i >= a && i < b);
  for (const call of calls) {
    const r = new RegExp(`\\b${reEscape(call)}\\s*\\(`, 'g');
    while ((m = r.exec(text))) if (!inComment(m.index)) out.push({ call, offset: m.index, length: call.length });
  }
  return out.sort((a, b) => a.offset - b.offset);
}

/**
 * What a build printed, as problems to show: Lean's `error:`/`warning:` lines with the message lines under them,
 * lean2il's refusals (`lean2il: Name: reason`), and Tenet's rejections (`REJECTED Module: Name: reason`).
 */
function parseBuildOutput(output) {
  const problems = [];
  const lines = output.split(/\r?\n/);
  for (let i = 0; i < lines.length; i++) {
    const lean = /^(error|warning): (.+?\.lean):(\d+):(\d+): (.*)$/.exec(lines[i]);
    if (lean) {
      const more = [];
      for (let j = i + 1; j < lines.length && j < i + 12 && !/^(error|warning|info|✖|⚠|✔|trace|Some required|lean2il|tenet)/.test(lines[j]); j++) more.push(lines[j]);
      problems.push({ kind: 'lean', file: lean[2], line: +lean[3], column: +lean[4], severity: lean[1], message: [lean[5], ...more].join('\n').trim() });
      continue;
    }
    const tenet = /REJECTED \S+: (\S+): (.*)$/.exec(lines[i]);
    if (tenet) { problems.push({ kind: 'tenet', name: tenet[1], severity: 'error', message: 'Tenet rejected this declaration: ' + tenet[2] }); continue; }
    const l2 = /^lean2il: ([A-Za-z_][\w.']*): (.*)$/.exec(lines[i]);
    if (l2 && l2[1].includes('.')) { problems.push({ kind: 'lean2il', name: l2[1], severity: 'error', message: 'lean2il cannot compile this: ' + l2[2] }); continue; }
    const general = /^lean2il: (.*)$/.exec(lines[i]);
    if (general && !/^(\d+ modules? in |skipping )/.test(general[1])) problems.push({ kind: 'lean2il', severity: 'error', message: general[1] });
  }
  return problems;
}

/** Whether `dotnet --list-runtimes` output includes a .NET runtime of this major version. */
function hasRuntime(listRuntimes, major = 10) {
  return new RegExp(`^Microsoft\\.NETCore\\.App ${major}\\.`, 'm').test(listRuntimes || '');
}

/** A LeanViz link for a declaration, given the site's URL (which may already carry `?p=project`). */
function leanvizLink(base, name) {
  if (!base) return undefined;
  return (base.includes('?') ? base : base.replace(/\/?$/, '/')) + '#/d/' + encodeURIComponent(name);
}

/** Whether a build is older than any of the Lean sources it came from (mtimes in ms). */
function isStale(buildTime, sourceTimes) {
  return sourceTimes.some(t => t > buildTime + 1000);
}

module.exports = { plural, firstPara, esc, inline, declarationRegex, declarationLine, csharpCalls, parseBuildOutput, hasRuntime, leanvizLink, isStale };
