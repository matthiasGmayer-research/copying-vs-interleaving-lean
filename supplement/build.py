#!/usr/bin/env python3
"""Build the supplementary PDF "Appendix: Lean formalisation" of the cstar paper from this repository.

usage (from the repository root, after `lake build` and `lake env lean Check.lean > Check.out`):
  python3 supplement/build.py [--paper PATH/main.typ] [--no-pdf] [--allow-dirty]

Everything in the PDF is generated, so it rebuilds after renames:
  - title and author: from the paper's main.typ (the `title:` and `authors:` arguments of `paper.with`);
  - coverage: the paper's own words, the paragraph under the `<sec-lean>` heading of main.typ
    (cross-references printed as labels), then the README's status and cited-results paragraphs;
  - the main statements, the correspondence, the earlier versions: README.md, converted section by section;
  - the correspondence table is checked against the source: every row lists exactly the declarations tagged
    `@[kb "cstarpaper-<label>"]` with its labels (supplement/tags.py); a difference stops the build;
  - versions and audit: lean-toolchain, lake-manifest.json (Mathlib), Check.lean and its output Check.out.
Output: supplement/lean-appendix.typ, and supplement/lean-appendix.pdf (typst compile; not committed).
"""
import argparse, json, os, re, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tags as tagscan

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FONTS = os.path.expanduser('~/projects/papers/fonts')


def die(msg):
    sys.exit('build.py: ' + msg)


# ---------------------------------------------------------------- the paper (main.typ)

def balanced(s, i, open_='[', close=']'):
    """The content of the bracket starting at s[i] (s[i] == open_), and the index after it."""
    assert s[i] == open_
    d = 0
    for j in range(i, len(s)):
        if s[j] == open_: d += 1
        elif s[j] == close:
            d -= 1
            if d == 0: return s[i + 1:j], j + 1
    die('unbalanced bracket in main.typ')


def strip_comments(s):
    return '\n'.join(l for l in s.split('\n') if not l.lstrip().startswith('//'))


def paper_meta(path):
    s = strip_comments(open(path).read())
    m = re.search(r'#show:\s*paper\.with\(', s)
    if not m: die(f'no `#show: paper.with(` in {path}')
    t = s.index('title:', m.end())
    title, _ = balanced(s, s.index('[', t))
    a = s.index('authors:', m.end())
    names = re.findall(r'name:\s*"([^"]*)"', s[a:s.index('abstract:', a) if 'abstract:' in s[a:] else a + 400])
    # keyed on the label, so a change of the heading's wording or case does not break the build
    m = re.search(r'^== .*<sec-lean>\s*$', s, re.M)
    if not m: die(f'no heading `== … <sec-lean>` in {path}')
    rest = s[m.end():]
    n = re.search(r'^=', rest, re.M)
    body = rest[:n.start() if n else len(rest)].strip()
    # cross-references -> the label in monospace (the paper's labels, as in the README)
    body = re.sub(r'@([A-Za-z0-9][A-Za-z0-9_:-]*[A-Za-z0-9])', lambda k: f'#raw("{k.group(1)}")', body)
    # the paper's notation macros (ARC, sZLC, ...), without the site's hover links
    nf = os.path.join(os.path.dirname(path), 'notation.typ')
    notation = ''
    if os.path.exists(nf):
        notation = '#let doc-sym(label, body) = body\n' + '\n'.join(
            l for l in open(nf).read().split('\n') if not l.startswith('#import'))
    return title.strip(), names, body, notation


# ---------------------------------------------------------------- Markdown (the README subset) -> Typst

ESC = re.compile(r'([\\*_`#$@<>~\[\]])')


def esc(t):
    t = ESC.sub(r'\\\1', t)
    t = t.replace('//', '/\\/')
    return t


def rawstr(t):
    return 'raw("' + t.replace('\\', '\\\\').replace('"', '\\"') + '")'


def inline(t):
    out, i = [], 0
    for m in re.finditer(r'`([^`]+)`|\*\*([^*]+)\*\*|(?<![\w*])\*([^*\s][^*]*)\*(?![\w*])', t):
        out.append(esc(t[i:m.start()]))
        if m.group(1) is not None: out.append('#' + rawstr(m.group(1)))
        elif m.group(2) is not None: out.append('*' + inline(m.group(2)) + '*')
        else: out.append('_' + inline(m.group(3)) + '_')
        i = m.end()
    out.append(esc(t[i:]))
    s = ''.join(out)
    s = s.lstrip()
    if s[:1] in ('-', '+', '=', '/'): s = '\\' + s
    s = re.sub(r'^(\d+)\.', r'\1\\.', s)
    return s


def table(rows, widths=None):
    cells = [[c.strip() for c in r.strip().strip('|').split('|')] for r in rows]
    head, body = cells[0], cells[2:]
    n = len(head)
    cols = widths or f'({", ".join(["auto"] * n)})'
    out = [f'#table(columns: {cols}, align: left, stroke: 0.4pt + luma(180), inset: 4pt,',
           '  table.header(' + ', '.join(f'[*{inline(h)}*]' for h in head) + '),']
    for r in body:
        r = (r + [''] * n)[:n]
        # several proof steps in a cell: one per line
        out.append('  ' + ', '.join('[' + inline(c).replace('; #raw("st-', ' \\\n#raw("st-') + ']' for c in r) + ',')
    out.append(')')
    return '\n'.join(out)


WORD = re.compile(r'[^\W_]+')


def md_to_typst(md, level_shift=0, table_widths=None):
    out = _md_to_typst(md, level_shift, table_widths)
    # no prose may be lost: every word of the Markdown (as a multiset) must be in the Typst
    from collections import Counter
    src = Counter(WORD.findall(re.sub(r'<!--.*?-->', '', md, flags=re.S)))
    got = Counter(WORD.findall(out))
    lost = src - got
    if lost:
        die(f'README text lost in the conversion (words missing: {dict(lost)}) in the section starting '
            f'{md.strip()[:80]!r}')
    return out


def _md_to_typst(md, level_shift=0, table_widths=None):
    md = re.sub(r'<!--.*?-->', '', md, flags=re.S)
    lines, out, i = md.split('\n'), [], 0
    para = []

    def flush():
        if para:
            out.append(inline(' '.join(para)))
            out.append('')
            para.clear()
    while i < len(lines):
        l = lines[i]
        if l.startswith('```'):
            flush()
            lang = l[3:].strip()
            j = i + 1
            while not lines[j].startswith('```'): j += 1
            code = '\n'.join(lines[i + 1:j])
            fence = '`' * max(3, max((len(x) for x in re.findall(r'`+', code)), default=0) + 1)
            out += [f'{fence}{lang}', code, fence, '']
            i = j + 1
            continue
        m = re.match(r'(#+)\s+(.*)', l)
        if m:
            flush()
            out += ['=' * (len(m.group(1)) - 1 + level_shift) + ' ' + inline(m.group(2)), '']
        elif l.startswith('|') and i + 1 < len(lines) and re.match(r'\|\s*:?-{3,}', lines[i + 1]):
            flush()
            j = i
            while j < len(lines) and lines[j].startswith('|'): j += 1
            out += [table(lines[i:j], table_widths), '']
            i = j
            continue
        elif re.match(r'\s*[-*]\s+', l):
            flush()
            item = [re.sub(r'^\s*[-*]\s+', '', l)]
            while i + 1 < len(lines) and lines[i + 1].startswith('  ') and lines[i + 1].strip():
                i += 1; item.append(lines[i].strip())
            out.append('- ' + inline(' '.join(item)))
        elif not l.strip():
            flush()
        else:
            para.append(l.strip())
        i += 1
    flush()
    return '\n'.join(out)


def sections(md):
    """README.md -> (title, preamble, {section heading: section text without its heading})."""
    parts = re.split(r'^## (.*)$', md, flags=re.M)
    head = parts[0]
    m = re.match(r'# (.*)\n', head)
    return (m.group(1) if m else ''), head[m.end() if m else 0:], {parts[k].strip(): parts[k + 1] for k in range(1, len(parts), 2)}


# ---------------------------------------------------------------- the check of the correspondence table

def full(n):
    return n if n.startswith('CopyingInterleaving.') else 'CopyingInterleaving.Paper.' + n


def check_table(readme, tags, paper_labels):
    tab = readme.split('<!-- tab-lean -->')[1].split('<!-- /tab-lean -->')[0]
    problems, seen = [], set()
    for row in tab.strip().split('\n')[2:]:
        cells = [c.strip() for c in row.strip().strip('|').split('|')]
        labs = re.findall(r'`([^`]+)`', cells[0])
        names = {full(n) for n in re.findall(r'`([^`]+)`', cells[1])}
        tagged = set().union(*[set(tags.get(l, [])) for l in labs])
        seen |= set(labs)
        if names != tagged:
            problems.append(f'row {labs}: README only {sorted(names - tagged)}; tagged only {sorted(tagged - names)}')
        for part in cells[2].split(';'):
            m = re.match(r'\s*`([^`]+)`:\s*(.*)', part)
            if not m: continue
            st = m.group(1); seen.add(st)
            v = {full(n) for n in re.findall(r'`([^`]+)`', m.group(2))}
            tv = set(tags.get(st, []))
            if v != tv: problems.append(f'step {st}: README only {sorted(v - tv)}; tagged only {sorted(tv - v)}')
    for l in labs_missing(paper_labels, seen):
        problems.append(f'paper block {l} has no row')
    untabled = sorted(l for l in tags if l not in seen and not l.startswith('s-') and l in paper_labels
                      and not l.startswith('sec-'))
    for l in untabled:
        problems.append(f'tagged paper label {l} has no row')
    for l in sorted(l for l in paper_labels if l.startswith('s-') and l not in tags):
        problems.append(f'sentence anchor {l} of the paper has no tagged declaration')
    return problems, seen


def labs_missing(paper_labels, seen):
    numbered = ('thm-', 'lem-', 'cor-', 'prop-', 'def-', 'ex-', 'rem-', 'st-')
    return sorted(l for l in paper_labels if l.startswith(numbered) and l not in seen)


def paper_labels_of(path):
    s = strip_comments(open(path).read())
    fig = os.path.join(os.path.dirname(path), 'figures.typ')   # tables and figures (tab-relay, fig-example anchors) live here
    if os.path.exists(fig): s += '\n' + strip_comments(open(fig).read())
    return set(re.findall(r'<([a-z][a-z0-9-]*)>', s))


# ---------------------------------------------------------------- main

def git(*a):
    return subprocess.run(['git', '-C', ROOT, *a], capture_output=True, text=True).stdout.strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--paper', default=os.path.expanduser('~/projects/papers/cstar/draft/main.typ'))
    ap.add_argument('--no-pdf', action='store_true')
    ap.add_argument('--allow-dirty', action='store_true', help='build from uncommitted changes (draft marking)')
    a = ap.parse_args()
    os.chdir(ROOT)

    title, authors, coverage, notation = paper_meta(a.paper)
    readme = open('README.md').read()
    rtitle, pre, sec = sections(readme)
    need = ['The main statements in Lean', 'Versions and build', 'The correspondence', 'Earlier versions',
            'Cited results', 'The earlier formalisation']
    for k in need:
        if k not in sec: die(f'README.md has no section "## {k}"')
    extra = [k for k in sec if k not in need]

    tags = {k: [n for n, _ in v] for k, v in tagscan.scan('CopyingInterleaving').items()}
    labels = paper_labels_of(a.paper)
    problems, seen = check_table(readme, tags, labels)
    if problems:
        die('the correspondence table of README.md differs from the tags in the source:\n  ' + '\n  '.join(problems))
    sentences = sorted(l for l in tags if l in labels and l not in seen)
    stale = sorted(l for l in tags if l not in labels and l not in seen and not l.startswith('cite-'))

    toolchain = open('lean-toolchain').read().strip()
    mathlib = next(p for p in json.load(open('lake-manifest.json'))['packages'] if p['name'] == 'mathlib')
    if not os.path.exists('Check.out'): die('Check.out missing: run `lake env lean Check.lean > Check.out`')
    check_lean, check_out = open('Check.lean').read(), open('Check.out').read()
    if os.path.getmtime('Check.out') < max(os.path.getmtime(p) for p in ['Check.lean', 'CopyingInterleaving.lean']):
        die('Check.out is older than Check.lean/CopyingInterleaving.lean: rerun `lake env lean Check.lean > Check.out`')
    ax = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", check_out, re.M)
    bad = [(n, x) for n, x in ax if set(map(str.strip, x.split(','))) - {'propext', 'Classical.choice', 'Quot.sound'}]
    if bad or 'error' in check_out or 'sorry' in check_out:
        die(f'axiom audit not clean: {bad[:5]} (or an error/sorry in Check.out)')
    nprint = len(re.findall(r'^#print axioms', check_lean, re.M))
    if len(ax) != nprint: die(f'Check.out has {len(ax)} axiom lines, Check.lean {nprint} #print axioms')

    # the README's preamble without its first paragraph (what the README is; the title page says it here)
    pre_kept = '\n\n'.join(p for p in re.split(r'\n\s*\n', pre.strip()) if not p.startswith('Machine-checked proofs'))
    rev = git('log', '-1', '--format=%h', '--abbrev=12', '--', 'CopyingInterleaving', 'CopyingInterleaving.lean', 'README.md', 'Check.lean', 'lakefile.toml',
              'lake-manifest.json', 'lean-toolchain')   # the last commit of the inputs, not of the PDF source
    dirty = bool(git('status', '--porcelain', '--', 'CopyingInterleaving', 'CopyingInterleaving.lean', 'README.md', 'Check.lean', 'lakefile.toml',
                     'lake-manifest.json', 'lean-toolchain'))
    if dirty and not a.allow_dirty: die('uncommitted changes in the formalisation (commit, or --allow-dirty for a draft)')
    nmod = sum(1 for l in open('CopyingInterleaving.lean') if l.startswith('import '))
    ndecl = sum(len(v) for k, v in tags.items() if k in labels)
    numbered = ('thm-', 'lem-', 'cor-', 'prop-', 'def-', 'ex-', 'rem-')
    nsteps = len([l for l in seen if l.startswith('st-')])
    nblocks = len([l for l in seen if l.startswith(numbered)])
    others = sorted(l for l in seen if not l.startswith(numbered + ('st-',)))
    # the README's version paragraph must agree with the pinned files (it is printed; the files are the truth)
    vb = sec['Versions and build']
    if toolchain not in vb or mathlib['rev'][:7] not in vb or mathlib.get('inputRev', '') not in vb:
        die('README "Versions and build" disagrees with lean-toolchain / lake-manifest.json')

    T = []
    T.append(f'''// GENERATED by supplement/build.py from README.md, Check.lean, Check.out, lake-manifest.json, lean-toolchain
// and the paper's main.typ; do not edit (edit those and rebuild).
#set document(title: "Appendix: Lean formalisation")
#set page(paper: "a4", margin: (x: 2.2cm, y: 2.4cm), numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt, lang: "en")
#show math.equation: set text(font: "New Computer Modern Math")
#show raw: set text(font: "DejaVu Sans Mono", size: 0.82em)
#show raw.where(block: true): set block(width: 100%, inset: (x: 6pt, y: 5pt), fill: luma(246), radius: 2pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1")
#show heading.where(level: 1): set block(above: 1.6em, below: 0.9em)
#show table: set text(size: 8.5pt)
#show table: set par(justify: false)
#show link: set text(fill: rgb("#1f4e8c"))
// the paper's notation (its notation.typ)
{notation}

#align(center)[
  #v(1cm)
  #text(size: 20pt, weight: "bold")[Appendix: Lean formalisation]
  #v(0.6cm)
  #text(size: 12pt)[Supplementary material to]
  #v(0.2cm)
  #block(width: 85%)[#text(size: 13pt, style: "italic")[{title}]]
  #v(0.4cm)
  #text(size: 12pt)[{esc(", ".join(authors))}]
  #v(1.2cm)
  #text(size: 10pt)[Lean repository revision #raw("{rev}"){" (with uncommitted changes: DRAFT)" if dirty else ""} · Lean #raw("{toolchain.split(':')[-1]}") · Mathlib #raw("{mathlib['rev'][:7]}") \\
  {nmod} modules · {ndecl} declarations tagged with labels of the paper · axioms: #raw("propext"), #raw("Classical.choice"), #raw("Quot.sound")]
]
#v(1.2cm)
#block(inset: (x: 1cm))[#set text(size: 9.5pt)
This supplement gives what a referee needs to check the paper's claim of formal verification (Section 1.3) without
the repository: the coverage and its exceptions, the main statements as they stand in Lean, the declaration of every
numbered block and proof step, and the build and axiom audit. It is generated from the repository at the revision
above. The paper's blocks are cited by their labels (such as #raw("thm-upper")), which the Lean source carries as
tags (#raw("@[kb \\"cstarpaper-<label>\\"]")).]
#v(0.6cm)
#outline(depth: 2)
#pagebreak()

= Coverage

Section 1.3 of the paper (Formal Verification) states:

#block(inset: (left: 1.2em), stroke: (left: 1pt + luma(180)))[{coverage}]

{md_to_typst(pre_kept)}
In this revision, the table of @sec-map has a row for each of the paper's {nblocks} numbered blocks, with the
declarations of their {nsteps} proof steps, and rows for {", ".join(f'#raw("{l}")' for l in others)} (conventions and
notation stated in those sections); {len(sentences)} further tags anchor sentences of the paper's text.

== Cited results

{md_to_typst(sec['Cited results'])}
''')
    T.append('= The main statements in Lean <sec-main>\n\n' + md_to_typst(sec['The main statements in Lean']))
    T.append('= The correspondence <sec-map>\n\n' + md_to_typst(sec['The correspondence'],
             table_widths='(auto, 1.3fr, 1fr)'))
    T.append('== Earlier versions\n\n' + md_to_typst(sec['Earlier versions'], table_widths='(1fr, 1fr)'))
    T.append('== The earlier formalisation\n\n' + md_to_typst(sec['The earlier formalisation']))
    for k in extra:
        T.append(f'== {inline(k)}\n\n' + md_to_typst(sec[k]))
    T.append(f'''= Build and axiom audit <sec-audit>

{md_to_typst(sec['Versions and build'])}
The full Mathlib commit is #raw("{mathlib['rev']}"); the build has {nmod} modules.

== The audit file Check.lean

```lean
{check_lean.rstrip()}
```

== Its output

All {len(ax)} declarations audited depend only on #raw("propext"), #raw("Classical.choice") and #raw("Quot.sound")
(the output of #raw("lake env lean Check.lean") at this revision; build.py checks it).

```text
{check_out.rstrip()}
```
''')
    src = '\n'.join(T)
    # a character right after an embedded expression would continue it: `;` ends the expression (and is eaten),
    # `[` or `(` would add an argument; escape it (the README has `name`; and `name`[...] in prose)
    RAWCALL = r'(#raw\("(?:[^"\\]|\\.)*"\))'
    src = re.sub(RAWCALL + r'([;\[(])', r'\1\\\2', src)
    if re.search(RAWCALL + r'[;\[(]', src): die('unescaped character after #raw(...)')
    out = os.path.join(ROOT, 'supplement', 'lean-appendix.typ')
    open(out, 'w').write(src)
    print(f'wrote {out}: {len(seen)} labels in the table, {len(sentences)} sentence tags, {len(ax)} axiom lines;'
          f' revision {rev}{" DIRTY" if dirty else ""}')
    if stale:
        print(f'note: {len(stale)} tags of labels no longer in the paper (earlier versions; not listed): {", ".join(stale)}')
    if extra:
        print(f'note: README sections appended at the end of the correspondence: {extra}')
    if rtitle and title.replace('$1\\/4$', '1/4') not in rtitle:
        print(f'WARNING: the README heading differs from the paper title:\n  {rtitle}\n  {title}')
    if not a.no_pdf:
        cmd = ['typst', 'compile', out, out[:-4] + '.pdf']
        if os.path.isdir(FONTS): cmd[2:2] = ['--font-path', FONTS]
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode: die('typst failed:\n' + r.stderr)
        print('built', out[:-4] + '.pdf')


if __name__ == '__main__':
    main()
