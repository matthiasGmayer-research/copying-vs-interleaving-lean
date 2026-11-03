#!/bin/bash
# Export the Lean of the cstar paper from the SP project (its import closure only) into this repository.
# usage: ./export.sh   (WITH_TEXT=1 also exports SP/CstarText, the formalisation along the paper's text, once it is complete)
set -euo pipefail
SRC=${SRC:-$HOME/projects/SP/lean}
cd "$(dirname "$0")"
ROOTS="SP.CstarPaper.Statement SP.Reverse.Statement SP.ReverseUpper.Statement"
[ "${WITH_TEXT:-0}" = 1 ] && [ -d "$SRC/SP/CstarText" ] && ROOTS="$ROOTS $(cd "$SRC" && find SP/CstarText -name '*.lean' | sed 's#\.lean$##; s#/#.#g' | tr '\n' ' ')"
rm -rf SP CopyingInterleaving SP.lean CopyingInterleaving.lean; mkdir CopyingInterleaving
python3 - "$SRC" $ROOTS <<'PY'
import os, re, shutil, sys
sys.path.insert(0, os.getcwd())
import rename_map   # the recorded rename map (SP -> CopyingInterleaving, CstarText -> Paper, ...)
src, roots = sys.argv[1], sys.argv[2:]
seen, todo = set(), list(roots)
while todo:
    m = todo.pop()
    if m in seen: continue
    seen.add(m)
    f = os.path.join(src, m.replace('.', '/') + '.lean')
    for l in open(f):
        mm = re.match(r'import (SP[\w.]*)', l)
        if mm: todo.append(mm.group(1))
for m in sorted(seen):
    rel = m.replace('.', '/') + '.lean'
    out = rename_map.path(rel)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    s = open(os.path.join(src, rel)).read()
    if rel == 'SP/Setting.lean':   # Kosoy's cube-root bound is cited in SP but used by nothing exported
        a = s.index('/-! ## Kosoy\'s results used here -/'); b = s.rindex('end SP')
        s = s[:a] + s[b:]
    open(out, 'w').write(rename_map.text(s))
open('CopyingInterleaving.lean', 'w').write(rename_map.text(''.join(f'import {m}\n' for m in sorted(seen))))
print(len(seen), 'modules')
PY
cp "$SRC/lean-toolchain" "$SRC/lake-manifest.json" .
sed -e "0,/^name = \"SP\"/s//name = \"copying-vs-interleaving-lean\"/" -e 's/^defaultTargets = \["SP"\]/defaultTargets = ["CopyingInterleaving"]/' -e 's/^name = "SP"$/name = "CopyingInterleaving"/' "$SRC/lakefile.toml" > lakefile.toml
