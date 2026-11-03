#!/usr/bin/env python3
"""The rename map of the exported repository (user 2026-11-03, c-0097). The SP source is unchanged; export.sh applies this
transform to every exported module, so re-exports reproduce it. Also used on the hand-written files (Check.lean, README.md,
supplement/*.py) when the map changes.

  library and root namespace   SP            -> CopyingInterleaving   (SP.lean -> CopyingInterleaving.lean, folder SP/)
  formalisation along the text SP.CstarText  -> CopyingInterleaving.Paper
  other Cstar-prefixed modules (root level; none collides with an existing module or namespace component):
    Cstar -> Main (the main result)         CstarPaper -> Statements        CstarConst -> Constants
    CstarUpper -> Upper                     CstarSC -> SC, CstarSCxxx -> SCxxx   (the SC namespace of the same name is
    a namespace only; modules SC, SCAP, SCChoice, SCCores, SCParams, SCProgram, SCStructure, SCThm do not exist at root)
  revision-history module names (C1Referee, RefereeRev, ...) are kept.
"""
import re

COMP = {'CstarText': 'Paper', 'CstarPaper': 'Statements', 'CstarConst': 'Constants', 'CstarUpper': 'Upper',
        'Cstar': 'Main'}
ROOT = 'CopyingInterleaving'


def comp(m):
    w = m.group(0)
    if w in COMP: return COMP[w]
    if w.startswith('CstarSC'): return w[len('Cstar'):]
    return w


def text(s):
    s = re.sub(r'\bCstar[A-Za-z0-9_]*\b', comp, s)
    s = re.sub(r'\bSP(?=[./][A-Za-z_«])', ROOT, s)
    s = re.sub(r'(?m)^((?:namespace|end|open|import|export|section)\b[^\n]*)', lambda m: re.sub(r'\bSP\b', ROOT, m.group(1)), s)
    return s


def path(rel):
    """'SP/CstarText/X.lean' -> 'CopyingInterleaving/Paper/X.lean'; 'SP.lean' -> 'CopyingInterleaving.lean'."""
    parts = rel.split('/')
    out = []
    for i, p in enumerate(parts):
        stem, dot, ext = p.partition('.')
        if i == 0 and stem == 'SP': stem = ROOT
        else: stem = re.sub(r'\bCstar[A-Za-z0-9_]*\b', comp, stem)
        out.append(stem + dot + ext)
    return '/'.join(out)


if __name__ == '__main__':
    import sys
    for f in sys.argv[1:]:
        s = open(f).read(); t = text(s)
        if s != t: open(f, 'w').write(t)
