#!/usr/bin/env python3
"""The paper tags of the Lean source: every declaration tagged `@[kb "cstarpaper-<label>" ...]` (commented tags are
retired and skipped). usage: supplement/tags.py [--json]   (run from the repository root)."""
import json, os, re, sys

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |partial |unsafe )*'
                  r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([^\s:({\[]+)')
TAG = re.compile(r'kb "cstarpaper-([^"]+)"')

def scan(root='SP'):
    tags = {}
    for d, _, fs in os.walk(root):
        for f in sorted(fs):
            if not f.endswith('.lean'): continue
            path = os.path.join(d, f)
            ns, pending = [], []
            lines = open(path).read().split('\n')
            in_doc = False
            for line in lines:
                s = line.strip()
                if in_doc:
                    if '-/' in s: in_doc = False
                    continue
                if s.startswith('/-') and '-/' not in s[2:]:
                    in_doc = True; continue
                if s.startswith('--'): continue
                m = re.match(r'namespace\s+(\S+)', s)
                if m: ns.append(m.group(1)); continue
                m = re.match(r'end\s+(\S+)', s)
                if m and ns and ns[-1] == m.group(1): ns.pop(); continue
                if s.startswith('@['):
                    pending += TAG.findall(s)
                m = DECL.match(s)
                if m and pending:
                    name = m.group(2)
                    full = name[1:] if name.startswith('_root_.') else '.'.join(ns + [name])
                    for lab in pending:
                        tags.setdefault(lab, []).append((full, path))
                    pending = []
                elif m:
                    pending = []
    return tags

if __name__ == '__main__':
    t = scan()
    if '--json' in sys.argv:
        print(json.dumps({k: [n for n, _ in v] for k, v in sorted(t.items())}, indent=1, ensure_ascii=False))
    else:
        for k, v in sorted(t.items()):
            print(k, ' '.join(n for n, _ in v))
