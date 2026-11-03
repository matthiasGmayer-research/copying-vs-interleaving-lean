#!/usr/bin/env python3
"""Run the dependency-route check of tools/Deps.lean on every declaration named in the correspondence table of README.md (formerly the paper's App. F.2).

usage: tools/deps.py README.md [--lean-dir DIR]
Reads the names in backquotes from the table `tab-lean` of README.md (or of a .typ) (relative to CopyingInterleaving.Paper unless they begin
with SP.), writes a copy of tools/Deps.lean with these targets to a temporary file in DIR (default: this repository)
and runs `lake env lean` on it in DIR. Prints one line per declaration: its route and, if it uses theorems outside
CopyingInterleaving.Paper, which. Unknown names are reported by Lean as errors.
"""
import argparse, os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


def table_names(main):
    src = open(main, encoding="utf-8").read()
    if "<!-- tab-lean -->" in src:   # README.md (since 2026-10-28)
        a = src.index("<!-- tab-lean -->")
        b = src.index("<!-- /tab-lean -->", a)
    else:                            # the paper's former App. F.2 (Typst table tab-lean)
        a = src.index("table.header([*paper*]")
        b = src.index(")\n})", a) if ")\n})" in src[a:] else len(src)
    names = []
    for row in src[a:b].splitlines():
        if row.strip().startswith("//"):
            continue
        for n in re.findall(r"`([^`\s]+)`", row):
            n = n.strip().rstrip(",")
            if not re.match(r"^[\w.'αβγδεζηθικλμνξοπρστυφχψωΓΔΘΛΞΠΣΦΨΩ₀-₉]+$", n):
                continue
            full = n if n.startswith("CopyingInterleaving.") else "CopyingInterleaving.Paper." + n
            if full not in names:
                names.append(full)
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("main")
    ap.add_argument("--lean-dir", default=os.path.join(HERE, ".."))
    args = ap.parse_args()
    names = table_names(args.main)
    src = open(os.path.join(HERE, "Deps.lean"), encoding="utf-8").read()
    a = src.index("def targets : List Name := [")
    b = src.index("]", a)
    body = ",\n".join(f"  `{n}" for n in names)
    src = src[:a] + "def targets : List Name := [\n" + body + src[b:]
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=args.lean_dir, delete=False, encoding="utf-8") as f:
        f.write(src)
        tmp = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", tmp], cwd=args.lean_dir, capture_output=True, text=True)
    finally:
        os.unlink(tmp)
    out = r.stdout + r.stderr
    sys.stdout.write(out)
    routes = re.findall(r"^  (USES THE EARLIER ROUTE|TEXT ROUTE, with|TEXT ROUTE \()", out, re.M)
    print(f"deps: {len(names)} table names; earlier route: {routes.count('USES THE EARLIER ROUTE')}, "
          f"text route with helpers: {routes.count('TEXT ROUTE, with')}, text route only: {routes.count('TEXT ROUTE (')}")
    return r.returncode


if __name__ == "__main__":
    sys.exit(main())
