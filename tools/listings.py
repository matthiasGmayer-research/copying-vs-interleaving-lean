#!/usr/bin/env python3
"""The Lean listings of README.md ("The main statements in Lean"; formerly the paper's Appendix F.1), extracted from the source of this repository, and their check.

usage:
  tools/listings.py                      print the listings (one block per paper listing) to stdout
  tools/listings.py --out FILE           also write them to FILE
  tools/listings.py --check README.md    compare with the ```lean blocks of README.md (or of a .typ with <app-lean-main>)

Extraction: each declaration is copied verbatim from its source file, from its first line (after the docstring and
the attributes) to the end of the declaration header: for a theorem up to `:=` (the proof is dropped), for a
definition or structure up to the first blank line, without one-line field docstrings. A comment
`-- namespace N` precedes declarations outside the namespace `CopyingInterleaving` (the paper's convention).

Check: the listings in the paper are split into declaration units (a unit starts at a declaration keyword, with the
namespace comment before it); each unit is compared, whitespace-normalised, with the extracted unit of the same
declaration. Reported: units that agree, units that differ (with a diff), units of the paper that name no extracted
declaration, and extracted declarations that the paper does not list. Exit status 1 if a unit differs or is unknown.
"""
import argparse, difflib, os, re, sys

ROOT = os.environ.get("LISTINGS_ROOT") or os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "CopyingInterleaving")

S = "Setting.lean"
PRELIM = "Paper/Prelim/Defs.lean"
SCSTRUCT = "Paper/SCStructure/Defs.lean"
# (block, namespace comment or None, source file relative to CopyingInterleaving/, start of the declaration's first line)
SPEC = [
    ("arcs", None, S, "structure ArithInterval where"),
    ("arcs", None, S, "def ArithInterval.apply"),
    ("arcs", None, S, "instance : CoeFun ArithInterval"),
    ("arcs", None, S, "def readAt "),
    ("arcs", None, S, "def Covers "),
    ("arcs", None, S, "def IsARS "),
    ("arcs", None, S, "noncomputable def ARC "),
    ("zlp", None, S, "def zip {"),
    ("zlp", None, S, "structure SlotGraph "),
    ("zlp", None, S, "def SlotGraph.arity "),
    ("zlp", None, S, "def SlotGraph.Edge "),
    ("zlp", None, S, "def SlotGraph.valFuel "),
    ("zlp", None, S, "structure Program "),
    ("zlp", None, S, "def Program.IsZLP "),
    ("zlp", None, S, "noncomputable def Program.value "),
    ("zlp", None, S, "noncomputable def Program.val "),
    ("zlp", None, S, "noncomputable def Program.size "),
    ("zlp", None, S, "noncomputable def ZLC "),
    ("sync", "CopyingInterleaving.Paper.Prelim", PRELIM, "def IsSynchronous "),
    ("sync", "CopyingInterleaving.Paper.Prelim", PRELIM, "noncomputable def sZLC "),
    ("occ", None, S, "structure Occ where"),
    ("occ", None, S, "instance : CoeFun Occ"),
    ("occ", None, S, "inductive Program.OccVia "),
    ("occ", None, S, "def Program.occ "),
    ("misc", None, S, "noncomputable def log2 "),
    ("misc", "CopyingInterleaving.Statements", "Statements/Statement.lean", "def AdmissibleOAlpha "),
    ("misc", "CopyingInterleaving.Paper.C1Structure", "Paper/C1Structure/Defs.lean", "noncomputable def n (k L"),
    ("misc", "CopyingInterleaving.Paper.C1Structure", "Paper/C1Structure/Defs.lean", "noncomputable def x (k L"),
    ("upper", "CopyingInterleaving.Paper.U12a", "Paper/U12a/Statement.lean", "theorem thm_upper "),
    ("lower", "CopyingInterleaving.Paper.C1Lower", "Paper/C1Lower/Defs.lean", "def lossFactor "),
    ("lower", "CopyingInterleaving.Paper.C1Lower", "Paper/C1Lower/Statement.lean", "theorem thm_lower "),
    ("cors", "CopyingInterleaving.Paper.CorDirect", "Paper/CorDirect/Statement.lean", "theorem cor_cstar "),
    ("cors", "CopyingInterleaving.Paper.CorDirect", "Paper/CorDirect/Statement.lean", "theorem cor_szlc "),
    ("reverse", "CopyingInterleaving.Paper.ReverseZ", "Paper/ReverseZ/Statement.lean", "theorem prop_reverse "),
]

DECL = re.compile(r"^(?:noncomputable |private |protected )*(theorem|lemma|def|structure|instance|inductive|abbrev|class)\b")


def grab(path, header):
    lines = open(os.path.join(ROOT, path), encoding="utf-8").read().splitlines()
    idx = [i for i, l in enumerate(lines) if l.startswith(header)]
    if len(idx) != 1:
        sys.exit(f"listings.py: {path}: {len(idx)} lines start with {header!r} (expected 1)")
    theorem = header.startswith(("theorem", "lemma"))
    out, i = [], idx[0]
    while i < len(lines):
        l = lines[i]
        if l.strip() == "":
            break
        if theorem and ":=" in l:
            head = l[: l.index(":=")].rstrip()
            if head.strip():
                out.append(head)
            break
        if re.match(r"^\s*/--.*-/\s*$", l):  # one-line docstring of a field
            i += 1
            continue
        out.append(l)
        i += 1
    return "\n".join(out)


def extract():
    """[(block, name, text)] in SPEC order; text includes the namespace comment."""
    res = []
    for block, ns, path, header in SPEC:
        text = grab(path, header)
        if ns:
            text = f"-- namespace {ns}\n" + text
        res.append((block, decl_name(text), text))
    return res


def unit_ns(unit):
    ns = re.search(r"^-- namespace (\S+)", unit, re.M)
    return ns.group(1) if ns else None


def decl_name(unit, ns=None):
    """The declaration's name, qualified by its namespace (the unit's comment, else `ns`), e.g. `CopyingInterleaving.ARC`."""
    ns = unit_ns(unit) or ns or "CopyingInterleaving"
    for l in unit.splitlines():
        m = DECL.match(l)
        if m:
            rest = l[m.end():].split()
            if m.group(1) == "instance":
                return ns + ".instance " + " ".join(rest[:3])
            return ns + "." + rest[0]
    return None


def norm(t):
    """Whitespace-normalised, without the namespace comments (the namespace is compared through the name)."""
    return " ".join(" ".join(l for l in t.splitlines() if not l.startswith("-- namespace ")).split())


def paper_units(main):
    src = open(main, encoding="utf-8").read()
    # README.md (since 2026-10-28) marks the section with HTML comments; the paper's former App. F used labels
    ma, mb = ("<!-- app-lean-main -->", "<!-- app-lean-map -->") if "<!-- app-lean-main -->" in src else ("<app-lean-main>", "<app-lean-map>")
    a = src.index(ma)
    b = src.index(mb, a)
    units = []  # (unit, namespace in force: the last namespace comment of the block, else CopyingInterleaving)
    for blk in re.findall(r"```lean\n(.*?)```", src[a:b], re.S):
        cur, ns = [], None
        def push():
            nonlocal ns
            u = "\n".join(cur).strip("\n")
            ns = unit_ns(u) or ns
            units.append((u, ns))
        for l in blk.splitlines():
            starts = DECL.match(l) or l.startswith("-- namespace ")
            # a namespace comment or a declaration keyword starts a new unit (a namespace comment directly
            # before a declaration belongs to it)
            if starts and cur and not (DECL.match(l) and cur[-1].startswith("-- namespace ")
                                       and all(x.startswith("-- namespace ") or not x.strip() for x in cur)):
                if any(x.strip() for x in cur):
                    push()
                cur = []
            cur.append(l)
        if any(x.strip() for x in cur):
            push()
    return units


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out")
    ap.add_argument("--check")
    args = ap.parse_args()
    ex = extract()
    blocks = []
    for block, _, text in ex:
        if not blocks or blocks[-1][0] != block:
            blocks.append((block, []))
        blocks[-1][1].append(text)
    listing = "\n\n".join(f"== {b} ==\n" + "\n\n".join(ts) for b, ts in blocks) + "\n"
    if not args.check or args.out:
        if args.out:
            open(args.out, "w", encoding="utf-8").write(listing)
        else:
            sys.stdout.write(listing)
    if not args.check:
        return 0
    byname = {n: t for _, n, t in ex}
    seen, bad = set(), 0
    for u, ns in paper_units(args.check):
        n = decl_name(u, ns)
        if n not in byname:
            print(f"UNKNOWN   {n}: the paper lists a declaration the extractor does not know")
            bad += 1
            continue
        seen.add(n)
        if norm(u) == norm(byname[n]):
            print(f"OK        {n}")
        else:
            bad += 1
            print(f"DIFFERS   {n}")
            for d in difflib.unified_diff(byname[n].splitlines(), u.splitlines(), "repository", "paper", lineterm=""):
                print("    " + d)
    for _, n, _ in ex:
        if n not in seen:
            print(f"NOT IN PAPER  {n}")
    print(f"listing check: {len(seen)} units compared, {bad} differing or unknown")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
