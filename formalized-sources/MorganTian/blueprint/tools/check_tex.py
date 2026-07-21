#!/usr/bin/env python3
"""Mechanical well-formedness check for the blueprint chapters. Reports, per file:
environment begin/end balance, brace balance, unescaped-$ parity, leftover
hygiene artifacts, and dangling \\ref targets (resolved against ALL chapters)."""
import re, glob, os, sys

CH = sys.argv[1] if len(sys.argv) > 1 else \
    "/home/Axel/HyperGraph/examples/poincaré/blueprint/src/chapters"
ENVS = ["theorem", "proposition", "lemma", "corollary", "claim", "definition",
        "example", "conjecture", "remark", "proof", "equation", "eqnarray",
        "align", "itemize", "enumerate", "figure"]
files = sorted(glob.glob(os.path.join(CH, "*.tex")))
labels = set()
for f in files:
    labels |= set(re.findall(r"\\label\{([^}]*)\}", open(f).read()))

for f in files:
    t = open(f).read()
    name = os.path.basename(f)
    issues = []
    for e in ENVS:
        b = len(re.findall(r"\\begin\{" + re.escape(e) + r"\*?\}", t))
        n = len(re.findall(r"\\end\{" + re.escape(e) + r"\*?\}", t))
        if b != n:
            issues.append(f"env {e}: begin {b} != end {n}")
    if t.count("{") != t.count("}"):
        issues.append(f"braces: {t.count('{')} open vs {t.count('}')} close")
    dollars = len(re.findall(r"(?<!\\)\$", t.replace("$$", "")))
    if dollars % 2:
        issues.append(f"odd unescaped $ count ({dollars})")
    for pat, lab in [(r"\\protect", "protect"), (r"\\index\{", "index"),
                     (r"\{\\rm\b", "{\\rm}"), (r"\\begin\{figure", "figure"),
                     (r"\\epsf", "epsf"), (r"\\relabel", "relabel")]:
        c = len(re.findall(pat, t))
        if c:
            issues.append(f"{lab}: {c}")
    dang = sorted({r for r in re.findall(r"\\(?:ref|eqref|cref|Cref)\{([^}]*)\}", t)
                   if r not in labels})
    if dang:
        issues.append(f"dangling refs ({len(dang)}): {dang}")
    print(f"{name}: {'OK' if not issues else ''}")
    for i in issues:
        print("   -", i)
