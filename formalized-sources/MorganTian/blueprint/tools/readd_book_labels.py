#!/usr/bin/env python3
"""
Restore each statement's ORIGINAL book \label as a second anchor in the
subagent-built chapters (the script-built ones already keep it), so the book's
own prose \ref{...} cross-references resolve across the whole blueprint. Also
strips literal \protect. Purely mechanical; aligns output statements to the
source theorem-environments by order and VERIFIES the env sequence before
touching anything — on any mismatch it reports and skips that chapter.
"""
import re, sys, json, subprocess, os

TOOLS = os.path.dirname(os.path.abspath(__file__))
SRC = "/home/Axel/HyperGraph/examples/poincaré/references/latex-source"
CH = "/home/Axel/HyperGraph/examples/poincaré/blueprint/src/chapters"
CANON = {"thm": "theorem", "prop": "proposition", "lem": "lemma",
         "cor": "corollary", "claim": "claim", "defn": "definition",
         "exam": "example", "conj": "conjecture", "rem": "remark",
         "ex": "example", "assumption": "definition", "addendum": "remark"}
NEW = sorted(set(CANON.values()))
# output chapter file(s)  <-  source file   (only subagent-built chapters)
PAIRS = [
    (["Ch01_Preliminaries", "Ch02_ManifoldsNonNegativeCurvature"], "prelim"),
    (["Ch03_BasicsOfRicciFlow"], "flowbasics"),
    (["Ch05_ConvergenceResults"], "converge2"),
    (["Ch06_ComparisonGeometry"], "newcompar"),
    (["Ch08_NonCollapsed"], "noncoll"),
    (["Ch09_KappaAncientSolutions"], "temp2kappa"),
    (["Ch10_BoundedCurvatureBoundedDistance"], "bddcurvbdddist"),
    (["Ch11_GeometricLimits"], "singlimit2"),
    (["Ch12_StandardSolution"], "stdsoln"),
    (["Ch18_FiniteTimeExtinction"], "energy1"),
    (["Ch19_CanonicalNeighborhoods"], "canonnbhd"),
]
# begin -> first \label after it (lazy; tolerates any [title], even unbalanced [ ])
STMT = re.compile(r"\\begin\{(" + "|".join(NEW) + r")\}.*?\\label\{([^}]*)\}",
                  re.DOTALL)
# book \chapter labels to re-anchor \ref{secmaxprin} etc., keyed by output file
CHAP_LABELS = {
    "Ch01_Preliminaries": "sectprelim",
    "Ch02_ManifoldsNonNegativeCurvature": "nonnegcurv",
    "Ch03_BasicsOfRicciFlow": "flowbasics",
    "Ch04_MaximumPrinciple": "secmaxprin",
    "Ch06_ComparisonGeometry": "lengthfn",
    "Ch07_CompleteRicciFlows": "newcomp2",
    "Ch08_NonCollapsed": "noncoll",
    "Ch09_KappaAncientSolutions": "kappasect",
    "Ch12_StandardSolution": "stdsolnsect",
    "Ch14_RicciFlowWithSurgery": "sect:surgery",
    "Ch16_ProofNonCollapsing": "sectnoncoll",
    "Ch18_FiniteTimeExtinction": "energy",
    "Ch19_CanonicalNeighborhoods": "sect:canonnbhd",
}


def skeleton(srcfile):
    out = subprocess.check_output(
        [sys.executable, os.path.join(TOOLS, "extract_skeleton.py"),
         os.path.join(SRC, srcfile + ".tex")], text=True)
    return json.loads(out)["rows"]


def main():
    total_added = 0
    for outfiles, srcfile in PAIRS:
        rows = skeleton(srcfile)
        # gather output statements across the (possibly two) output files in order
        outstmts = []  # (fileidx, env, semantic_label, match_start, match_end)
        texts = []
        for fi, of in enumerate(outfiles):
            t = open(os.path.join(CH, of + ".tex")).read()
            texts.append(t)
            for m in STMT.finditer(t):
                outstmts.append((fi, m.group(1), m.group(2), m.start(), m.end()))
        tag = "+".join(outfiles)
        if len(outstmts) != len(rows):
            print(f"SKIP {tag}: {len(outstmts)} output stmts != {len(rows)} "
                  f"source envs")
            continue
        # verify env sequence
        bad = None
        for i, (row, (fi, env, sem, a, b)) in enumerate(zip(rows, outstmts)):
            if CANON[row["env_old"]] != env:
                bad = (i, CANON[row["env_old"]], env, row.get("book_label"))
                break
        if bad:
            print(f"SKIP {tag}: env mismatch at stmt #{bad[0]} "
                  f"(source {bad[1]} vs output {bad[2]}, book_label {bad[3]})")
            continue
        # build insertions per file (reverse order so offsets stay valid)
        ins = {fi: [] for fi in range(len(outfiles))}
        added = 0
        for row, (fi, env, sem, a, b) in zip(rows, outstmts):
            bl = row.get("book_label")
            if bl and bl != sem and ("\\label{" + bl + "}") not in texts[fi]:
                ins[fi].append((b, "\n\\label{" + bl + "}"))
                added += 1
        for fi, of in enumerate(outfiles):
            t = texts[fi]
            for pos, s in sorted(ins[fi], reverse=True):
                t = t[:pos] + s + t[pos:]
            t = t.replace("\\protect", "")            # strip literal \protect
            open(os.path.join(CH, of + ".tex"), "w").write(t)
        total_added += added
        print(f"OK   {tag}: re-added {added} book labels")
    # re-anchor book \chapter labels + strip \protect across every chapter file
    chap_added = 0
    for f in os.listdir(CH):
        if not f.endswith(".tex"):
            continue
        p, base = os.path.join(CH, f), f[:-4]
        t = open(p).read()
        bl = CHAP_LABELS.get(base)
        if bl and ("\\label{" + bl + "}") not in t:
            t, n = re.subn(r"(\\chapter\*?\{(?:[^{}]|\{[^{}]*\})*\}\s*\\label\{"
                           r"chap:[^}]*\})",
                           r"\1\n\\label{" + bl + "}", t, count=1)
            chap_added += n
        t = t.replace("\\protect", "")
        open(p, "w").write(t)
    print(f"\nTOTAL statement labels re-added: {total_added}; "
          f"chapter labels re-added: {chap_added}")


if __name__ == "__main__":
    main()
