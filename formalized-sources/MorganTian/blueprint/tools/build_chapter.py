#!/usr/bin/env python3
"""
build_chapter.py — deterministically turn a Morgan-Tian arXiv source chapter into
an hgraph blueprint chapter, WITHOUT regenerating any prose.

It byte-copies the verbatim mathematical text straight from your local source in
references/latex-source/ and only performs mechanical edits + injects the graph
metadata (titles / semantic labels / \\uses) supplied in a small JSON annotations
file. No model runs at build time; this is a text transform of a file you already
have (a smarter `sed`).

Usage:
    python build_chapter.py SOURCE.tex ANNOTATIONS.json OUTPUT.tex

ANNOTATIONS.json:
    {"chapter_labels": ["chap:...", ...],          # one per \\chapter, in order
     "statements": [                               # one per theorem-like env, DOC ORDER
       {"env": "theorem",                          # MUST equal CANON[env_old]
        "title": "...", "label": "thm:...",
        "uses": ["def:..."], "proof_uses": ["lem:..."]}, ...]}

The book's own \\label{...} is kept in place (so prose \\ref{...} still resolves);
our semantic \\label is injected first, which is what hgraph keys the node off.
"""
import json, re, sys

# fixed old->recognized environment map (begin AND end renamed identically)
CANON = {"thm": "theorem", "prop": "proposition", "lem": "lemma",
         "cor": "corollary", "claim": "claim", "defn": "definition",
         "exam": "example", "conj": "conjecture", "rem": "remark",
         "ex": "example", "assumption": "definition", "addendum": "remark"}
NEW_ENVS = sorted(set(CANON.values()))
STMT_BEGIN = re.compile(r"\\begin\{(" + "|".join(NEW_ENVS) + r")\}(\s*\[[^\]]*\])?")
RM_OPS = ["Ric", "Rm", "Hess", "Vol", "vol", "Jac", "sn", "ct", "dist", "diam",
          "inj", "Sym", "Hom", "End", "Spec", "Tr", "tr", "Id", "Area",
          "Length", "scal", "Ker"]


def strip_balanced(text, cmd):
    out, i, n, tok = [], 0, len(text), "\\" + cmd + "{"
    while i < n:
        if text.startswith(tok, i):
            depth, j = 1, i + len(tok)
            while j < n and depth:
                depth += {"{": 1, "}": -1}.get(text[j], 0); j += 1
            i = j
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def remove_env_blocks(text, env):
    return re.sub(r"\\begin\{" + env + r"\}.*?\\end\{" + env + r"\}", "",
                  text, flags=re.DOTALL)


def rename_envs(text):
    for old, new in CANON.items():
        text = re.sub(r"\\begin\{" + old + r"\}", r"\\begin{" + new + "}", text)
        text = re.sub(r"\\end\{" + old + r"\}", r"\\end{" + new + "}", text)
    return text


def normalize_rm(text):
    for op in RM_OPS:
        text = re.sub(r"\{\\rm\s+" + op + r"\}", "\\\\" + op, text)
    return re.sub(r"\{\\rm\s+([A-Za-z][A-Za-z0-9]*)\}", r"\\mathrm{\1}", text)


def inject_chapter_labels(text, labels):
    it = iter(labels)
    pat = re.compile(r"\\chapter\*?\{(?:[^{}]|\{[^{}]*\})*\}(?:\s*\\label\{[^}]*\})?")
    def repl(m):
        try:
            lab = next(it)
        except StopIteration:
            return m.group(0)
        chap = re.match(r"\\chapter\*?\{(?:[^{}]|\{[^{}]*\})*\}", m.group(0)).group(0)
        return chap + "\n\\label{" + lab + "}"
    return pat.sub(repl, text)


def main():
    src_path, ann_path, out_path = sys.argv[1], sys.argv[2], sys.argv[3]
    text = open(src_path, encoding="utf-8").read()
    ann = json.load(open(ann_path, encoding="utf-8"))
    stmts = ann["statements"]

    # 1. hygiene: figures / picture boxes / eps includes
    for env in ("figure", r"figure\*", "relabelbox", "wrapfigure"):
        text = remove_env_blocks(text, env)
    text = re.sub(r"\\(centerline|epsffile|epsfbox|epsfig|includegraphics)"
                  r"(\[[^\]]*\])?\{[^}]*\}", "", text)
    text = re.sub(r"^.*\\(relabel|adjustrelabel|extralabel)\b.*$", "",
                  text, flags=re.MULTILINE)
    # 2. index / marginal notes / include machinery
    for cmd in ("index", "note"):
        text = strip_balanced(text, cmd)
    text = re.sub(r"\\(includeonly|include|input)\{[^}]*\}", "", text)
    # 3. operator normalization, 4. env rename (begin+end), 5. chapter labels
    text = normalize_rm(text)
    text = rename_envs(text)
    text = inject_chapter_labels(text, ann.get("chapter_labels", []))

    # 6. inject semantic header (title + \label + statement \uses) per statement
    counter = {"i": 0}
    def stmt_repl(m):
        i = counter["i"]
        if i >= len(stmts):
            raise SystemExit(f"ERROR: source has more theorem envs than the "
                             f"{len(stmts)} annotations (stopped at #{i+1}).")
        s = stmts[i]; counter["i"] += 1
        env = m.group(1)
        if s["env"] != env:
            raise SystemExit(f"ERROR stmt #{i+1}: annotation env '{s['env']}' "
                             f"!= source env '{env}'. Ordering mismatch.")
        head = "\\begin{" + env + "}[" + s["title"] + "]\n\\label{" + s["label"] + "}"
        if s.get("uses"):
            head += "\n\\uses{" + ",".join(s["uses"]) + "}"
        return head
    text = STMT_BEGIN.sub(stmt_repl, text)
    if counter["i"] != len(stmts):
        raise SystemExit(f"ERROR: {len(stmts)} annotations but "
                         f"{counter['i']} envs matched.")

    # 7. inject proof-level \uses into the first proof after each statement
    counter["i"] = 0; pend = {"pu": None}
    walk = re.compile(r"\\begin\{(" + "|".join(NEW_ENVS) + r"|proof)\}")
    def wrepl(m):
        if m.group(1) == "proof":
            pu = pend["pu"]; pend["pu"] = None
            return "\\begin{proof}\n\\uses{" + ",".join(pu) + "}" if pu else m.group(0)
        pend["pu"] = stmts[counter["i"]].get("proof_uses") or None
        counter["i"] += 1
        return m.group(0)
    text = walk.sub(wrepl, text)

    open(out_path, "w", encoding="utf-8").write(text)
    kinds = {}
    for s in stmts:
        kinds[s["env"]] = kinds.get(s["env"], 0) + 1
    print(f"wrote {out_path}: {len(stmts)} nodes " +
          ", ".join(f"{k}={v}" for k, v in sorted(kinds.items())))


if __name__ == "__main__":
    main()
