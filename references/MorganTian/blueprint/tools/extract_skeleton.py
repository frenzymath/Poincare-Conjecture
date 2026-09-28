#!/usr/bin/env python3
"""Emit the ordered theorem-environment skeleton of a source .tex as JSON.
Outputs ONLY identifiers (env kind, the book's own \\label, and any \\ref targets
in the statement body / following proof) — never prose. Used to pin annotation
ordering so build_chapter.py injection lines up exactly."""
import json, re, sys

OLD = ["thm", "prop", "lem", "cor", "claim", "defn", "exam", "conj", "rem",
       "ex", "assumption", "addendum"]
BEGIN = re.compile(r"\\begin\{(" + "|".join(OLD) + r")\}")
LABEL = re.compile(r"\A\s*(?:\[[^\]]*\])?\s*\\label\{([^}]*)\}")
REF = re.compile(r"\\(?:ref|eqref|cref|Cref)\{([^}]*)\}")

def matching_end(text, start, env):
    """index just past the \\end{env} that closes the begin at `start`."""
    depth, i, b, e = 0, start, "\\begin{" + env + "}", "\\end{" + env + "}"
    while i < len(text):
        if text.startswith(b, i): depth += 1; i += len(b)
        elif text.startswith(e, i):
            depth -= 1; i += len(e)
            if depth == 0: return i
        else: i += 1
    return len(text)

def main():
    text = open(sys.argv[1], encoding="utf-8").read()
    rows, begins = [], list(BEGIN.finditer(text))
    for k, m in enumerate(begins):
        env = m.group(1)
        end = matching_end(text, m.start(), env)
        body = text[m.end():end]
        lm = LABEL.match(body)
        book_label = lm.group(1) if lm else None
        refs_stmt = sorted(set(REF.findall(body)))
        # following proof, up to the next theorem-begin
        nxt = begins[k + 1].start() if k + 1 < len(begins) else len(text)
        tail = text[end:nxt]
        pm = re.search(r"\\begin\{proof\}", tail)
        refs_proof = []
        if pm:
            pend = matching_end(tail, pm.start(), "proof")
            refs_proof = sorted(set(REF.findall(tail[pm.end():pend])))
        rows.append({"i": k, "env_old": env, "book_label": book_label,
                     "refs_stmt": refs_stmt, "refs_proof": refs_proof})
    print(json.dumps({"count": len(rows), "rows": rows}, indent=1))

if __name__ == "__main__":
    main()
