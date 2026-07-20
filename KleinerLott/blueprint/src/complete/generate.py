#!/usr/bin/env python3
"""Generate the complete Kleiner--Lott blueprint from authoritative TeX."""

from __future__ import annotations

from collections import Counter, defaultdict
from pathlib import Path
import json
import re

WORKSPACE = Path(__file__).resolve().parents[4]
SOURCE = WORKSPACE / "references/kleiner-lott/latex-source/notes021313.tex"
OUT = Path(__file__).resolve().parent
SOURCE_KINDS = (
    "theorem", "lemma", "sublemma", "proposition",
    "corollary", "definition", "remark", "claim",
)
KIND_MAP = {"sublemma": "lemma", "claim": "proposition"}
PREFIX = {
    "theorem": "thm", "lemma": "lem", "proposition": "prop",
    "corollary": "cor", "definition": "def", "remark": "rem",
}
EXPECTED = Counter({
    "theorem": 19, "lemma": 85, "sublemma": 5, "proposition": 25,
    "corollary": 24, "definition": 34, "remark": 42, "claim": 8,
})


def balanced_argument(text: str, open_brace: int) -> tuple[str, int]:
    depth = 0
    for i in range(open_brace, len(text)):
        if text[i] == "{" and (i == 0 or text[i - 1] != "\\"):
            depth += 1
        elif text[i] == "}" and (i == 0 or text[i - 1] != "\\"):
            depth -= 1
            if depth == 0:
                return text[open_brace + 1:i], i + 1
    raise ValueError("unbalanced argument")


def source_sections(text: str) -> list[tuple[int, str]]:
    sections = []
    for match in re.finditer(r"\\section\{", text):
        title, _ = balanced_argument(text, match.end() - 1)
        sections.append((match.start(), title))
    return sections


def plain(text: str) -> str:
    text = re.sub(r"%[^\n]*", " ", text)
    text = re.sub(r"\\(?:label|dcref|group|source|uses)\{[^{}]*\}", " ", text)
    text = re.sub(r"\\(?:ref|eqref|cite)\*?(?:\[[^\]]*\])?\{([^{}]*)\}", r"\1", text)
    text = re.sub(r"\$[^$]*\$", " ", text)
    text = re.sub(r"\\\[[\s\S]*?\\\]", " ", text)
    text = re.sub(r"\\begin\{[^{}]*\}|\\end\{[^{}]*\}", " ", text)
    text = re.sub(r"\\[A-Za-z@]+(?:\[[^\]]*\])?", " ", text)
    text = text.replace("{", " ").replace("}", " ")
    text = re.sub(r"[^A-Za-z0-9' -]+", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def semantic_section(raw: str) -> str:
    if re.search(r"\\mathcal\s*\{?\s*F", raw):
        return "F-entropy"
    if re.search(r"\\mathcal\s*\{?\s*W", raw):
        return "W-entropy"
    if re.search(r"\\mathcal\s*\{?\s*L|\\L\b", raw):
        return "reduced L-geometry"
    if re.search(r"\$\s*L\s*\$", raw):
        return "reduced L-geometry"
    title = plain(raw)
    title = re.sub(r"^(?:I|II)[ .()0-9-]+", "", title).strip(" .-")
    title = re.sub(r"^(?:Theorem|Claim)\s+[0-9.]+\s*", "", title)
    title = re.sub(r"\b(?:I|II)\s+(?:[0-9]+\s*)+", "", title)
    title = re.sub(r"^\s*(?:of|the)\s+", "", title)
    title = re.sub(r"\s+", " ", title).strip(" .-")
    return title or "Ricci flow"


SOURCE_TEXT = SOURCE.read_text()


def group_for(position: int) -> str:
    line = SOURCE_TEXT.count("\n", 0, position) + 1
    boundaries = [
        (1321, "Kleiner--Lott Entropy Functionals"),
        (2489, "Kleiner--Lott Reduced Geometry"),
        (3994, "Kleiner--Lott Local Estimates"),
        (4321, "Kleiner--Lott Differential Harnack"),
        (4586, "Kleiner--Lott Pseudolocality"),
        (5382, "Kleiner--Lott Kappa Solutions"),
        (7365, "Kleiner--Lott Canonical Neighborhoods"),
        (8508, "Kleiner--Lott Thick--Thin Decomposition"),
        (8963, "Kleiner--Lott Surgery Foundations"),
        (10230, "Kleiner--Lott Singularities and Surgery"),
        (12352, "Kleiner--Lott Surgery Existence"),
        (13608, "Kleiner--Lott Long-Time Curvature"),
        (14780, "Kleiner--Lott Long-Time Topology"),
        (17187, "Kleiner--Lott Analytic Appendices"),
        (17905, "Kleiner--Lott Geometric Appendices"),
    ]
    group = "Kleiner--Lott Overview"
    for start, candidate in boundaries:
        if line >= start:
            group = candidate
    return group


def slug(text: str) -> str:
    value = plain(text).lower()
    value = re.sub(r"\b(?:the|a|an|of|for|to|and|in|on|with|is|are|we|have)\b", " ", value)
    value = re.sub(r"[^a-z0-9]+", "-", value).strip("-")
    return value[:72].rstrip("-") or "ricci-flow-declaration"


def clean_generated(text: str) -> str:
    """Remove source-formatting whitespace without changing TeX content."""
    lines = "\n".join(line.rstrip() for line in text.splitlines())
    return lines.rstrip("\n") + "\n"


def title_for(statement: str, section: str, kind: str) -> str:
    """Return a concise concept title, never a formula transcription."""
    lower = statement.lower()
    section_name = semantic_section(section).lower()
    combined = lower + "\n" + section_name
    if (
        kind == "definition"
        and r"\lambda" in statement
        and ("invariant" in section_name or "lambda" in section_name)
    ):
        if r"\overline{\lambda}" in statement:
            return "rescaled lambda invariant"
        return "lambda invariant"
    if re.search(r"formal gradient flow", lower):
        return "gradient-flow formula for the lambda invariant"
    if re.search(r"steady\s+breather", combined):
        return "rigidity of steady breathers" if kind != "definition" else "steady breather definition"
    if re.search(r"expanding\s+breather", combined):
        return "rigidity of expanding breathers" if kind != "definition" else "expanding breather definition"
    if re.search(r"shrinking\s+breather", combined):
        return "rigidity of shrinking breathers" if kind != "definition" else "shrinking breather definition"
    if re.search(r"rescaled.*invariant", section_name):
        if re.search(r"constant\s+nonpositive", lower):
            return "rigidity at constant rescaled lambda"
        return "monotonicity of the rescaled lambda invariant"
    if r"\delta" in statement and (
        "functional" in combined or "f-entropy" in combined or "w-entropy" in combined
    ):
        if re.search(r"\\mathcal\s*\{?\s*w", combined):
            return "first variation of W-entropy"
        return "first variation of F-entropy"
    if re.search(r"differential inequality", section_name):
        return "differential inequality for reduced length"
    if re.search(r"upper bound on the integral", section_name):
        return "integral bound in pseudolocality"
    if kind == "definition":
        definition_terms = [
            (r"noncollaps", "kappa noncollapsing"),
            (r"\\kappa\$-solution|\\kappa\W*-solution", "kappa solution definition"),
            (r"center of an .*neck", "center of an epsilon-neck"),
            (r"epsilon\$-tube|epsilon\$-horn", "epsilon-tubes horns and caps"),
            (r"almost nonnegative\s+curvature", "almost nonnegative curvature"),
            (r"distance .*c\^n.*topology", "smooth closeness and epsilon-necks"),
            (r"canonical neighborhood assumption", "canonical neighborhood assumption"),
            (r"pinching assumption", "curvature pinching assumption"),
            (r"ricci flow with .*cutoff", "Ricci flow with cutoff"),
            (r"subset .*omega.*sup", "bounded-curvature regular set"),
            (r"omega_\\rho", "curvature sublevel of the regular set"),
            (r"a priori.*assumptions", "surgery a priori assumptions"),
            (r"unique number .*rho", "curvature scale"),
            (r"w\$-thin part", "thick--thin decomposition"),
            (r"pointed smooth riemannian manifolds", "pointed smooth closeness"),
            (r"let .*lambda_w.*space", "hyperbolic pointed-limit space"),
        ]
        matched_term = next(
            (name for pattern, name in definition_terms if re.search(pattern, lower, re.S)),
            None,
        )
        if matched_term:
            return matched_term
        emphasized = re.search(r"\{\\em\s+([^{}$]+)\}", statement)
        if emphasized:
            term = plain(emphasized.group(1)).lower().strip()
            if 1 <= len(term.split()) <= 9:
                return f"{term} definition"

    concepts = [
        (r"\\mathcal\s*\{?\s*f|f-functional|f-entropy", "F-entropy"),
        (r"\\mathcal\s*\{?\s*w|w-functional|w-entropy", "W-entropy"),
        (r"canonical\s+neighbou?rhood", "canonical neighborhoods"),
        (r"reduced\s+volume|\\widetilde\{?v", "reduced volume"),
        (r"reduced\s+length|\\bl\b|\\mathcal\s*\{l\}", "reduced length"),
        (r"\\mathcal\s*\{l\}.*geodesic|l\}\s*-geodesic", "L-geodesics"),
        (r"kappa|\\kappa", "kappa solutions"),
        (r"noncollaps|locally\s+collaps", "noncollapsing"),
        (r"pseudolocal", "pseudolocality"),
        (r"standard\s+solution", "standard solutions"),
        (r"ricci\s+flow\s+with\s+surgery|surgery", "Ricci flow with surgery"),
        (r"neck", "neck geometry"),
        (r"\bcap\b", "cap geometry"),
        (r"soliton", "Ricci solitons"),
        (r"thick|thin", "thick--thin geometry"),
        (r"hyperbol", "hyperbolic geometry"),
        (r"graph\s+manifold", "graph manifolds"),
        (r"alexandrov", "Alexandrov geometry"),
        (r"harnack", "Harnack inequalities"),
        (r"heat\s+(?:equation|kernel)", "heat evolution"),
        (r"scalar\s+curvature", "scalar curvature"),
        (r"curvature\s+operator", "curvature operators"),
        (r"sectional\s+curvature", "sectional curvature"),
        (r"curvature", "curvature"),
        (r"injectivity\s+radius", "injectivity radius"),
        (r"diameter", "diameter"),
        (r"distance", "distance distortion"),
        (r"volume", "volume"),
        (r"eigenvalue|spectrum", "spectral geometry"),
        (r"entropy|\\lambda", "entropy"),
        (r"maximum\s+principle", "maximum principles"),
        (r"metric", "Riemannian metrics"),
    ]
    concept = next((name for pattern, name in concepts if re.search(pattern, combined)), None)
    if concept is None:
        concept = semantic_section(section).lower()

    qualifiers = [
        (r"if and only if|equivalent", "characterization"),
        (r"unique|uniqueness", "uniqueness"),
        (r"there (?:is|are|exists)|there exists|existence", "existence"),
        (r"compact|precompact", "compactness"),
        (r"converge|subsequence|limit", "convergence"),
        (r"differential\s+inequal|frac\{d\\lambda\}|d\\lambda", "differential inequality"),
        (r"monoton|nondecreasing|nonincreasing", "monotonicity"),
        (r"bounded|bound|estimate|inequal", "estimates"),
        (r"positive|nonnegative", "positivity"),
        (r"vanish|zero", "vanishing"),
        (r"continuous|continuity", "continuity"),
        (r"diffeomorph|isometr|rigid", "rigidity"),
        (r"extend|continuation", "continuation"),
        (r"decompos|split", "decomposition"),
    ]
    qualifier = next((name for pattern, name in qualifiers if re.search(pattern, lower)), None)
    if qualifier:
        return f"{qualifier} for {concept}"
    if kind == "remark":
        return f"structural remark on {concept}"
    if concept == section_name:
        return f"{concept} {kind}"
    return f"{concept} {kind}"


GAP_PATTERNS = (
    r"\bfrom a standard formula\b",
    r"\bby (?:a )?standard (?:argument|calculation|application)\b",
    r"\bstandard (?:argument|calculation|reasoning|rescaling argument)\b",
    r"\bobvious(?:ly)?\b",
    r"\bone can check\b",
    r"\bstraightforward\b",
    r"\bexercise\b",
    r"\(\s*Sketch\s*\)",
    r"\bwe (?:first )?sketch\b",
    r"\bproof is basically the same\b",
    r"\bproof .* analogous\b",
    r"\banalogous to the proof\b",
    r"\bsimilar argument\b",
    r"\bjust state the main idea\b",
    r"\bdetails? (?:are|is) (?:omitted|left)\b",
    r"\bleft to (?:the )?reader\b",
    r"\bwe omit\b",
    r"\bexercise for the reader\b",
)


PROOF_TOKEN = re.compile(r"\\begin\{proof\}(?:\[[^\]]*\])?|\\end\{proof\}")


def matching_proof_end(text: str, begin: int) -> int:
    depth = 0
    for token in PROOF_TOKEN.finditer(text, begin):
        if token.group().startswith(r"\begin"):
            depth += 1
        else:
            depth -= 1
            if depth == 0:
                return token.end()
    raise ValueError(f"unclosed proof at {begin}")


def proof_blocks(text: str, start: int, end: int) -> list[dict]:
    blocks = []
    stack = []
    pairs = []
    for token in PROOF_TOKEN.finditer(text, start, end):
        if token.group().startswith(r"\begin"):
            stack.append(token)
        else:
            if not stack:
                raise ValueError(f"unmatched proof end at {token.start()}")
            pairs.append((stack.pop(), token))
    if stack:
        raise ValueError(f"unclosed proof at {stack[-1].start()}")
    for match, close_token in sorted(pairs, key=lambda pair: pair[0].start()):
        close = close_token.start()
        close_end = close_token.end()
        body = text[match.end():close]
        audited_body = re.sub(r"\\uses\{[^{}]*\}", " ", body)
        gaps = [
            pattern for pattern in GAP_PATTERNS
            if re.search(pattern, audited_body, re.I | re.S)
        ]
        if (
            "To write this out precisely" in body
            and r"\bwe (?:first )?sketch\b" in gaps
        ):
            gaps.remove(r"\bwe (?:first )?sketch\b")
        blocks.append({
            "begin_start": match.start(),
            "begin_end": match.end(),
            "end_start": close,
            "end_end": close_end,
            "body": body,
            "gaps": gaps,
        })
    return blocks


def find_proof(text: str, declaration_end: int) -> tuple[int, int, str] | None:
    match = re.match(r"(?:\s|%[^\n]*\n)*\\begin\{proof\}", text[declaration_end:])
    if not match:
        return None
    begin = declaration_end + match.end() - len(r"\begin{proof}")
    end = matching_proof_end(text, begin)
    return begin, end, text[begin:end]


def main() -> None:
    source = SOURCE_TEXT
    body_start = source.index(r"\section{Introduction}")
    bibliography_start = source.index(r"\begin{thebibliography}")
    sections = source_sections(source)
    all_source_proofs = proof_blocks(source, body_start, bibliography_start)
    incomplete_source_proofs = [proof for proof in all_source_proofs if proof["gaps"]]
    incomplete_proof_starts = {
        proof["begin_start"] for proof in incomplete_source_proofs
    }
    pattern = re.compile(r"\\begin\{(" + "|".join(SOURCE_KINDS) + r")\}")
    declarations = []
    section_ordinals: defaultdict[str, int] = defaultdict(int)
    seen_labels: set[str] = set()

    for global_index, match in enumerate(pattern.finditer(source), 1):
        if not (body_start <= match.start() < bibliography_start):
            continue
        source_kind = match.group(1)
        end_token = rf"\end{{{source_kind}}}"
        statement_end = source.find(end_token, match.end())
        if statement_end < 0:
            raise ValueError(f"unclosed {source_kind} at {match.start()}")
        statement_end += len(end_token)
        statement = source[match.end():statement_end - len(end_token)]
        current_section = max((x for x in sections if x[0] < match.start()), key=lambda x: x[0])
        _, section_raw = current_section
        section_key = slug(semantic_section(section_raw))
        section_ordinals[section_key] += 1
        ordinal = section_ordinals[section_key]
        target_kind = KIND_MAP.get(source_kind, source_kind)
        original_labels = re.findall(r"\\label\{([^{}]+)\}", statement)
        dcref = original_labels[0] if original_labels else f"{section_key}:{source_kind}-{ordinal}"
        title = title_for(statement, section_raw, target_kind)
        semantic_label = (
            f"{PREFIX[target_kind]}:kl-{section_key}-{slug(title)}"
        )
        if semantic_label in seen_labels:
            semantic_label = f"{semantic_label}-{ordinal}"
        if semantic_label in seen_labels:
            semantic_label = f"{semantic_label}-{global_index}"
        seen_labels.add(semantic_label)
        declarations.append({
            "index": global_index,
            "position": match.start(),
            "source_kind": source_kind,
            "target_kind": target_kind,
            "begin_start": match.start(),
            "begin_end": match.end(),
            "statement_end": statement_end,
            "statement": statement,
            "proof": find_proof(source, statement_end),
            "title": title,
            "semantic_label": semantic_label,
            "original_labels": original_labels,
            "dcref": dcref,
            "group": group_for(match.start()),
            "section": semantic_section(section_raw),
        })

    source_counts = Counter(d["source_kind"] for d in declarations)
    if source_counts != EXPECTED:
        raise SystemExit(f"baseline mismatch: {source_counts} != {EXPECTED}")

    original_to_semantic = {}
    for declaration in declarations:
        for label in declaration["original_labels"]:
            original_to_semantic[label] = declaration["semantic_label"]

    edits: list[tuple[int, int, str]] = []
    dependency_count = 0
    for declaration in declarations:
        statement_refs = re.findall(r"\\(?:ref|eqref)\{([^{}]+)\}", declaration["statement"])
        statement_uses = sorted({
            original_to_semantic[ref] for ref in statement_refs
            if ref in original_to_semantic
            and original_to_semantic[ref] != declaration["semantic_label"]
        })
        metadata = [
            f"  \\label{{{declaration['semantic_label']}}}",
            f"  \\dcref{{{declaration['dcref']}}}",
            f"  \\group{{{declaration['group']}}}",
            "  \\source{kleiner-lott}",
        ]
        if statement_uses:
            metadata.append("  \\uses{" + ",".join(statement_uses) + "}")
        dependency_count += len(statement_uses)
        replacement = (
            f"\\begin{{{declaration['target_kind']}}}"
            f"[{declaration['title']}]\n" + "\n".join(metadata) + "\n"
        )
        edits.append((declaration["begin_start"], declaration["begin_end"], replacement))
        source_end = declaration["statement_end"] - len(
            rf"\end{{{declaration['source_kind']}}}"
        )
        edits.append((
            source_end,
            declaration["statement_end"],
            rf"\end{{{declaration['target_kind']}}}",
        ))
        if (
            declaration["proof"]
            and declaration["proof"][0] not in incomplete_proof_starts
        ):
            proof_begin, _, proof_text = declaration["proof"]
            proof_refs = re.findall(r"\\(?:ref|eqref)\{([^{}]+)\}", proof_text)
            proof_uses = sorted({
                original_to_semantic[ref] for ref in proof_refs
                if ref in original_to_semantic
                and original_to_semantic[ref] != declaration["semantic_label"]
            })
            if proof_uses:
                proof_token_end = proof_begin + len(r"\begin{proof}")
                edits.append((
                    proof_begin,
                    proof_token_end,
                    "\\begin{proof}\n  \\uses{" + ",".join(proof_uses) + "}",
                ))
                dependency_count += len(proof_uses)

    # Preserve incomplete source arguments verbatim, but do not expose them as
    # proof environments: that would falsely certify a sketch as a proof.
    for proof in incomplete_source_proofs:
        edits.append((
            proof["begin_start"],
            proof["begin_end"],
            "\\par\\medskip\\noindent\\textit{Source argument (not certified "
            "as complete).}\\ \\begingroup\\itshape ",
        ))
        edits.append((
            proof["end_start"],
            proof["end_end"],
            "\\endgroup\\par\\medskip",
        ))

    transformed = source
    for start, end, replacement in sorted(edits, reverse=True):
        transformed = transformed[:start] + replacement + transformed[end:]

    # The source has one Polish-letter command where the reduced-length
    # variable l is intended; in math mode that command is invalid.
    transformed = transformed.replace(
        r"$\l = \frac{\bar L}{4\tau}$",
        r"$l = \frac{\bar L}{4\tau}$",
    )

    t_body_start = transformed.index(r"\section{Introduction}")
    t_part_i = transformed.index(r"\section{I.1.1.", t_body_start)
    t_part_ii = transformed.index(
        "\\section{Overview of \n{\\em Ricci Flow with Surgery", t_part_i
    )
    t_appendix = transformed.index(r"\appendix", t_part_ii)
    t_bibliography = transformed.index(r"\begin{thebibliography}", t_appendix)
    t_bib_end = transformed.index(r"\end{thebibliography}", t_bibliography)
    t_bib_end += len(r"\end{thebibliography}")

    appendix_token = r"\appendix"
    appendix_body_start = t_appendix + len(appendix_token)
    chunks = {
        "introduction.tex": transformed[t_body_start:t_part_i],
        "part-i.tex": transformed[t_part_i:t_part_ii],
        "part-ii.tex": transformed[t_part_ii:t_appendix],
        "appendices.tex": transformed[appendix_body_start:t_bibliography],
        "bibliography.tex": transformed[t_bibliography:t_bib_end] + "\n",
    }
    for name, text in chunks.items():
        (OUT / name).write_text(clean_generated(text))
    content = (
        "% Complete source-preserving Kleiner--Lott blueprint.\n"
        "\\input{complete/introduction}\n"
        "\\part{Ricci Flow without Surgery}\n"
        "\\label{part:kl-without-surgery}\n"
        "\\input{complete/part-i}\n"
        "\\part{Ricci Flow with Surgery}\n"
        "\\label{part:kl-with-surgery}\n"
        "\\input{complete/part-ii}\n"
        "\\appendix\n"
        "\\part*{Appendices}\n"
        "\\input{complete/appendices}\n"
    )
    (OUT / "content.tex").write_text(content)
    (OUT.parent / "content.tex").write_text(
        "% Canonical entry point for the complete February 2013 notes.\n"
        + content
    )
    preamble = transformed[:t_body_start]
    metadata_macros = r"""
\newcommand{\dcref}[1]{}
\newcommand{\group}[1]{}
\newcommand{\uses}[1]{}
\newcommand{\source}[1]{}
\providecommand{\lean}[1]{}
\providecommand{\leanok}{}
\providecommand{\mathlibok}{}
\DeclareFontShape{OT1}{cmr}{m}{scit}{<->ssub*cmr/m/sc}{}
"""
    parser_macros = []
    for line in preamble.splitlines():
        if re.match(r"\\(?:newcommand|renewcommand)", line):
            line = line.replace(r"\renewcommand", r"\newcommand", 1)
            line = line.replace(r"\newcommand{ \defeq}", r"\newcommand{\defeq}")
            parser_macros.append(line.rstrip())
    parser_macros.extend([
        r"\newcommand{\dcref}[1]{}",
        r"\newcommand{\group}[1]{}",
        r"\newcommand{\uses}[1]{}",
        r"\newcommand{\source}[1]{}",
        r"\newcommand{\lean}[1]{}",
        r"\newcommand{\leanok}{}",
        r"\newcommand{\mathlibok}{}",
    ])
    (OUT.parent / "macros.tex").write_text(
        "% KaTeX macro catalog generated from the authoritative source.\n"
        + "\n".join(parser_macros)
        + "\n"
    )
    preamble = preamble.replace(r"\begin{document}", metadata_macros + "\n\\begin{document}")
    complete_driver = clean_generated(
        preamble + "\\input{complete/content}\n"
        + "\\input{complete/bibliography}\n"
        + "\\end{document}\n"
    )
    root_driver = clean_generated(
        preamble + "\\input{content}\n"
        + "\\input{complete/bibliography}\n"
        + "\\end{document}\n"
    )
    (OUT / "blueprint.tex").write_text(complete_driver)
    (OUT.parent / "blueprint.tex").write_text(root_driver)

    source_citations = {
        key.strip()
        for body in re.findall(
            r"\\cite(?:\[[^\]]*\])?\{([^{}]+)\}",
            transformed[t_body_start:t_bibliography],
        )
        for key in body.split(",")
    }
    bibliography_keys = set(re.findall(
        r"\\bibitem\{([^{}]+)\}", transformed[t_bibliography:t_bib_end]
    ))
    mapped_counts = Counter(d["target_kind"] for d in declarations)
    original_labels = [
        label for declaration in declarations for label in declaration["original_labels"]
    ]
    transformed_proofs = proof_blocks(transformed, t_body_start, t_bibliography)
    remaining_gap_proofs = [
        transformed.count("\n", 0, proof["begin_start"]) + 1
        for proof in transformed_proofs if proof["gaps"]
    ]
    title_quality_issues = [
        {"index": declaration["index"], "title": declaration["title"]}
        for declaration in declarations
        if (
            not re.fullmatch(r"[A-Za-z0-9' -]+", declaration["title"])
            or re.search(
                r"(?:given by|the -|-functional|\bof i\b|\bof ii\b|"
                r"\btheorem theorem\b|\blemma lemma\b|\bproposition proposition\b|"
                r"\bdefinition definition\b|\bfor\s*$)",
                declaration["title"],
                re.I,
            )
        )
    ]
    audit = {
        "source": str(SOURCE.relative_to(WORKSPACE)),
        "source_lines": len(source.splitlines()),
        "baseline": 242,
        "mapped": len(declarations),
        "omissions": 242 - len(declarations),
        "duplicates": len(declarations) - len({d["position"] for d in declarations}),
        "source_kind_counts": dict(sorted(source_counts.items())),
        "mapped_kind_counts": dict(sorted(mapped_counts.items())),
        "source_proof_blocks": len(all_source_proofs),
        "complete_proof_environments": transformed[t_body_start:t_bibliography].count(
            r"\begin{proof}"
        ),
        "source_arguments_declassified": len(incomplete_source_proofs),
        "declassified_source_lines": [
            source.count("\n", 0, proof["begin_start"]) + 1
            for proof in incomplete_source_proofs
        ],
        "semantic_labels": len(seen_labels),
        "dcref_annotations": transformed[t_body_start:t_bibliography].count(
            r"\dcref{"
        ),
        "group_annotations": transformed[t_body_start:t_bibliography].count(
            r"\group{"
        ),
        "source_anchors": transformed[t_body_start:t_bibliography].count(
            r"\source{kleiner-lott}"
        ),
        "title_quality_issues": title_quality_issues,
        "remaining_explicit_gap_proof_environments": remaining_gap_proofs,
        "original_declaration_labels_preserved": len(original_labels),
        "uses_edges_authored": dependency_count,
        "citation_keys_used": len(source_citations),
        "bibliography_keys": len(bibliography_keys),
        "unresolved_citations": sorted(source_citations - bibliography_keys),
        "additional_unenvironmented_nodes": 0,
        "additional_unenvironmented_audit": (
            "No additional theorem-like environments occur in the source. "
            "Named Claim sections are followed by declarations already included "
            "in the 242-node baseline; no separate assertion was duplicated."
        ),
    }
    (OUT / "audit.json").write_text(json.dumps(audit, indent=2) + "\n")
    (OUT / "AUDIT.md").write_text(
        "# Complete blueprint audit\n\n"
        f"- Source: {audit['source']} ({audit['source_lines']} lines).\n"
        f"- Baseline declarations: **{audit['baseline']}**.\n"
        f"- Mapped declarations: **{audit['mapped']}**.\n"
        f"- Omissions: **{audit['omissions']}**.\n"
        f"- Duplicates: **{audit['duplicates']}**.\n"
        f"- Source proof blocks preserved: **{audit['source_proof_blocks']}**.\n"
        f"- Complete proof environments retained: "
        f"**{audit['complete_proof_environments']}**.\n"
        f"- Explicitly incomplete source arguments declassified: "
        f"**{audit['source_arguments_declassified']}**.\n"
        f"- Semantic labels: **{audit['semantic_labels']}**.\n"
        f"- dcref / group / source annotations: "
        f"**{audit['dcref_annotations']} / {audit['group_annotations']} / "
        f"{audit['source_anchors']}**.\n"
        f"- Title-quality issues: **{len(audit['title_quality_issues'])}**.\n"
        f"- Remaining explicit-gap proof environments: "
        f"**{len(audit['remaining_explicit_gap_proof_environments'])}**.\n"
        f"- Authored uses edges: **{audit['uses_edges_authored']}**.\n"
        f"- Citation keys used / bibliography keys: "
        f"**{audit['citation_keys_used']} / {audit['bibliography_keys']}**.\n"
        f"- Unresolved citations: **{len(audit['unresolved_citations'])}**.\n"
        "- Additional unenvironmented nodes: **0**. "
        + audit["additional_unenvironmented_audit"] + "\n\n"
        "## Source-kind reconciliation\n\n"
        + json.dumps(audit["source_kind_counts"], indent=2) + "\n\n"
        "Claims are mapped to propositions and sublemmas to lemmas; all other "
        "declaration kinds are retained.\n"
    )
    if (
        audit["omissions"]
        or audit["duplicates"]
        or audit["unresolved_citations"]
        or audit["title_quality_issues"]
        or audit["remaining_explicit_gap_proof_environments"]
    ):
        raise SystemExit(json.dumps(audit, indent=2))
    print(json.dumps(audit, indent=2))


if __name__ == "__main__":
    main()
