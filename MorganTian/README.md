# Ricci Flow and the Poincaré Conjecture — hgraph example

An hgraph blueprint of the **first two chapters** of

> J. W. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*,
> arXiv:math/0607607.

Pure blueprint (no Lean), built by restructuring the book's own LaTeX source.

## Layout

| Path | What it is |
|------|-----------|
| `references/` | The authoritative arXiv source: LaTeX, `.bbl`, figures, tarball, compiled PDF (see `references/README.md`) |
| `blueprint/src/chapters/Ch1_Preliminaries.tex` | Chapter 1, *Preliminaries from Riemannian geometry* — 59 statements |
| `blueprint/src/chapters/Ch2_BasicsOfRicciFlow.tex` | Chapter 2, *Basics of Ricci flow* — 41 statements |
| `blueprint/src/content.tex` | the entry `sync` points at — `\input`s the two chapters |
| `blueprint/src/macros.tex` | Morgan–Tian math macros (auto-discovered for KaTeX) |
| `blueprint/src/meta.tex` | `\title` / `\author` (auto-discovered for the dashboard title page) |
| `blueprint/src/refs.bib` | BibTeX for the 20 works cited in Ch. 1–2 (auto-discovered) |
| `hgraph/config.yaml` | points `sync` at `blueprint/src/content.tex` |
| `build.sh` | `hgraph sync` + `hgraph dashboard` → `dashboard.html` |
| `ocr/page-*.md` | earlier page-by-page OCR of the printed PDF (independent of the blueprint) |

## Build

```bash
bash examples/poincaré/build.sh      # → 100 nodes, 23 edges, dashboard.html
```

## How the source was adapted for hgraph

`hgraph sync` makes a **node** from every theorem-like environment that carries a
`\label`, and **edges** from `\uses{...}`. The book's LaTeX needed four
mechanical changes (the prose and mathematics are otherwise verbatim):

1. **Environment names.** The parser recognises `definition, theorem, lemma,
   proposition, corollary, claim, example, conjecture, remark`. The book's short
   names were renamed accordingly (`defn→definition`, `exam→example`,
   `conj→conjecture`, `rem→remark`, `ex(Exercise)→example`; `thm/prop/lem/cor/
   claim` kept).
2. **A semantic `\label` + title on every statement.** Each statement carries a
   `<kind>:<kebab-slug>` label describing its content (`def:riemannian-metric`,
   `thm:bishop-gromov`, `def:ricci-flow`, `thm:shi-derivative-estimates`, …) and a
   human-readable bracket title (`\begin{theorem}[Bishop--Gromov relative volume
   comparison]`) that surfaces in the dashboard.
3. **`\uses` dependency graph** (123 edges). Wired from the book's explicit
   `\ref`/`\eqref` cross-references, results named in the prose, and definitional
   term usage (statement refs → `depends_on`, proof refs → `uses`), including
   cross-chapter edges such as `cor:distance-integral-bound →
   lem:forward-difference-quotient`. References to results **outside** these two
   chapters (e.g. appendix lemmas `topiso`, `directions`) are left as prose `\ref`
   only, not wired.
4. **Web/KaTeX hygiene:** EPS `figure` blocks and `\index` removed; the source's
   `{rm Jac}` typo and `{\rm …}`/`\mathit{…}` operators normalised to the macros
   in `macros.tex` (`\Ric \Rm \Hess \Vol \Jac \sn \ct …`).

No `\lean`/`\leanok` is present, so every node's `lean_status` is `empty` — this
is a mathematical blueprint, not a formalization.

## Provenance / caveat

Statement **text and formulas** are copied verbatim from the arXiv source. The
**labels/titles** and the **`\uses` dependency graph**, however, were generated
(the dependencies inferred from cross-references, prose, and definitional usage),
so they are heuristic — spot-check before relying on the edges for anything
load-bearing. Dependencies on results outside these two chapters are intentionally
not wired.
