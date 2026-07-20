# CaoZhu — Hamilton–Perelman's proof

A Lean 4 project and mathematical blueprint following Huai-Dong Cao and
Xi-Ping Zhu, *Hamilton–Perelman's Proof of the Poincaré Conjecture and the
Geometrization Conjecture*, revised arXiv version (2006).

The authoritative source is the complete TeX e-print at
`../references/cao-zhu/latex-source/revisedAJM.tex`, registered under the
reference slug `cao-zhu`.

## Scope

The blueprint covers the complete revised TeX source, including all eight
chapters and all 156 source declaration environments. Eighteen additional
named intermediate obligations in the prose are made explicit as dependency
nodes, for 174 nodes in total. It preserves the source's statements, proofs,
narrative development, citations, and chapter structure from Ricci-flow
evolution equations through surgery, long-time analysis, and geometrization.

There are no `\lean`, `\leanok`, or `\mathlibok` annotations yet; the graph is
the full mathematical specification for the future Lean formalization.

## Layout

- `CaoZhuLib.lean` — root Lean module; currently imports shared geometry only.
- `blueprint/src/content.tex` — blueprint entry point.
- `blueprint/src/complete/` — complete chapters, source bibliography, and audit.
- `blueprint/src/print.tex` and `web.tex` — standalone leanblueprint drivers.
- `hgraph/config.yaml` — Horizon graph synchronization entry point.
- `build.sh` — Lean, graph, and PDF validation.

## Build

```bash
./build.sh
```

The script builds the Lean library, synchronizes the blueprint DAG, and writes
`blueprint/build/print.pdf`. The Lean project uses the workspace mathlib
revision and shared `OpenGALib` infrastructure through `../DoCarmo`.
