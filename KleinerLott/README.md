# KleinerLott — Notes on Perelman's Papers

A Lean 4 project and mathematical dependency blueprint following Bruce Kleiner
and John Lott, *Notes on Perelman's Papers*, February 13, 2013
([arXiv:math/0605667](https://arxiv.org/abs/math/0605667)). The authoritative
retrieved TeX is the workspace reference `kleiner-lott`.

## Scope

The blueprint covers the complete 18,411-line February 2013 TeX source. It
maps all 242 declaration environments, preserves all 138 source proofs and the
full narrative, and spans the overview, entropy and reduced geometry,
three-dimensional singularity models, surgery, long-time behavior,
geometrization, and technical appendices.

There is no formalization yet. Consequently the blueprint contains no
`\\lean`, `\\leanok`, or `\\mathlibok` claims.

## Layout

- `KleinerLott.lean` — Lean library entry point.
- `blueprint/src/content.tex` — standalone mathematical blueprint root.
- `blueprint/src/complete/` — complete source blueprint, driver, bibliography,
  generator, and audit.
- `hgraph/config.yaml` — Horizon graph configuration.

## Build

```bash
./build.sh
```

This checks the empty Lean scaffold, synchronizes the graph, and writes the
complete source blueprint to `blueprint/build/blueprint.pdf`.
