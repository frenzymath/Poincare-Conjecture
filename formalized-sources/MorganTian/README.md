# Morgan-Tian - Ricci Flow and the Poincare Conjecture

A source-based Lean 4 formalization and dependency blueprint following John
Morgan and Gang Tian, *Ricci Flow and the Poincare Conjecture*
([arXiv:math/0607607](https://arxiv.org/abs/math/0607607)).

This is a reference project. The repository's custom proof architecture lives
in the root `PoincareConjecture/` project.

## Layout

| Path | Contents |
| --- | --- |
| `MorganTianLib/Ch01/` | Riemannian preliminaries and comparison geometry |
| `MorganTianLib/Ch02/` | Nonnegative curvature, Busemann functions, splitting, and ends |
| `MorganTianLib/Ch03/RicciFlow/` | Ricci-flow, space-time, and curvature-variation infrastructure |
| `MorganTianLib/Ch05/` | Geometric-limit, packing, and pointed-GH convergence infrastructure |
| `MorganTianLib.lean` | Aggregate Lean import |
| `blueprint/src/chapters/` | Distilled mathematical chapters and Lean status annotations |
| `hgraph/` | Graph configuration plus nested human verdict attachments |

The package uses `DoCarmoLib` through the sibling `../DoCarmo` path dependency.

## Build

```bash
lake exe cache get
lake build
```

Workspace-wide website and review instructions are in the root
`CONTRIBUTING.md`.

## Human statement reviews

External reviewers record statement status in nested hgraph attachments under
`hgraph/nodes/<id>/verdicts.yaml`. Generated node and edge bodies are
regenerated in CI and are not committed.
