# Morgan-Tian - Ricci Flow and the Poincare Conjecture

A source-based Lean 4 formalization and dependency blueprint following John
Morgan and Gang Tian, *Ricci Flow and the Poincare Conjecture*
([arXiv:math/0607607](https://arxiv.org/abs/math/0607607)).

This is a reference project. The repository's custom proof architecture lives
in the root `PoincareConjecture/` project.

## Layout

- `MorganTianLib/` - Lean source modules.
- `MorganTianLib.lean` - root library module.
- `blueprint/src/` - source-based mathematical blueprint.
- `hgraph/config.yaml` - graph synchronization configuration.

The package uses `DoCarmoLib` through the sibling `../DoCarmo` path dependency.

## Build

```bash
lake exe cache get
lake build
```

Workspace-wide website and review instructions are in the root
`CONTRIBUTING.md`.
