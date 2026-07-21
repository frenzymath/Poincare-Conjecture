# do Carmo - Riemannian Geometry

A source-based Lean 4 formalization and blueprint following Manfredo P. do
Carmo, *Riemannian Geometry*.

`DoCarmoLib` develops metrics, connections, curvature, geodesics, Jacobi
fields, the exponential map, Hopf-Rinow, and comparison geometry in the order
needed by the book. General-purpose mathlib gaps and repository linters live in
the separate root `shared/` package.

## Layout

- `DoCarmoLib/` - Lean source modules.
- `DoCarmoLib.lean` - root library module.
- `blueprint/src/` - source-faithful mathematical blueprint.
- `hgraph/config.yaml` - graph synchronization configuration.

## Build

```bash
lake exe cache get
lake build
lake test
```

Workspace-wide website and review instructions are in the root
`CONTRIBUTING.md`.
