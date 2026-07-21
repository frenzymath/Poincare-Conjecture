# Cheeger-Gromov-Taylor - Finite Propagation Speed and Kernel Estimates

A Lean 4 reference project and source-faithful blueprint for Jeff Cheeger,
Mikhail Gromov, and Michael Taylor, *Finite Propagation Speed, Kernel Estimates
for Functions of the Laplace Operator, and the Geometry of Complete Riemannian
Manifolds* (Journal of Differential Geometry 17, 1982).

The blueprint covers the complete article: finite propagation speed, kernel
estimates under Ricci-curvature and bounded-geometry hypotheses, and the
resulting volume and injectivity estimates. The Lean library is an initial
scaffold for declarations following that dependency graph.

## Layout

- `CheegerGromovTaylor/` - Lean source modules.
- `CheegerGromovTaylor.lean` - root library module.
- `blueprint/src/` - source-faithful mathematical blueprint.
- `hgraph/config.yaml` - graph synchronization configuration.

The package uses `DoCarmoLib` through the sibling `../DoCarmo` path dependency.

## Build

```bash
lake exe cache get
lake build
```

Workspace-wide website and review instructions are in the root
`CONTRIBUTING.md`.
