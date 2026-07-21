# Topping - Lectures on the Ricci Flow

A Lean 4 reference project and source-faithful blueprint following Peter
Topping, *Lectures on the Ricci Flow* (London Mathematical Society Lecture
Note Series 325).

The blueprint covers the complete text: ten chapters, the connected-sum
appendix, and supporting front and end matter. Its mathematical development
runs from Riemannian and parabolic preliminaries through Perelman entropy and
three-dimensional curvature pinching. The Lean library is an initial scaffold
for declarations following that dependency graph.

## Layout

- `Topping/` - Lean source modules.
- `Topping.lean` - root library module.
- `blueprint/src/chapters/` - source-faithful chapter files.
- `blueprint/src/content.tex` - blueprint entry point.
- `hgraph/config.yaml` - graph synchronization configuration.

The package uses `DoCarmoLib` through the sibling `../DoCarmo` path dependency.

## Build

```bash
lake exe cache get
lake build
```

Workspace-wide website and review instructions are in the root
`CONTRIBUTING.md`.
