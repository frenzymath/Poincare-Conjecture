# Chow et al. - The Ricci Flow: Techniques and Applications

A Lean 4 reference project and source-faithful blueprint following Bennett
Chow and collaborators, *The Ricci Flow: Techniques and Applications*.

The published blueprint covers Parts II-IV. Part I is intentionally excluded
because the available source is incomplete; it should be added only when a
complete copy can be audited. The Lean library is an initial scaffold for
declarations following the blueprint's dependency graph.

## Layout

- `ChowEtAl/` - Lean source modules.
- `ChowEtAl.lean` - root library module.
- `blueprint/src/parts/` - source chapters grouped by published volume.
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
