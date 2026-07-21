# Gilbarg--Trudinger - Elliptic PDE of Second Order

This Lean 4 project carries a source-faithful blueprint of David Gilbarg and
Neil S. Trudinger, *Elliptic Partial Differential Equations of Second Order*.
The blueprint covers the front matter, all 17 chapters, and the end matter of
the revised second-edition reprint.

## Layout

- `GilbargTrudinger.lean` and `GilbargTrudinger/`: Lean package.
- `blueprint/src/content.tex`: ordered blueprint entry point.
- `blueprint/src/chapters/`: canonical chapter sources.
- `blueprint/src/macros/`: shared print and web macros.
- `hgraph/config.yaml`: project-local graph inputs.

The repository publishes canonical chapter files directly under `chapters/`;
generated merge directories, graph records, and TeX build output are omitted.

## Build

From this directory:

```bash
lake exe cache get
lake build
```

Workspace-wide build and site instructions are maintained in the repository
root `CONTRIBUTING.md`.
