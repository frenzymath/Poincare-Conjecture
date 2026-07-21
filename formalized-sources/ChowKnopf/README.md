# Chow-Knopf - The Ricci Flow: An Introduction

A Lean 4 reference project and source-faithful blueprint following Bennett
Chow and Dan Knopf, *The Ricci Flow: An Introduction* (AMS, 2004).

The blueprint covers all nine chapters and both mathematical appendices, from
special solutions and short-time existence through maximum principles,
derivative estimates, and singularity models. The Lean library is an initial
scaffold for declarations following that dependency graph.

## Layout

- `ChowKnopf/` - Lean source modules.
- `ChowKnopf.lean` - root library module.
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
