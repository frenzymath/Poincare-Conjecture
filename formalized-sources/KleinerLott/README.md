# Kleiner-Lott - Notes on Perelman's Papers

A Lean 4 project and complete source-based dependency blueprint following
Bruce Kleiner and John Lott, *Notes on Perelman's Papers*
([arXiv:math/0605667](https://arxiv.org/abs/math/0605667)).

The blueprint preserves the complete source development across entropy,
reduced geometry, singularity models, surgery, long-time behavior,
geometrization, and the technical appendices. Lean formalization is at an
early scaffold stage.

## Layout

- `KleinerLott/` - Lean source modules.
- `blueprint/src/content.tex` - blueprint entry point.
- `blueprint/src/chapters/` - the authoritative source chapter files.
- `hgraph/config.yaml` - graph synchronization configuration.

## Build

```bash
lake exe cache get
lake build
```

Workspace-wide website and review instructions are in the root
`CONTRIBUTING.md`.
