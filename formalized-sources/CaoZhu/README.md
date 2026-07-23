# Cao-Zhu - Hamilton-Perelman's proof

A Lean 4 project and complete source-based blueprint following Huai-Dong Cao
and Xi-Ping Zhu, *Hamilton-Perelman's Proof of the Poincare Conjecture and the
Geometrization Conjecture*.

The blueprint covers the revised source's eight chapters, including Ricci-flow
evolution equations, reduced geometry, singularity formation, surgery, and
geometrization. Lean declarations will be added along its dependency frontier.

## Layout

- `CaoZhuLib/` - Lean source modules.
- `blueprint/src/content.tex` - blueprint entry point.
- `blueprint/src/chapters/` - the authoritative source chapter files.
- `hgraph/config.yaml` - graph synchronization configuration.

The package uses `DoCarmoLib` through the sibling `../DoCarmo` path dependency.

## Build

```bash
lake exe cache get
lake build
```

Workspace-wide website and review instructions are in the root
`CONTRIBUTING.md`.
