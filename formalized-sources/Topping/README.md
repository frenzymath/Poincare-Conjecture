# Topping - Lectures on the Ricci Flow

A Lean 4 formalization and source-based dependency blueprint following Peter
Topping, *Lectures on the Ricci Flow* (LMS Lecture Note Series 325).

This is a reference project. The repository's custom proof architecture lives
in the root `PoincareConjecture/` project.

## Layout

- `Topping/` - Lean library modules (Riemannian, Ricci flow, maximum principle,
  parabolic PDE infrastructure).
- `Topping.lean` - root library module.
- `blueprint/src/` - source-based mathematical blueprint.
- `hgraph/config.yaml` - graph synchronization configuration.

The package depends on `DoCarmoLib` and `MorganTianLib` through the sibling
paths `../DoCarmo` and `../MorganTian`.

## Build

```bash
lake exe cache get
lake build
```

Workspace-wide website and review instructions are in the root
`CONTRIBUTING.md`.
