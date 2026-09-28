> This reference is now blueprint-only. Its Lean sources and Lake package have
> been removed; earlier formalization and build notes below are historical.
> The active proof library is in `../../PoincareConjecture/`.

# Han-Lin - Lecture Notes on Elliptic Differential Equations

A Lean 4 reference project and source-faithful blueprint following Qing Han
and Fang-Hua Lin, *Lecture Notes on Elliptic Differential Equations* (2007).

The blueprint covers the complete five-chapter notes: harmonic functions,
maximum principles, weak solutions and regularity, and viscosity solutions.
The Lean library is an initial scaffold for declarations following that
dependency graph.

## Layout

- `HanLinLectureNotes/` - Lean source modules.
- `HanLinLectureNotes.lean` - root library module.
- `blueprint/src/chapters/` - source-faithful chapter files.
- `blueprint/src/content.tex` - blueprint entry point.
- `../../site/projects/references/HanLinLectureNotes/config.yaml` - graph synchronization configuration.

The package uses `DoCarmoLib` through the sibling `../DoCarmo` path dependency.

## Build

```bash
lake exe cache get
lake build
```

Workspace-wide website and review instructions are in the root
`CONTRIBUTING.md`.
