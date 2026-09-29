> This reference is now blueprint-only. Its Lean sources and Lake package have
> been removed; earlier formalization and build notes below are historical.
> The active proof library is in `../../PoincareConjecture/`.

# Thurston - The Geometry and Topology of Three-Manifolds

A Lean 4 reference project and independently worded mathematical blueprint
following William P. Thurston's *The Geometry and Topology of Three-Manifolds*.

## Scope and provenance

The source is the free SLMath electronic edition 1.1 (March 2002), based on
Thurston's Princeton lecture notes from 1978--1980. The public source edition
is available at <https://library.slmath.org/nonmsri/gt3m/>. The raw PDF and
page transcription are maintained separately; they are not copied into this
repository.

The blueprint covers the eleven mathematical chapters present in that edition:
Chapters 1--9, 11, and 13. Chapters 10 and 12 do not exist in the source. The
index is retained in the reference archive but is not reproduced in the
blueprint.

## Copyright-sensitive distillation

The blueprint is not a transcription. It extracts formalization-relevant
definitions, results, formulas, exceptional cases, and proof ideas into concise,
independently written mathematical prose. Motivational, historical,
reader-directed, illustrative, and repetitive source prose is excluded. The
page-level `\source{thurston:page-NNNN}` metadata preserves the audit trail to
the source without reproducing its text.

## Layout

- `Thurston.lean` - Lean library entry point.
- `Thurston/Basic.lean` - initial namespace module.
- `blueprint/src/content.tex` - ordered blueprint entry point.
- `blueprint/src/chapters/` - independently worded chapter distillations.
- `../../site/projects/references/Thurston/config.yaml` - graph configuration.

## Build

```bash
lake exe cache get
lake build
```

Workspace-wide website and hgraph instructions are in the root
`CONTRIBUTING.md`.
