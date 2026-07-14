<h1 align="center">Petersen — Riemannian Geometry</h1>

<p align="center"><em>Chapter 1 formalization in progress.</em></p>

A Lean 4 formalization following Peter Petersen, *Riemannian Geometry*
(Graduate Texts in Mathematics 171, 3rd ed.).

## Layout

- `PetersenLib/Foundations/` — the metric core (vendored from the shared
  OpenGALib infrastructure, namespace `PetersenLib`): `RiemannianMetric`
  (aliasing mathlib's `Bundle.ContMDiffRiemannianMetric`), `metricInner`
  algebra, Riesz duality, and the field-generic positive-definite
  bilinear-form core.
- `PetersenLib/Ch01/` — Chapter 1 (*Riemannian Metrics*), one module per
  topic: `RiemannianManifolds` (isometries, pullback metrics, immersions,
  submersions, pseudo-Riemannian metrics), `Sphere`, `Minkowski`,
  `HyperbolicSpace`, `VolumeForm`, `IsometryGroups`, `MetricConstructions`
  (product / left-invariant / covering metrics, flat torus),
  `CoordinateRepresentations`, `PolarCoordinates`, `SurfaceOfRevolution`,
  `SnCsFunctions`, `WarpedProducts`, `SmoothnessCriterion`,
  `TensorConcepts`, and the exercises.
- `blueprint/src/` — the LaTeX blueprint; `content.tex` is the root, one
  `chNN.tex` file per chapter, parsed into the dependency DAG by
  `horizon blueprint`. `\lean{...}` tags name the backing declarations;
  `\leanok` marks checked Lean.

## Build

```
lake exe cache get
lake build
```

Requires Mathlib at the SHA pinned in `lakefile.lean`.
