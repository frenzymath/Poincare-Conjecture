<h1 align="center">LeeRiemannian — Introduction to Riemannian Manifolds</h1>

<p align="center"><em>Chapter 1 formalized; Chapter 2 well advanced; Chapters 3+ not yet started.</em></p>

A Lean 4 formalization following John M. Lee, *Introduction to Riemannian
Manifolds* (Graduate Texts in Mathematics 176, 2nd ed.).

Formerly the `Lee` project; renamed when `LeeSmooth/` (the same author's
*Introduction to Smooth Manifolds*, GTM 218) was added. The Lean library keeps
its historical name `LeeLib`, and historical task IDs keep the `LEE.*` prefix.

## Layout

- `LeeLib/Ch01/` — Chapter 1 (*What Is Curvature?*), one module per topic:
  - `RigidMotion` — rigid motions of a Euclidean space and the **isometry
    extension theorem**: a correspondence between families of points that
    preserves all pairwise distances is realised by a rigid motion of the
    whole space (finite dimension). Also `congruent_iff_exists_affineIsometryEquiv`,
    identifying mathlib's distance-based `Congruent` with congruence by rigid
    motions.
  - `EuclideanTriangles` — Theorem 1.1, side-side-side.
  - `CircleClassification` — Theorem 1.3, two circles are congruent iff they
    have the same radius.
  - `Circumference` — Theorem 1.4, the arc length of a circle of radius `R`
    is `2πR`.
- `LeeLib/Ch02/` — Chapter 2 (*Riemannian Metrics*), ~37 modules: metrics and
  their existence, orthonormal/adapted frames, pullback and product/warped
  metrics, musical isomorphisms, normal bundles, the Riemannian distance
  function and its comparison lemmas, Riemannian submersions, and the
  pseudo-Riemannian substrate (which mathlib lacks entirely).
- `LeeLib/AppendixA/` — Appendix A infrastructure that mathlib does not have:
  local sections of a submersion and the `sliceChart` local normal form
  (`LocalSection`, `SliceChart`), the local frame and subbundle criteria.
- `blueprint/src/` — the LaTeX blueprint; `content.tex` is the root, one
  `chapterN.tex` file per chapter, parsed into the dependency DAG by
  `horizon blueprint`. `\lean{...}` tags name the backing declarations,
  `\leanok` marks checked Lean, `\mathlibok` marks a mathlib leaf, and
  `\notready` marks a statement not yet formalizable.

## Chapter 1 status

Chapter 1 is Lee's informal survey: it states eleven theorems and proves none
of them, and the technical treatment begins in Chapter 2. Of those eleven:

| Theorem | Status |
| --- | --- |
| 1.1 Side-Side-Side | `\leanok` — `LeeLib.Ch01.side_side_side_iff` |
| 1.2 Angle-Sum | `\mathlibok` — `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` |
| 1.3 Circle Classification | `\leanok` — `LeeLib.Ch01.euclidean_circle_congruent_iff_radius_eq` |
| 1.4 Circumference | `\leanok` — `LeeLib.Ch01.circumference_circle` |
| 1.5–1.11 | `\notready` — previews of results Lee proves in Chapters 3, 9, 11 and 12 |

Lee defines congruence by rigid motions, so the content of Theorems 1.1 and 1.3
lies in producing a rigid motion, not in comparing distances. Mathlib's
`Congruent` is *defined* as equality of corresponding distances, which is why
`EuclideanGeometry.side_side_side` does not by itself give Theorem 1.1 — see
`LeeLib/Ch01/RigidMotion.lean`.

Theorems 1.5–1.11 (plane-curve classification, total curvature, uniformization,
Gauss–Bonnet, the classification of constant-curvature metrics, Cartan–Hadamard,
Myers) are stated in Chapter 1 only as previews. Their formalization belongs to
the later chapters that prove them.

## Build

```
lake build
```

Requires Mathlib at the SHA pinned in `lakefile.lean`. The package deliberately
depends on mathlib alone: Chapter 1 is classical Euclidean geometry and needs no
Riemannian infrastructure. Later chapters overlap the DoCarmo (`OpenGALib`) and
Petersen (`PetersenLib`) projects heavily; if a chapter comes to need that
shared material, add `require OpenGALib from "../DoCarmo"` the way Poincare
does — but note that this makes lake rebuild DoCarmo modules inside DoCarmo's
own build directory, which is the subject of workspace issue I-0109.
