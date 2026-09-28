/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# The Circle Classification Theorem

This file formalizes Theorem 1.3 of J. M. Lee, *Introduction to Riemannian Manifolds* (2nd ed.),
Chapter 1:

> Two circles in the Euclidean plane are congruent if and only if they have the same radius.

## Modelling congruence

Lee defines a *rigid motion* of the plane to be a bijective, distance-preserving transformation of
the plane onto itself, and calls two plane figures *congruent* when some rigid motion carries one
onto the other.  We model a rigid motion of a real normed space `E` by an element of
`E ≃ᵃⁱ[ℝ] E` (`AffineIsometryEquiv`): a bijective, distance-preserving affine self-map.  By the
Mazur-Ulam theorem (`Mathlib/Analysis/Normed/Affine/MazurUlam.lean`) *every* distance-preserving
bijection of a real normed space is automatically affine, so this is a faithful rendering of Lee's
definition rather than a restriction.  Congruence of two circles is then the statement that some
`f : E ≃ᵃⁱ[ℝ] E` carries the first circle onto the second *as a set*.

A circle of centre `c` and radius `r` is `Metric.sphere c r`.

## The nontriviality hypothesis

The theorem genuinely requires `[Nontrivial E]`, and this is not a technicality.  In the zero space
every sphere of nonzero radius is empty, so the identity carries the "circle" of radius `1` onto the
"circle" of radius `2`: all positive-radius circles are congruent and the theorem is false.  This
failure is recorded in `exists_affineIsometryEquiv_image_sphere_of_subsingleton`, which shows
`Nontrivial E` is not merely sufficient but *necessary*.  Nontriviality is exactly what makes
`Metric.diam_sphere_eq` (`diam (sphere x r) = 2 * r`) true, i.e. exactly what makes the radius of a
circle recoverable from the circle as a metric subspace.  No dimension or finite-dimensionality
hypothesis is needed beyond this: the argument never uses that `E` is a plane.

## Main results

* `AffineIsometryEquiv.image_sphere`: a rigid motion carries a sphere onto a sphere of the same
  radius about the image of the centre.
* `radius_eq_of_affineIsometryEquiv_image_sphere`: the forward direction — congruent circles have
  equal radii, because a rigid motion preserves `Metric.diam` and the diameter of a circle of
  radius `r` is `2 * r`.
* `circle_congruent_iff_radius_eq`: Lee, Theorem 1.3, for an arbitrary nontrivial real normed
  space.
* `euclidean_circle_congruent_iff_radius_eq`: the same statement for the Euclidean plane
  `EuclideanSpace ℝ (Fin 2)`, which is Lee's Theorem 1.3 verbatim.
-/

open Metric

namespace LeeLib.Ch01

section AffineIsometryEquivSphere

variable {𝕜 V P V₂ P₂ : Type*} [NormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂]

/-- An affine isometry equivalence (a rigid motion) carries the sphere of centre `x` and radius `r`
onto the sphere of centre `e x` and the *same* radius `r`.  This is the set-level form of the
statement that rigid motions carry circles to circles of the same radius. -/
@[simp]
theorem _root_.AffineIsometryEquiv.image_sphere (e : P ≃ᵃⁱ[𝕜] P₂) (x : P) (r : ℝ) :
    e '' sphere x r = sphere (e x) r := by
  rw [← e.coe_toIsometryEquiv, e.toIsometryEquiv.image_sphere]

end AffineIsometryEquivSphere

section Translation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The translation `x ↦ v + x`, regarded as a rigid motion of `E`, carries the circle of centre
`c` and radius `r` onto the circle of centre `v + c` and radius `r`. -/
theorem constVAdd_image_sphere (v c : E) (r : ℝ) :
    (AffineIsometryEquiv.constVAdd ℝ E v) '' sphere c r = sphere (v + c) r := by
  rw [AffineIsometryEquiv.image_sphere]
  simp [AffineIsometryEquiv.coe_constVAdd]

/-- Any two circles of the same radius are congruent: the translation carrying `c₁` to `c₂` is a
rigid motion taking the circle of centre `c₁` and radius `r` onto the circle of centre `c₂` and
radius `r`.  This is the converse half of Lee's Theorem 1.3, and it needs no hypothesis on `E`. -/
theorem exists_affineIsometryEquiv_image_sphere (c₁ c₂ : E) (r : ℝ) :
    ∃ f : E ≃ᵃⁱ[ℝ] E, f '' sphere c₁ r = sphere c₂ r := by
  refine ⟨AffineIsometryEquiv.constVAdd ℝ E (c₂ - c₁), ?_⟩
  rw [constVAdd_image_sphere]
  congr 1
  abel

end Translation

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Sharpness of the nontriviality hypothesis.**  If `E` is the zero space then every circle of
nonzero radius is empty, hence *any* two circles of nonzero radii are congruent — even when their
radii differ.  So `Nontrivial E` in `circle_congruent_iff_radius_eq` cannot be dropped. -/
theorem exists_affineIsometryEquiv_image_sphere_of_subsingleton [Subsingleton E] (c₁ c₂ : E)
    {r₁ r₂ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) :
    ∃ f : E ≃ᵃⁱ[ℝ] E, f '' sphere c₁ r₁ = sphere c₂ r₂ := by
  have hs : ∀ (c : E) {r : ℝ}, r ≠ 0 → sphere c r = (∅ : Set E) := by
    intro c r hr
    ext x
    simp [Subsingleton.elim x c, hr.symm]
  exact ⟨AffineIsometryEquiv.refl ℝ E, by rw [hs c₁ h₁, hs c₂ h₂, Set.image_empty]⟩

variable [Nontrivial E]

/-- **Forward direction of Lee's Theorem 1.3.**  If some rigid motion carries the circle of centre
`c₁` and radius `r₁` onto the circle of centre `c₂` and radius `r₂`, then `r₁ = r₂`.

The proof is Lee's: a rigid motion is an isometry, so it preserves the metric diameter
(`Isometry.diam_image`), while the diameter of a circle of radius `r ≥ 0` is `2 * r`
(`Metric.diam_sphere_eq`).  Hence `2 * r₁ = 2 * r₂`. -/
theorem radius_eq_of_affineIsometryEquiv_image_sphere {c₁ c₂ : E} {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (f : E ≃ᵃⁱ[ℝ] E)
    (hf : f '' sphere c₁ r₁ = sphere c₂ r₂) : r₁ = r₂ := by
  have key : (2 : ℝ) * r₁ = 2 * r₂ := by
    calc (2 : ℝ) * r₁ = diam (sphere c₁ r₁) := (diam_sphere_eq c₁ hr₁).symm
      _ = diam (f '' sphere c₁ r₁) := (f.isometry.diam_image _).symm
      _ = diam (sphere c₂ r₂) := by rw [hf]
      _ = 2 * r₂ := diam_sphere_eq c₂ hr₂
  linarith

/-- **Lee, *Introduction to Riemannian Manifolds* (2nd ed.), Theorem 1.3 (Circle Classification
Theorem).**  Two circles in a nontrivial real normed space are congruent — i.e. some rigid motion
of the ambient space carries one onto the other as a set — if and only if they have the same
radius.

Rigid motions are modelled as `E ≃ᵃⁱ[ℝ] E`; by Mazur-Ulam this is exactly Lee's notion of a
bijective distance-preserving self-map of the space.  See the module docstring for why
`[Nontrivial E]` is necessary. -/
theorem circle_congruent_iff_radius_eq (c₁ c₂ : E) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    (∃ f : E ≃ᵃⁱ[ℝ] E, f '' sphere c₁ r₁ = sphere c₂ r₂) ↔ r₁ = r₂ := by
  constructor
  · rintro ⟨f, hf⟩
    exact radius_eq_of_affineIsometryEquiv_image_sphere hr₁ hr₂ f hf
  · rintro rfl
    exact exists_affineIsometryEquiv_image_sphere c₁ c₂ r₁

end Main

/-- **Lee's Theorem 1.3 for the Euclidean plane**, which is the setting of Lee's Chapter 1: two
circles in `EuclideanSpace ℝ (Fin 2)` are congruent if and only if they have the same radius. -/
theorem euclidean_circle_congruent_iff_radius_eq
    (c₁ c₂ : EuclideanSpace ℝ (Fin 2)) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    (∃ f : EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2),
      f '' sphere c₁ r₁ = sphere c₂ r₂) ↔ r₁ = r₂ :=
  circle_congruent_iff_radius_eq c₁ c₂ hr₁ hr₂

end LeeLib.Ch01
