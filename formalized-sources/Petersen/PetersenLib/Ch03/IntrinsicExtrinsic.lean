import PetersenLib.Ch03.ExercisesHypersurface

/-!
# Petersen Ch. 3, §3.2 — Intrinsic versus extrinsic geometry

Petersen's remark (`rem:pet-ch3-intrinsic-extrinsic`, following Example 3.2.9):
the curvature tensor of `(M,g)` measures *intrinsic* bending — everything
computable from `g` alone — while the shape operator `S` of an isometric
immersion measures *extrinsic* bending, i.e. how `(M,g)` sits inside the ambient
space.

The logical content that distinguishes the two notions is that the shape
operator is **not** recoverable from the intrinsic curvature: two genuinely
different second fundamental forms can induce the *same* intrinsic curvature.
For a hypersurface `H^{n-1} ⊂ ℝⁿ` in flat ambient space, the Gauss equation
(Thm 3.2.4) identifies the intrinsic `(0,4)`-curvature with the Kulkarni–Nomizu
square `Π ⊛ Π` of the second fundamental form (`Ex12.gaussCurvatureForm`, the
payload of Exercise 3.4.12).  The **plane** (`S = 0`) and a **cylinder**
(`S =` a rank-one shape operator) are the classical illustration: both are
intrinsically flat (`Π ⊛ Π ≡ 0`, since a rank-one form has vanishing
Kulkarni–Nomizu square) yet have different shape operators — extrinsic data lost
to the intrinsic curvature.

`intrinsicExtrinsicGeometry` records exactly this: there exist two distinct
symmetric shape operators on `ℝ²` whose (flat-ambient) intrinsic curvature
forms agree identically.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.2, remark after
Example 3.2.9.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace PetersenLib

/-- **Math.** Petersen §3.2 (`rem:pet-ch3-intrinsic-extrinsic`): the shape
operator (extrinsic data) is not determined by the intrinsic curvature.  Two
distinct symmetric shape operators on `ℝ²` — the plane `S₁ = 0` and a rank-one
"cylinder" `S₂ : x ↦ ⟪u,x⟫·u` — induce the *same* intrinsic Gauss curvature form
`Π ⊛ Π ≡ 0` (both are intrinsically flat), witnessing that intrinsic geometry
(curvature) and extrinsic geometry (the second fundamental form) are genuinely
different: `S₁ ≠ S₂` while `gaussCurvatureForm S₁ = gaussCurvatureForm S₂`. -/
theorem intrinsicExtrinsicGeometry :
    ∃ S₁ S₂ : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      S₁.IsSymmetric ∧ S₂.IsSymmetric ∧ S₁ ≠ S₂ ∧
      ∀ v w x y, Ex12.gaussCurvatureForm S₁ v w x y = Ex12.gaussCurvatureForm S₂ v w x y := by
  classical
  set u : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (1 : ℝ) with hu
  have hcoord : u 0 = 1 := by rw [hu]; simp
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0] at hcoord; simp at hcoord
  have huu : (0 : ℝ) < ⟪u, u⟫ := real_inner_self_pos.mpr hu0
  -- The rank-one "cylinder" shape operator `S₂ : x ↦ ⟪u,x⟫ • u`.
  refine ⟨0, (innerₗ (EuclideanSpace ℝ (Fin 2)) u).smulRight u, ?_, ?_, ?_, ?_⟩
  · -- `S₁ = 0` is self-adjoint.
    intro x y; simp
  · -- `S₂` is self-adjoint: `⟪⟪u,x⟫•u, y⟫ = ⟪x, ⟪u,y⟫•u⟫`.
    intro x y
    simp only [LinearMap.smulRight_apply, innerₗ_apply_apply, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm x u]; ring
  · -- `S₁ ≠ S₂`: `S₂ u = ⟪u,u⟫ • u ≠ 0` while `S₁ u = 0`.
    intro h
    have key : ((innerₗ (EuclideanSpace ℝ (Fin 2)) u).smulRight u) u = 0 := by
      rw [← h]; simp
    simp only [LinearMap.smulRight_apply, innerₗ_apply_apply] at key
    rw [smul_eq_zero] at key
    rcases key with h' | h'
    · exact huu.ne' h'
    · exact hu0 h'
  · -- Both curvature forms vanish (rank-one Kulkarni–Nomizu square).
    intro v w x y
    simp only [Ex12.gaussCurvatureForm, Ex12.secondFundamentalBilin_apply,
      kulkarniNomizuProduct, LinearMap.zero_apply, inner_zero_left, LinearMap.smulRight_apply,
      innerₗ_apply_apply, real_inner_smul_left]
    ring

end PetersenLib
