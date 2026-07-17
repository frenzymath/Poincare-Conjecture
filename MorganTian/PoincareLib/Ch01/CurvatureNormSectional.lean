import PoincareLib.Ch01.CurvatureOperator

/-!
# Poincaré Ch. 1, §1.2 — `|Rm| ≤ K` bounds *every* sectional curvature

`def:curvature-operator-norm` records that `|Rm(x)| ≤ K` gives `|K(P)| ≤ K` for every `2`-plane
`P`, and `abs_curvatureForm_le_of_hasCurvatureOperatorNormLe` proves it — but only in the form
`|B(x,y,x,y)| ≤ K` for an **orthonormal** pair `x, y`. The comparison lemmas of §1.5
(`lem:conjugate-sturm`, and through it `lem:local-diffeomorphism-bounded-curvature` and
`thm:sectional-curvature-comparison`) consume a bound on `sectionalCurvature B x y` for
**arbitrary** `x, y`. This file closes that gap, at the level of a single fiber.

## The argument

`sectionalCurvature B x y = B(x,y,x,y) / |x ∧ y|²` depends only on the plane spanned by `x, y`,
not on the spanning pair (`IsAlgCurvatureForm.sectionalCurvature_changeBasis`, do Carmo Ch. 4
Prop. 3.1). So:

* if `x, y` are **dependent**, `|x ∧ y|² = 0` and `sectionalCurvature` takes the junk value `0`
  (division by zero), which is `≤ K` because `K ≥ 0`;
* if `x, y` are **independent**, Gram–Schmidt replaces them by an orthonormal pair spanning the
  same plane — `x' = ‖x‖⁻¹·x` and `y' = ‖z‖⁻¹·z` with `z = y − (⟨x,y⟩/⟨x,x⟩)·x` — and this is a
  linear change of the spanning pair of determinant `‖x‖⁻¹‖z‖⁻¹ ≠ 0`. On an orthonormal pair
  `|x' ∧ y'|² = 1`, so the sectional curvature *is* `B(x',y',x',y')`, and the operator-norm bound
  applies directly.

## Main results

* `exists_orthonormal_changeBasis` — Gram–Schmidt, packaged as the explicit change of basis
  `sectionalCurvature_changeBasis` consumes.
* `abs_sectionalCurvature_le_of_hasCurvatureOperatorNormLe` — `|Rm| ≤ K ⟹ |K(P)| ≤ K` for every
  pair, junk cases included.

The manifold-level corollary (`sectionalCurvatureAt ... ≤ K` at a point, which is the form
`lem:conjugate-sturm` consumes) is a direct wrapper, but must be stated under the
`Bundle.RiemannianBundle` local instance that `curvatureFormAt` carries; it is left for the
session that re-quantifies `lem:local-diffeomorphism-bounded-curvature` over the whole ball.

Blueprint: `def:curvature-operator-norm`, `def:sectional-curvature`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2.
-/

open Riemannian

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : V → V → V → V → ℝ}

/-- **Math.** **Gram–Schmidt for a linearly independent pair.** From independent `x, y` produce
an *orthonormal* pair spanning the same plane, presented as an explicit linear change of the
spanning pair `x' = a·x + b·y`, `y' = c·x + d·y` with `a·d − b·c ≠ 0` — the shape
`IsAlgCurvatureForm.sectionalCurvature_changeBasis` consumes.

Concretely `x' = ‖x‖⁻¹·x` and `y' = ‖z‖⁻¹·z` for `z = y − (⟨x,y⟩/⟨x,x⟩)·x`. -/
theorem exists_orthonormal_changeBasis (x y : V) (hxy : LinearIndependent ℝ ![x, y]) :
    ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧
      (inner ℝ (a • x + b • y) (a • x + b • y) : ℝ) = 1 ∧
      (inner ℝ (c • x + d • y) (c • x + d • y) : ℝ) = 1 ∧
      (inner ℝ (a • x + b • y) (c • x + d • y) : ℝ) = 0 := by
  classical
  -- `x ≠ 0`: otherwise `0 • y = x`, contradicting independence
  have hx0 : x ≠ 0 := by
    intro h
    rw [linearIndependent_fin2] at hxy
    exact hxy.2 0 (by simp [h])
  have hxx : (0 : ℝ) < inner ℝ x x := real_inner_self_pos.2 hx0
  have hxxne : (inner ℝ x x : ℝ) ≠ 0 := ne_of_gt hxx
  -- the Gram–Schmidt correction `z = y − (⟨x,y⟩/⟨x,x⟩)·x`
  set μ : ℝ := (inner ℝ x y : ℝ) / (inner ℝ x x : ℝ) with hμ
  set z : V := y - μ • x with hz
  -- `z ≠ 0`, else `y = μ·x`
  have hz0 : z ≠ 0 := by
    intro h
    rw [hz] at h
    exact ((LinearIndependent.pair_iff' hx0).mp hxy) μ (sub_eq_zero.mp h).symm
  have hzz : (0 : ℝ) < inner ℝ z z := real_inner_self_pos.2 hz0
  -- `z ⟂ x`
  have hxz : (inner ℝ x z : ℝ) = 0 := by
    rw [hz, inner_sub_right, real_inner_smul_right, hμ, div_mul_cancel₀ _ hxxne, sub_self]
  -- the normalizing scalars
  set nx : ℝ := Real.sqrt (inner ℝ x x : ℝ) with hnx
  set nz : ℝ := Real.sqrt (inner ℝ z z : ℝ) with hnz
  have hnxpos : 0 < nx := Real.sqrt_pos.2 hxx
  have hnzpos : 0 < nz := Real.sqrt_pos.2 hzz
  have hnx2 : nx * nx = (inner ℝ x x : ℝ) := Real.mul_self_sqrt hxx.le
  have hnz2 : nz * nz = (inner ℝ z z : ℝ) := Real.mul_self_sqrt hzz.le
  -- `x' = nx⁻¹·x + 0·y`,  `y' = (−nz⁻¹μ)·x + nz⁻¹·y = nz⁻¹·z`
  have hxe : (nx⁻¹ • x + (0 : ℝ) • y) = nx⁻¹ • x := by simp
  have hye : (-(nz⁻¹ * μ) • x + nz⁻¹ • y) = nz⁻¹ • z := by
    rw [hz, smul_sub, smul_smul]
    module
  refine ⟨nx⁻¹, 0, -(nz⁻¹ * μ), nz⁻¹, ?_, ?_, ?_, ?_⟩
  · -- the determinant is `nx⁻¹·nz⁻¹ ≠ 0`
    have hd : nx⁻¹ * nz⁻¹ - 0 * (-(nz⁻¹ * μ)) = nx⁻¹ * nz⁻¹ := by ring
    rw [hd]
    positivity
  · -- `⟨x', x'⟩ = 1`
    rw [hxe, real_inner_smul_left, real_inner_smul_right, ← hnx2]
    field_simp
  · -- `⟨y', y'⟩ = 1`
    rw [hye, real_inner_smul_left, real_inner_smul_right, ← hnz2]
    field_simp
  · -- `⟨x', y'⟩ = 0`, since `z ⟂ x`
    rw [hxe, hye, real_inner_smul_left, real_inner_smul_right, hxz]
    ring

/-- **Math.** **`|Rm| ≤ K` bounds every sectional curvature.** The final claim of
`def:curvature-operator-norm`, for an arbitrary pair — neither assumed orthonormal nor assumed
independent.

Blueprint: `def:curvature-operator-norm`, `def:sectional-curvature`. -/
theorem abs_sectionalCurvature_le_of_hasCurvatureOperatorNormLe
    (hB : IsAlgCurvatureForm B) {K : ℝ} (hK : 0 ≤ K)
    (h : HasCurvatureOperatorNormLe hB K) (x y : V) :
    |sectionalCurvature B x y| ≤ K := by
  classical
  by_cases hxy : LinearIndependent ℝ ![x, y]
  · -- independent: Gram–Schmidt to an orthonormal pair spanning the same plane
    obtain ⟨a, b, c, d, hdet, hx1, hy1, hxy0⟩ := exists_orthonormal_changeBasis x y hxy
    have hchange :
        sectionalCurvature B (a • x + b • y) (c • x + d • y) = sectionalCurvature B x y :=
      hB.sectionalCurvature_changeBasis hdet x y hxy
    -- on an orthonormal pair the wedge norm is `1`, so the sectional curvature *is* `B(x',y',x',y')`
    have hw : wedgeSq (a • x + b • y) (c • x + d • y) = 1 := by
      rw [wedgeSq, hx1, hy1, hxy0]
      ring
    have hsec : sectionalCurvature B (a • x + b • y) (c • x + d • y)
        = B (a • x + b • y) (c • x + d • y) (a • x + b • y) (c • x + d • y) := by
      rw [sectionalCurvature, hw, div_one]
    rw [← hchange, hsec]
    exact abs_curvatureForm_le_of_hasCurvatureOperatorNormLe hB h _ _ hx1 hy1 hxy0
  · -- dependent: the wedge norm vanishes, so the sectional curvature is the junk value `0`
    have hw : wedgeSq x y = 0 :=
      le_antisymm (not_lt.mp fun hpos =>
        hxy ((wedgeSq_pos_iff_linearIndependent x y).mp hpos)) (wedgeSq_nonneg x y)
    rw [sectionalCurvature, hw, div_zero, abs_zero]
    exact hK

end PoincareLib

end
