import PoincareLib.Ch01.IndexFormConjugate
import PoincareLib.Ch01.FrameCurvSmooth

/-!
# Poincaré Ch. 1 — the negative direction at a conjugate point, as two smooth halves

`IndexFormNegative` / `IndexFormConjugate` deliver the first half of
`prop:minimal-geodesic-no-conjugate`: from a conjugate point at an interior time
`t₀ ∈ (0, 1)` they produce a field `W` along `γ`, vanishing at `0` and `1`, with
`indexForm (frameCurvOp g γ e) 0 1 W DW W DW < 0`.  But `W` is exported only as a
*piecewise-`C¹`* object (a `ContinuousOn` plus two `HasDerivWithinAt` clauses),
and the second half — `I ≥ 0` for a minimizing geodesic, proved by a broken chart
variation — cannot consume that.  The chart variation bump-extends its data with
`exists_contDiff_eqOn_of_contDiffOn_Ioo`, so it needs **each smooth piece of the
field to be `C³` on an open interval strictly containing that piece**.

This file closes the mismatch.  Nothing analytic is lost: the construction of
`IndexFormNegative` already has the regularity, it is only the *truncation* that
hides it.

* The Jacobi solution `y` does not stop at `t₀`: in the frame it solves
  `y″ + ℛ y = 0` on the whole open interval `(a, b)`, and `ℛ = frameCurvOp` is now
  known to be `C^∞` in `t` (`contDiffOn_frameCurvOp_infty`, built for exactly this
  purpose).  So `y` is `C^∞` on `(a, b)` — `contDiffOn_jacobiSol_of_isOpen`, the
  two-line bootstrap `y′ = v`, `v′ = −ℛ y` of `contDiffOn_secondOrderODE`'s style
  (openness of the time set is load-bearing).
* The test field `Z t = t(1 − t) • v t₀` is a polynomial times a fixed vector, hence
  `C^∞` on all of `ℝ`.

So instead of the glued, cornered field `W = ŷ + c·Z` we export its two **halves**

`W₀ = y + c·Z`  on `[0, t₀]`,   `W₁ = c·Z`  on `[t₀, 1]`,

which are `C^∞` where they live, match at `t₀` (because `y t₀ = 0`), vanish at the
outer endpoints (`y 0 = 0`, `Z 0 = Z 1 = 0`), and whose **two index forms sum to a
strictly negative number** — precisely the sum the broken-chart second variation
produces.  The gluing is thereby moved out of the analysis and into the statement.

The quadratic-perturbation argument is run directly on the sum, which is cleaner
than on the glued field: the truncated field never appears, so neither does its
corner.  Writing `κ = I_{[0,t₀]}(y, Z)` and `Q = I_{[0,t₀]}(Z) + I_{[t₀,1]}(Z)`,

`I_{[0,t₀]}(y + cZ) + I_{[t₀,1]}(cZ) = I_{[0,t₀]}(y) + 2cκ + c²Q = 2cκ + c²Q`,

since a Jacobi field vanishing at both ends of `[0, t₀]` has zero index
(`IsJacobiSolOn.indexForm_self_eq_zero`); and integration by parts against the
Jacobi field (`IsJacobiSolOn.indexForm_eq_sub`) gives
`κ = ⟪v t₀, Z t₀⟫ = t₀(1 − t₀)‖v t₀‖² > 0`, because `v t₀ ≠ 0` at a conjugate point
of a nontrivial Jacobi field.  A nonzero linear term makes the quadratic negative
on one side of the origin (`exists_quadratic_neg`).

Main results:

* `contDiffOn_jacobiSol_of_isOpen` — a solution of `y″ + R y = 0` with `R` of class
  `C^∞` on an **open** set of times is `C^n` there, for every `n`;
* `hasDerivAt_frameVec_fst` / `_snd` — the frame reading of a Jacobi field solves the
  abstract ODE with **two-sided** derivatives at every interior time (the `Ioo`
  companion of `isJacobiSolOn_frameVec`, which reads it on a closed `[0, B]`);
* `exists_indexForm_neg_split_of_jacobi_vanishing` — the abstract two-half statement;
* `exists_indexForm_neg_smooth_of_isConjugatePointAt` — **the deliverable**: on the
  manifold, a conjugate point at an interior time yields a parallel orthonormal frame
  and two `C³` half-fields whose index forms sum to a strictly negative number.

Blueprint: `prop:minimal-geodesic-no-conjugate`, `lem:index-form-negative-at-conjugate`,
`claim:second-variation-minimal-geodesic`, `def:conjugate-point`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.3–§1.4.
-/

open Set Riemannian Module MeasureTheory intervalIntegral
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

/-! ### A real quadratic with a nonzero linear term goes negative -/

/-- **Math.** If `κ ≠ 0` then the quadratic `c ↦ 2cκ + c²Q` is strictly negative
somewhere: the linear term dominates near the origin.  Taking
`c = −κ/(|Q| + 1)` — which has sign opposite to `κ` and satisfies `|cQ| < |κ|` —
makes `2κ + cQ` have the sign of `κ`, so `c(2κ + cQ) < 0`.

This is the scalar core of `exists_indexForm_neg`, isolated so that it can be run
against a *sum* of index forms over adjacent intervals rather than a single one. -/
theorem exists_quadratic_neg {κ Q : ℝ} (hκ : κ ≠ 0) :
    ∃ c : ℝ, 2 * c * κ + c ^ 2 * Q < 0 := by
  refine ⟨-κ / (|Q| + 1), ?_⟩
  have hpos : (0 : ℝ) < |Q| + 1 := by positivity
  set c : ℝ := -κ / (|Q| + 1) with hc
  have hq : 2 * c * κ + c ^ 2 * Q = c * (2 * κ + c * Q) := by ring
  rw [hq]
  have hcQ : |c * Q| < |κ| := by
    rw [hc, abs_mul, abs_div, abs_neg, abs_of_pos hpos]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
    have hκpos : 0 < |κ| := abs_pos.mpr hκ
    nlinarith [abs_nonneg Q]
  rcases lt_or_gt_of_ne hκ with hneg | hpos'
  · have hcpos : 0 < c := by
      rw [hc]; exact div_pos (neg_pos.mpr hneg) hpos
    have hlin : 2 * κ + c * Q < 0 := by
      have h := abs_lt.mp hcQ
      have hκabs : |κ| = -κ := abs_of_neg hneg
      linarith [h.2, hκabs ▸ h.2]
    exact mul_neg_of_pos_of_neg hcpos hlin
  · have hcneg : c < 0 := by
      rw [hc]; exact div_neg_of_neg_of_pos (neg_neg_iff_pos.mpr hpos') hpos
    have hlin : 0 < 2 * κ + c * Q := by
      have h := abs_lt.mp hcQ
      have hκabs : |κ| = κ := abs_of_pos hpos'
      linarith [h.1, hκabs ▸ h.1]
    exact mul_neg_of_neg_of_pos hcneg hlin

/-! ### The abstract theory over the coefficient space -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-! #### The ODE bootstrap: a Jacobi solution is as smooth as its coefficient -/

/-- **Math.** **ODE bootstrap for the Jacobi equation.**  Let `J ⊆ ℝ` be **open**,
`R : ℝ → F →L[ℝ] F` of class `C^∞` on `J`, and let `(y, v)` satisfy the first-order
system `y′ = v`, `v′ = −R y` with *two-sided* derivatives at every `t ∈ J`.  Then `y`
and `v` are `C^n` on `J`, for every `n`.

*Proof.*  Simultaneous induction on `n`.  For `n = 0` both are differentiable, hence
continuous.  For the step: `deriv y = v` is `C^n` by the inductive hypothesis, and
`deriv v = −R y` is a `C^n` expression in `C^n` data (`R` is `C^∞`, `y` is `C^n`), so
`contDiffOn_succ_iff_deriv_of_isOpen` — openness of `J` is load-bearing — upgrades
both from `C^n` to `C^{n+1}`.  ∎

This is the exact analogue, for the *linear second-order* equation, of the geodesic
bootstrap `contDiffOn_secondOrderODE` and of the parallel-transport bootstrap
`contDiffOn_firstOrderLinearODE`; no completeness, no finite-dimensionality and no
uniqueness theory is used.  It is what lifts the conjugate-point field from the `C¹`
that the intrinsic theory produces to the `C³` that the second variation demands. -/
theorem contDiffOn_jacobiSol_of_isOpen {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {J : Set ℝ}
    (hJ : IsOpen J) (hR : ContDiffOn ℝ ∞ R J)
    (hy : ∀ t ∈ J, HasDerivAt y (v t) t)
    (hv : ∀ t ∈ J, HasDerivAt v (-(R t) (y t)) t) (n : ℕ) :
    ContDiffOn ℝ n y J ∧ ContDiffOn ℝ n v J := by
  have hdy : DifferentiableOn ℝ y J := fun t ht =>
    (hy t ht).differentiableAt.differentiableWithinAt
  have hdv : DifferentiableOn ℝ v J := fun t ht =>
    (hv t ht).differentiableAt.differentiableWithinAt
  have hddy : ∀ t ∈ J, deriv y t = v t := fun t ht => (hy t ht).deriv
  have hddv : ∀ t ∈ J, deriv v t = -(R t) (y t) := fun t ht => (hv t ht).deriv
  induction n with
  | zero =>
    exact ⟨contDiffOn_zero.mpr hdy.continuousOn, contDiffOn_zero.mpr hdv.continuousOn⟩
  | succ n ih =>
    obtain ⟨hyn, hvn⟩ := ih
    have hRn : ContDiffOn ℝ n R J := contDiffOn_infty.mp hR n
    have hderiv_y : ContDiffOn ℝ n (deriv y) J := hvn.congr hddy
    have hderiv_v : ContDiffOn ℝ n (deriv v) J :=
      ((hRn.clm_apply hyn).neg).congr hddv
    exact ⟨(contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr ⟨hdy, by simp, hderiv_y⟩,
      (contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr ⟨hdv, by simp, hderiv_v⟩⟩

/-- **Math.** A solution of `y″ + R y = 0` with `C^∞` coefficient is `C^∞` on an open
set of times. -/
theorem contDiffOn_infty_jacobiSol_of_isOpen {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {J : Set ℝ}
    (hJ : IsOpen J) (hR : ContDiffOn ℝ ∞ R J)
    (hy : ∀ t ∈ J, HasDerivAt y (v t) t)
    (hv : ∀ t ∈ J, HasDerivAt v (-(R t) (y t)) t) :
    ContDiffOn ℝ ∞ y J :=
  contDiffOn_infty.mpr fun n => (contDiffOn_jacobiSol_of_isOpen hJ hR hy hv n).1

/-! #### Smoothness of the test field -/

/-- **Math.** The test field `Z t = t(1 − t) • w` is a polynomial times a fixed
vector, hence `C^∞` on all of `ℝ`. -/
theorem contDiff_testField (w : F) (n : WithTop ℕ∞) : ContDiff ℝ n (testField w) :=
  (contDiff_id.mul (contDiff_const.sub contDiff_id)).smul contDiff_const

/-! #### The two-half negative-index construction -/

/-- **Math.** **A conjugate point at an interior time makes the index form indefinite
— in two smooth halves.**

Let `R` be a self-adjoint coefficient of class `C^∞` on an open interval `(A, B)`
containing `[0, 1]`, and let `(y, v)` solve the Jacobi ODE `y″ + R y = 0` there (with
two-sided derivatives, `(A, B)` being open).  Suppose `y 0 = 0`, `y t₀ = 0` for some
`t₀ ∈ (0, 1)`, and `y` is not identically zero on `[0, t₀]` — i.e. `t₀` is a conjugate
point of a nontrivial Jacobi field.

Then there are **two fields `W₀`, `W₁`**, `C^∞` where they live (`W₀` on `(A, B)`,
`W₁` on all of `ℝ`), with

`W₀ 0 = 0`,  `W₁ 1 = 0`,  `W₀ t₀ = W₁ t₀`  (so they glue to a continuous field
vanishing at both endpoints of `[0, 1]`),

whose two index forms **sum to a strictly negative number**:

`I_{[0,t₀]}(W₀) + I_{[t₀,1]}(W₁) < 0`.

The witnesses are `W₀ = y + c·Z`, `W₁ = c·Z` with `Z t = t(1 − t) • v t₀` and `c` the
perturbation parameter; they match at `t₀` exactly because `y t₀ = 0`, which is the
truncation of `IndexFormNegative` seen from the other side — here it costs nothing,
because the two halves are never glued into a single (cornered) function.

Blueprint: `lem:index-form-negative-at-conjugate`,
`prop:minimal-geodesic-no-conjugate`. -/
theorem exists_indexForm_neg_split_of_jacobi_vanishing
    {R : ℝ → F →L[ℝ] F} {A B t₀ : ℝ} {y v : ℝ → F}
    (hA : A < 0) (hB : 1 < B) (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
    (hR : ContDiffOn ℝ ∞ R (Ioo A B))
    (hRsymm : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hy : ∀ t ∈ Ioo A B, HasDerivAt y (v t) t)
    (hv : ∀ t ∈ Ioo A B, HasDerivAt v (-(R t) (y t)) t)
    (hy0 : y 0 = 0) (hyt : y t₀ = 0) (hne : ∃ t ∈ Icc 0 t₀, y t ≠ 0) :
    ∃ W₀ W₁ : ℝ → F,
      ContDiffOn ℝ ∞ W₀ (Ioo A B) ∧ ContDiff ℝ ∞ W₁ ∧
      W₀ 0 = 0 ∧ W₁ 1 = 0 ∧ W₀ t₀ = W₁ t₀ ∧
      indexForm R 0 t₀ W₀ (deriv W₀) W₀ (deriv W₀)
        + indexForm R t₀ 1 W₁ (deriv W₁) W₁ (deriv W₁) < 0 := by
  -- ### the two closed pieces sit inside the open interval
  have h01 : Icc (0 : ℝ) 1 ⊆ Ioo A B := fun t ht =>
    ⟨lt_of_lt_of_le hA ht.1, lt_of_le_of_lt ht.2 hB⟩
  have h0t₀ : Icc (0 : ℝ) t₀ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl ht₁.le
  have hsubAB : Icc (0 : ℝ) t₀ ⊆ Ioo A B := h0t₀.trans h01
  have hRc : ContinuousOn R (Icc (0 : ℝ) 1) := hR.continuousOn.mono h01
  have hR₁ : ContinuousOn R (Icc (0 : ℝ) t₀) := hRc.mono h0t₀
  -- ### the Jacobi solution on the first piece, and the corner datum `v t₀ ≠ 0`
  have hsol : IsJacobiSolOn R 0 t₀ y v :=
    { hasDerivWithinAt_fst := fun t ht => (hy t (hsubAB ht)).hasDerivWithinAt
      hasDerivWithinAt_snd := fun t ht => (hv t (hsubAB ht)).hasDerivWithinAt }
  have hvne : v t₀ ≠ 0 := hsol.snd_ne_zero_of_ne_zero hR₁ hyt hne
  -- ### the test field
  set Z : ℝ → F := testField (v t₀) with hZdef
  set DZ : ℝ → F := testDeriv (v t₀) with hDZdef
  have hZc : Continuous Z := by rw [hZdef]; exact continuous_testField _
  have hDZc : Continuous DZ := by rw [hDZdef]; exact continuous_testDeriv _
  have hZderiv : ∀ t, HasDerivAt Z (DZ t) t := by
    intro t; rw [hZdef, hDZdef]; exact hasDerivAt_testField (v t₀) t
  have hZ0 : Z 0 = 0 := by rw [hZdef]; exact testField_zero _
  have hZ1 : Z 1 = 0 := by rw [hZdef]; exact testField_one _
  have hZt₀ : Z t₀ = (t₀ * (1 - t₀)) • v t₀ := by rw [hZdef]; rfl
  -- ### integrability on the first piece
  have hyc : ContinuousOn y (Icc 0 t₀) := hsol.continuousOn_fst
  have hvc : ContinuousOn v (Icc 0 t₀) := hsol.continuousOn_snd
  have hint_yy : IntervalIntegrable (indexIntegrand R y v y v) volume 0 t₀ := by
    refine intervalIntegrable_indexIntegrand ?_ ?_ ?_ ?_ ?_ <;> rw [uIcc_of_le ht₀.le]
    exacts [hR₁, hyc, hvc, hyc, hvc]
  have hint_yz : IntervalIntegrable (indexIntegrand R y v Z DZ) volume 0 t₀ := by
    refine intervalIntegrable_indexIntegrand ?_ ?_ ?_ ?_ ?_ <;> rw [uIcc_of_le ht₀.le]
    exacts [hR₁, hyc, hvc, hZc.continuousOn, hDZc.continuousOn]
  have hint_zz : IntervalIntegrable (indexIntegrand R Z DZ Z DZ) volume 0 t₀ := by
    refine intervalIntegrable_indexIntegrand ?_ ?_ ?_ ?_ ?_ <;> rw [uIcc_of_le ht₀.le]
    exacts [hR₁, hZc.continuousOn, hDZc.continuousOn, hZc.continuousOn, hDZc.continuousOn]
  -- ### the Jacobi field is a null direction of the index form on `[0, t₀]`
  have hI_self : indexForm R 0 t₀ y v y v = 0 :=
    hsol.indexForm_self_eq_zero ht₀.le hR₁ hy0 hyt
  -- ### the cross term: integration by parts sees only the boundary
  have hκ : indexForm R 0 t₀ y v Z DZ = t₀ * (1 - t₀) * ‖v t₀‖ ^ 2 := by
    rw [hsol.indexForm_eq_sub ht₀.le hR₁ (fun t _ => (hZderiv t).hasDerivWithinAt)
      hDZc.continuousOn, hZ0, hZt₀]
    simp only [inner_zero_right, sub_zero, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hκne : indexForm R 0 t₀ y v Z DZ ≠ 0 := by
    rw [hκ]
    have hpos : 0 < t₀ * (1 - t₀) * ‖v t₀‖ ^ 2 := by
      have h1 : 0 < 1 - t₀ := by linarith
      have h2 : 0 < ‖v t₀‖ := norm_pos_iff.mpr hvne
      positivity
    exact ne_of_gt hpos
  -- ### the perturbation parameter
  obtain ⟨c, hc⟩ := exists_quadratic_neg
    (κ := indexForm R 0 t₀ y v Z DZ)
    (Q := indexForm R 0 t₀ Z DZ Z DZ + indexForm R t₀ 1 Z DZ Z DZ) hκne
  -- ### the two half-fields and their derivatives
  have hW₀d : ∀ t ∈ Ioo A B, HasDerivAt (y + c • Z) (v t + c • DZ t) t := fun t ht =>
    (hy t ht).add ((hZderiv t).const_smul c)
  have hdW₀ : ∀ t ∈ Ioo A B, deriv (y + c • Z) t = v t + c • DZ t := fun t ht =>
    (hW₀d t ht).deriv
  have hdW₁ : ∀ t, deriv (c • Z) t = c • DZ t := fun t => ((hZderiv t).const_smul c).deriv
  -- ### smoothness
  have hysm : ContDiffOn ℝ ∞ y (Ioo A B) :=
    contDiffOn_infty_jacobiSol_of_isOpen isOpen_Ioo hR hy hv
  have hZsm : ContDiff ℝ ∞ Z := by rw [hZdef]; exact contDiff_testField _ _
  have hW₀sm : ContDiffOn ℝ ∞ (y + c • Z) (Ioo A B) :=
    hysm.add (hZsm.const_smul c).contDiffOn
  have hW₁sm : ContDiff ℝ ∞ (c • Z) := hZsm.const_smul c
  refine ⟨y + c • Z, c • Z, hW₀sm, hW₁sm, ?_, ?_, ?_, ?_⟩
  · simp [hy0, hZ0]
  · simp [hZ1]
  · simp [hyt]
  -- ### the index computation
  · have e₀ : indexForm R 0 t₀ (y + c • Z) (deriv (y + c • Z)) (y + c • Z)
        (deriv (y + c • Z))
        = indexForm R 0 t₀ (y + c • Z) (v + c • DZ) (y + c • Z) (v + c • DZ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le ht₀.le] at ht
      simp [indexIntegrand, hdW₀ t (hsubAB ht)]
    have e₁ : indexForm R t₀ 1 (c • Z) (deriv (c • Z)) (c • Z) (deriv (c • Z))
        = indexForm R t₀ 1 (c • Z) (c • DZ) (c • Z) (c • DZ) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp [indexIntegrand, hdW₁ t]
    have hexp₀ : indexForm R 0 t₀ (y + c • Z) (v + c • DZ) (y + c • Z) (v + c • DZ)
        = indexForm R 0 t₀ y v y v + 2 * c * indexForm R 0 t₀ y v Z DZ
          + c ^ 2 * indexForm R 0 t₀ Z DZ Z DZ :=
      indexForm_add_smul hRsymm hint_yy hint_yz hint_zz c
    have hexp₁ : indexForm R t₀ 1 (c • Z) (c • DZ) (c • Z) (c • DZ)
        = c ^ 2 * indexForm R t₀ 1 Z DZ Z DZ := by
      unfold indexForm
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [indexIntegrand, Pi.smul_apply, map_smul, real_inner_smul_left,
        real_inner_smul_right]
      ring
    have hcollect : indexForm R 0 t₀ y v y v + 2 * c * indexForm R 0 t₀ y v Z DZ
          + c ^ 2 * indexForm R 0 t₀ Z DZ Z DZ + c ^ 2 * indexForm R t₀ 1 Z DZ Z DZ
        = 2 * c * indexForm R 0 t₀ y v Z DZ
          + c ^ 2 * (indexForm R 0 t₀ Z DZ Z DZ + indexForm R t₀ 1 Z DZ Z DZ) := by
      rw [hI_self]; ring
    rw [e₀, e₁, hexp₀, hexp₁, hcollect]
    exact hc

end Abstract

/-! ### The manifold statement -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-! #### The frame reading of a Jacobi field, differentiated two-sidedly -/

/-- **Math.** **`y′ = v` at interior times, two-sidedly.**  The `Ioo` companion of the
first half of `isJacobiSolOn_frameVec`: that lemma packages the frame reading of a
Jacobi field as a solution on the *closed* interval `[0, B]`, with one-sided
derivatives at the endpoints, which is what the comparison theory wants.  The ODE
*bootstrap*, on the other hand, wants two-sided derivatives on an **open** set of
times — openness is exactly what `contDiffOn_succ_iff_deriv_of_isOpen` consumes — and
it wants them at times to the left of `0` as well, since the half-field `W₀` must be
smooth on an open interval strictly containing `[0, t₀]`.

The proof is the termwise differentiation of `frameVec V = ∑ᵢ ⟨V, Eᵢ⟩ • bᵢ`, using the
scalar Jacobi system `cᵢ′ = dᵢ` of `hasDerivAt_frameCoeff_fst` — which is *already*
stated at interior times of `[a, b]`. -/
theorem hasDerivAt_frameVec_fst {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (finrank ℝ E) → ℝ → E} {J DJ : ℝ → E} {a b : ℝ}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (frameVec (I := I) g γ e J) (frameVec (I := I) g γ e DJ t) t := by
  classical
  have hterm : ∀ i ∈ Finset.univ, HasDerivAt
      (fun s => frameCoeff (I := I) g γ e J i s • (𝔟 i : 𝔼))
      (frameCoeff (I := I) g γ e DJ i t • (𝔟 i : 𝔼)) t := fun i _ =>
    (hJac.hasDerivAt_frameCoeff_fst hPar hgeo hγc i ht).smul_const _
  rw [frameVec_eq_sumFun (I := I) g γ e J]
  exact HasDerivAt.sum hterm

/-- **Math.** **`v′ = −ℛ y` at interior times, two-sidedly** — the second half of the
same statement, from the scalar system `dᵢ′ = ∑ⱼ ℛᵢⱼ cⱼ` of
`hasDerivAt_frameCoeff_snd`, with the sign flip `ℛ = −frameCurv` built into
`frameCurvOp`. -/
theorem hasDerivAt_frameVec_snd {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (finrank ℝ E) → ℝ → E} {J DJ : ℝ → E} {a b : ℝ}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (frameVec (I := I) g γ e DJ)
      (-(frameCurvOp (I := I) g γ e t) (frameVec (I := I) g γ e J t)) t := by
  classical
  have hterm : ∀ i ∈ Finset.univ, HasDerivAt
      (fun s => frameCoeff (I := I) g γ e DJ i s • (𝔟 i : 𝔼))
      ((∑ j, frameCurv (I := I) g γ e i j t * frameCoeff (I := I) g γ e J j t)
        • (𝔟 i : 𝔼)) t := fun i _ =>
    (hJac.hasDerivAt_frameCoeff_snd hPar hgeo hγc horth i ht).smul_const _
  have hval : -(frameCurvOp (I := I) g γ e t) (frameVec (I := I) g γ e J t)
      = ∑ i, (∑ j, frameCurv (I := I) g γ e i j t
          * frameCoeff (I := I) g γ e J j t) • (𝔟 i : 𝔼) := by
    rw [frameCurvOp_apply]
    simp only [inner_basisFun_frameVec, neg_mul, neg_smul, neg_neg, Finset.sum_neg_distrib]
  rw [frameVec_eq_sumFun (I := I) g γ e DJ, hval]
  exact HasDerivAt.sum hterm

/-! #### The deliverable -/

/-- **Math.** **A conjugate point at an interior time makes the index form of the
geodesic indefinite — with `C³` data on each half.**

This is `exists_indexForm_neg_of_isConjugatePointAt` upgraded from *piecewise `C¹`* to
*piecewise `C³`, each piece smooth on an open interval strictly containing it* — the
regularity that the second-variation half of `prop:minimal-geodesic-no-conjugate`
demands of its input (it bump-extends each piece with
`exists_contDiff_eqOn_of_contDiffOn_Ioo`, which needs a `ContDiffOn` on an **open**
`Ioo`; a `ContDiffOn` on the closed piece would not do).

Along a geodesic `γ` on `[a, b] ⊇ [0, 1]` with a little room at both ends, and given a
conjugate point at `t₀ ∈ (0, 1)`, we produce a parallel `g`-orthonormal frame `e` and
two fields `W₀`, `W₁` in the coefficient space with

* `W₀` of class `C³` on the **open** interval `(a, b) ⊇ [0, t₀]`, and `W₁` of class
  `C³` on all of `ℝ` (it is a polynomial times a fixed vector);
* `W₀ 0 = 0`, `W₁ 1 = 0` — the glued field vanishes at both endpoints of `[0, 1]`;
* `W₀ t₀ = W₁ t₀` — the two halves match at the junction, so they *do* glue to a
  continuous field;
* `I_{[0,t₀]}(W₀) + I_{[t₀,1]}(W₁) < 0` — the index form of the glued field, computed
  as the sum over the two pieces (which is exactly the shape the broken-chart second
  variation produces, by additivity of the interval integral), is strictly negative.

Since a minimizing geodesic has nonnegative index form, this is the contradiction that
establishes `prop:minimal-geodesic-no-conjugate`: a minimizing geodesic has no
interior conjugate point.

The regularity comes from two facts that the intrinsic theory only recently acquired:
the frame Jacobi operator `ℛ = frameCurvOp` is `C^∞` in `t` along the geodesic
(`contDiffOn_frameCurvOp_infty`), and a solution of `y″ + ℛ y = 0` with `C^∞`
coefficient on an open set of times is `C^∞` there
(`contDiffOn_jacobiSol_of_isOpen`).  It is *not* an extra analytic input: the Jacobi
field never was only `C¹`; only its truncation at `t₀` was, and the truncation is
avoided here by exporting the two halves separately.

Blueprint: `prop:minimal-geodesic-no-conjugate`,
`lem:index-form-negative-at-conjugate`, `def:conjugate-point`. -/
theorem exists_indexForm_neg_smooth_of_isConjugatePointAt
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b t₀ : ℝ}
    (ha : a < 0) (hb : 1 < b) (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hconj : IsConjugatePointAt (I := I) g γ t₀) :
    ∃ (e : Fin (finrank ℝ E) → ℝ → E) (W₀ W₁ : ℝ → 𝔼),
      (∀ i, IsParallelAlongOn (I := I) g γ (e i) a b) ∧
      (∀ t ∈ Icc a b, ∀ i j,
        g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0) ∧
      ContDiffOn ℝ 3 W₀ (Ioo a b) ∧ ContDiff ℝ 3 W₁ ∧
      W₀ 0 = 0 ∧ W₁ 1 = 0 ∧ W₀ t₀ = W₁ t₀ ∧
      indexForm (frameCurvOp (I := I) g γ e) 0 t₀ W₀ (deriv W₀) W₀ (deriv W₀)
        + indexForm (frameCurvOp (I := I) g γ e) t₀ 1 W₁ (deriv W₁) W₁ (deriv W₁) < 0 := by
  classical
  have hab : a < b := ha.trans (by linarith)
  have ht₀b : t₀ < b := ht₁.trans hb
  have h0ab : (0 : ℝ) ∈ Icc a b := ⟨ha.le, by linarith⟩
  have hIcc0t : Icc (0 : ℝ) t₀ ⊆ Icc a b := Icc_subset_Icc ha.le ht₀b.le
  -- ### a parallel `g`-orthonormal frame along `γ`
  obtain ⟨e, hPar, horth⟩ := exists_orthonormalParallelFrameAlong (I := I) hab hgeo hγc
  refine ⟨e, ?_⟩
  -- ### the coefficient: `C^∞` in `t` on the open interval
  have hRsm : ContDiffOn ℝ ∞ (frameCurvOp (I := I) g γ e) (Ioo a b) :=
    contDiffOn_frameCurvOp_infty (I := I) hPar hgeo hγc
  have hRsymm : ∀ t, ∀ x x' : 𝔼,
      ⟪frameCurvOp (I := I) g γ e t x, x'⟫ = ⟪x, frameCurvOp (I := I) g γ e t x'⟫ :=
    fun t x x' => frameCurvOp_symm (I := I) g γ e t x x'
  -- ### the conjugate-point Jacobi field, re-solved on the large interval
  obtain ⟨J, DJ, hJac, ⟨s, hs, hJs⟩, hJ0, hJt₀⟩ := hconj
  obtain ⟨J', DJ', hJac', hJ'0, hDJ'0⟩ :=
    exists_isJacobiFieldAlongOn_mem (I := I) hab hgeo hγc h0ab (J 0) (DJ 0)
  have hgeo₀ : IsGeodesicOn (I := I) g γ (Icc 0 t₀) := hgeo.mono hIcc0t
  have hγc₀ : ∀ t ∈ Icc (0 : ℝ) t₀, ContinuousAt γ t := fun t ht => hγc t (hIcc0t ht)
  have hJac'₀ : IsJacobiFieldAlongOn (I := I) g γ J' DJ' 0 t₀ :=
    hJac'.mono ha.le ht₀ ht₀b.le
  have hagree : ∀ t ∈ Icc (0 : ℝ) t₀, J t = J' t ∧ DJ t = DJ' t :=
    IsJacobiFieldAlongOn.eqOn_of_initial (I := I) ht₀ hgeo₀ hγc₀ hJac hJac'₀
      (by rw [hJ'0]) (by rw [hDJ'0])
  have hJ'0' : J' 0 = 0 := by rw [hJ'0, hJ0]
  have hJ't₀ : J' t₀ = 0 := by rw [← (hagree t₀ ⟨ht₀.le, le_rfl⟩).1, hJt₀]
  have hJ's : J' s ≠ 0 := by rw [← (hagree s hs).1]; exact hJs
  -- ### read in the frame: an honest solution of the abstract ODE on `(a, b)`
  have hyd : ∀ t ∈ Ioo a b, HasDerivAt (frameVec (I := I) g γ e J')
      (frameVec (I := I) g γ e DJ' t) t := fun t ht =>
    hasDerivAt_frameVec_fst (I := I) hJac' hPar hgeo hγc ht
  have hvd : ∀ t ∈ Ioo a b, HasDerivAt (frameVec (I := I) g γ e DJ')
      (-(frameCurvOp (I := I) g γ e t) (frameVec (I := I) g γ e J' t)) t := fun t ht =>
    hasDerivAt_frameVec_snd (I := I) hJac' hPar hgeo hγc horth ht
  have hy0 : frameVec (I := I) g γ e J' 0 = 0 :=
    frameVec_eq_zero_of_eq_zero (I := I) hJ'0'
  have hyt₀ : frameVec (I := I) g γ e J' t₀ = 0 :=
    frameVec_eq_zero_of_eq_zero (I := I) hJ't₀
  have hyne : ∃ t ∈ Icc (0 : ℝ) t₀, frameVec (I := I) g γ e J' t ≠ 0 := by
    refine ⟨s, hs, fun hcon => hJ's ?_⟩
    exact eq_zero_of_frameVec_eq_zero (I := I) (horth s (hIcc0t hs)) hcon
  -- ### the abstract two-half construction
  obtain ⟨W₀, W₁, hW₀sm, hW₁sm, hW₀0, hW₁1, hmatch, hneg⟩ :=
    exists_indexForm_neg_split_of_jacobi_vanishing (F := 𝔼) ha hb ht₀ ht₁ hRsm hRsymm
      hyd hvd hy0 hyt₀ hyne
  exact ⟨W₀, W₁, hPar, horth, contDiffOn_infty.mp hW₀sm 3, contDiff_infty.mp hW₁sm 3,
    hW₀0, hW₁1, hmatch, hneg⟩

end PoincareLib

end

#print axioms PoincareLib.exists_quadratic_neg
#print axioms PoincareLib.contDiffOn_jacobiSol_of_isOpen
#print axioms PoincareLib.contDiff_testField
#print axioms PoincareLib.exists_indexForm_neg_split_of_jacobi_vanishing
#print axioms PoincareLib.hasDerivAt_frameVec_fst
#print axioms PoincareLib.hasDerivAt_frameVec_snd
#print axioms PoincareLib.exists_indexForm_neg_smooth_of_isConjugatePointAt
