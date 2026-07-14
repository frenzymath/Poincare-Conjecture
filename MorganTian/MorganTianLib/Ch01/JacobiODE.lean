import OpenGALib.Riemannian.Geodesic.LinearODE
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Poincaré Ch. 1 — the Jacobi second-order linear ODE engine

In a parallel frame along a geodesic, Morgan–Tian's Jacobi equation
`∇_X ∇_X Y + ℛ(Y, X)X = 0` becomes the **second-order linear ODE**
`y'' + R(t) y = 0` with a continuous operator-valued coefficient
`R : ℝ → F →L[ℝ] F` (blueprint `lem:exponential-differential-jacobi`,
`lem:geodesic-polar-form`). This file provides that manifold-free analytic
engine over an arbitrary real Banach space `F` — so it applies verbatim to
vector-valued Jacobi fields (`F = E`) and to matrix Jacobi fields
(`F = E →L[ℝ] E`, the `𝒥(r)` of `lem:geodesic-polar-form`(3)):

* `IsJacobiSolOn R a b y v` — the pair `(y, v)` solves `y' = v`, `v' = −R y`
  on `[a, b]` (one-sided derivatives at the endpoints);
* `exists_isJacobiSolOn_Icc` — global existence with prescribed initial data
  `(y a, v a) = (y₀, v₀)`, by reduction to the first-order linear system
  `W' = A(t) W` on `F × F`, `A(t)(y, v) = (v, −R(t) y)`
  (`Riemannian.LinearODE.exists_hasDerivWithinAt_Icc`);
* `IsJacobiSolOn.eqOn_of_left` / `eqOn_of_right` — uniqueness given the
  initial (resp. final) data, by Grönwall for the pair system;
* superposition (`add`, `const_smul`, `sub`, `isJacobiSolOn_zero`) and the
  vanishing criterion `IsJacobiSolOn.eqOn_zero` — a solution with
  `y a = 0`, `v a = 0` vanishes identically;
* the Grönwall a-priori bound `IsJacobiSolOn.max_norm_le`:
  `max ‖y t‖ ‖v t‖ ≤ max ‖y a‖ ‖v a‖ · e^{K(t−a)}` with `K = max 1 C`,
  `C` an operator-norm bound for `R`;
* **small-time asymptotics** with explicit constants (blueprint
  `lem:jacobi-small-time`): on `[0, b]` with `y 0 = 0` and
  `M = ‖v 0‖ e^{Kb}`,
  `‖y t‖ ≤ M t`, `‖v t − v 0‖ ≤ C M t²/2`, `‖y t − t • v 0‖ ≤ C M t³/6`.
  These are the `𝒥(r) = r·Id + O(r³)`, `𝒥'(r) = Id + O(r²)` estimates of
  `lem:geodesic-polar-form`(3).

Blueprint: `lem:second-order-linear-ode`, `lem:jacobi-small-time`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1
(the Jacobi-field discussion of §1.2 and Lemma `lem:geodesic-polar-form`).
-/

open Set intervalIntegral
open scoped NNReal Topology Interval

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-! ### The first-order pair coefficient -/

/-- **Math.** The coefficient of the first-order system equivalent to the
Jacobi-type equation `y'' + R(t) y = 0`: on the pair space `F × F`,
`A(t)(y, v) = (v, −R(t) y)`, so that `(y, v)' = A(t)(y, v)` iff `y' = v` and
`v' = −R(t) y`. Blueprint: `lem:second-order-linear-ode`. -/
def jacobiPairCoeff (R : ℝ → F →L[ℝ] F) (t : ℝ) : (F × F) →L[ℝ] F × F :=
  (ContinuousLinearMap.snd ℝ F F).prod (-((R t).comp (ContinuousLinearMap.fst ℝ F F)))

@[simp] theorem jacobiPairCoeff_apply (R : ℝ → F →L[ℝ] F) (t : ℝ) (p : F × F) :
    jacobiPairCoeff R t p = (p.2, -(R t) p.1) := rfl

/-- **Math.** Operator-norm bound for the pair coefficient: in the sup norm on
`F × F`, `‖A(t)‖ ≤ max 1 ‖R(t)‖`. -/
theorem norm_jacobiPairCoeff_le (R : ℝ → F →L[ℝ] F) (t : ℝ) :
    ‖jacobiPairCoeff R t‖ ≤ max 1 ‖R t‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (le_trans zero_le_one (le_max_left _ _)) fun p => ?_
  have hnorm : ‖jacobiPairCoeff R t p‖ = max ‖p.2‖ ‖(R t) p.1‖ := by
    simp [Prod.norm_def]
  rw [hnorm]
  refine max_le ?_ ?_
  · calc ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      _ = 1 * ‖p‖ := (one_mul _).symm
      _ ≤ max 1 ‖R t‖ * ‖p‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · calc ‖(R t) p.1‖ ≤ ‖R t‖ * ‖p.1‖ := (R t).le_opNorm _
      _ ≤ ‖R t‖ * ‖p‖ := mul_le_mul_of_nonneg_left (norm_fst_le p) (norm_nonneg _)
      _ ≤ max 1 ‖R t‖ * ‖p‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- **Math.** The pair coefficient inherits continuity from `R`. -/
theorem continuousOn_jacobiPairCoeff {R : ℝ → F →L[ℝ] F} {s : Set ℝ}
    (hR : ContinuousOn R s) : ContinuousOn (jacobiPairCoeff R) s := by
  have h1 : ContinuousOn
      (fun t => -((R t).comp (ContinuousLinearMap.fst ℝ F F))) s :=
    (hR.clm_comp continuousOn_const).neg
  have h2 : ContinuousOn (fun t =>
      ((ContinuousLinearMap.snd ℝ F F : (F × F) →L[ℝ] F),
        -((R t).comp (ContinuousLinearMap.fst ℝ F F)))) s :=
    continuousOn_const.prodMk h1
  exact (ContinuousLinearMap.prodₗᵢ (E := F × F) (F := F) (G := F)
    ℝ).continuous.comp_continuousOn h2

/-! ### The Jacobi-type second-order linear ODE -/

/-- **Math.** The pair `(y, v)` **solves the Jacobi-type second-order linear
ODE** `y'' + R(t) y = 0` on `[a, b]`, in the first-order formulation
`y' = v`, `v' = −R(t) y` (one-sided derivatives at the endpoints).

Blueprint: `lem:second-order-linear-ode`. -/
structure IsJacobiSolOn (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v : ℝ → F) : Prop where
  hasDerivWithinAt_fst : ∀ t ∈ Icc a b, HasDerivWithinAt y (v t) (Icc a b) t
  hasDerivWithinAt_snd : ∀ t ∈ Icc a b, HasDerivWithinAt v (-(R t) (y t)) (Icc a b) t

namespace IsJacobiSolOn

variable {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}

theorem continuousOn_fst (h : IsJacobiSolOn R a b y v) : ContinuousOn y (Icc a b) :=
  fun t ht => (h.hasDerivWithinAt_fst t ht).continuousWithinAt

theorem continuousOn_snd (h : IsJacobiSolOn R a b y v) : ContinuousOn v (Icc a b) :=
  fun t ht => (h.hasDerivWithinAt_snd t ht).continuousWithinAt

/-- **Math.** The pair curve `t ↦ (y t, v t)` solves the equivalent first-order
linear system `W' = A(t) W` on `F × F`. -/
theorem isSolOn_pair (h : IsJacobiSolOn R a b y v) :
    Riemannian.LinearODE.IsSolOn (jacobiPairCoeff R) a b (fun t => (y t, v t)) := by
  intro t ht
  have := (h.hasDerivWithinAt_fst t ht).prodMk (h.hasDerivWithinAt_snd t ht)
  simpa using this

end IsJacobiSolOn

/-- **Math.** Conversely, the components of a solution of the pair system solve
the second-order equation. -/
theorem isJacobiSolOn_of_isSolOn {R : ℝ → F →L[ℝ] F} {a b : ℝ} {W : ℝ → F × F}
    (h : Riemannian.LinearODE.IsSolOn (jacobiPairCoeff R) a b W) :
    IsJacobiSolOn R a b (fun t => (W t).1) (fun t => (W t).2) where
  hasDerivWithinAt_fst t ht := by
    have := (ContinuousLinearMap.fst ℝ F F).hasFDerivAt.comp_hasDerivWithinAt t (h t ht)
    simpa using this
  hasDerivWithinAt_snd t ht := by
    have := (ContinuousLinearMap.snd ℝ F F).hasFDerivAt.comp_hasDerivWithinAt t (h t ht)
    simpa using this

/-- Package a real bound `‖R t‖ ≤ C` on `[a, b]` as an `ℝ≥0` operator-norm bound
`‖A t‖₊ ≤ max 1 C` for the pair coefficient, as required by the first-order
theory. -/
theorem nnnorm_jacobiPairCoeff_le {R : ℝ → F →L[ℝ] F} {a b C : ℝ}
    (hC : ∀ t ∈ Icc a b, ‖R t‖ ≤ C) :
    ∀ t ∈ Icc a b, ‖jacobiPairCoeff R t‖₊ ≤
      ⟨max 1 C, le_trans zero_le_one (le_max_left _ _)⟩ := by
  intro t ht
  have h : ‖jacobiPairCoeff R t‖ ≤ max 1 C :=
    (norm_jacobiPairCoeff_le R t).trans (max_le_max le_rfl (hC t ht))
  rwa [← NNReal.coe_le_coe, coe_nnnorm]

/-- **Math.** **Global existence** for the Jacobi-type equation
`y'' + R(t) y = 0` on a compact interval: for every initial position `y₀` and
initial velocity `v₀` there is a solution on `[a, b]` with `y a = y₀`,
`v a = v₀`. Reduction to the first-order linear system on `F × F` and
`Riemannian.LinearODE.exists_hasDerivWithinAt_Icc`.

Blueprint: `lem:second-order-linear-ode` (existence half). -/
theorem exists_isJacobiSolOn_Icc {a b : ℝ} (hab : a ≤ b) (R : ℝ → F →L[ℝ] F)
    (hR : ContinuousOn R (Icc a b)) (y₀ v₀ : F) :
    ∃ y v : ℝ → F, y a = y₀ ∧ v a = v₀ ∧ IsJacobiSolOn R a b y v := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hR
  have hKb := nnnorm_jacobiPairCoeff_le hC
  have hcont := continuousOn_jacobiPairCoeff (F := F) hR
  obtain ⟨W, hWa, hW⟩ := Riemannian.LinearODE.exists_hasDerivWithinAt_Icc hab
    (jacobiPairCoeff R) (y₀, v₀) hcont hKb
  exact ⟨fun t => (W t).1, fun t => (W t).2,
    show (W a).1 = y₀ by rw [hWa],
    show (W a).2 = v₀ by rw [hWa],
    isJacobiSolOn_of_isSolOn hW⟩

namespace IsJacobiSolOn

variable {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}

/-- **Math.** **Forward uniqueness**: two solutions with the same initial
position and velocity at `a` agree on `[a, b]` (Grönwall for the pair system).

Blueprint: `lem:second-order-linear-ode` (uniqueness half). -/
theorem eqOn_of_left (hR : ContinuousOn R (Icc a b))
    (h₁ : IsJacobiSolOn R a b y v) (h₂ : IsJacobiSolOn R a b z w)
    (hy : y a = z a) (hv : v a = w a) :
    EqOn y z (Icc a b) ∧ EqOn v w (Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hR
  have hKb := nnnorm_jacobiPairCoeff_le hC
  have h1 := h₁.isSolOn_pair
  have h2 := h₂.isSolOn_pair
  have hpair := Riemannian.LinearODE.IsSolOn.eqOn_of_left hKb h1 h2
    (show (y a, v a) = (z a, w a) by rw [hy, hv])
  exact ⟨fun t ht => congrArg Prod.fst (hpair ht),
    fun t ht => congrArg Prod.snd (hpair ht)⟩

/-- **Math.** **Backward uniqueness**: two solutions with the same position and
velocity at the right endpoint `b` agree on `[a, b]` (time-reversed Grönwall).

Blueprint: `lem:second-order-linear-ode` (uniqueness half). -/
theorem eqOn_of_right (hR : ContinuousOn R (Icc a b))
    (h₁ : IsJacobiSolOn R a b y v) (h₂ : IsJacobiSolOn R a b z w)
    (hy : y b = z b) (hv : v b = w b) :
    EqOn y z (Icc a b) ∧ EqOn v w (Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hR
  have hKb := nnnorm_jacobiPairCoeff_le hC
  have h1 := h₁.isSolOn_pair
  have h2 := h₂.isSolOn_pair
  have hpair := Riemannian.LinearODE.IsSolOn.eqOn_of_right hKb h1 h2
    (show (y b, v b) = (z b, w b) by rw [hy, hv])
  exact ⟨fun t ht => congrArg Prod.fst (hpair ht),
    fun t ht => congrArg Prod.snd (hpair ht)⟩

/-- **Math.** Superposition: the sum of two solutions is a solution. -/
theorem add (h₁ : IsJacobiSolOn R a b y v) (h₂ : IsJacobiSolOn R a b z w) :
    IsJacobiSolOn R a b (y + z) (v + w) where
  hasDerivWithinAt_fst t ht := by
    simpa using (h₁.hasDerivWithinAt_fst t ht).add (h₂.hasDerivWithinAt_fst t ht)
  hasDerivWithinAt_snd t ht := by
    have h := (h₁.hasDerivWithinAt_snd t ht).add (h₂.hasDerivWithinAt_snd t ht)
    have heq : -(R t) ((y + z) t) = -(R t) (y t) + -(R t) (z t) := by
      rw [Pi.add_apply, map_add, neg_add]
    rw [heq]
    exact h

/-- **Math.** Superposition: a scalar multiple of a solution is a solution. -/
theorem const_smul (c : ℝ) (h : IsJacobiSolOn R a b y v) :
    IsJacobiSolOn R a b (c • y) (c • v) where
  hasDerivWithinAt_fst t ht := by
    simpa using (h.hasDerivWithinAt_fst t ht).const_smul c
  hasDerivWithinAt_snd t ht := by
    have := (h.hasDerivWithinAt_snd t ht).const_smul c
    simpa [smul_neg] using this

/-- **Math.** Superposition: the difference of two solutions is a solution. -/
theorem sub (h₁ : IsJacobiSolOn R a b y v) (h₂ : IsJacobiSolOn R a b z w) :
    IsJacobiSolOn R a b (y - z) (v - w) := by
  have := h₁.add (h₂.const_smul (-1))
  simpa [sub_eq_add_neg, neg_one_smul] using this

end IsJacobiSolOn

/-- **Math.** The zero pair is a solution. -/
theorem isJacobiSolOn_zero (R : ℝ → F →L[ℝ] F) (a b : ℝ) :
    IsJacobiSolOn R a b 0 0 where
  hasDerivWithinAt_fst t _ := by
    simpa using (hasDerivWithinAt_const t (Icc a b) (0 : F))
  hasDerivWithinAt_snd t _ := by
    simpa using (hasDerivWithinAt_const t (Icc a b) (0 : F))

namespace IsJacobiSolOn

variable {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v : ℝ → F}

/-- **Math.** A solution whose position and velocity both vanish at `a`
vanishes identically on `[a, b]`. In particular a not-identically-zero solution
has `(y a, v a) ≠ 0`; contrapositively, a Jacobi field with nontrivial data is
nonzero. Blueprint: `lem:second-order-linear-ode`. -/
theorem eqOn_zero (hR : ContinuousOn R (Icc a b)) (h : IsJacobiSolOn R a b y v)
    (hy0 : y a = 0) (hv0 : v a = 0) :
    EqOn y 0 (Icc a b) ∧ EqOn v 0 (Icc a b) :=
  h.eqOn_of_left hR (isJacobiSolOn_zero R a b) (by simpa using hy0)
    (by simpa using hv0)

/-! ### The Grönwall a-priori bound and small-time asymptotics -/

/-- **Math.** **Grönwall bound.** If `‖R‖ ≤ C` on `[a, b]` then, with
`K = max 1 C` (an operator-norm bound for the pair coefficient in the sup
norm), `max ‖y t‖ ‖v t‖ ≤ max ‖y a‖ ‖v a‖ · e^{K (t − a)}` on `[a, b]`.

Blueprint: `lem:jacobi-small-time`. -/
theorem max_norm_le {C : ℝ} (h : IsJacobiSolOn R a b y v)
    (hC : ∀ t ∈ Icc a b, ‖R t‖ ≤ C) :
    ∀ t ∈ Icc a b,
      max ‖y t‖ ‖v t‖ ≤ max ‖y a‖ ‖v a‖ * Real.exp (max 1 C * (t - a)) := by
  intro t ht
  set f : ℝ → F × F := fun s => (y s, v s) with hf
  have hcont : ContinuousOn f (Icc a b) := h.isSolOn_pair.continuousOn
  have hderiv : ∀ x ∈ Ico a b,
      HasDerivWithinAt f (jacobiPairCoeff R x (f x)) (Ici x) x := fun x hx =>
    (h.isSolOn_pair x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (Riemannian.LinearODE.Icc_mem_nhdsWithin_Ici hx)
  have hbound : ∀ x ∈ Ico a b,
      ‖jacobiPairCoeff R x (f x)‖ ≤ max 1 C * ‖f x‖ + 0 := by
    intro x hx
    rw [add_zero]
    calc ‖jacobiPairCoeff R x (f x)‖ ≤ ‖jacobiPairCoeff R x‖ * ‖f x‖ :=
          (jacobiPairCoeff R x).le_opNorm _
      _ ≤ max 1 C * ‖f x‖ :=
          mul_le_mul_of_nonneg_right
            ((norm_jacobiPairCoeff_le R x).trans
              (max_le_max le_rfl (hC x (Ico_subset_Icc_self hx))))
            (norm_nonneg _)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv
    (le_refl ‖f a‖) hbound t ht
  rw [gronwallBound_ε0] at hg
  simpa [hf, Prod.norm_def] using hg

end IsJacobiSolOn

/-- **Math.** Fundamental theorem of calculus along an `Icc`-differentiable
curve: for `t ∈ [a, b]`, `f t − f a = ∫_a^t f'`. -/
theorem sub_eq_integral_of_hasDerivWithinAt_Icc {a b : ℝ} {f f' : ℝ → F}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t)
    (hf' : ContinuousOn f' (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b) :
    f t - f a = ∫ s in a..t, f' s := by
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn f (Icc a t) :=
    fun s hs => ((hf s (hsub hs)).continuousWithinAt).mono hsub
  have hderiv : ∀ x ∈ Ioo a t, HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    have hx' : x ∈ Ico a b := ⟨hx.1.le, lt_of_lt_of_le hx.2 ht.2⟩
    exact ((hf x (Ico_subset_Icc_self hx')).mono_of_mem_nhdsWithin
      (Riemannian.LinearODE.Icc_mem_nhdsWithin_Ici hx')).mono Ioi_subset_Ici_self
  have hint : IntervalIntegrable f' MeasureTheory.volume a t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hf'.mono hsub
  exact (integral_eq_sub_of_hasDeriv_right_of_le ht.1 hcont hderiv hint).symm

namespace IsJacobiSolOn

variable {R : ℝ → F →L[ℝ] F} {b C : ℝ} {y v : ℝ → F}

/-- **Math.** Small-time bound, velocity: for a solution on `[0, b]` starting
at `y 0 = 0`, `‖v t‖ ≤ ‖v 0‖ · e^{K b} =: M` for all `t ∈ [0, b]`, where
`K = max 1 C`. Blueprint: `lem:jacobi-small-time`. -/
theorem norm_snd_le (h : IsJacobiSolOn R 0 b y v)
    (hC : ∀ t ∈ Icc 0 b, ‖R t‖ ≤ C) (hy0 : y 0 = 0) :
    ∀ t ∈ Icc 0 b, ‖v t‖ ≤ ‖v 0‖ * Real.exp (max 1 C * b) := by
  intro t ht
  have hK0 : (0 : ℝ) ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  have h1 := h.max_norm_le hC t ht
  rw [hy0] at h1
  have h2 : max ‖(0 : F)‖ ‖v 0‖ = ‖v 0‖ := by
    simp
  rw [h2, sub_zero] at h1
  calc ‖v t‖ ≤ max ‖y t‖ ‖v t‖ := le_max_right _ _
    _ ≤ ‖v 0‖ * Real.exp (max 1 C * t) := h1
    _ ≤ ‖v 0‖ * Real.exp (max 1 C * b) := by
        have := mul_le_mul_of_nonneg_left ht.2 hK0
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) (norm_nonneg _)

/-- **Math.** Small-time bound, position: for a solution on `[0, b]` with
`y 0 = 0`, `‖y t‖ ≤ M t` where `M = ‖v 0‖ e^{Kb}`, `K = max 1 C` — the
position grows at most linearly, at the a-priori velocity scale. From
`y t = ∫_0^t v`. Blueprint: `lem:jacobi-small-time`. -/
theorem norm_fst_le (h : IsJacobiSolOn R 0 b y v)
    (hC : ∀ t ∈ Icc 0 b, ‖R t‖ ≤ C) (hy0 : y 0 = 0) :
    ∀ t ∈ Icc 0 b, ‖y t‖ ≤ (‖v 0‖ * Real.exp (max 1 C * b)) * t := by
  intro t ht
  have key := sub_eq_integral_of_hasDerivWithinAt_Icc h.hasDerivWithinAt_fst
    h.continuousOn_snd ht
  rw [hy0, sub_zero] at key
  rw [key]
  have hbound : ∀ x ∈ Ι (0 : ℝ) t, ‖v x‖ ≤ ‖v 0‖ * Real.exp (max 1 C * b) := by
    intro x hx
    rw [uIoc_of_le ht.1] at hx
    exact h.norm_snd_le hC hy0 x ⟨hx.1.le, hx.2.trans ht.2⟩
  have := norm_integral_le_of_norm_le_const hbound
  rwa [sub_zero, abs_of_nonneg ht.1] at this

/-- **Math.** Small-time asymptotics, velocity: `‖v t − v 0‖ ≤ C M t²/2` with
`M = ‖v 0‖ e^{Kb}`, `K = max 1 C`. From `v t − v 0 = −∫_0^t R y` and the
linear position bound. This is the `𝒥'(r) = Id + O(r²)` estimate of
`lem:geodesic-polar-form`(3). Blueprint: `lem:jacobi-small-time`. -/
theorem norm_snd_sub_le (h : IsJacobiSolOn R 0 b y v)
    (hR : ContinuousOn R (Icc 0 b)) (hC : ∀ t ∈ Icc 0 b, ‖R t‖ ≤ C)
    (hy0 : y 0 = 0) :
    ∀ t ∈ Icc 0 b, ‖v t - v 0‖ ≤
      C * (‖v 0‖ * Real.exp (max 1 C * b)) * t ^ 2 / 2 := by
  intro t ht
  have hC0 : (0 : ℝ) ≤ C := (norm_nonneg (R 0)).trans (hC 0 ⟨le_rfl, ht.1.trans ht.2⟩)
  set M : ℝ := ‖v 0‖ * Real.exp (max 1 C * b) with hM
  have hM0 : (0 : ℝ) ≤ M := mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
  have hRy_cont : ContinuousOn (fun s => -(R s) (y s)) (Icc 0 b) :=
    (hR.clm_apply h.continuousOn_fst).neg
  have key := sub_eq_integral_of_hasDerivWithinAt_Icc h.hasDerivWithinAt_snd
    hRy_cont ht
  rw [key]
  have hsub : Icc 0 t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
  have hint₁ : IntervalIntegrable (fun s => ‖-(R s) (y s)‖)
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact (hRy_cont.mono hsub).norm
  have hint₂ : IntervalIntegrable (fun s => C * M * s) MeasureTheory.volume 0 t :=
    (intervalIntegrable_id).const_mul _
  calc ‖∫ s in (0:ℝ)..t, -(R s) (y s)‖
      ≤ ∫ s in (0:ℝ)..t, ‖-(R s) (y s)‖ :=
        norm_integral_le_integral_norm ht.1
    _ ≤ ∫ s in (0:ℝ)..t, C * M * s := by
        apply integral_mono_on ht.1 hint₁ hint₂
        intro s hs
        have hs' : s ∈ Icc 0 b := hsub hs
        rw [norm_neg]
        calc ‖(R s) (y s)‖ ≤ ‖R s‖ * ‖y s‖ := (R s).le_opNorm _
          _ ≤ C * (M * s) :=
              mul_le_mul (hC s hs') (h.norm_fst_le hC hy0 s hs')
                (norm_nonneg _) hC0
          _ = C * M * s := by ring
    _ = C * M * t ^ 2 / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring

/-- **Math.** Small-time asymptotics, position: `‖y t − t • v 0‖ ≤ C M t³/6`
with `M = ‖v 0‖ e^{Kb}`, `K = max 1 C`. From
`y t − t v 0 = ∫_0^t (v − v 0)` and the quadratic velocity estimate. This is
the `𝒥(r) = r·Id + O(r³)` estimate of `lem:geodesic-polar-form`(3).
Blueprint: `lem:jacobi-small-time`. -/
theorem norm_fst_sub_le (h : IsJacobiSolOn R 0 b y v)
    (hR : ContinuousOn R (Icc 0 b)) (hC : ∀ t ∈ Icc 0 b, ‖R t‖ ≤ C)
    (hy0 : y 0 = 0) :
    ∀ t ∈ Icc 0 b, ‖y t - t • v 0‖ ≤
      C * (‖v 0‖ * Real.exp (max 1 C * b)) * t ^ 3 / 6 := by
  intro t ht
  have hC0 : (0 : ℝ) ≤ C := (norm_nonneg (R 0)).trans (hC 0 ⟨le_rfl, ht.1.trans ht.2⟩)
  set M : ℝ := ‖v 0‖ * Real.exp (max 1 C * b) with hM
  have hM0 : (0 : ℝ) ≤ M := mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
  have hz : ∀ s ∈ Icc (0:ℝ) b,
      HasDerivWithinAt (fun τ => y τ - τ • v 0) (v s - v 0) (Icc 0 b) s := by
    intro s hs
    have hsm : HasDerivWithinAt (fun τ : ℝ => τ • v 0) (v 0) (Icc 0 b) s := by
      simpa using ((hasDerivAt_id s).smul_const (v 0)).hasDerivWithinAt
    exact (h.hasDerivWithinAt_fst s hs).sub hsm
  have hcont : ContinuousOn (fun s => v s - v 0) (Icc 0 b) :=
    h.continuousOn_snd.sub continuousOn_const
  have key := sub_eq_integral_of_hasDerivWithinAt_Icc hz hcont ht
  rw [hy0] at key
  simp only [zero_smul, sub_zero] at key
  rw [key]
  have hsub : Icc 0 t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
  have hint₁ : IntervalIntegrable (fun s => ‖v s - v 0‖)
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact (hcont.mono hsub).norm
  have hint₂ : IntervalIntegrable (fun s => C * M * s ^ 2 / 2)
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    exact (Continuous.continuousOn (by fun_prop))
  calc ‖∫ s in (0:ℝ)..t, (v s - v 0)‖
      ≤ ∫ s in (0:ℝ)..t, ‖v s - v 0‖ := norm_integral_le_integral_norm ht.1
    _ ≤ ∫ s in (0:ℝ)..t, C * M * s ^ 2 / 2 := by
        apply integral_mono_on ht.1 hint₁ hint₂
        intro s hs
        exact h.norm_snd_sub_le hR hC hy0 s (hsub hs)
    _ = C * M * t ^ 3 / 6 := by
        have : ∀ s : ℝ, C * M * s ^ 2 / 2 = (C * M / 2) * s ^ 2 := fun s => by ring
        simp_rw [this]
        rw [intervalIntegral.integral_const_mul, integral_pow]
        norm_num
        ring

end IsJacobiSolOn

end MorganTianLib

end
