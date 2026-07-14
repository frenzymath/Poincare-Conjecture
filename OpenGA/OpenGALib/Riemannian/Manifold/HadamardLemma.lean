import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Hadamard's lemma (do Carmo Ch.0, Lem. 5.5)

A differentiable function vanishing at the origin of its first variable factors,
smoothly in the remaining variables, as that variable times a differentiable
remainder: if `h : ℝ × U → F` is differentiable with `h 0 q = 0`, then
`h t q = t • g t q` for a differentiable `g` with `g 0 q = ∂ₜ h 0 q`.

Mathlib has no packaged Hadamard lemma; this file supplies it as reusable
project-local infrastructure.  The factoring identity is the fundamental theorem
of calculus after the substitution `u = s t`; the explicit remainder is
`g t q = ∫₀¹ (∂ₜ h)(s t) q ds`.

This is the analytic content behind `prop:dc-ch0-5-4` (bracket as Lie derivative
along the flow).
-/

open scoped ContDiff
open intervalIntegral MeasureTheory

namespace Riemannian.Hadamard

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Hadamard factoring, one-variable core.**  If `h : ℝ → F` is everywhere
differentiable with continuous derivative and `h 0 = 0`, then
`h t = t • ∫₀¹ h'(s t) ds`.  This is the fundamental theorem of calculus after
the substitution `u = s t`. -/
theorem eq_smul_integral_deriv {h h' : ℝ → F}
    (hderiv : ∀ x, HasDerivAt h (h' x) x) (hcont : Continuous h') (h0 : h 0 = 0) (t : ℝ) :
    h t = t • ∫ s in (0:ℝ)..1, h' (s * t) := by
  have key := integral_unitInterval_deriv_eq_sub (f := h) (f' := h') (z₀ := (0:ℝ)) (z₁ := t)
    (by
      simp only [zero_add, smul_eq_mul]
      exact (hcont.comp (by fun_prop)).continuousOn)
    (by intro s _; simpa using hderiv (s * t))
  simp only [zero_add, smul_eq_mul, h0, sub_zero] at key
  simpa [smul_eq_mul] using key.symm

/-- The Hadamard remainder at `t = 0` is the derivative of `h` at `0`. -/
theorem integral_deriv_at_zero {h' : ℝ → F} :
    (∫ s in (0:ℝ)..1, h' (s * 0)) = h' 0 := by
  simp

/-! ### Parametric Hadamard lemma

Now `h : ℝ → E → F`, differentiable in its first variable with `t`-partial `pd`,
and `h 0 q = 0` for all `q`.  The remainder `g t q = ∫₀¹ pd (s t) q ds` satisfies
`h t q = t • g t q`, `g 0 q = pd 0 q`, and (when `pd` is jointly continuous) `g`
is jointly continuous. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **Hadamard remainder** of a function `h : ℝ → E → F` whose first-variable
partial derivative is `pd`: `g t q = ∫₀¹ pd (s t) q ds`. -/
noncomputable def remainder (pd : ℝ → E → F) (t : ℝ) (q : E) : F := ∫ s in (0:ℝ)..1, pd (s * t) q

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- **Parametric Hadamard factoring.**  If `u ↦ h u q` is differentiable with
continuous derivative `u ↦ pd u q` and `h 0 q = 0`, then `h t q = t • g t q` with
`g` the Hadamard remainder. -/
theorem eq_smul_remainder {h : ℝ → E → F} {pd : ℝ → E → F}
    (hderiv : ∀ q u, HasDerivAt (fun u => h u q) (pd u q) u)
    (hcont : ∀ q, Continuous fun u => pd u q) (h0 : ∀ q, h 0 q = 0) (t : ℝ) (q : E) :
    h t q = t • remainder pd t q := by
  simpa [remainder] using
    eq_smul_integral_deriv (h := fun u => h u q) (h' := fun u => pd u q)
      (hderiv q) (hcont q) (h0 q) t

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The Hadamard remainder at `t = 0` is the first-variable partial derivative at `0`,
recovering `g 0 q = (Xf) q` in do Carmo's application. -/
@[simp] theorem remainder_zero (pd : ℝ → E → F) (q : E) : remainder pd 0 q = pd 0 q := by
  simp [remainder]

omit [CompleteSpace F] [NormedSpace ℝ E] in
/-- **Joint continuity of the Hadamard remainder.**  If the first-variable partial
derivative `pd` is jointly continuous, so is the remainder `g`. -/
theorem continuous_remainder {pd : ℝ → E → F} (hpd : Continuous (Function.uncurry pd)) :
    Continuous (Function.uncurry (remainder pd)) := by
  have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) (f := fun (x : ℝ × E) (s : ℝ) => pd (s * x.1) x.2)
    (by
      have hmul : Continuous fun p : (ℝ × E) × ℝ => p.2 * p.1.1 := by fun_prop
      exact hpd.comp (hmul.prodMk (by fun_prop))) 0 1
  simpa [Function.uncurry, remainder] using this

/-! ### Joint differentiability of the Hadamard remainder

The factoring and continuity above hold with no regularity beyond a continuous
first-variable partial.  For joint *differentiability* of the remainder we use
differentiation under the integral sign, which asks for a `C¹` integrand.  There
is no packaged "`C¹`-under-the-integral" lemma in Mathlib, but the pointwise
Fréchet-derivative version `hasFDerivAt_integral_of_dominated_of_fderiv_le''` is
available, and the domination bound follows from continuity of `fderiv` on the
compact set swept by `s ∈ [0,1]` and the parameter `x` in a closed ball — hence
the finite-dimensionality hypothesis on the parameter space `E`, matching do
Carmo's `U ⊆ ℝⁿ`. -/

/-- The linear reparametrization `x = (t, q) ↦ (s·t, q)` on `ℝ × E`, through which
the Hadamard integrand factors: `pd (s * x.1) x.2 = (uncurry pd) (hadamardScale s x)`. -/
noncomputable def hadamardScale (s : ℝ) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  ((0 : (ℝ × E) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ E)) +
    s • ((ContinuousLinearMap.fst ℝ ℝ E).prod (0 : (ℝ × E) →L[ℝ] E))

@[simp] lemma hadamardScale_apply (s : ℝ) (x : ℝ × E) :
    hadamardScale s x = (s * x.1, x.2) := by
  simp [hadamardScale, Prod.smul_mk, smul_eq_mul]

lemma continuous_hadamardScale : Continuous (hadamardScale (E := E)) := by
  unfold hadamardScale
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- On `s ∈ [0,1]` the reparametrization is nonexpansive: `‖hadamardScale s‖ ≤ 1`. -/
lemma hadamardScale_opNorm_le {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    ‖hadamardScale (E := E) s‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [hadamardScale_apply, one_mul]
  have hs' : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  simp only [Prod.norm_def, Real.norm_eq_abs, abs_mul]
  apply max_le
  · calc |s| * |x.1| ≤ 1 * |x.1| := by gcongr
      _ = |x.1| := one_mul _
      _ ≤ max |x.1| ‖x.2‖ := le_max_left _ _
  · exact le_max_right _ _

omit [CompleteSpace F] in
/-- **Joint differentiability of the Hadamard remainder.**  If the first-variable
partial derivative `pd` is `C¹` jointly (as the uncurried map on `ℝ × E`, with `E`
finite dimensional), then the Hadamard remainder `g t q = ∫₀¹ pd (s t) q ds` is
differentiable in `(t, q)`.  This closes the differentiability content of do
Carmo's Hadamard lemma (Ch. 0, Lem. 5.5). -/
theorem differentiable_remainder [FiniteDimensional ℝ E] {pd : ℝ → E → F}
    (hpd : ContDiff ℝ 1 (Function.uncurry pd)) :
    Differentiable ℝ (Function.uncurry (remainder pd)) := by
  set g : ℝ × E → F := Function.uncurry pd with hg_def
  have hg_cont : Continuous g := hpd.continuous
  have hg_diff : Differentiable ℝ g := hpd.differentiable one_ne_zero
  have hg_fderiv : Continuous (fun p => fderiv ℝ g p) := hpd.continuous_fderiv one_ne_zero
  -- continuity of the evaluated reparametrization `(s, x) ↦ hadamardScale s x`
  have hscale_eval : Continuous fun p : ℝ × (ℝ × E) => hadamardScale p.1 p.2 := by
    simp only [hadamardScale_apply]
    fun_prop
  intro x₀
  -- the compact parameter region and the derivative-norm bound on it
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
    (f := fun p : ℝ × (ℝ × E) => fderiv ℝ g (hadamardScale p.1 p.2))
    ((hg_fderiv.comp hscale_eval).continuousOn)
  have key : HasFDerivAt (fun x : ℝ × E => ∫ s in (0:ℝ)..1, g (hadamardScale s x))
      (∫ s in (0:ℝ)..1, (fderiv ℝ g (hadamardScale s x₀)).comp (hadamardScale s)) x₀ := by
    have hscale_x : ∀ x : ℝ × E, Continuous fun s : ℝ => hadamardScale s x := fun x =>
      hscale_eval.comp (continuous_id.prodMk continuous_const)
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (bound := fun _ => C)
      (F' := fun x s => (fderiv ℝ g (hadamardScale s x)).comp (hadamardScale s))
      (Metric.closedBall_mem_nhds x₀ one_pos)
    · exact Filter.Eventually.of_forall fun x =>
        (hg_cont.comp (hscale_x x)).aestronglyMeasurable
    · exact (hg_cont.comp (hscale_x x₀)).intervalIntegrable 0 1
    · exact ((hg_fderiv.comp (hscale_x x₀)).clm_comp
        (continuous_hadamardScale (E := E))).aestronglyMeasurable
    · -- domination bound `‖F' x s‖ ≤ C` for `s ∈ Ι 0 1`, `x ∈ closedBall x₀ 1`
      apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
      intro s hs x hx
      have hs' : s ∈ Set.Icc (0:ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at hs
        exact Set.Ioc_subset_Icc_self hs
      have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC (s, x) ⟨hs', hx⟩)
      calc ‖(fderiv ℝ g (hadamardScale s x)).comp (hadamardScale (E := E) s)‖
          ≤ ‖fderiv ℝ g (hadamardScale s x)‖ * ‖hadamardScale (E := E) s‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ C * 1 := mul_le_mul (hC (s, x) ⟨hs', hx⟩) (hadamardScale_opNorm_le hs')
            (norm_nonneg _) hCnn
        _ = C := mul_one C
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun s x _ => ?_
      exact (hg_diff (hadamardScale s x)).hasFDerivAt.comp x
        (hadamardScale (E := E) s).hasFDerivAt
  -- transport back to `Function.uncurry (remainder pd)`
  have hfun : (fun x : ℝ × E => ∫ s in (0:ℝ)..1, g (hadamardScale s x))
      = Function.uncurry (remainder pd) := by
    funext x
    simp only [hadamardScale_apply, Function.uncurry, remainder, hg_def]
  rw [← hfun]
  exact key.differentiableAt

end Riemannian.Hadamard
