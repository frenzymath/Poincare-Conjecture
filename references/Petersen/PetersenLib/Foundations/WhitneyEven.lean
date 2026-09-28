import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Whitney's even-function theorem

A smooth even function `f : ℝ → ℝ` factors as `f t = g (t ^ 2)` with `g` smooth on `[0, ∞)`
(Whitney, *Differentiable even functions*, Duke Math. J. 10 (1943)).

This is the analytic heart of the smoothness criterion for rotationally symmetric metrics
(Petersen, *Riemannian Geometry*, Ch. 1): a rotationally symmetric expression `φ(r²)` is smooth
across the axis iff the profile function is smooth and even in `r`.

## Main results

* `PetersenLib.hadamardDiv`: the Hadamard quotient `t ↦ ∫ s in 0..1, f' (t*s)`,
  so that `f t - f 0 = t * hadamardDiv f t`.
* `PetersenLib.contDiffOn_comp_sqrt_of_stable`: the core induction. If a predicate `P` on
  functions implies smoothness and is stable under "divide the derivative by `2t`", then
  `s ↦ f (√s)` is smooth on `[0, ∞)` for every `f` with `P f`.
* `PetersenLib.contDiffOn_comp_sqrt_of_even`, `PetersenLib.whitney_even`,
  `PetersenLib.contDiff_even_comp_norm`: Whitney's theorem for even functions.
* `PetersenLib.contDiffOn_comp_sqrt_of_flat`, `PetersenLib.contDiff_flat_comp_norm`:
  the analogue for functions flat at `0` (all iterated derivatives vanish).
-/

open Set Filter MeasureTheory intervalIntegral
open scoped Topology ContDiff Interval

namespace PetersenLib

/-- The Hadamard quotient of `f`: `hadamardDiv f t = ∫ s in 0..1, f' (t s) ds`.
For smooth `f` it satisfies `f t - f 0 = t * hadamardDiv f t`. -/
noncomputable def hadamardDiv (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, deriv f (t * s)

section ParametricIntegral

variable {w ξ f : ℝ → ℝ}

/-- Continuity of the weighted parametric integral `t ↦ ∫ s in 0..1, w s * ξ (t s)`. -/
lemma continuous_parametricHadamard (hw : Continuous w) (hξ : Continuous ξ) :
    Continuous fun t : ℝ => ∫ s in (0 : ℝ)..1, w s * ξ (t * s) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hw.comp continuous_snd).mul (hξ.comp (continuous_fst.mul continuous_snd))

/-- Differentiation under the integral sign for `t ↦ ∫ s in 0..1, w s * ξ (t s)`. -/
lemma hasDerivAt_parametricHadamard (hw : Continuous w) (hξ : ContDiff ℝ 1 ξ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ s in (0 : ℝ)..1, w s * ξ (t * s))
      (∫ s in (0 : ℝ)..1, w s * s * deriv ξ (t₀ * s)) t₀ := by
  have hξc : Continuous ξ := hξ.continuous
  have hξd : Continuous (deriv ξ) := hξ.continuous_deriv le_rfl
  have hξdiff : Differentiable ℝ ξ := hξ.differentiable one_ne_zero
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ Icc (t₀ - 1) (t₀ + 1) ×ˢ Icc (0 : ℝ) 1,
      ‖w p.2 * p.2 * deriv ξ (p.1 * p.2)‖ ≤ C :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (((hw.comp continuous_snd).mul continuous_snd).mul
        (hξd.comp (continuous_fst.mul continuous_snd))).continuousOn
  have h_bound : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0 : ℝ) 1 →
      ∀ x ∈ Metric.ball t₀ 1, ‖w s * s * deriv ξ (x * s)‖ ≤ C := by
    refine Eventually.of_forall fun s hs x hx => hC (x, s) (Set.mem_prod.mpr ⟨?_, ?_⟩)
    · exact Set.Ioo_subset_Icc_self (by rwa [Real.ball_eq_Ioo] at hx)
    · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      exact ⟨hs.1.le, hs.2⟩
  have h_diff : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0 : ℝ) 1 →
      ∀ x ∈ Metric.ball t₀ 1,
        HasDerivAt (fun t => w s * ξ (t * s)) (w s * s * deriv ξ (x * s)) x := by
    refine Eventually.of_forall fun s _hs x _hx => ?_
    have h1 : HasDerivAt (fun y : ℝ => y * s) s x := hasDerivAt_mul_const s
    have h2 : HasDerivAt ξ (deriv ξ (x * s)) (x * s) := (hξdiff (x * s)).hasDerivAt
    have h4 : HasDerivAt (fun y : ℝ => w s * ξ (y * s)) (w s * (deriv ξ (x * s) * s)) x :=
      (h2.comp x h1).const_mul (w s)
    convert h4 using 1
    ring
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t s => w s * ξ (t * s)) (F' := fun t s => w s * s * deriv ξ (t * s))
    (x₀ := t₀) (bound := fun _ => C) (Metric.ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t =>
      ((hw.mul (hξc.comp (continuous_const.mul continuous_id))).aestronglyMeasurable))
    ((hw.mul (hξc.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 1)
    ((hw.mul continuous_id).mul
      (hξd.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    h_bound intervalIntegrable_const h_diff
  exact key.2

/-- Derivative of the weighted parametric integral, as a function. -/
lemma deriv_parametricHadamard (hw : Continuous w) (hξ : ContDiff ℝ 1 ξ) :
    deriv (fun t : ℝ => ∫ s in (0 : ℝ)..1, w s * ξ (t * s))
      = fun t => ∫ s in (0 : ℝ)..1, w s * s * deriv ξ (t * s) :=
  funext fun t => (hasDerivAt_parametricHadamard hw hξ t).deriv

/-- Smoothness (of any finite order) of the weighted parametric integral. -/
lemma contDiff_parametricHadamard (n : ℕ) :
    ∀ {w ξ : ℝ → ℝ}, Continuous w → ContDiff ℝ n ξ →
      ContDiff ℝ n fun t : ℝ => ∫ s in (0 : ℝ)..1, w s * ξ (t * s) := by
  induction n with
  | zero =>
    intro w ξ hw hξ
    rw [Nat.cast_zero, contDiff_zero] at hξ ⊢
    exact continuous_parametricHadamard hw hξ
  | succ n ih =>
    intro w ξ hw hξ
    rw [Nat.cast_succ] at hξ ⊢
    have hξ1 : ContDiff ℝ 1 ξ := hξ.of_le le_add_self
    rw [contDiff_succ_iff_deriv] at hξ ⊢
    refine ⟨fun t => (hasDerivAt_parametricHadamard hw hξ1 t).differentiableAt, ?_, ?_⟩
    · intro h
      exact absurd h (by simp)
    · rw [deriv_parametricHadamard hw hξ1]
      exact ih (hw.mul continuous_id) hξ.2.2

/-- Smoothness of the weighted parametric integral. -/
lemma contDiff_top_parametricHadamard (hw : Continuous w) (hξ : ContDiff ℝ ∞ ξ) :
    ContDiff ℝ ∞ fun t : ℝ => ∫ s in (0 : ℝ)..1, w s * ξ (t * s) :=
  contDiff_infty.mpr fun n => contDiff_parametricHadamard n hw (contDiff_infty.mp hξ n)

end ParametricIntegral

section HadamardDiv

variable {f : ℝ → ℝ}

/-- The Hadamard quotient of a smooth function is smooth. -/
lemma contDiff_hadamardDiv (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (hadamardDiv f) := by
  have h := contDiff_top_parametricHadamard (w := fun _ => (1 : ℝ)) continuous_const
    ((contDiff_infty_iff_deriv.mp hf).2)
  have he : hadamardDiv f = fun t => ∫ s in (0 : ℝ)..1, (1 : ℝ) * deriv f (t * s) := by
    funext t
    simp [hadamardDiv]
  rw [he]
  exact h

/-- Fundamental theorem of calculus for the Hadamard quotient:
`f t - f 0 = t * hadamardDiv f t`. -/
lemma sub_eq_mul_hadamardDiv (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    f t - f 0 = t * hadamardDiv f t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have hf1 : ContDiff ℝ 1 f := hf.of_le (mod_cast le_top)
    have hd : Continuous (deriv f) := hf1.continuous_deriv le_rfl
    have hsub : ∫ u in (0 : ℝ)..t, deriv f u = f t - f 0 :=
      intervalIntegral.integral_deriv_eq_sub
        (fun x _ => (hf1.differentiable one_ne_zero).differentiableAt)
        (hd.intervalIntegrable 0 t)
    have hcomp : ∫ s in (0 : ℝ)..1, deriv f (t * s)
        = t⁻¹ • ∫ u in t * 0..t * 1, deriv f u :=
      intervalIntegral.integral_comp_mul_left (deriv f) ht
    show f t - f 0 = t * ∫ s in (0 : ℝ)..1, deriv f (t * s)
    rw [hcomp, mul_zero, mul_one, hsub, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]

/-- The derivative of an even function is odd. -/
lemma deriv_odd_of_even (heven : ∀ t, f (-t) = f t) (t : ℝ) :
    deriv f (-t) = -deriv f t := by
  have h : (fun x => f (-x)) = f := funext heven
  have h1 := deriv_comp_neg f t
  rw [h] at h1
  linarith

/-- The derivative of an odd function is even. -/
lemma deriv_even_of_odd (hodd : ∀ t, f (-t) = -f t) (t : ℝ) :
    deriv f (-t) = deriv f t := by
  have h : (fun x => f (-x)) = -f := funext fun x => (hodd x).trans (Pi.neg_apply f x).symm
  have h1 := deriv_comp_neg f t
  rw [h, deriv.neg] at h1
  linarith

/-- An odd function vanishes at `0`. -/
lemma eq_zero_of_odd (hodd : ∀ t, f (-t) = -f t) : f 0 = 0 := by
  have h := hodd 0
  rw [neg_zero] at h
  linarith

/-- The Hadamard quotient of an even function is odd. -/
lemma hadamardDiv_odd_of_even (heven : ∀ t, f (-t) = f t) (t : ℝ) :
    hadamardDiv f (-t) = -hadamardDiv f t := by
  show (∫ s in (0 : ℝ)..1, deriv f (-t * s)) = -∫ s in (0 : ℝ)..1, deriv f (t * s)
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s _hs => ?_
  rw [neg_mul, deriv_odd_of_even heven]

/-- The Hadamard quotient of an odd function is even. -/
lemma hadamardDiv_even_of_odd (hodd : ∀ t, f (-t) = -f t) (t : ℝ) :
    hadamardDiv f (-t) = hadamardDiv f t := by
  show (∫ s in (0 : ℝ)..1, deriv f (-t * s)) = ∫ s in (0 : ℝ)..1, deriv f (t * s)
  refine intervalIntegral.integral_congr fun s _hs => ?_
  rw [neg_mul, deriv_even_of_odd hodd]

end HadamardDiv

section Core

/-- **The core induction for Whitney-type theorems.** Let `P` be a predicate on functions
`ℝ → ℝ` such that every `P`-function is smooth, and the derivative of a `P`-function `f`
factors as `deriv f t = 2 * (t * g t)` for some `P`-function `g`. Then `s ↦ f (√s)` is
smooth on `[0, ∞)` for every `P`-function `f`. -/
theorem contDiffOn_comp_sqrt_of_stable {P : (ℝ → ℝ) → Prop}
    (hP_smooth : ∀ f, P f → ContDiff ℝ ∞ f)
    (hP_step : ∀ f, P f → ∃ g, P g ∧ ∀ t, deriv f t = 2 * (t * g t)) :
    ∀ f, P f → ContDiffOn ℝ ∞ (fun s => f (Real.sqrt s)) (Set.Ici 0) := by
  suffices H : ∀ n : ℕ, ∀ f, P f → ContDiffOn ℝ n (fun s => f (Real.sqrt s)) (Set.Ici 0) from
    fun f hf => contDiffOn_infty.mpr fun n => H n f hf
  intro n
  induction n with
  | zero =>
    intro f hf
    rw [Nat.cast_zero, contDiffOn_zero]
    exact ((hP_smooth f hf).continuous.comp Real.continuous_sqrt).continuousOn
  | succ n ih =>
    intro f hf
    obtain ⟨g, hgP, hg⟩ := hP_step f hf
    have hfc : ContDiff ℝ ∞ f := hP_smooth f hf
    have hgc : ContDiff ℝ ∞ g := hP_smooth g hgP
    -- (a) chain rule on the open half-line
    have ha : ∀ x : ℝ, 0 < x → HasDerivAt (fun s => f (Real.sqrt s)) (g (Real.sqrt x)) x := by
      intro x hx
      have hsq : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx
      have h1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx.ne'
      have h2 : HasDerivAt f (deriv f (Real.sqrt x)) (Real.sqrt x) :=
        ((hfc.differentiable (by simp)) (Real.sqrt x)).hasDerivAt
      have h3 : HasDerivAt (fun s => f (Real.sqrt s))
          (deriv f (Real.sqrt x) * (1 / (2 * Real.sqrt x))) x := h2.comp x h1
      convert h3 using 1
      rw [hg (Real.sqrt x)]
      field_simp
    -- (b) derivative at the boundary point from the right
    have hb : HasDerivWithinAt (fun s => f (Real.sqrt s)) (g 0) (Set.Ici 0) 0 := by
      have hdiff_Ioi : DifferentiableOn ℝ (fun s => f (Real.sqrt s)) (Set.Ioi 0) :=
        fun x hx => ((ha x hx).differentiableAt).differentiableWithinAt
      have hcont : ContinuousWithinAt (fun s => f (Real.sqrt s)) (Set.Ioi 0) 0 :=
        ((hfc.continuous.comp Real.continuous_sqrt).continuousAt).continuousWithinAt
      refine hasDerivWithinAt_Ici_of_tendsto_deriv hdiff_Ioi hcont self_mem_nhdsWithin ?_
      have hgs : Continuous fun x : ℝ => g (Real.sqrt x) :=
        hgc.continuous.comp Real.continuous_sqrt
      have h1 : Tendsto (fun x : ℝ => g (Real.sqrt x)) (𝓝[>] 0) (𝓝 (g 0)) := by
        have h := hgs.tendsto 0
        simp only [Real.sqrt_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact ((ha x hx).deriv).symm
    -- (c) differentiability on the closed half-line
    have hdiff : DifferentiableOn ℝ (fun s => f (Real.sqrt s)) (Set.Ici 0) := by
      intro x hx
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with rfl | hx'
      · exact hb.differentiableWithinAt
      · exact ((ha x hx').differentiableAt).differentiableWithinAt
    -- (d) identification of the one-sided derivative
    have hderivWithin : ∀ x ∈ Set.Ici (0 : ℝ),
        derivWithin (fun s => f (Real.sqrt s)) (Set.Ici 0) x = g (Real.sqrt x) := by
      intro x hx
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with rfl | hx'
      · rw [Real.sqrt_zero]
        exact hb.derivWithin (uniqueDiffOn_Ici 0 0 Set.self_mem_Ici)
      · rw [derivWithin_of_mem_nhds (Ici_mem_nhds hx')]
        exact (ha x hx').deriv
    -- (e) assemble via the smooth-order recursion
    rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
    refine ⟨hdiff, ?_, ?_⟩
    · intro h
      exact absurd h (by simp)
    · exact (ih g hgP).congr hderivWithin

end Core

section Even

variable {f : ℝ → ℝ}

/-- **Whitney's even-function theorem, `√`-composition form.** If `f` is smooth and even,
then `s ↦ f (√s)` is smooth on `[0, ∞)`. -/
theorem contDiffOn_comp_sqrt_of_even (hf : ContDiff ℝ ∞ f) (heven : ∀ t, f (-t) = f t) :
    ContDiffOn ℝ ∞ (fun s => f (Real.sqrt s)) (Set.Ici 0) := by
  refine contDiffOn_comp_sqrt_of_stable
    (P := fun f => ContDiff ℝ ∞ f ∧ ∀ t, f (-t) = f t)
    (fun f hf => hf.1) ?_ f ⟨hf, heven⟩
  rintro f ⟨hfc, hfe⟩
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hfc).2
  have hodd : ∀ t, deriv f (-t) = -deriv f t := deriv_odd_of_even hfe
  refine ⟨fun t => (1 / 2 : ℝ) * hadamardDiv (deriv f) t, ⟨?_, ?_⟩, ?_⟩
  · exact contDiff_const.mul (contDiff_hadamardDiv hd)
  · intro t
    show (1 / 2 : ℝ) * hadamardDiv (deriv f) (-t) = (1 / 2 : ℝ) * hadamardDiv (deriv f) t
    rw [hadamardDiv_even_of_odd hodd]
  · intro t
    have h0 : deriv f 0 = 0 := eq_zero_of_odd hodd
    have hC := sub_eq_mul_hadamardDiv hd t
    rw [h0, sub_zero] at hC
    rw [hC]
    ring

/-- **Whitney's even-function theorem.** A smooth even function `f : ℝ → ℝ` factors as
`f t = g (t ^ 2)` with `g` smooth on `[0, ∞)`. -/
theorem whitney_even (hf : ContDiff ℝ ∞ f) (heven : ∀ t, f (-t) = f t) :
    ∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Set.Ici 0) ∧ ∀ t, f t = g (t ^ 2) := by
  refine ⟨fun s => f (Real.sqrt s), contDiffOn_comp_sqrt_of_even hf heven, fun t => ?_⟩
  show f t = f (Real.sqrt (t ^ 2))
  rw [Real.sqrt_sq_eq_abs]
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h]
    exact (heven t).symm

/-- A smooth function on `[0, ∞)` of the form `s ↦ f (√s)` yields a smooth function of the
norm on any real inner product space. -/
private theorem contDiff_comp_norm_of_comp_sqrt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (h : ContDiffOn ℝ ∞ (fun s => f (Real.sqrt s)) (Set.Ici 0)) :
    ContDiff ℝ ∞ fun x : E => f ‖x‖ := by
  have h1 : ContDiffOn ℝ ∞ ((fun s => f (Real.sqrt s)) ∘ fun x : E => ‖x‖ ^ 2) Set.univ :=
    h.comp (contDiff_norm_sq ℝ).contDiffOn fun x _ => Set.mem_Ici.mpr (sq_nonneg ‖x‖)
  rw [← contDiffOn_univ]
  refine h1.congr fun x _ => ?_
  show f ‖x‖ = f (Real.sqrt (‖x‖ ^ 2))
  rw [Real.sqrt_sq (norm_nonneg x)]

/-- **Whitney's even-function theorem, norm form.** If `f : ℝ → ℝ` is smooth and even, then
`x ↦ f ‖x‖` is smooth on any real inner product space. -/
theorem contDiff_even_comp_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hf : ContDiff ℝ ∞ f) (heven : ∀ t, f (-t) = f t) :
    ContDiff ℝ ∞ fun x : E => f ‖x‖ :=
  contDiff_comp_norm_of_comp_sqrt (contDiffOn_comp_sqrt_of_even hf heven)

end Even

section Flat

variable {f : ℝ → ℝ}

/-- Iterated derivatives of the weighted parametric integral: each differentiation
multiplies the weight by `s`. -/
lemma iteratedDeriv_parametricHadamard :
    ∀ (n : ℕ) {w ξ : ℝ → ℝ}, Continuous w → ContDiff ℝ ∞ ξ → ∀ t : ℝ,
      iteratedDeriv n (fun t : ℝ => ∫ s in (0 : ℝ)..1, w s * ξ (t * s)) t
        = ∫ s in (0 : ℝ)..1, w s * s ^ n * iteratedDeriv n ξ (t * s) := by
  intro n
  induction n with
  | zero =>
    intro w ξ hw hξ t
    simp [iteratedDeriv_zero]
  | succ n ih =>
    intro w ξ hw hξ t
    have hξ1 : ContDiff ℝ 1 ξ := hξ.of_le (mod_cast le_top)
    have hξ' : ContDiff ℝ ∞ (deriv ξ) := (contDiff_infty_iff_deriv.mp hξ).2
    calc iteratedDeriv (n + 1) (fun t : ℝ => ∫ s in (0 : ℝ)..1, w s * ξ (t * s)) t
        = iteratedDeriv n (deriv (fun t : ℝ => ∫ s in (0 : ℝ)..1, w s * ξ (t * s))) t := by
          rw [iteratedDeriv_succ']
      _ = iteratedDeriv n (fun t : ℝ => ∫ s in (0 : ℝ)..1, w s * s * deriv ξ (t * s)) t := by
          rw [deriv_parametricHadamard hw hξ1]
      _ = ∫ s in (0 : ℝ)..1, (w s * s) * s ^ n * iteratedDeriv n (deriv ξ) (t * s) :=
          ih (hw.mul continuous_id) hξ' t
      _ = ∫ s in (0 : ℝ)..1, w s * s ^ (n + 1) * iteratedDeriv (n + 1) ξ (t * s) := by
          refine intervalIntegral.integral_congr fun s _hs => ?_
          rw [iteratedDeriv_succ']
          ring

/-- **Whitney's theorem for flat functions, `√`-composition form.** If `f` is smooth and all
its iterated derivatives vanish at `0`, then `s ↦ f (√s)` is smooth on `[0, ∞)`. -/
theorem contDiffOn_comp_sqrt_of_flat (hf : ContDiff ℝ ∞ f)
    (hflat : ∀ n : ℕ, iteratedDeriv n f 0 = 0) :
    ContDiffOn ℝ ∞ (fun s => f (Real.sqrt s)) (Set.Ici 0) := by
  refine contDiffOn_comp_sqrt_of_stable
    (P := fun f => ContDiff ℝ ∞ f ∧ ∀ n : ℕ, iteratedDeriv n f 0 = 0)
    (fun f hf => hf.1) ?_ f ⟨hf, hflat⟩
  rintro f ⟨hfc, hff⟩
  have hd1 : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hfc).2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hd1).2
  refine ⟨fun t => ∫ s in (0 : ℝ)..1, (1 / 2 : ℝ) * deriv (deriv f) (t * s), ⟨?_, ?_⟩, ?_⟩
  · exact contDiff_top_parametricHadamard continuous_const hd2
  · -- flatness of the step function
    intro n
    rw [iteratedDeriv_parametricHadamard n continuous_const hd2 0]
    have h1 : iteratedDeriv n (deriv (deriv f)) 0 = 0 := by
      have h := hff (n + 1 + 1)
      rwa [iteratedDeriv_succ', iteratedDeriv_succ'] at h
    calc (∫ s in (0 : ℝ)..1, (1 / 2 : ℝ) * s ^ n * iteratedDeriv n (deriv (deriv f)) (0 * s))
        = ∫ s in (0 : ℝ)..1, (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun s _hs => ?_
          rw [zero_mul, h1, mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  · -- the division identity
    intro t
    have h0 : deriv f 0 = 0 := by
      have h := hff 1
      rwa [iteratedDeriv_one] at h
    have hC := sub_eq_mul_hadamardDiv hd1 t
    rw [h0, sub_zero] at hC
    show deriv f t = 2 * (t * ∫ s in (0 : ℝ)..1, (1 / 2 : ℝ) * deriv (deriv f) (t * s))
    rw [intervalIntegral.integral_const_mul, hC]
    show t * hadamardDiv (deriv f) t
        = 2 * (t * (1 / 2 * ∫ s in (0 : ℝ)..1, deriv (deriv f) (t * s)))
    rw [show (∫ s in (0 : ℝ)..1, deriv (deriv f) (t * s)) = hadamardDiv (deriv f) t from rfl]
    ring

/-- **Whitney's theorem for flat functions, norm form.** If `f : ℝ → ℝ` is smooth and all its
iterated derivatives vanish at `0`, then `x ↦ f ‖x‖` is smooth on any real inner product
space. -/
theorem contDiff_flat_comp_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hf : ContDiff ℝ ∞ f) (hflat : ∀ n : ℕ, iteratedDeriv n f 0 = 0) :
    ContDiff ℝ ∞ fun x : E => f ‖x‖ :=
  contDiff_comp_norm_of_comp_sqrt (contDiffOn_comp_sqrt_of_flat hf hflat)

end Flat

section Odd

variable {f : ℝ → ℝ}

/-- **Whitney's theorem for odd functions.** A smooth odd function `f : ℝ → ℝ` factors as
`f t = t * g (t ^ 2)` with `g` smooth on `[0, ∞)`. -/
theorem whitney_odd (hf : ContDiff ℝ ∞ f) (hodd : ∀ t, f (-t) = -f t) :
    ∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Set.Ici 0) ∧ ∀ t, f t = t * g (t ^ 2) := by
  obtain ⟨g, hg, hfg⟩ :=
    whitney_even (contDiff_hadamardDiv hf) (hadamardDiv_even_of_odd hodd)
  refine ⟨g, hg, fun t => ?_⟩
  have h := sub_eq_mul_hadamardDiv hf t
  rw [eq_zero_of_odd hodd, sub_zero] at h
  rw [h, hfg t]

end Odd

section IteratedParity

variable {f g : ℝ → ℝ}

/-- Sign-parametrized parity propagation: if `f (-t) = ε * f t` for all `t`, then
`iteratedDeriv n f (-t) = (-1) ^ n * ε * iteratedDeriv n f t`. Each differentiation flips
the parity sign once. No differentiability hypothesis is needed: `deriv` of a
non-differentiable function is `0`, and the parity identities for `deriv` hold
unconditionally. -/
lemma iteratedDeriv_comp_neg_of_sign (n : ℕ) :
    ∀ (f : ℝ → ℝ) (ε : ℝ), (∀ t, f (-t) = ε * f t) →
      ∀ t, iteratedDeriv n f (-t) = (-1) ^ n * ε * iteratedDeriv n f t := by
  induction n with
  | zero =>
    intro f ε hf t
    simpa using hf t
  | succ n ih =>
    intro f ε hf t
    have hd : ∀ t, deriv f (-t) = -ε * deriv f t := by
      intro t
      have h1 := deriv_comp_neg f t
      have h2 : (fun x => f (-x)) = fun x => ε * f x := funext hf
      rw [h2, deriv_const_mul_field] at h1
      linear_combination h1
    rw [iteratedDeriv_succ', ih (deriv f) (-ε) hd t]
    ring

set_option linter.unusedVariables false in
/-- **Math.** Every odd-order iterated derivative of a smooth even function vanishes at `0`.
(The smoothness hypothesis is kept for interface stability; the parity argument is
unconditional.) -/
theorem iteratedDeriv_odd_of_even (hf : ContDiff ℝ ∞ f) (heven : ∀ t, f (-t) = f t) (k : ℕ) :
    iteratedDeriv (2 * k + 1) f 0 = 0 := by
  refine eq_zero_of_odd fun t => ?_
  have h := iteratedDeriv_comp_neg_of_sign (2 * k + 1) f 1
    (fun t => by rw [one_mul]; exact heven t) t
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, by ring⟩
  rw [h, hpow]
  ring

set_option linter.unusedVariables false in
/-- **Math.** Every even-order iterated derivative of a smooth odd function vanishes at `0`.
(The smoothness hypothesis is kept for interface stability; the parity argument is
unconditional.) -/
theorem iteratedDeriv_even_of_odd (hf : ContDiff ℝ ∞ f) (hodd : ∀ t, f (-t) = -f t) (k : ℕ) :
    iteratedDeriv (2 * k) f 0 = 0 := by
  refine eq_zero_of_odd fun t => ?_
  have h := iteratedDeriv_comp_neg_of_sign (2 * k) f (-1)
    (fun t => by rw [neg_one_mul]; exact hodd t) t
  have hpow : (-1 : ℝ) ^ (2 * k) = 1 := Even.neg_one_pow ⟨k, by ring⟩
  rw [h, hpow]
  ring

/-- Auxiliary form of `iteratedDeriv_comp_const_sub` with the function universally
quantified, for the induction. No differentiability hypothesis is needed. -/
private lemma iteratedDeriv_comp_const_sub_aux (c : ℝ) (n : ℕ) :
    ∀ (f : ℝ → ℝ) (x : ℝ),
      iteratedDeriv n (fun s => f (c - s)) x = (-1) ^ n * iteratedDeriv n f (c - x) := by
  induction n with
  | zero =>
    intro f x
    simp
  | succ n ih =>
    intro f x
    have hd : deriv (fun s => f (c - s)) = fun s => (-1 : ℝ) * deriv f (c - s) := by
      funext s
      rw [deriv_comp_const_sub f c s]
      ring
    rw [iteratedDeriv_succ', hd]
    simp only [iteratedDeriv_const_mul_field]
    rw [ih (deriv f) x, iteratedDeriv_succ']
    ring

set_option linter.unusedVariables false in
/-- **Math.** Iterated derivatives of the reflection `s ↦ f (c - s)`:
`iteratedDeriv n (fun s => f (c - s)) x = (-1) ^ n * iteratedDeriv n f (c - x)`.
(The smoothness hypothesis is kept for interface stability; the identity is
unconditional.) -/
theorem iteratedDeriv_comp_const_sub (hf : ContDiff ℝ ∞ f) (c : ℝ) (n : ℕ) :
    ∀ x, iteratedDeriv n (fun s => f (c - s)) x = (-1) ^ n * iteratedDeriv n f (c - x) :=
  fun x => iteratedDeriv_comp_const_sub_aux c n f x

/-- **Math.** Germ transfer at `0` from the right: if two smooth functions agree on
`(0, δ)` for some `δ > 0`, then all their iterated derivatives agree at `0`. Indeed the
iterated derivatives agree on the open interval, are continuous at `0`, and `0` is in the
closure of `(0, δ)`. -/
theorem iteratedDeriv_eq_of_eqOn_Ioo (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {δ : ℝ} (hδ : 0 < δ) (hfg : ∀ t ∈ Set.Ioo (0 : ℝ) δ, f t = g t) (n : ℕ) :
    iteratedDeriv n f 0 = iteratedDeriv n g 0 := by
  have heq : Set.EqOn (iteratedDeriv n f) (iteratedDeriv n g) (Set.Ioo 0 δ) :=
    Set.EqOn.iteratedDeriv_of_isOpen (fun t ht => hfg t ht) isOpen_Ioo n
  have hcf : Tendsto (iteratedDeriv n f) (𝓝[>] (0 : ℝ)) (𝓝 (iteratedDeriv n f 0)) :=
    ((hf.continuous_iteratedDeriv n (mod_cast le_top)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hcg : Tendsto (iteratedDeriv n g) (𝓝[>] (0 : ℝ)) (𝓝 (iteratedDeriv n g 0)) :=
    ((hg.continuous_iteratedDeriv n (mod_cast le_top)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hev : iteratedDeriv n f =ᶠ[𝓝[>] (0 : ℝ)] iteratedDeriv n g := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
    exact heq hx
  exact tendsto_nhds_unique (hcf.congr' hev) hcg

end IteratedParity

end PetersenLib
