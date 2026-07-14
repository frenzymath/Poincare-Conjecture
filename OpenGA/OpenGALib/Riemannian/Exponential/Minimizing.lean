import OpenGALib.Riemannian.Exponential.GaussLemma
import OpenGALib.Riemannian.Exponential.StrictDerivativeBall
import OpenGALib.Riemannian.Exponential.LocalDiffeo
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

/-!
# Radial geodesics minimize length on the Gauss ball (do Carmo Ch. 3, Prop. 3.6)

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 3.6: inside a normal ball,
the radial geodesic `γ(t) = exp_p(t v)` is no longer than any piecewise
differentiable curve joining its endpoints. This file proves the inequality
for competing curves presented in polar form through the exponential chart:
a curve `c(t) = exp_p(w(t))` with `w : [a, b] → B_ρ(0) ⊂ T_pM` differentiable.

The analytic core is the **smoothed-radius comparison**
(`gauss_radius_comparison`): writing `r(t) = √⟨w(t), w(t)⟩_p` for the
`g`-radius of the polar lift, do Carmo's inequality (1)
`|dc/dt| ≥ |dr/dt|` integrates to `r(b) - r(a) ≤ ℓ(c)`. Since `r` need not
be differentiable at zeros of `w`, we run the comparison on the smoothed
radius `r_δ(t) = √(⟨w(t), w(t)⟩_p + δ)`, `δ > 0`, which is differentiable
everywhere with

`r_δ'(t) = ⟨w, w'⟩_p / √(⟨w, w⟩_p + δ)`,

and the radial lower bound from the Gauss lemma
(`exists_gauss_radial_lower_bound_ball`, do Carmo's
`⟨v, ξ⟩_p² ≤ ⟨v, v⟩_p · |(d exp_p)_v ξ|²`) gives `|r_δ'(t)| ≤ |ċ(t)|_g`
*at every* `t` — including zeros of `w`. The fundamental theorem of calculus
and monotonicity of the interval integral yield
`r_δ(b) - r_δ(a) ≤ ∫ |ċ|_g`, and `δ → 0⁺` recovers the radius comparison
with no corner analysis.

## Main statements

* `hasDerivAt_chartMetricInner_const_base` — product rule for the chart Gram
  pairing at a **fixed** base point: `d/dt ⟨V(t), W(t)⟩_{y₀} = ⟨V', W⟩ + ⟨V, W'⟩`.
* `continuousOn_chartMetricInner_along` — continuity of `t ↦ ⟨V(t), W(t)⟩_{u(t)}`
  for continuous data along a continuous base curve in the chart target.
* `chartMetricInner_self_nonneg_of_mem_target` — the chart Gram quadratic form
  is positive semidefinite at every base point of the chart target.
* `gauss_radius_comparison` — the smoothed-radius comparison, abstract in the
  chart reading `f` of the exponential map.
* `exists_gauss_radius_comparison_ball` — the comparison on the Gauss ball of
  `exp_p`: `r(b) - r(a) ≤ ℓ(exp_p ∘ w)` (chart-read lengths).
* `exists_expMap_ray_speed_ball` — the radial geodesic `t ↦ exp_p(t v)` has
  constant chart-read speed `⟨v, v⟩_p` on `[0, 1]` (Gauss lemma at `(tv, v)`;
  at `t = 0`, `d(exp_p)_0 = id`).
* `exists_minimizing_geodesic_ball` — **the minimizing property** (do Carmo
  Ch. 3, Prop. 3.6, polar form): for every competing differentiable polar lift
  `w` with `w(0) = 0`, `w(1) = v`,
  `ℓ(t ↦ exp_p(t v)) ≤ ℓ(t ↦ exp_p(w(t)))`.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

section ChartMetricInnerCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Product rule for the chart Gram inner product at a **fixed** base
point `y₀`: for differentiable vector paths `V, W : ℝ → E`,
`d/dt ⟨V(t), W(t)⟩_{y₀} = ⟨V'(t), W(t)⟩_{y₀} + ⟨V(t), W'(t)⟩_{y₀}`.
(No Christoffel correction appears: the base point does not move.) -/
theorem hasDerivAt_chartMetricInner_const_base (g : RiemannianMetric I M) (α : M) (y₀ : E)
    {V W : ℝ → E} {V' W' : E} {t : ℝ}
    (hV : HasDerivAt V V' t) (hW : HasDerivAt W W' t) :
    HasDerivAt (fun s => chartMetricInner (I := I) g α y₀ (V s) (W s))
      (chartMetricInner (I := I) g α y₀ V' (W t)
        + chartMetricInner (I := I) g α y₀ (V t) W') t := by
  classical
  have hv : ∀ i : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => Geodesic.chartCoord (E := E) i (V s))
        (Geodesic.chartCoord (E := E) i V') t := by
    intro i
    simpa only [Geodesic.chartCoordFunctional_apply, Function.comp_def] using
      (Geodesic.chartCoordFunctional (E := E) i).hasFDerivAt.comp_hasDerivAt t hV
  have hw : ∀ j : Fin (Module.finrank ℝ E),
      HasDerivAt (fun s => Geodesic.chartCoord (E := E) j (W s))
        (Geodesic.chartCoord (E := E) j W') t := by
    intro j
    simpa only [Geodesic.chartCoordFunctional_apply, Function.comp_def] using
      (Geodesic.chartCoordFunctional (E := E) j).hasFDerivAt.comp_hasDerivAt t hW
  have hfun : (fun s => chartMetricInner (I := I) g α y₀ (V s) (W s))
      = ∑ i, ∑ j, fun s => chartGramOnE (I := I) g α i j y₀
          * Geodesic.chartCoord (E := E) i (V s) * Geodesic.chartCoord (E := E) j (W s) := by
    funext s
    simp only [chartMetricInner_def, Finset.sum_apply]
  have hsum : HasDerivAt (fun s => chartMetricInner (I := I) g α y₀ (V s) (W s))
      (∑ i, ∑ j, (chartGramOnE (I := I) g α i j y₀
            * Geodesic.chartCoord (E := E) i V' * Geodesic.chartCoord (E := E) j (W t)
          + chartGramOnE (I := I) g α i j y₀
            * Geodesic.chartCoord (E := E) i (V t) * Geodesic.chartCoord (E := E) j W')) t := by
    rw [hfun]
    refine HasDerivAt.sum fun i _ => HasDerivAt.sum fun j _ => ?_
    have h := (HasDerivAt.const_mul (chartGramOnE (I := I) g α i j y₀) (hv i)).mul (hw j)
    refine h.congr_deriv ?_
    ring
  refine hsum.congr_deriv ?_
  rw [chartMetricInner_def, chartMetricInner_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]

/-- **Math.** Continuity of the chart Gram pairing along a continuous base curve
in the chart target, against continuous vector paths: `t ↦ ⟨V(t), W(t)⟩_{u(t)}`
is continuous on `s` whenever `u, V, W` are and `u` stays in the chart target
(where the pulled-back Gram entries are smooth). -/
theorem continuousOn_chartMetricInner_along (g : RiemannianMetric I M) (α : M)
    {s : Set ℝ} {u V W : ℝ → E}
    (hu : ContinuousOn u s) (hV : ContinuousOn V s) (hW : ContinuousOn W s)
    (htgt : ∀ t ∈ s, u t ∈ (extChartAt I α).target) :
    ContinuousOn (fun t => chartMetricInner (I := I) g α (u t) (V t) (W t)) s := by
  classical
  have hfun : (fun t => chartMetricInner (I := I) g α (u t) (V t) (W t))
      = fun t => ∑ i, ∑ j, chartGramOnE (I := I) g α i j (u t)
          * Geodesic.chartCoord (E := E) i (V t) * Geodesic.chartCoord (E := E) j (W t) := by
    funext t
    simp only [chartMetricInner_def]
  rw [hfun]
  refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
  have hG : ContinuousOn (fun t => chartGramOnE (I := I) g α i j (u t)) s :=
    (chartGramOnE_contDiffOn (I := I) g α i j).continuousOn.comp hu
      (fun t ht => htgt t ht)
  have hcV : ContinuousOn (fun t => Geodesic.chartCoord (E := E) i (V t)) s := by
    have h := (Geodesic.chartCoordFunctional (E := E) i).continuous.comp_continuousOn hV
    simpa only [Geodesic.chartCoordFunctional_apply, Function.comp_def] using h
  have hcW : ContinuousOn (fun t => Geodesic.chartCoord (E := E) j (W t)) s := by
    have h := (Geodesic.chartCoordFunctional (E := E) j).continuous.comp_continuousOn hW
    simpa only [Geodesic.chartCoordFunctional_apply, Function.comp_def] using h
  exact (hG.mul hcV).mul hcW

/-- **Math.** The chart Gram quadratic form is **positive semidefinite** at every
base point `y` of the chart target: `0 ≤ ⟨a, a⟩_y`. The Gram pairing at `y` is
the intrinsic inner product at the foot `(extChartAt I p).symm y`. -/
theorem chartMetricInner_self_nonneg_of_mem_target (g : RiemannianMetric I M) (p : M)
    {y : E} (hy : y ∈ (extChartAt I p).target) (a : E) :
    0 ≤ chartMetricInner (I := I) g p y a a := by
  have hb : (extChartAt I p).symm y ∈ (chartAt H p).source := by
    have h := (extChartAt I p).map_target hy
    rwa [extChartAt_source] at h
  have h := chartMetricInner_extChartAt_eq_metricInner (I := I) g p hb a a
  rw [(extChartAt I p).right_inv hy] at h
  rw [h]
  exact g.metricInner_self_nonneg _ _

end ChartMetricInnerCalculus

namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

open Riemannian.Geodesic

/-- **Math.** **The smoothed-radius comparison** (do Carmo Ch. 3, the integral
estimate (1)–(2) in the proof of Prop. 3.6), abstract in the chart reading
`f` of the exponential map. Suppose on the ball `B_ρ(0)`:

* `f` maps into the chart target and is `C¹`;
* the **radial lower bound** holds:
  `⟨v, ξ⟩_p² ≤ ⟨v, v⟩_p · ⟨(df)_v ξ, (df)_v ξ⟩_{f(v)}`.

Then for every continuous path `w : [a, b] → B_ρ(0)`, differentiable on the
open interval with derivative extending continuously to the endpoints, the
`g_p`-radius gain is bounded by the chart-read length of the composed curve
`c = f ∘ w`:

`√⟨w(b), w(b)⟩_p − √⟨w(a), w(a)⟩_p ≤ ∫_a^b √⟨ċ(t), ċ(t)⟩_{c(t)} dt`,

with `ċ(t) = (df)_{w(t)} w'(t)` by the chain rule. The proof runs the estimate
on the smoothed radius `r_δ = √(⟨w, w⟩_p + δ)`, which is differentiable even
at zeros of `w`, and lets `δ → 0⁺`. Only interior differentiability is
required (the fundamental theorem of calculus is applied in its
right-derivative form), so the estimate telescopes over the pieces of a
piecewise-differentiable competitor. -/
theorem gauss_radius_comparison (g : RiemannianMetric I M) (p : M)
    (f : E → E) {ρ : ℝ}
    (htgt : ∀ u : E, ‖u‖ < ρ → f u ∈ (extChartAt I p).target)
    (hC1 : ContDiffOn ℝ 1 f (ball (0 : E) ρ))
    (hradial : ∀ v ξ : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (extChartAt I p p) v ξ ^ 2
        ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v
          * chartMetricInner (I := I) g p (f v) (fderiv ℝ f v ξ) (fderiv ℝ f v ξ))
    {w w' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hw_cont : ContinuousOn w (Icc a b))
    (hw : ∀ t ∈ Ioo a b, HasDerivAt w (w' t) t)
    (hw' : ContinuousOn w' (Icc a b))
    (hwball : ∀ t ∈ Icc a b, ‖w t‖ < ρ) :
    Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w b) (w b))
      - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w a) (w a))
      ≤ ∫ t in a..b, Real.sqrt (chartMetricInner (I := I) g p (f (w t))
          (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t))) := by
  classical
  have hy₀tgt : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source (mem_extChartAt_source p)
  set Q : ℝ → ℝ :=
    fun t => chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t) with hQdef
  set P : ℝ → ℝ :=
    fun t => chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w' t) with hPdef
  set D : ℝ → E := fun t => fderiv ℝ f (w t) (w' t) with hDdef
  set R : ℝ → ℝ :=
    fun t => chartMetricInner (I := I) g p (f (w t)) (D t) (D t) with hRdef
  set S : ℝ → ℝ := fun t => Real.sqrt (R t) with hSdef
  -- continuity of the pieces on `[a, b]`
  have hQ_cont : ContinuousOn Q (Icc a b) :=
    continuousOn_chartMetricInner_along (I := I) g p continuousOn_const hw_cont hw_cont
      (fun t _ => hy₀tgt)
  have hP_cont : ContinuousOn P (Icc a b) :=
    continuousOn_chartMetricInner_along (I := I) g p continuousOn_const hw_cont hw'
      (fun t _ => hy₀tgt)
  have hmaps : MapsTo w (Icc a b) (ball (0 : E) ρ) := fun t ht =>
    mem_ball_zero_iff.mpr (hwball t ht)
  have hD_cont : ContinuousOn D (Icc a b) := by
    have h1 : ContinuousOn (fun t => fderiv ℝ f (w t)) (Icc a b) :=
      (hC1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).comp hw_cont hmaps
    exact h1.clm_apply hw'
  have hfw_tgt : ∀ t ∈ Icc a b, f (w t) ∈ (extChartAt I p).target := fun t ht =>
    htgt (w t) (hwball t ht)
  have hfw_cont : ContinuousOn (fun t => f (w t)) (Icc a b) :=
    hC1.continuousOn.comp hw_cont hmaps
  have hR_cont : ContinuousOn R (Icc a b) :=
    continuousOn_chartMetricInner_along (I := I) g p hfw_cont hD_cont hD_cont hfw_tgt
  have hS_cont : ContinuousOn S (Icc a b) := hR_cont.sqrt
  have hS_int : IntervalIntegrable S MeasureTheory.volume a b :=
    hS_cont.intervalIntegrable_of_Icc hab
  -- nonnegativity of the two quadratic forms
  have hQ_nonneg : ∀ t ∈ Icc a b, 0 ≤ Q t := fun t _ =>
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p hy₀tgt (w t)
  have hR_nonneg : ∀ t ∈ Icc a b, 0 ≤ R t := fun t ht =>
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p (hfw_tgt t ht) (D t)
  -- the radial lower bound in `P/Q/R` form
  have hPQR : ∀ t ∈ Icc a b, P t ^ 2 ≤ Q t * R t := fun t ht =>
    hradial (w t) (w' t) (hwball t ht)
  -- ## the smoothed-radius estimate, for every `δ > 0`
  have hkey : ∀ δ : ℝ, 0 < δ →
      Real.sqrt (Q b + δ) - Real.sqrt (Q a + δ) ≤ ∫ t in a..b, S t := by
    intro δ hδ
    have hQδ_pos : ∀ t ∈ Icc a b, 0 < Q t + δ := fun t ht => by
      have := hQ_nonneg t ht; linarith
    -- the smoothed radius and its derivative (on the open interval)
    have hφderiv : ∀ t ∈ Ioo a b,
        HasDerivAt (fun s => Real.sqrt (Q s + δ)) (P t / Real.sqrt (Q t + δ)) t := by
      intro t ht
      have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
      have hQ' : HasDerivAt Q (2 * P t) t := by
        have h := hasDerivAt_chartMetricInner_const_base (I := I) g p
          (extChartAt I p p) (hw t ht) (hw t ht)
        refine h.congr_deriv ?_
        rw [chartMetricInner_symm (I := I) g p (extChartAt I p p) (w' t) (w t)]
        rw [hPdef]
        ring
      have hQt : HasDerivAt (fun s => Q s + δ) (2 * P t) t := hQ'.add_const δ
      have hsq := (Real.hasDerivAt_sqrt (ne_of_gt (hQδ_pos t ht'))).comp t hQt
      have hs_pos : 0 < Real.sqrt (Q t + δ) := Real.sqrt_pos.mpr (hQδ_pos t ht')
      refine (hsq.congr_deriv ?_ : HasDerivAt (fun s => Real.sqrt (Q s + δ)) _ t)
      field_simp
    have hφ'_cont : ContinuousOn (fun t => P t / Real.sqrt (Q t + δ)) (Icc a b) := by
      refine hP_cont.div ((hQ_cont.add continuousOn_const).sqrt) ?_
      intro t ht
      exact ne_of_gt (Real.sqrt_pos.mpr (hQδ_pos t ht))
    have hφ'_int : IntervalIntegrable (fun t => P t / Real.sqrt (Q t + δ))
        MeasureTheory.volume a b :=
      hφ'_cont.intervalIntegrable_of_Icc hab
    have hφcont : ContinuousOn (fun s => Real.sqrt (Q s + δ)) (Icc a b) :=
      (hQ_cont.add continuousOn_const).sqrt
    have hFTC : (∫ t in a..b, P t / Real.sqrt (Q t + δ))
        = Real.sqrt (Q b + δ) - Real.sqrt (Q a + δ) := by
      refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
        (f := fun s => Real.sqrt (Q s + δ)) hab hφcont
        (fun t ht => (hφderiv t ht).hasDerivWithinAt) hφ'_int
    -- the pointwise bound `r_δ'(t) ≤ |ċ(t)|_g`
    have hbound : ∀ t ∈ Icc a b, P t / Real.sqrt (Q t + δ) ≤ S t := by
      intro t ht
      have hRt := hR_nonneg t ht
      have hs_pos : 0 < Real.sqrt (Q t + δ) := Real.sqrt_pos.mpr (hQδ_pos t ht)
      have h1 : P t ^ 2 ≤ (Q t + δ) * R t := by
        have h2 := hPQR t ht
        nlinarith [mul_nonneg (le_of_lt hδ) hRt]
      have h2 : P t ≤ Real.sqrt ((Q t + δ) * R t) :=
        calc P t ≤ |P t| := le_abs_self _
          _ = Real.sqrt (P t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt ((Q t + δ) * R t) := Real.sqrt_le_sqrt h1
      rw [div_le_iff₀ hs_pos]
      calc P t ≤ Real.sqrt ((Q t + δ) * R t) := h2
        _ = Real.sqrt (Q t + δ) * S t := Real.sqrt_mul (le_of_lt (hQδ_pos t ht)) _
        _ = S t * Real.sqrt (Q t + δ) := mul_comm _ _
    calc Real.sqrt (Q b + δ) - Real.sqrt (Q a + δ)
        = ∫ t in a..b, P t / Real.sqrt (Q t + δ) := hFTC.symm
      _ ≤ ∫ t in a..b, S t :=
          intervalIntegral.integral_mono_on hab hφ'_int hS_int hbound
  -- ## let `δ → 0⁺`
  have htend : Tendsto (fun δ : ℝ => Real.sqrt (Q b + δ) - Real.sqrt (Q a + δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (Q b) - Real.sqrt (Q a))) := by
    have hcont : Continuous (fun δ : ℝ => Real.sqrt (Q b + δ) - Real.sqrt (Q a + δ)) := by
      fun_prop
    have h0 := hcont.tendsto 0
    simp only [add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hkey δ hδ

/-- **Math.** **The reach estimate** (do Carmo Ch. 3, the escape case
`ℓ(c) ≥ ρ` in the proof of Prop. 3.6, polar form): under the hypotheses of
`gauss_radius_comparison`, the `g_p`-radius reached by the polar lift at
*any* intermediate time is dominated by the total length of the composed
curve:

`√⟨w(t₁), w(t₁)⟩_p − √⟨w(a), w(a)⟩_p ≤ ∫_a^b |ċ(t)| dt` for `t₁ ∈ [a, b]`.

Radius comparison on `[a, t₁]`, then monotonicity of the integral of the
(pointwise nonnegative) speed. With `w(a) = 0` this is do Carmo's escape
inequality: a curve whose polar lift reaches `g_p`-radius `ρ'` has length at
least `ρ'`, regardless of where it ends. -/
theorem gauss_radius_reach (g : RiemannianMetric I M) (p : M)
    (f : E → E) {ρ : ℝ}
    (htgt : ∀ u : E, ‖u‖ < ρ → f u ∈ (extChartAt I p).target)
    (hC1 : ContDiffOn ℝ 1 f (ball (0 : E) ρ))
    (hradial : ∀ v ξ : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (extChartAt I p p) v ξ ^ 2
        ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v
          * chartMetricInner (I := I) g p (f v) (fderiv ℝ f v ξ) (fderiv ℝ f v ξ))
    {w w' : ℝ → E} {a b : ℝ}
    (hw_cont : ContinuousOn w (Icc a b))
    (hw : ∀ t ∈ Ioo a b, HasDerivAt w (w' t) t)
    (hw' : ContinuousOn w' (Icc a b))
    (hwball : ∀ t ∈ Icc a b, ‖w t‖ < ρ)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a b) :
    Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t₁) (w t₁))
      - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w a) (w a))
      ≤ ∫ t in a..b, Real.sqrt (chartMetricInner (I := I) g p (f (w t))
          (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t))) := by
  classical
  have hsub : Icc a t₁ ⊆ Icc a b := Icc_subset_Icc le_rfl ht₁.2
  have hsub' : Ioo a t₁ ⊆ Ioo a b := Ioo_subset_Ioo le_rfl ht₁.2
  -- radius comparison on `[a, t₁]`
  have hstep := gauss_radius_comparison (I := I) g p f htgt hC1 hradial
    (w := w) (w' := w') ht₁.1 (hw_cont.mono hsub)
    (fun t ht => hw t (hsub' ht)) (hw'.mono hsub) (fun t ht => hwball t (hsub ht))
  refine hstep.trans ?_
  -- the speed integrand is continuous on `[a, b]`, hence interval integrable
  have hmaps : MapsTo w (Icc a b) (ball (0 : E) ρ) := fun t ht =>
    mem_ball_zero_iff.mpr (hwball t ht)
  have hD_cont : ContinuousOn (fun t => fderiv ℝ f (w t) (w' t)) (Icc a b) :=
    ((hC1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).comp hw_cont
      hmaps).clm_apply hw'
  have hS_cont : ContinuousOn (fun t => Real.sqrt (chartMetricInner (I := I) g p
      (f (w t)) (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t)))) (Icc a b) :=
    (continuousOn_chartMetricInner_along (I := I) g p
      (hC1.continuousOn.comp hw_cont hmaps) hD_cont hD_cont
      (fun t ht => htgt (w t) (hwball t ht))).sqrt
  have hS_int : IntervalIntegrable (fun t => Real.sqrt (chartMetricInner (I := I) g p
      (f (w t)) (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t))))
      MeasureTheory.volume a b :=
    hS_cont.intervalIntegrable_of_Icc (ht₁.1.trans ht₁.2)
  -- monotonicity in the upper endpoint: the integrand is nonnegative
  refine intervalIntegral.integral_mono_interval le_rfl ht₁.1 ht₁.2 ?_ hS_int
  filter_upwards with t
  exact Real.sqrt_nonneg _

/-- **Math.** **The radius comparison on the Gauss ball of `exp_p`** (do Carmo
Ch. 3, the integral estimate (2) in the proof of Prop. 3.6). There is `ρ > 0`
with the ball `B_ρ(0) ⊂ T_pM` in the exponential domain and its image in the
chart at `p`, such that for every differentiable path `w : [a, b] → B_ρ(0)`
with continuous derivative, the `g_p`-radius gain of `w` is at most the
chart-read length of the curve `c = exp_p ∘ w`:

`√⟨w(b), w(b)⟩_p − √⟨w(a), w(a)⟩_p ≤ ∫_a^b √⟨ċ, ċ⟩_{c(t)} dt`. -/
theorem exists_gauss_radius_comparison_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : E, ‖u‖ < ρ → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ρ →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ (w w' : ℝ → E) (a b : ℝ), a ≤ b →
        ContinuousOn w (Icc a b) →
        (∀ t ∈ Ioo a b, HasDerivAt w (w' t) t) →
        ContinuousOn w' (Icc a b) →
        (∀ t ∈ Icc a b, ‖w t‖ < ρ) →
        Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w b) (w b))
          - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w a) (w a))
          ≤ ∫ t in a..b, Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (w t) (w' t))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (w t) (w' t)))) := by
  classical
  obtain ⟨ρ₁, hρ₁, hdom₁, hsrc₁, hradial⟩ :=
    exists_gauss_radial_lower_bound_ball (I := I) g p
  obtain ⟨ρ₂, hρ₂, hdom₂, hsrc₂, hC1⟩ :=
    exists_contDiffOn_extChartAt_expMap_ball (I := I) g p
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂,
    fun u hu => hdom₁ u (hu.trans_le (min_le_left _ _)),
    fun u hu => hsrc₁ u (hu.trans_le (min_le_left _ _)), ?_⟩
  intro w w' a b hab hwc hw hw' hwball
  exact gauss_radius_comparison (I := I) g p
    (fun u : E => extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
    (fun u hu => (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc₁ u (hu.trans_le (min_le_left _ _))))
    (hC1.mono (ball_subset_ball (min_le_right _ _)))
    (fun v ξ hv => hradial v ξ (hv.trans_le (min_le_left _ _)))
    hab hwc hw hw' hwball

/-- **Math.** **The reach estimate on the Gauss ball of `exp_p`** (do Carmo
Ch. 3, the escape case in the proof of Prop. 3.6, polar form). On the Gauss
ball: a curve `c = exp_p ∘ w` starting at `p` (`w(a) = 0`) has length at
least the `g_p`-radius its polar lift reaches at any time:

`√⟨w(t₁), w(t₁)⟩_p ≤ ∫_a^b |ċ(t)| dt` for every `t₁ ∈ [a, b]`.

In do Carmo's escape case, a competitor leaving the normal ball of `g_p`-radius
`ρ'` reaches radius `ρ'`, so its length is at least `ρ' > ℓ(γ)`. -/
theorem exists_gauss_radius_reach_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : E, ‖u‖ < ρ → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ρ →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ (w w' : ℝ → E) (a b : ℝ),
        ContinuousOn w (Icc a b) →
        (∀ t ∈ Ioo a b, HasDerivAt w (w' t) t) →
        ContinuousOn w' (Icc a b) →
        (∀ t ∈ Icc a b, ‖w t‖ < ρ) →
        w a = 0 →
        ∀ t₁ ∈ Icc a b,
        Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t₁) (w t₁))
          ≤ ∫ t in a..b, Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (w t) (w' t))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (w t) (w' t)))) := by
  classical
  obtain ⟨ρ₁, hρ₁, hdom₁, hsrc₁, hradial⟩ :=
    exists_gauss_radial_lower_bound_ball (I := I) g p
  obtain ⟨ρ₂, hρ₂, hdom₂, hsrc₂, hC1⟩ :=
    exists_contDiffOn_extChartAt_expMap_ball (I := I) g p
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂,
    fun u hu => hdom₁ u (hu.trans_le (min_le_left _ _)),
    fun u hu => hsrc₁ u (hu.trans_le (min_le_left _ _)), ?_⟩
  intro w w' a b hwc hw hw' hwball hwa t₁ ht₁
  have hreach := gauss_radius_reach (I := I) g p
    (fun u : E => extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
    (fun u hu => (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc₁ u (hu.trans_le (min_le_left _ _))))
    (hC1.mono (ball_subset_ball (min_le_right _ _)))
    (fun v ξ hv => hradial v ξ (hv.trans_le (min_le_left _ _)))
    hwc hw hw' hwball ht₁
  rwa [hwa, chartMetricInner_zero_left, Real.sqrt_zero, sub_zero] at hreach

/-- **Math.** **The radial geodesic has constant chart-read speed** (do Carmo
Ch. 3, the identity `|∂f/∂r| = 1` in the proof of Prop. 3.6, unnormalized
form). There is `ρ > 0` such that for every `v` with `‖v‖ < ρ` and every
`t ∈ [0, 1]`, the chart-read squared speed of the radial curve
`τ ↦ exp_p(τ v)` at time `t` equals `⟨v, v⟩_p`:

`⟨(d exp_p)_{tv}(v), (d exp_p)_{tv}(v)⟩_{exp_p(tv)} = ⟨v, v⟩_p`.

For `t ≠ 0` this is the Gauss identity at the pair `(tv, v)` divided by `t`;
at `t = 0` it is `(d exp_p)_0 = id` and `exp_p(0) = p`. -/
theorem exists_expMap_ray_speed_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : E, ‖u‖ < ρ → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ρ →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ v : E, ‖v‖ < ρ → ∀ t ∈ Icc (0 : ℝ) 1,
        chartMetricInner (I := I) g p
            (extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
            (fderiv ℝ (fun u : E =>
              extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)
            (fderiv ℝ (fun u : E =>
              extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)
          = chartMetricInner (I := I) g p (extChartAt I p p) v v) := by
  classical
  obtain ⟨ρ₁, c, hρ₁, hc, hadm, hC2, hfd0, hODE⟩ :=
    exists_expMap_ray_ode_ball (I := I) g p
  obtain ⟨ρ₂, hρ₂, hdom₂, hsrc₂, hgauss⟩ := exists_gauss_lemma_ball (I := I) g p
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂,
    fun u hu => hdom₂ u (hu.trans_le (min_le_right _ _)),
    fun u hu => hsrc₂ u (hu.trans_le (min_le_right _ _)), ?_⟩
  intro v hv t ht
  rcases eq_or_ne t 0 with rfl | ht0
  · -- `t = 0`: the derivative is the identity and the foot is `p`
    rw [zero_smul, hfd0]
    have hf0 : extChartAt I p (expMap (I := I) g p ((0 : E) : TangentSpace I p))
        = extChartAt I p p :=
      congrArg (extChartAt I p) (expMap_zero (I := I) g p)
    rw [hf0, ContinuousLinearMap.id_apply]
  · -- `t ≠ 0`: Gauss identity at the pair `(t • v, v)`, divided by `t`
    have htv : ‖t • v‖ < ρ₂ := by
      have h01 : |t| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [ht.1], ht.2⟩
      calc ‖t • v‖ = |t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right h01 (norm_nonneg v)
        _ = ‖v‖ := one_mul _
        _ < ρ₂ := hv.trans_le (min_le_right _ _)
    have hg := hgauss (t • v) v htv
    rw [map_smul, chartMetricInner_smul_left, chartMetricInner_smul_left] at hg
    exact mul_left_cancel₀ ht0 hg

/-- **Math.** **Radial geodesics minimize on the Gauss ball** (do Carmo Ch. 3,
Proposition 3.6, polar form). There is `ρ > 0` such that for every `v` with
`‖v‖ < ρ` and every competing curve presented in polar form through the
exponential chart — a differentiable `w : [0, 1] → B_ρ(0) ⊂ T_pM` with
continuous derivative, `w(0) = 0`, `w(1) = v` — the chart-read length of the
radial geodesic `γ(t) = exp_p(t v)` is at most that of `c(t) = exp_p(w(t))`:

`ℓ(γ) = ∫_0^1 √⟨γ̇, γ̇⟩ dt = √⟨v, v⟩_p ≤ ∫_0^1 √⟨ċ, ċ⟩ dt = ℓ(c)`.

The left-hand side is evaluated by the constant ray speed
(`exists_expMap_ray_speed_ball`), the right-hand side is bounded below by the
radius gain `√⟨w(1), w(1)⟩_p − √⟨w(0), w(0)⟩_p = √⟨v, v⟩_p`
(`exists_gauss_radius_comparison_ball`). do Carmo's arbitrary competing curve
inside the normal ball reduces to this polar form through the local inverse of
`exp_p` (`exists_c1_local_diffeomorphism_expMap`); curves leaving the ball and
the equality case are handled separately. -/
theorem exists_minimizing_geodesic_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : E, ‖u‖ < ρ → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ρ →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ v : E, ‖v‖ < ρ → ∀ w w' : ℝ → E,
        ContinuousOn w (Icc (0 : ℝ) 1) →
        (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt w (w' t) t) →
        ContinuousOn w' (Icc (0 : ℝ) 1) →
        (∀ t ∈ Icc (0 : ℝ) 1, ‖w t‖ < ρ) →
        w 0 = 0 → w 1 = v →
        (∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
            (extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
            (fderiv ℝ (fun u : E =>
              extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)
            (fderiv ℝ (fun u : E =>
              extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)))
          ≤ ∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (w t) (w' t))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (w t) (w' t)))) := by
  classical
  obtain ⟨ρ₁, hρ₁, hdom₁, hsrc₁, hcomp⟩ :=
    exists_gauss_radius_comparison_ball (I := I) g p
  obtain ⟨ρ₂, hρ₂, hdom₂, hsrc₂, hray⟩ :=
    exists_expMap_ray_speed_ball (I := I) g p
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂,
    fun u hu => hdom₁ u (hu.trans_le (min_le_left _ _)),
    fun u hu => hsrc₁ u (hu.trans_le (min_le_left _ _)), ?_⟩
  intro v hv w w' hwc hw hw' hwball hw0 hw1
  -- the radial geodesic has length `√⟨v, v⟩_p`
  have hLHS : (∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
        (fderiv ℝ (fun u : E =>
          extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)
        (fderiv ℝ (fun u : E =>
          extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)))
      = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) := by
    have hEq : EqOn (fun t : ℝ => Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
          (fderiv ℝ (fun u : E =>
            extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)
          (fderiv ℝ (fun u : E =>
            extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)))
        (fun _ : ℝ => Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v))
        (uIcc (0 : ℝ) 1) := by
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact congrArg Real.sqrt (hray v (hv.trans_le (min_le_right _ _)) t ht)
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_const]
    norm_num
  -- the competing curve is at least as long as the radius gain
  have hRHS := hcomp w w' 0 1 (by norm_num) hwc hw hw'
    (fun t ht => (hwball t ht).trans_le (min_le_left _ _))
  rw [hw0, hw1, chartMetricInner_zero_left, Real.sqrt_zero, sub_zero] at hRHS
  rw [hLHS]
  exact hRHS

/-- **Math.** **Radial geodesics minimize among curves in a normal ball**
(do Carmo Ch. 3, Proposition 3.6, the case `c([0,1]) ⊂ B`). There is `ε > 0`
such that `exp_p` is injective on `B_ε(0) ⊂ T_pM` with open image (so
`B = exp_p(B_ε(0))` is a normal ball), and for every `v` with `‖v‖ < ε` and
every curve `c : [0, 1] → B` from `c(0) = p` to `c(1) = exp_p(v)` whose chart
reading `t ↦ φ_p(c(t))` is differentiable with continuous derivative `u'`,
the chart-read length of the radial geodesic `γ(t) = exp_p(t v)` is at most
the chart-read length of `c`:

`ℓ(γ) ≤ ∫_0^1 √⟨u'(t), u'(t)⟩_{c(t)} dt = ℓ(c)`.

The competing curve is put in polar form `c = exp_p ∘ w`,
`w = exp_p⁻¹ ∘ c` through the local `C¹` inverse of `exp_p`
(`exists_c1_local_diffeomorphism_expMap`), and the polar-form minimizing
property (`exists_minimizing_geodesic_ball`) applies; the chain rule and
uniqueness of one-sided derivatives on `[0, 1]` identify the two length
integrands. -/
theorem exists_minimizing_geodesic_normal_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ u : E, ‖u‖ < ε → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ε →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun z : E => expMap (I := I) g p (z : TangentSpace I p))
        (ball (0 : E) ε) ∧
      IsOpen ((fun z : E => expMap (I := I) g p (z : TangentSpace I p)) ''
        ball (0 : E) ε) ∧
      (∀ v : E, ‖v‖ < ε → ∀ (c : ℝ → M) (u' : ℝ → E),
        (∀ t ∈ Icc (0 : ℝ) 1, c t ∈
          (fun z : E => expMap (I := I) g p (z : TangentSpace I p)) ''
            ball (0 : E) ε) →
        (∀ t ∈ Icc (0 : ℝ) 1,
          HasDerivAt (fun τ : ℝ => extChartAt I p (c τ)) (u' t) t) →
        ContinuousOn u' (Icc (0 : ℝ) 1) →
        c 0 = p → c 1 = expMap (I := I) g p (v : TangentSpace I p) →
        (∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
            (extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
            (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (t • v) v)
            (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (t • v) v)))
          ≤ ∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (c t)) (u' t) (u' t))) := by
  classical
  obtain ⟨ε₁, hε₁, hdom₁, hsrc₁, hinj₁, hopenM₁, hfC1, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  obtain ⟨ρ, hρ, hdomρ, hsrcρ, hmin⟩ :=
    exists_minimizing_geodesic_ball (I := I) g p
  obtain ⟨ρe, hρe, hdome, hsrce, hequiv⟩ :=
    exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball (I := I) g p
  set f : E → E :=
    fun z => extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)) with hfdef
  set ε : ℝ := min ε₁ (min ρ ρe) with hεdef
  have hε : 0 < ε := lt_min hε₁ (lt_min hρ hρe)
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  have hερ : ε ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hερe : ε ≤ ρe := (min_le_right _ _).trans (min_le_right _ _)
  -- the chart image of the `ε`-ball is open: the derivative of the chart
  -- reading is an equivalence at every point of the ball
  have hopen_f : IsOpen (f '' ball (0 : E) ε) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨D', hD'⟩ := hequiv z ((mem_ball_zero_iff.mp hz).trans_le hερe)
    rw [← hD'.map_nhds_eq_of_equiv]
    exact image_mem_map (isOpen_ball.mem_nhds hz)
  -- the image of `exp_p` is the chart pull-back of the image of `f`
  have himg : (fun z : E => expMap (I := I) g p (z : TangentSpace I p)) ''
        ball (0 : E) ε
      = (extChartAt I p).source ∩ extChartAt I p ⁻¹' (f '' ball (0 : E) ε) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hsrcz : expMap (I := I) g p (z : TangentSpace I p) ∈
          (chartAt H p).source :=
        hsrc₁ z ((mem_ball_zero_iff.mp hz).trans_le hεε₁)
      exact ⟨by rw [extChartAt_source]; exact hsrcz, ⟨z, hz, rfl⟩⟩
    · rintro ⟨hxsrc, ⟨z, hz, hfz⟩⟩
      refine ⟨z, hz, ?_⟩
      have hsrcz : expMap (I := I) g p (z : TangentSpace I p) ∈
          (extChartAt I p).source := by
        rw [extChartAt_source]
        exact hsrc₁ z ((mem_ball_zero_iff.mp hz).trans_le hεε₁)
      exact (extChartAt I p).injOn hsrcz hxsrc hfz
  have hopen_exp : IsOpen ((fun z : E => expMap (I := I) g p
      (z : TangentSpace I p)) '' ball (0 : E) ε) := by
    rw [himg]
    exact (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_source p) hopen_f
  refine ⟨ε, hε, fun u hu => hdom₁ u (hu.trans_le hεε₁),
    fun u hu => hsrc₁ u (hu.trans_le hεε₁),
    hinj₁.mono (ball_subset_ball hεε₁), hopen_exp, ?_⟩
  intro v hv c u' hcball hu hu'_cont hc0 hc1
  -- the chart reading of the curve, and its polar lift through `finv`
  set u : ℝ → E := fun t => extChartAt I p (c t) with hudef
  set w : ℝ → E := fun t => finv (u t) with hwdef
  -- pointwise polar description: on `[0,1]`, `c t = exp_p (w t)` with
  -- `w t` in the `ε`-ball and `f (w t) = u t`
  have hpolar : ∀ t ∈ Icc (0 : ℝ) 1, w t ∈ ball (0 : E) ε ∧ f (w t) = u t := by
    intro t ht
    obtain ⟨z, hz, hcz⟩ := hcball t ht
    have hwz : w t = z := by
      rw [hwdef]
      show finv (u t) = z
      rw [hudef]
      show finv (extChartAt I p (c t)) = z
      rw [← hcz]
      exact hlinv z ((mem_ball_zero_iff.mp hz).trans_le hεε₁)
    constructor
    · rw [hwz]; exact hz
    · rw [hwz, hfdef]
      show extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)) = u t
      rw [hudef]
      show _ = extChartAt I p (c t)
      rw [← hcz]
  have hu_mem : ∀ t ∈ Icc (0 : ℝ) 1, u t ∈ f '' ball (0 : E) ε := by
    intro t ht
    obtain ⟨hwball, hfw⟩ := hpolar t ht
    exact ⟨w t, hwball, hfw⟩
  -- `finv` is `C¹` on the open set `f '' B_ε(0)`
  have hsub : f '' ball (0 : E) ε ⊆ f '' ball (0 : E) ε₁ :=
    image_mono (ball_subset_ball hεε₁)
  have hfinvC1' : ContDiffOn ℝ 1 finv (f '' ball (0 : E) ε) := hfinvC1.mono hsub
  have hfinv_diff : ∀ y ∈ f '' ball (0 : E) ε,
      HasFDerivAt finv (fderiv ℝ finv y) y := by
    intro y hy
    exact ((hfinvC1'.contDiffAt (hopen_f.mem_nhds hy)).differentiableAt
      one_ne_zero).hasFDerivAt
  -- the polar lift is differentiable, with continuous derivative
  have hw_deriv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt w (fderiv ℝ finv (u t) (u' t)) t := fun t ht =>
    (hfinv_diff (u t) (hu_mem t ht)).comp_hasDerivAt t (hu t ht)
  have hu_cont : ContinuousOn u (Icc (0 : ℝ) 1) := fun t ht =>
    (hu t ht).continuousAt.continuousWithinAt
  have hw'_cont : ContinuousOn (fun t => fderiv ℝ finv (u t) (u' t))
      (Icc (0 : ℝ) 1) := by
    have h1 : ContinuousOn (fun t => fderiv ℝ finv (u t)) (Icc (0 : ℝ) 1) :=
      (hfinvC1'.continuousOn_fderiv_of_isOpen hopen_f le_rfl).comp hu_cont
        (fun t ht => hu_mem t ht)
    exact h1.clm_apply hu'_cont
  have hw_ball : ∀ t ∈ Icc (0 : ℝ) 1, ‖w t‖ < ρ := fun t ht =>
    (mem_ball_zero_iff.mp (hpolar t ht).1).trans_le hερ
  -- endpoints of the polar lift
  have hw0 : w 0 = 0 := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
    have hf0 : f 0 = extChartAt I p p := by
      rw [hfdef]
      show extChartAt I p (expMap (I := I) g p ((0 : E) : TangentSpace I p)) = _
      exact congrArg (extChartAt I p) (expMap_zero (I := I) g p)
    rw [hwdef]
    show finv (u 0) = 0
    rw [hudef]
    show finv (extChartAt I p (c 0)) = 0
    rw [hc0, ← hf0]
    have := hlinv 0 (by rw [norm_zero]; exact hε₁)
    exact this
  have hw1 : w 1 = v := by
    rw [hwdef]
    show finv (u 1) = v
    rw [hudef]
    show finv (extChartAt I p (c 1)) = v
    rw [hc1]
    exact hlinv v (hv.trans_le hεε₁)
  -- the polar-form minimizing property
  have hw_cont : ContinuousOn w (Icc (0 : ℝ) 1) := fun t ht =>
    (hw_deriv t ht).continuousAt.continuousWithinAt
  have hcore := hmin v (hv.trans_le hερ) w (fun t => fderiv ℝ finv (u t) (u' t))
    hw_cont (fun t ht => hw_deriv t (Ioo_subset_Icc_self ht)) hw'_cont hw_ball hw0 hw1
  -- identify the competing integrand with the chart-read length of `c`
  have hIcc : Icc (0 : ℝ) 1 = uIcc (0 : ℝ) 1 :=
    (uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)).symm
  have hEq : EqOn
      (fun t : ℝ => Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
        (fderiv ℝ (fun z : E =>
          extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (w t)
          (fderiv ℝ finv (u t) (u' t)))
        (fderiv ℝ (fun z : E =>
          extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (w t)
          (fderiv ℝ finv (u t) (u' t)))))
      (fun t : ℝ => Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p (c t)) (u' t) (u' t)))
      (uIcc (0 : ℝ) 1) := by
    intro t ht
    rw [← hIcc] at ht
    obtain ⟨hwball, hfw⟩ := hpolar t ht
    -- the foot: `exp_p (w t) = c t` in the chart
    have hfoot : extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p))
        = extChartAt I p (c t) := hfw
    -- the velocity: `d f (w t) (w' t) = u' t` by uniqueness of the
    -- one-sided derivative of `u = f ∘ w` on `[0, 1]`
    have hf_diff : HasFDerivAt f (fderiv ℝ f (w t)) (w t) := by
      have hball₁ : w t ∈ ball (0 : E) ε₁ := ball_subset_ball hεε₁ hwball
      exact ((hfC1.contDiffAt (isOpen_ball.mem_nhds hball₁)).differentiableAt
        one_ne_zero).hasFDerivAt
    have h2 : HasDerivAt (fun s => f (w s))
        (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t))) t :=
      hf_diff.comp_hasDerivAt t (hw_deriv t ht)
    have h2' : HasDerivWithinAt u
        (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t))) (Icc (0 : ℝ) 1) t := by
      refine (h2.hasDerivWithinAt).congr ?_ (hpolar t ht).2.symm
      intro s hs
      exact ((hpolar s hs).2).symm
    have h1' : HasDerivWithinAt u (u' t) (Icc (0 : ℝ) 1) t :=
      (hu t ht).hasDerivWithinAt
    have huniq : fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t)) = u' t :=
      (uniqueDiffOn_Icc (zero_lt_one : (0 : ℝ) < 1) t ht).eq_deriv
        _ h2' h1'
    show Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
        (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t)))
        (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t))))
      = Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p (c t)) (u' t) (u' t))
    rw [hfoot, huniq]
  calc (∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
        (fderiv ℝ (fun z : E =>
          extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (t • v) v)
        (fderiv ℝ (fun z : E =>
          extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (t • v) v)))
      ≤ ∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
          (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (w t)
            (fderiv ℝ finv (u t) (u' t)))
          (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (w t)
            (fderiv ℝ finv (u t) (u' t)))) := hcore
    _ = ∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p (c t)) (u' t) (u' t)) :=
        intervalIntegral.integral_congr hEq

end Exponential
end Riemannian

end
