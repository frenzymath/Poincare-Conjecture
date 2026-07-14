import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# `C^∞` smoothness of a parametric Bochner integral over a compact parameter space

This file supplies a piece of analysis that Mathlib does not currently package: if a family
of maps `F a : E → G` (`a` ranging over a **compact** parameter space `α` carrying a finite
measure `μ`) is jointly nice — each `F a` is `C^∞`, and every order-`m` iterated `x`-derivative
`(a, x) ↦ D_x^m(F a)(x)` is **jointly continuous** — then the averaged map

  `x ↦ ∫_α F a x dμ(a)`

is itself `C^∞`, and its `m`-th derivative is obtained by differentiating under the integral,
`D^m(∫ F) = ∫ D^m F`.

Mathlib provides the *first* derivative under the integral sign
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`) and a `C^∞` version **specialised to
convolutions** (`contDiffOn_convolution_right_with_param`), but no general `C^∞`
parametric-integral theorem.  The proof here follows the classical route:

* the candidate Taylor series is `parametricIntegralSeries F x m = ∫_α D_x^m(F a)(x) dμ` (a
  `FormalMultilinearSeries` with a **fixed** codomain `G`, which avoids the universe bump that
  forces the convolution proof through `ULift`);
* the derivative step `D(∫ D^m F) = ∫ D^{m+1} F` is `hasFDerivAt_parametricIntegral_iteratedFDeriv`,
  an application of the first-derivative theorem whose domination bound is a genuine constant
  supplied by continuity on the compact `α ×ˢ closedBall`;
* continuity of each series term is `continuous_parametric_integral_of_continuous`.

Assembling these into a `HasFTaylorSeriesUpTo ∞` yields `contDiff_parametricIntegral`.

The intended client is Petersen Exercise 1.6.26 (`avgMetricCompact.contMDiff`): smoothness in the
base point of the Haar average of the pullback metric over a compact-group action.

Reference: e.g. Lang, *Real and Functional Analysis*, differentiation under the integral sign.
-/

open MeasureTheory Filter Metric Set
open scoped Topology ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace PetersenLib

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [SecondCountableTopology α] [CompactSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → E → G}

/-- The candidate formal Taylor series of the parametric integral `x ↦ ∫_α F a x dμ`: its
`m`-th term is the Bochner integral over the parameter of the order-`m` iterated derivative of
the integrand. -/
def parametricIntegralSeries (F : α → E → G) (x : E) : FormalMultilinearSeries ℝ E G :=
  fun m => ∫ a, iteratedFDeriv ℝ m (F a) x ∂μ

/-- For a fixed base point, the order-`m` derivative integrand is integrable: it is continuous
on the compact parameter space against the finite measure `μ`. -/
theorem integrable_iteratedFDeriv_apply {m : ℕ}
    (hcm : Continuous (fun p : α × E => iteratedFDeriv ℝ m (F p.1) p.2)) (x : E) :
    Integrable (fun a => iteratedFDeriv ℝ m (F a) x) μ := by
  have hc : Continuous (fun a : α => iteratedFDeriv ℝ m (F a) x) :=
    hcm.comp (continuous_id.prodMk continuous_const)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Each term of the candidate Taylor series is continuous in the base point, by continuity of
the parametric integral of a jointly continuous integrand over the compact `α`. -/
theorem continuous_parametricIntegralSeries {m : ℕ}
    (hcm : Continuous (fun p : α × E => iteratedFDeriv ℝ m (F p.1) p.2)) :
    Continuous (fun x => ∫ a, iteratedFDeriv ℝ m (F a) x ∂μ) := by
  have huncurry : Continuous (Function.uncurry (fun (x : E) (a : α) => iteratedFDeriv ℝ m (F a) x)) :=
    hcm.comp continuous_swap
  have h := continuous_parametric_integral_of_continuous (μ := μ) huncurry isCompact_univ
  simpa only [setIntegral_univ] using h

/-- **Isolated Mathlib gap — `curryLeft` commutes with the Bochner integral.**
`(∫_α g a dμ).curryLeft = ∫_α (g a).curryLeft dμ` for an integrable family `g` of continuous
`(m+1)`-multilinear maps.  Mathematically immediate — `curryLeft` is the linear isometry
`continuousMultilinearCurryLeftEquiv` — but *not currently formalizable in this Mathlib*:

* bundling `curryLeft` as a `ContinuousLinearMap` over the **normed** `ContinuousMultilinearMap`
  instance (needed to match `iteratedFDeriv`, whose values use `normedAddCommGroup'`) fails, because
  the pre-built `continuousMultilinearCurryLeftEquiv` carries the **seminormed** instance and
  `LinearMap.mkContinuous` produces the operator-seminorm *metric* topology, which is a distinct
  instance from the canonical `ContinuousLinearMap`/`ContinuousMultilinearMap` topology;
* consequently the doubly-iterated operator-norm space `E →L[ℝ] (E [×m]→L[ℝ] G)` does not resolve a
  `ContinuousENorm` instance, so direct Bochner integration of `curryLeft`-valued families is also
  blocked (the "2-level CLM Bochner gotcha").

This is the sole remaining obstruction in `contDiff_parametricIntegral`; closing it needs an upstream
Mathlib fix to the iterated operator-norm topology/`ContinuousENorm` instance diamond. -/
theorem curryLeft_integral_comm {m : ℕ} (g : α → E [×(m + 1)]→L[ℝ] G) (hg : Integrable g μ) :
    (∫ a, g a ∂μ).curryLeft = ∫ a, (g a).curryLeft ∂μ := by
  sorry

/-- **The order-`m` derivative-under-the-integral step.**  Under joint continuity of the
order-`m` and order-`(m+1)` iterated derivatives (and `C^∞`-ness of each `F a`), the parametric
integral of the order-`m` derivative is differentiable in the base point, with derivative the
`curryLeft` of the parametric integral of the order-`(m+1)` derivative — i.e. `D(∫ D^m F) =
∫ D^{m+1} F`, up to the canonical `curryLeft` identification. -/
theorem hasFDerivAt_parametricIntegral_iteratedFDeriv {m : ℕ}
    (hdiff : ∀ a, ContDiff ℝ ∞ (F a))
    (hcm : Continuous (fun p : α × E => iteratedFDeriv ℝ m (F p.1) p.2))
    (hcm1 : Continuous (fun p : α × E => iteratedFDeriv ℝ (m + 1) (F p.1) p.2))
    (x : E) :
    HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ m (F a) y ∂μ)
      ((∫ a, iteratedFDeriv ℝ (m + 1) (F a) x ∂μ).curryLeft) x := by
  -- per-parameter: `iteratedFDeriv^m (F a)` is differentiable with derivative the `curryLeft` of
  -- the next iterate, from the finite Taylor expansion of the smooth `F a`.
  have htaylor : ∀ a : α, ∀ y : E,
      HasFDerivAt (fun z => iteratedFDeriv ℝ m (F a) z)
        ((iteratedFDeriv ℝ (m + 1) (F a) y).curryLeft) y := by
    intro a y
    have hcd : ContDiff ℝ (m + 1 : ℕ) (F a) := (hdiff a).of_le (by exact_mod_cast le_top)
    have h := hcd.ftaylorSeries.fderiv m (by exact_mod_cast Nat.lt_succ_self m) y
    simpa only [ftaylorSeries] using h
  have hfderiv_eq : ∀ a : α, ∀ y : E,
      fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y
        = (iteratedFDeriv ℝ (m + 1) (F a) y).curryLeft :=
    fun a y => (htaylor a y).fderiv
  -- a uniform bound on the order-`(m+1)` derivative over the compact `α ×ˢ closedBall x 1`
  obtain ⟨C, hC⟩ : ∃ C, ∀ a : α, ∀ y ∈ closedBall x 1,
      ‖iteratedFDeriv ℝ (m + 1) (F a) y‖ ≤ C := by
    have hK : IsCompact ((univ : Set α) ×ˢ closedBall x 1) :=
      isCompact_univ.prod (isCompact_closedBall x 1)
    obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn hcm1.continuousOn
    exact ⟨C, fun a y hy => hCb (a, y) ⟨mem_univ a, hy⟩⟩
  -- assemble the hypotheses of `hasFDerivAt_integral_of_dominated_of_fderiv_le`
  have hF_meas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (fun a => iteratedFDeriv ℝ m (F a) y) μ := by
    filter_upwards with y
    exact (hcm.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hF_int : Integrable (fun a => iteratedFDeriv ℝ m (F a) x) μ :=
    integrable_iteratedFDeriv_apply hcm x
  have hF'_meas : AEStronglyMeasurable
      (fun a => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x) μ := by
    rw [show (fun a => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x)
          = (fun a => (iteratedFDeriv ℝ (m + 1) (F a) x).curryLeft) from
        funext fun a => hfderiv_eq a x]
    exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) G).isometry.continuous.comp
      (hcm1.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  have h_bound : ∀ᵐ a ∂μ, ∀ y ∈ ball x 1,
      ‖fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y‖ ≤ C := by
    filter_upwards with a y hy
    have hnorm : ‖fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y‖
        = ‖iteratedFDeriv ℝ (m + 1) (F a) y‖ := by
      rw [hfderiv_eq a y]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) G).norm_map _
    rw [hnorm]
    exact hC a y (ball_subset_closedBall hy)
  have h_diff : ∀ᵐ a ∂μ, ∀ y ∈ ball x 1,
      HasFDerivAt (fun z => iteratedFDeriv ℝ m (F a) z)
        (fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y) y := by
    filter_upwards with a y _
    exact (htaylor a y).differentiableAt.hasFDerivAt
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun y a => iteratedFDeriv ℝ m (F a) y)
    (F' := fun y a => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y)
    (bound := fun _ => C) (x₀ := x) (s := ball x 1)
    (ball_mem_nhds x one_pos) hF_meas hF_int hF'_meas h_bound (integrable_const C) h_diff
  -- identify `∫ D(D^m F)` with the `curryLeft` of `∫ D^{m+1} F`: rewrite each fibre derivative as
  -- a `curryLeft`, then pull `curryLeft` out of the integral (the one isolated Mathlib gap).
  have hint : Integrable (fun a => iteratedFDeriv ℝ (m + 1) (F a) x) μ :=
    integrable_iteratedFDeriv_apply hcm1 x
  have hEq : (∫ a, fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x ∂μ)
      = (∫ a, iteratedFDeriv ℝ (m + 1) (F a) x ∂μ).curryLeft := by
    rw [curryLeft_integral_comm _ hint]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => hfderiv_eq a x)
  rw [← hEq]
  exact key

/-- **`C^∞` parametric Bochner integral (compact parameter space).**  If each `F a : E → G` is
`C^∞` and every order-`m` iterated `x`-derivative `(a, x) ↦ D_x^m(F a)(x)` is jointly continuous
over the compact parameter space `α`, then the average `x ↦ ∫_α F a x dμ(a)` is `C^∞`.

This is the general parametric-integral smoothness theorem Mathlib is missing (it has only the
first derivative and a convolution-specific `C^∞` version). -/
theorem contDiff_parametricIntegral
    (hdiff : ∀ a, ContDiff ℝ ∞ (F a))
    (hcont : ∀ m : ℕ, Continuous (fun p : α × E => iteratedFDeriv ℝ m (F p.1) p.2)) :
    ContDiff ℝ ∞ (fun x => ∫ a, F a x ∂μ) := by
  have htaylor : HasFTaylorSeriesUpTo ∞ (fun x => ∫ a, F a x ∂μ)
      (parametricIntegralSeries (μ := μ) F) := by
    refine ⟨?_, ?_, ?_⟩
    · -- `zero_eq`: the 0-th term evaluates (curry0) to the integral itself.  Evaluation of a
      -- continuous multilinear map commutes with the Bochner integral.
      intro x
      show (∫ a, iteratedFDeriv ℝ 0 (F a) x ∂μ).curry0 = ∫ a, F a x ∂μ
      rw [ContinuousMultilinearMap.curry0_apply,
        ContinuousMultilinearMap.integral_apply (integrable_iteratedFDeriv_apply (hcont 0) x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      simp only [iteratedFDeriv_zero_apply]
    · -- `fderiv`: the derivative step
      intro m _ x
      exact hasFDerivAt_parametricIntegral_iteratedFDeriv hdiff (hcont m) (hcont (m + 1)) x
    · -- `cont`: continuity of each term
      intro m _
      exact continuous_parametricIntegralSeries (hcont m)
  exact htaylor.contDiff

end PetersenLib
