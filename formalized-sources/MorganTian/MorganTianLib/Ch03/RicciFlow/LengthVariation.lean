import MorganTianLib.Ch03.RicciFlow.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Time variation of the length of a fixed curve

Supporting results for Claim 3.23. The length here is the integral of the
actual Riemannian speed, with the curve held fixed while the metric varies.
These results do not assert compactness of minimizing geodesics for varying
metrics; that is a separate geometric step in Claim 3.23.
-/

open scoped Topology Manifold ContDiff Interval Bundle ENNReal
open Set Filter MeasureTheory Riemannian Bundle

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

/-- **Math.** Joint continuity on a compact rectangle supplies the uniform integrable
bound needed to differentiate the integral in its time parameter. -/
theorem hasDerivAt_intervalIntegral_of_continuousOn
    {F F' : ℝ → ℝ → ℝ} {l r a b t : ℝ} (ht : t ∈ Ioo l r)
    (hF : ContinuousOn (Function.uncurry F) (Icc l r ×ˢ uIcc a b))
    (hF' : ContinuousOn (Function.uncurry F') (Icc l r ×ˢ uIcc a b))
    (hd : ∀ s ∈ Ioo l r, ∀ u ∈ uIcc a b, HasDerivAt (fun s => F s u) (F' s u) s) :
    HasDerivAt (fun s => ∫ u in a..b, F s u) (∫ u in a..b, F' t u) t := by
  have hc (s : ℝ) (hs : s ∈ Icc l r) : ContinuousOn (F s) (uIcc a b) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun u hu => ⟨hs, hu⟩)
  have hc' : ContinuousOn (F' t) (uIcc a b) :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨⟨ht.1.le, ht.2.le⟩, hu⟩)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hF'
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := Ioo l r) (bound := fun _ => B)
    (Ioo_mem_nhds ht.1 ht.2) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact ((hc s ⟨hs.1.le, hs.2.le⟩).mono uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · exact (hc t ⟨ht.1.le, ht.2.le⟩).intervalIntegrable
  · exact (hc'.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact Eventually.of_forall fun u hu s hs => hB (s, u)
      ⟨⟨hs.1.le, hs.2.le⟩, uIoc_subset_uIcc hu⟩
  · exact Eventually.of_forall fun u hu s hs => hd s hs u (uIoc_subset_uIcc hu)

section Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The real-valued speed of a parametrized curve in an explicit metric. -/
def metricCurveNorm (g : RiemannianMetric I M) (c : ℝ → M) (u : ℝ) : ℝ :=
  Real.sqrt (g.metricInner (c u)
    (mfderiv 𝓘(ℝ, ℝ) I c u (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I c u (1 : ℝ)))

/-- **Math.** The real-valued Riemannian length, oriented from `a` to `b`. For `a ≤ b`
and a regular smooth curve this is the usual nonnegative length. -/
def metricCurveLengthReal (g : RiemannianMetric I M) (c : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ u in a..b, metricCurveNorm g c u

/-- **Math.** Time differentiation of the speed of a fixed, regular curve under the
Ricci flow equation. The vector is held fixed in the tangent space at `c u`. -/
theorem hasDerivAt_metricCurveNorm_of_isRicciFlowEquationOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowEquationOn g J)
    {c : ℝ → M} {u t : ℝ} (ht : J ∈ 𝓝 t)
    (hv : mfderiv 𝓘(ℝ, ℝ) I c u (1 : ℝ) ≠ 0) :
    HasDerivAt (fun s => metricCurveNorm (g s) c u)
      (-ricciTensorAt (g t) (c u) (mfderiv 𝓘(ℝ, ℝ) I c u (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I c u (1 : ℝ)) / metricCurveNorm (g t) c u) t := by
  have hpos := (g t).metricInner_self_pos (c u) _ hv
  have h := ((hg t (mem_of_mem_nhds ht) (c u) _ _).hasDerivAt ht).sqrt (ne_of_gt hpos)
  convert h using 1 <;> simp only [metricCurveNorm]
  ring

/-- **Math.** The time-variation integrand for the length of a fixed curve under
Ricci flow. It is evaluated only on regular curves in the derivative results. -/
def metricCurveNormTimeDeriv (g : RiemannianMetric I M) (c : ℝ → M) (u : ℝ) : ℝ :=
  -ricciTensorAt g (c u) (mfderiv 𝓘(ℝ, ℝ) I c u (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) I c u (1 : ℝ)) / metricCurveNorm g c u

/-- **Math.** The constant curve has zero length in every metric. -/
theorem metricCurveLengthReal_const (g : RiemannianMetric I M) (x : M) :
    metricCurveLengthReal g (fun _ : ℝ => x) 0 1 = 0 := by
  simp [metricCurveLengthReal, metricCurveNorm, mfderiv_const,
    RiemannianMetric.metricInner_apply]

end Riemannian

end MorganTianLib
