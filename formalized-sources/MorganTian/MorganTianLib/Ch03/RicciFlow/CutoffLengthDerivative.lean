import MorganTianLib.Ch03.RicciFlow.MetricTimeBoundary
import MorganTianLib.Ch03.RicciFlow.GeodesicCutoffIndex

/-! # Endpoint cutoff bounds for the time derivative of geodesic length

Supporting lemmas for Morgan--Tian Claim 3.24. The physical cutoff radius is
converted to the constant-speed parameter, and Ricci flow supplies the
right derivative of the actual curve length, including at initial times.
-/

open scoped Topology Manifold ContDiff Interval Bundle
open Set Filter Riemannian Riemannian.Geodesic MeasureTheory

noncomputable section
namespace MorganTianLib
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The speed of a unit-interval geodesic is its length at every
parameter, not just at the initial point. -/
theorem metricCurveNorm_geodesic_eq_length
    {g : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g γ)
    (hcγ : Continuous γ) (s : ℝ) :
    metricCurveNorm g γ s = metricCurveLengthReal g γ 0 1 := by
  rw [metricCurveLengthReal_geodesic_eq_norm hγ hcγ]
  exact congrArg Real.sqrt ((hγ.isGeodesicOn univ).speedSq_eq
    isOpen_univ isPreconnected_univ hcγ.continuousOn (mem_univ s) (mem_univ 0))

/-- **Math.** The endpoint Ricci bounds and the cutoff index inequality give
the length-derivative estimate. Only the half-open endpoint parameter
intervals are used; continuity extends the bound to the cutoff corners.
The parameter radius is converted to physical radius, and the actual
right length derivative is derived from the Ricci-flow equation. -/
theorem length_derivWithin_ge_of_cutoff_secondVariation_along
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {t₀ b N K r : ℝ} (htb : t₀ < b) (hwindow : Icc t₀ b ⊆ J)
    {γ : ℝ → M} (hγ : IsGeodesic (g t₀) γ) (hcγ : Continuous γ)
    (hr : 0 < r) (hshort : 2 * r ≤ metricCurveLengthReal (g t₀) γ 0 1)
    (hRic : ∀ s ∈ Ico (0 : ℝ) (r / metricCurveLengthReal (g t₀) γ 0 1) ∪
        Ioc (1 - r / metricCurveLengthReal (g t₀) γ 0 1) 1,
      metricCurveRicci (g t₀) γ s ≤ N * K * (g t₀).metricInner (γ s)
        (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)))
    (hsecond : HasGeodesicCutoffSecondVariation (g t₀) γ N) :
    -2 * N * (2 / 3 * K * r + r⁻¹) ≤
      derivWithin (fun t => metricCurveLengthReal (g t) γ 0 1) (Ici t₀) t₀ := by
  let L := metricCurveLengthReal (g t₀) γ 0 1
  have hL : 0 < L := lt_of_lt_of_le (by positivity : 0 < 2 * r) hshort
  have hnorm (s : ℝ) : metricCurveNorm (g t₀) γ s = L :=
    metricCurveNorm_geodesic_eq_length hγ hcγ s
  have hv (s : ℝ) : mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) ≠ 0 := by
    intro hz
    have hs := hnorm s
    simp [metricCurveNorm, hz, RiemannianMetric.metricInner_apply] at hs
    linarith
  have hD : Continuous (metricCurveNormTimeDeriv (g t₀) γ) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact continuousAt_normTimeDeriv_withinTime hg htb hwindow hγ hcγ
      ⟨le_rfl, htb.le⟩ (hv s)
  have hq (s : ℝ) : metricCurveRicci (g t₀) γ s =
      -metricCurveNormTimeDeriv (g t₀) γ s * L := by
    unfold metricCurveNormTimeDeriv metricCurveRicci
    rw [hnorm]
    field_simp [ne_of_gt hL]
  have hcont : Continuous (metricCurveRicci (g t₀) γ) := by
    change Continuous (fun s => metricCurveRicci (g t₀) γ s)
    simp_rw [hq]
    exact hD.neg.mul_const L
  have hbound (s : ℝ) (hs : s ∈ Ico (0 : ℝ) (r / L) ∪ Ioc (1 - r / L) 1) : metricCurveRicci (g t₀) γ s ≤ N * (K * L ^ 2) := by
    have hsq : (g t₀).metricInner (γ s)
        (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) = L ^ 2 := by
      rw [← Real.sq_sqrt ((g t₀).metricInner_self_nonneg _ _)]
      change metricCurveNorm (g t₀) γ s ^ 2 = L ^ 2
      rw [hnorm]
    have h := hRic s hs
    rw [hsq] at h
    simpa only [metricCurveRicci, mul_assoc] using h
  have hρ : 0 < r / L := div_pos hr hL
  have hρlen : 2 * (r / L) ≤ 1 := by
    rw [← mul_div_assoc, div_le_iff₀ hL, one_mul]
    exact hshort
  have hcut := lowerBound_of_cutoff_secondVariation (N := N) (K := K * L ^ 2)
    hρ hρlen hcont.continuousOn hcont.continuousOn
    (fun s hs => le_on_closure (fun u hu => hbound u (Or.inl hu))
      hcont.continuousOn continuousOn_const (by rwa [closure_Ico (ne_of_lt hρ)]))
    (fun s hs => le_on_closure (fun u hu => hbound u (Or.inr hu))
      hcont.continuousOn continuousOn_const
      (by rwa [closure_Ioc (show 1 - r / L ≠ 1 by linarith)])) (hsecond _ hρ hρlen)
  have hdiv := div_le_div_of_nonneg_right hcut hL.le
  have hcoeff : (-2 * N * (2 / 3 * (K * L ^ 2) * (r / L) + (r / L)⁻¹)) / L =
      -2 * N * (2 / 3 * K * r + r⁻¹) := by
    field_simp [ne_of_gt hL, ne_of_gt hr]
  rw [hcoeff] at hdiv
  rw [(hasDerivWithinAt_length_geodesic_right hg htb hwindow hγ hcγ
    (fun s _ => hv s)).derivWithin (uniqueDiffWithinAt_Ici t₀)]
  have hderiv (s : ℝ) : metricCurveNormTimeDeriv (g t₀) γ s =
      -metricCurveRicci (g t₀) γ s / L := by
    unfold metricCurveNormTimeDeriv metricCurveRicci
    rw [hnorm]
  simp_rw [hderiv]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_neg]
  exact hdiv

end MorganTianLib
