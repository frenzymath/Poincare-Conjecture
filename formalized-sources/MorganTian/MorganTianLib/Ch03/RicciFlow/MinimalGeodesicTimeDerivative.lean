import MorganTianLib.Ch03.RicciFlow.CutoffLengthDerivative

/-! # Morgan--Tian Claim 3.24: minimal geodesic time derivative

The Ricci upper bound is required only in the two open endpoint balls at
the initial time. Geodesic minimality supplies the cutoff index inequality;
Ricci flow supplies the actual time derivative of the fixed curve length.
The right derivative formulation also includes initial times of the flow.
-/

open Set Filter Riemannian Riemannian.Geodesic Module MeasureTheory
open scoped ContDiff Manifold Topology Bundle
noncomputable section
namespace MorganTianLib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [T3Space M] [ConnectedSpace M]
  [T2Space (TangentBundle I M)]

/-- **Math.** A positive-length geodesic has nonzero velocity everywhere. -/
theorem geodesic_velocity_ne_zero_of_length_pos
    {g : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g γ) (hcγ : Continuous γ)
    (hL : 0 < metricCurveLengthReal g γ 0 1) (s : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) ≠ 0 := by
  intro hz
  have hs := metricCurveNorm_geodesic_eq_length hγ hcγ s
  simp [metricCurveNorm, hz, RiemannianMetric.metricInner_apply] at hs
  linarith

/-- **Math.** **Claim 3.24**, including initial times. For a minimizing
geodesic of length at least `2r`, the upper Ricci bound `(n-1)K` in the two
open endpoint balls implies the stated lower right length derivative.
Completeness is only needed at the time at which the geodesic minimizes. -/
theorem minimal_geodesic_time_derivative_right
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {t₀ b K r : ℝ} (htb : t₀ < b) (hwindow : Icc t₀ b ⊆ J)
    (hcomplete : IsCompleteMetric (g t₀)) (x y : M) (hr : 0 < r)
    (hd : 2 * r ≤ metricDistanceReal (g t₀) x y)
    (hRic : ∀ p : M, metricDistanceReal (g t₀) x p < r ∨
        metricDistanceReal (g t₀) y p < r → ∀ v : TangentSpace I p,
      ricciTensorAt (g t₀) p v v ≤ ((finrank ℝ E : ℝ) - 1) * K * (g t₀).metricInner p v v)
    {γ : ℝ → M} (hγ0 : γ 0 = x) (hγ1 : γ 1 = y)
    (hγ : IsGeodesic (g t₀) γ) (hcγ : Continuous γ)
    (hmin : metricCurveLengthReal (g t₀) γ 0 1 = metricDistanceReal (g t₀) x y) :
    -2 * ((finrank ℝ E : ℝ) - 1) * (2 / 3 * K * r + r⁻¹) ≤
      derivWithin (fun t => metricCurveLengthReal (g t) γ 0 1) (Ici t₀) t₀ := by
  let L := metricCurveLengthReal (g t₀) γ 0 1
  have hshort : 2 * r ≤ L := by simpa only [L, hmin] using hd
  have hL : 0 < L := lt_of_lt_of_le (by positivity : 0 < 2 * r) hshort
  have hv := geodesic_velocity_ne_zero_of_length_pos hγ hcγ hL
  letI : MetricSpace M := canonicalMetricSpace (g t₀)
  letI : CompleteSpace M := hcomplete
  have hdist := canonicalMetricSpace_isRiemannianDist (g t₀)
  have hspeed (s : ℝ) : Real.sqrt (speedSq (I := I) (g t₀) γ s) = L :=
    metricCurveNorm_geodesic_eq_length hγ hcγ s
  have hminimal : Real.sqrt (speedSq (I := I) (g t₀) γ 0) ≤ dist (γ 0) (γ 1) := by
    rw [hspeed, hγ0, hγ1]
    exact le_of_eq hmin
  have hsecond := hasGeodesicCutoffSecondVariation_of_minimizing (g t₀) hdist
    hγ hcγ hminimal (hv (-1))
  apply length_derivWithin_ge_of_cutoff_secondVariation_along hg htb hwindow
    hγ hcγ hr hshort ?_ hsecond
  intro s hs
  apply hRic (γ s) ?_
  rcases hs with hs | hs
  · left
    have hle := (hγ.isGeodesicOn univ).dist_le (g t₀) hdist isOpen_univ
      isPreconnected_univ hcγ.continuousOn (mem_univ 0) (mem_univ s) hs.1
    rw [hspeed, sub_zero, hγ0] at hle
    change dist x (γ s) < r
    exact hle.trans_lt (by
      have hlt := (lt_div_iff₀ hL).mp hs.2
      nlinarith)
  · right
    have hle := (hγ.isGeodesicOn univ).dist_le (g t₀) hdist isOpen_univ
      isPreconnected_univ hcγ.continuousOn (mem_univ s) (mem_univ 1) hs.2
    rw [hspeed, hγ1, dist_comm] at hle
    change dist y (γ s) < r
    exact hle.trans_lt (by
      have hlt : 1 - s < r / L := by linarith [hs.1]
      have hlt' := (lt_div_iff₀ hL).mp hlt
      nlinarith)

/-- **Math.** **Claim 3.24** with the ordinary derivative at an interior
time of the flow. The existence of this derivative follows from Ricci flow
and the regularity of a positive-length geodesic. -/
theorem minimal_geodesic_time_derivative
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {t₀ K r : ℝ} (ht₀ : t₀ ∈ interior J)
    (hcomplete : IsCompleteMetric (g t₀)) (x y : M) (hr : 0 < r)
    (hd : 2 * r ≤ metricDistanceReal (g t₀) x y)
    (hRic : ∀ p : M, metricDistanceReal (g t₀) x p < r ∨
        metricDistanceReal (g t₀) y p < r → ∀ v : TangentSpace I p,
      ricciTensorAt (g t₀) p v v ≤ ((finrank ℝ E : ℝ) - 1) * K * (g t₀).metricInner p v v)
    {γ : ℝ → M} (hγ0 : γ 0 = x) (hγ1 : γ 1 = y)
    (hγ : IsGeodesic (g t₀) γ) (hcγ : Continuous γ)
    (hmin : metricCurveLengthReal (g t₀) γ 0 1 = metricDistanceReal (g t₀) x y) :
    -2 * ((finrank ℝ E : ℝ) - 1) * (2 / 3 * K * r + r⁻¹) ≤
      deriv (fun t => metricCurveLengthReal (g t) γ 0 1) t₀ := by
  obtain ⟨a, b, htI, hIJ⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (isOpen_interior.mem_nhds ht₀)
  have hwindow : Icc t₀ ((t₀ + b) / 2) ⊆ J := by
    intro t ht
    apply interior_subset (hIJ ?_)
    constructor <;> linarith [htI.1, htI.2, ht.1, ht.2]
  have hL : 0 < metricCurveLengthReal (g t₀) γ 0 1 := by rw [hmin]; linarith
  have hderiv := hasDerivAt_metricCurveLengthReal_geodesic (a := 0) (b := 1) hg hγ hcγ
    (fun s _ => geodesic_velocity_ne_zero_of_length_pos hγ hcγ hL s) ht₀
  have hbound := minimal_geodesic_time_derivative_right hg
    (by linarith [htI.2] : t₀ < (t₀ + b) / 2) hwindow hcomplete x y hr hd hRic hγ0 hγ1 hγ hcγ hmin
  rwa [hderiv.differentiableAt.derivWithin (uniqueDiffWithinAt_Ici t₀)] at hbound

end MorganTianLib
