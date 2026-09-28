import MorganTianLib.Ch03.RicciFlow.DistanceVariationVariableBound
import MorganTianLib.Ch03.RicciFlow.MetricDistortion

/-!
# Morgan--Tian Ch. 3 - integrated distance-variation bounds

This file records the one-dimensional integration step behind the distance
integral bound.  The geometric Ricci-flow estimate supplies the lower
forward-Dini bound; the theorem below integrates a time-dependent bound on a
compact interval.
-/

open Filter Real Set Function
open scoped Topology

noncomputable section

namespace MorganTianLib

/-- **Math.** A continuous time-dependent lower forward-Dini bound integrates
to the corresponding endpoint estimate.  This is the regularity level used
by the distance estimate with a continuous curvature coefficient; unlike the
`ContDiff` variant below, no derivative of the coefficient itself is needed.
-/
theorem lowerEndpointBound_of_forwardDiffQuotientGE_of_continuous
    {f C : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hC : Continuous C)
    (hfd : ∀ t ∈ Ico a b,
      ForwardDiffQuotientGE f t (-C t)) :
    f a ≤ f b + ∫ t in a..b, C t := by
  let F : ℝ → ℝ := fun t => -f t
  let G : ℝ → ℝ := fun t => -f a + ∫ s in a..t, C s
  have hF : ContinuousOn F (Icc a b) := by
    change ContinuousOn (fun t => -f t) (Icc a b)
    exact hf.neg
  have hfdF : ∀ t ∈ Ico a b, ForwardDiffQuotientLE F t (C t) := by
    intro t ht
    have h := ForwardDiffQuotientGE.to_neg (hfd t ht)
    simpa [F] using h
  have hG : ContinuousOn G (Icc a b) := by
    intro t ht
    have hprim : HasDerivAt (fun u : ℝ => ∫ s in a..u, C s) (C t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hC.intervalIntegrable a t)
        (hC.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 t))
        hC.continuousAt
    exact (hprim.const_add (-f a)).continuousAt.continuousWithinAt
  have hG' : ∀ t ∈ Ico a b,
      HasDerivWithinAt G (C t) (Ici t) t := by
    intro t ht
    have hprim : HasDerivAt (fun u : ℝ => ∫ s in a..u, C s) (C t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hC.intervalIntegrable a t)
        (hC.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 t))
        hC.continuousAt
    simpa [G] using (hprim.const_add (-f a)).hasDerivWithinAt
  have hcomp : ∀ t ∈ Icc a b, F t ≤ G t := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary
      (f := F) (a := a) (b := b) hF
    · dsimp [F, G]
      simp
    · exact hG
    · exact hG'
    · intro t ht r hr
      exact (hfdF t ht r hr).frequently
  have hb := hcomp b ⟨hab, le_rfl⟩
  dsimp [F, G] at hb
  linarith

/-- **Math.** A continuous time-dependent lower forward-Dini bound integrates
to the corresponding interval-integral endpoint estimate. -/
theorem lowerEndpointBound_of_forwardDiffQuotientGE_of_contDiff
    {f C : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hC : ContDiff ℝ 1 C)
    (hfd : ∀ t ∈ Ico a b,
      ForwardDiffQuotientGE f t (-C t)) :
    f a ≤ f b + ∫ t in a..b, C t := by
  exact lowerEndpointBound_of_forwardDiffQuotientGE_of_continuous hab hf
    hC.continuous hfd

/-! The next adapter keeps the half-open time domain of a Ricci flow visible.
At an interior time, the flow equation on `Ico a b` restricts to the forward
neighborhood needed by the Dini quotient. -/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

/-- **Math.** At an interior time of a Ricci flow on a half-open interval, the
metric-inner equation yields the forward-Dini bound without requiring the
global (and generally false) inclusion `Ici t₀ ⊆ Ico a b`. -/
theorem metricInner_forwardDiffQuotientGE_of_isRicciFlowOn_Ico
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [FiniteDimensional ℝ E]
      [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    {g : ℝ → RiemannianMetric I M} {a b : ℝ}
    (hflow : IsRicciFlowOn g (Ico a b))
    {t₀ : ℝ} (hta : a ≤ t₀) (htb : t₀ < b)
    (p : M) (v : TangentSpace I p) :
    ForwardDiffQuotientGE
      (fun t => (g t).metricInner p v v) t₀
      (-2 * ricciTensorAt (g t₀) p v v) := by
  have ht : t₀ ∈ Ico a b := ⟨hta, htb⟩
  have hnhds : Ico a b ∈ 𝓝[Ici t₀] t₀ := by
    rw [Metric.mem_nhdsWithin_iff]
    refine ⟨b - t₀, sub_pos.mpr htb, ?_⟩
    intro y hy
    have hyball : dist y t₀ < b - t₀ := Metric.mem_ball.mp hy.1
    have hyt : t₀ ≤ y := hy.2
    have hyb : y < b := by
      have hyb' : y - t₀ < b - t₀ := by
        simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyt)] using hyball
      linarith
    exact ⟨le_trans hta hyt, hyb⟩
  have hderiv := hflow.equation t₀ ht p v v
  have hderivIci : HasDerivWithinAt
      (fun t => (g t).metricInner p v v)
      (-2 * ricciTensorAt (g t₀) p v v) (Ici t₀) t₀ :=
    hderiv.mono_of_mem_nhdsWithin hnhds
  exact HasDerivWithinAt.forwardDiffQuotientGE hderivIci

/-- **Math.** An absolute Ricci bound integrates the pointwise metric equation
for each fixed tangent vector on a half-open time interval. -/
theorem metricInner_endpointBound_of_isRicciFlowOn_Ico
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [FiniteDimensional ℝ E]
      [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    {g : ℝ → RiemannianMetric I M} {a b C : ℝ}
    (hab : a ≤ b)
    (hflow : IsRicciFlowOn g (Ico a b))
    (hRic : HasAbsoluteRicciBoundOn g (Ico a b) C)
    {p : M} {v : TangentSpace I p}
    (hf : Continuous (fun t => (g t).metricInner p v v)) :
    (g a).metricInner p v v ≤
      (g b).metricInner p v v +
        ∫ t in a..b, 2 * C * (g t).metricInner p v v := by
  let f : ℝ → ℝ := fun t => (g t).metricInner p v v
  let q : ℝ → ℝ := fun t => 2 * C * f t
  have hq : Continuous q := by
    exact continuous_const.mul hf
  have hfd : ∀ t ∈ Ico a b, ForwardDiffQuotientGE f t (-q t) := by
    intro t ht
    have hmetric := metricInner_forwardDiffQuotientGE_of_isRicciFlowOn_Ico
      hflow ht.1 ht.2 p v
    have hbound := abs_le.mp (hRic t ht p v)
    have hmono : -q t ≤ -2 * ricciTensorAt (g t) p v v := by
      dsimp [q, f]
      calc
        -(2 * C * (g t).metricInner p v v) =
            2 * (-(C * (g t).metricInner p v v)) := by ring
        _ ≤ 2 * (-ricciTensorAt (g t) p v v) :=
          mul_le_mul_of_nonneg_left (neg_le_neg hbound.2) (by norm_num)
        _ = -2 * ricciTensorAt (g t) p v v := by ring
    exact hmetric.mono hmono
  have hmain := lowerEndpointBound_of_forwardDiffQuotientGE_of_continuous
    (f := f) (C := q) hab hf.continuousOn hq hfd
  simpa [f, q, mul_assoc] using hmain

end MorganTianLib

end
