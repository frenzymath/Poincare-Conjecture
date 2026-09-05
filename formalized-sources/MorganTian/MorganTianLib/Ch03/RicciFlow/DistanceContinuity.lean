import MorganTianLib.Ch03.RicciFlow.MetricDistanceDistortion
import MorganTianLib.Ch01.MetricRescaling
import MorganTianLib.Ch03.RicciFlow.DistanceIntegralBound

/-!
# Continuity of intrinsic distance along Ricci flow

This module supplies the continuity input needed to integrate Morgan--Tian's
forward distance-variation estimate.  A uniform absolute Ricci bound gives an
exponential comparison between any two time slices, hence between the explicit
intrinsic distances induced by those metrics.
-/

open scoped ContDiff Manifold Topology Bundle ENNReal
open Bundle Filter Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** If `|Ric| ≤ C g` along a Ricci flow, then the metric pairings
at two ordered times differ by at most the factors `exp (±2 C (t - s))`.
Unlike the initial-time version, this statement can be applied at every time
of an order-connected flow interval. -/
theorem metricInner_exp_comparison_between_times_of_le
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {C s t : ℝ}
    (hflow : IsRicciFlowOn g J)
    (hRic : HasAbsoluteRicciBoundOn g J C)
    (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t)
    (p : M) (v : TangentSpace I p) :
    Real.exp (-(2 * C) * (t - s)) * (g s).metricInner p v v ≤
        (g t).metricInner p v v ∧
      (g t).metricInner p v v ≤
        Real.exp ((2 * C) * (t - s)) * (g s).metricInner p v v := by
  let f : ℝ → ℝ := fun u => (g u).metricInner p v v
  let upper : ℝ → ℝ :=
    (fun u => Real.exp (-(2 * C) * (u - s))) * f
  let lower : ℝ → ℝ :=
    (fun u => Real.exp ((2 * C) * (u - s))) * f
  have hsub : Icc s t ⊆ J := hflow.ordConnected.out hs ht
  have hfDeriv (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivWithinAt f (-2 * ricciTensorAt (g u) p v v) (Icc s t) u :=
    (hflow.equation u (hsub hu) p v v).mono hsub
  have hfCont : ContinuousOn f (Icc s t) :=
    fun u hu => (hfDeriv u hu).continuousWithinAt
  have hUpperCont : ContinuousOn upper (Icc s t) := by
    have hExp : Continuous (fun u : ℝ => Real.exp (-(2 * C) * (u - s))) := by
      fun_prop
    exact hExp.continuousOn.mul hfCont
  have hLowerCont : ContinuousOn lower (Icc s t) := by
    have hExp : Continuous (fun u : ℝ => Real.exp ((2 * C) * (u - s))) := by
      fun_prop
    exact hExp.continuousOn.mul hfCont
  have hUpperDeriv (u : ℝ) (hu : u ∈ interior (Icc s t)) :
      HasDerivWithinAt upper
        (Real.exp (-(2 * C) * (u - s)) *
          (-(2 * C) * f u - 2 * ricciTensorAt (g u) p v v))
        (interior (Icc s t)) u := by
    have huIcc : u ∈ Icc s t := interior_subset hu
    have hmetric : HasDerivAt f (-2 * ricciTensorAt (g u) p v v) u :=
      (hfDeriv u huIcc).hasDerivAt (mem_interior_iff_mem_nhds.mp hu)
    have hExp : HasDerivAt
        (fun r : ℝ => Real.exp (-(2 * C) * (r - s)))
        (-(2 * C) * Real.exp (-(2 * C) * (u - s))) u := by
      convert ((((hasDerivAt_id u).sub_const s).const_mul (-(2 * C))).exp) using 1
      · simp only [id]
      · simp only [id, mul_one]
        ring
    have hderiv :
        (-(2 * C) * Real.exp (-(2 * C) * (u - s))) * f u +
            Real.exp (-(2 * C) * (u - s)) *
              (-2 * ricciTensorAt (g u) p v v) =
          Real.exp (-(2 * C) * (u - s)) *
            (-(2 * C) * f u - 2 * ricciTensorAt (g u) p v v) := by
      ring
    exact ((hExp.mul hmetric).congr_deriv hderiv).hasDerivWithinAt
  have hLowerDeriv (u : ℝ) (hu : u ∈ interior (Icc s t)) :
      HasDerivWithinAt lower
        (Real.exp ((2 * C) * (u - s)) *
          ((2 * C) * f u - 2 * ricciTensorAt (g u) p v v))
        (interior (Icc s t)) u := by
    have huIcc : u ∈ Icc s t := interior_subset hu
    have hmetric : HasDerivAt f (-2 * ricciTensorAt (g u) p v v) u :=
      (hfDeriv u huIcc).hasDerivAt (mem_interior_iff_mem_nhds.mp hu)
    have hExp : HasDerivAt
        (fun r : ℝ => Real.exp ((2 * C) * (r - s)))
        ((2 * C) * Real.exp ((2 * C) * (u - s))) u := by
      convert ((((hasDerivAt_id u).sub_const s).const_mul (2 * C)).exp) using 1
      · simp only [id]
      · simp only [id, mul_one]
        ring
    have hderiv :
        ((2 * C) * Real.exp ((2 * C) * (u - s))) * f u +
            Real.exp ((2 * C) * (u - s)) *
              (-2 * ricciTensorAt (g u) p v v) =
          Real.exp ((2 * C) * (u - s)) *
            ((2 * C) * f u - 2 * ricciTensorAt (g u) p v v) := by
      ring
    exact ((hExp.mul hmetric).congr_deriv hderiv).hasDerivWithinAt
  have hUpperNonpos (u : ℝ) (hu : u ∈ interior (Icc s t)) :
      Real.exp (-(2 * C) * (u - s)) *
          (-(2 * C) * f u - 2 * ricciTensorAt (g u) p v v) ≤ 0 := by
    have huIcc : u ∈ Icc s t := interior_subset hu
    have hbounds := abs_le.mp (hRic u (hsub huIcc) p v)
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    dsimp only [f]
    linarith
  have hLowerNonneg (u : ℝ) (hu : u ∈ interior (Icc s t)) :
      0 ≤ Real.exp ((2 * C) * (u - s)) *
          ((2 * C) * f u - 2 * ricciTensorAt (g u) p v v) := by
    have huIcc : u ∈ Icc s t := interior_subset hu
    have hbounds := abs_le.mp (hRic u (hsub huIcc) p v)
    apply mul_nonneg (Real.exp_pos _).le
    dsimp only [f]
    linarith
  have hUpperAnti : AntitoneOn upper (Icc s t) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t) hUpperCont
      hUpperDeriv hUpperNonpos
  have hLowerMono : MonotoneOn lower (Icc s t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t) hLowerCont
      hLowerDeriv hLowerNonneg
  have hsIcc : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have htIcc : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have hUpperCompare := hUpperAnti hsIcc htIcc hst
  have hLowerCompare := hLowerMono hsIcc htIcc hst
  dsimp only [upper, lower, f] at hUpperCompare hLowerCompare
  change Real.exp (-(2 * C) * (t - s)) * (g t).metricInner p v v ≤
      Real.exp (-(2 * C) * (s - s)) * (g s).metricInner p v v at hUpperCompare
  change Real.exp ((2 * C) * (s - s)) * (g s).metricInner p v v ≤
      Real.exp ((2 * C) * (t - s)) * (g t).metricInner p v v at hLowerCompare
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hUpperCompare hLowerCompare
  have hcancelUpper :
      Real.exp ((2 * C) * (t - s)) *
          Real.exp (-(2 * C) * (t - s)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  have hcancelLower :
      Real.exp (-(2 * C) * (t - s)) *
          Real.exp ((2 * C) * (t - s)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  constructor
  · calc
      Real.exp (-(2 * C) * (t - s)) * (g s).metricInner p v v ≤
          Real.exp (-(2 * C) * (t - s)) *
            (Real.exp ((2 * C) * (t - s)) * (g t).metricInner p v v) :=
        mul_le_mul_of_nonneg_left hLowerCompare (Real.exp_pos _).le
      _ = (g t).metricInner p v v := by
        rw [← mul_assoc, hcancelLower, one_mul]
  · calc
      (g t).metricInner p v v =
          Real.exp ((2 * C) * (t - s)) *
            (Real.exp (-(2 * C) * (t - s)) * (g t).metricInner p v v) := by
        rw [← mul_assoc, hcancelUpper, one_mul]
      _ ≤ Real.exp ((2 * C) * (t - s)) * (g s).metricInner p v v :=
        mul_le_mul_of_nonneg_left hUpperCompare (Real.exp_pos _).le

/-- **Math.** The ordered two-time metric comparison induces the corresponding
bilipschitz estimate for the explicit intrinsic extended distance.  The
quadratic-form factor `exp (2 C (t - s))` becomes the length factor
`exp (C (t - s))`. -/
theorem metricIntrinsicEDist_exp_comparison_between_times_of_le
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {C s t : ℝ}
    (hflow : IsRicciFlowOn g J)
    (hRic : HasAbsoluteRicciBoundOn g J C)
    (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t)
    (x y : M) :
    ENNReal.ofReal (Real.exp (C * (t - s)))⁻¹ *
          metricIntrinsicEDist (g s) x y ≤ metricIntrinsicEDist (g t) x y ∧
      metricIntrinsicEDist (g t) x y ≤
        ENNReal.ofReal (Real.exp (C * (t - s))) *
          metricIntrinsicEDist (g s) x y := by
  let A : ℝ := Real.exp (C * (t - s))
  have hA : 0 < A := Real.exp_pos _
  have hAsq : A ^ 2 = Real.exp ((2 * C) * (t - s)) := by
    dsimp [A]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hmetric := metricInner_exp_comparison_between_times_of_le
    hflow hRic hs ht hst
  have h₀₁ : ∀ (p : M) (v : TangentSpace I p),
      (g t).metricInner p v v ≤ A ^ 2 * (g s).metricInner p v v := by
    intro p v
    simpa only [hAsq] using (hmetric p v).2
  have h₁₀ : ∀ (p : M) (v : TangentSpace I p),
      (g s).metricInner p v v ≤ A ^ 2 * (g t).metricInner p v v := by
    intro p v
    have hlower := (hmetric p v).1
    have hmul := mul_le_mul_of_nonneg_left hlower
      (Real.exp_pos ((2 * C) * (t - s))).le
    have hcancel : Real.exp ((2 * C) * (t - s)) *
        Real.exp (-(2 * C) * (t - s)) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      ring_nf
    calc
      (g s).metricInner p v v =
          Real.exp ((2 * C) * (t - s)) *
            (Real.exp (-(2 * C) * (t - s)) *
              (g s).metricInner p v v) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ Real.exp ((2 * C) * (t - s)) * (g t).metricInner p v v := hmul
      _ = A ^ 2 * (g t).metricInner p v v := by rw [hAsq]
  exact metricIntrinsicEDist_bilipschitz_of_metricInner_bilipschitz
    hA h₀₁ h₁₀ x y

/-- **Math.** On a preconnected manifold, the explicit intrinsic distance of
any Riemannian metric is finite.  This is the explicit-metric version of the
standard finiteness theorem for Riemannian distance. -/
theorem metricIntrinsicEDist_ne_top [PreconnectedSpace M]
    (g : RiemannianMetric I M) (x y : M) :
    metricIntrinsicEDist g x y ≠ ⊤ := by
  rw [metricIntrinsicEDist_eq_riemannianEDist]
  letI : Bundle.RiemannianBundle (fun p : M => TangentSpace I p) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun p : M => TangentSpace I p) :=
    riemannianMetric_isContinuousRiemannianBundle g
  letI : ∀ p : M, ENorm (TangentSpace I p) := metricENorm g
  exact Manifold.riemannianEDist_ne_top I x y

/-- **Math.** The finite real-valued intrinsic distance associated to an
explicit Riemannian metric on a preconnected manifold. -/
noncomputable def metricIntrinsicDist (g : RiemannianMetric I M)
    (x y : M) : ℝ :=
  (metricIntrinsicEDist g x y).toReal

/-- **Math.** On a preconnected manifold, the ordered exponential comparison
for intrinsic extended distance descends to the corresponding real-valued
distance comparison. -/
theorem metricIntrinsicDist_exp_comparison_between_times_of_le
    [PreconnectedSpace M]
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {C s t : ℝ}
    (hflow : IsRicciFlowOn g J)
    (hRic : HasAbsoluteRicciBoundOn g J C)
    (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t)
    (x y : M) :
    (Real.exp (C * (t - s)))⁻¹ * metricIntrinsicDist (g s) x y ≤
        metricIntrinsicDist (g t) x y ∧
      metricIntrinsicDist (g t) x y ≤
        Real.exp (C * (t - s)) * metricIntrinsicDist (g s) x y := by
  have hcomp := metricIntrinsicEDist_exp_comparison_between_times_of_le
    hflow hRic hs ht hst x y
  constructor
  · have hreal := ENNReal.toReal_mono
      (metricIntrinsicEDist_ne_top (g t) x y) hcomp.1
    simpa only [metricIntrinsicDist, ENNReal.toReal_mul,
      ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (Real.exp_pos (C * (t - s))).le,
      ENNReal.toReal_ofReal (inv_nonneg.mpr
        (Real.exp_pos (C * (t - s))).le)] using hreal
  · have hrightFinite :
        ENNReal.ofReal (Real.exp (C * (t - s))) *
            metricIntrinsicEDist (g s) x y ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (metricIntrinsicEDist_ne_top (g s) x y)
    have hreal := ENNReal.toReal_mono hrightFinite hcomp.2
    simpa only [metricIntrinsicDist, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos (C * (t - s))).le] using hreal

/-- **Math.** The real intrinsic distances at any two times in the flow
interval are bilipschitz with factor `exp (C |t - s|)`. -/
theorem metricIntrinsicDist_exp_comparison_between_times
    [PreconnectedSpace M]
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {C s t : ℝ}
    (hflow : IsRicciFlowOn g J)
    (hRic : HasAbsoluteRicciBoundOn g J C)
    (hs : s ∈ J) (ht : t ∈ J)
    (x y : M) :
    (Real.exp (C * |t - s|))⁻¹ * metricIntrinsicDist (g s) x y ≤
        metricIntrinsicDist (g t) x y ∧
      metricIntrinsicDist (g t) x y ≤
        Real.exp (C * |t - s|) * metricIntrinsicDist (g s) x y := by
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using
      metricIntrinsicDist_exp_comparison_between_times_of_le
        hflow hRic hs ht hst x y
  · have hcomp := metricIntrinsicDist_exp_comparison_between_times_of_le
      hflow hRic ht hs hts x y
    have habs : |t - s| = s - t := by
      rw [abs_of_nonpos (sub_nonpos.mpr hts)]
      ring
    rw [habs]
    let A : ℝ := Real.exp (C * (s - t))
    have hA : 0 < A := Real.exp_pos _
    have hA0 : A ≠ 0 := ne_of_gt hA
    change A⁻¹ * metricIntrinsicDist (g t) x y ≤
        metricIntrinsicDist (g s) x y ∧
      metricIntrinsicDist (g s) x y ≤
        A * metricIntrinsicDist (g t) x y at hcomp
    change A⁻¹ * metricIntrinsicDist (g s) x y ≤
        metricIntrinsicDist (g t) x y ∧
      metricIntrinsicDist (g t) x y ≤
        A * metricIntrinsicDist (g s) x y
    constructor
    · calc
        A⁻¹ * metricIntrinsicDist (g s) x y ≤
            A⁻¹ * (A * metricIntrinsicDist (g t) x y) :=
          mul_le_mul_of_nonneg_left hcomp.2 (inv_nonneg.mpr hA.le)
        _ = metricIntrinsicDist (g t) x y := by
          rw [← mul_assoc, inv_mul_cancel₀ hA0, one_mul]
    · calc
        metricIntrinsicDist (g t) x y =
            A * (A⁻¹ * metricIntrinsicDist (g t) x y) := by
          rw [← mul_assoc, mul_inv_cancel₀ hA0, one_mul]
        _ ≤ A * metricIntrinsicDist (g s) x y :=
          mul_le_mul_of_nonneg_left hcomp.1 hA.le

/-- **Math.** Under a uniform absolute Ricci bound, the finite intrinsic
distance between two fixed points varies continuously in time along a Ricci
flow on an order-connected interval. -/
theorem continuousOn_metricIntrinsicDist
    [PreconnectedSpace M]
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {C : ℝ}
    (hflow : IsRicciFlowOn g J)
    (hRic : HasAbsoluteRicciBoundOn g J C)
    (x y : M) :
    ContinuousOn (fun t => metricIntrinsicDist (g t) x y) J := by
  intro s hs
  have hlower :
      Tendsto
        (fun t : ℝ => (Real.exp (C * |t - s|))⁻¹ *
          metricIntrinsicDist (g s) x y)
        (𝓝[J] s) (𝓝 (metricIntrinsicDist (g s) x y)) := by
    have hcont : ContinuousAt
        (fun t : ℝ => (Real.exp (C * |t - s|))⁻¹ *
          metricIntrinsicDist (g s) x y) s := by
      have hexp : ContinuousAt (fun t : ℝ => Real.exp (C * |t - s|)) s := by
        fun_prop
      exact (hexp.inv₀ (Real.exp_ne_zero _)).mul continuousAt_const
    simpa [ContinuousWithinAt, sub_self, abs_zero, mul_zero, Real.exp_zero,
      inv_one, one_mul] using
      (hcont.continuousWithinAt (s := J))
  have hupper :
      Tendsto
        (fun t : ℝ => Real.exp (C * |t - s|) *
          metricIntrinsicDist (g s) x y)
        (𝓝[J] s) (𝓝 (metricIntrinsicDist (g s) x y)) := by
    have hcont : ContinuousAt
        (fun t : ℝ => Real.exp (C * |t - s|) *
          metricIntrinsicDist (g s) x y) s := by
      fun_prop
    simpa [ContinuousWithinAt, sub_self, abs_zero, mul_zero, Real.exp_zero,
      one_mul] using
      (hcont.continuousWithinAt (s := J))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (metricIntrinsicDist_exp_comparison_between_times
      hflow hRic hs ht x y).1
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (metricIntrinsicDist_exp_comparison_between_times
      hflow hRic hs ht x y).2

/-- **Math.** Once the geometric forward-Dini estimate for the intrinsic
distance is supplied, the preceding continuity theorem feeds it into the
standard interval-integral endpoint argument.  The Dini estimate is kept as
an explicit hypothesis: producing it from minimizing geodesics and the index
form is the remaining geometric part of the Morgan--Tian distance proof. -/
theorem lowerEndpointBound_metricIntrinsicDist_of_isRicciFlowOn
    [PreconnectedSpace M]
    {g : ℝ → RiemannianMetric I M} {a b K : ℝ} {q : ℝ → ℝ}
    (hflow : IsRicciFlowOn g (Icc a b))
    (hRic : HasAbsoluteRicciBoundOn g (Icc a b) K)
    (hab : a ≤ b) (hq : Continuous q) (x y : M)
    (hfd : ∀ t ∈ Ico a b,
      ForwardDiffQuotientGE
        (fun u => metricIntrinsicDist (g u) x y) t (-q t)) :
    metricIntrinsicDist (g a) x y ≤
      metricIntrinsicDist (g b) x y + ∫ t in a..b, q t := by
  exact lowerEndpointBound_of_forwardDiffQuotientGE_of_continuous hab
    (continuousOn_metricIntrinsicDist hflow hRic x y) hq hfd

end MorganTianLib

end
