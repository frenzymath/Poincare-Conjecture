import MorganTianLib.Ch05.Foundations
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3GeodesicMetricBall

/-!
# Morgan--Tian Chapter 5: local intrinsic exponential endpoint

The local geodesic flow theorem gives a positive metric radius on which the
intrinsic exponential is defined at a chosen point.  This adapter keeps the
manifold and Hausdorff hypotheses explicit and does not assume completeness of
the manifold itself.
-/

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace MorganTianLib

universe u

/-- **Math.** Around every point of a finite-dimensional Riemannian manifold,
the intrinsic exponential is defined on a positive metric-inner ball.  The
fixed interval supplied by Do Carmo's local flow contains time `1`, so its
geodesic family is an intrinsic witness for membership in the exponential
domain.  No `CompleteSpace M` hypothesis is used.

Blueprint: `def:delta-regular-point` (local exponential endpoint). -/
theorem exists_intrinsicExpRegularAt
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    (g : Riemannian.RiemannianMetric I M) (p : M) :
    ∃ ε > 0, IsIntrinsicExpRegularAt g ε p := by
  obtain ⟨V, hV, ε, hε, W, hW, c, hc, hsmooth⟩ :=
    Riemannian.GeodesicLocal.geodesic_local_existence_fixedInterval_metricBall
      (I := I) g p
  refine ⟨ε, hε, ?_⟩
  intro v hv
  have hpV : p ∈ V := mem_of_mem_nhds hV
  have hwmetric : g.metricInner p v v < ε ^ 2 := by
    have hsqrt : Real.sqrt (g.metricInner p v v) < ε := hv
    have hnonneg : 0 ≤ g.metricInner p v v :=
      g.metricInner_self_nonneg p v
    nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (g.metricInner p v v)]
  have hmain := hc p hpV v hwmetric
  simp only [Riemannian.Geodesic.chartFiberCoord_mk] at hmain
  have hzero : (0 : ℝ) ∈ Ioo (-2) 2 := by norm_num
  have hone : (1 : ℝ) ∈ Ioo (-2) 2 := by norm_num
  change Riemannian.Geodesic.IntrinsicGeodesicWitness (I := I) g p v 1
  refine ⟨c p v, Ioo (-2) 2, isOpen_Ioo, isPreconnected_Ioo,
    hzero, hone, ?_⟩
  change c p v 0 = p ∧
    HasDerivAt (fun s => extChartAt I p (c p v s)) (v : E) 0 ∧
      Riemannian.Geodesic.IsGeodesicCurveOn (I := I) g (c p v) (Ioo (-2) 2)
  exact ⟨hmain.2.2.1, hmain.2.2.2.1, hmain.2.1⟩

end MorganTianLib
