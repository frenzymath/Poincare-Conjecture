/-
# The Riemannian volume of a geodesic ball as a Jacobian integral

`thm:bishop-gromov` needs its relative volume comparison for the honest Riemannian volume
`μ_g(B(p,r))`, whereas the comparison engine (`Ch01/BishopGromovBall.lean`) proves it for the
integral `∫_{U_p ∩ ball} ρ_p` of the exponential Jacobian over the segment domain.  This file is the
bridge — blueprint gap **(a'2)** of `thm:bishop-gromov`:

  `μ_g(B(p,r)) = ∫⁻_{U_p ∩ {|v|_g < r}} ρ_p`.

The proof assembles three already-formalized facts:

* `riemannianMeasure_image_segmentDomain_eq_lintegral` (gap `(a'1)`): for measurable `U ⊆ U_p`,
  `μ_g(exp_p '' U) = ∫_U ρ_p`;
* `exists_mem_segmentDomain_expMapGlobal_eq` (gap `(a'2)` surjectivity, `Ch01/SegmentSurjective`):
  every `q ∈ B(p,r) ∖ C_p` is `exp_p(v)` for a `v ∈ U_p` with `|v|_g = d(p,q) < r`;
* `riemannianMeasure_cutLocus_eq_zero` (`lem:cut-locus-null`): `μ_g(C_p) = 0`.

Writing `U = U_p ∩ {|v|_g < r}`, the first fact evaluates `μ_g(exp_p '' U)`; the second and the
easy inclusion `exp_p '' U ⊆ B(p,r)` sandwich `B(p,r) ∖ C_p ⊆ exp_p '' U ⊆ B(p,r)`; and the third
collapses the sandwich to an equality of measures, since removing the null cut locus does not change
the volume of the ball.

Blueprint: `thm:bishop-gromov` (item `(a'2)`); `prop:exponential-diffeomorphism-cut-locus`.
-/
import PoincareLib.Ch01.SegmentSurjective
import PoincareLib.Ch01.ExpRiemannianJacobian
import PoincareLib.Ch01.CutLocusNull

open Set Filter Riemannian Module MeasureTheory Measure Metric
open scoped ContDiff Manifold Topology ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

/-- **Math.** **On the segment domain the exponential map realises the distance.** For `v ∈ U_p`
the radial geodesic minimizes past parameter `1`, so `d(p, exp_p(v)) = |v|_g`. This is the easy
half of `lem:cut-time-star-shaped`(2), and gives the inclusion `exp_p '' (U_p ∩ {|v|_g<r}) ⊆ B(p,r)`
used below. -/
theorem dist_expMapGlobal_of_mem_segmentDomain (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) {v : TangentSpace I p} (hv : v ∈ segmentDomain (I := I) g hg p) :
    dist p (expMapGlobal (I := I) g hg p v) = Real.sqrt (g.metricInner p v v) := by
  have hle : (ENNReal.ofReal 1 : ℝ≥0∞) ≤ cutTime (I := I) g hg p v := by
    rw [show (ENNReal.ofReal 1 : ℝ≥0∞) = 1 by simp]
    exact le_of_lt hv
  have hmin : IsMinimizingUpTo (I := I) g hg p v 1 :=
    (le_cutTime_iff (I := I) g hg p v (by norm_num)).1 hle
  rw [IsMinimizingUpTo, mul_one] at hmin
  rw [expMapGlobal_def]
  exact hmin

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Math.** **The Riemannian volume of a geodesic ball is the Jacobian integral over the segment
domain** — blueprint gap `(a'2)` of `thm:bishop-gromov`:

  `μ_g(B(p,r)) = ∫⁻_{v ∈ U_p, |v|_g < r} ρ_p(v)`.

Removing the null cut locus, the ball is the injective `exp_p`-image of `U_p ∩ {|v|_g<r}`, so the
change-of-variables formula `(a'1)` applies. -/
theorem riemannianMeasure_ball_eq_lintegral_segmentDomain (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [ConnectedSpace M] (p : M) (r : ℝ) :
    riemannianMeasure (I := I) g μ (Metric.ball p r)
      = ∫⁻ v in {v : E | 1 < cutTime (I := I) g hg p v} ∩
            {v : E | Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r},
          ENNReal.ofReal (expRiemannianJacobian (I := I) g hg p v) ∂μ := by
  classical
  set U : Set E := {v : E | 1 < cutTime (I := I) g hg p v} ∩
      {v : E | Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r} with hUdef
  -- `U ⊆ U_p` and `U` is measurable
  have hUsub : U ⊆ segmentDomain (I := I) g hg p := Set.inter_subset_left
  have hUmeas : MeasurableSet U :=
    (measurableSet_segmentDomain (I := I) g hg p).inter
      ((continuous_metricNorm (I := I) g p).measurable measurableSet_Iio)
  -- `exp_p '' U ⊆ B(p,r)`
  have hsub1 : expMapGlobal (I := I) g hg p '' U ⊆ Metric.ball p r := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Metric.mem_ball, dist_comm,
      dist_expMapGlobal_of_mem_segmentDomain (I := I) g hg p (hUsub hv)]
    exact hv.2
  -- `B(p,r) ∖ C_p ⊆ exp_p '' U`
  have hsub2 : Metric.ball p r \ cutLocus (I := I) g hg p ⊆ expMapGlobal (I := I) g hg p '' U := by
    rintro q ⟨hqball, hqcut⟩
    obtain ⟨v, hvseg, hvexp, hvnorm⟩ :=
      exists_mem_segmentDomain_expMapGlobal_eq (I := I) g hg p hqcut
    refine ⟨v, ⟨hvseg, ?_⟩, hvexp⟩
    show Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r
    rw [hvnorm]
    rwa [Metric.mem_ball, dist_comm] at hqball
  -- the cut locus is null, so removing it does not change the ball's volume
  have hCnull : riemannianMeasure (I := I) g μ (cutLocus (I := I) g hg p) = 0 :=
    riemannianMeasure_cutLocus_eq_zero (I := I) g hg μ p
  have hdiff : riemannianMeasure (I := I) g μ (Metric.ball p r \ cutLocus (I := I) g hg p)
      = riemannianMeasure (I := I) g μ (Metric.ball p r) := measure_diff_null hCnull
  -- squeeze: `μ_g(exp_p '' U) = μ_g(B(p,r))`
  have himg : riemannianMeasure (I := I) g μ (expMapGlobal (I := I) g hg p '' U)
      = riemannianMeasure (I := I) g μ (Metric.ball p r) := by
    refine le_antisymm (measure_mono hsub1) ?_
    rw [← hdiff]
    exact measure_mono hsub2
  -- conclude via the change-of-variables formula (a'1)
  rw [← himg]
  exact riemannianMeasure_image_segmentDomain_eq_lintegral μ g hg p hUmeas hUsub

end PoincareLib

end
