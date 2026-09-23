import MorganTianLib.Ch03.RicciFlow.MetricCoordinateVariation
import DoCarmoLib.Riemannian.Geodesic.UniformExistence

/-!
# Local geodesic equations with a varying metric parameter

The metric time is a constant state variable in the autonomous ODE below.
Picard--Lindelöf consequently gives one local existence interval and a
Lipschitz estimate simultaneously in metric time, position, and velocity.
This is a local coordinate ingredient of the compactness step in Claim 3.23;
global propagation along complete geodesics is not asserted here.
-/

open scoped Topology Manifold ContDiff NNReal
open Set Filter Metric Riemannian Riemannian.Geodesic

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Add metric time as a stationary coordinate of the geodesic spray. -/
def metricParameterSpray (g : ℝ → RiemannianMetric I M) (p : M)
    (z : ℝ × (E × E)) : ℝ × (E × E) :=
  (0, geodesicSprayCoord (g z.1) p z.2.1 z.2.2)

set_option maxHeartbeats 800000 in
/-- **Math.** The augmented geodesic vector field is smooth on its chart domain. -/
theorem contDiffOn_metricParameterSpray
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (p : M) :
    ContDiffOn ℝ ∞ (metricParameterSpray g p)
      (interior J ×ˢ ((extChartAt I p).target ×ˢ univ)) := by
  let S := interior J ×ˢ ((extChartAt I p).target ×ˢ (univ : Set E))
  have hvel : ContDiffOn ℝ ∞ (fun z : ℝ × (E × E) => z.2.2) S := contDiffOn_snd.snd
  have hmap : ContDiffOn ℝ ∞ (fun z : ℝ × (E × E) => (z.1, z.2.1)) S :=
    contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hmaps : MapsTo (fun z : ℝ × (E × E) => (z.1, z.2.1)) S
      (interior J ×ˢ (extChartAt I p).target) := fun _ hz => ⟨hz.1, hz.2.1⟩
  have hΓ (i j k : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞
      (fun z : ℝ × (E × E) => chartChristoffel (I := I) (g z.1) p i j k z.2.1)
      S := by
    simpa only [Function.comp_def] using
      (contDiffOn_chartChristoffel_timeSpace (I := I) hg p i j k).comp hmap hmaps
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞ (fun z : ℝ × (E × E) => chartCoord (E := E) i z.2.2) S := by
    simpa only [chartCoordFunctional_apply, Function.comp_def] using
      (chartCoordFunctional (E := E) i).contDiff.comp_contDiffOn hvel
  have hΓvv : ContDiffOn ℝ ∞ (fun z : ℝ × (E × E) =>
      chartChristoffelContraction (g z.1) p z.2.2 z.2.2 z.2.1) S := by
    unfold chartChristoffelContraction
    exact ContDiffOn.sum fun k _ =>
      (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
        ((hΓ i j k).mul (hcoord i)).mul (hcoord j)).smul contDiffOn_const
  change ContDiffOn ℝ ∞ (fun z : ℝ × (E × E) =>
    ((0 : ℝ), (z.2.2, -chartChristoffelContraction (g z.1) p z.2.2 z.2.2 z.2.1))) S
  exact contDiffOn_const.prodMk (hvel.prodMk hΓvv.neg)

/-- **Math.** A single coordinate flow, confined to the chart, exists for all
nearby metric times, positions and velocities. Its dependence on all three
initial-data components is uniformly Lipschitz on a common time interval. -/
theorem exists_local_geodesicFlow_metricParameter
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (p : M) {t₀ : ℝ} (ht : t₀ ∈ interior J) {x₀ v₀ : E}
    (hx : x₀ ∈ (extChartAt I p).target) :
    ∃ (r ε : ℝ) (Z : (ℝ × (E × E)) → ℝ → E × E) (L : ℝ≥0),
      0 < r ∧ 0 < ε ∧
      (∀ q ∈ closedBall (t₀, (x₀, v₀)) r,
        Z q 0 = q.2 ∧
        (∀ s ∈ Icc (-ε) ε, HasDerivWithinAt (Z q)
          (geodesicSprayCoord (g q.1) p (Z q s).1 (Z q s).2) (Icc (-ε) ε) s) ∧
        (∀ s ∈ Icc (-ε) ε, (Z q s).1 ∈ (extChartAt I p).target)) ∧
      (∀ s ∈ Icc (-ε) ε, ∀ q ∈ closedBall (t₀, (x₀, v₀)) r,
        ∀ q' ∈ closedBall (t₀, (x₀, v₀)) r,
          dist (Z q s) (Z q' s) ≤ L * dist q q') := by
  let U := interior J ×ˢ ((extChartAt I p).target ×ˢ (univ : Set E))
  have hU : IsOpen U := isOpen_interior.prod ((isOpen_extChartAt_target p).prod isOpen_univ)
  have hz : (t₀, (x₀, v₀)) ∈ U := ⟨ht, hx, mem_univ _⟩
  have hF : ContDiffAt ℝ 1 (metricParameterSpray g p) (t₀, (x₀, v₀)) :=
    ((contDiffOn_metricParameterSpray hg p).of_le (by simp)).contDiffAt (hU.mem_nhds hz)
  obtain ⟨r, ε, W, L, hr, hε, hW, hLip⟩ :=
    Riemannian.exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt hF (hU.mem_nhds hz)
  have hzero : (0 : ℝ) ∈ Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hparam (q : ℝ × (E × E)) (hq : q ∈ closedBall (t₀, (x₀, v₀)) r)
      (s : ℝ) (hs : s ∈ Icc (-ε) ε) : (W q s).1 = q.1 := by
    have hd : ∀ u ∈ Icc (-ε) ε,
        HasDerivWithinAt (fun u => (W q u).1) 0 (Icc (-ε) ε) u :=
      fun u hu => ((hW q hq).2.1 u hu).fst
    have hb := (convex_Icc (-ε) ε).norm_image_sub_le_of_norm_hasDerivWithin_le
      hd (fun _ _ => (show ‖(0 : ℝ)‖ ≤ 0 by simp)) hzero hs
    have heq : (W q s).1 = (W q 0).1 := sub_eq_zero.mp (norm_eq_zero.mp
      (le_antisymm (by simpa only [zero_mul] using hb) (norm_nonneg _)))
    simpa only [(hW q hq).1] using heq
  refine ⟨r, ε, (fun q s => (W q s).2), L, hr, hε, ?_, ?_⟩
  · intro q hq
    refine ⟨congrArg Prod.snd (hW q hq).1, ?_, ?_⟩
    · intro s hs
      have hd : HasDerivWithinAt (fun u => (W q u).2)
          (metricParameterSpray g p (W q s)).2 (Icc (-ε) ε) s :=
        ((hW q hq).2.1 s hs).snd
      simpa only [metricParameterSpray, hparam q hq s hs] using hd
    · intro s hs
      exact ((hW q hq).2.2 s hs).2.1
  · intro s hs q hq q' hq'
    calc
      dist (W q s).2 (W q' s).2 ≤ dist (W q s) (W q' s) := le_max_right _ _
      _ ≤ L * dist q q' := (hLip s hs).dist_le_mul q hq q' hq'

end MorganTianLib
