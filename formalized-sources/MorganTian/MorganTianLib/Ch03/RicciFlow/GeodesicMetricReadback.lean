import MorganTianLib.Ch03.RicciFlow.GeodesicMetricParameter
import DoCarmoLib.Riemannian.Geodesic.IntrinsicUniqueness
import DoCarmoLib.Riemannian.Geodesic.DataTransfer

/-!
# Reading parameter-dependent coordinate flows as intrinsic geodesics

Coordinate solutions are projected through the inverse chart, and intrinsic
uniqueness identifies them with any geodesic having the same initial data.
The metric parameter may vary between the curves being compared in a sequence;
uniqueness is used separately at each fixed metric.
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

/-- **Math.** A coordinate solution of the geodesic spray is an intrinsic
geodesic, and its second component is the derivative of its chart reading. -/
theorem isGeodesicOn_of_coordinateSolution
    {g : RiemannianMetric I M} {p : M} {S : Set ℝ} (hS : IsOpen S)
    {z : ℝ → E × E}
    (hd : ∀ s ∈ S, HasDerivAt z (geodesicSprayCoord g p (z s).1 (z s).2) s)
    (hconf : ∀ s ∈ S, (z s).1 ∈ (extChartAt I p).target) :
    let γ := fun s => (extChartAt I p).symm (z s).1
    ContinuousOn γ S ∧ IsGeodesicOn g γ S ∧
      (∀ s ∈ S, γ s ∈ (chartAt H p).source ∧
        extChartAt I p (γ s) = (z s).1 ∧
        HasDerivAt (chartReading (I := I) p γ) (z s).2 s) := by
  let c : ℝ → E := fun s => (z s).1
  let v : ℝ → E := fun s => (z s).2
  let γ : ℝ → M := fun s => (extChartAt I p).symm (c s)
  have hc (s : ℝ) (hs : s ∈ S) : HasDerivAt c (v s) s := (hd s hs).fst
  have hv (s : ℝ) (hs : s ∈ S) : HasDerivAt v
      (-chartChristoffelContraction g p (v s) (v s) (c s)) s := (hd s hs).snd
  have hsrc (s : ℝ) (hs : s ∈ S) : γ s ∈ (chartAt H p).source := by
    have h := (extChartAt I p).map_target (hconf s hs)
    rwa [extChartAt_source] at h
  have hread (s : ℝ) (hs : s ∈ S) : chartReading (I := I) p γ s = c s :=
    (extChartAt I p).right_inv (hconf s hs)
  have hcont : ContinuousOn γ S := (continuousOn_extChartAt_symm p).comp
    (fun s hs => (hc s hs).continuousAt.continuousWithinAt) hconf
  have hev (s : ℝ) (hs : s ∈ S) : chartReading (I := I) p γ =ᶠ[𝓝 s] c := by
    filter_upwards [hS.mem_nhds hs] with u hu using hread u hu
  have hderiv (s : ℝ) (hs : s ∈ S) : deriv (chartReading (I := I) p γ) s = v s := by
    rw [(hev s hs).deriv_eq]
    exact (hc s hs).deriv
  refine ⟨hcont, ?_, fun s hs => ⟨hsrc s hs, hread s hs,
    (hc s hs).congr_of_eventuallyEq (hev s hs)⟩⟩
  intro s hs
  have hsolves : SolvesGeodesicODEAt g p γ s := by
    constructor
    · filter_upwards [hS.mem_nhds hs] with u hu
      rw [hderiv u hu]
      exact (hc u hu).congr_of_eventuallyEq (hev u hu)
    · refine ⟨-chartChristoffelContraction g p (v s) (v s) (c s), ?_, ?_⟩
      · apply (hv s hs).congr_of_eventuallyEq
        filter_upwards [hS.mem_nhds hs] with u hu using hderiv u hu
      · rw [hderiv s hs, hread s hs]
        exact neg_add_cancel _
  exact hsolves.hasGeodesicEquationAt (hcont.continuousAt (hS.mem_nhds hs)) (hsrc s hs)

/-- **Math.** Intrinsic uniqueness identifies an arbitrary geodesic with a
coordinate solution on their common open connected time interval. -/
theorem geodesic_eq_coordinateSolution
    {g : RiemannianMetric I M} {p : M} {S : Set ℝ} (hS : IsOpen S)
    (hconn : IsPreconnected S) {z : ℝ → E × E} {γ : ℝ → M} {s₀ : ℝ}
    (hd : ∀ s ∈ S, HasDerivAt z (geodesicSprayCoord g p (z s).1 (z s).2) s)
    (hconf : ∀ s ∈ S, (z s).1 ∈ (extChartAt I p).target)
    (hgeo : IsGeodesicOn g γ S) (hc : ContinuousOn γ S) (hs₀ : s₀ ∈ S)
    (hsrc : γ s₀ ∈ (chartAt H p).source)
    (hpos : extChartAt I p (γ s₀) = (z s₀).1)
    (hvel : deriv (chartReading (I := I) p γ) s₀ = (z s₀).2) :
    ∀ s ∈ S, γ s = (extChartAt I p).symm (z s).1 ∧
      extChartAt I p (γ s) = (z s).1 ∧
      HasDerivAt (chartReading (I := I) p γ) (z s).2 s := by
  obtain ⟨hc', hg', hread⟩ := isGeodesicOn_of_coordinateSolution hS hd hconf
  have hpos' : γ s₀ = (extChartAt I p).symm (z s₀).1 := by
    rw [← hpos, (extChartAt I p).left_inv (by rwa [extChartAt_source])]
  have heq := hgeo.eqOn_of_deriv_chartReading_eq hS hconn hg' hc hc' hs₀ hpos' hsrc
    (hvel.trans (hread s₀ hs₀).2.2.deriv.symm)
  intro s hs
  refine ⟨heq hs, ?_, ?_⟩
  · rw [heq hs]
    exact (hread s hs).2.1
  · apply (hread s hs).2.2.congr_of_eventuallyEq
    filter_upwards [hS.mem_nhds hs] with u hu
    exact congrArg (extChartAt I p) (heq hu)

/-- **Math.** The flow from `exists_local_geodesicFlow_metricParameter` reads
back any global continuous geodesic from its position and velocity at zero. -/
theorem geodesic_eq_metricParameterFlow
    {g : ℝ → RiemannianMetric I M} {p : M} {ε : ℝ} (hε : 0 < ε)
    {Z : (ℝ × (E × E)) → ℝ → E × E} {q : ℝ × (E × E)} {γ : ℝ → M}
    (hZ₀ : Z q 0 = q.2)
    (hZ : ∀ s ∈ Icc (-ε) ε, HasDerivWithinAt (Z q)
      (geodesicSprayCoord (g q.1) p (Z q s).1 (Z q s).2) (Icc (-ε) ε) s)
    (hconf : ∀ s ∈ Icc (-ε) ε, (Z q s).1 ∈ (extChartAt I p).target)
    (hgeo : IsGeodesic (g q.1) γ) (hc : Continuous γ)
    (hsrc : γ 0 ∈ (chartAt H p).source)
    (hpos : extChartAt I p (γ 0) = q.2.1)
    (hvel : deriv (chartReading (I := I) p γ) 0 = q.2.2) :
    ∀ s ∈ Ioo (-ε) ε, γ s = (extChartAt I p).symm (Z q s).1 ∧
      extChartAt I p (γ s) = (Z q s).1 ∧
      HasDerivAt (chartReading (I := I) p γ) (Z q s).2 s := by
  apply geodesic_eq_coordinateSolution isOpen_Ioo (convex_Ioo (-ε) ε).isPreconnected
    (fun s hs => (hZ s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2))
    (fun s hs => hconf s (Ioo_subset_Icc_self hs))
    (hgeo.isGeodesicOn _) hc.continuousOn ⟨neg_lt_zero.mpr hε, hε⟩ hsrc
  · simpa only [hZ₀] using hpos
  · simpa only [hZ₀] using hvel

/-- **Math.** The same readback formula based at any curve parameter. -/
theorem geodesic_eq_metricParameterFlow_shift
    {g : ℝ → RiemannianMetric I M} {p : M} {ε : ℝ} (hε : 0 < ε)
    {Z : (ℝ × (E × E)) → ℝ → E × E} {q : ℝ × (E × E)} {γ : ℝ → M} {b : ℝ}
    (hZ₀ : Z q 0 = q.2)
    (hZ : ∀ s ∈ Icc (-ε) ε, HasDerivWithinAt (Z q)
      (geodesicSprayCoord (g q.1) p (Z q s).1 (Z q s).2) (Icc (-ε) ε) s)
    (hconf : ∀ s ∈ Icc (-ε) ε, (Z q s).1 ∈ (extChartAt I p).target)
    (hgeo : IsGeodesic (g q.1) γ) (hc : Continuous γ)
    (hsrc : γ b ∈ (chartAt H p).source)
    (hpos : extChartAt I p (γ b) = q.2.1)
    (hvel : deriv (chartReading (I := I) p γ) b = q.2.2) :
    ∀ s ∈ Ioo (-ε) ε, γ (s + b) = (extChartAt I p).symm (Z q s).1 ∧
      γ (s + b) ∈ (chartAt H p).source ∧
      extChartAt I p (γ (s + b)) = (Z q s).1 ∧
      deriv (chartReading (I := I) p γ) (s + b) = (Z q s).2 := by
  have hshift := geodesic_eq_metricParameterFlow hε hZ₀ hZ hconf
    (isGeodesic_comp_add hgeo b) (hc.comp (continuous_add_const b))
    (by simpa using hsrc) (by simpa using hpos)
    (by
      change deriv (fun u => extChartAt I p (γ (u + b))) 0 = q.2.2
      rw [deriv_comp_add_const (fun u => extChartAt I p (γ u)) b 0, zero_add]
      exact hvel)
  intro s hs
  obtain ⟨heq, hread, hv⟩ := hshift s hs
  refine ⟨heq, ?_, hread, ?_⟩
  · rw [heq, ← extChartAt_source (I := I) p]
    exact (extChartAt I p).map_target (hconf s (Ioo_subset_Icc_self hs))
  · have hv' : deriv (fun u => extChartAt I p (γ (u + b))) s = (Z q s).2 := hv.deriv
    rw [deriv_comp_add_const (fun u => extChartAt I p (γ u)) b s] at hv'
    exact hv'

/-- **Math.** Moving-time evaluations of a uniformly Lipschitz family of
coordinate solutions converge when the metric parameter and initial data do. -/
theorem tendsto_metricParameterFlow_eval
    {r ε : ℝ} {Z : (ℝ × (E × E)) → ℝ → E × E} {L : ℝ≥0}
    {c q : ℝ × (E × E)}
    (hLip : ∀ s ∈ Icc (-ε) ε, ∀ q ∈ closedBall c r,
      ∀ q' ∈ closedBall c r, dist (Z q s) (Z q' s) ≤ L * dist q q')
    (hq : q ∈ closedBall c r) (hc : ContinuousOn (Z q) (Icc (-ε) ε))
    {qs : ℕ → ℝ × (E × E)} (hqs : Tendsto qs atTop (𝓝 q))
    (hmem : ∀ᶠ n in atTop, qs n ∈ closedBall c r)
    {ss : ℕ → ℝ} {s₀ : ℝ} (hss : Tendsto ss atTop (𝓝 s₀))
    (hs₀ : s₀ ∈ Icc (-ε) ε) (hs : ∀ᶠ n in atTop, ss n ∈ Icc (-ε) ε) :
    Tendsto (fun n => Z (qs n) (ss n)) atTop (𝓝 (Z q s₀)) := by
  have hbase : Tendsto (fun n => Z q (ss n)) atTop (𝓝 (Z q s₀)) :=
    (hc s₀ hs₀).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hss, hs⟩)
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ᶠ n in atTop, dist (Z (qs n) (ss n)) (Z q s₀) ≤
      L * dist (qs n) q + dist (Z q (ss n)) (Z q s₀) := by
    filter_upwards [hmem, hs] with n hn hsn
    exact (dist_triangle _ (Z q (ss n)) _).trans (add_le_add (hLip _ hsn _ hn _ hq) le_rfl)
  have hlim : Tendsto (fun n => L * dist (qs n) q + dist (Z q (ss n)) (Z q s₀))
      atTop (𝓝 0) := by
    simpa using ((tendsto_iff_dist_tendsto_zero.mp hqs).const_mul (L : ℝ)).add
      (tendsto_iff_dist_tendsto_zero.mp hbase)
  exact squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hbound hlim

/-- **Math.** Velocity convergence transfers between charts even if the
metrics of the geodesics and the sample times vary with the sequence. -/
theorem tendsto_geodesic_velocity_chartTransfer
    {gs : ℕ → RiemannianMetric I M} {g₀ : RiemannianMetric I M}
    {γs : ℕ → ℝ → M} {γ : ℝ → M} {ss : ℕ → ℝ} {s₀ : ℝ} {p q : M}
    (hgeo : ∀ n, HasGeodesicEquationAt (gs n) (γs n) (ss n))
    (hc : ∀ n, ContinuousAt (γs n) (ss n))
    (hgeo₀ : HasGeodesicEquationAt g₀ γ s₀) (hc₀ : ContinuousAt γ s₀)
    (hp : γ s₀ ∈ (chartAt H p).source) (hq : γ s₀ ∈ (chartAt H q).source)
    (hpos : Tendsto (fun n => γs n (ss n)) atTop (𝓝 (γ s₀)))
    (hvel : Tendsto (fun n => deriv (chartReading (I := I) p (γs n)) (ss n))
      atTop (𝓝 (deriv (chartReading (I := I) p γ) s₀))) :
    Tendsto (fun n => deriv (chartReading (I := I) q (γs n)) (ss n))
      atTop (𝓝 (deriv (chartReading (I := I) q γ) s₀)) := by
  have hev : ∀ᶠ n in atTop,
      γs n (ss n) ∈ (chartAt H p).source ∩ (chartAt H q).source :=
    hpos.eventually_mem (((chartAt H p).open_source.inter
      (chartAt H q).open_source).mem_nhds ⟨hp, hq⟩)
  change Tendsto (fun n => deriv (fun u => extChartAt I q (γs n u)) (ss n))
    atTop (𝓝 (deriv (fun u => extChartAt I q (γ u)) s₀))
  rw [hgeo₀.deriv_extChartAt_transfer hc₀ hp hq]
  apply (tendsto_tangentCoordChange_of_tendsto hpos hp hq hvel).congr'
  filter_upwards [hev] with n hn
  exact ((hgeo n).deriv_extChartAt_transfer (hc n) hn.1 hn.2).symm

end MorganTianLib
