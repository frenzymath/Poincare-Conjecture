/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Geodesic/FlowC1Dependence.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Geodesic.UniformExistence
import PetersenLib.Riemannian.Geodesic.FlowDependence

set_option linter.unusedSectionVars false

/-!
# C¹ dependence of the local geodesic flow on its initial condition

The uniform-time local flow `Z` of the coordinate geodesic spray
(`exists_uniform_geodesic_flow`) is upgraded here with *strict differentiability in the
initial condition at every point of the flow ball* — not merely at the zero-section
equilibrium. This is the geodesic-spray instantiation of the non-equilibrium
C¹-dependence theorem (`PetersenLib.FlowDependence.hasStrictFDerivAt_of_picardResidual_curve`)
and the pointwise-C¹ content of do Carmo, *Riemannian Geometry*, Ch. 3, Theorem 2.2 /
Proposition 2.7 for the geodesic flow.

The two analytic inputs beyond the abstract theorem are:

* **Confinement in a compact ball.** The trajectories are confined (via Lipschitz
  dependence on the initial condition, no compactness needed for that step) inside a small
  ball whose *closure* lies in the chart region; in finite dimension that closed ball is
  compact.
* **Uniform derivative bound.** The spray derivative `fderiv F` is continuous on the chart
  region, hence bounded by some `C` on the compact confinement ball; every trajectory's
  operator curve `A₀(t) = fderiv F (Z x₀ t)` then has sup-norm `≤ C`, and a Picard time
  `T` with `T · C < 1` works *simultaneously for every* initial condition in the flow
  ball.

Main declaration:

* `exists_uniform_geodesic_flow_hasStrictFDerivAt` — a uniform-time local geodesic flow
  `Z` (with the same four clauses as `exists_uniform_geodesic_flow`: spray ODE, chart
  confinement, Lipschitz dependence, computation of the canonical maximal geodesic),
  together with a Picard time `0 < T < ε` and the flow read as a curve family
  `σ : E × E → C([0,T], E × E)`, such that at *every* initial condition `x₀` in the open
  flow ball, `σ` is strictly Fréchet differentiable with derivative `D` characterized by
  the linearized (variational) integral equation along the base trajectory.

Downstream, evaluation at time `T` and the fibre-scaling identification
`exp_p(w) = π(Z(φ_p(p), w/T)(T))` differentiate the exponential map at *nonzero*
velocities (`PetersenLib.Exponential.exists_hasStrictFDerivAt_extChartAt_expMap_ball`).
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace PetersenLib
namespace Geodesic

open PetersenLib.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The local geodesic flow is strictly differentiable in its initial condition
at every point of the flow ball** (do Carmo Ch. 3, Thm 2.2 / Prop. 2.7, pointwise C¹
dependence for the geodesic spray). There are `r, ε > 0`, a local flow `Z` of the
coordinate spray at `p` with the four clauses of `exists_uniform_geodesic_flow` (spray ODE
on `[-ε, ε]`, chart confinement, Lipschitz dependence on the initial condition,
computation of the canonical maximal geodesic by the flow), and a Picard time
`0 < T < ε` together with the flow read as a curve family
`σ : E × E → C([0, T], E × E)` (`σ x = Z x |_{[0,T]}` on the flow ball), such that at
*every* initial condition `x₀` in the open flow ball — equilibrium or not — the family
`σ` is strictly Fréchet differentiable at `x₀`, with derivative `D` characterized by the
linearized (variational) integral equation
`D v - ∫₀ᵗ A₀(s) ((D v)(s)) ds = const v` along the operator curve
`A₀(t) = (dF)_{σ(x₀)(t)}` of the spray `F` over the base trajectory. -/
theorem exists_uniform_geodesic_flow_hasStrictFDerivAt
    (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E) (L : ℝ≥0)
      (σ : E × E → C(Set.Icc (0:ℝ) T, E × E))
      (hT : 0 < T),
      0 < r ∧ 0 < ε ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      (∀ t ∈ Icc (-ε) ε, LipschitzOnWith L (Z · t)
        (closedBall ((extChartAt I p p, (0 : E)) : E × E) r)) ∧
      (∀ w : E, ‖w‖ ≤ r →
        Ioo (-ε) ε ⊆
          maximalGeodesicInterval (I := I) g p (w : TangentSpace I p) ∧
        ∀ s ∈ Ioo (-ε) ε,
          extChartAt I p
              (maximalGeodesic (I := I) g p (w : TangentSpace I p) s) =
            (Z ((extChartAt I p p, w) : E × E) s).1) ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        ∀ t : Set.Icc (0:ℝ) T, σ z t = Z z t.1) ∧
      (∀ x₀ ∈ ball ((extChartAt I p p, (0 : E)) : E × E) r,
        ∃ (D : E × E →L[ℝ] C(Set.Icc (0:ℝ) T, E × E))
          (A₀ : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))),
          (∀ t : Set.Icc (0:ℝ) T, A₀ t = fderiv ℝ
            (fun ζ : E × E => geodesicSprayCoord (I := I) g p ζ.1 ζ.2) (σ x₀ t)) ∧
          (∀ v : E × E, D v - intervalPrimitive hT.le (postcompCurve A₀ (D v))
            = ContinuousMap.const _ v) ∧
          HasStrictFDerivAt σ D x₀) := by
  classical
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set F : E × E → E × E := fun ζ => geodesicSprayCoord (I := I) g p ζ.1 ζ.2 with hFdef
  have hf : ContDiffAt ℝ 1 F z₀ := contDiffAt_geodesicSprayCoord_zero (I := I) g p
  -- the open chart region and a compact confinement ball inside it
  have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  have hmemz₀ : z₀ ∈ (extChartAt I p).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target p, mem_univ _⟩
  obtain ⟨ρc, hρc, hρcΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hopen.mem_nhds hmemz₀)
  -- the spray and its derivative on the chart region
  have hFs : ContDiffOn ℝ ∞ F ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    contDiffOn_geodesicSprayCoord_prod (I := I) g p
  have hcfder : ContinuousOn (fderiv ℝ F) ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    hFs.continuousOn_fderiv_of_isOpen hopen (by exact_mod_cast le_top)
  -- a uniform derivative bound on the compact confinement ball
  obtain ⟨C, hboundC⟩ := (isCompact_closedBall z₀ ρc).exists_bound_of_continuousOn
    (hcfder.mono hρcΩ)
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hboundC z₀ (mem_closedBall_self hρc.le))
  -- the local flow, confined to the open confinement ball
  have hU : ball z₀ ρc ∈ 𝓝 z₀ := ball_mem_nhds z₀ hρc
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip⟩ :=
    exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt hf hU
  -- the Picard time: short against both `ε` and the derivative bound
  set T : ℝ := min (ε / 2) (1 / (2 * (C + 1))) with hTdef
  have hT : 0 < T := lt_min (by positivity) (by positivity)
  have hTε : T < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hTC : T * C < 1 := by
    have h1 : T ≤ 1 / (2 * (C + 1)) := min_le_right _ _
    have h2 : (0 : ℝ) < 2 * (C + 1) := by positivity
    have h3 : T * C ≤ (1 / (2 * (C + 1))) * C := mul_le_mul_of_nonneg_right h1 hC0
    have h4 : (1 / (2 * (C + 1))) * (2 * (C + 1)) = 1 := one_div_mul_cancel (ne_of_gt h2)
    nlinarith
  have hIccTsub : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := fun t ht =>
    ⟨le_trans (neg_nonpos.mpr hε.le) ht.1, ht.2.trans hTε.le⟩
  -- trajectories stay in the chart region
  have hmemΩ : ∀ z ∈ closedBall z₀ r, ∀ t ∈ Icc (-ε) ε,
      Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E) := fun z hz t ht =>
    hρcΩ (ball_subset_closedBall ((hflow z hz).2.2 t ht))
  -- the flow read as a curve family on `[0, T]`
  set σ : E × E → C(Set.Icc (0 : ℝ) T, E × E) := fun x =>
    if hx : x ∈ closedBall z₀ r then
      ⟨fun t => Z x t.1, by
        have hcont : ContinuousOn (Z x) (Icc (-ε) ε) := fun s hs =>
          ((hflow x hx).2.1 s hs).continuousWithinAt
        exact hcont.comp_continuous continuous_subtype_val
          fun t => hIccTsub t.2⟩
    else ContinuousMap.const _ z₀ with hσdef
  have hσ_ball : ∀ z ∈ closedBall z₀ r, ∀ t : Set.Icc (0 : ℝ) T,
      σ z t = Z z t.1 := by
    intro z hz t
    simp only [hσdef, dif_pos hz]
    rfl
  refine ⟨r, ε, T, Z, L, σ, hT, hr, hε, hTε, ?_, hLip, ?_, hσ_ball, ?_⟩
  · -- the flow clauses, with chart confinement
    intro z hz
    obtain ⟨h0, hd, -⟩ := hflow z hz
    exact ⟨h0, hd, hmemΩ z hz⟩
  · -- transfer to the canonical maximal geodesic via the chart-flow bridge
    intro w hv
    have hzmem : ((extChartAt I p p, w) : E × E) ∈ closedBall z₀ r := by
      rw [mem_closedBall, hz₀def, Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      exact max_le hr.le hv
    obtain ⟨h0, hd, -⟩ := hflow _ hzmem
    have hdIoo : ∀ s ∈ Ioo (-ε) ε,
        HasDerivAt (Z ((extChartAt I p p, w) : E × E))
          (geodesicSprayCoord (I := I) g p
            (Z ((extChartAt I p p, w) : E × E) s).1
            (Z ((extChartAt I p p, w) : E × E) s).2) s := by
      intro s hs
      exact (hd s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hmemΨ : ∀ s ∈ Ioo (-ε) ε,
        Z ((extChartAt I p p, w) : E × E) s ∈
          (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
      intro s hs
      rw [extChartAt_tangent_target (I := I) p]
      exact hmemΩ _ hzmem s (Ioo_subset_Icc_self hs)
    have h0Ioo : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
    obtain ⟨hwit, hsrc, -⟩ :=
      isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord (I := I) g p
        (w : TangentSpace I p) h0 hdIoo hmemΨ
    refine ⟨subset_maximalGeodesicInterval_of_witness (I := I) hwit isOpen_Ioo
      isPreconnected_Ioo h0Ioo, fun s hs => ?_⟩
    exact extChartAt_maximalGeodesic_of_hasDerivAt_sprayCoord (I := I)
      isOpen_Ioo isPreconnected_Ioo h0Ioo h0 hdIoo hmemΨ hs
  · -- strict differentiability at every initial condition in the open flow ball
    intro x₀ hx₀
    have hx₀c : x₀ ∈ closedBall z₀ r := ball_subset_closedBall hx₀
    -- the base trajectory stays in the chart region and the compact ball
    have hα₀Ω : ∀ t : Set.Icc (0 : ℝ) T,
        σ x₀ t ∈ (extChartAt I p).target ×ˢ (univ : Set E) := fun t => by
      rw [hσ_ball x₀ hx₀c t]
      exact hmemΩ x₀ hx₀c t.1 (hIccTsub t.2)
    have hα₀ball : ∀ t : Set.Icc (0 : ℝ) T, σ x₀ t ∈ closedBall z₀ ρc := fun t => by
      rw [hσ_ball x₀ hx₀c t]
      exact ball_subset_closedBall ((hflow x₀ hx₀c).2.2 t.1 (hIccTsub t.2))
    -- differentiability data for the spray on the chart region
    have hd : ∀ x ∈ (extChartAt I p).target ×ˢ (univ : Set E),
        HasFDerivAt F (fderiv ℝ F x) x := fun x hx =>
      ((hFs.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hc : ∀ t : Set.Icc (0 : ℝ) T, ContinuousAt (fderiv ℝ F) (σ x₀ t) := fun t =>
      hcfder.continuousAt (hopen.mem_nhds (hα₀Ω t))
    -- the operator curve along the base trajectory, bounded by `C`
    set A₀ : C(Set.Icc (0 : ℝ) T, (E × E) →L[ℝ] (E × E)) :=
      ⟨fun t => fderiv ℝ F (σ x₀ t),
        hcfder.comp_continuous (σ x₀).continuous hα₀Ω⟩ with hA₀def
    have hA₀ : ∀ t : Set.Icc (0 : ℝ) T, A₀ t = fderiv ℝ F (σ x₀ t) := fun _ => rfl
    have hA₀C : ‖A₀‖ ≤ C := (ContinuousMap.norm_le _ hC0).mpr fun t =>
      hboundC _ (hα₀ball t)
    have hTL : T * ‖A₀‖ < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hA₀C hT.le) hTC
    -- continuity of the family at `x₀`, from Lipschitz dependence
    have hσc : ContinuousAt σ x₀ := by
      have hlips : LipschitzOnWith L σ (closedBall z₀ r) := by
        refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
        rw [ContinuousMap.dist_le (mul_nonneg L.coe_nonneg dist_nonneg)]
        intro t
        rw [hσ_ball x hx t, hσ_ball y hy t]
        exact (hLip t.1 (hIccTsub t.2)).dist_le_mul x hx y hy
      exact (hlips.continuousOn.continuousWithinAt hx₀c).continuousAt
        (Filter.mem_of_superset (isOpen_ball.mem_nhds hx₀) ball_subset_closedBall)
    -- the flow solutions satisfy the Picard integral equation near `x₀`
    have hσres : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le F (x, σ x) = 0 := by
      filter_upwards [isOpen_ball.mem_nhds hx₀] with x hx
      have hx' : x ∈ closedBall z₀ r := ball_subset_closedBall hx
      obtain ⟨h0, hdZ, -⟩ := hflow x hx'
      exact picardResidual_eq_zero_of_hasDerivWithinAt hT hFs.continuousOn h0
        (fun t ht => hmemΩ x hx' t (hIccTsub ht))
        (fun t ht => (hdZ t (hIccTsub ht)).mono hIccTsub)
        (σ x) (fun t => hσ_ball x hx' t)
    -- the non-equilibrium C¹-dependence theorem
    obtain ⟨D, hD, hstrict⟩ :=
      exists_hasStrictFDerivAt_of_picardResidual_curve hT hopen hd hα₀Ω hc hA₀ hTL
        rfl hσc hσres
    exact ⟨D, A₀, hA₀, hD, hstrict⟩

end Geodesic
end PetersenLib
