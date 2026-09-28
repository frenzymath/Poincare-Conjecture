import DoCarmoLib.Riemannian.Geodesic.UniformExistence
import DoCarmoLib.Riemannian.Geodesic.FlowDependence
import DoCarmoLib.Riemannian.Geodesic.FlowSmoothDependence
import DoCarmoLib.Riemannian.Geodesic.BumpExtension

set_option linter.unusedSectionVars false

/-!
# `C^∞` dependence of the local geodesic flow on its initial condition

The uniform-time local flow `Z` of the coordinate geodesic spray (`exists_uniform_geodesic_flow`)
is upgraded here to *`C^∞` in the initial condition at every point of the flow ball*. This is the
geodesic-spray instantiation of the abstract `C^∞` flow-dependence theorem
(`Riemannian.FlowDependence.contDiffAt_flow_of_picardResidual`), and the pointwise-`C^∞` content
of do Carmo, *Riemannian Geometry*, Ch. 3, Theorem 2.2 / Proposition 2.7 for the geodesic flow —
the regularity beyond the `C¹` (`FlowC1Dependence`) and `C²` (`FlowC2Dependence`) results.

The abstract theorem needs a field that is `C^∞` on the *whole* space; the coordinate spray is only
`ContDiffOn ℝ ∞` on the chart region. The bridge is the *multiply by a bump* extension
(`exists_contDiff_eqOn_closedBall_of_contDiffOn`): the spray `F` is replaced by a globally `C^∞`
field `F'` that agrees with it on a closed ball `closedBall z₀ a` around the zero section. The flow
is confined (Picard–Lindelöf, no compactness) to `ball z₀ a`, where `F' = F`, so it *is* the flow of
`F'` there; hence it satisfies the Picard integral equation of `F'` and inherits its `C^∞`
dependence. The Picard time `T` is chosen short against a uniform bound `C` on `‖fderiv F'‖` over the
compact `closedBall z₀ a`, giving the contraction bound `T · C < 1` simultaneously for every initial
condition in the flow ball.

Main declaration:

* `exists_uniform_geodesic_flow_contDiffAt` — a uniform-time local geodesic flow `Z` with the same
  four clauses as `exists_uniform_geodesic_flow` (spray ODE, chart confinement, Lipschitz
  dependence, computation of the canonical maximal geodesic), a Picard time `0 < T < ε`, the flow
  read as a curve family `σ : E × E → C([0,T], E × E)`, and — the new content — `ContDiffAt ℝ ∞ σ`
  at every initial condition in the open flow ball.

Downstream, evaluation at time `T` and the fibre-scaling identification
`exp_p(w) = π(Z(φ_p(p), w/T)(T))` make the chart reading of `exp_p` `C^∞` on a ball.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian
namespace Geodesic

open Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The local geodesic flow is `C^∞` in its initial condition at every point of the
flow ball** (do Carmo Ch. 3, Thm 2.2 / Prop. 2.7, `C^∞` dependence for the geodesic spray). There
are `r, ε > 0`, a local flow `Z` of the coordinate spray at `p` with the four clauses of
`exists_uniform_geodesic_flow` (spray ODE on `[-ε, ε]`, chart confinement, Lipschitz dependence on
the initial condition, computation of the canonical maximal geodesic by the flow), a Picard time
`0 < T < ε`, and the flow read as a curve family `σ : E × E → C([0, T], E × E)` (`σ x = Z x |_{[0,T]}`
on the flow ball), such that at *every* initial condition `x₀` in the open flow ball, `σ` is `C^∞`.

The field is bump-extended to a globally `C^∞` field `F'` agreeing with the spray on a closed ball
containing every trajectory; the flow is the `F'`-flow there, so the abstract `C^∞` flow-dependence
theorem (`contDiffAt_flow_of_picardResidual`) applies, with a Picard time short against a uniform
`‖fderiv F'‖`-bound on the compact confinement ball. -/
theorem exists_uniform_geodesic_flow_contDiffAt
    (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E) (L : ℝ≥0)
      (σ : E × E → C(Set.Icc (0:ℝ) T, E × E))
      (_hT : 0 < T),
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
        ContDiffAt ℝ ∞ σ x₀) := by
  classical
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set F : E × E → E × E := fun ζ => geodesicSprayCoord (I := I) g p ζ.1 ζ.2 with hFdef
  have hf : ContDiffAt ℝ 1 F z₀ := contDiffAt_geodesicSprayCoord_zero (I := I) g p
  -- the open chart region containing `z₀`, and the spray's `C^∞`-ness there
  have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  have hmemz₀ : z₀ ∈ (extChartAt I p).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target p, mem_univ _⟩
  have hFs : ContDiffOn ℝ ∞ F ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    contDiffOn_geodesicSprayCoord_prod (I := I) g p
  -- bump-extend the spray to a globally `C^∞` field agreeing on a closed ball around `z₀`
  obtain ⟨F', a, ha, haΩ, hF'C, hF'F⟩ :=
    exists_contDiff_eqOn_closedBall_of_contDiffOn hopen hFs hmemz₀
  -- `fderiv F'` is continuous; a uniform bound `C` on the compact confinement ball
  have hcfder : Continuous (fderiv ℝ F') := hF'C.continuous_fderiv (by simp)
  obtain ⟨C, hboundC⟩ := (isCompact_closedBall z₀ a).exists_bound_of_continuousOn
    hcfder.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hboundC z₀ (mem_closedBall_self ha.le))
  -- the local flow, confined to the open ball `ball z₀ a` where `F' = F`
  have hU : ball z₀ a ∈ 𝓝 z₀ := ball_mem_nhds z₀ ha
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip⟩ :=
    exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt hf hU
  -- the Picard time: short against `ε` and the derivative bound
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
  -- trajectories stay in the chart region (via `ball z₀ a ⊆ closedBall z₀ a ⊆ Ω`)
  have hmemΩ : ∀ z ∈ closedBall z₀ r, ∀ t ∈ Icc (-ε) ε,
      Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E) := fun z hz t ht =>
    haΩ (ball_subset_closedBall ((hflow z hz).2.2 t ht))
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
  · -- `C^∞` dependence at every initial condition in the open flow ball
    intro x₀ hx₀
    have hx₀c : x₀ ∈ closedBall z₀ r := ball_subset_closedBall hx₀
    -- the base trajectory stays in `ball z₀ a` (hence in the compact confinement ball)
    have hconf : ∀ t : Set.Icc (0 : ℝ) T, σ x₀ t ∈ ball z₀ a := fun t => by
      rw [hσ_ball x₀ hx₀c t]
      exact (hflow x₀ hx₀c).2.2 t.1 (hIccTsub t.2)
    -- the operator curve `A₀(t) = (dF')_{σ(x₀)(t)}`, bounded by `C`
    set A₀ : C(Set.Icc (0 : ℝ) T, (E × E) →L[ℝ] (E × E)) :=
      ⟨fun t => fderiv ℝ F' (σ x₀ t), hcfder.comp (σ x₀).continuous⟩ with hA₀def
    have hA₀ : ∀ t : Set.Icc (0 : ℝ) T, A₀ t = fderiv ℝ F' (σ x₀ t) := fun _ => rfl
    have hA₀C : ‖A₀‖ ≤ C := (ContinuousMap.norm_le _ hC0).mpr fun t =>
      hboundC _ (ball_subset_closedBall (hconf t))
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
    -- the flow solutions satisfy the Picard integral equation of `F'` near `x₀`
    have hσres : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le F' (x, σ x) = 0 := by
      filter_upwards [isOpen_ball.mem_nhds hx₀] with x hx
      have hx' : x ∈ closedBall z₀ r := ball_subset_closedBall hx
      obtain ⟨h0, hdZ, hmemU⟩ := hflow x hx'
      refine picardResidual_eq_zero_of_hasDerivWithinAt hT hF'C.continuous.continuousOn h0
        (fun t _ => mem_univ _) ?_ (σ x) (fun t => hσ_ball x hx' t)
      intro t ht
      have hmem : Z x t ∈ closedBall z₀ a :=
        ball_subset_closedBall (hmemU t (hIccTsub ht))
      have hd := (hdZ t (hIccTsub ht)).mono hIccTsub
      rw [hF'F hmem]
      exact hd
    exact contDiffAt_flow_of_picardResidual hT hF'C hA₀ hTL rfl hσc hσres

end Geodesic
end Riemannian
