import OpenGALib.Riemannian.Geodesic.FlowCInftyDependence
import OpenGALib.Riemannian.Geodesic.FlowGeodesic

/-!
# One-chart geodesic flow steps with `C^∞` dependence at an arbitrary anchor

This is the `C^∞` companion of `exists_geodesic_flow_step` (`FlowStep.lean`), which
supplies the *strict-Fréchet-derivative* (C¹) form of the one-chart geodesic flow
step consumed by the differential of the exponential map. For the **global
smoothness** of `exp_p` (do Carmo Ch. 7, the Hadamard theorem) one needs, instead
of the derivative, the full `C^∞` regularity of the time-`τ` endpoint map of the
geodesic flow, at an *arbitrary* anchor state — not merely the zero section handled
by `Riemannian.Geodesic.exists_uniform_geodesic_flow_contDiffAt`.

`exists_geodesic_flow_step_contDiff` provides exactly that. Around any state
`z₀ = (x₀, w₀)` whose position lies in the chart target at `β` (so `w₀` is an
*arbitrary* velocity, not necessarily zero), there are radii `r`, an interval margin
`ε` and a Picard time `0 < T < ε`, and a local flow `Z` of the coordinate geodesic
spray at `β`, such that:

1. every trajectory `Z z` (`z ∈ closedBall z₀ r`) starts at `z`, solves the spray
   ODE on `[-ε, ε]`, and keeps its position in the chart target;
2. each trajectory projects to an *intrinsic* geodesic on `(-ε, ε)`;
3. at every inner state `x₀ ∈ ball z₀ r` and every time `τ ∈ [0, T]`, the endpoint
   map `z ↦ Z z τ` is **`C^∞`** at `x₀`.

The proof mirrors `exists_uniform_geodesic_flow_contDiffAt`: the spray field is
bump-extended (`exists_contDiff_eqOn_closedBall_of_contDiffOn`) to a globally `C^∞`
field `F'` agreeing with it on a closed ball around `z₀`; the flow is confined to
`ball z₀ a` where `F' = F`, so it satisfies the Picard integral equation of `F'` and
inherits its `C^∞` dependence via `contDiffAt_flow_of_picardResidual`. Evaluating the
`C^∞` curve family `σ` at the fixed time `τ` gives the endpoint map. The only change
from the zero-section version is that `z₀` is an arbitrary interior state, so the
first-order regularity `hf : ContDiffAt ℝ 1 F z₀` comes from
`contDiffOn_geodesicSprayCoord_prod` rather than from the zero-section lemma.

Blueprint: `thm:dc-ch7-3-1`, `lem:dc-ch7-3-2` (the global smoothness of `exp_p`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4; do Carmo,
*Riemannian Geometry*, Ch. 7, §3.
-/

open Set Riemannian Filter Metric
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **One-chart geodesic flow step with `C^∞` dependence at an arbitrary
anchor state.** Let `β : M` and let `z₀ = (x₀, w₀) ∈ E × E` be a state whose position
lies in the chart target at `β` (the velocity `w₀` is arbitrary). Then there are
`r > 0`, an interval margin `ε` and a Picard time `0 < T < ε`, and a local flow `Z` of
the coordinate geodesic spray at `β`, such that:

1. for every `z ∈ closedBall z₀ r`, the trajectory `Z z` starts at `z`, solves the
   spray ODE on `[-ε, ε]`, and its position stays in the chart target;
2. each trajectory projects to an *intrinsic* geodesic on `(-ε, ε)`;
3. at every `x₀ ∈ ball z₀ r` and every `τ ∈ [0, T]`, the endpoint map `z ↦ Z z τ` is
   `C^∞` at `x₀`.

This is the `C^∞` companion of `exists_geodesic_flow_step`, generalizing
`exists_uniform_geodesic_flow_contDiffAt` from the zero-section anchor
`(φ_p(p), 0)` to an arbitrary anchor state — the regularity consumed by the chart
chain that globalizes the smoothness of `exp_p`.

Blueprint: `thm:dc-ch7-3-1`. -/
theorem exists_geodesic_flow_step_contDiff (g : RiemannianMetric I M) (β : M)
    {z₀ : E × E} (hz₀ : z₀.1 ∈ (extChartAt I β).target) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E),
      0 < r ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall z₀ r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g β (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, (Z z t).1 ∈ (extChartAt I β).target)) ∧
      (∀ z ∈ closedBall z₀ r,
        IsGeodesicOn (I := I) g (sprayBase (I := I) β (Z z)) (Ioo (-ε) ε)) ∧
      (∀ x₀ ∈ ball z₀ r, ∀ τ ∈ Icc (0 : ℝ) T,
        ContDiffAt ℝ ∞ (fun z => Z z τ) x₀) := by
  classical
  set F : E × E → E × E := fun ζ => geodesicSprayCoord (I := I) g β ζ.1 ζ.2 with hFdef
  -- the open chart region containing `z₀`, and the spray's regularity there
  have hopen : IsOpen ((extChartAt I β).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target β).prod isOpen_univ
  have hmemz₀ : z₀ ∈ (extChartAt I β).target ×ˢ (univ : Set E) :=
    ⟨hz₀, mem_univ _⟩
  have hFs : ContDiffOn ℝ ∞ F ((extChartAt I β).target ×ˢ (univ : Set E)) :=
    contDiffOn_geodesicSprayCoord_prod (I := I) g β
  have hf : ContDiffAt ℝ 1 F z₀ :=
    (hFs.contDiffAt (hopen.mem_nhds hmemz₀)).of_le (by exact_mod_cast le_top)
  -- bump-extend the spray to a globally `C^∞` field agreeing on a closed ball
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
      Z z t ∈ (extChartAt I β).target ×ˢ (univ : Set E) := fun z hz t ht =>
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
  refine ⟨r, ε, T, Z, hr, hT, hTε, ?_, ?_, ?_⟩
  · -- the flow clauses, with chart confinement
    intro z hz
    obtain ⟨h0, hd, -⟩ := hflow z hz
    exact ⟨h0, hd, fun t ht => (hmemΩ z hz t ht).1⟩
  · -- intrinsic-geodesic semantics of the base curves
    intro z hz
    have hdIoo : ∀ s ∈ Ioo (-ε) ε,
        HasDerivAt (Z z)
          (geodesicSprayCoord (I := I) g β (Z z s).1 (Z z s).2) s := fun s hs =>
      ((hflow z hz).2.1 s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    exact isGeodesicOn_sprayBase (I := I) isOpen_Ioo hdIoo
      fun s hs => (hmemΩ z hz s (Ioo_subset_Icc_self hs)).1
  · -- `C^∞` dependence of the endpoint map at every inner state
    intro x₀ hx₀ τ hτ
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
    have hcd_σ : ContDiffAt ℝ ∞ σ x₀ :=
      contDiffAt_flow_of_picardResidual hT hF'C hA₀ hTL rfl hσc hσres
    -- evaluate the `C^∞` curve family at the fixed time `τ`
    have hcd_eval :=
      ((ContinuousMap.evalCLM ℝ (⟨τ, hτ⟩ : Set.Icc (0 : ℝ) T)).contDiff.contDiffAt).comp
        x₀ hcd_σ
    refine hcd_eval.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hx₀] with z hz
    exact (hσ_ball z (ball_subset_closedBall hz) ⟨τ, hτ⟩).symm

end Riemannian.Jacobi

end
