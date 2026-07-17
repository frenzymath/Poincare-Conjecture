import PoincareLib.Ch01.SprayLinearization
import OpenGALib.Riemannian.Geodesic.UniformExistence
import OpenGALib.Riemannian.Geodesic.FlowDependence
import OpenGALib.Riemannian.Geodesic.FlowGeodesic

/-!
# Poincaré Ch. 1, §1.4 — one-chart geodesic flow steps with C¹ dependence

The differential of the exponential map (`lem:exponential-differential-jacobi`)
is computed by composing, along a compact geodesic segment, short one-chart
flow steps of the coordinate geodesic spray, each strictly differentiable in
its initial condition with derivative the solution of the variational
equation. This file provides the *step*:

* `exists_geodesic_flow_step` — around any state `z₀` over a chart target,
  there are radii `r`, a margin interval `[-ε, ε]` and a Picard time
  `0 < T < ε`, with a uniform local flow `Z` of the coordinate spray at `β`
  (ODE + chart confinement on `[-ε, ε]` for every initial condition in
  `closedBall z₀ r`), whose base curves are *intrinsic* geodesics
  (`IsGeodesicOn`), and such that at every `x₀ ∈ ball z₀ r` each time-`τ`
  endpoint map `z ↦ Z z τ` (`τ ∈ [0, T]`) is strictly differentiable, the
  assignment `τ ↦ D x₀ τ` starting from `D x₀ 0 = 1` and solving the
  linearized (variational) ODE `(D · v)' = (dF)_{Z x₀ t} (D t v)` along the
  base trajectory.

  This generalizes `Riemannian.Geodesic.exists_uniform_geodesic_flow_hasStrictFDerivAt`
  (OpenGALib) from the zero-section anchor `(φ_p(p), 0)` to an arbitrary
  anchor state, and repackages the abstract curve-family derivative as the
  pointwise variational solution, which is what the Jacobi identification
  consumes.

* `IsJacobiFieldOn.variational_transport` — the transport identity: if `W`
  solves the variational equation along a chart geodesic `u` and starts at
  the *variational pair* `(J l, DJ l - Γ_{u l}(u̇ l, J l))` of a Jacobi field
  `(J, DJ)`, then it stays equal to the variational pair of `(J, DJ)` on the
  whole interval. Combined with `isJacobiFieldOn_of_variational` and the
  Grönwall uniqueness `IsJacobiFieldOn.eqOn_of_left`, this is how the
  derivative of the geodesic flow is identified with Jacobi-field data.

Blueprint: `lem:exponential-differential-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter Metric
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-! ### The one-chart flow step -/

/-- **Math.** **One-chart geodesic flow step with C¹ dependence at an arbitrary
anchor state.** Let `β : M` and let `z₀ = (x₀, w₀) ∈ E × E` be a state whose
position lies in the chart target at `β`. Then there are `r > 0`, an interval
margin `ε` and a Picard time `0 < T < ε`, a local flow `Z` of the coordinate
geodesic spray at `β`, and a derivative assignment `D`, such that:

1. for every initial condition `z ∈ closedBall z₀ r`, the trajectory `Z z`
   starts at `z`, solves the spray ODE on `[-ε, ε]`, and its position stays
   in the chart target;
2. each such trajectory projects to an *intrinsic* geodesic on `(-ε, ε)`
   (`IsGeodesicOn`, moving-chart formulation — the output can be glued
   across charts);
3. at every `x₀ ∈ ball z₀ r` and every `τ ∈ [0, T]`, the time-`τ` flow map
   `z ↦ Z z τ` is strictly differentiable at `x₀` with derivative `D x₀ τ`,
   `D x₀ 0 = 1`, and for each vector `v` the curve `t ↦ D x₀ t v` solves the
   **variational equation** `W' = (dF)_{Z x₀ t} W` of the spray along the
   base trajectory, one-sidedly on `[0, T]`.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem exists_geodesic_flow_step (g : RiemannianMetric I M) (β : M) {z₀ : E × E}
    (hz₀ : z₀.1 ∈ (extChartAt I β).target) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E)
      (D : E × E → ℝ → (E × E) →L[ℝ] (E × E)),
      0 < r ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall z₀ r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g β (Z z t).1 (Z z t).2)
          (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, (Z z t).1 ∈ (extChartAt I β).target)) ∧
      (∀ z ∈ closedBall z₀ r,
        IsGeodesicOn (I := I) g (sprayBase (I := I) β (Z z)) (Ioo (-ε) ε)) ∧
      (∀ x₀ ∈ ball z₀ r,
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasStrictFDerivAt (fun z => Z z τ) (D x₀ τ) x₀) ∧
        (∀ v : E × E, D x₀ 0 v = v) ∧
        (∀ v : E × E, ∀ t ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (fun s => D x₀ s v)
            (fderiv ℝ
              (fun ζ : E × E => geodesicSprayCoord (I := I) g β ζ.1 ζ.2)
              (Z x₀ t) (D x₀ t v)) (Icc (0 : ℝ) T) t)) := by
  classical
  set F : E × E → E × E := fun ζ => geodesicSprayCoord (I := I) g β ζ.1 ζ.2
    with hFdef
  -- the open chart region and a compact confinement ball inside it
  have hopen : IsOpen ((extChartAt I β).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target β).prod isOpen_univ
  have hmemz₀ : z₀ ∈ (extChartAt I β).target ×ˢ (univ : Set E) :=
    ⟨hz₀, mem_univ _⟩
  obtain ⟨ρc, hρc, hρcΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hopen.mem_nhds hmemz₀)
  -- the spray and its derivative on the chart region
  have hFs : ContDiffOn ℝ ∞ F ((extChartAt I β).target ×ˢ (univ : Set E)) :=
    contDiffOn_geodesicSprayCoord_prod (I := I) g β
  have hf : ContDiffAt ℝ 1 F z₀ :=
    (hFs.contDiffAt (hopen.mem_nhds hmemz₀)).of_le (by exact_mod_cast le_top)
  have hcfder : ContinuousOn (fderiv ℝ F)
      ((extChartAt I β).target ×ˢ (univ : Set E)) :=
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
      Z z t ∈ (extChartAt I β).target ×ˢ (univ : Set E) := fun z hz t ht =>
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
  -- the abstract C¹-dependence theorem at every inner state, with the
  -- derivative characterized by the pointwise linearized Volterra identity
  have hkey : ∀ x₀ ∈ ball z₀ r,
      ∃ Dσ : E × E →L[ℝ] C(Set.Icc (0 : ℝ) T, E × E),
        (∀ v : E × E, ∀ τ : Set.Icc (0 : ℝ) T,
          Dσ v τ = v + ∫ s in (0 : ℝ)..(τ : ℝ),
            fderiv ℝ F (σ x₀ (projIcc (0 : ℝ) T hT.le s))
              (Dσ v (projIcc (0 : ℝ) T hT.le s)))
        ∧ HasStrictFDerivAt σ Dσ x₀ := by
    intro x₀ hx₀
    have hx₀c : x₀ ∈ closedBall z₀ r := ball_subset_closedBall hx₀
    have hα₀Ω : ∀ t : Set.Icc (0 : ℝ) T,
        σ x₀ t ∈ (extChartAt I β).target ×ˢ (univ : Set E) := fun t => by
      rw [hσ_ball x₀ hx₀c t]
      exact hmemΩ x₀ hx₀c t.1 (hIccTsub t.2)
    have hα₀ball : ∀ t : Set.Icc (0 : ℝ) T, σ x₀ t ∈ closedBall z₀ ρc := fun t => by
      rw [hσ_ball x₀ hx₀c t]
      exact ball_subset_closedBall ((hflow x₀ hx₀c).2.2 t.1 (hIccTsub t.2))
    have hd : ∀ x ∈ (extChartAt I β).target ×ˢ (univ : Set E),
        HasFDerivAt F (fderiv ℝ F x) x := fun x hx =>
      ((hFs.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hc : ∀ t : Set.Icc (0 : ℝ) T, ContinuousAt (fderiv ℝ F) (σ x₀ t) := fun t =>
      hcfder.continuousAt (hopen.mem_nhds (hα₀Ω t))
    set A₀ : C(Set.Icc (0 : ℝ) T, (E × E) →L[ℝ] (E × E)) :=
      ⟨fun t => fderiv ℝ F (σ x₀ t),
        (hcfder.comp_continuous (σ x₀).continuous fun t => by
          rw [hσ_ball x₀ (ball_subset_closedBall hx₀) t]
          exact hmemΩ x₀ (ball_subset_closedBall hx₀) t.1 (hIccTsub t.2))⟩
      with hA₀def
    have hA₀ : ∀ t : Set.Icc (0 : ℝ) T, A₀ t = fderiv ℝ F (σ x₀ t) := fun _ => rfl
    have hA₀C : ‖A₀‖ ≤ C := (ContinuousMap.norm_le _ hC0).mpr fun t =>
      hboundC _ (hα₀ball t)
    have hTL : T * ‖A₀‖ < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hA₀C hT.le) hTC
    have hσc : ContinuousAt σ x₀ := by
      have hlips : LipschitzOnWith L σ (closedBall z₀ r) := by
        refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
        rw [ContinuousMap.dist_le (mul_nonneg L.coe_nonneg dist_nonneg)]
        intro t
        rw [hσ_ball x hx t, hσ_ball y hy t]
        exact (hLip t.1 (hIccTsub t.2)).dist_le_mul x hx y hy
      exact (hlips.continuousOn.continuousWithinAt hx₀c).continuousAt
        (Filter.mem_of_superset (isOpen_ball.mem_nhds hx₀) ball_subset_closedBall)
    have hσres : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le F (x, σ x) = 0 := by
      filter_upwards [isOpen_ball.mem_nhds hx₀] with x hx
      have hx' : x ∈ closedBall z₀ r := ball_subset_closedBall hx
      obtain ⟨h0, hdZ, -⟩ := hflow x hx'
      exact picardResidual_eq_zero_of_hasDerivWithinAt hT hFs.continuousOn h0
        (fun t ht => hmemΩ x hx' t (hIccTsub ht))
        (fun t ht => (hdZ t (hIccTsub ht)).mono hIccTsub)
        (σ x) (fun t => hσ_ball x hx' t)
    obtain ⟨Dσ, hDeq, hstrict⟩ :=
      exists_hasStrictFDerivAt_of_picardResidual_curve hT hopen hd hα₀Ω hc hA₀ hTL
        rfl hσc hσres
    refine ⟨Dσ, fun v τ => ?_, hstrict⟩
    have h := congrArg (fun ξ : C(Set.Icc (0 : ℝ) T, E × E) => ξ τ) (hDeq v)
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply,
      intervalPrimitive_apply, postcompCurve_apply, hA₀def,
      ContinuousMap.coe_mk] at h
    exact sub_eq_iff_eq_add.mp h
  -- the derivative assignment, by choice at inner states
  set D : E × E → ℝ → (E × E) →L[ℝ] (E × E) := fun x₀ τ =>
    if hx₀ : x₀ ∈ ball z₀ r then
      (ContinuousMap.evalCLM ℝ (projIcc (0 : ℝ) T hT.le τ)).comp
        (Classical.choose (hkey x₀ hx₀))
    else 0 with hDdef
  refine ⟨r, ε, T, Z, D, hr, hT, hTε, ?_, ?_, ?_⟩
  · -- the flow clauses, with chart confinement
    intro z hz
    obtain ⟨h0, hd, -⟩ := hflow z hz
    exact ⟨h0, hd, fun t ht => (hmemΩ z hz t ht).1⟩
  · -- intrinsic-geodesic semantics of the base curves
    intro z hz
    have hdIoo : ∀ s ∈ Ioo (-ε) ε,
        HasDerivAt (Z z)
          (geodesicSprayCoord (I := I) g β (Z z s).1 (Z z s).2) s := fun s hs =>
      ((hflow z hz).2.1 s (Ioo_subset_Icc_self hs)).hasDerivAt
        (Icc_mem_nhds hs.1 hs.2)
    exact isGeodesicOn_sprayBase (I := I) isOpen_Ioo hdIoo
      fun s hs => (hmemΩ z hz s (Ioo_subset_Icc_self hs)).1
  · -- strict differentiability of the endpoint maps + the variational equation
    intro x₀ hx₀
    obtain ⟨hint, hstrict⟩ := Classical.choose_spec (hkey x₀ hx₀)
    set Dσ := Classical.choose (hkey x₀ hx₀) with hDσdef
    have hx₀c : x₀ ∈ closedBall z₀ r := ball_subset_closedBall hx₀
    have hDval : ∀ (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T), ∀ v : E × E,
        D x₀ τ v = Dσ v ⟨τ, hτ⟩ := by
      intro τ hτ v
      simp only [hDdef, dif_pos hx₀, ContinuousLinearMap.comp_apply]
      rw [projIcc_of_mem hT.le hτ]
      rfl
    -- the continuous integrand
    have hicont : ∀ v : E × E, Continuous fun s : ℝ =>
        fderiv ℝ F (σ x₀ (projIcc (0 : ℝ) T hT.le s))
          (Dσ v (projIcc (0 : ℝ) T hT.le s)) := by
      intro v
      have hA : Continuous fun t : Set.Icc (0 : ℝ) T => fderiv ℝ F (σ x₀ t) :=
        hcfder.comp_continuous (σ x₀).continuous fun t => by
          rw [hσ_ball x₀ hx₀c t]
          exact hmemΩ x₀ hx₀c t.1 (hIccTsub t.2)
      have h1 : Continuous fun t : Set.Icc (0 : ℝ) T =>
          fderiv ℝ F (σ x₀ t) (Dσ v t) :=
        (hA.clm_apply (Dσ v).continuous)
      exact h1.comp continuous_projIcc
    refine ⟨?_, ?_, ?_⟩
    · -- strict differentiability of the time-`τ` endpoint maps
      intro τ hτ
      have heval : HasStrictFDerivAt (fun z => σ z ⟨τ, hτ⟩)
          ((ContinuousMap.evalCLM ℝ (⟨τ, hτ⟩ : Set.Icc (0 : ℝ) T)).comp Dσ) x₀ :=
        (ContinuousMap.evalCLM ℝ (⟨τ, hτ⟩ : Set.Icc (0 : ℝ) T)).hasStrictFDerivAt.comp
          x₀ hstrict
      have hev : (fun z => σ z ⟨τ, hτ⟩) =ᶠ[𝓝 x₀] (fun z => Z z τ) := by
        filter_upwards [isOpen_ball.mem_nhds hx₀] with z hz
        exact hσ_ball z (ball_subset_closedBall hz) ⟨τ, hτ⟩
      have hDτ : D x₀ τ
          = (ContinuousMap.evalCLM ℝ (⟨τ, hτ⟩ : Set.Icc (0 : ℝ) T)).comp Dσ := by
        simp only [hDdef, dif_pos hx₀]
        rw [projIcc_of_mem hT.le hτ]
      rw [hDτ]
      exact heval.congr_of_eventuallyEq hev
    · -- the derivative starts at the identity
      intro v
      have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
      rw [hDval 0 h0mem v, hint v ⟨0, h0mem⟩]
      simp
    · -- the variational equation for the derivative curves
      intro v t ht
      -- the primitive expression of the derivative curve
      set h : ℝ → E × E := fun s =>
        fderiv ℝ F (σ x₀ (projIcc (0 : ℝ) T hT.le s))
          (Dσ v (projIcc (0 : ℝ) T hT.le s)) with hhdef
      have hprim : ∀ s ∈ Icc (0 : ℝ) T,
          D x₀ s v = v + ∫ u in (0 : ℝ)..s, h u := by
        intro s hs
        rw [hDval s hs v, hint v ⟨s, hs⟩]
      have hderiv : HasDerivAt (fun s : ℝ => v + ∫ u in (0 : ℝ)..s, h u) (h t) t := by
        have hFTC : HasDerivAt (fun s : ℝ => ∫ u in (0 : ℝ)..s, h u) (h t) t :=
          intervalIntegral.integral_hasDerivAt_right
            ((hicont v).intervalIntegrable 0 t)
            ((hicont v).stronglyMeasurableAtFilter _ _)
            (hicont v).continuousAt
        simpa using hFTC.const_add v
      have hgoal : HasDerivWithinAt (fun s => D x₀ s v) (h t) (Icc (0 : ℝ) T) t := by
        refine (hderiv.hasDerivWithinAt.congr (fun s hs => ?_) (hprim t ht))
        exact hprim s hs
      have hht : h t = fderiv ℝ F (Z x₀ t) (D x₀ t v) := by
        rw [hhdef]
        simp only
        rw [projIcc_of_mem hT.le ht, hσ_ball x₀ hx₀c ⟨t, ht⟩, hDval t ht v]
      rwa [hht] at hgoal

/-! ### Variational transport of Jacobi pairs -/

/-- **Math.** **Variational transport = covariant transport.** Let `u` be a chart
geodesic on `[l, r]` over the interior of the chart target at `β`, let `W`
solve the variational equation `W' = (dF)_{(u, u̇)} W` of the geodesic spray
along `u`, and let `(J, DJ)` be a Jacobi field along `u`
(`IsJacobiFieldOn`). If `W` starts at the variational pair
`(J l, DJ l - Γ_{u l}(u̇ l, J l))` of `(J, DJ)`, then `W` equals the
variational pair of `(J, DJ)` on all of `[l, r]`:
`W t = (J t, DJ t - Γ_{u t}(u̇ t, J t))`.

This is the identification of the derivative of the geodesic flow with
Jacobi-field data along one chart piece: `isJacobiFieldOn_of_variational`
turns `W` into a Jacobi pair with the same initial data as `(J, DJ)`, and
the Grönwall uniqueness `IsJacobiFieldOn.eqOn_of_left` forces equality.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem IsJacobiFieldOn.variational_transport (g : RiemannianMetric I M) (β : M)
    {u : ℝ → E} {W : ℝ → E × E} {J DJ : ℝ → E} {l r : ℝ}
    (hmem : ∀ t ∈ Icc l r, u t ∈ interior (extChartAt I β).target)
    (hu : ∀ t ∈ Icc l r, HasDerivAt u (deriv u t) t)
    (hu' : ∀ t ∈ Icc l r, HasDerivAt (deriv u)
      (-(Geodesic.chartChristoffelContraction (I := I) g β
        (deriv u t) (deriv u t) (u t))) t)
    (hW : ∀ t ∈ Icc l r, HasDerivWithinAt W
      (fderiv ℝ
        (fun ζ : E × E => Geodesic.geodesicSprayCoord (I := I) g β ζ.1 ζ.2)
        (u t, deriv u t) (W t)) (Icc l r) t)
    (hJac : IsJacobiFieldOn (I := I) g β u J DJ l r)
    (hWl : W l = (J l, DJ l - Geodesic.chartChristoffelContraction (I := I) g β
      (deriv u l) (J l) (u l)))
    (hlr : l ≤ r) :
    ∀ t ∈ Icc l r, W t = (J t,
      DJ t - Geodesic.chartChristoffelContraction (I := I) g β
        (deriv u t) (J t) (u t)) := by
  have hlmem : l ∈ Icc l r := ⟨le_rfl, hlr⟩
  -- the variational solution is a Jacobi pair
  have hWJac : IsJacobiFieldOn (I := I) g β u (fun t => (W t).1)
      (fun t => (W t).2 + Geodesic.chartChristoffelContraction (I := I) g β
        (deriv u t) ((W t).1) (u t)) l r :=
    isJacobiFieldOn_of_variational (I := I) g β hmem hu hu' hW
  -- coefficient bound for Grönwall uniqueness
  have hucont : ContinuousOn u (Icc l r) := fun t ht =>
    (hu t ht).continuousAt.continuousWithinAt
  have hu'cont : ContinuousOn (deriv u) (Icc l r) := fun t ht =>
    (hu' t ht).continuousAt.continuousWithinAt
  obtain ⟨K, hK⟩ := exists_nnnorm_jacobiPairCoeffCoord_le (I := I) g β
    hucont hu'cont hmem
  -- the two Jacobi pairs share their data at `l`
  have hJl : (fun t => (W t).1) l = J l := by simp only [hWl]
  have hDJl : (fun t => (W t).2 + Geodesic.chartChristoffelContraction (I := I) g β
      (deriv u t) ((W t).1) (u t)) l = DJ l := by
    simp only [hWl]
    abel
  obtain ⟨heqJ, heqDJ⟩ := hWJac.eqOn_of_left (I := I) hK hJac hJl hDJl
  intro t ht
  have h1 : (W t).1 = J t := heqJ ht
  have h2 : (W t).2 + Geodesic.chartChristoffelContraction (I := I) g β
      (deriv u t) ((W t).1) (u t) = DJ t := heqDJ ht
  have h2' : (W t).2 = DJ t - Geodesic.chartChristoffelContraction (I := I) g β
      (deriv u t) (J t) (u t) := by
    rw [← h2, h1]
    abel
  exact Prod.ext h1 h2'

end PoincareLib

end
