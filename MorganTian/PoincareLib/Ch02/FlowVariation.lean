import OpenGALib.Riemannian.Geodesic.UniformExistence
import OpenGALib.Riemannian.Geodesic.FlowDependence

/-!
# Morgan–Tian Ch. 2 — C¹ dependence of the local flow of a `C¹` vector field

Blueprint `lem:parallel-gradient-flow`(4), analytic engine. The uniform-time
local flow of an autonomous `C¹` field `f : E → E` (mathlib Picard–Lindelöf,
packaged by `Riemannian.exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt`)
is upgraded with **strict differentiability in the initial condition** at every
point of the flow ball, following do Carmo's geodesic-spray instantiation
(`Riemannian.Geodesic.exists_uniform_geodesic_flow_hasStrictFDerivAt`) of the
abstract non-equilibrium C¹-dependence theorem
(`Riemannian.FlowDependence.exists_hasStrictFDerivAt_of_picardResidual_curve`),
but for a **general** `C¹` field on an open confinement region — the form
needed for the chart representation of the gradient field of a Busemann-type
function (and its negation, for negative flow times).

* `exists_localFlow_hasStrictFDerivAt` — a uniform-time local flow `Z` on
  `closedBall z₀ r` (flow ODE on `[-ε, ε]`, confinement in the prescribed
  open region `Ω`, joint continuity), a Picard time `0 < T < ε`, the flow read
  as a curve family `σ`, and at every initial condition in the open flow ball
  a strict Fréchet derivative `D` of `σ` characterized by the linearized
  (variational) integral equation `D v = v + ∫₀ᵗ A₀(s)\,(D v)(s)\,ds` along
  the operator curve `A₀(t) = (df)_{σ(x₀)(t)}`.
* `exists_extension_hasDerivAt_variational` — the **variational solutions
  are genuine ODE solutions**: any curve satisfying the linearized integral
  equation extends to a function on `ℝ` with two-sided derivative
  `A₀(t)\,(d(t))` at every `t ∈ [0, T]` (fundamental theorem of calculus).
  This is the input shape of the chart-level norm-constancy
  (`chartMetricInner_variational_gradientField_eq_left`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-flow`); do Carmo Ch. 3, Thm 2.2 (flow
dependence).
-/

open Set Filter Function Metric Riemannian
open Riemannian.FlowDependence
open scoped Manifold Topology ContDiff NNReal

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- **Math.** **The local flow of a `C¹` field is strictly differentiable in
its initial condition at every point of the flow ball.** For `f : E → E`
that is `C¹` on an open region `Ω ∋ z₀`, there are `r, ε > 0`, a local flow
`Z` (flow ODE on `[-ε, ε]`, starting anywhere in `closedBall z₀ r`, confined
to `Ω`, jointly continuous), and a Picard time `0 < T < ε` with the flow read
as a curve family `σ : E → C([0, T], E)`, such that at every initial
condition `x₀` in the **open** flow ball, `σ` is strictly Fréchet
differentiable at `x₀` with derivative `D` characterized by the linearized
(variational) integral equation
`D v - ∫₀ᵗ A₀(s)\,((D v)(s))\,ds = const v` along the operator curve
`A₀(t) = (df)_{σ(x₀)(t)}`. Blueprint `lem:parallel-gradient-flow`(4). -/
theorem exists_localFlow_hasStrictFDerivAt
    {f : E → E} {z₀ : E} {Ω : Set E} (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Ω)
    (hfs : ContDiffOn ℝ 1 f Ω) :
    ∃ (r ε T : ℝ) (Z : E → ℝ → E) (σ : E → C(Set.Icc (0:ℝ) T, E)) (hT : 0 < T),
      0 < r ∧ 0 < ε ∧ T < ε ∧
      (∀ z ∈ closedBall z₀ r, Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z) (f (Z z t)) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ Ω)) ∧
      ContinuousOn ↿Z (closedBall z₀ r ×ˢ Icc (-ε) ε) ∧
      (∀ z ∈ closedBall z₀ r, ∀ t : Set.Icc (0:ℝ) T, σ z t = Z z t.1) ∧
      (∀ x₀ ∈ ball z₀ r,
        ∃ (D : E →L[ℝ] C(Set.Icc (0:ℝ) T, E))
          (A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)),
          (∀ t : Set.Icc (0:ℝ) T, A₀ t = fderiv ℝ f (σ x₀ t)) ∧
          (∀ v : E, D v - intervalPrimitive hT.le (postcompCurve A₀ (D v))
            = ContinuousMap.const _ v) ∧
          HasStrictFDerivAt σ D x₀) := by
  classical
  have hf : ContDiffAt ℝ 1 f z₀ := hfs.contDiffAt (hΩ.mem_nhds hz₀)
  -- a compact confinement ball inside the open region
  obtain ⟨ρc, hρc, hρcΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hΩ.mem_nhds hz₀)
  -- the derivative of the field is continuous on the region, hence bounded on
  -- the compact confinement ball
  have hcfder : ContinuousOn (fderiv ℝ f) Ω :=
    hfs.continuousOn_fderiv_of_isOpen hΩ le_rfl
  obtain ⟨C, hboundC⟩ := (isCompact_closedBall z₀ ρc).exists_bound_of_continuousOn
    (hcfder.mono hρcΩ)
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hboundC z₀ (mem_closedBall_self hρc.le))
  -- the local flow, confined to the open confinement ball
  have hU : ball z₀ ρc ∈ 𝓝 z₀ := ball_mem_nhds z₀ hρc
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip⟩ :=
    Riemannian.exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt hf hU
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
  -- trajectories stay in the region
  have hmemΩ : ∀ z ∈ closedBall z₀ r, ∀ t ∈ Icc (-ε) ε, Z z t ∈ Ω := fun z hz t ht =>
    hρcΩ (ball_subset_closedBall ((hflow z hz).2.2 t ht))
  -- joint continuity of the flow, from the Lipschitz dependence
  have hZcont : ContinuousOn ↿Z (closedBall z₀ r ×ˢ Icc (-ε) ε) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith (↿Z) L
      (fun z hz => HasDerivWithinAt.continuousOn (hflow z hz).2.1) hLip
  -- the flow read as a curve family on `[0, T]`
  set σ : E → C(Set.Icc (0 : ℝ) T, E) := fun x =>
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
  refine ⟨r, ε, T, Z, σ, hT, hr, hε, hTε, ?_, hZcont, hσ_ball, ?_⟩
  · -- the flow clauses, with confinement in `Ω`
    intro z hz
    obtain ⟨h0, hd, -⟩ := hflow z hz
    exact ⟨h0, hd, hmemΩ z hz⟩
  · -- strict differentiability at every initial condition in the open flow ball
    intro x₀ hx₀
    have hx₀c : x₀ ∈ closedBall z₀ r := ball_subset_closedBall hx₀
    -- the base trajectory stays in the region and the compact ball
    have hα₀Ω : ∀ t : Set.Icc (0 : ℝ) T, σ x₀ t ∈ Ω := fun t => by
      rw [hσ_ball x₀ hx₀c t]
      exact hmemΩ x₀ hx₀c t.1 (hIccTsub t.2)
    have hα₀ball : ∀ t : Set.Icc (0 : ℝ) T, σ x₀ t ∈ closedBall z₀ ρc := fun t => by
      rw [hσ_ball x₀ hx₀c t]
      exact ball_subset_closedBall ((hflow x₀ hx₀c).2.2 t.1 (hIccTsub t.2))
    -- differentiability data for the field on the region
    have hd : ∀ x ∈ Ω, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
      ((hfs.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hc : ∀ t : Set.Icc (0 : ℝ) T, ContinuousAt (fderiv ℝ f) (σ x₀ t) := fun t =>
      hcfder.continuousAt (hΩ.mem_nhds (hα₀Ω t))
    -- the operator curve along the base trajectory, bounded by `C`
    set A₀ : C(Set.Icc (0 : ℝ) T, E →L[ℝ] E) :=
      ⟨fun t => fderiv ℝ f (σ x₀ t),
        hcfder.comp_continuous (σ x₀).continuous hα₀Ω⟩ with hA₀def
    have hA₀ : ∀ t : Set.Icc (0 : ℝ) T, A₀ t = fderiv ℝ f (σ x₀ t) := fun _ => rfl
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
    have hσres : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le f (x, σ x) = 0 := by
      filter_upwards [isOpen_ball.mem_nhds hx₀] with x hx
      have hx' : x ∈ closedBall z₀ r := ball_subset_closedBall hx
      obtain ⟨h0, hdZ, -⟩ := hflow x hx'
      exact picardResidual_eq_zero_of_hasDerivWithinAt hT
        (hfs.continuousOn) h0
        (fun t ht => hmemΩ x hx' t (hIccTsub ht))
        (fun t ht => (hdZ t (hIccTsub ht)).mono hIccTsub)
        (σ x) (fun t => hσ_ball x hx' t)
    -- the non-equilibrium C¹-dependence theorem
    obtain ⟨D, hD, hstrict⟩ :=
      exists_hasStrictFDerivAt_of_picardResidual_curve hT hΩ hd hα₀Ω hc hA₀ hTL
        rfl hσc hσres
    exact ⟨D, A₀, hA₀, hD, hstrict⟩

/-- **Math.** **Variational solutions are genuine ODE solutions** (fundamental
theorem of calculus): a curve `d ∈ C([0, T], E)` satisfying the linearized
integral equation `d - ∫₀ᵗ A₀(s)\,(d(s))\,ds = const v` extends to a function
on `ℝ` agreeing with `d` on `[0, T]` and having the two-sided derivative
`A₀(t)\,(d(t))` at every `t ∈ [0, T]` — including the endpoints, which is
what the metric-constancy argument along variational pairs consumes. -/
theorem exists_extension_hasDerivAt_variational {T : ℝ} (hT : 0 < T)
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} {dc : C(Set.Icc (0:ℝ) T, E)} {v : E}
    (hD : dc - intervalPrimitive hT.le (postcompCurve A₀ dc)
      = ContinuousMap.const _ v) :
    ∃ dext : ℝ → E,
      (∀ t : Set.Icc (0:ℝ) T, dext t = dc t) ∧
      ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivAt dext
        (A₀ (Set.projIcc 0 T hT.le t) (dc (Set.projIcc 0 T hT.le t))) t := by
  classical
  have hβcont : Continuous
      (fun s : ℝ => (postcompCurve A₀ dc) (Set.projIcc 0 T hT.le s)) :=
    (postcompCurve A₀ dc).continuous.comp continuous_projIcc
  -- the integral extension
  refine ⟨fun s => v + ∫ τ in (0:ℝ)..s,
    (postcompCurve A₀ dc) (Set.projIcc 0 T hT.le τ), ?_, ?_⟩
  · -- agreement with `dc` on `[0, T]`, from the integral equation
    intro t
    have hEq := congrFun
      (congrArg (fun (φ : C(Set.Icc (0:ℝ) T, E)) => (φ : _ → E)) hD) t
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply,
      intervalPrimitive_apply] at hEq
    rw [← hEq]
    abel
  · intro t ht
    -- the fundamental theorem of calculus at `t`
    have hFTC : HasDerivAt
        (fun s => ∫ τ in (0:ℝ)..s, (postcompCurve A₀ dc) (Set.projIcc 0 T hT.le τ))
        ((postcompCurve A₀ dc) (Set.projIcc 0 T hT.le t)) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hβcont.intervalIntegrable _ _)
        (hβcont.stronglyMeasurableAtFilter _ _)
        hβcont.continuousAt
    have hval : (postcompCurve A₀ dc) (Set.projIcc 0 T hT.le t)
        = A₀ (Set.projIcc 0 T hT.le t) (dc (Set.projIcc 0 T hT.le t)) := rfl
    simpa [hval] using hFTC.const_add v

end PoincareLib

end
