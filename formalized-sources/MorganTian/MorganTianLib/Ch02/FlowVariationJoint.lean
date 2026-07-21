import DoCarmoLib.Riemannian.Geodesic.UniformExistence
import DoCarmoLib.Riemannian.Geodesic.FlowDependence
-- provides `Riemannian.FlowDependence.postcompCurve_sub`, which this file used to
-- restate locally (the two collided once both modules reached the root module)
import DoCarmoLib.Riemannian.Geodesic.VariationalEquation
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Morgan–Tian Ch. 2 — joint `C¹` regularity of the chart-local flow in `(x, t)`

Blueprint `prop:parallel-gradient-splitting` Step 4, analytic engine for the sharp
ℓ² product formula: the uniform-time local flow `Z` of an autonomous `C¹` field
`f : E → E` is **jointly `C¹` in the initial condition and the time** on the open
box `ball z₀ r × (0, T)`.

`FlowVariation.exists_localFlow_hasStrictFDerivAt` produced, at every base point
`x` of the flow ball separately, a strict space-derivative `D(x)` characterized by
the linearized (variational) Volterra equation along the base trajectory. The new
content here is **continuity of `x ↦ D(x)`** and its consequence, joint `C¹`:

* the space-derivative is the Neumann resolvent
  `D(x) = (1 - J∘M_{A₀(x)})⁻¹ ∘ const` — realized here by the *total* function
  `x ↦ Ring.inverse (1 - J∘M_{A₀(x)}) ∘ const`, which agrees with the unit inverse
  on the flow ball;
* the operator curve `A₀(x) = (df) ∘ σ(x)` is continuous in sup norm, by
  Heine–Cantor uniform continuity of `df` on the compact confinement ball plus
  Lipschitz dependence of the trajectory on its initial condition;
* the Volterra composite `A ↦ J∘M_A` is `T`-Lipschitz
  (`norm_intervalPrimitive_comp_postcompCurve_sub_le`), and Banach-algebra
  inversion is continuous at units (`NormedRing.inverse_continuousAt`);
* solutions of the variational equation are Lipschitz in time with constant
  `‖A₀‖ ‖D‖` (`norm_evalCLM_comp_sub_evalCLM_comp_le`), so the evaluated
  space-partial `(x, t) ↦ evalCLM t ∘ D(x)` is *jointly* continuous;
* the time-partial derivative is `f (Z x t)`, jointly continuous since the flow
  is; mathlib's `hasStrictFDerivAt_uncurry_coprod` (continuous partial
  derivatives ⟹ joint strict differentiability) then gives joint strict
  differentiability at every point of the open box, hence joint `C¹` by
  `Riemannian.FlowDependence.contDiffOn_one_of_forall_hasStrictFDerivAt`.

Main declaration:

* `exists_localFlow_hasStrictFDerivAt_uncurry` — a uniform-time local flow `Z` on
  `closedBall z₀ r` (flow ODE on `[-ε, ε]`, confinement in the prescribed open
  region `Ω`, joint continuity), a Picard time `0 < T < ε`, and a space-derivative
  field `Dx` such that on the open box `ball z₀ r ×ˢ Ioo 0 T`: each `Dx x t` is
  the space-partial derivative of `Z` at `(x, t)`, the field `↿Dx` is continuous,
  the uncurried flow `↿Z` is strictly differentiable at every point of the box
  with derivative `(Dx x t).coprod (τ ↦ τ • f (Z x t))`, and `↿Z` is `C¹` there.

Downstream (manifold level): transfer through a chart and glue by the flow group
law to make `(t, x) ↦ θ_t(x)` a `C¹` map on `ℝ × M`, the regularity needed for the
tilted-competitor-path and level-projection arguments of the sharp product metric
identity in blueprint `prop:parallel-gradient-splitting`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4 (blueprint
`lem:parallel-gradient-flow`, `prop:parallel-gradient-splitting`); do Carmo Ch. 3,
Thm 2.2 (flow dependence).
-/

open Set Filter Function Metric Riemannian
open Riemannian.FlowDependence
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ}

/- `postcompCurve_sub` (postcomposition by an operator-curve difference is the
difference of the postcompositions) is not restated here: it is already provided,
with the same statement and proof, by
`DoCarmoLib.Riemannian.Geodesic.VariationalEquation`, which this file imports
transitively. Restating it in the same `Riemannian.FlowDependence` namespace made
the two declarations collide at import time. -/

/-- **Math.** The Volterra composite `A ↦ J ∘ M_A` is `T`-Lipschitz in the operator
curve: `‖J∘M_A - J∘M_B‖ ≤ T ‖A - B‖`. This makes the Neumann resolvent of the
variational equation continuous in the base trajectory. -/
lemma norm_intervalPrimitive_comp_postcompCurve_sub_le (hT : (0:ℝ) ≤ T)
    (A B : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)) :
    ‖(intervalPrimitive hT).comp (postcompCurve A)
      - (intervalPrimitive hT).comp (postcompCurve B)‖ ≤ T * ‖A - B‖ := by
  rw [← ContinuousLinearMap.comp_sub, ← postcompCurve_sub]
  exact norm_intervalPrimitive_comp_postcompCurve_le hT (A - B)

/-- **Math.** The Volterra composite `A ↦ J ∘ M_A` of the interval primitive with
postcomposition by the operator curve `A`, as a linear map in `A` (linearity is
pointwise in the curve). -/
noncomputable def volterraCompositeLM (hT : (0:ℝ) ≤ T) :
    C(Set.Icc (0 : ℝ) T, E →L[ℝ] E) →ₗ[ℝ]
      (C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E)) where
  toFun A := (intervalPrimitive hT).comp (postcompCurve A)
  map_add' A B := ContinuousLinearMap.ext fun β => by
    show (intervalPrimitive hT) (postcompCurve (A + B) β)
      = (intervalPrimitive hT) (postcompCurve A β)
        + (intervalPrimitive hT) (postcompCurve B β)
    rw [show postcompCurve (A + B) β
        = postcompCurve A β + postcompCurve B β from by ext t; simp,
      map_add]
  map_smul' c A := ContinuousLinearMap.ext fun β => by
    show (intervalPrimitive hT) (postcompCurve (c • A) β)
      = c • (intervalPrimitive hT) (postcompCurve A β)
    rw [show postcompCurve (c • A) β
        = c • postcompCurve A β from by ext t; simp,
      map_smul]

/-- **Math.** The Volterra composite `A ↦ J ∘ M_A` is continuous in the operator
curve `A` (it is linear with operator norm at most `T`). -/
lemma continuous_intervalPrimitive_comp_postcompCurve (hT : (0:ℝ) ≤ T) :
    Continuous fun A : C(Set.Icc (0 : ℝ) T, E →L[ℝ] E) =>
      (intervalPrimitive hT).comp (postcompCurve A) := by
  have hb : ∀ A : C(Set.Icc (0 : ℝ) T, E →L[ℝ] E),
      ‖volterraCompositeLM (E := E) (T := T) hT A‖ ≤ T * ‖A‖ := fun A =>
    norm_intervalPrimitive_comp_postcompCurve_le hT A
  have h := AddMonoidHomClass.continuous_of_bound
    (volterraCompositeLM (E := E) (T := T) hT) T hb
  exact h

/-- **Math.** Evaluating an operator into curve space at a time is bounded by the
operator norm: `‖ev_t ∘ B‖ ≤ ‖B‖`. -/
lemma norm_evalCLM_comp_le (t : Set.Icc (0:ℝ) T)
    (B : E →L[ℝ] C(Set.Icc (0:ℝ) T, E)) :
    ‖(ContinuousMap.evalCLM ℝ t).comp B‖ ≤ ‖B‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun v =>
    ((B v).norm_coe_le_norm t).trans (B.le_opNorm v)

/-- **Math.** **Solutions of the variational Volterra equation are Lipschitz in
time**, uniformly over directions: if `D v - ∫₀ᵗ A₀ (D v) = const v` for every
`v`, then `‖ev_t ∘ D - ev_s ∘ D‖ ≤ ‖A₀‖ ‖D‖ |t - s|`. The increment of `D v`
between two times is the integral of the operator curve applied to `D v` over the
interval between them. This is the equicontinuity making the evaluated
space-partial derivative of a flow *jointly* continuous in `(x, t)`. -/
lemma norm_evalCLM_comp_sub_evalCLM_comp_le (hT : (0:ℝ) < T)
    {A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)} {D : E →L[ℝ] C(Set.Icc (0:ℝ) T, E)}
    (hD : ∀ v : E, D v - intervalPrimitive hT.le (postcompCurve A₀ (D v))
      = ContinuousMap.const _ v)
    (s t : Set.Icc (0:ℝ) T) :
    ‖(ContinuousMap.evalCLM ℝ t).comp D - (ContinuousMap.evalCLM ℝ s).comp D‖
      ≤ ‖A₀‖ * ‖D‖ * |(t:ℝ) - (s:ℝ)| := by
  have hconst : (0:ℝ) ≤ ‖A₀‖ * ‖D‖ * |(t:ℝ) - (s:ℝ)| := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hconst fun v => ?_
  show ‖D v t - D v s‖ ≤ ‖A₀‖ * ‖D‖ * |(t:ℝ) - (s:ℝ)| * ‖v‖
  set β : C(Set.Icc (0:ℝ) T, E) := postcompCurve A₀ (D v) with hβ_def
  have hβint : ∀ a b : ℝ, IntervalIntegrable
      (fun τ => β (Set.projIcc 0 T hT.le τ)) MeasureTheory.volume a b := fun a b =>
    (β.continuous.comp continuous_projIcc).intervalIntegrable a b
  have hev : ∀ u : Set.Icc (0:ℝ) T,
      D v u - intervalPrimitive hT.le β u = v := by
    intro u
    have h := congrArg (fun φ : C(Set.Icc (0:ℝ) T, E) => φ u) (hD v)
    simpa using h
  have hsub : D v t - D v s
      = ∫ τ in (s:ℝ)..(t:ℝ), β (Set.projIcc 0 T hT.le τ) := by
    have e1 : D v t = v + intervalPrimitive hT.le β t := by
      have h := hev t
      rw [sub_eq_iff_eq_add] at h
      rw [h, add_comm]
    have e2 : D v s = v + intervalPrimitive hT.le β s := by
      have h := hev s
      rw [sub_eq_iff_eq_add] at h
      rw [h, add_comm]
    have hint := intervalIntegral.integral_interval_sub_left
      (hβint 0 (t:ℝ)) (hβint 0 (s:ℝ))
    rw [e1, e2, intervalPrimitive_apply, intervalPrimitive_apply, ← hint]
    abel
  rw [hsub]
  have hβnorm : ‖β‖ ≤ ‖A₀‖ * (‖D‖ * ‖v‖) := by
    calc ‖β‖ ≤ ‖(postcompCurve A₀ : C(Set.Icc (0:ℝ) T, E) →L[ℝ] _)‖ * ‖D v‖ :=
        (postcompCurve A₀).le_opNorm (D v)
      _ ≤ ‖A₀‖ * ‖D v‖ :=
        mul_le_mul_of_nonneg_right (norm_postcompCurve_le A₀) (norm_nonneg _)
      _ ≤ ‖A₀‖ * (‖D‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (D.le_opNorm v) (by positivity)
  calc ‖∫ τ in (s:ℝ)..(t:ℝ), β (Set.projIcc 0 T hT.le τ)‖
      ≤ ‖β‖ * |(t:ℝ) - (s:ℝ)| := intervalIntegral.norm_integral_le_of_norm_le_const
        fun τ _ => β.norm_coe_le_norm _
    _ ≤ (‖A₀‖ * (‖D‖ * ‖v‖)) * |(t:ℝ) - (s:ℝ)| :=
        mul_le_mul_of_nonneg_right hβnorm (abs_nonneg _)
    _ = ‖A₀‖ * ‖D‖ * |(t:ℝ) - (s:ℝ)| * ‖v‖ := by ring

end Riemannian.FlowDependence

namespace MorganTianLib

/-- **Eng.** Curried restatement of mathlib's `hasStrictFDerivAt_uncurry_coprod`. All the
`↿`-vs-lambda unifications happen here, on opaque variables (cheap); call sites
never mention `↿` on concrete local functions, whose unification can blow the
heartbeat budget. -/
private theorem hasStrictFDerivAt_uncurry_coprod_curried
    {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E₁ × E₂} {f : E₁ → E₂ → F} {f₁ : E₁ → E₂ → E₁ →L[ℝ] F}
    {f₂ : E₁ → E₂ → E₂ →L[ℝ] F}
    (df₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (fun x => f x v.2) (f₁ v.1 v.2) v.1)
    (df₂ : ∀ᶠ v in 𝓝 u, HasFDerivAt (f v.1) (f₂ v.1 v.2) v.2)
    (cf₁ : ContinuousAt (fun v : E₁ × E₂ => f₁ v.1 v.2) u)
    (cf₂ : ContinuousAt (fun v : E₁ × E₂ => f₂ v.1 v.2) u) :
    HasStrictFDerivAt (fun v : E₁ × E₂ => f v.1 v.2)
      ((f₁ u.1 u.2).coprod (f₂ u.1 u.2)) u :=
  hasStrictFDerivAt_uncurry_coprod (f := f) (f₁ := f₁) (f₂ := f₂) (u := u)
    df₁ df₂ cf₁ cf₂

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

set_option maxHeartbeats 1600000 in
/-- **Math.** **The local flow of a `C¹` field is jointly `C¹` in `(x, t)` on an
open space-time box.** For `f : E → E` that is `C¹` on an open region `Ω ∋ z₀`,
there are `r, ε, T > 0` with `T < ε`, a local flow `Z` (flow ODE on `[-ε, ε]`,
starting anywhere in `closedBall z₀ r`, confined to `Ω`, jointly continuous), and
a space-derivative field `Dx : E → ℝ → E →L[ℝ] E` such that on the open box
`ball z₀ r ×ˢ Ioo 0 T`:

1. each `Dx x t` is the space-partial derivative: `HasFDerivAt (Z · t) (Dx x t) x`;
2. the field `↿Dx` is continuous on the box;
3. the uncurried flow `↿Z` is strictly differentiable at every point of the box
   with joint derivative `(v, τ) ↦ Dx x t v + τ • f (Z x t)`;
4. `↿Z` is `C¹` on the box.

Blueprint `prop:parallel-gradient-splitting` Step 4 (joint `C¹` engine for the
sharp ℓ² product formula). -/
theorem exists_localFlow_hasStrictFDerivAt_uncurry
    {f : E → E} {z₀ : E} {Ω : Set E} (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Ω)
    (hfs : ContDiffOn ℝ 1 f Ω) :
    ∃ (r ε T : ℝ) (Z : E → ℝ → E) (Dx : E → ℝ → E →L[ℝ] E),
      0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall z₀ r, Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z) (f (Z z t)) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ Ω)) ∧
      ContinuousOn ↿Z (closedBall z₀ r ×ˢ Icc (-ε) ε) ∧
      (∀ p : E × ℝ, p ∈ ball z₀ r ×ˢ Ioo 0 T →
        HasFDerivAt (fun y => Z y p.2) (Dx p.1 p.2) p.1) ∧
      ContinuousOn ↿Dx (ball z₀ r ×ˢ Ioo 0 T) ∧
      (∀ p : E × ℝ, p ∈ ball z₀ r ×ˢ Ioo 0 T →
        HasStrictFDerivAt ↿Z
          ((Dx p.1 p.2).coprod ((1 : ℝ →L[ℝ] ℝ).smulRight (f (Z p.1 p.2)))) p) ∧
      ContDiffOn ℝ 1 ↿Z (ball z₀ r ×ˢ Ioo 0 T) := by
  classical
  have hf : ContDiffAt ℝ 1 f z₀ := hfs.contDiffAt (hΩ.mem_nhds hz₀)
  -- a compact confinement ball inside the open region
  obtain ⟨ρc, hρc, hρcΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hΩ.mem_nhds hz₀)
  -- the derivative of the field is continuous on the region, hence bounded and
  -- uniformly continuous on the compact confinement ball
  have hcfder : ContinuousOn (fderiv ℝ f) Ω :=
    hfs.continuousOn_fderiv_of_isOpen hΩ le_rfl
  obtain ⟨C, hboundC⟩ := (isCompact_closedBall z₀ ρc).exists_bound_of_continuousOn
    (hcfder.mono hρcΩ)
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hboundC z₀ (mem_closedBall_self hρc.le))
  have hucfder : UniformContinuousOn (fderiv ℝ f) (closedBall z₀ ρc) :=
    (isCompact_closedBall z₀ ρc).uniformContinuousOn_of_continuous
      (hcfder.mono hρcΩ)
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
  -- trajectories stay in the region and in the compact confinement ball
  have hmemc : ∀ z ∈ closedBall z₀ r, ∀ t ∈ Icc (-ε) ε,
      Z z t ∈ closedBall z₀ ρc := fun z hz t ht =>
    ball_subset_closedBall ((hflow z hz).2.2 t ht)
  have hmemΩ : ∀ z ∈ closedBall z₀ r, ∀ t ∈ Icc (-ε) ε, Z z t ∈ Ω := fun z hz t ht =>
    hρcΩ (hmemc z hz t ht)
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
  have hσmemc : ∀ z ∈ closedBall z₀ r, ∀ t : Set.Icc (0 : ℝ) T,
      σ z t ∈ closedBall z₀ ρc := fun z hz t => by
    rw [hσ_ball z hz t]
    exact hmemc z hz t.1 (hIccTsub t.2)
  have hσmemΩ : ∀ z ∈ closedBall z₀ r, ∀ t : Set.Icc (0 : ℝ) T,
      σ z t ∈ Ω := fun z hz t => hρcΩ (hσmemc z hz t)
  -- `σ` is Lipschitz on the closed flow ball, hence continuous
  have hσlip : LipschitzOnWith L σ (closedBall z₀ r) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [ContinuousMap.dist_le (mul_nonneg L.coe_nonneg dist_nonneg)]
    intro t
    rw [hσ_ball x hx t, hσ_ball y hy t]
    exact (hLip t.1 (hIccTsub t.2)).dist_le_mul x hx y hy
  have hσcont : ContinuousOn σ (closedBall z₀ r) := hσlip.continuousOn
  -- the operator curve along the trajectory of each base point
  set Acurve : E → C(Set.Icc (0 : ℝ) T, E →L[ℝ] E) := fun x =>
    if hx : x ∈ closedBall z₀ r then
      ⟨fun t => fderiv ℝ f (σ x t),
        hcfder.comp_continuous (σ x).continuous (hσmemΩ x hx)⟩
    else ContinuousMap.const _ (fderiv ℝ f z₀) with hAdef
  have hA_ball : ∀ x ∈ closedBall z₀ r, ∀ t : Set.Icc (0 : ℝ) T,
      Acurve x t = fderiv ℝ f (σ x t) := by
    intro x hx t
    simp only [hAdef, dif_pos hx]
    rfl
  -- the operator curve is bounded by `C` on the closed flow ball
  have hAnorm : ∀ x ∈ closedBall z₀ r, ‖Acurve x‖ ≤ C := by
    intro x hx
    refine (ContinuousMap.norm_le _ hC0).mpr fun t => ?_
    rw [hA_ball x hx t]
    exact hboundC _ (hσmemc x hx t)
  -- the operator curve is continuous on the closed flow ball (Heine–Cantor)
  have hAcont : ContinuousOn Acurve (closedBall z₀ r) := by
    intro x hx
    refine (Metric.continuousWithinAt_iff (f := Acurve) (a := x)
      (s := closedBall z₀ r)).mpr fun δ hδ => ?_
    obtain ⟨η, hη, hηuc⟩ := Metric.uniformContinuousOn_iff.mp hucfder (δ / 2)
      (by positivity)
    refine ⟨η / (L + 1), by positivity, fun {y} hy hyx => ?_⟩
    have hyc : y ∈ closedBall z₀ r := hy
    have hσclose : dist (σ y) (σ x) < η := by
      have h1 : dist (σ y) (σ x) ≤ L * dist y x := hσlip.dist_le_mul y hyc x hx
      have h2 : (L : ℝ) * dist y x ≤ L * (η / (L + 1)) :=
        mul_le_mul_of_nonneg_left hyx.le L.coe_nonneg
      have h3 : (L : ℝ) * (η / (L + 1)) < η := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < (L:ℝ) + 1)]
        nlinarith [L.coe_nonneg, hη]
      linarith
    have hbound : dist (Acurve y) (Acurve x) ≤ δ / 2 := by
      rw [ContinuousMap.dist_le (by positivity)]
      intro t
      rw [hA_ball y hyc t, hA_ball x hx t]
      have hyt : σ y t ∈ closedBall z₀ ρc := hσmemc y hyc t
      have hxt : σ x t ∈ closedBall z₀ ρc := hσmemc x hx t
      have hdist : dist (σ y t) (σ x t) < η :=
        lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist t) hσclose
      exact (hηuc _ hyt _ hxt hdist).le
    linarith [hbound]
  -- the Volterra composite along each base point, contractive on the flow ball
  set JP : E → C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E) := fun x =>
    (intervalPrimitive hT.le).comp (postcompCurve (Acurve x)) with hJPdef
  have hJPnorm : ∀ x ∈ closedBall z₀ r, ‖JP x‖ < 1 := fun x hx =>
    lt_of_le_of_lt
      ((norm_intervalPrimitive_comp_postcompCurve_le hT.le (Acurve x)).trans
        (mul_le_mul_of_nonneg_left (hAnorm x hx) hT.le))
      hTC
  have hJPcont : ContinuousOn JP (closedBall z₀ r) :=
    (continuous_intervalPrimitive_comp_postcompCurve hT.le).comp_continuousOn
      hAcont
  -- the constant embedding
  set constE : E →L[ℝ] C(Set.Icc (0 : ℝ) T, E) :=
    ContinuousLinearMap.const ℝ (Set.Icc (0 : ℝ) T) with hconstEdef
  -- the space-derivative operator at each base point: the Neumann resolvent
  set Dmap : E → E →L[ℝ] C(Set.Icc (0 : ℝ) T, E) := fun x =>
    (Ring.inverse ((1 : C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E))
      - JP x)).comp constE with hDmapdef
  -- on the flow ball, `Dmap` is the unit inverse and solves the variational equation
  have hDmap_unit : ∀ x (hx : x ∈ closedBall z₀ r),
      Dmap x = (↑(Units.oneSub (JP x) (hJPnorm x hx))⁻¹ :
        C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E)).comp constE := by
    intro x hx
    rw [hDmapdef]
    simp only
    rw [NormedRing.inverse_one_sub (JP x) (hJPnorm x hx)]
  have hDeq : ∀ x ∈ closedBall z₀ r, ∀ v : E,
      Dmap x v - intervalPrimitive hT.le (postcompCurve (Acurve x) (Dmap x v))
        = ContinuousMap.const _ v := by
    intro x hx v
    have hval : ((1 : C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E))
        - JP x).comp
        (↑(Units.oneSub (JP x) (hJPnorm x hx))⁻¹ :
          C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E))
        = ContinuousLinearMap.id ℝ _ := (Units.oneSub (JP x) (hJPnorm x hx)).mul_inv
    have h := congrArg
      (fun B : C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E) =>
        B (constE v)) hval
    rw [hDmap_unit x hx]
    simpa [ContinuousLinearMap.sub_apply, sub_eq_iff_eq_add, hJPdef,
      hconstEdef] using h
  -- `Dmap` is continuous on the open flow ball
  have hDmapcont : ContinuousOn Dmap (ball z₀ r) := by
    intro x hx
    have hxc : x ∈ closedBall z₀ r := ball_subset_closedBall hx
    refine ContinuousWithinAt.mono ?_ (ball_subset_closedBall)
    have hJPat : ContinuousWithinAt JP (closedBall z₀ r) x := hJPcont x hxc
    have hsubat : ContinuousWithinAt
        (fun y => (1 : C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E))
          - JP y) (closedBall z₀ r) x :=
      continuousWithinAt_const.sub hJPat
    have hinvat : ContinuousAt Ring.inverse
        ((1 : C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E)) - JP x) := by
      have : ((1 : C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E)) - JP x)
          = ↑(Units.oneSub (JP x) (hJPnorm x hxc)) := rfl
      rw [this]
      exact NormedRing.inverse_continuousAt (Units.oneSub (JP x) (hJPnorm x hxc))
    have hcompright : Continuous
        (fun B : C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E) =>
          B.comp constE) :=
      (ContinuousLinearMap.isBoundedLinearMap_comp_right constE).continuous
    have hinner : ContinuousWithinAt
        (fun y => Ring.inverse
          ((1 : C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E)) - JP y))
        (closedBall z₀ r) x :=
      hinvat.comp_continuousWithinAt
        (f := fun y => (1 : C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E))
          - JP y) hsubat
    exact hcompright.continuousAt.comp_continuousWithinAt
      (f := fun y => Ring.inverse
        ((1 : C(Set.Icc (0 : ℝ) T, E) →L[ℝ] C(Set.Icc (0 : ℝ) T, E)) - JP y)) hinner
  -- strict space-differentiability at every point of the open flow ball
  have hstrictσ : ∀ x ∈ ball z₀ r, HasStrictFDerivAt σ (Dmap x) x := by
    intro x₀ hx₀
    have hx₀c : x₀ ∈ closedBall z₀ r := ball_subset_closedBall hx₀
    have hd : ∀ x ∈ Ω, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
      ((hfs.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hc : ∀ t : Set.Icc (0 : ℝ) T, ContinuousAt (fderiv ℝ f) (σ x₀ t) := fun t =>
      hcfder.continuousAt (hΩ.mem_nhds (hσmemΩ x₀ hx₀c t))
    have hTL : T * ‖Acurve x₀‖ < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hAnorm x₀ hx₀c) hT.le) hTC
    have hσc : ContinuousAt σ x₀ :=
      (hσcont.continuousWithinAt hx₀c).continuousAt
        (Filter.mem_of_superset (isOpen_ball.mem_nhds hx₀) ball_subset_closedBall)
    have hσres : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le f (x, σ x) = 0 := by
      filter_upwards [isOpen_ball.mem_nhds hx₀] with x hx
      have hx' : x ∈ closedBall z₀ r := ball_subset_closedBall hx
      obtain ⟨h0, hdZ, -⟩ := hflow x hx'
      exact picardResidual_eq_zero_of_hasDerivWithinAt hT
        (hfs.continuousOn) h0
        (fun t ht => hmemΩ x hx' t (hIccTsub ht))
        (fun t ht => (hdZ t (hIccTsub ht)).mono hIccTsub)
        (σ x) (fun t => hσ_ball x hx' t)
    exact hasStrictFDerivAt_of_picardResidual_curve hT hΩ hd (hσmemΩ x₀ hx₀c)
      hc (hA_ball x₀ hx₀c) hTL rfl hσc hσres (hDeq x₀ hx₀c)
  -- the space-derivative field on the open box
  set Dx : E → ℝ → E →L[ℝ] E := fun x t =>
    (ContinuousMap.evalCLM ℝ (Set.projIcc 0 T hT.le t)).comp (Dmap x) with hDxdef
  -- clause 1: the space-partial derivative on the box
  have hDx : ∀ p : E × ℝ, p ∈ ball z₀ r ×ˢ Ioo 0 T →
      HasFDerivAt (fun y => Z y p.2) (Dx p.1 p.2) p.1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have htmem : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
    have hproj : Set.projIcc 0 T hT.le t = ⟨t, htmem⟩ := Set.projIcc_of_mem _ htmem
    have hstrict : HasStrictFDerivAt (fun y => σ y ⟨t, htmem⟩)
        ((ContinuousMap.evalCLM ℝ (⟨t, htmem⟩ : Set.Icc (0:ℝ) T)).comp (Dmap x)) x :=
      (ContinuousMap.evalCLM ℝ _).hasStrictFDerivAt.comp x (hstrictσ x hx)
    have hcongr : (fun y => σ y ⟨t, htmem⟩) =ᶠ[𝓝 x] (fun y => Z y t) := by
      filter_upwards [Filter.mem_of_superset (isOpen_ball.mem_nhds hx)
        ball_subset_closedBall] with y hy
      exact hσ_ball y hy ⟨t, htmem⟩
    have := hstrict.hasFDerivAt.congr_of_eventuallyEq hcongr.symm
    simpa [hDxdef, hproj] using this
  -- clause 2: joint continuity of the space-derivative field on the box
  have hDxcont : ContinuousOn ↿Dx (ball z₀ r ×ˢ Ioo 0 T) := by
    rintro ⟨x₁, t₁⟩ ⟨hx₁, ht₁⟩
    refine ContinuousAt.continuousWithinAt ?_
    rw [Metric.continuousAt_iff]
    intro δ hδ
    have hx₁c : x₁ ∈ closedBall z₀ r := ball_subset_closedBall hx₁
    -- the Lipschitz-in-time constant of the base operator
    set Cop : ℝ := ‖Acurve x₁‖ * ‖Dmap x₁‖ with hCopdef
    have hCop0 : 0 ≤ Cop := by rw [hCopdef]; positivity
    -- continuity of `Dmap` at `x₁` gives closeness of the operator part
    have hDmapAt : ContinuousAt Dmap x₁ :=
      (hDmapcont x₁ hx₁).continuousAt (isOpen_ball.mem_nhds hx₁)
    obtain ⟨δ₁, hδ₁, hDmapδ⟩ := (Metric.continuousAt_iff (f := Dmap)
      (a := x₁)).mp hDmapAt (δ / 2) (by positivity)
    refine ⟨min δ₁ (δ / (2 * (Cop + 1))), lt_min hδ₁ (by positivity),
      fun {p} hp => ?_⟩
    obtain ⟨x, t⟩ := p
    rw [Prod.dist_eq, max_lt_iff] at hp
    obtain ⟨hpx, hpt⟩ := hp
    have hpx₁ : dist x x₁ < δ₁ := hpx.trans_le (min_le_left _ _)
    have hpt₁ : dist t t₁ < δ / (2 * (Cop + 1)) :=
      hpt.trans_le (min_le_right _ _)
    -- split into the operator increment and the time increment
    have hsplit : dist (↿Dx (x, t)) (↿Dx (x₁, t₁))
        ≤ ‖Dmap x - Dmap x₁‖ + Cop * dist t t₁ := by
      have htri : dist (↿Dx (x, t)) (↿Dx (x₁, t₁))
          ≤ dist (↿Dx (x, t)) (↿Dx (x₁, t)) + dist (↿Dx (x₁, t)) (↿Dx (x₁, t₁)) :=
        dist_triangle _ _ _
      have hterm1 : dist (↿Dx (x, t)) (↿Dx (x₁, t)) ≤ ‖Dmap x - Dmap x₁‖ := by
        rw [dist_eq_norm]
        have : ↿Dx (x, t) - ↿Dx (x₁, t)
            = (ContinuousMap.evalCLM ℝ (Set.projIcc 0 T hT.le t)).comp
              (Dmap x - Dmap x₁) := by
          simp [hDxdef, HasUncurry.uncurry, ContinuousLinearMap.comp_sub]
        rw [this]
        exact norm_evalCLM_comp_le _ _
      have hterm2 : dist (↿Dx (x₁, t)) (↿Dx (x₁, t₁)) ≤ Cop * dist t t₁ := by
        rw [dist_eq_norm]
        have hbound := norm_evalCLM_comp_sub_evalCLM_comp_le hT
          (A₀ := Acurve x₁) (D := Dmap x₁) (hDeq x₁ hx₁c)
          (Set.projIcc 0 T hT.le t₁) (Set.projIcc 0 T hT.le t)
        have hprojlip : |((Set.projIcc 0 T hT.le t : Set.Icc (0:ℝ) T) : ℝ)
            - ((Set.projIcc 0 T hT.le t₁ : Set.Icc (0:ℝ) T) : ℝ)| ≤ |t - t₁| := by
          have h := (LipschitzWith.projIcc (a := (0:ℝ)) (b := T) hT.le).dist_le_mul t t₁
          rw [NNReal.coe_one, one_mul] at h
          rw [Subtype.dist_eq, Real.dist_eq, Real.dist_eq] at h
          exact h
        calc ‖↿Dx (x₁, t) - ↿Dx (x₁, t₁)‖
            ≤ ‖Acurve x₁‖ * ‖Dmap x₁‖
              * |((Set.projIcc 0 T hT.le t : Set.Icc (0:ℝ) T) : ℝ)
                - ((Set.projIcc 0 T hT.le t₁ : Set.Icc (0:ℝ) T) : ℝ)| := hbound
          _ ≤ Cop * |t - t₁| := by
              rw [hCopdef]
              exact mul_le_mul_of_nonneg_left hprojlip hCop0
          _ = Cop * dist t t₁ := by rw [Real.dist_eq]
      linarith
    have h1 : ‖Dmap x - Dmap x₁‖ < δ / 2 :=
      lt_of_eq_of_lt (dist_eq_norm (Dmap x) (Dmap x₁)).symm (hDmapδ hpx₁)
    have h2 : Cop * dist t t₁ < δ / 2 := by
      have hlt : Cop * dist t t₁ ≤ Cop * (δ / (2 * (Cop + 1))) :=
        mul_le_mul_of_nonneg_left hpt₁.le hCop0
      have : Cop * (δ / (2 * (Cop + 1))) < δ / 2 := by
        rw [mul_div_assoc']
        rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (Cop + 1))
          (by norm_num : (0:ℝ) < 2)]
        nlinarith [hCop0, hδ]
      linarith
    linarith [hsplit]
  -- the time-partial derivative on the box
  have hVt : ∀ p : E × ℝ, p ∈ ball z₀ r ×ˢ Ioo 0 T →
      HasDerivAt (Z p.1) (f (Z p.1 p.2)) p.2 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have hxc : x ∈ closedBall z₀ r := ball_subset_closedBall hx
    have htI : t ∈ Icc (-ε) ε := hIccTsub ⟨ht.1.le, ht.2.le⟩
    have hnhds : Icc (-ε) ε ∈ 𝓝 t :=
      Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2, hTε])
    exact ((hflow x hxc).2.1 t htI).hasDerivAt hnhds
  -- joint strict differentiability at every point of the open box
  have hbox : IsOpen (ball z₀ r ×ˢ Ioo (0:ℝ) T) := isOpen_ball.prod isOpen_Ioo
  have hjoint : ∀ p : E × ℝ, p ∈ ball z₀ r ×ˢ Ioo 0 T →
      HasStrictFDerivAt ↿Z
        ((Dx p.1 p.2).coprod ((1 : ℝ →L[ℝ] ℝ).smulRight (f (Z p.1 p.2)))) p := by
    intro p hp
    have hev : ∀ᶠ v in 𝓝 p, v ∈ ball z₀ r ×ˢ Ioo (0:ℝ) T :=
      hbox.mem_nhds hp
    have df₁ : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun y => Z y v.2) (Dx v.1 v.2) v.1 := by
      filter_upwards [hev] with v hv
      exact hDx v hv
    have df₂ : ∀ᶠ v in 𝓝 p,
        HasFDerivAt (Z v.1) ((1 : ℝ →L[ℝ] ℝ).smulRight (f (Z v.1 v.2))) v.2 := by
      filter_upwards [hev] with v hv
      exact (hVt v hv).hasFDerivAt
    have cf₁ : ContinuousAt (fun v : E × ℝ => Dx v.1 v.2) p :=
      (hDxcont p hp).continuousAt (hbox.mem_nhds hp)
    have cf₂ : ContinuousAt
        (fun v : E × ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight (f (Z v.1 v.2))) p := by
      have hZat : ContinuousAt ↿Z p := by
        refine (hZcont.continuousAt (Filter.mem_of_superset (hbox.mem_nhds hp) ?_))
        rintro ⟨y, s⟩ ⟨hy, hs⟩
        exact ⟨ball_subset_closedBall hy, hIccTsub ⟨hs.1.le, hs.2.le⟩⟩
      have hZΩ : ↿Z p ∈ Ω := by
        obtain ⟨x, t⟩ := p
        obtain ⟨hx, ht⟩ := hp
        exact hmemΩ x (ball_subset_closedBall hx) t (hIccTsub ⟨ht.1.le, ht.2.le⟩)
      have hfat : ContinuousAt f (↿Z p) :=
        (hfs.continuousOn.continuousWithinAt hZΩ).continuousAt (hΩ.mem_nhds hZΩ)
      have hsmul : Continuous (fun v : E => (1 : ℝ →L[ℝ] ℝ).smulRight v) := by
        have := (ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).continuous
        convert this using 1
      exact (hsmul.continuousAt).comp (hfat.comp hZat)
    have h := hasStrictFDerivAt_uncurry_coprod_curried (f := Z) (f₁ := Dx)
      (f₂ := fun x t => (1 : ℝ →L[ℝ] ℝ).smulRight (f (Z x t))) (u := p)
      df₁ df₂ cf₁ cf₂
    exact h
  -- joint `C¹` on the box
  have hC1 : ContDiffOn ℝ 1 ↿Z (ball z₀ r ×ˢ Ioo 0 T) :=
    contDiffOn_one_of_forall_hasStrictFDerivAt hbox hjoint
  exact ⟨r, ε, T, Z, Dx, hr, hε, hT, hTε,
    fun z hz => ⟨(hflow z hz).1, (hflow z hz).2.1, hmemΩ z hz⟩,
    hZcont, hDx, hDxcont, hjoint, hC1⟩

end MorganTianLib

end
