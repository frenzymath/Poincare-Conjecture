/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Geodesic/FlowC2Dependence.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Geodesic.VariationalEquation
import PetersenLib.Riemannian.Geodesic.UniformExistence

set_option linter.unusedSectionVars false
-- the sup-norm instance on curves valued in operators of the extended state space
-- needs nested pending instance synthesis beyond the default depth
set_option maxSynthPendingDepth 3

/-!
# C² dependence of the local geodesic flow on its initial condition

This file instantiates the abstract second-order dependence theory of
`VariationalEquation.lean` for the coordinate geodesic spray: the uniform-time local
geodesic flow `σ` of `FlowC1Dependence.lean` is upgraded with the **variational
(operator) flow** `τ` along each trajectory, satisfying

* `τ x` solves the operator-valued linear Volterra equation
  `W = 1 + ∫₀ᵗ (dF)_{σ x (s)} ∘ W(s) ds` along the base trajectory `σ x` — constructed
  *by the Neumann series* `τ x = (1 - J_x)⁻¹ (const 1)`, which yields existence,
  uniqueness *and* continuity in `x` simultaneously (the Volterra operator `J_x` depends
  continuously on `x` and has norm `≤ T·C < 1/2` uniformly on the flow ball);
* **the variational flow computes the derivative of the flow**: at every initial
  condition `x₀` in the open flow ball, `σ` is strictly differentiable with derivative
  `v ↦ (t ↦ τ x₀ (t) v)` (`PetersenLib.FlowDependence.flowDeriv_eq_applyCurve_opFlow`);
* **second-order dependence**: the family `x ↦ τ x` is itself strictly differentiable at
  every point of the open flow ball
  (`PetersenLib.FlowDependence.exists_hasStrictFDerivAt_opFlow_of_picardResidual_curve`),
  i.e. the geodesic flow is `C²` in its initial condition.

The Picard time `T` is chosen against **both** the first and the second derivative
bounds of the spray on a compact confinement ball (`T·(C + 2C₂) < 1`), so that the
contraction estimates for the base system *and* for the extended (variational) system
hold simultaneously for every initial condition in the flow ball.

This is the C²-regularity content of do Carmo, *PetersenLib Geometry*, Ch. 3,
Theorem 2.2 / Proposition 2.7 for the geodesic spray. Downstream, evaluation at the
Picard time and the fibre-scaling identification `exp_p(w) = π(Z(φ_p(p), w/T)(T))` make
the exponential map `C²` on a ball around the origin of `T_pM`
(`PetersenLib.Exponential.exists_contDiffOn_two_extChartAt_expMap_ball`).
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

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **Math.** **The local geodesic flow is `C²` in its initial condition at every point of
the flow ball** (do Carmo Ch. 3, Thm 2.2 / Prop. 2.7, second-order dependence for the
geodesic spray). There are `r, ε > 0`, a local flow `Z` of the coordinate spray at `p`
with the four clauses of `exists_uniform_geodesic_flow`, a Picard time `0 < T < ε`, the
flow read as a curve family `σ : E × E → C([0, T], E × E)`, and the **variational
(operator) flow family** `τ : E × E → C([0, T], (E × E) →L (E × E))` along it, such that
at *every* initial condition `x₀` in the open flow ball:

* `σ` is strictly Fréchet differentiable at `x₀` and its derivative **is computed by the
  variational flow**: `Dσ(x₀) v = (t ↦ τ x₀ (t) v)`;
* the variational-flow family `τ` is itself strictly Fréchet differentiable at `x₀`.

Together these say the local geodesic flow is `C²` in its initial condition. The
variational flow is constructed by the Neumann series for the operator-valued Volterra
equation `W = 1 + ∫₀ᵗ (dF)_{σ x (s)} ∘ W(s) ds`, the Picard time being chosen so that the
contraction estimates for the base and the extended (variational) systems hold
simultaneously on the flow ball. -/
theorem exists_uniform_geodesic_flow_hasStrictFDerivAt_opFlow
    (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E) (L : ℝ≥0)
      (σ : E × E → C(Set.Icc (0:ℝ) T, E × E))
      (τ : E × E → C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)))
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
        ∃ D : E × E →L[ℝ] C(Set.Icc (0:ℝ) T, E × E),
          (∀ v : E × E,
            D v = postcomp (ContinuousLinearMap.apply ℝ (E × E) v) (τ x₀)) ∧
          HasStrictFDerivAt σ D x₀) ∧
      (∀ x₀ ∈ ball ((extChartAt I p p, (0 : E)) : E × E) r,
        ∃ Dτ : E × E →L[ℝ] C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)),
          HasStrictFDerivAt τ Dτ x₀) := by
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
  -- the spray, its derivative and its second derivative on the chart region
  have hFs : ContDiffOn ℝ ∞ F ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    contDiffOn_geodesicSprayCoord_prod (I := I) g p
  have hFs' : ContDiffOn ℝ ∞ (fderiv ℝ F) ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    hFs.fderiv_of_isOpen hopen (by simp)
  have hcfder : ContinuousOn (fderiv ℝ F) ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    hFs.continuousOn_fderiv_of_isOpen hopen (by exact_mod_cast le_top)
  have hcfder2 : ContinuousOn (fderiv ℝ (fderiv ℝ F))
      ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    hFs'.continuousOn_fderiv_of_isOpen hopen (by exact_mod_cast le_top)
  -- uniform first- and second-derivative bounds on the compact confinement ball
  obtain ⟨C, hboundC⟩ := (isCompact_closedBall z₀ ρc).exists_bound_of_continuousOn
    (hcfder.mono hρcΩ)
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _) (hboundC z₀ (mem_closedBall_self hρc.le))
  obtain ⟨C₂, hboundC₂⟩ := (isCompact_closedBall z₀ ρc).exists_bound_of_continuousOn
    (hcfder2.mono hρcΩ)
  have hC₂0 : 0 ≤ C₂ :=
    le_trans (norm_nonneg _) (hboundC₂ z₀ (mem_closedBall_self hρc.le))
  -- the local flow, confined to the open confinement ball
  have hU : ball z₀ ρc ∈ 𝓝 z₀ := ball_mem_nhds z₀ hρc
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip⟩ :=
    exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt hf hU
  -- the Picard time: short against `ε` and against BOTH derivative bounds
  set T : ℝ := min (ε / 2) (1 / (2 * (C + 2 * C₂ + 1))) with hTdef
  have hT : 0 < T := lt_min (by positivity) (by positivity)
  have hTε : T < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hTC : T * C ≤ 1 / 2 := by
    have h1 : T ≤ 1 / (2 * (C + 2 * C₂ + 1)) := min_le_right _ _
    have h2 : (0 : ℝ) < 2 * (C + 2 * C₂ + 1) := by positivity
    have h3 : T * C ≤ (1 / (2 * (C + 2 * C₂ + 1))) * C :=
      mul_le_mul_of_nonneg_right h1 hC0
    have h4 : (1 / (2 * (C + 2 * C₂ + 1))) * (2 * (C + 2 * C₂ + 1)) = 1 :=
      one_div_mul_cancel (ne_of_gt h2)
    nlinarith
  have hTA₂ : T * (C + C₂ * 2) < 1 := by
    have h1 : T ≤ 1 / (2 * (C + 2 * C₂ + 1)) := min_le_right _ _
    have h2 : (0 : ℝ) < 2 * (C + 2 * C₂ + 1) := by positivity
    have h3 : T * (C + C₂ * 2) ≤ (1 / (2 * (C + 2 * C₂ + 1))) * (C + C₂ * 2) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h4 : (1 / (2 * (C + 2 * C₂ + 1))) * (2 * (C + 2 * C₂ + 1)) = 1 :=
      one_div_mul_cancel (ne_of_gt h2)
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
  -- the operator curve of the spray linearization along each trajectory
  set A : E × E → C(Set.Icc (0 : ℝ) T, (E × E) →L[ℝ] (E × E)) := fun x =>
    if hx : x ∈ closedBall z₀ r then
      ⟨fun t => fderiv ℝ F (Z x t.1), by
        have hcont : ContinuousOn (Z x) (Icc (-ε) ε) := fun s hs =>
          ((hflow x hx).2.1 s hs).continuousWithinAt
        have hZcont : Continuous fun t : Set.Icc (0:ℝ) T => Z x t.1 :=
          hcont.comp_continuous continuous_subtype_val fun t => hIccTsub t.2
        exact hcfder.comp_continuous hZcont fun t =>
          hmemΩ x hx t.1 (hIccTsub t.2)⟩
    else ContinuousMap.const _ (fderiv ℝ F z₀) with hAdef
  have hA_ball : ∀ x ∈ closedBall z₀ r, ∀ t : Set.Icc (0 : ℝ) T,
      A x t = fderiv ℝ F (Z x t.1) := by
    intro x hx t
    simp only [hAdef, dif_pos hx]
    rfl
  have hAnorm : ∀ x ∈ closedBall z₀ r, ‖A x‖ ≤ C := by
    intro x hx
    refine (ContinuousMap.norm_le _ hC0).mpr fun t => ?_
    rw [hA_ball x hx t]
    exact hboundC _ (ball_subset_closedBall ((hflow x hx).2.2 t.1 (hIccTsub t.2)))
  -- the Volterra operator of the variational equation along each trajectory
  set JP : E × E → (C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
      C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) := fun x =>
    (intervalPrimitive hT.le).comp
      (postcompCurve (postcomp
        (ContinuousLinearMap.compL ℝ (E × E) (E × E) (E × E)) (A x))) with hJPdef
  have hJPle : ∀ x ∈ closedBall z₀ r, ‖JP x‖ ≤ T * C := by
    intro x hx
    refine le_trans (norm_intervalPrimitive_comp_postcompCurve_le hT.le _) ?_
    exact mul_le_mul_of_nonneg_left
      (le_trans (norm_postcomp_compL_le (A x)) (hAnorm x hx)) hT.le
  have hJPhalf : ∀ x ∈ closedBall z₀ r, ‖JP x‖ ≤ 1 / 2 := fun x hx =>
    (hJPle x hx).trans hTC
  have hJPn : ∀ x ∈ closedBall z₀ r, ‖JP x‖ < 1 := fun x hx =>
    lt_of_le_of_lt (hJPhalf x hx) (by norm_num)
  -- the variational flow family, by the Neumann series
  set τ : E × E → C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) := fun x =>
    Ring.inverse ((1 : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
        C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) - JP x)
      (ContinuousMap.const _ (1 : (E × E) →L[ℝ] (E × E))) with hτdef
  -- the variational flow solves the operator Volterra equation
  have hτeq : ∀ x ∈ closedBall z₀ r,
      ((1 : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
          C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) - JP x) (τ x)
        = ContinuousMap.const _ (1 : (E × E) →L[ℝ] (E × E)) := by
    intro x hx
    set w : (C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
        C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)))ˣ :=
      Units.oneSub (JP x) (hJPn x hx) with hwdef
    have hτx : τ x = (↑w⁻¹ : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
        C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)))
          (ContinuousMap.const _ (1 : (E × E) →L[ℝ] (E × E))) := by
      have hinv : Ring.inverse ((1 : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
          C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) - JP x)
          = (↑w⁻¹ : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
              C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) := by
        have hval : ((1 : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
            C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) - JP x) = (↑w : _) := rfl
        rw [hval, Ring.inverse_unit]
      show Ring.inverse ((1 : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
          C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) - JP x)
        (ContinuousMap.const _ (1 : (E × E) →L[ℝ] (E × E))) = _
      rw [hinv]
    rw [hτx]
    have hmul : ((1 : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
        C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) - JP x)
          ((↑w⁻¹ : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
            C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)))
              (ContinuousMap.const _ (1 : (E × E) →L[ℝ] (E × E))))
        = ((↑w * ↑w⁻¹ : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
            C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))))
              (ContinuousMap.const _ (1 : (E × E) →L[ℝ] (E × E))) := rfl
    rw [hmul, w.mul_inv]
    rfl
  -- fixed-point form: the extended-residual input for the bridging lemma
  have hτfix : ∀ x ∈ closedBall z₀ r,
      τ x - ContinuousMap.const _ (1 : (E × E) →L[ℝ] (E × E))
        - intervalPrimitive hT.le
            (postcompCurve (postcomp
              (ContinuousLinearMap.compL ℝ (E × E) (E × E) (E × E)) (A x)) (τ x))
        = 0 := by
    intro x hx
    have h := hτeq x hx
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at h
    have hJPapp : (JP x) (τ x) = intervalPrimitive hT.le
        (postcompCurve (postcomp
          (ContinuousLinearMap.compL ℝ (E × E) (E × E) (E × E)) (A x)) (τ x)) := rfl
    rw [← hJPapp]
    have hre : τ x - ContinuousMap.const _ (1 : (E × E) →L[ℝ] (E × E)) - (JP x) (τ x)
        = (τ x - (JP x) (τ x))
          - ContinuousMap.const _ (1 : (E × E) →L[ℝ] (E × E)) := by abel
    rw [hre, h, sub_self]
  -- norm bound on the variational flow, uniform on the flow ball
  have hτnorm : ∀ x ∈ closedBall z₀ r, ‖τ x‖ ≤ 2 := by
    intro x hx
    have h := hτeq x hx
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at h
    have hτadd : τ x = ContinuousMap.const _ (1 : (E × E) →L[ℝ] (E × E)) + (JP x) (τ x) :=
      sub_eq_iff_eq_add.mp h
    have hone : ‖ContinuousMap.const (Set.Icc (0:ℝ) T)
        (1 : (E × E) →L[ℝ] (E × E))‖ ≤ 1 := by
      refine (ContinuousMap.norm_le _ zero_le_one).mpr fun t => ?_
      show ‖(1 : (E × E) →L[ℝ] (E × E))‖ ≤ 1
      rw [ContinuousLinearMap.one_def]
      exact ContinuousLinearMap.norm_id_le
    have hb : ‖τ x‖ ≤ 1 + (1 / 2) * ‖τ x‖ := by
      calc ‖τ x‖ = ‖ContinuousMap.const _ (1 : (E × E) →L[ℝ] (E × E)) + (JP x) (τ x)‖ := by
            rw [← hτadd]
        _ ≤ ‖ContinuousMap.const (Set.Icc (0:ℝ) T) (1 : (E × E) →L[ℝ] (E × E))‖
            + ‖(JP x) (τ x)‖ := norm_add_le _ _
        _ ≤ 1 + ‖JP x‖ * ‖τ x‖ := add_le_add hone ((JP x).le_opNorm (τ x))
        _ ≤ 1 + (1 / 2) * ‖τ x‖ :=
            add_le_add le_rfl
              (mul_le_mul_of_nonneg_right (hJPhalf x hx) (norm_nonneg _))
    linarith
  -- the base solutions satisfy the Picard integral equation on the closed flow ball
  have hres1 : ∀ x ∈ closedBall z₀ r, picardResidual hT.le F (x, σ x) = 0 := by
    intro x hx
    obtain ⟨h0, hdZ, -⟩ := hflow x hx
    exact picardResidual_eq_zero_of_hasDerivWithinAt hT hFs.continuousOn h0
      (fun t ht => hmemΩ x hx t (hIccTsub ht))
      (fun t ht => (hdZ t (hIccTsub ht)).mono hIccTsub)
      (σ x) (fun t => hσ_ball x hx t)
  -- the pairs (σ x, τ x) satisfy the extended Picard equation on the closed flow ball
  have hresExt : ∀ x ∈ closedBall z₀ r,
      picardResidual hT.le (variationalField F (fderiv ℝ F))
        ((x, (1 : (E × E) →L[ℝ] (E × E))), curveProd (σ x, τ x)) = 0 := by
    intro x hx
    refine picardResidual_variationalField_eq_zero hT hFs.continuousOn hcfder
      (fun t => ?_) (hres1 x hx) (fun t => ?_) (hτfix x hx)
    · rw [hσ_ball x hx t]
      exact hmemΩ x hx t.1 (hIccTsub t.2)
    · rw [hA_ball x hx t, hσ_ball x hx t]
  -- differentiability data for the spray on the chart region
  have hd : ∀ x ∈ (extChartAt I p).target ×ˢ (univ : Set E),
      HasFDerivAt F (fderiv ℝ F x) x := fun x hx =>
    ((hFs.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hd2 : ∀ x ∈ (extChartAt I p).target ×ˢ (univ : Set E),
      HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x := fun x hx =>
    ((hFs'.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  -- continuity of the flow family on the flow ball, from Lipschitz dependence
  have hσc : ∀ x₀ ∈ ball z₀ r, ContinuousAt σ x₀ := by
    intro x₀ hx₀
    have hlips : LipschitzOnWith L σ (closedBall z₀ r) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [ContinuousMap.dist_le (mul_nonneg L.coe_nonneg dist_nonneg)]
      intro t
      rw [hσ_ball x hx t, hσ_ball y hy t]
      exact (hLip t.1 (hIccTsub t.2)).dist_le_mul x hx y hy
    exact (hlips.continuousOn.continuousWithinAt (ball_subset_closedBall hx₀)).continuousAt
      (Filter.mem_of_superset (isOpen_ball.mem_nhds hx₀) ball_subset_closedBall)
  -- continuity of the operator-curve family on the flow ball (Heine + Lipschitz)
  have hAc : ∀ x₀ ∈ ball z₀ r, ContinuousAt A x₀ := by
    intro x₀ hx₀
    rw [Metric.continuousAt_iff]
    intro ε' hε'
    have hcball : ∀ y ∈ closedBall z₀ ρc, ContinuousAt (fderiv ℝ F) y := fun y hy =>
      hcfder.continuousAt (hopen.mem_nhds (hρcΩ hy))
    obtain ⟨δ, hδ, hunif⟩ :=
      (isCompact_closedBall z₀ ρc).exists_forall_dist_image_lt_of_continuousAt hcball
        (half_pos hε')
    have hrpos : 0 < r - dist x₀ z₀ := by
      rw [mem_ball] at hx₀
      linarith
    refine ⟨min (δ / (L + 1)) (r - dist x₀ z₀), lt_min (by positivity) hrpos,
      fun {x} hx => ?_⟩
    have hxc : x ∈ closedBall z₀ r := by
      rw [mem_closedBall]
      have h1 : dist x x₀ < r - dist x₀ z₀ := hx.trans_le (min_le_right _ _)
      calc dist x z₀ ≤ dist x x₀ + dist x₀ z₀ := dist_triangle _ _ _
        _ ≤ r := by linarith
    have hx₀c : x₀ ∈ closedBall z₀ r := ball_subset_closedBall hx₀
    have hle : dist (A x) (A x₀) ≤ ε' / 2 := by
      rw [ContinuousMap.dist_le (by positivity)]
      intro t
      rw [hA_ball x hxc t, hA_ball x₀ hx₀c t]
      have hmem₀ : Z x₀ t.1 ∈ closedBall z₀ ρc :=
        ball_subset_closedBall ((hflow x₀ hx₀c).2.2 t.1 (hIccTsub t.2))
      have hZd : dist (Z x₀ t.1) (Z x t.1) < δ := by
        have hlip := (hLip t.1 (hIccTsub t.2)).dist_le_mul x₀ hx₀c x hxc
        have hdx : dist x₀ x < δ / (L + 1) := by
          rw [dist_comm]
          exact hx.trans_le (min_le_left _ _)
        have hL1 : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
        calc dist (Z x₀ t.1) (Z x t.1) ≤ (L : ℝ) * dist x₀ x := hlip
          _ ≤ ((L : ℝ) + 1) * dist x₀ x :=
              mul_le_mul_of_nonneg_right hL1 dist_nonneg
          _ < ((L : ℝ) + 1) * (δ / ((L : ℝ) + 1)) := by
              refine mul_lt_mul_of_pos_left hdx ?_
              positivity
          _ = δ := by field_simp
      rw [dist_comm]
      exact (hunif _ hmem₀ _ hZd).le
    exact hle.trans_lt (half_lt_self hε')
  -- continuity of the Volterra-operator family on the flow ball
  have hJPc : ∀ x₀ ∈ ball z₀ r, ContinuousAt JP x₀ := by
    intro x₀ hx₀
    rw [Metric.continuousAt_iff]
    intro ε' hε'
    obtain ⟨δ, hδ, hAδ⟩ := Metric.continuousAt_iff.mp (hAc x₀ hx₀)
      (ε' / (2 * (T + 1))) (by positivity)
    refine ⟨δ, hδ, fun {x} hx => ?_⟩
    have hd1 : dist (A x) (A x₀) < ε' / (2 * (T + 1)) := hAδ hx
    have hkey : JP x - JP x₀ = (intervalPrimitive hT.le).comp
        (postcompCurve (postcomp
          (ContinuousLinearMap.compL ℝ (E × E) (E × E) (E × E)) (A x - A x₀))) := by
      rw [map_sub (postcomp (ContinuousLinearMap.compL ℝ (E × E) (E × E) (E × E)))
        (A x) (A x₀), postcompCurve_sub, ContinuousLinearMap.comp_sub]
    have hnorm : dist (JP x) (JP x₀) ≤ T * dist (A x) (A x₀) := by
      rw [dist_eq_norm, hkey, dist_eq_norm]
      refine le_trans (norm_intervalPrimitive_comp_postcompCurve_le hT.le _) ?_
      exact mul_le_mul_of_nonneg_left (norm_postcomp_compL_le _) hT.le
    calc dist (JP x) (JP x₀) ≤ T * dist (A x) (A x₀) := hnorm
      _ ≤ T * (ε' / (2 * (T + 1))) :=
          mul_le_mul_of_nonneg_left hd1.le hT.le
      _ ≤ (T + 1) * (ε' / (2 * (T + 1))) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = ε' / 2 := by field_simp
      _ < ε' := half_lt_self hε'
  -- continuity of the variational-flow family on the flow ball
  have hτc : ∀ x₀ ∈ ball z₀ r, ContinuousAt τ x₀ := by
    intro x₀ hx₀
    have hu : ((1 : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
        C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) - JP x₀)
        = ↑(Units.oneSub (JP x₀) (hJPn x₀ (ball_subset_closedBall hx₀))) := rfl
    have h1 : ContinuousAt (fun x =>
        (1 : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
          C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) - JP x) x₀ :=
      continuousAt_const.sub (hJPc x₀ hx₀)
    have h2 : ContinuousAt (Ring.inverse :
        (C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
          C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) →
        (C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
          C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))))
        ((1 : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
          C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) - JP x₀) := by
      rw [hu]
      exact NormedRing.inverse_continuousAt _
    have hinv : ContinuousAt (fun x => Ring.inverse
        ((1 : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ]
          C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E))) - JP x)) x₀ :=
      Filter.Tendsto.comp h2 h1
    exact hinv.clm_apply continuousAt_const
  -- assemble the statement
  refine ⟨r, ε, T, Z, L, σ, τ, hT, hr, hε, hTε, ?_, hLip, ?_, hσ_ball, ?_, ?_⟩
  · -- the flow clauses, with chart confinement
    intro z hz
    obtain ⟨h0, hdZ, -⟩ := hflow z hz
    exact ⟨h0, hdZ, hmemΩ z hz⟩
  · -- transfer to the canonical maximal geodesic via the chart-flow bridge
    intro w hv
    have hzmem : ((extChartAt I p p, w) : E × E) ∈ closedBall z₀ r := by
      rw [mem_closedBall, hz₀def, Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      exact max_le hr.le hv
    obtain ⟨h0, hdZ, -⟩ := hflow _ hzmem
    have hdIoo : ∀ s ∈ Ioo (-ε) ε,
        HasDerivAt (Z ((extChartAt I p p, w) : E × E))
          (geodesicSprayCoord (I := I) g p
            (Z ((extChartAt I p p, w) : E × E) s).1
            (Z ((extChartAt I p p, w) : E × E) s).2) s := by
      intro s hs
      exact (hdZ s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
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
  · -- C¹ dependence, with the derivative computed by the variational flow
    intro x₀ hx₀
    have hx₀c : x₀ ∈ closedBall z₀ r := ball_subset_closedBall hx₀
    have hα₀Ω : ∀ t : Set.Icc (0 : ℝ) T,
        σ x₀ t ∈ (extChartAt I p).target ×ˢ (univ : Set E) := fun t => by
      rw [hσ_ball x₀ hx₀c t]
      exact hmemΩ x₀ hx₀c t.1 (hIccTsub t.2)
    have hc : ∀ t : Set.Icc (0 : ℝ) T, ContinuousAt (fderiv ℝ F) (σ x₀ t) := fun t =>
      hcfder.continuousAt (hopen.mem_nhds (hα₀Ω t))
    have hA₀ : ∀ t : Set.Icc (0 : ℝ) T, A x₀ t = fderiv ℝ F (σ x₀ t) := fun t => by
      rw [hA_ball x₀ hx₀c t, hσ_ball x₀ hx₀c t]
    have hTL : T * ‖A x₀‖ < 1 :=
      (mul_le_mul_of_nonneg_left (hAnorm x₀ hx₀c) hT.le).trans_lt
        (hTC.trans_lt one_half_lt_one)
    have hσres : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le F (x, σ x) = 0 := by
      filter_upwards [isOpen_ball.mem_nhds hx₀] with x hx
      exact hres1 x (ball_subset_closedBall hx)
    obtain ⟨D, hD, hstrict⟩ :=
      exists_hasStrictFDerivAt_of_picardResidual_curve hT hopen hd hα₀Ω hc hA₀ hTL
        rfl (hσc x₀ hx₀) hσres
    refine ⟨D, fun v => ?_, hstrict⟩
    exact flowDeriv_eq_applyCurve_opFlow hT hd hd2 (fun t => hα₀Ω t) hA₀ hTL hD
      (hresExt x₀ hx₀c) v
  · -- C² dependence: strict differentiability of the variational-flow family
    intro x₀ hx₀
    have hx₀c : x₀ ∈ closedBall z₀ r := ball_subset_closedBall hx₀
    have hα₀Ω : ∀ t : Set.Icc (0 : ℝ) T,
        σ x₀ t ∈ (extChartAt I p).target ×ˢ (univ : Set E) := fun t => by
      rw [hσ_ball x₀ hx₀c t]
      exact hmemΩ x₀ hx₀c t.1 (hIccTsub t.2)
    have hα₀ball : ∀ t : Set.Icc (0 : ℝ) T, σ x₀ t ∈ closedBall z₀ ρc := fun t => by
      rw [hσ_ball x₀ hx₀c t]
      exact ball_subset_closedBall ((hflow x₀ hx₀c).2.2 t.1 (hIccTsub t.2))
    have hc : ∀ t : Set.Icc (0 : ℝ) T, ContinuousAt (fderiv ℝ F) (σ x₀ t) := fun t =>
      hcfder.continuousAt (hopen.mem_nhds (hα₀Ω t))
    have hc2 : ∀ t : Set.Icc (0 : ℝ) T,
        ContinuousAt (fderiv ℝ (fderiv ℝ F)) (σ x₀ t) := fun t =>
      hcfder2.continuousAt (hopen.mem_nhds (hα₀Ω t))
    have hpair : ∀ᶠ x in 𝓝 x₀, picardResidual hT.le (variationalField F (fderiv ℝ F))
        ((x, (1 : (E × E) →L[ℝ] (E × E))), curveProd (σ x, τ x)) = 0 := by
      filter_upwards [isOpen_ball.mem_nhds hx₀] with x hx
      exact hresExt x (ball_subset_closedBall hx)
    have hA₂cont : Continuous fun t : Set.Icc (0:ℝ) T =>
        variationalFieldDeriv (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F)) (σ x₀ t, τ x₀ t) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hpt : ContinuousAt (fun s : Set.Icc (0:ℝ) T => (σ x₀ s, τ x₀ s)) t :=
        ((σ x₀).continuous.prodMk (τ x₀).continuous).continuousAt
      exact (continuousAt_variationalFieldDeriv (hc t) (hc2 t)).comp hpt
    set A₂ : C(Set.Icc (0:ℝ) T,
        ((E × E) × ((E × E) →L[ℝ] (E × E))) →L[ℝ]
          ((E × E) × ((E × E) →L[ℝ] (E × E)))) :=
      ⟨fun t => variationalFieldDeriv (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F))
        (σ x₀ t, τ x₀ t), hA₂cont⟩ with hA₂def
    have hA₂norm : ‖A₂‖ ≤ C + C₂ * 2 := by
      refine (ContinuousMap.norm_le _ (by positivity)).mpr fun t => ?_
      exact norm_variationalFieldDeriv_le (hboundC _ (hα₀ball t))
        (hboundC₂ _ (hα₀ball t))
        (((τ x₀).norm_coe_le_norm t).trans (hτnorm x₀ hx₀c)) hC₂0 (by norm_num)
    have hTL2 : T * ‖A₂‖ < 1 :=
      (mul_le_mul_of_nonneg_left hA₂norm hT.le).trans_lt hTA₂
    exact exists_hasStrictFDerivAt_opFlow_of_picardResidual_curve hT hopen hd hd2
      hα₀Ω hc2 rfl (hσc x₀ hx₀) (hτc x₀ hx₀) hpair (fun t => rfl) hTL2

end Geodesic
end PetersenLib
