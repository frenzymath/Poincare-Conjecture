import OpenGALib.Riemannian.Geodesic.FlowC2Dependence
import OpenGALib.Riemannian.Exponential.Ray

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

/-!
# The exponential map is C² on a ball

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 2.9 asserts that `exp_p` is a
*diffeomorphism* near `0 ∈ T_pM`. The `C¹` regularity was established in
`StrictDerivativeBall.lean` / `LocalDiffeo.lean`; this file upgrades it to `C²`:

* `exists_contDiffOn_two_extChartAt_expMap_ball` — there is `ρ > 0` such that the ball
  `B_ρ(0) ⊂ T_pM` lies in the exponential domain, its image under `exp_p` stays in the
  chart at `p`, and the chart reading `w ↦ φ_p(exp_p(w))` is **`C²`** on `B_ρ(0)`.

Route: by the fibre-scaling identification `exp_p(w) = π(Z(φ_p(p), w/T)(T))`, the chart
reading of `exp_p` is the composition of the affine map `ι : w ↦ (φ_p(p), w/T)` with the
time-`T` evaluation of the local geodesic flow family `σ`. The C²-flow theorem
(`Riemannian.Geodesic.exists_uniform_geodesic_flow_hasStrictFDerivAt_opFlow`) provides,
at every initial condition in the flow ball, both the strict derivative of `σ` —
*computed by the variational (operator) flow `τ`* — and the strict differentiability of
`τ` itself. Consequently the derivative of the chart reading at `w` is the **explicit
continuous-linear image `Φ (τ (ι w))`** of the variational flow, where `Φ` is a fixed
continuous linear functional (evaluate at time `T`, project to the base component,
precompose with `dι`); since `τ` is strictly differentiable and `Φ`, `ι` are linear, the
derivative map `w ↦ Φ (τ (ι w))` is `C¹` on the ball, which is exactly `C²` of the chart
reading.

This is the regularity input for the Gauss lemma (do Carmo Ch. 3, Lemma 3.5): the mixed
second derivatives of the chart reading of `exp_p` exist and are symmetric on the ball.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian
namespace Exponential

open Riemannian.Geodesic Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

set_option maxHeartbeats 1000000 in
/-- **Math.** **`exp_p` is `C²` on a ball around the origin** (do Carmo Ch. 3,
Prop. 2.9, second-order regularity; the analytic input for the Gauss lemma 3.5).
There is `ρ > 0` such that every `w` with `‖w‖ < ρ` lies in the exponential domain,
`exp_p(w)` stays in the chart at `p`, and the chart reading `w ↦ φ_p(exp_p(w))` is
`C²` on the ball `B_ρ(0)`.

The derivative of the chart reading at `w` is the continuous-linear image
`Φ (τ (ι w))` of the variational (operator) flow `τ` along the geodesic trajectory
with initial data `ι w = (φ_p(p), w/T)`; strict differentiability of the family `τ`
(the second-order flow-dependence theorem) makes this derivative map `C¹` on the
ball, i.e. the chart reading `C²`. -/
theorem exists_contDiffOn_two_extChartAt_expMap_ball
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      ContDiffOn ℝ 2
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (ball (0 : E) ρ) := by
  classical
  obtain ⟨r, ε, T, Z, L, σ, τ, hT, hr, hε, hTε, hflow, hLip, hmax, hσ_ball,
    hC1τ, hC2τ⟩ :=
    exists_uniform_geodesic_flow_hasStrictFDerivAt_opFlow (I := I) g p
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  have hTIoo : T ∈ Ioo (-ε) ε := ⟨lt_trans (neg_lt_zero.mpr hε) hT, hTε⟩
  set tT : Set.Icc (0 : ℝ) T := ⟨T, ⟨hT.le, le_rfl⟩⟩ with htTdef
  set ρ : ℝ := r * T with hρdef
  have hρpos : 0 < ρ := by positivity
  -- the identification: for `‖w‖ < ρ`, `exp_p(w)` is computed by the flow at time `T`
  -- from the rescaled initial velocity `w/T`
  have key : ∀ w : E, ‖w‖ < ρ →
      ((w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))
        = (σ ((extChartAt I p p, T⁻¹ • w) : E × E) tT).1) := by
    intro w hw
    set u : E := T⁻¹ • w with hudef
    have hu : ‖u‖ < r := by
      rw [hudef, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
      rw [inv_mul_lt_iff₀ hT]
      rw [hρdef] at hw
      linarith [hw, mul_comm r T]
    have hTu : (T : ℝ) • u = w := smul_inv_smul₀ hT.ne' w
    -- the flow trajectory with initial condition `(φ_p(p), u)`
    have hzu : ((extChartAt I p p, u) : E × E) ∈ closedBall z₀ r := by
      rw [mem_closedBall, hz₀def, Prod.dist_eq]
      simp only [dist_self, dist_zero_right]
      exact max_le hr.le hu.le
    obtain ⟨h0u, hdu, hmemu⟩ := hflow _ hzu
    have hdIoo : ∀ s ∈ Ioo (-ε) ε,
        HasDerivAt (Z ((extChartAt I p p, u) : E × E))
          (geodesicSprayCoord (I := I) g p
            (Z ((extChartAt I p p, u) : E × E) s).1
            (Z ((extChartAt I p p, u) : E × E) s).2) s := fun s hs =>
      (hdu s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hmemΨ : ∀ s ∈ Ioo (-ε) ε,
        Z ((extChartAt I p p, u) : E × E) s ∈
          (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
      intro s hs
      rw [extChartAt_tangent_target (I := I) p]
      exact hmemu s (Ioo_subset_Icc_self hs)
    obtain ⟨hwit, hsrc, hchart⟩ :=
      isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord (I := I) g p
        (u : TangentSpace I p) h0u hdIoo hmemΨ
    -- fibre-scale the witness from `(p, u)` to `(p, T • u) = (p, w)`
    have hTu' : (T • (u : TangentSpace I p)) = (w : TangentSpace I p) := by
      show (T • u : E) = w
      exact hTu
    have hwitW : IsGeodesicOnWithInitial (I := I) g
        (fun t => (((extChartAt I.tangent
          (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (Z ((extChartAt I p p, u) : E × E) (T * t))).proj))
        {t : ℝ | T * t ∈ Ioo (-ε) ε} p (w : TangentSpace I p) := by
      obtain ⟨fW, hproj, hf0, hint⟩ := hwit.fiberScale T
      refine ⟨fW, hproj, ?_, hint⟩
      rw [hf0]
      exact congrArg
        (fun v : TangentSpace I p => (⟨p, v⟩ : TangentBundle I M)) hTu'
    have hJ'o : IsOpen {t : ℝ | T * t ∈ Ioo (-ε) ε} :=
      isOpen_Ioo.preimage (continuous_const.mul continuous_id)
    have hJ'c : IsPreconnected {t : ℝ | T * t ∈ Ioo (-ε) ε} := by
      have hJ'eq : {t : ℝ | T * t ∈ Ioo (-ε) ε} = Ioo (-(ε / T)) (ε / T) := by
        ext t
        simp only [mem_setOf_eq, mem_Ioo]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_⟩
          · rw [← neg_div, div_lt_iff₀ hT]
            nlinarith
          · rw [lt_div_iff₀ hT]
            nlinarith
        · rintro ⟨h1, h2⟩
          rw [← neg_div, div_lt_iff₀ hT] at h1
          rw [lt_div_iff₀ hT] at h2
          exact ⟨by nlinarith, by nlinarith⟩
      rw [hJ'eq]; exact isPreconnected_Ioo
    have h0J' : (0 : ℝ) ∈ {t : ℝ | T * t ∈ Ioo (-ε) ε} := by
      simp only [mem_setOf_eq, mul_zero]
      exact ⟨neg_lt_zero.mpr hε, hε⟩
    have h1J' : (1 : ℝ) ∈ {t : ℝ | T * t ∈ Ioo (-ε) ε} := by
      simp only [mem_setOf_eq, mul_one]
      exact hTIoo
    have hsrcW : ∀ t ∈ {t : ℝ | T * t ∈ Ioo (-ε) ε},
        (((extChartAt I.tangent
          (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (Z ((extChartAt I p p, u) : E × E) (T * t))).proj) ∈
          (chartAt H p).source := fun t ht => hsrc (T * t) ht
    -- the canonical maximal geodesic is computed by the scaled witness
    have hval := maximalGeodesic_eq_witness_of_mem_chart (I := I) hwitW
      hJ'o hJ'c h0J' hsrcW h1J'
    have hdom : (w : TangentSpace I p) ∈ expDomain (I := I) g p := by
      show (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p (w : TangentSpace I p)
      exact subset_maximalGeodesicInterval_of_witness (I := I) hwitW
        hJ'o hJ'c h0J' h1J'
    have hexp_eq : expMap (I := I) g p (w : TangentSpace I p)
        = (((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (Z ((extChartAt I p p, u) : E × E) (T * 1))).proj) := by
      show maximalGeodesic (I := I) g p (w : TangentSpace I p) 1 = _
      exact hval
    rw [mul_one] at hexp_eq
    refine ⟨hdom, ?_, ?_⟩
    · rw [hexp_eq]
      exact hsrc T hTIoo
    · rw [hexp_eq, hchart T hTIoo]
      have hσval : σ ((extChartAt I p p, u) : E × E) tT
          = Z ((extChartAt I p p, u) : E × E) T :=
        hσ_ball _ hzu tT
      rw [hσval]
  -- the affine reparametrization `w ↦ (φ_p(p), w/T)` and its derivative
  set ι : E → E × E := fun w => (extChartAt I p p, T⁻¹ • w) with hιdef
  set Dι : E →L[ℝ] E × E :=
    (0 : E →L[ℝ] E).prod (T⁻¹ • ContinuousLinearMap.id ℝ E) with hDιdef
  have hι : ∀ w₀ : E, HasStrictFDerivAt ι Dι w₀ := fun w₀ =>
    (hasStrictFDerivAt_const _ _).prodMk
      (T⁻¹ • ContinuousLinearMap.id ℝ E).hasStrictFDerivAt
  have hxmem : ∀ w₀ : E, ‖w₀‖ < ρ → ι w₀ ∈ ball z₀ r := by
    intro w₀ hw₀
    rw [hιdef, mem_ball, hz₀def, Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    have hnorm : ‖T⁻¹ • w₀‖ < r := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hT.le, inv_mul_lt_iff₀ hT]
      rw [hρdef] at hw₀
      linarith [hw₀, mul_comm r T]
    exact max_lt hr hnorm
  -- the fixed evaluation functional: evaluate the operator flow at time `T`, read the
  -- base component, precompose with the affine derivative
  set Φ : C(Set.Icc (0:ℝ) T, (E × E) →L[ℝ] (E × E)) →L[ℝ] (E →L[ℝ] E) :=
    ((((ContinuousLinearMap.compL ℝ E (E × E) E).flip Dι).comp
      (ContinuousLinearMap.compL ℝ (E × E) (E × E) E
        (ContinuousLinearMap.fst ℝ E E))).comp
      (ContinuousMap.evalCLM ℝ tT)) with hΦdef
  -- the chart reading of `exp_p` is strictly differentiable at every point of the
  -- ball, with derivative the `Φ`-image of the variational flow
  have hstricte : ∀ w₀ : E, ‖w₀‖ < ρ →
      HasStrictFDerivAt
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (Φ (τ (ι w₀))) w₀ := by
    intro w₀ hw₀
    obtain ⟨D, hDτ, hstrict⟩ := hC1τ (ι w₀) (hxmem w₀ hw₀)
    have heval : HasStrictFDerivAt (fun y => σ y tT)
        ((ContinuousMap.evalCLM ℝ tT).comp D) (ι w₀) :=
      (ContinuousMap.evalCLM ℝ tT).hasStrictFDerivAt.comp (ι w₀) hstrict
    have hfstσ : HasStrictFDerivAt (fun y => (σ y tT).1)
        ((ContinuousLinearMap.fst ℝ E E).comp
          ((ContinuousMap.evalCLM ℝ tT).comp D)) (ι w₀) :=
      (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.comp (ι w₀) heval
    have hcomp : HasStrictFDerivAt (fun w => (σ (ι w) tT).1)
        (((ContinuousLinearMap.fst ℝ E E).comp
          ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι) w₀ :=
      hfstσ.comp w₀ (hι w₀)
    -- the derivative is the `Φ`-image of the variational flow
    have hDid : ((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι = Φ (τ (ι w₀)) := by
      refine ContinuousLinearMap.ext fun v => ?_
      show ((D (Dι v)) tT).1 = _
      rw [hDτ (Dι v)]
      rfl
    rw [hDid] at hcomp
    -- transfer along the identification, on the open ball `‖w‖ < ρ`
    have hev : (fun w : E => extChartAt I p
        (expMap (I := I) g p (w : TangentSpace I p)))
        =ᶠ[𝓝 w₀] fun w => (σ (ι w) tT).1 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw₀)] with w hw
      exact (key w (mem_ball_zero_iff.mp hw)).2.2
    exact hcomp.congr_of_eventuallyEq hev.symm
  -- the derivative family `w ↦ Φ (τ (ι w))` is strictly differentiable on the ball
  have hstrictd : ∀ w₀ ∈ ball (0 : E) ρ,
      HasStrictFDerivAt (fun w : E => Φ (τ (ι w)))
        (fderiv ℝ (fun w : E => Φ (τ (ι w))) w₀) w₀ := by
    intro w₀ hw₀
    obtain ⟨Dτ, hDτs⟩ := hC2τ (ι w₀) (hxmem w₀ (mem_ball_zero_iff.mp hw₀))
    have h : HasStrictFDerivAt (fun w : E => Φ (τ (ι w)))
        ((Φ.comp Dτ).comp Dι) w₀ :=
      (Φ.hasStrictFDerivAt.comp (ι w₀) hDτs).comp w₀ (hι w₀)
    rw [h.hasFDerivAt.fderiv]
    exact h
  -- assemble: `C²` on the open ball via `C¹` of the derivative map
  refine ⟨ρ, hρpos, fun w hw => (key w hw).1, fun w hw => (key w hw).2.1, ?_⟩
  have h2eq : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2eq, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
  refine ⟨fun w hw => ((hstricte w
    (mem_ball_zero_iff.mp hw)).differentiableAt).differentiableWithinAt,
    fun h => by simp at h, ?_⟩
  have hfeq : ∀ w ∈ ball (0 : E) ρ,
      fderiv ℝ (fun w : E => extChartAt I p
        (expMap (I := I) g p (w : TangentSpace I p))) w = Φ (τ (ι w)) := fun w hw =>
    (hstricte w (mem_ball_zero_iff.mp hw)).hasFDerivAt.fderiv
  exact (contDiffOn_one_of_forall_hasStrictFDerivAt isOpen_ball hstrictd).congr hfeq

end Exponential
end Riemannian
