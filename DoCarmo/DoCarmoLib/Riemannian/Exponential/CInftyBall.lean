import DoCarmoLib.Riemannian.Geodesic.FlowCInftyDependence
import DoCarmoLib.Riemannian.Exponential.Ray

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

/-!
# The exponential map is `C^∞` on a ball

`C2Ball.lean` proved the chart reading of `exp_p` is `C²` on a ball around `0 ∈ T_pM`; this file
upgrades that to `C^∞`, using the `C^∞` dependence of the local geodesic flow on its initial
condition (`Riemannian.Geodesic.exists_uniform_geodesic_flow_contDiffAt`).

* `exists_contDiffOn_infty_extChartAt_expMap_ball` — there is `ρ > 0` such that the ball
  `B_ρ(0) ⊂ T_pM` lies in the exponential domain, its image under `exp_p` stays in the chart at `p`,
  and the chart reading `w ↦ φ_p(exp_p(w))` is **`C^∞`** on `B_ρ(0)`.

Route (unchanged from the `C²` version, except the regularity of the flow): by the fibre-scaling
identification `exp_p(w) = π(Z(φ_p(p), w/T)(T))`, the chart reading is the composition of the affine
map `ι : w ↦ (φ_p(p), w/T)`, the `C^∞` flow family `σ`, the evaluation at time `T`, and the base
projection — a composition of `C^∞` maps, hence `C^∞`.

This is the regularity that the do-Carmo–faithful surface route to `cor:dc-ch5-2-5`
(`J = ∂f/∂s` for `f(t,s) = exp_p(t·v(s))`) requires — it differentiates `exp_p` to third order —
and the local-ball input to the global smoothness of `exp_p` (do Carmo Ch. 7, Hadamard).
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
/-- **Math.** **`exp_p` is `C^∞` on a ball around the origin** (do Carmo Ch. 3, Prop. 2.9, upgraded
to all orders). There is `ρ > 0` such that every `w` with `‖w‖ < ρ` lies in the exponential domain,
`exp_p(w)` stays in the chart at `p`, and the chart reading `w ↦ φ_p(exp_p(w))` is `C^∞` on
`B_ρ(0)`. The chart reading equals `w ↦ (σ(φ_p(p), w/T)(T))₁`, a composition of the affine
reparametrization, the `C^∞` flow family `σ`, the time-`T` evaluation, and the base projection. -/
theorem exists_contDiffOn_infty_extChartAt_expMap_ball
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      ContDiffOn ℝ ∞
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (ball (0 : E) ρ) := by
  classical
  obtain ⟨r, ε, T, Z, L, σ, hT, hr, hε, hTε, hflow, hLip, hmax, hσ_ball, hcd⟩ :=
    exists_uniform_geodesic_flow_contDiffAt (I := I) g p
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
  -- the affine reparametrization `ι : w ↦ (φ_p(p), w/T)` is `C^∞`
  set ι : E → E × E := fun w => (extChartAt I p p, T⁻¹ • w) with hιdef
  set Dι : E →L[ℝ] E × E :=
    (0 : E →L[ℝ] E).prod (T⁻¹ • ContinuousLinearMap.id ℝ E) with hDιdef
  have hιcd : ContDiff ℝ ∞ ι := by
    have hιeq : ι = fun w => z₀ + Dι w := by
      funext w
      simp [hιdef, hDιdef, hz₀def]
    rw [hιeq]
    exact contDiff_const.add Dι.contDiff
  have hxmem : ∀ w₀ : E, ‖w₀‖ < ρ → ι w₀ ∈ ball z₀ r := by
    intro w₀ hw₀
    rw [hιdef, mem_ball, hz₀def, Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    have hnorm : ‖T⁻¹ • w₀‖ < r := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hT.le, inv_mul_lt_iff₀ hT]
      rw [hρdef] at hw₀
      linarith [hw₀, mul_comm r T]
    exact max_lt hr hnorm
  -- the base-projection-after-time-`T`-evaluation functional
  set Φ' : C(Set.Icc (0:ℝ) T, E × E) →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E E).comp (ContinuousMap.evalCLM ℝ tT) with hΦ'def
  -- the chart reading `w ↦ (σ(ι w)(T))₁` is `C^∞` at every point of the ball
  have hcompose : ∀ w₀ : E, ‖w₀‖ < ρ →
      ContDiffAt ℝ ∞ (fun w : E => (σ (ι w) tT).1) w₀ := by
    intro w₀ hw₀
    have hσι : ContDiffAt ℝ ∞ (fun w : E => σ (ι w)) w₀ :=
      (hcd (ι w₀) (hxmem w₀ hw₀)).comp w₀ hιcd.contDiffAt
    exact (Φ'.contDiff.contDiffAt).comp w₀ hσι
  -- assemble `C^∞` on the open ball via the identification
  refine ⟨ρ, hρpos, fun w hw => (key w hw).1, fun w hw => (key w hw).2.1, ?_⟩
  intro w hw
  have hw' : ‖w‖ < ρ := mem_ball_zero_iff.mp hw
  have hcda : ContDiffAt ℝ ∞
      (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) w := by
    refine (hcompose w hw').congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw')] with x hx
    exact (key x (mem_ball_zero_iff.mp hx)).2.2
  exact hcda.contDiffWithinAt

/-- **Math.** **`exp_p` is `C^∞` as a manifold map on a ball around the origin** (the manifold-level
form of `exists_contDiffOn_infty_extChartAt_expMap_ball`). There is `ρ > 0` such that `B_ρ(0) ⊂ T_pM`
lies in the exponential domain and `w ↦ exp_p(w)` is `ContMDiff 𝓘(ℝ,E) I ∞` on `B_ρ(0)`.

Written through the chart at `p`, `exp_p = (extChartAt I p).symm ∘ (φ_p ∘ exp_p)`: the chart reading
`φ_p ∘ exp_p` is `C^∞` on the ball (`exists_contDiffOn_infty_extChartAt_expMap_ball`), hence a
`C^∞` manifold map into `E` (`contMDiffOn_iff_contDiffOn`), and the chart inverse
`(extChartAt I p).symm` is `C^∞` (`contMDiffOn_extChartAt_symm`); the composition equals `exp_p`
on the ball since `exp_p(w)` stays in the chart source. This is the base-case local smoothness of
`exp_p` as a map of manifolds — the manifold regularity that the global smoothness of `exp_p`
(do Carmo Ch. 7, Hadamard) is chained from, and that the do-Carmo surface route to the exp–Jacobi
bridge (`cor:dc-ch5-2-5`) requires. -/
theorem contMDiffOn_infty_expMap_ball
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      ContMDiffOn 𝓘(ℝ, E) I ∞
        (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) (ball (0 : E) ρ) := by
  obtain ⟨ρ, hρ, hdom, hsrc, hcd⟩ :=
    exists_contDiffOn_infty_extChartAt_expMap_ball (I := I) g p
  set f : E → E :=
    fun w => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  refine ⟨ρ, hρ, hdom, ?_⟩
  have hfM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f (ball (0 : E) ρ) :=
    contMDiffOn_iff_contDiffOn.mpr hcd
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I p).symm (extChartAt I p).target :=
    contMDiffOn_extChartAt_symm p
  have hmaps : MapsTo f (ball (0 : E) ρ) (extChartAt I p).target := by
    intro w hw
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]; exact hsrc w (mem_ball_zero_iff.mp hw))
  refine (hsymm.comp hfM hmaps).congr ?_
  intro w hw
  show expMap (I := I) g p (w : TangentSpace I p) = (extChartAt I p).symm (f w)
  rw [hfdef]
  exact ((extChartAt I p).left_inv (by
    rw [extChartAt_source]; exact hsrc w (mem_ball_zero_iff.mp hw))).symm

end Exponential
end Riemannian
