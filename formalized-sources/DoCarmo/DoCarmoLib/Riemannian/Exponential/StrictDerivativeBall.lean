import DoCarmoLib.Riemannian.Geodesic.FlowC1Dependence
import DoCarmoLib.Riemannian.Exponential.Ray


/-!
# Strict differentiability of the exponential map on a ball

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 2.9 asserts that `exp_p` is a
*diffeomorphism* near `0 ∈ T_pM`; the regularity input beyond `d(exp_p)_0 = id`
(`Riemannian.Exponential.exists_hasStrictFDerivAt_extChartAt_expMap`, at the origin
only) is differentiability of `exp_p` *away from* the origin — C¹ dependence of the
geodesic flow on its initial condition at non-equilibrium base trajectories. This
file provides that:

* `exists_hasStrictFDerivAt_extChartAt_expMap_ball` — there is `ρ > 0` such that the
  ball `B_ρ(0) ⊂ T_pM` lies in the exponential domain, its image under `exp_p` stays
  in the chart at `p`, and at **every** `v₀` with `‖v₀‖ < ρ` — zero or not — the chart
  reading `w ↦ φ_p(exp_p(w))` has a strict Fréchet derivative at `v₀`. In particular
  `exp_p` is (strictly) differentiable at every point of a neighbourhood of the
  origin, not only at the origin itself.

Route: the C¹-dependence of the local geodesic flow at every initial condition in
the flow ball (`Riemannian.Geodesic.exists_uniform_geodesic_flow_hasStrictFDerivAt`,
via the non-equilibrium Picard-residual theorem), composed with the fibre-scaling
identification `exp_p(w) = γ(1, p, w) = γ(T, p, w/T)`: the witness-level homogeneity
trades the fixed evaluation time `1` for the short Picard time `T`, and the chart
reading of the maximal geodesic is computed by the flow. The derivative at `v₀ ≠ 0`
is *not* the identity — it is the abstract solution of the variational (linearized)
integral equation along the base trajectory, delivered by the Neumann series; its
identification (and invertibility, toward the full local-diffeomorphism statement
and the Gauss lemma) is the next layer.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian
namespace Exponential

open Riemannian.Geodesic Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **`exp_p` is strictly differentiable at every point of a ball around the
origin** (do Carmo Ch. 3, Prop. 2.9, C¹-regularity content away from the origin).
There is `ρ > 0` such that every `w` with `‖w‖ < ρ` lies in the exponential domain,
`exp_p(w)` stays in the chart at `p`, and at every `v₀` with `‖v₀‖ < ρ` the chart
reading `w ↦ φ_p(exp_p(w))` has a strict Fréchet derivative.

The derivative is obtained by evaluating, at the Picard time `T`, the strict
derivative of the local geodesic flow in its initial condition at the
(non-equilibrium) base point `(φ_p(p), v₀/T)`, then composing with the linear map
`w ↦ (0, w/T)`; the identification `φ_p(exp_p(w)) = (Z(φ_p(p), w/T)(T))_1` is the
fibre-scaling homogeneity `γ(1, p, w) = γ(T, p, w/T)` realized on the flow witness. -/
theorem exists_hasStrictFDerivAt_extChartAt_expMap_ball
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ v₀ : E, ‖v₀‖ < ρ →
        ∃ D' : E →L[ℝ] E,
          HasStrictFDerivAt
            (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
            D' v₀) := by
  classical
  obtain ⟨r, ε, T, Z, L, σ, hT, hr, hε, hTε, hflow, hLip, hmax, hσ_ball, hC1⟩ :=
    exists_uniform_geodesic_flow_hasStrictFDerivAt (I := I) g p
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
  refine ⟨ρ, hρpos, fun w hw => (key w hw).1, fun w hw => (key w hw).2.1, ?_⟩
  -- strict differentiability at every `v₀` in the ball
  intro v₀ hv₀
  -- the affine reparametrization `w ↦ (φ_p(p), w/T)` and its base point
  set ι : E → E × E := fun w => (extChartAt I p p, T⁻¹ • w) with hιdef
  set Dι : E →L[ℝ] E × E :=
    (0 : E →L[ℝ] E).prod (T⁻¹ • ContinuousLinearMap.id ℝ E) with hDιdef
  have hι : HasStrictFDerivAt ι Dι v₀ :=
    (hasStrictFDerivAt_const _ _).prodMk
      (T⁻¹ • ContinuousLinearMap.id ℝ E).hasStrictFDerivAt
  have hx₀ : ι v₀ ∈ ball z₀ r := by
    rw [hιdef, mem_ball, hz₀def, Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    have hnorm : ‖T⁻¹ • v₀‖ < r := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hT.le, inv_mul_lt_iff₀ hT]
      rw [hρdef] at hv₀
      linarith [hv₀, mul_comm r T]
    exact max_lt hr hnorm
  -- strict derivative of the flow family at the (non-equilibrium) base point
  obtain ⟨D, A₀, hA₀, hD, hstrict⟩ := hC1 (ι v₀) hx₀
  have heval : HasStrictFDerivAt (fun y => σ y tT)
      ((ContinuousMap.evalCLM ℝ tT).comp D) (ι v₀) :=
    (ContinuousMap.evalCLM ℝ tT).hasStrictFDerivAt.comp (ι v₀) hstrict
  have hfstσ : HasStrictFDerivAt (fun y => (σ y tT).1)
      ((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)) (ι v₀) :=
    (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.comp (ι v₀) heval
  have hcomp : HasStrictFDerivAt (fun w => (σ (ι w) tT).1)
      (((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι) v₀ :=
    hfstσ.comp v₀ hι
  -- transfer along the identification, on the open ball `‖w‖ < ρ`
  have hev : (fun w : E => extChartAt I p
      (expMap (I := I) g p (w : TangentSpace I p)))
      =ᶠ[𝓝 v₀] fun w => (σ (ι w) tT).1 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hv₀)] with w hw
    exact (key w (mem_ball_zero_iff.mp hw)).2.2
  exact ⟨_, hcomp.congr_of_eventuallyEq hev.symm⟩

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **`exp_p` is `C¹` on a ball around the origin** (do Carmo Ch. 3, Prop. 2.9,
`C¹`-regularity clause). There is `ρ > 0` such that the ball `B_ρ(0) ⊂ T_pM` lies in the
exponential domain, its image under `exp_p` stays in the chart at `p`, and the chart
reading `w ↦ φ_p(exp_p(w))` is `C¹` on `B_ρ(0)`.

Pointwise strict differentiability (`exists_hasStrictFDerivAt_extChartAt_expMap_ball`)
self-improves on the open ball: the derivative map is continuous
(`Riemannian.FlowDependence.continuousOn_of_forall_hasStrictFDerivAt`), which is the `C¹`
characterization on open sets. -/
theorem exists_contDiffOn_extChartAt_expMap_ball
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      ContDiffOn ℝ 1
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (ball (0 : E) ρ) := by
  obtain ⟨ρ, hρ, hdom, hsrc, hstrict⟩ :=
    exists_hasStrictFDerivAt_extChartAt_expMap_ball (I := I) g p
  refine ⟨ρ, hρ, hdom, hsrc, ?_⟩
  have hstrict' : ∀ v₀ ∈ ball (0 : E) ρ,
      HasStrictFDerivAt
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (fderiv ℝ
          (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) v₀)
        v₀ := by
    intro v₀ hv₀
    obtain ⟨D', hD'⟩ := hstrict v₀ (mem_ball_zero_iff.mp hv₀)
    rwa [hD'.hasFDerivAt.fderiv]
  exact contDiffOn_one_of_forall_hasStrictFDerivAt isOpen_ball hstrict'

end Exponential
end Riemannian
