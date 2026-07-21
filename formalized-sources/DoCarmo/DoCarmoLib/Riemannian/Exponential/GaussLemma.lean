import DoCarmoLib.Riemannian.Exponential.RayODE
import DoCarmoLib.Riemannian.Geodesic.SymmetryLemma
import DoCarmoLib.Riemannian.Geodesic.CovariantDerivative
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge

set_option maxSynthPendingDepth 3

/-!
# The Gauss lemma (do Carmo Ch. 3, Lemma 3.5)

`⟨(d exp_p)_v(v), (d exp_p)_v(w)⟩ = ⟨v, w⟩`: the exponential map is a *radial
isometry*. Everything is read in the fixed chart at `p`: the metric is the chart
Gram inner product `chartMetricInner`, the derivative of `exp_p` is the Fréchet
derivative of the chart reading `f : w ↦ φ_p(exp_p(w))`, and the statement holds
for `v` in the ball supplied by `exists_expMap_ray_ode_ball`.

The proof is do Carmo's: for the parametrized surface
`c(t, s) = f(t·(v + s·w))`,

* each `t`-curve is a geodesic (`exists_expMap_ray_ode_ball`), so by metric
  compatibility (`hasDerivAt_chartMetricInner_along`) the squared speed
  `ψ(t,s) = ⟨∂_t c, ∂_t c⟩` is constant in `t`, and equals `⟨v+sw, v+sw⟩` at `t=0`
  (`(df)_0 = id`);
* by the symmetry lemma (`covariant_sndFDeriv_symm_of_eventually`, do Carmo 3.4)
  `D/∂t ∂_s c = D/∂s ∂_t c`, so with compatibility in the `s`-direction
  `∂_t⟨∂_s c, ∂_t c⟩ = ⟨D/∂s ∂_t c, ∂_t c⟩ = ½ ∂_s ψ = ⟨v, w⟩` for every `t`;
* integrating from `∂_s c(0, ·) = 0` gives `⟨∂_s c, ∂_t c⟩(1,0) = ⟨v, w⟩`, which is
  the Gauss identity.

The surface computation is isolated in `gauss_surface_computation`, a statement
about an arbitrary `C²` map `f` whose rays satisfy the chart geodesic ODE; the
main theorem `exists_gauss_lemma_ball` instantiates it with the chart reading of
`exp_p`.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

section ChartMetricInnerAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart Gram inner product vanishes when its first vector slot is
zero. -/
theorem chartMetricInner_zero_left (g : RiemannianMetric I M) (α : M) (y b : E) :
    chartMetricInner (I := I) g α y 0 b = 0 := by
  simp [chartMetricInner_def]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart Gram inner product vanishes when its second vector slot is
zero. -/
theorem chartMetricInner_zero_right (g : RiemannianMetric I M) (α : M) (y a : E) :
    chartMetricInner (I := I) g α y a 0 = 0 := by
  simp [chartMetricInner_def]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart Gram inner product is homogeneous in its first vector
slot. -/
theorem chartMetricInner_smul_left (g : RiemannianMetric I M) (α : M) (y : E)
    (s : ℝ) (a b : E) :
    chartMetricInner (I := I) g α y (s • a) b
      = s * chartMetricInner (I := I) g α y a b := by
  simp only [chartMetricInner_def, Geodesic.chartCoord_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart Gram inner product is homogeneous in its second vector
slot. -/
theorem chartMetricInner_smul_right (g : RiemannianMetric I M) (α : M) (y : E)
    (s : ℝ) (a b : E) :
    chartMetricInner (I := I) g α y a (s • b)
      = s * chartMetricInner (I := I) g α y a b := by
  simp only [chartMetricInner_def, Geodesic.chartCoord_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart Gram inner product is symmetric (the Gram matrix is,
`chartGramOnE_symm`). -/
theorem chartMetricInner_symm (g : RiemannianMetric I M) (α : M) (y a b : E) :
    chartMetricInner (I := I) g α y a b = chartMetricInner (I := I) g α y b a := by
  rw [chartMetricInner_def, chartMetricInner_def, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [chartGramOnE_symm (I := I) g α]
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The derivative at `s = 0` of the quadratic form
`s ↦ ⟨a + s·d, a + s·d⟩_y` is `⟨a, d⟩_y + ⟨d, a⟩_y`. This computes
`∂_s |v + s w|²` in the Gauss-lemma argument. -/
theorem hasDerivAt_chartMetricInner_quadratic (g : RiemannianMetric I M) (α : M)
    (y a d : E) :
    HasDerivAt (fun s : ℝ => chartMetricInner (I := I) g α y (a + s • d) (a + s • d))
      (chartMetricInner (I := I) g α y a d + chartMetricInner (I := I) g α y d a)
      0 := by
  have hexp : (fun s : ℝ => chartMetricInner (I := I) g α y (a + s • d) (a + s • d))
      = fun s : ℝ => chartMetricInner (I := I) g α y a a
          + s * (chartMetricInner (I := I) g α y a d
            + chartMetricInner (I := I) g α y d a)
          + s * s * chartMetricInner (I := I) g α y d d := by
    funext s
    simp only [chartMetricInner_add_left, chartMetricInner_add_right,
      chartMetricInner_smul_left, chartMetricInner_smul_right]
    ring
  rw [hexp]
  have h1 : HasDerivAt (fun s : ℝ => chartMetricInner (I := I) g α y a a
      + s * (chartMetricInner (I := I) g α y a d
        + chartMetricInner (I := I) g α y d a))
      (chartMetricInner (I := I) g α y a d
        + chartMetricInner (I := I) g α y d a) 0 :=
    (hasDerivAt_mul_const _).const_add _
  have h2 : HasDerivAt
      (fun s : ℝ => s * s * chartMetricInner (I := I) g α y d d) 0 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const
      (chartMetricInner (I := I) g α y d d)
    simpa using h
  simpa using h1.add h2

end ChartMetricInnerAlgebra

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]

omit [T2Space (TangentBundle I M)] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **The Gauss-lemma surface computation** (do Carmo Ch. 3, Lemma 3.5,
the analytic core). Let `f : E → E` be a `C²` map on `B_ρ(0)` — think of the
chart reading `w ↦ φ_p(exp_p w)` — whose values lie in the chart target, with
`f(0) = φ_p(p)`, `(df)_0 = id`, and whose ray velocities satisfy the chart
geodesic ODE `V' = −Γ_p(V,V)(f)` (the package of `exists_expMap_ray_ode_ball`).
Then for `‖v‖ < ρ` and any `w`,

`⟨(df)_v(v), (df)_v(w)⟩_{f(v)} = ⟨v, w⟩_{φ_p(p)}`

in the chart Gram inner product: `f` is a radial isometry. The proof is
do Carmo's parametrized-surface argument for `c(t,s) = f(t·(v+s·w))`, combining
metric compatibility (`hasDerivAt_chartMetricInner_along`), the symmetry lemma
(`covariant_sndFDeriv_symm_of_eventually`), constant geodesic speed, and
`∂_s c(0, ·) = 0`. -/
theorem gauss_surface_computation (g : RiemannianMetric I M) (p : M)
    (f : E → E) {ρ b : ℝ} (hb : 1 < b)
    (hC2 : ContDiffOn ℝ 2 f (ball (0 : E) ρ))
    (hf0 : f 0 = extChartAt I p p)
    (hfd0 : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E)
    (htarget : ∀ w' : E, ‖w'‖ < ρ → f w' ∈ (extChartAt I p).target)
    (hbase : ∀ w' : E, ‖w'‖ < ρ →
      (extChartAt I p).symm (f w') ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (hODE : ∀ (u : E) (t : ℝ), ‖u‖ < ρ → |t| < b → ‖t • u‖ < ρ →
      HasDerivAt (fun t' : ℝ => fderiv ℝ f (t' • u) u)
        (- Geodesic.chartChristoffelContraction (I := I) g p
            (fderiv ℝ f (t • u) u) (fderiv ℝ f (t • u) u) (f (t • u))) t)
    (v w : E) (hv : ‖v‖ < ρ) :
    chartMetricInner (I := I) g p (f v) (fderiv ℝ f v v) (fderiv ℝ f v w)
      = chartMetricInner (I := I) g p (extChartAt I p p) v w := by
  classical
  -- ## the parametrized surface in chart coordinates
  set A : ℝ × ℝ → E := fun q => q.1 • v + (q.1 * q.2) • w with hAdef
  have hAfact : ∀ q : ℝ × ℝ, A q = q.1 • (v + q.2 • w) := by
    intro q
    simp only [hAdef, smul_add, smul_smul]
  set DA : ℝ × ℝ → (ℝ × ℝ →L[ℝ] E) := fun q =>
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v
      + (q.1 • (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w
        + q.2 • (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight w) with hDAdef
  have hA : ∀ q : ℝ × ℝ, HasFDerivAt A (DA q) q := by
    intro q
    have h1 : HasFDerivAt (fun y : ℝ × ℝ => y.1 • v)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v) q :=
      hasFDerivAt_fst.smul_const v
    have h2 : HasFDerivAt (fun y : ℝ × ℝ => (y.1 * y.2) • w)
        ((q.1 • ContinuousLinearMap.snd ℝ ℝ ℝ
          + q.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight w) q :=
      (hasFDerivAt_fst.mul hasFDerivAt_snd).smul_const w
    have h2' : ((q.1 • ContinuousLinearMap.snd ℝ ℝ ℝ
          + q.2 • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight w)
        = q.1 • (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w
          + q.2 • (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight w := by
      refine ContinuousLinearMap.ext fun ξ => ?_
      simp [add_smul, smul_smul]
    rw [h2'] at h2
    exact (h1.add h2).congr_fderiv (by rw [hDAdef])
  have hDA_e₁ : ∀ q : ℝ × ℝ, DA q ((1 : ℝ), (0 : ℝ)) = v + q.2 • w := by
    intro q
    simp [hDAdef]
  have hDA_e₂ : ∀ q : ℝ × ℝ, DA q ((0 : ℝ), (1 : ℝ)) = q.1 • w := by
    intro q
    simp [hDAdef]
  -- the open parameter domain
  set Ω : Set (ℝ × ℝ) := {q : ℝ × ℝ |
    ‖q.1 • (v + q.2 • w)‖ < ρ ∧ ‖v + q.2 • w‖ < ρ ∧ |q.1| < b} with hΩdef
  have hΩo : IsOpen Ω := by
    rw [hΩdef, setOf_and, setOf_and]
    refine (isOpen_lt ?_ continuous_const).inter
      ((isOpen_lt ?_ continuous_const).inter (isOpen_lt ?_ continuous_const))
    · exact (continuous_fst.smul
        (continuous_const.add (continuous_snd.smul continuous_const))).norm
    · exact (continuous_const.add (continuous_snd.smul continuous_const)).norm
    · exact continuous_fst.abs
  have hΩt0 : ∀ t ∈ Icc (0 : ℝ) 1, ((t, (0 : ℝ)) : ℝ × ℝ) ∈ Ω := by
    intro t ht
    have habs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    refine ⟨?_, ?_, lt_of_le_of_lt habs hb⟩
    · show ‖t • (v + (0 : ℝ) • w)‖ < ρ
      rw [zero_smul, add_zero, norm_smul, Real.norm_eq_abs]
      calc |t| * ‖v‖ ≤ 1 * ‖v‖ :=
            mul_le_mul_of_nonneg_right habs (norm_nonneg v)
        _ = ‖v‖ := one_mul _
        _ < ρ := hv
    · show ‖v + (0 : ℝ) • w‖ < ρ
      rw [zero_smul, add_zero]
      exact hv
  have hAball : ∀ q ∈ Ω, A q ∈ ball (0 : E) ρ := by
    intro q hq
    rw [mem_ball_zero_iff, hAfact q]
    exact hq.1
  -- the surface, its partial velocities and its full derivative
  set c : ℝ × ℝ → E := fun q => f (A q) with hcdef
  set P : ℝ × ℝ → E := fun q => fderiv ℝ f (A q) (v + q.2 • w) with hPdef
  set Q : ℝ × ℝ → E := fun q => fderiv ℝ f (A q) (q.1 • w) with hQdef
  set Dc : ℝ × ℝ → (ℝ × ℝ →L[ℝ] E) :=
    fun q => (fderiv ℝ f (A q)).comp (DA q) with hDcdef
  have hf_diffAt : ∀ q ∈ Ω, DifferentiableAt ℝ f (A q) := by
    intro q hq
    exact (hC2.contDiffAt (isOpen_ball.mem_nhds (hAball q hq))).differentiableAt
      (by norm_num)
  have hc_hasF : ∀ q ∈ Ω, HasFDerivAt c (Dc q) q := by
    intro q hq
    have h := ((hf_diffAt q hq).hasFDerivAt).comp q (hA q)
    simpa [Function.comp_def, hcdef, hDcdef] using h
  have hP_eq : ∀ q : ℝ × ℝ, Dc q ((1 : ℝ), (0 : ℝ)) = P q := by
    intro q
    simp only [hDcdef, hPdef, ContinuousLinearMap.comp_apply]
    rw [hDA_e₁ q]
  have hQ_eq : ∀ q : ℝ × ℝ, Dc q ((0 : ℝ), (1 : ℝ)) = Q q := by
    intro q
    simp only [hDcdef, hQdef, ContinuousLinearMap.comp_apply]
    rw [hDA_e₂ q]
  -- regularity of the derivative family
  have hfC1 : ContDiffOn ℝ 1 (fderiv ℝ f) (ball (0 : E) ρ) :=
    hC2.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hfderiv_diffAt : ∀ q ∈ Ω,
      DifferentiableAt ℝ (fun y : ℝ × ℝ => fderiv ℝ f (A y)) q := by
    intro q hq
    have h1 : DifferentiableAt ℝ (fderiv ℝ f) (A q) :=
      (hfC1.contDiffAt (isOpen_ball.mem_nhds (hAball q hq))).differentiableAt
        (by norm_num)
    exact h1.comp q (hA q).differentiableAt
  have hDA_diff : ∀ q : ℝ × ℝ, DifferentiableAt ℝ DA q := by
    intro q
    rw [hDAdef]
    refine (differentiableAt_const _).add (DifferentiableAt.add ?_ ?_)
    · exact (hasFDerivAt_fst.smul_const
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w)).differentiableAt
    · exact (hasFDerivAt_snd.smul_const
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight w)).differentiableAt
  have hDc_diffAt : ∀ q ∈ Ω, DifferentiableAt ℝ Dc q := by
    intro q hq
    rw [hDcdef]
    exact (hfderiv_diffAt q hq).clm_comp (hDA_diff q)
  -- chart membership of the surface values
  have hGram : ∀ q ∈ Ω, ∀ i j,
      DifferentiableAt ℝ (chartGramOnE (I := I) g p i j) (c q) := by
    intro q hq i j
    have htgt : c q ∈ (extChartAt I p).target := by
      simp only [hcdef]
      exact htarget (A q) (mem_ball_zero_iff.mp (hAball q hq))
    exact ((chartGramOnE_contDiffOn (I := I) g p i j).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds htgt)).differentiableAt (by norm_num)
  have hBase : ∀ q ∈ Ω, (extChartAt I p).symm (c q) ∈
      (trivializationAt E (TangentSpace I) p).baseSet := by
    intro q hq
    simp only [hcdef]
    exact hbase (A q) (mem_ball_zero_iff.mp (hAball q hq))
  -- ## the `t`-curves are geodesics: velocity, geodesic ODE, zero covariant accel
  have huTs : ∀ (s t' : ℝ), ((t', s) : ℝ × ℝ) ∈ Ω →
      HasDerivAt (fun τ : ℝ => c ((τ, s) : ℝ × ℝ)) (P ((t', s) : ℝ × ℝ)) t' := by
    intro s t' hq
    have hcurve : HasDerivAt (fun τ : ℝ => ((τ, s) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) t' :=
      (hasDerivAt_id t').prodMk (hasDerivAt_const t' s)
    have h := (hc_hasF _ hq).comp_hasDerivAt t' hcurve
    rwa [hP_eq] at h
  have huSs : ∀ (t σ₀ : ℝ), ((t, σ₀) : ℝ × ℝ) ∈ Ω →
      HasDerivAt (fun σ : ℝ => c ((t, σ) : ℝ × ℝ)) (Q ((t, σ₀) : ℝ × ℝ)) σ₀ := by
    intro t σ₀ hq
    have hcurve : HasDerivAt (fun σ : ℝ => ((t, σ) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) σ₀ :=
      (hasDerivAt_const σ₀ t).prodMk (hasDerivAt_id σ₀)
    have h := (hc_hasF _ hq).comp_hasDerivAt σ₀ hcurve
    rwa [hQ_eq] at h
  have hVTs : ∀ (s t' : ℝ), ((t', s) : ℝ × ℝ) ∈ Ω →
      HasDerivAt (fun τ : ℝ => P ((τ, s) : ℝ × ℝ))
        (- Geodesic.chartChristoffelContraction (I := I) g p
            (P ((t', s) : ℝ × ℝ)) (P ((t', s) : ℝ × ℝ)) (c ((t', s) : ℝ × ℝ))) t' := by
    intro s t' hq
    obtain ⟨h1, h2, h3⟩ := hq
    have hODE' := hODE (v + s • w) t' h2 h3 h1
    have hfun : (fun τ : ℝ => P ((τ, s) : ℝ × ℝ))
        = fun τ : ℝ => fderiv ℝ f (τ • (v + s • w)) (v + s • w) := by
      funext τ
      simp only [hPdef]
      rw [hAfact]
    have hval1 : fderiv ℝ f (t' • (v + s • w)) (v + s • w) = P ((t', s) : ℝ × ℝ) := by
      simp only [hPdef]
      rw [hAfact]
    have hval2 : f (t' • (v + s • w)) = c ((t', s) : ℝ × ℝ) := by
      simp only [hcdef]
      rw [hAfact]
    rw [hval1, hval2] at hODE'
    rw [hfun]
    exact hODE'
  have hgeo : ∀ (s t' : ℝ), ((t', s) : ℝ × ℝ) ∈ Ω →
      covariantDerivCoord (I := I) g p (fun τ : ℝ => c ((τ, s) : ℝ × ℝ))
        (fun τ : ℝ => P ((τ, s) : ℝ × ℝ)) t' = 0 := by
    intro s t' hq
    rw [covariantDerivCoord_def, (hVTs s t' hq).deriv, (huTs s t' hq).deriv]
    exact neg_add_cancel _
  -- ## constant speed: `ψ(t, s) = ⟨∂_t c, ∂_t c⟩` is constant in `t`
  have hψt : ∀ (s t' : ℝ), ((t', s) : ℝ × ℝ) ∈ Ω →
      HasDerivAt (fun τ : ℝ => chartMetricInner (I := I) g p (c ((τ, s) : ℝ × ℝ))
        (P ((τ, s) : ℝ × ℝ)) (P ((τ, s) : ℝ × ℝ))) 0 t' := by
    intro s t' hq
    have h := hasDerivAt_chartMetricInner_along (I := I) g p
      (fun τ : ℝ => c ((τ, s) : ℝ × ℝ)) (fun τ : ℝ => P ((τ, s) : ℝ × ℝ))
      (fun τ : ℝ => P ((τ, s) : ℝ × ℝ))
      (huTs s t' hq).differentiableAt (hVTs s t' hq).differentiableAt
      (hVTs s t' hq).differentiableAt (fun i j => hGram _ hq i j) (hBase _ hq)
    rw [hgeo s t' hq] at h
    simpa [chartMetricInner_zero_left, chartMetricInner_zero_right] using h
  have hψconst : ∀ s : ℝ, ‖v + s • w‖ < ρ → ∀ t ∈ Icc (0 : ℝ) 1,
      chartMetricInner (I := I) g p (c ((t, s) : ℝ × ℝ))
          (P ((t, s) : ℝ × ℝ)) (P ((t, s) : ℝ × ℝ))
        = chartMetricInner (I := I) g p (c (((0 : ℝ), s) : ℝ × ℝ))
          (P (((0 : ℝ), s) : ℝ × ℝ)) (P (((0 : ℝ), s) : ℝ × ℝ)) := by
    intro s hs t ht
    have hmem : ∀ x ∈ Icc (0 : ℝ) 1, ((x, s) : ℝ × ℝ) ∈ Ω := by
      intro x hx
      have habs : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      refine ⟨?_, hs, lt_of_le_of_lt habs hb⟩
      show ‖x • (v + s • w)‖ < ρ
      rw [norm_smul, Real.norm_eq_abs]
      calc |x| * ‖v + s • w‖ ≤ 1 * ‖v + s • w‖ :=
            mul_le_mul_of_nonneg_right habs (norm_nonneg _)
        _ = ‖v + s • w‖ := one_mul _
        _ < ρ := hs
    have hcont : ContinuousOn (fun τ : ℝ => chartMetricInner (I := I) g p
        (c ((τ, s) : ℝ × ℝ)) (P ((τ, s) : ℝ × ℝ)) (P ((τ, s) : ℝ × ℝ)))
        (Icc (0 : ℝ) 1) := fun x hx =>
      ((hψt s x (hmem x hx)).continuousAt).continuousWithinAt
    have hderiv : ∀ x ∈ Ico (0 : ℝ) 1, HasDerivWithinAt
        (fun τ : ℝ => chartMetricInner (I := I) g p
          (c ((τ, s) : ℝ × ℝ)) (P ((τ, s) : ℝ × ℝ)) (P ((τ, s) : ℝ × ℝ)))
        0 (Ici x) x := fun x hx =>
      (hψt s x (hmem x (Ico_subset_Icc_self hx))).hasDerivWithinAt
    exact constant_of_has_deriv_right_zero hcont hderiv t ht
  -- ## endpoint values at `t = 0`
  have hψ0 : ∀ s : ℝ, ‖v + s • w‖ < ρ →
      chartMetricInner (I := I) g p (c (((0 : ℝ), s) : ℝ × ℝ))
          (P (((0 : ℝ), s) : ℝ × ℝ)) (P (((0 : ℝ), s) : ℝ × ℝ))
        = chartMetricInner (I := I) g p (extChartAt I p p)
            (v + s • w) (v + s • w) := by
    intro s hs
    have hA0 : A (((0 : ℝ), s) : ℝ × ℝ) = 0 := by
      rw [hAfact]
      show (0 : ℝ) • (v + s • w) = 0
      rw [zero_smul]
    have hc0 : c (((0 : ℝ), s) : ℝ × ℝ) = extChartAt I p p := by
      simp only [hcdef]
      rw [hA0, hf0]
    have hP0 : P (((0 : ℝ), s) : ℝ × ℝ) = v + s • w := by
      simp only [hPdef]
      rw [hA0, hfd0]
      rfl
    rw [hc0, hP0]
  -- ## the `s`-derivative of the squared speed at `s = 0`
  have hψsderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun σ : ℝ => chartMetricInner (I := I) g p (c ((t, σ) : ℝ × ℝ))
        (P ((t, σ) : ℝ × ℝ)) (P ((t, σ) : ℝ × ℝ)))
      (chartMetricInner (I := I) g p (extChartAt I p p) v w
        + chartMetricInner (I := I) g p (extChartAt I p p) w v) 0 := by
    intro t ht
    have hquad := hasDerivAt_chartMetricInner_quadratic (I := I) g p
      (extChartAt I p p) v w
    refine hquad.congr_of_eventuallyEq ?_
    have hopen : IsOpen {σ : ℝ | ‖v + σ • w‖ < ρ} :=
      isOpen_lt ((continuous_const.add (continuous_id.smul continuous_const)).norm)
        continuous_const
    have h0 : ‖v + (0 : ℝ) • w‖ < ρ := by
      rw [zero_smul, add_zero]; exact hv
    filter_upwards [hopen.mem_nhds h0] with σ hσ
    rw [hψconst σ hσ t ht, hψ0 σ hσ]
  -- ## the main derivative computation for `h(t) = ⟨∂_s c, ∂_t c⟩(t, 0)`
  have hmain : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun τ : ℝ => chartMetricInner (I := I) g p (c ((τ, (0 : ℝ)) : ℝ × ℝ))
        (Q ((τ, (0 : ℝ)) : ℝ × ℝ)) (P ((τ, (0 : ℝ)) : ℝ × ℝ)))
      (chartMetricInner (I := I) g p (extChartAt I p p) v w) t := by
    intro t ht
    have hqt := hΩt0 t ht
    -- second-derivative data at `(t, 0)`
    have hD2c : HasFDerivAt Dc (fderiv ℝ Dc ((t, (0 : ℝ)) : ℝ × ℝ))
        ((t, (0 : ℝ)) : ℝ × ℝ) := (hDc_diffAt _ hqt).hasFDerivAt
    have hcurve_t : HasDerivAt (fun τ : ℝ => ((τ, (0 : ℝ)) : ℝ × ℝ))
        ((1 : ℝ), (0 : ℝ)) t := (hasDerivAt_id t).prodMk (hasDerivAt_const t 0)
    have hcurve_s : HasDerivAt (fun σ : ℝ => ((t, σ) : ℝ × ℝ))
        ((0 : ℝ), (1 : ℝ)) 0 := (hasDerivAt_const 0 t).prodMk (hasDerivAt_id 0)
    have hDct : HasDerivAt (fun τ : ℝ => Dc ((τ, (0 : ℝ)) : ℝ × ℝ))
        (fderiv ℝ Dc ((t, (0 : ℝ)) : ℝ × ℝ) ((1 : ℝ), (0 : ℝ))) t := by
      simpa [Function.comp_def] using hD2c.comp_hasDerivAt t hcurve_t
    have hDcs : HasDerivAt (fun σ : ℝ => Dc ((t, σ) : ℝ × ℝ))
        (fderiv ℝ Dc ((t, (0 : ℝ)) : ℝ × ℝ) ((0 : ℝ), (1 : ℝ))) 0 := by
      simpa [Function.comp_def] using hD2c.comp_hasDerivAt 0 hcurve_s
    -- mixed partials of the surface through `Dc`
    have hQt : HasDerivAt (fun τ : ℝ => Q ((τ, (0 : ℝ)) : ℝ × ℝ))
        (fderiv ℝ Dc ((t, (0 : ℝ)) : ℝ × ℝ) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))) t := by
      have h := hDct.clm_apply (hasDerivAt_const t ((0 : ℝ), (1 : ℝ)))
      simp only [map_zero, add_zero] at h
      have hfun : (fun τ : ℝ => Dc ((τ, (0 : ℝ)) : ℝ × ℝ) ((0 : ℝ), (1 : ℝ)))
          = fun τ : ℝ => Q ((τ, (0 : ℝ)) : ℝ × ℝ) := funext fun τ => hQ_eq _
      rwa [hfun] at h
    have hPs : HasDerivAt (fun σ : ℝ => P ((t, σ) : ℝ × ℝ))
        (fderiv ℝ Dc ((t, (0 : ℝ)) : ℝ × ℝ) ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))) 0 := by
      have h := hDcs.clm_apply (hasDerivAt_const 0 ((1 : ℝ), (0 : ℝ)))
      simp only [map_zero, add_zero] at h
      have hfun : (fun σ : ℝ => Dc ((t, σ) : ℝ × ℝ) ((1 : ℝ), (0 : ℝ)))
          = fun σ : ℝ => P ((t, σ) : ℝ × ℝ) := funext fun σ => hP_eq _
      rwa [hfun] at h
    -- the symmetry lemma: `D/∂t ∂_s c = D/∂s ∂_t c`
    have hc_ev : ∀ᶠ y in nhds ((t, (0 : ℝ)) : ℝ × ℝ), HasFDerivAt c (Dc y) y := by
      filter_upwards [hΩo.mem_nhds hqt] with y hy
      exact hc_hasF y hy
    have hsym := Geodesic.covariant_sndFDeriv_symm_of_eventually (I := I) g p
      hc_ev hD2c ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
    rw [hP_eq, hQ_eq] at hsym
    have hswap : covariantDerivCoord (I := I) g p
        (fun τ : ℝ => c ((τ, (0 : ℝ)) : ℝ × ℝ))
        (fun τ : ℝ => Q ((τ, (0 : ℝ)) : ℝ × ℝ)) t
      = covariantDerivCoord (I := I) g p
        (fun σ : ℝ => c ((t, σ) : ℝ × ℝ))
        (fun σ : ℝ => P ((t, σ) : ℝ × ℝ)) 0 := by
      rw [covariantDerivCoord_def, covariantDerivCoord_def,
        hQt.deriv, hPs.deriv, (huTs 0 t hqt).deriv, (huSs t 0 hqt).deriv]
      exact hsym
    -- the `s`-direction product rule, matched against the quadratic derivative
    have halongS := hasDerivAt_chartMetricInner_along (I := I) g p
      (fun σ : ℝ => c ((t, σ) : ℝ × ℝ)) (fun σ : ℝ => P ((t, σ) : ℝ × ℝ))
      (fun σ : ℝ => P ((t, σ) : ℝ × ℝ))
      (huSs t 0 hqt).differentiableAt hPs.differentiableAt hPs.differentiableAt
      (fun i j => hGram _ hqt i j) (hBase _ hqt)
    have huniq := halongS.unique (hψsderiv t ht)
    have hcovS_val : chartMetricInner (I := I) g p (c ((t, (0 : ℝ)) : ℝ × ℝ))
        (covariantDerivCoord (I := I) g p (fun σ : ℝ => c ((t, σ) : ℝ × ℝ))
          (fun σ : ℝ => P ((t, σ) : ℝ × ℝ)) 0)
        (P ((t, (0 : ℝ)) : ℝ × ℝ))
      = chartMetricInner (I := I) g p (extChartAt I p p) v w := by
      have h1 := chartMetricInner_symm (I := I) g p (c ((t, (0 : ℝ)) : ℝ × ℝ))
        (P ((t, (0 : ℝ)) : ℝ × ℝ))
        (covariantDerivCoord (I := I) g p (fun σ : ℝ => c ((t, σ) : ℝ × ℝ))
          (fun σ : ℝ => P ((t, σ) : ℝ × ℝ)) 0)
      have h2 := chartMetricInner_symm (I := I) g p (extChartAt I p p) w v
      linarith [huniq]
    -- the `t`-direction product rule for `h`
    have halongT := hasDerivAt_chartMetricInner_along (I := I) g p
      (fun τ : ℝ => c ((τ, (0 : ℝ)) : ℝ × ℝ)) (fun τ : ℝ => Q ((τ, (0 : ℝ)) : ℝ × ℝ))
      (fun τ : ℝ => P ((τ, (0 : ℝ)) : ℝ × ℝ))
      (huTs 0 t hqt).differentiableAt hQt.differentiableAt
      (hVTs 0 t hqt).differentiableAt
      (fun i j => hGram _ hqt i j) (hBase _ hqt)
    rw [hgeo 0 t hqt, chartMetricInner_zero_right, add_zero, hswap, hcovS_val]
      at halongT
    exact halongT
  -- ## integrate: `h(1) − h(0) = ⟨v, w⟩`, with `h(0) = 0`
  have hF : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun τ : ℝ =>
      chartMetricInner (I := I) g p (c ((τ, (0 : ℝ)) : ℝ × ℝ))
        (Q ((τ, (0 : ℝ)) : ℝ × ℝ)) (P ((τ, (0 : ℝ)) : ℝ × ℝ))
      - τ * chartMetricInner (I := I) g p (extChartAt I p p) v w) 0 t := by
    intro t ht
    have h := (hmain t ht).sub
      (hasDerivAt_mul_const (chartMetricInner (I := I) g p (extChartAt I p p) v w))
    simpa using h
  have hFcont : ContinuousOn (fun τ : ℝ =>
      chartMetricInner (I := I) g p (c ((τ, (0 : ℝ)) : ℝ × ℝ))
        (Q ((τ, (0 : ℝ)) : ℝ × ℝ)) (P ((τ, (0 : ℝ)) : ℝ × ℝ))
      - τ * chartMetricInner (I := I) g p (extChartAt I p p) v w)
      (Icc (0 : ℝ) 1) := fun x hx => ((hF x hx).continuousAt).continuousWithinAt
  have hFderiv : ∀ x ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (fun τ : ℝ =>
      chartMetricInner (I := I) g p (c ((τ, (0 : ℝ)) : ℝ × ℝ))
        (Q ((τ, (0 : ℝ)) : ℝ × ℝ)) (P ((τ, (0 : ℝ)) : ℝ × ℝ))
      - τ * chartMetricInner (I := I) g p (extChartAt I p p) v w)
      0 (Ici x) x := fun x hx =>
    (hF x (Ico_subset_Icc_self hx)).hasDerivWithinAt
  have h10 := constant_of_has_deriv_right_zero hFcont hFderiv 1
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  -- `h(0) = 0` since `∂_s c(0, ·) = 0`
  have hQ00 : Q (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) = 0 := by
    simp only [hQdef]
    rw [zero_smul, map_zero]
  rw [hQ00, chartMetricInner_zero_left] at h10
  simp only [zero_mul, one_mul, sub_zero] at h10
  -- ## read off the Gauss identity at `(1, 0)`
  have hA10 : A (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) = v := by
    rw [hAfact]
    show (1 : ℝ) • (v + (0 : ℝ) • w) = v
    rw [zero_smul, add_zero, one_smul]
  have hc10 : c (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) = f v := by
    simp only [hcdef]
    rw [hA10]
  have hP10 : P (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) = fderiv ℝ f v v := by
    simp only [hPdef]
    rw [hA10, zero_smul, add_zero]
  have hQ10 : Q (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) = fderiv ℝ f v w := by
    simp only [hQdef]
    rw [hA10, one_smul]
  rw [hc10, hP10, hQ10, sub_eq_zero] at h10
  rw [chartMetricInner_symm (I := I) g p (f v) (fderiv ℝ f v v) (fderiv ℝ f v w)]
  exact h10

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **The Gauss lemma** (do Carmo Ch. 3, Lemma 3.5). There is `ρ > 0`
such that the ball `B_ρ(0) ⊂ T_pM` lies in the exponential domain, its image
stays in the chart at `p`, and for every `v` with `‖v‖ < ρ` and every `w`,

`⟨(d exp_p)_v(v), (d exp_p)_v(w)⟩_{exp_p(v)} = ⟨v, w⟩_p`,

everything read in the chart at `p`: the derivative of `exp_p` is the Fréchet
derivative of the chart reading `w ↦ φ_p(exp_p(w))` and the inner products are
the chart Gram inner products at the respective base points. In particular
`exp_p` preserves the radial component of the metric — the geodesic spheres
`exp_p(∂B_r(0))` are orthogonal to the radial geodesics. -/
theorem exists_gauss_lemma_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ v w : E, ‖v‖ < ρ →
        chartMetricInner (I := I) g p
          (extChartAt I p (expMap (I := I) g p (v : TangentSpace I p)))
          (fderiv ℝ (fun w' : E =>
            extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v v)
          (fderiv ℝ (fun w' : E =>
            extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v w)
        = chartMetricInner (I := I) g p (extChartAt I p p) v w) := by
  classical
  obtain ⟨ρ, b, hρ, hb, hadm, hC2, hfd0, hODE⟩ :=
    exists_expMap_ray_ode_ball (I := I) g p
  have hsrc : ∀ w' : E, ‖w'‖ < ρ →
      expMap (I := I) g p (w' : TangentSpace I p) ∈ (chartAt H p).source := by
    intro w' hw'
    have h := (hadm w' 1 hw' (by rw [abs_one]; exact hb)).2
    rwa [one_smul] at h
  have hdom : ∀ w' : E, ‖w'‖ < ρ →
      (w' : TangentSpace I p) ∈ expDomain (I := I) g p := by
    intro w' hw'
    have h := (hadm w' 1 hw' (by rw [abs_one]; exact hb)).1
    rwa [one_smul] at h
  refine ⟨ρ, hρ, hdom, hsrc, ?_⟩
  intro v w hv
  refine gauss_surface_computation (I := I) g p
    (fun w' : E => extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p)))
    hb hC2 ?_ hfd0 ?_ ?_ hODE v w hv
  · show extChartAt I p (expMap (I := I) g p ((0 : E) : TangentSpace I p))
      = extChartAt I p p
    exact congrArg (extChartAt I p) (expMap_zero (I := I) g p)
  · intro w' hw'
    refine (extChartAt I p).map_source ?_
    rw [extChartAt_source]
    exact hsrc w' hw'
  · intro w' hw'
    have hmem : expMap (I := I) g p (w' : TangentSpace I p)
        ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hsrc w' hw'
    show (extChartAt I p).symm
        (extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) ∈ _
    rw [(extChartAt I p).left_inv hmem, TangentBundle.trivializationAt_baseSet]
    exact hsrc w' hw'

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Radial lower bound from the Gauss lemma** (do Carmo Ch. 3, the
inequality driving Prop. 3.6). On the Gauss ball, for every `v` with `‖v‖ < ρ`
and every direction `ξ`,

`⟨v, ξ⟩_p² ≤ ⟨v, v⟩_p · ⟨(d exp_p)_v(ξ), (d exp_p)_v(ξ)⟩_{exp_p(v)}`

in the chart Gram inner products. Decomposing `ξ = λ v + ξ_N` with `ξ_N ⊥ v`,
the Gauss identity kills the cross term and evaluates the radial one, so
`|(d exp_p)_v(ξ)|² = λ²|v|² + |(d exp_p)_v(ξ_N)|² ≥ ⟨v,ξ⟩²/|v|²`: the
exponential map does not shrink the radial component of any vector. This is
the pointwise inequality behind `ℓ(c) ≥ ℓ(γ)` for curves in a normal ball. -/
theorem exists_gauss_radial_lower_bound_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ v ξ : E, ‖v‖ < ρ →
        chartMetricInner (I := I) g p (extChartAt I p p) v ξ ^ 2
          ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v
            * chartMetricInner (I := I) g p
                (extChartAt I p (expMap (I := I) g p (v : TangentSpace I p)))
                (fderiv ℝ (fun w' : E =>
                  extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v ξ)
                (fderiv ℝ (fun w' : E =>
                  extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v ξ)) := by
  classical
  obtain ⟨ρ, hρ, hdom, hsrc, hgauss⟩ := exists_gauss_lemma_ball (I := I) g p
  refine ⟨ρ, hρ, hdom, hsrc, ?_⟩
  intro v ξ hv
  -- the chart Gram inner product at the origin is the metric at `p`
  have hG00 : ∀ a c : E, chartMetricInner (I := I) g p (extChartAt I p p) a c
      = g.metricInner p a c := by
    intro a c
    have h := chartMetricInner_extChartAt_eq_metricInner (I := I) g p
      (mem_chart_source H p) a c
    rwa [trivializationAt_symm_self, trivializationAt_symm_self] at h
  -- the chart Gram inner product at `exp_p(v)` is positive semidefinite
  have hQnn : ∀ ξ' : E, 0 ≤ chartMetricInner (I := I) g p
      (extChartAt I p (expMap (I := I) g p (v : TangentSpace I p))) ξ' ξ' := by
    intro ξ'
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (hsrc v hv)]
    exact g.metricInner_self_nonneg _ _
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [chartMetricInner_zero_left, chartMetricInner_zero_left]
    simp
  · have hb_pos : 0 < chartMetricInner (I := I) g p (extChartAt I p p) v v := by
      rw [hG00]
      exact g.metricInner_self_pos p v hv0
    set a : ℝ := chartMetricInner (I := I) g p (extChartAt I p p) v ξ with hadef
    set b : ℝ := chartMetricInner (I := I) g p (extChartAt I p p) v v with hbdef
    have hb0 : b ≠ 0 := ne_of_gt hb_pos
    set ξn : E := ξ - (a / b) • v with hξndef
    -- orthogonal decomposition
    have hortho : chartMetricInner (I := I) g p (extChartAt I p p) v ξn = 0 := by
      rw [hξndef, sub_eq_add_neg, ← neg_smul, chartMetricInner_add_right,
        chartMetricInner_smul_right, ← hadef, ← hbdef]
      field_simp
      ring
    have hexp : ξ = (a / b) • v + ξn := by
      rw [hξndef]
      abel
    have hDf : fderiv ℝ (fun w' : E =>
          extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v ξ
        = (a / b) • (fderiv ℝ (fun w' : E =>
            extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v v)
          + fderiv ℝ (fun w' : E =>
            extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v ξn := by
      conv_lhs => rw [hexp]
      rw [map_add, map_smul]
    rw [hDf, chartMetricInner_add_left, chartMetricInner_add_right,
      chartMetricInner_add_right, chartMetricInner_smul_left,
      chartMetricInner_smul_left, chartMetricInner_smul_right,
      chartMetricInner_smul_right,
      chartMetricInner_symm (I := I) g p _
        (fderiv ℝ (fun w' : E =>
          extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v ξn)
        (fderiv ℝ (fun w' : E =>
          extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v v),
      hgauss v v hv, hgauss v ξn hv, hortho]
    set Qn : ℝ := chartMetricInner (I := I) g p
        (extChartAt I p (expMap (I := I) g p (v : TangentSpace I p)))
        (fderiv ℝ (fun w' : E =>
          extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v ξn)
        (fderiv ℝ (fun w' : E =>
          extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v ξn)
      with hQndef
    have hQn : 0 ≤ Qn := by
      rw [hQndef]
      exact hQnn _
    rw [← hbdef]
    have hfinal : b * (a / b * (a / b * b) + a / b * 0 + (a / b * 0 + Qn))
        = a ^ 2 + b * Qn := by
      field_simp
      ring
    rw [hfinal]
    have hbQ : 0 ≤ b * Qn := mul_nonneg hb_pos.le hQn
    linarith

end Exponential
end Riemannian
