import DoCarmoLib.Riemannian.Exponential.Minimizing

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Base-uniform Gauss estimates: the analytic core at a free base Gram point

do Carmo Ch. 3, §3 (Proposition 3.6, the analytic heart), generalized so the
*base point* of the Gram form is a free vector `y ∈ (extChartAt I p).target`
rather than the fixed center `extChartAt I p p`.

The fixed-base versions in `GaussLemma.lean` / `Minimizing.lean`
(`gauss_surface_computation`, `gauss_radius_comparison`, `gauss_radius_reach`)
are all *abstract in the chart reading `f`* of the exponential map, and use the
base point only as (i) the value `f 0` and (ii) a base Gram point in
base-point-general helper lemmas — **positive-definiteness of the base Gram is
never used** in the surface computation, and only positive *semi*definiteness
(`chartMetricInner_self_nonneg_of_mem_target`) in the comparison/reach. Hence the
whole analytic chain generalizes to a free base Gram point `y` by a purely
mechanical substitution `extChartAt I p p ↦ y`.

This is the missing **base-uniform** toolkit: instantiated at the moving base
`y = φ_p(q)` with `f` the chart-`p` reading `w ↦ (Z(φ_p q, T⁻¹ • w) T)₁` of the
totally-normal flow-segment exponential at `q`, these give the Gauss lemma and
the radial length comparison at every center `q` near `p`, *uniformly*, which is
exactly the lower-bound crux (`Hlb`) of the convex-neighborhood Proposition 4.2
(`prop:dc-ch3-4-2`). What remains, to close `Hlb`, is to supply the abstract
hypotheses (`C²`, `(df)₀ = id`, the chart-`p` geodesic ODE for the ray
velocities) for that moving flow reading — see the file docstring of
`ConvexNeighborhoodJoin.lean`.

Contents (all free in the base Gram point `y`):
* `gauss_surface_computation_at` — the Gauss-lemma surface computation
  `⟨(df)_v v, (df)_v w⟩_{f v} = ⟨v, w⟩_y`;
* `gauss_radial_lower_bound_at` — the radial Cauchy–Schwarz inequality
  `⟨v, ξ⟩_y² ≤ ⟨v, v⟩_y · ⟨(df)_v ξ, (df)_v ξ⟩_{f v}` (from the Gauss identity);
* `gauss_radius_comparison_at` — the radius-gain ≤ chart length estimate;
* `gauss_radius_reach_at` — the escape/reach estimate.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The Gauss-lemma surface computation at a free base Gram point**
(do Carmo Ch. 3, Lemma 3.5, base-generalized). Identical to
`gauss_surface_computation` but with the fixed center `extChartAt I p p` replaced
by an arbitrary base vector `y` (supplied as `f 0 = y`): the surface argument
never uses positive-definiteness of the base Gram, so `f` is a radial isometry
onto the Gram form based at `y`. -/
theorem gauss_surface_computation_at (g : RiemannianMetric I M) (p : M)
    (f : E → E) (y : E) {ρ b : ℝ} (hb : 1 < b)
    (hC2 : ContDiffOn ℝ 2 f (ball (0 : E) ρ))
    (hf0 : f 0 = y)
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
      = chartMetricInner (I := I) g p (y) v w := by
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
        = chartMetricInner (I := I) g p (y)
            (v + s • w) (v + s • w) := by
    intro s hs
    have hA0 : A (((0 : ℝ), s) : ℝ × ℝ) = 0 := by
      rw [hAfact]
      show (0 : ℝ) • (v + s • w) = 0
      rw [zero_smul]
    have hc0 : c (((0 : ℝ), s) : ℝ × ℝ) = y := by
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
      (chartMetricInner (I := I) g p (y) v w
        + chartMetricInner (I := I) g p (y) w v) 0 := by
    intro t ht
    have hquad := hasDerivAt_chartMetricInner_quadratic (I := I) g p
      (y) v w
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
      (chartMetricInner (I := I) g p (y) v w) t := by
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
      = chartMetricInner (I := I) g p (y) v w := by
      have h1 := chartMetricInner_symm (I := I) g p (c ((t, (0 : ℝ)) : ℝ × ℝ))
        (P ((t, (0 : ℝ)) : ℝ × ℝ))
        (covariantDerivCoord (I := I) g p (fun σ : ℝ => c ((t, σ) : ℝ × ℝ))
          (fun σ : ℝ => P ((t, σ) : ℝ × ℝ)) 0)
      have h2 := chartMetricInner_symm (I := I) g p (y) w v
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
      - τ * chartMetricInner (I := I) g p (y) v w) 0 t := by
    intro t ht
    have h := (hmain t ht).sub
      (hasDerivAt_mul_const (chartMetricInner (I := I) g p (y) v w))
    simpa using h
  have hFcont : ContinuousOn (fun τ : ℝ =>
      chartMetricInner (I := I) g p (c ((τ, (0 : ℝ)) : ℝ × ℝ))
        (Q ((τ, (0 : ℝ)) : ℝ × ℝ)) (P ((τ, (0 : ℝ)) : ℝ × ℝ))
      - τ * chartMetricInner (I := I) g p (y) v w)
      (Icc (0 : ℝ) 1) := fun x hx => ((hF x hx).continuousAt).continuousWithinAt
  have hFderiv : ∀ x ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (fun τ : ℝ =>
      chartMetricInner (I := I) g p (c ((τ, (0 : ℝ)) : ℝ × ℝ))
        (Q ((τ, (0 : ℝ)) : ℝ × ℝ)) (P ((τ, (0 : ℝ)) : ℝ × ℝ))
      - τ * chartMetricInner (I := I) g p (y) v w)
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


theorem gauss_radius_comparison_at (g : RiemannianMetric I M) (p : M)
    (f : E → E) (y : E) (hy : y ∈ (extChartAt I p).target) {ρ : ℝ}
    (htgt : ∀ u : E, ‖u‖ < ρ → f u ∈ (extChartAt I p).target)
    (hC1 : ContDiffOn ℝ 1 f (ball (0 : E) ρ))
    (hradial : ∀ v ξ : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (y) v ξ ^ 2
        ≤ chartMetricInner (I := I) g p (y) v v
          * chartMetricInner (I := I) g p (f v) (fderiv ℝ f v ξ) (fderiv ℝ f v ξ))
    {w w' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hw_cont : ContinuousOn w (Icc a b))
    (hw : ∀ t ∈ Ioo a b, HasDerivAt w (w' t) t)
    (hw' : ContinuousOn w' (Icc a b))
    (hwball : ∀ t ∈ Icc a b, ‖w t‖ < ρ) :
    Real.sqrt (chartMetricInner (I := I) g p (y) (w b) (w b))
      - Real.sqrt (chartMetricInner (I := I) g p (y) (w a) (w a))
      ≤ ∫ t in a..b, Real.sqrt (chartMetricInner (I := I) g p (f (w t))
          (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t))) := by
  classical
  have hy₀tgt : y ∈ (extChartAt I p).target :=
    hy
  set Q : ℝ → ℝ :=
    fun t => chartMetricInner (I := I) g p (y) (w t) (w t) with hQdef
  set P : ℝ → ℝ :=
    fun t => chartMetricInner (I := I) g p (y) (w t) (w' t) with hPdef
  set D : ℝ → E := fun t => fderiv ℝ f (w t) (w' t) with hDdef
  set R : ℝ → ℝ :=
    fun t => chartMetricInner (I := I) g p (f (w t)) (D t) (D t) with hRdef
  set S : ℝ → ℝ := fun t => Real.sqrt (R t) with hSdef
  -- continuity of the pieces on `[a, b]`
  have hQ_cont : ContinuousOn Q (Icc a b) :=
    continuousOn_chartMetricInner_along (I := I) g p continuousOn_const hw_cont hw_cont
      (fun t _ => hy₀tgt)
  have hP_cont : ContinuousOn P (Icc a b) :=
    continuousOn_chartMetricInner_along (I := I) g p continuousOn_const hw_cont hw'
      (fun t _ => hy₀tgt)
  have hmaps : MapsTo w (Icc a b) (ball (0 : E) ρ) := fun t ht =>
    mem_ball_zero_iff.mpr (hwball t ht)
  have hD_cont : ContinuousOn D (Icc a b) := by
    have h1 : ContinuousOn (fun t => fderiv ℝ f (w t)) (Icc a b) :=
      (hC1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).comp hw_cont hmaps
    exact h1.clm_apply hw'
  have hfw_tgt : ∀ t ∈ Icc a b, f (w t) ∈ (extChartAt I p).target := fun t ht =>
    htgt (w t) (hwball t ht)
  have hfw_cont : ContinuousOn (fun t => f (w t)) (Icc a b) :=
    hC1.continuousOn.comp hw_cont hmaps
  have hR_cont : ContinuousOn R (Icc a b) :=
    continuousOn_chartMetricInner_along (I := I) g p hfw_cont hD_cont hD_cont hfw_tgt
  have hS_cont : ContinuousOn S (Icc a b) := hR_cont.sqrt
  have hS_int : IntervalIntegrable S MeasureTheory.volume a b :=
    hS_cont.intervalIntegrable_of_Icc hab
  -- nonnegativity of the two quadratic forms
  have hQ_nonneg : ∀ t ∈ Icc a b, 0 ≤ Q t := fun t _ =>
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p hy₀tgt (w t)
  have hR_nonneg : ∀ t ∈ Icc a b, 0 ≤ R t := fun t ht =>
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p (hfw_tgt t ht) (D t)
  -- the radial lower bound in `P/Q/R` form
  have hPQR : ∀ t ∈ Icc a b, P t ^ 2 ≤ Q t * R t := fun t ht =>
    hradial (w t) (w' t) (hwball t ht)
  -- ## the smoothed-radius estimate, for every `δ > 0`
  have hkey : ∀ δ : ℝ, 0 < δ →
      Real.sqrt (Q b + δ) - Real.sqrt (Q a + δ) ≤ ∫ t in a..b, S t := by
    intro δ hδ
    have hQδ_pos : ∀ t ∈ Icc a b, 0 < Q t + δ := fun t ht => by
      have := hQ_nonneg t ht; linarith
    -- the smoothed radius and its derivative (on the open interval)
    have hφderiv : ∀ t ∈ Ioo a b,
        HasDerivAt (fun s => Real.sqrt (Q s + δ)) (P t / Real.sqrt (Q t + δ)) t := by
      intro t ht
      have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
      have hQ' : HasDerivAt Q (2 * P t) t := by
        have h := hasDerivAt_chartMetricInner_const_base (I := I) g p
          (y) (hw t ht) (hw t ht)
        refine h.congr_deriv ?_
        rw [chartMetricInner_symm (I := I) g p (y) (w' t) (w t)]
        rw [hPdef]
        ring
      have hQt : HasDerivAt (fun s => Q s + δ) (2 * P t) t := hQ'.add_const δ
      have hsq := (Real.hasDerivAt_sqrt (ne_of_gt (hQδ_pos t ht'))).comp t hQt
      have hs_pos : 0 < Real.sqrt (Q t + δ) := Real.sqrt_pos.mpr (hQδ_pos t ht')
      refine (hsq.congr_deriv ?_ : HasDerivAt (fun s => Real.sqrt (Q s + δ)) _ t)
      field_simp
    have hφ'_cont : ContinuousOn (fun t => P t / Real.sqrt (Q t + δ)) (Icc a b) := by
      refine hP_cont.div ((hQ_cont.add continuousOn_const).sqrt) ?_
      intro t ht
      exact ne_of_gt (Real.sqrt_pos.mpr (hQδ_pos t ht))
    have hφ'_int : IntervalIntegrable (fun t => P t / Real.sqrt (Q t + δ))
        MeasureTheory.volume a b :=
      hφ'_cont.intervalIntegrable_of_Icc hab
    have hφcont : ContinuousOn (fun s => Real.sqrt (Q s + δ)) (Icc a b) :=
      (hQ_cont.add continuousOn_const).sqrt
    have hFTC : (∫ t in a..b, P t / Real.sqrt (Q t + δ))
        = Real.sqrt (Q b + δ) - Real.sqrt (Q a + δ) := by
      refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
        (f := fun s => Real.sqrt (Q s + δ)) hab hφcont
        (fun t ht => (hφderiv t ht).hasDerivWithinAt) hφ'_int
    -- the pointwise bound `r_δ'(t) ≤ |ċ(t)|_g`
    have hbound : ∀ t ∈ Icc a b, P t / Real.sqrt (Q t + δ) ≤ S t := by
      intro t ht
      have hRt := hR_nonneg t ht
      have hs_pos : 0 < Real.sqrt (Q t + δ) := Real.sqrt_pos.mpr (hQδ_pos t ht)
      have h1 : P t ^ 2 ≤ (Q t + δ) * R t := by
        have h2 := hPQR t ht
        nlinarith [mul_nonneg (le_of_lt hδ) hRt]
      have h2 : P t ≤ Real.sqrt ((Q t + δ) * R t) :=
        calc P t ≤ |P t| := le_abs_self _
          _ = Real.sqrt (P t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt ((Q t + δ) * R t) := Real.sqrt_le_sqrt h1
      rw [div_le_iff₀ hs_pos]
      calc P t ≤ Real.sqrt ((Q t + δ) * R t) := h2
        _ = Real.sqrt (Q t + δ) * S t := Real.sqrt_mul (le_of_lt (hQδ_pos t ht)) _
        _ = S t * Real.sqrt (Q t + δ) := mul_comm _ _
    calc Real.sqrt (Q b + δ) - Real.sqrt (Q a + δ)
        = ∫ t in a..b, P t / Real.sqrt (Q t + δ) := hFTC.symm
      _ ≤ ∫ t in a..b, S t :=
          intervalIntegral.integral_mono_on hab hφ'_int hS_int hbound
  -- ## let `δ → 0⁺`
  have htend : Tendsto (fun δ : ℝ => Real.sqrt (Q b + δ) - Real.sqrt (Q a + δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (Q b) - Real.sqrt (Q a))) := by
    have hcont : Continuous (fun δ : ℝ => Real.sqrt (Q b + δ) - Real.sqrt (Q a + δ)) := by
      fun_prop
    have h0 := hcont.tendsto 0
    simp only [add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hkey δ hδ


theorem gauss_radius_reach_at (g : RiemannianMetric I M) (p : M)
    (f : E → E) (y : E) (hy : y ∈ (extChartAt I p).target) {ρ : ℝ}
    (htgt : ∀ u : E, ‖u‖ < ρ → f u ∈ (extChartAt I p).target)
    (hC1 : ContDiffOn ℝ 1 f (ball (0 : E) ρ))
    (hradial : ∀ v ξ : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (y) v ξ ^ 2
        ≤ chartMetricInner (I := I) g p (y) v v
          * chartMetricInner (I := I) g p (f v) (fderiv ℝ f v ξ) (fderiv ℝ f v ξ))
    {w w' : ℝ → E} {a b : ℝ}
    (hw_cont : ContinuousOn w (Icc a b))
    (hw : ∀ t ∈ Ioo a b, HasDerivAt w (w' t) t)
    (hw' : ContinuousOn w' (Icc a b))
    (hwball : ∀ t ∈ Icc a b, ‖w t‖ < ρ)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a b) :
    Real.sqrt (chartMetricInner (I := I) g p (y) (w t₁) (w t₁))
      - Real.sqrt (chartMetricInner (I := I) g p (y) (w a) (w a))
      ≤ ∫ t in a..b, Real.sqrt (chartMetricInner (I := I) g p (f (w t))
          (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t))) := by
  classical
  have hsub : Icc a t₁ ⊆ Icc a b := Icc_subset_Icc le_rfl ht₁.2
  have hsub' : Ioo a t₁ ⊆ Ioo a b := Ioo_subset_Ioo le_rfl ht₁.2
  -- radius comparison on `[a, t₁]`
  have hstep := gauss_radius_comparison_at (I := I) g p f y hy htgt hC1 hradial
    (w := w) (w' := w') ht₁.1 (hw_cont.mono hsub)
    (fun t ht => hw t (hsub' ht)) (hw'.mono hsub) (fun t ht => hwball t (hsub ht))
  refine hstep.trans ?_
  -- the speed integrand is continuous on `[a, b]`, hence interval integrable
  have hmaps : MapsTo w (Icc a b) (ball (0 : E) ρ) := fun t ht =>
    mem_ball_zero_iff.mpr (hwball t ht)
  have hD_cont : ContinuousOn (fun t => fderiv ℝ f (w t) (w' t)) (Icc a b) :=
    ((hC1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).comp hw_cont
      hmaps).clm_apply hw'
  have hS_cont : ContinuousOn (fun t => Real.sqrt (chartMetricInner (I := I) g p
      (f (w t)) (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t)))) (Icc a b) :=
    (continuousOn_chartMetricInner_along (I := I) g p
      (hC1.continuousOn.comp hw_cont hmaps) hD_cont hD_cont
      (fun t ht => htgt (w t) (hwball t ht))).sqrt
  have hS_int : IntervalIntegrable (fun t => Real.sqrt (chartMetricInner (I := I) g p
      (f (w t)) (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t))))
      MeasureTheory.volume a b :=
    hS_cont.intervalIntegrable_of_Icc (ht₁.1.trans ht₁.2)
  -- monotonicity in the upper endpoint: the integrand is nonnegative
  refine intervalIntegral.integral_mono_interval le_rfl ht₁.1 ht₁.2 ?_ hS_int
  filter_upwards with t
  exact Real.sqrt_nonneg _

/-- **Math.** **The chart Gram quadratic form is positive definite at every base
point `y` of the chart target.** For `v ≠ 0`, `0 < ⟨v, v⟩_y`. The base Gram at
`y = φ_p(q)` is the pullback of the (positive-definite) metric at the foot
`q = φ_p⁻¹(y)` through the *injective* trivialization inverse
`(trivializationAt E (TangentSpace I) p).symm q`, so it stays positive definite —
the moving-base analogue of `chartMetricInner_extChartAt_self_pos` (which is the
special case `y = extChartAt I p p`). -/
theorem chartMetricInner_self_pos_of_mem_target (g : RiemannianMetric I M) (p : M)
    {y : E} (hy : y ∈ (extChartAt I p).target) {v : E} (hv : v ≠ 0) :
    0 < chartMetricInner (I := I) g p y v v := by
  have hfoot : (extChartAt I p).symm y ∈ (chartAt H p).source := by
    have h := (extChartAt I p).map_target hy
    rwa [extChartAt_source] at h
  have hbaseSet : (extChartAt I p).symm y ∈
      (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hfoot
  have hyval : y = extChartAt I p ((extChartAt I p).symm y) :=
    ((extChartAt I p).right_inv hy).symm
  rw [hyval, chartMetricInner_extChartAt_eq_metricInner (I := I) g p hfoot]
  refine g.metricInner_self_pos _ _ ?_
  -- the trivialization inverse over `q ∈ baseSet` is injective (it is the inverse
  -- of the continuous linear equivalence `continuousLinearEquivAt`)
  set cle := (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ
    ((extChartAt I p).symm y) hbaseSet with hcle
  have hid : (trivializationAt E (TangentSpace I) p).symm ((extChartAt I p).symm y) v
      = cle.symm v := by
    rw [show (trivializationAt E (TangentSpace I) p).symm ((extChartAt I p).symm y) v
          = (trivializationAt E (TangentSpace I) p).symmL ℝ
              ((extChartAt I p).symm y) v from rfl,
      ← Trivialization.symm_continuousLinearEquivAt_eq
          (trivializationAt E (TangentSpace I) p) hbaseSet]
  rw [hid]
  simpa using (cle.symm.map_eq_zero_iff).not.mpr hv

/-- **Math.** **The radial lower bound at a free base Gram point** (do Carmo
Ch. 3, the Cauchy–Schwarz inequality driving Prop. 3.6, base-generalized). Given
the Gauss identity `⟨(df)_v v, (df)_v w⟩_{f v} = ⟨v, w⟩_y` (e.g. from
`gauss_surface_computation_at`) and `y ∈ (extChartAt I p).target`, decomposing
`ξ = λ v + ξ_N` with `ξ_N ⊥_y v` gives
`⟨v, ξ⟩_y² ≤ ⟨v, v⟩_y · ⟨(df)_v ξ, (df)_v ξ⟩_{f v}`: `f` does not shrink the
radial component of any vector, measured against the Gram form based at `y`. -/
theorem gauss_radial_lower_bound_at (g : RiemannianMetric I M) (p : M)
    (f : E → E) (y : E) (hy : y ∈ (extChartAt I p).target) {ρ : ℝ}
    (htgt : ∀ w' : E, ‖w'‖ < ρ → f w' ∈ (extChartAt I p).target)
    (hgauss : ∀ v w : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (f v) (fderiv ℝ f v v) (fderiv ℝ f v w)
        = chartMetricInner (I := I) g p y v w)
    (v ξ : E) (hv : ‖v‖ < ρ) :
    chartMetricInner (I := I) g p y v ξ ^ 2
      ≤ chartMetricInner (I := I) g p y v v
        * chartMetricInner (I := I) g p (f v)
            (fderiv ℝ f v ξ) (fderiv ℝ f v ξ) := by
  classical
  have hQnn : ∀ ξ' : E, 0 ≤ chartMetricInner (I := I) g p (f v) ξ' ξ' := fun ξ' =>
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p (htgt v hv) ξ'
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [chartMetricInner_zero_left, chartMetricInner_zero_left]
    simp
  · have hb_pos : 0 < chartMetricInner (I := I) g p y v v :=
      chartMetricInner_self_pos_of_mem_target (I := I) g p hy hv0
    set a : ℝ := chartMetricInner (I := I) g p y v ξ with hadef
    set b : ℝ := chartMetricInner (I := I) g p y v v with hbdef
    have hb0 : b ≠ 0 := ne_of_gt hb_pos
    set ξn : E := ξ - (a / b) • v with hξndef
    have hortho : chartMetricInner (I := I) g p y v ξn = 0 := by
      rw [hξndef, sub_eq_add_neg, ← neg_smul, chartMetricInner_add_right,
        chartMetricInner_smul_right, ← hadef, ← hbdef]
      field_simp
      ring
    have hexp : ξ = (a / b) • v + ξn := by
      rw [hξndef]
      abel
    have hDf : fderiv ℝ f v ξ
        = (a / b) • (fderiv ℝ f v v) + fderiv ℝ f v ξn := by
      conv_lhs => rw [hexp]
      rw [map_add, map_smul]
    rw [hDf, chartMetricInner_add_left, chartMetricInner_add_right,
      chartMetricInner_add_right, chartMetricInner_smul_left,
      chartMetricInner_smul_left, chartMetricInner_smul_right,
      chartMetricInner_smul_right,
      chartMetricInner_symm (I := I) g p _ (fderiv ℝ f v ξn) (fderiv ℝ f v v),
      hgauss v v hv, hgauss v ξn hv, hortho]
    set Qn : ℝ := chartMetricInner (I := I) g p (f v)
        (fderiv ℝ f v ξn) (fderiv ℝ f v ξn) with hQndef
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
