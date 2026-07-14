import OpenGALib.Riemannian.Geodesic.UniformExistence
import OpenGALib.Riemannian.Geodesic.FlowDependence
import OpenGALib.Riemannian.Geodesic.FlowC1Dependence
import OpenGALib.Riemannian.Geodesic.EquationTransfer
import OpenGALib.Riemannian.Exponential.StrictDerivative

/-!
# Totally normal neighborhoods (do Carmo Ch. 3, Theorem 3.7)

do Carmo, *Riemannian Geometry*, Ch. 3, Theorem 3.7: for every `p ∈ M` there
are a neighborhood `W` of `p` and `δ > 0` such that every `q ∈ W` is the
center of a normal ball of radius `δ` whose image contains `W` — any two
points of `W` are joined by a geodesic segment of small initial velocity,
uniquely parametrized. do Carmo's proof applies the inverse function theorem
to the pair map `F(q, v) = (q, exp_q v)`, whose differential at `(p, 0)` is
the invertible block matrix `[[I, 0], [I, I]]`.

The formalization works in the chart at `p` throughout, so that a *single*
uniform velocity ball serves every base point `q ∈ W`:

* the geodesic with initial data `(q, v)` is realized as the flow line of the
  chart-`p` coordinate spray through `(φ_p(q), w)`, where `w` is the chart-`p`
  coordinate of the velocity (`exists_uniform_geodesic_flow` accepts arbitrary
  initial conditions near the zero section, not only those over `p`);
* `isGeodesicOn_uniform_flow_segment` — **descent**: such a flow line projects
  to a curve on `M` satisfying the *intrinsic* moving-foot geodesic equation
  (`IsGeodesicOn`, the predicate consumed by the Hopf–Rinow development),
  via the chart-independence of the geodesic ODE (`EquationTransfer.lean`).
  This sidesteps the chart-`q`-anchored witness framework of
  `MaximalInterval.lean`, which cannot support a `δ` uniform in `q` (the
  charts at nearby `q` have no common lower bound on their source size);
* `exists_pairMap_hasStrictFDerivAt` — the pair map
  `G(y, w) = (y, (Z(y, w/T) T).1)` (chart reading of
  `(q, v) ↦ (q, exp_q v)` under the time-rescaling `γ(1, q, v) = γ(T, q, v/T)`)
  is strictly differentiable at `(φ_p(p), 0)` with derivative the shear
  `(a, b) ↦ (a, a + b)` — do Carmo's matrix `[[I, 0], [I, I]]` read in the
  first components. The derivative is computed from the variational equation
  along the equilibrium, whose operator `A(u, w) = (w, 0)` is two-step
  nilpotent, exactly as in `StrictDerivative.lean` but keeping the base-point
  slot of the initial condition free;
* `exists_totallyNormal_neighborhood` — the theorem: the shear is invertible,
  so the inverse function theorem makes `G` a homeomorphism near `(φ_p(p), 0)`;
  a product ball inside its source and a square neighborhood
  `W̃ × W̃ ⊆ G(ball × ball)` produce `W` and `δ` with existence and uniqueness
  of the joining parameter.
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **Descent: flow segments of the chart-`p` spray are intrinsic
geodesic segments, from any base point in the chart** (do Carmo Ch. 3, §2.5,
freed from the initial-point-over-`p` restriction of `ChartFlow.lean`). Let `Z`
be a local flow of the chart-`p` coordinate spray on a ball around the zero
section, as produced by `exists_uniform_geodesic_flow`, and let `(y, T⁻¹ • w)`
be an initial condition in that ball (base chart-position `y`, chart-velocity
`T⁻¹ • w`). Then the time-rescaled projected curve
`γ(s) = φ_p⁻¹((Z(y, T⁻¹ • w)(sT))₁)`

* starts at `φ_p⁻¹(y)`,
* is continuous on `[0, 1]` and satisfies the intrinsic geodesic equation
  (`IsGeodesicOn`) there,
* stays in the chart at `p`, where its reading is the flow line itself, and
* has chart velocity `w` at `s = 0`.

The geodesic property is intrinsic (`HasGeodesicEquationAt` reads the equation
in the chart at the moving foot): the flow line solves the second-order spray
ODE in the fixed chart at `p`, and the chart-independence of the geodesic ODE
(`SolvesGeodesicODEAt.hasGeodesicEquationAt`) transfers it to the foot chart.
No membership of the feet in charts other than the chart at `p` is needed —
this is what makes the statement uniform in the base point `y`. -/
theorem isGeodesicOn_uniform_flow_segment
    (g : RiemannianMetric I M) (p : M) {r ε T : ℝ} {Z : E × E → ℝ → E × E}
    (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    {y w : E}
    (hmem : ((y, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r) :
    (fun s : ℝ => (extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) 0 = (extChartAt I p).symm y ∧
    ContinuousOn (fun s : ℝ => (extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) (Icc 0 1) ∧
    IsGeodesicOn (I := I) g (fun s : ℝ => (extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) (Icc 0 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1,
      (extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1) ∈
        (chartAt H p).source ∧
      extChartAt I p
          ((extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) =
        (Z ((y, T⁻¹ • w) : E × E) (s * T)).1) ∧
    HasDerivAt (fun s : ℝ =>
      extChartAt I p
        ((extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1))) w 0 ∧
    HasDerivAt (deriv (fun s : ℝ =>
        extChartAt I p
          ((extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1))))
      (geodesicSprayCoord (I := I) g p y w).2 0 := by
  classical
  obtain ⟨h0, hd, hconf⟩ := hflow _ hmem
  set zc : ℝ → E × E := Z ((y, T⁻¹ • w) : E × E) with hzcdef
  -- upgrade the flow derivative to `HasDerivAt` on the open time interval
  have hdIoo : ∀ t ∈ Ioo (-ε) ε, HasDerivAt zc
      (geodesicSprayCoord (I := I) g p (zc t).1 (zc t).2) t := fun t ht =>
    (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  -- the rescaled time window
  set J : Set ℝ := Ioo (-(ε / T)) (ε / T) with hJdef
  have hJopen : IsOpen J := isOpen_Ioo
  have hwin : ∀ s ∈ J, s * T ∈ Ioo (-ε) ε := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    have h2' : s * T < ε := (lt_div_iff₀ hT).mp h2
    have h1' : -s < ε / T := neg_lt.mp h1
    have h1'' : -s * T < ε := (lt_div_iff₀ hT).mp h1'
    exact ⟨by linarith, h2'⟩
  have h01J : Icc (0 : ℝ) 1 ⊆ J := by
    intro s hs
    have hεT : (1 : ℝ) < ε / T := (one_lt_div hT).mpr hTε
    exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  -- the chart-position and chart-velocity components of the rescaled flow line
  set c : ℝ → E := fun s => (zc (s * T)).1 with hcdef
  set v : ℝ → E := fun s => (zc (s * T)).2 with hvdef
  have hcv : ∀ s ∈ J, HasDerivAt (fun σ : ℝ => zc (σ * T))
      (T • geodesicSprayCoord (I := I) g p (zc (s * T)).1 (zc (s * T)).2) s := by
    intro s hs
    have hmul : HasDerivAt (fun σ : ℝ => σ * T) T s := by
      simpa using (hasDerivAt_id s).mul_const T
    exact (hdIoo (s * T) (hwin s hs)).scomp s hmul
  have hc : ∀ s ∈ J, HasDerivAt c (T • v s) s := by
    intro s hs
    have h := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt s
      (hcv s hs)
    simpa [hcdef, hvdef, geodesicSprayCoord_def] using h
  have hv : ∀ s ∈ J, HasDerivAt v
      (T • (- chartChristoffelContraction (I := I) g p (v s) (v s) (c s))) s := by
    intro s hs
    have h := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt s
      (hcv s hs)
    simpa [hcdef, hvdef, geodesicSprayCoord_def] using h
  -- confinement of the chart-position component in the chart target
  have hcmem : ∀ s ∈ J, c s ∈ (extChartAt I p).target := fun s hs =>
    (hconf (s * T) (Ioo_subset_Icc_self (hwin s hs))).1
  -- the projected curve on `M`
  set γ : ℝ → M := fun s => (extChartAt I p).symm (c s) with hγdef
  have hγsrc : ∀ s ∈ J, γ s ∈ (chartAt H p).source := by
    intro s hs
    have := (extChartAt I p).map_target (hcmem s hs)
    rwa [extChartAt_source] at this
  have hread : ∀ s ∈ J, extChartAt I p (γ s) = c s := fun s hs =>
    (extChartAt I p).right_inv (hcmem s hs)
  have hccont : ∀ s ∈ J, ContinuousAt c s := fun s hs => (hc s hs).continuousAt
  have hγcont : ContinuousOn γ J := by
    intro s hs
    have hcw : ContinuousWithinAt c J s := (hccont s hs).continuousWithinAt
    have hmap : MapsTo c J (extChartAt I p).target := fun σ hσ => hcmem σ hσ
    exact ((continuousOn_extChartAt_symm p).comp (fun σ hσ => (hccont σ hσ).continuousWithinAt) hmap) s hs
  -- the reading agrees with `c` near every point of the window
  have hread_ev : ∀ s ∈ J, chartReading (I := I) p γ =ᶠ[𝓝 s] c := by
    intro s hs
    filter_upwards [hJopen.mem_nhds hs] with σ hσ
    exact hread σ hσ
  have hderiv_read : ∀ s ∈ J, deriv (chartReading (I := I) p γ) s = T • v s := by
    intro s hs
    rw [(hread_ev s hs).deriv_eq]
    exact (hc s hs).deriv
  -- the intrinsic geodesic equation on the window
  have hgeo : IsGeodesicOn (I := I) g γ J := by
    intro s₀ hs₀
    have hsolves : SolvesGeodesicODEAt (I := I) g p γ s₀ := by
      constructor
      · filter_upwards [hJopen.mem_nhds hs₀] with τ hτ
        have h1 : HasDerivAt (chartReading (I := I) p γ) (T • v τ) τ :=
          (hc τ hτ).congr_of_eventuallyEq (hread_ev τ hτ)
        rwa [hderiv_read τ hτ]
      · refine ⟨- chartChristoffelContraction (I := I) g p (T • v s₀) (T • v s₀)
          (c s₀), ?_, ?_⟩
        · have hTv : HasDerivAt (fun τ => T • v τ)
              (T • (T • (- chartChristoffelContraction (I := I) g p
                (v s₀) (v s₀) (c s₀)))) s₀ := (hv s₀ hs₀).const_smul T
          have hval : (T • (T • (- chartChristoffelContraction (I := I) g p
              (v s₀) (v s₀) (c s₀))))
              = - chartChristoffelContraction (I := I) g p (T • v s₀) (T • v s₀)
                  (c s₀) := by
            rw [chartChristoffelContraction_smul_smul (I := I) g p T (v s₀) (c s₀)]
            rw [smul_neg, smul_neg, smul_smul]
          rw [hval] at hTv
          refine hTv.congr_of_eventuallyEq ?_
          filter_upwards [hJopen.mem_nhds hs₀] with τ hτ
          exact hderiv_read τ hτ
        · rw [hderiv_read s₀ hs₀]
          have hval₀ : chartReading (I := I) p γ s₀ = c s₀ := hread s₀ hs₀
          rw [hval₀]
          exact neg_add_cancel _
    exact hsolves.hasGeodesicEquationAt
      (hγcont.continuousAt (hJopen.mem_nhds hs₀)) (hγsrc s₀ hs₀)
  -- initial value
  have h0J : (0 : ℝ) ∈ J := h01J ⟨le_rfl, zero_le_one⟩
  have hγ0 : γ 0 = (extChartAt I p).symm y := by
    have : c 0 = y := by
      show (zc (0 * T)).1 = y
      rw [zero_mul, h0]
    rw [hγdef]
    show (extChartAt I p).symm (c 0) = (extChartAt I p).symm y
    rw [this]
  -- chart velocity at `s = 0`
  have hvel : HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 := by
    have hv0 : v 0 = T⁻¹ • w := by
      show (zc (0 * T)).2 = T⁻¹ • w
      rw [zero_mul, h0]
    have h1 : HasDerivAt c (T • v 0) 0 := hc 0 h0J
    rw [hv0, smul_smul, mul_inv_cancel₀ hT.ne', one_smul] at h1
    exact h1.congr_of_eventuallyEq (hread_ev 0 h0J)
  -- chart acceleration at `s = 0`: `x''(0) = (spray(y, w))₂ = -Γ_y(w, w)`. The reading's
  -- derivative equals `T • v` near `0` (`hderiv_read`); differentiating `T • v` picks up a
  -- second factor `T`, and the degree-2 homogeneity of the Christoffel contraction turns
  -- `T² • (spray(y, T⁻¹ w))₂` into `(spray(y, w))₂`, read straight off the geodesic ODE with
  -- no time integration.
  have hacc : HasDerivAt (deriv (fun s : ℝ => extChartAt I p (γ s)))
      ((geodesicSprayCoord (I := I) g p y w).2) 0 := by
    have hc0 : c 0 = y := by
      show (zc (0 * T)).1 = y
      rw [zero_mul, h0]
    have hv0 : v 0 = T⁻¹ • w := by
      show (zc (0 * T)).2 = T⁻¹ • w
      rw [zero_mul, h0]
    have hev : (deriv (fun s : ℝ => extChartAt I p (γ s)))
        =ᶠ[𝓝 (0 : ℝ)] (fun s => T • v s) := by
      filter_upwards [hJopen.mem_nhds h0J] with s hs
      exact hderiv_read s hs
    have hTv : HasDerivAt (fun s : ℝ => T • v s)
        (T • (T • (- chartChristoffelContraction (I := I) g p (v 0) (v 0) (c 0)))) 0 :=
      (hv 0 h0J).const_smul T
    have hval : (T • (T • (- chartChristoffelContraction (I := I) g p (v 0) (v 0) (c 0))))
        = (geodesicSprayCoord (I := I) g p y w).2 := by
      have hTne : T ≠ 0 := hT.ne'
      rw [hc0, hv0]
      simp only [geodesicSprayCoord_def]
      rw [chartChristoffelContraction_smul_smul (I := I) g p T⁻¹ w y,
        smul_neg, smul_neg, smul_smul, smul_smul,
        show (T * T) * (T⁻¹ * T⁻¹) = 1 from by field_simp, one_smul]
    rw [hval] at hTv
    exact hTv.congr_of_eventuallyEq hev
  exact ⟨hγ0, hγcont.mono h01J, hgeo.mono h01J,
    fun s hs => ⟨hγsrc s (h01J hs), hread s (h01J hs)⟩, hvel, hacc⟩

set_option maxHeartbeats 1000000 in
/-- **Math.** **The pair map of the exponential is strictly differentiable at the
zero section, with derivative the unipotent shear `(a, b) ↦ (a, a + b)`**
(do Carmo Ch. 3, proof of Theorem 3.7: `dF_{(p,0)} = [[I, 0], [I, I]]`). Here
the pair map is realized on the chart of `p` as
`G(y, w) = (y, (Z(y, T⁻¹ • w) T)₁)`, where `Z` is the uniform local flow of the
chart-`p` coordinate spray and `T` is a short Picard time: by the degree-2
homogeneity of the spray, `(Z(y, T⁻¹ • w) T)₁` is the chart reading of the
time-`1` geodesic value `exp_q(v)` for the base point `q = φ_p⁻¹(y)` and the
velocity with chart-`p` coordinate `w` (`isGeodesicOn_uniform_flow_segment`).

The derivative is computed exactly as for `d(exp_p)_0 = id`
(`exists_hasStrictFDerivAt_extChartAt_expMap`): the flow is strictly
differentiable in its full initial condition `(y, u) ∈ E × E` at the
equilibrium, with derivative the solution `D = const + ramp ∘ A` of the
variational equation for the nilpotent linearization `A(u, w) = (w, 0)`;
composing with the rescaling `(y, w) ↦ (y, T⁻¹ • w)` and evaluating at time `T`
gives `(a, b) ↦ a + b` in the position component. The base-point slot, frozen
in `StrictDerivative.lean`, is kept free — that is the only difference. -/
theorem exists_pairMap_hasStrictFDerivAt (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E), 0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      (∀ t ∈ Icc (-ε) ε, Z ((extChartAt I p p, (0 : E)) : E × E) t =
        ((extChartAt I p p, (0 : E)) : E × E)) ∧
      HasStrictFDerivAt
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        ((ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
        ((extChartAt I p p, (0 : E)) : E × E) := by
  classical
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip, hZzero, hmax⟩ :=
    exists_uniform_geodesic_flow (I := I) g p
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set F : E × E → E × E := fun ζ => geodesicSprayCoord (I := I) g p ζ.1 ζ.2 with hFdef
  set A : E × E →L[ℝ] E × E :=
    (ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E) with hAdef
  have hA2 : A.comp A = 0 := sprayLinearization_comp_self
  have hfd : fderiv ℝ F z₀ = A :=
    fderiv_geodesicSprayCoord_equilibrium (I := I) g p
  -- the short Picard time
  set T : ℝ := min (ε / 2) (1 / (2 * (‖A‖ + 1))) with hTdef
  have hT : 0 < T := lt_min (by positivity) (by positivity)
  have hTε : T < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hTA : T * ‖A‖ < 1 := by
    have h1 : T ≤ 1 / (2 * (‖A‖ + 1)) := min_le_right _ _
    have h2 : (0 : ℝ) < 2 * (‖A‖ + 1) := by positivity
    have h3 : T * ‖A‖ ≤ (1 / (2 * (‖A‖ + 1))) * ‖A‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg A)
    have h4 : (1 / (2 * (‖A‖ + 1))) * (2 * (‖A‖ + 1)) = 1 :=
      one_div_mul_cancel (ne_of_gt h2)
    nlinarith [norm_nonneg A]
  have hIccTsub : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := fun t ht =>
    ⟨le_trans (neg_nonpos.mpr hε.le) ht.1, ht.2.trans hTε.le⟩
  set tT : Set.Icc (0 : ℝ) T := ⟨T, ⟨hT.le, le_rfl⟩⟩ with htTdef
  -- the solution family on `C([0,T], E × E)`
  set σ : E × E → C(Set.Icc (0 : ℝ) T, E × E) := fun x =>
    if hx : x ∈ closedBall z₀ r then
      ⟨fun t => Z x t.1, by
        have hcont : ContinuousOn (Z x) (Icc (-ε) ε) := fun s hs =>
          ((hflow x hx).2.1 s hs).continuousWithinAt
        exact hcont.comp_continuous continuous_subtype_val
          fun t => hIccTsub t.2⟩
    else ContinuousMap.const _ z₀ with hσdef
  have hσ_ball : ∀ x, x ∈ closedBall z₀ r → ∀ t : Set.Icc (0 : ℝ) T,
      σ x t = Z x t.1 := by
    intro x hx t
    simp only [hσdef, dif_pos hx]
    rfl
  have hσ0 : σ z₀ = ContinuousMap.const _ z₀ := by
    refine ContinuousMap.ext fun t => ?_
    rw [hσ_ball z₀ (mem_closedBall_self hr.le) t, ContinuousMap.const_apply]
    exact hZzero t.1 (hIccTsub t.2)
  have hσc : ContinuousAt σ z₀ := by
    have hlips : LipschitzOnWith L σ (closedBall z₀ r) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [ContinuousMap.dist_le (mul_nonneg L.coe_nonneg dist_nonneg)]
      intro t
      rw [hσ_ball x hx t, hσ_ball y hy t]
      exact (hLip t.1 (hIccTsub t.2)).dist_le_mul x hx y hy
    exact (hlips.continuousOn.continuousWithinAt
      (mem_closedBall_self hr.le)).continuousAt (closedBall_mem_nhds z₀ hr)
  -- differentiability data for the spray near the equilibrium
  have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  have hmemz₀ : z₀ ∈ (extChartAt I p).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target p, mem_univ _⟩
  have hFs : ContDiffOn ℝ ∞ F ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    contDiffOn_geodesicSprayCoord_prod (I := I) g p
  obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.isOpen_iff.mp hopen z₀ hmemz₀
  have hd : ∀ x ∈ ball z₀ ρ', HasFDerivAt F (fderiv ℝ F x) x := fun x hx =>
    ((hFs.contDiffAt (hopen.mem_nhds (hρ'sub hx))).differentiableAt
      (by simp)).hasFDerivAt
  have hc : ContinuousAt (fderiv ℝ F) z₀ :=
    (hFs.continuousOn_fderiv_of_isOpen hopen (by exact_mod_cast le_top)).continuousAt
      (hopen.mem_nhds hmemz₀)
  have heq : F z₀ = 0 := geodesicSprayCoord_zero_velocity (I := I) g p _
  have hTL : T * ‖fderiv ℝ F z₀‖ < 1 := by rw [hfd]; exact hTA
  -- the flow solutions satisfy the Picard integral equation
  have hσres : ∀ᶠ x in 𝓝 z₀, picardResidual hT.le F (x, σ x) = 0 := by
    filter_upwards [ball_mem_nhds z₀ hr] with x hx
    have hx' : x ∈ closedBall z₀ r := ball_subset_closedBall hx
    obtain ⟨h0, hdZ, hmemZ⟩ := hflow x hx'
    exact picardResidual_eq_zero_of_hasDerivWithinAt hT hFs.continuousOn h0
      (fun t ht => hmemZ t (hIccTsub ht))
      (fun t ht => (hdZ t (hIccTsub ht)).mono hIccTsub)
      (σ x) (fun t => hσ_ball x hx' t)
  -- the explicit derivative from the nilpotent linearization
  set D : E × E →L[ℝ] C(Set.Icc (0 : ℝ) T, E × E) :=
    ContinuousLinearMap.const ℝ (Set.Icc (0 : ℝ) T) + (linearRamp hT.le).comp A
    with hDdef
  have hD : ∀ v : E × E, D v - intervalPrimitive hT.le
      (postcomp (fderiv ℝ F z₀) (D v)) = ContinuousMap.const _ v := by
    intro v
    rw [hfd]
    exact sub_intervalPrimitive_postcomp_ramp hT.le hA2 v
  -- strict differentiability of the flow in its initial condition
  have hmain : HasStrictFDerivAt σ D z₀ :=
    hasStrictFDerivAt_of_picardResidual hT hρ'pos heq hd hc hTL hσ0 hσc hσres hD
  have heval : HasStrictFDerivAt (fun y => σ y tT)
      ((ContinuousMap.evalCLM ℝ tT).comp D) z₀ :=
    (ContinuousMap.evalCLM ℝ tT).hasStrictFDerivAt.comp z₀ hmain
  have hfstσ : HasStrictFDerivAt (fun y => (σ y tT).1)
      ((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)) z₀ :=
    (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.comp z₀ heval
  -- the rescaling of the velocity slot, keeping the base slot free
  set ι₂ : E × E → E × E := fun x => ((x.1 : E), T⁻¹ • x.2) with hι₂def
  set Dι₂ : E × E →L[ℝ] E × E :=
    (ContinuousLinearMap.fst ℝ E E).prod
      (T⁻¹ • ContinuousLinearMap.snd ℝ E E) with hDι₂def
  have hι₂ : HasStrictFDerivAt ι₂ Dι₂ z₀ := by
    have : HasStrictFDerivAt (fun x : E × E => Dι₂ x) Dι₂ z₀ :=
      Dι₂.hasStrictFDerivAt
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    show ι₂ x = Dι₂ x
    rw [hι₂def, hDι₂def]
    rfl
  have hι₂0 : ι₂ z₀ = z₀ := by
    rw [hι₂def, hz₀def]
    show ((extChartAt I p p : E), T⁻¹ • (0 : E)) = (extChartAt I p p, (0 : E))
    rw [smul_zero]
  -- strict derivative of the σ-composite pair map
  have hcompσ : HasStrictFDerivAt (fun x : E × E => (σ (ι₂ x) tT).1)
      (((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂) z₀ := by
    have hfstσ' : HasStrictFDerivAt (fun y => (σ y tT).1)
        ((ContinuousLinearMap.fst ℝ E E).comp
          ((ContinuousMap.evalCLM ℝ tT).comp D)) (ι₂ z₀) := by
      rw [hι₂0]; exact hfstσ
    exact hfstσ'.comp z₀ hι₂
  have hGpair : HasStrictFDerivAt
      (fun x : E × E => ((x.1 : E), (σ (ι₂ x) tT).1))
      ((ContinuousLinearMap.fst ℝ E E).prod
        ((((ContinuousLinearMap.fst ℝ E E).comp
          ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂))) z₀ :=
    (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.prodMk hcompσ
  -- the total derivative is the unipotent shear
  have hDtot : ((ContinuousLinearMap.fst ℝ E E).prod
      ((((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂)))
      = (ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)) := by
    refine ContinuousLinearMap.ext fun q => ?_
    obtain ⟨a, b⟩ := q
    refine Prod.ext rfl ?_
    show ((D (Dι₂ ((a, b) : E × E))) tT).1 = a + b
    have hval : Dι₂ ((a, b) : E × E) = ((a, T⁻¹ • b) : E × E) := by
      rw [hDι₂def]
      rfl
    rw [hval]
    have hDval : D (((a, T⁻¹ • b)) : E × E)
        = ContinuousMap.const _ (((a, T⁻¹ • b)) : E × E)
          + linearRamp hT.le ((((T⁻¹ • b : E), (0 : E))) : E × E) := rfl
    rw [hDval]
    show ((((a, T⁻¹ • b)) : E × E)
      + (T : ℝ) • ((((T⁻¹ • b : E), (0 : E))) : E × E)).1 = a + b
    show a + (T : ℝ) • (T⁻¹ • b) = a + b
    rw [smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
  rw [hDtot] at hGpair
  -- pass from the σ-composite to the flow composite
  have hev : (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
      =ᶠ[𝓝 z₀] (fun x : E × E => ((x.1 : E), (σ (ι₂ x) tT).1)) := by
    have hι₂cont : Continuous ι₂ := by
      rw [hι₂def]
      exact continuous_fst.prodMk (continuous_snd.const_smul T⁻¹)
    have hball : closedBall z₀ r ∈ 𝓝 (ι₂ z₀) := by
      rw [hι₂0]
      exact closedBall_mem_nhds z₀ hr
    filter_upwards [hι₂cont.continuousAt.preimage_mem_nhds hball] with x hx
    have hx' : ι₂ x ∈ closedBall z₀ r := hx
    refine Prod.ext rfl ?_
    show (Z ((x.1, T⁻¹ • x.2) : E × E) T).1 = (σ (ι₂ x) tT).1
    rw [hσ_ball _ hx' tT]
  exact ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hZzero,
    hGpair.congr_of_eventuallyEq hev.symm⟩

/-- **Math.** **Totally normal neighborhoods** (do Carmo Ch. 3, Theorem 3.7, in
the intrinsic/uniform-chart form). For every `p ∈ M` there are an open
neighborhood `W ∋ p` inside the chart at `p`, a radius `δ > 0`, a time scale
`T > 0` and a local geodesic flow `Z` of the chart-`p` spray such that:

* **(normal balls at every center)** for every `q ∈ W` and every chart
  velocity `w` with `‖w‖ < δ`, the rescaled flow segment
  `γ(s) = φ_p⁻¹((Z(φ_p(q), T⁻¹ • w)(sT))₁)` is a continuous curve on `[0, 1]`
  starting at `q`, satisfying the intrinsic geodesic equation
  (`IsGeodesicOn g γ (Icc 0 1)`), staying in the chart at `p` (where its
  reading is the flow line), with chart velocity `w` at `s = 0` — this is the
  geodesic `s ↦ exp_q(s v)` for the velocity `v ∈ T_qM` with chart-`p`
  coordinate `w`;
* **(`exp_q(B_δ) ⊇ W`, with injectivity)** any two points `q, m ∈ W` are
  joined by such a segment: there is a parameter `w` with `‖w‖ < δ` whose
  segment ends at `m` at time `1`, and `w` is the *unique* such parameter in
  the `δ`-ball.

The statement is uniform in `q` because velocities are coordinatized in the
single chart at `p`; the chart-`q`-anchored exponential `expMap g q` cannot
support a `q`-uniform radius, since the atlas charts at nearby `q` have no
common source size. do Carmo's `F(q, v) = (q, exp_q v)` becomes the pair map
`G(y, w) = (y, (Z(y, T⁻¹ • w) T)₁)`; its strict derivative at `(φ_p(p), 0)` is
the invertible shear `(a, b) ↦ (a, a + b)`
(`exists_pairMap_hasStrictFDerivAt`), the inverse function theorem makes `G` a
homeomorphism near `(φ_p(p), 0)`, and a square neighborhood
`W̃ × W̃ ⊆ G(ball × ball)` yields `W = φ_p⁻¹(W̃)` and the joining parameters. -/
theorem exists_totallyNormal_neighborhood (g : RiemannianMetric I M) (p : M) :
    ∃ (W : Set M) (δ T : ℝ) (Z : E × E → ℝ → E × E),
      IsOpen W ∧ p ∈ W ∧ W ⊆ (chartAt H p).source ∧ 0 < δ ∧ 0 < T ∧
      (∀ q ∈ W, ∀ w : E, ‖w‖ < δ →
        ∃ γ : ℝ → M,
          (∀ s : ℝ, γ s = (extChartAt I p).symm
            ((Z ((extChartAt I p q, T⁻¹ • w) : E × E) (s * T)).1)) ∧
          γ 0 = q ∧
          ContinuousOn γ (Icc 0 1) ∧
          IsGeodesicOn (I := I) g γ (Icc 0 1) ∧
          (∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ (chartAt H p).source ∧
            extChartAt I p (γ s) =
              (Z ((extChartAt I p q, T⁻¹ • w) : E × E) (s * T)).1) ∧
          HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 ∧
          HasDerivAt (deriv (fun s : ℝ => extChartAt I p (γ s)))
            (geodesicSprayCoord (I := I) g p (extChartAt I p q) w).2 0) ∧
      (∀ q ∈ W, ∀ m ∈ W, ∃ w : E, ‖w‖ < δ ∧
        (extChartAt I p).symm
          ((Z ((extChartAt I p q, T⁻¹ • w) : E × E) T).1) = m ∧
        ∀ w' : E, ‖w'‖ < δ →
          (extChartAt I p).symm
            ((Z ((extChartAt I p q, T⁻¹ • w') : E × E) T).1) = m →
          w' = w) := by
  classical
  obtain ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hzero, hstrict⟩ :=
    exists_pairMap_hasStrictFDerivAt (I := I) g p
  set y₀ : E := extChartAt I p p with hy₀def
  set x₀ : E × E := ((y₀, (0 : E)) : E × E) with hx₀def
  set G : E × E → E × E :=
    fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) with hGdef
  have hTIcc : T ∈ Icc (-ε) ε := ⟨by linarith [hT, hε], hTε.le⟩
  -- the shear as a continuous linear equivalence
  set shear : (E × E) ≃L[ℝ] (E × E) := ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.snd ℝ E E) - (ContinuousLinearMap.fst ℝ E E)))
    (fun x => by
      simp [ContinuousLinearMap.prod_apply])
    (fun x => by
      simp [ContinuousLinearMap.prod_apply]) with hsheardef
  have hshear_coe : (shear : (E × E) →L[ℝ] E × E)
      = (ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)) := rfl
  have hstrict' : HasStrictFDerivAt G
      ((shear : (E × E) ≃L[ℝ] E × E) : (E × E) →L[ℝ] E × E) x₀ := by
    rw [hshear_coe]
    exact hstrict
  -- the inverse function theorem: `G` is a homeomorphism near `x₀`
  set ho := hstrict'.toOpenPartialHomeomorph G with hodef
  have hsource : x₀ ∈ ho.source := hstrict'.mem_toOpenPartialHomeomorph_source
  have hcoe : ⇑ho = G := hstrict'.toOpenPartialHomeomorph_coe
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.isOpen_iff.mp ho.open_source x₀ hsource
  -- the product-ball domain: radii small enough for the IFT source and the flow
  set δ₁ : ℝ := min ρ₂ r with hδ₁def
  set δ : ℝ := min ρ₂ (T * r) with hδdef
  have hδ₁pos : 0 < δ₁ := lt_min hρ₂ hr
  have hδpos : 0 < δ := lt_min hρ₂ (by positivity)
  set B : Set (E × E) := ball y₀ δ₁ ×ˢ ball (0 : E) δ with hBdef
  have hBsource : B ⊆ ho.source := by
    intro x hx
    refine hρ₂sub ?_
    rw [mem_ball, hx₀def, Prod.dist_eq]
    exact max_lt (lt_of_lt_of_le hx.1 (min_le_left _ _))
      (lt_of_lt_of_le hx.2 (min_le_left _ _))
  have hBflow : ∀ x ∈ B, ((x.1, T⁻¹ • x.2) : E × E) ∈ closedBall x₀ r := by
    intro x hx
    rw [mem_closedBall, hx₀def, Prod.dist_eq]
    have hx1 : dist x.1 y₀ ≤ r :=
      le_of_lt (lt_of_lt_of_le (mem_ball.mp hx.1) (min_le_right _ _))
    refine max_le hx1 ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
    have hx2' : ‖x.2‖ < δ := by
      have := mem_ball.mp hx.2
      rwa [dist_zero_right] at this
    have hx2 : ‖x.2‖ < T * r := lt_of_lt_of_le hx2' (min_le_right _ _)
    rw [inv_mul_le_iff₀ hT]
    linarith [hx2]
  -- `G x₀ = (y₀, y₀)`
  have hGx₀ : G x₀ = ((y₀, y₀) : E × E) := by
    rw [hGdef]
    show ((x₀.1 : E), (Z ((x₀.1, T⁻¹ • x₀.2) : E × E) T).1) = ((y₀, y₀) : E × E)
    have h1 : ((x₀.1, T⁻¹ • x₀.2) : E × E) = x₀ := by
      rw [hx₀def]
      show ((y₀, T⁻¹ • (0 : E)) : E × E) = ((y₀, (0 : E)) : E × E)
      rw [smul_zero]
    rw [h1]
    have h2 : Z x₀ T = x₀ := hzero T hTIcc
    rw [h2]
  -- `G` maps neighborhoods of `x₀` onto neighborhoods of `(y₀, y₀)`
  have hmapnhds : Filter.map G (𝓝 x₀) = 𝓝 ((y₀, y₀) : E × E) := by
    have := hstrict'.map_nhds_eq_of_equiv
    rwa [hGx₀] at this
  have hB𝓝 : B ∈ 𝓝 x₀ := by
    rw [hBdef, hx₀def]
    exact prod_mem_nhds (ball_mem_nhds _ hδ₁pos) (ball_mem_nhds _ hδpos)
  have hGB : G '' B ∈ 𝓝 ((y₀, y₀) : E × E) := by
    rw [← hmapnhds]
    exact image_mem_map hB𝓝
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hGB
  set η' : ℝ := min η δ₁ with hη'def
  have hη'pos : 0 < η' := lt_min hη hδ₁pos
  -- the totally normal neighborhood
  set W : Set M := (chartAt H p).source ∩ extChartAt I p ⁻¹' ball y₀ η' with hWdef
  have hWopen : IsOpen W := by
    have hcont : ContinuousOn (extChartAt I p) (chartAt H p).source := by
      have := continuousOn_extChartAt (I := I) p
      rwa [extChartAt_source] at this
    exact hcont.isOpen_inter_preimage (chartAt H p).open_source isOpen_ball
  have hpW : p ∈ W := by
    refine ⟨mem_chart_source H p, ?_⟩
    show extChartAt I p p ∈ ball y₀ η'
    rw [hy₀def]
    exact mem_ball_self hη'pos
  have hWsub : W ⊆ (chartAt H p).source := inter_subset_left
  -- chart membership facts for points of `W`
  have hWchart : ∀ q ∈ W, extChartAt I p q ∈ ball y₀ η' := fun q hq => hq.2
  have hWsrc : ∀ q ∈ W, q ∈ (extChartAt I p).source := by
    intro q hq
    rw [extChartAt_source]
    exact hWsub hq
  -- flow membership for pairs from `W` and the `δ`-ball
  have hWflow : ∀ q ∈ W, ∀ w : E, ‖w‖ < δ →
      ((extChartAt I p q, T⁻¹ • w) : E × E) ∈ closedBall x₀ r := by
    intro q hq w hw
    refine hBflow ((extChartAt I p q, w)) ?_
    constructor
    · exact mem_ball.mpr
        (lt_of_lt_of_le (mem_ball.mp (hWchart q hq)) (min_le_right _ _))
    · rw [mem_ball, dist_zero_right]
      exact hw
  refine ⟨W, δ, T, Z, hWopen, hpW, hWsub, hδpos, hT, ?_, ?_⟩
  · -- descent: normal balls at every center of `W`
    intro q hq w hw
    obtain ⟨hγ0, hγcont, hγgeo, hγchart, hγvel, hγacc⟩ :=
      isGeodesicOn_uniform_flow_segment (I := I) g p hT hTε hflow
        (hWflow q hq w hw)
    refine ⟨fun s : ℝ => (extChartAt I p).symm
      ((Z ((extChartAt I p q, T⁻¹ • w) : E × E) (s * T)).1),
      fun s => rfl, ?_, hγcont, hγgeo, hγchart, hγvel, hγacc⟩
    rw [hγ0]
    exact (extChartAt I p).left_inv (hWsrc q hq)
  · -- covering with unique parameter
    intro q hq m hm
    set y : E := extChartAt I p q with hydef
    set u : E := extChartAt I p m with hudef
    have hyu : ((y, u) : E × E) ∈ ball ((y₀, y₀) : E × E) η := by
      rw [mem_ball, Prod.dist_eq]
      exact max_lt
        (lt_of_lt_of_le (mem_ball.mp (hWchart q hq)) (min_le_left _ _))
        (lt_of_lt_of_le (mem_ball.mp (hWchart m hm)) (min_le_left _ _))
    obtain ⟨x, hxB, hGx⟩ := hηsub hyu
    have hx1 : x.1 = y := congrArg Prod.fst hGx
    have hw : ‖x.2‖ < δ := by
      have := mem_ball.mp hxB.2
      rwa [dist_zero_right] at this
    have hee : (Z ((y, T⁻¹ • x.2) : E × E) T).1 = u := by
      have h2 : (Z ((x.1, T⁻¹ • x.2) : E × E) T).1 = u := congrArg Prod.snd hGx
      rwa [hx1] at h2
    refine ⟨x.2, hw, ?_, ?_⟩
    · rw [hee, hudef]
      exact (extChartAt I p).left_inv (hWsrc m hm)
    · -- uniqueness of the parameter in the `δ`-ball
      intro w' hw' hm'
      -- the endpoint reading of the `w'`-segment equals `u`
      have hmemw' : ((y, T⁻¹ • w') : E × E) ∈ closedBall x₀ r :=
        hWflow q hq w' hw'
      have hconf' := (hflow _ hmemw').2.2 T hTIcc
      have happ : (Z ((y, T⁻¹ • w') : E × E) T).1 = u := by
        have hrinv : extChartAt I p
            ((extChartAt I p).symm ((Z ((y, T⁻¹ • w') : E × E) T).1))
            = (Z ((y, T⁻¹ • w') : E × E) T).1 :=
          (extChartAt I p).right_inv hconf'.1
        rw [hm'] at hrinv
        rw [← hrinv, hudef]
      -- both parameters solve `G(y, ·) = (y, u)`; injectivity concludes
      have hyB : y ∈ ball y₀ δ₁ := mem_ball.mpr
        (lt_of_lt_of_le (mem_ball.mp (hWchart q hq)) (min_le_right _ _))
      have hxw'B : ((y, w') : E × E) ∈ B := by
        refine ⟨hyB, ?_⟩
        rwa [mem_ball, dist_zero_right]
      have hGeq : G ((y, w') : E × E) = G x := by
        rw [hGx]
        show ((y : E), (Z ((y, T⁻¹ • w') : E × E) T).1) = ((y, u) : E × E)
        rw [happ]
      have hinj := ho.injOn (hBsource hxw'B) (hBsource hxB)
      have hxeq : ((y, w') : E × E) = x := by
        apply hinj
        show ho ((y, w') : E × E) = ho x
        rw [hcoe]
        exact hGeq
      have := congrArg Prod.snd hxeq
      simpa using this

/-- **Math.** **The pair map is `C¹` on a ball around the zero section** (do Carmo
Ch. 3, Theorem 3.7, the regularity of `F(q, v) = (q, exp_q v)`; the joint
analogue of `exp_p`-regularity on a ball, `lem:dc-ch3-2-9-c1ball`). There are a
uniform flow `Z` of the chart-`p` spray and `T < ε` such that the pair map
`G(y, w) = (y, (Z(y, T⁻¹ • w) T)₁)` is `C¹` on the open set of admissible
initial conditions, and, slicing at each base point `y`, the chart exponential
`w ↦ (Z(y, T⁻¹ • w) T)₁` at the base point `φ_p⁻¹(y)` is `C¹` on the uniform
velocity ball of radius `T·r`. The strict derivative of the flow in its full
initial condition exists at every admissible point
(`exists_uniform_geodesic_flow_hasStrictFDerivAt`), and pointwise strict
differentiability on an open set upgrades to `C¹`
(`contDiffOn_one_of_forall_hasStrictFDerivAt`). -/
theorem exists_pairMap_contDiffOn (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E), 0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      ContDiffOn ℝ 1
        (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        {x : E × E | ((x.1, T⁻¹ • x.2) : E × E) ∈
          ball ((extChartAt I p p, (0 : E)) : E × E) r} ∧
      (∀ y ∈ ball (extChartAt I p p) r,
        ContDiffOn ℝ 1 (fun w : E => (Z ((y, T⁻¹ • w) : E × E) T).1)
          (ball (0 : E) (T * r))) := by
  classical
  obtain ⟨r, ε, T, Z, L, σ, hT, hr, hε, hTε, hflow, hLip, hmax, hσZ, hD⟩ :=
    exists_uniform_geodesic_flow_hasStrictFDerivAt (I := I) g p
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set tT : Set.Icc (0 : ℝ) T := ⟨T, ⟨hT.le, le_rfl⟩⟩ with htTdef
  set ι₂ : E × E → E × E := fun x => ((x.1 : E), T⁻¹ • x.2) with hι₂def
  set Dι₂ : E × E →L[ℝ] E × E :=
    (ContinuousLinearMap.fst ℝ E E).prod
      (T⁻¹ • ContinuousLinearMap.snd ℝ E E) with hDι₂def
  have hι₂eq : ι₂ = fun x : E × E => Dι₂ x := by
    funext x
    rw [hι₂def, hDι₂def]
    rfl
  have hι₂cont : Continuous ι₂ := by
    rw [hι₂eq]
    exact Dι₂.continuous
  set G : E × E → E × E :=
    fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) with hGdef
  set S : Set (E × E) := {x : E × E | ι₂ x ∈ ball z₀ r} with hSdef
  have hSopen : IsOpen S := isOpen_ball.preimage hι₂cont
  -- pointwise strict differentiability of `G` on `S`
  have key : ∀ x : E × E, ∃ D' : E × E →L[ℝ] E × E,
      x ∈ S → HasStrictFDerivAt G D' x := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨D, A₀, hA₀, hDeq, hDstrict⟩ := hD (ι₂ x) hx
      refine ⟨(ContinuousLinearMap.fst ℝ E E).prod
        ((((ContinuousLinearMap.fst ℝ E E).comp
          ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂)), fun _ => ?_⟩
      -- the σ-composite is strictly differentiable at `x`
      have heval : HasStrictFDerivAt (fun y => σ y tT)
          ((ContinuousMap.evalCLM ℝ tT).comp D) (ι₂ x) :=
        (ContinuousMap.evalCLM ℝ tT).hasStrictFDerivAt.comp (ι₂ x) hDstrict
      have hfstσ : HasStrictFDerivAt (fun y => (σ y tT).1)
          ((ContinuousLinearMap.fst ℝ E E).comp
            ((ContinuousMap.evalCLM ℝ tT).comp D)) (ι₂ x) :=
        (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.comp (ι₂ x) heval
      have hι₂strict : HasStrictFDerivAt ι₂ Dι₂ x := by
        rw [hι₂eq]
        exact Dι₂.hasStrictFDerivAt
      have hcompσ : HasStrictFDerivAt (fun x' : E × E => (σ (ι₂ x') tT).1)
          (((ContinuousLinearMap.fst ℝ E E).comp
            ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂) x :=
        hfstσ.comp x hι₂strict
      have hGpair : HasStrictFDerivAt
          (fun x' : E × E => ((x'.1 : E), (σ (ι₂ x') tT).1))
          ((ContinuousLinearMap.fst ℝ E E).prod
            ((((ContinuousLinearMap.fst ℝ E E).comp
              ((ContinuousMap.evalCLM ℝ tT).comp D)).comp Dι₂))) x :=
        (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.prodMk hcompσ
      -- pass to the flow composite near `x`
      have hev : G =ᶠ[𝓝 x]
          (fun x' : E × E => ((x'.1 : E), (σ (ι₂ x') tT).1)) := by
        filter_upwards [hι₂cont.continuousAt.preimage_mem_nhds
          (isOpen_ball.mem_nhds hx)] with x' hx'
        have hx'' : ι₂ x' ∈ closedBall z₀ r := ball_subset_closedBall hx'
        refine Prod.ext rfl ?_
        show (Z ((x'.1, T⁻¹ • x'.2) : E × E) T).1 = (σ (ι₂ x') tT).1
        rw [hσZ _ hx'' tT]
      exact hGpair.congr_of_eventuallyEq hev.symm
    · exact ⟨0, fun h => absurd h hx⟩
  choose D' hD' using key
  have hGC1 : ContDiffOn ℝ 1 G S :=
    contDiffOn_one_of_forall_hasStrictFDerivAt hSopen fun x hx => hD' x hx
  refine ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hGC1, ?_⟩
  -- slice at a fixed base point `y`
  intro y hy
  have hemb : ContDiff ℝ 1 (fun w : E => ((y, w) : E × E)) :=
    contDiff_const.prodMk contDiff_id
  have hmaps : MapsTo (fun w : E => ((y, w) : E × E)) (ball (0 : E) (T * r)) S := by
    intro w hw
    show ((y, T⁻¹ • w) : E × E) ∈ ball z₀ r
    rw [mem_ball, hz₀def, Prod.dist_eq]
    refine max_lt (mem_ball.mp hy) ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
    have hw' : ‖w‖ < T * r := by
      have := mem_ball.mp hw
      rwa [dist_zero_right] at this
    rw [inv_mul_lt_iff₀ hT]
    linarith [hw']
  have hcomp : ContDiffOn ℝ 1 (fun w : E => G ((y, w) : E × E))
      (ball (0 : E) (T * r)) :=
    hGC1.comp hemb.contDiffOn hmaps
  have hsnd : ContDiffOn ℝ 1 (fun w : E => (G ((y, w) : E × E)).2)
      (ball (0 : E) (T * r)) := contDiff_snd.comp_contDiffOn hcomp
  exact hsnd

end Exponential

end Riemannian
