import PetersenLib.Ch05.GeodesicCompleteness
import PetersenLib.Ch05.TangentCompactness
import PetersenLib.Ch05.InjectivityRadius
import PetersenLib.Riemannian.Exponential.TotallyNormalCInfty

/-!
# Petersen Ch. 5, §5.5 — a uniform injectivity radius on a compact set

`compactSet_uniformInjectivityRadius` (`cor:pet-ch5-uniform-injectivity-radius-compact`,
Petersen Cor. 5.5.2): for a compact `K ⊆ M` there is a single `ε > 0` such that for
**every** `q ∈ K` the exponential map `exp_q` is defined on the whole `g`-metric ball
`{v | |v|_g < ε}` of `T_qM` and is **injective** there.

## What this file provides

* `isGeodesicOn_flow_window` — the flow-segment/geodesic converter of
  `Exponential.isGeodesicOn_uniform_flow_segment` restated on the **open** time window
  `Ioo (-(ε/T)) (ε/T)`, which strictly contains `[0, 1]`.
* `uniform_intrinsic_domain` — the "defined" half: a uniform `ε > 0` over a compact `K`
  with `1 ∈ geodesicMaximalDomain g q v` for every `q ∈ K` and every `|v|_g < ε`.
* `exists_local_uniformInjOn` — the local injectivity half: around every `x ∈ M` an open
  `W ∋ x` and `ε > 0` with `v ↦ exp_q v` injective on the `g`-ball of radius `ε`,
  **uniformly for all `q ∈ W`**.
* `compactSet_uniformInjectivityRadius` — the headline corollary.

## What this file does NOT provide

The corollary is stated with the **intrinsic** moving-foot maximal geodesic
(`geodesicMaximalDomain` / `geodesicMaximalCurve`), *not* with `PetersenLib.expDomain` /
`PetersenLib.injectivityRadius`.  This is deliberate and load-bearing:
`expDomain g p = {v | 1 ∈ maximalGeodesicInterval g p v}` is defined by integral curves of
`geodesicVectorFieldChart g p`, the geodesic field of the **single chart at `p`**, which
Mathlib's trivialization makes `0` off `(chartAt H p).source`.  So an `expDomain` geodesic
can never leave the chart at its own initial point, and `expDomain g p` is bounded by the
chart at `p`.  Chart sources admit **no uniform lower bound** over a compact set (rescale
the charts of a restricted-identity atlas on `ℝ`), so Cor. 5.5.2 stated at `expDomain` /
`injectivityRadius` is **false**, not merely unproven.  The vendored engine's own authors
record the same defect at `Riemannian/Geodesic/HopfRinow.lean:37-43`
(`maximalGeodesicInterval g p v = Set.univ` fails for the round circle).  The intrinsic
`geodesicMaximalDomain` used here is a genuinely different — and correct — notion.

This file proves `exp_q` is **defined and injective** on a uniform `g`-ball.  It does NOT
prove the full "is a diffeomorphism onto its image" of Petersen's statement: the
smoothness and smooth-inverse clauses are not formalized here.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## The flow segment on its full open time window -/

/-- **Math.** Petersen Ch. 5 (§5.5, flow-window form of do Carmo's Thm. 3.7 package):
the time-rescaled projected flow line `γ(s) = φ_p⁻¹((Z(y, T⁻¹·w)(sT))₁)` is an intrinsic
geodesic on the **whole open window** `(-ε/T, ε/T)`, which strictly contains `[0, 1]`
because `T < ε`.

This is `Exponential.isGeodesicOn_uniform_flow_segment` with its conclusion recorded on the
open window rather than narrowed to `Icc 0 1`.  The open window is essential downstream:
geodesic uniqueness (`geodesic_global_uniqueness`) propagates initial data only across
**open** preconnected time sets, and `Icc 0 1` has interior `Ioo 0 1`, which misses the
time `0` where the initial datum lives.  With only the `Icc 0 1` clause the package curve
cannot be identified with the intrinsic maximal geodesic at all. -/
theorem isGeodesicOn_flow_window
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
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) (Ioo (-(ε / T)) (ε / T)) ∧
    IsGeodesicOn (I := I) g (fun s : ℝ => (extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) (Ioo (-(ε / T)) (ε / T)) ∧
    (∀ s ∈ Ioo (-(ε / T)) (ε / T),
      (extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1) ∈
        (chartAt H p).source ∧
      extChartAt I p
          ((extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) =
        (Z ((y, T⁻¹ • w) : E × E) (s * T)).1) ∧
    HasDerivAt (fun s : ℝ =>
      extChartAt I p
        ((extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1))) w 0 ∧
    (∀ s₀ ∈ Ioo (-(ε / T)) (ε / T), SolvesGeodesicODEAt (I := I) g p
      (fun s : ℝ => (extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) s₀) ∧
    Icc (0 : ℝ) 1 ⊆ Ioo (-(ε / T)) (ε / T) := by
  classical
  obtain ⟨h0, hd, hconf⟩ := hflow _ hmem
  set zc : ℝ → E × E := Z ((y, T⁻¹ • w) : E × E) with hzcdef
  have hdIoo : ∀ t ∈ Ioo (-ε) ε, HasDerivAt zc
      (geodesicSprayCoord (I := I) g p (zc t).1 (zc t).2) t := fun t ht =>
    (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
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
  have hcmem : ∀ s ∈ J, c s ∈ (extChartAt I p).target := fun s hs =>
    (hconf (s * T) (Ioo_subset_Icc_self (hwin s hs))).1
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
    have hmap : MapsTo c J (extChartAt I p).target := fun σ hσ => hcmem σ hσ
    exact ((continuousOn_extChartAt_symm p).comp
      (fun σ hσ => (hccont σ hσ).continuousWithinAt) hmap) s hs
  have hread_ev : ∀ s ∈ J, chartReading (I := I) p γ =ᶠ[𝓝 s] c := by
    intro s hs
    filter_upwards [hJopen.mem_nhds hs] with σ hσ
    exact hread σ hσ
  have hderiv_read : ∀ s ∈ J, deriv (chartReading (I := I) p γ) s = T • v s := by
    intro s hs
    rw [(hread_ev s hs).deriv_eq]
    exact (hc s hs).deriv
  have hsolves : ∀ s₀ ∈ J, SolvesGeodesicODEAt (I := I) g p γ s₀ := by
    intro s₀ hs₀
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
  have hgeo : IsGeodesicOn (I := I) g γ J := fun s₀ hs₀ =>
    (hsolves s₀ hs₀).hasGeodesicEquationAt
      (hγcont.continuousAt (hJopen.mem_nhds hs₀)) (hγsrc s₀ hs₀)
  have h0J : (0 : ℝ) ∈ J := h01J ⟨le_rfl, zero_le_one⟩
  have hγ0 : γ 0 = (extChartAt I p).symm y := by
    have hc0 : c 0 = y := by
      show (zc (0 * T)).1 = y
      rw [zero_mul, h0]
    rw [hγdef]
    show (extChartAt I p).symm (c 0) = (extChartAt I p).symm y
    rw [hc0]
  have hvel : HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 := by
    have hv0 : v 0 = T⁻¹ • w := by
      show (zc (0 * T)).2 = T⁻¹ • w
      rw [zero_mul, h0]
    have h1 : HasDerivAt c (T • v 0) 0 := hc 0 h0J
    rw [hv0, smul_smul, mul_inv_cancel₀ hT.ne', one_smul] at h1
    exact h1.congr_of_eventuallyEq (hread_ev 0 h0J)
  exact ⟨hγ0, hγcont, hgeo, fun s hs => ⟨hγsrc s hs, hread s hs⟩, hvel, hsolves, h01J⟩

/-- **Math.** Petersen Ch. 5 (§5.5): the flow-window curve of `isGeodesicOn_flow_window`,
launched from a foot `q` in the chart at `p` with the fibre coordinate of `v` as its
chart-`p` velocity, is the **intrinsic** solution of the geodesic initial-value problem
`c(0) = q`, `ċ(0) = v` on the open window `(-ε/T, ε/T)`.

The content is the velocity bookkeeping: the flow package reads velocities in the chart at
the *centre* `p`, while `IsGeodesicWithInitialOn` reads them in the chart at the curve's
*own foot* `q`.  The two readings differ by the tangent coordinate change at `q`, which is
exactly what `chartReading_geodesicODE_transfer` supplies along a solution of the geodesic
ODE — and the fibre coordinate `(trivializationAt E (TangentSpace I) p ⟨q, v⟩).2` is by
definition `tangentCoordChange I q p q v`, so the two coordinate changes compose to the
identity and the foot reading is `v` on the nose. -/
theorem isGeodesicWithInitialOn_flow_window
    (g : RiemannianMetric I M) (p : M) {r ε T : ℝ} {Z : E × E → ℝ → E × E}
    (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    {q : M} (hq : q ∈ (chartAt H p).source) (v : TangentSpace I q)
    (hmem : ((extChartAt I p q,
        T⁻¹ • (trivializationAt E (TangentSpace I) p (⟨q, v⟩ : TangentBundle I M)).2) : E × E)
      ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r) :
    IsGeodesicWithInitialOn (I := I) g
      (fun s : ℝ => (extChartAt I p).symm
        ((Z ((extChartAt I p q,
          T⁻¹ • (trivializationAt E (TangentSpace I) p (⟨q, v⟩ : TangentBundle I M)).2) : E × E)
            (s * T)).1))
      (Ioo (-(ε / T)) (ε / T)) 0 q v := by
  classical
  set w : E := (trivializationAt E (TangentSpace I) p (⟨q, v⟩ : TangentBundle I M)).2
    with hw_def
  obtain ⟨hγ0, hγcont, hgeo, hsrc, hvel, hsolves, h01J⟩ :=
    isGeodesicOn_flow_window (I := I) g p hT hTε hflow (y := extChartAt I p q) (w := w) hmem
  set γ : ℝ → M := fun s : ℝ => (extChartAt I p).symm
    ((Z ((extChartAt I p q, T⁻¹ • w) : E × E) (s * T)).1) with hγ_def
  have h0J : (0 : ℝ) ∈ Ioo (-(ε / T)) (ε / T) := h01J ⟨le_rfl, zero_le_one⟩
  have hqsrc_p : q ∈ (extChartAt I p).source := by rw [extChartAt_source I]; exact hq
  have hqsrc_q : q ∈ (extChartAt I q).source := mem_extChartAt_source (I := I) q
  -- the curve starts at `q`
  have hγ0' : γ 0 = q := by
    rw [hγ0]
    exact (extChartAt I p).left_inv hqsrc_p
  -- transfer the initial velocity from the chart at `p` to the chart at the foot `q`
  have hct0 : ContinuousAt γ 0 := hγcont.continuousAt (isOpen_Ioo.mem_nhds h0J)
  have hev : ∀ᶠ s in 𝓝 0, γ s ∈ (extChartAt I p).source ∩ (extChartAt I q).source := by
    refine hct0.eventually_mem ?_
    rw [hγ0']
    exact Filter.inter_mem ((isOpen_extChartAt_source p).mem_nhds hqsrc_p)
      ((isOpen_extChartAt_source q).mem_nhds hqsrc_q)
  obtain ⟨a, ha, heq⟩ := (hsolves 0 h0J).2
  obtain ⟨hev', hvelq, -⟩ := chartReading_geodesicODE_transfer (I := I) g
    hev (hsolves 0 h0J).1 ha heq
  have hφ_eq : w = tangentCoordChange I q p q v := rfl
  have hvel_val : deriv (fun s' => extChartAt I q (γ s')) 0 = (v : E) := by
    rw [hvelq, hvel.deriv, hγ0', hφ_eq,
      tangentCoordChange_comp (I := I) ⟨⟨hqsrc_q, hqsrc_p⟩, hqsrc_q⟩,
      tangentCoordChange_self (I := I) hqsrc_q]
  have hvelv : HasDerivAt (fun s' => extChartAt I q (γ s')) (v : E) 0 := by
    rw [← hvel_val]
    exact hev'.self_of_nhds
  exact ⟨hγcont, hγ0', hvelv, hgeo⟩

/-! ## The local uniform injectivity radius -/

/-- **Math.** Petersen Ch. 5 (`cor:pet-ch5-uniform-injectivity-radius-compact`, local
half): around every `x ∈ M` there are an open `W ∋ x` and a radius `ρ > 0` such that for
**every** `q ∈ W` the exponential map `v ↦ exp_q v` is injective on the `g`-metric ball
`{v ∈ T_qM | |v|_g < ρ}`.  Both `W` and `ρ` are uniform: one radius works simultaneously
for all feet `q ∈ W`.

Proof (do Carmo Ch. 3, Thm. 3.7 / Petersen §5.5): the flow package of
`exists_pairMap_hasStrictFDerivAt_equiv_ball_infty` provides a chart-`x` pair map
`G(y, w) = (y, (Z(y, T⁻¹·w)(T))₁)` which is strictly differentiable at the zero section
`(φ_x x, 0)` with derivative the unipotent shear `(a, b) ↦ (a, a + b)`, a linear
isomorphism; the inverse function theorem therefore makes `G` a homeomorphism — in
particular **injective** — on a ball `B(z₀, ρ₂)`.  Injectivity of `G` at a *fixed* first
coordinate `y = φ_x q` is injectivity of `w ↦ (Z(y, T⁻¹·w)(T))₁`, i.e. of the endpoint of
the geodesic launched from `q` with chart-`x` velocity `w`.

Two conversions turn this into the statement above.  Velocities: `v ↦ w` is the
trivialization fibre coordinate at `x`, a linear isomorphism on `T_qM`, so injectivity in
`w` gives injectivity in `v`.  Radii: the `g`-ball must be pushed inside the *coordinate*
ball `‖w‖ < δ` **uniformly in `q`**, which is exactly the uniform Gram eigenvalue bound
`exists_forall_le_chartMetricInner` on a compact `C ⊆ (chartAt H x).source` — this is why
`W` is cut down to `interior C`, and it is the step that makes `ρ` independent of `q`. -/
theorem exists_local_uniformInjOn (g : RiemannianMetric I M) [T2Space M] (x : M) :
    ∃ (W : Set M) (ρ : ℝ), IsOpen W ∧ x ∈ W ∧ 0 < ρ ∧ ∀ q ∈ W,
      Set.InjOn (fun v : TangentSpace I q => geodesicMaximalCurve (I := I) g q v 1)
        {v : TangentSpace I q | g.metricInner q v v < ρ ^ 2} := by
  classical
  obtain ⟨r, ε, T, ρ₀, Z, hr, hε, hT, hTε, hρ₀, hflow, hZT1, hρ₀sub, hGCinf,
    hstrict, hinv⟩ := exists_pairMap_hasStrictFDerivAt_equiv_ball_infty (I := I) g x
  set y₀ : E := extChartAt I x x with hy₀def
  set z₀ : E × E := ((y₀, (0 : E)) : E × E) with hz₀def
  set G : E × E → E × E :=
    fun z => ((z.1 : E), (Z ((z.1, T⁻¹ • z.2) : E × E) T).1) with hGdef
  -- the strict derivative at the zero section is the unipotent shear, a linear iso
  set shear : (E × E) ≃L[ℝ] E × E := ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)))
    ((ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.snd ℝ E E) - (ContinuousLinearMap.fst ℝ E E)))
    (fun z => by simp [ContinuousLinearMap.prod_apply])
    (fun z => by simp [ContinuousLinearMap.prod_apply]) with hsheardef
  have hshear_coe : (shear : (E × E) →L[ℝ] E × E)
      = (ContinuousLinearMap.fst ℝ E E).prod
          ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E)) := rfl
  have hstrict' : HasStrictFDerivAt G
      ((shear : (E × E) ≃L[ℝ] E × E) : (E × E) →L[ℝ] E × E) z₀ := by
    rw [hshear_coe]
    exact hstrict
  -- the inverse function theorem: `G` is injective near the zero section
  set ho := hstrict'.toOpenPartialHomeomorph G with hodef
  have hsource : z₀ ∈ ho.source := hstrict'.mem_toOpenPartialHomeomorph_source
  have hcoe : ⇑ho = G := hstrict'.toOpenPartialHomeomorph_coe
  obtain ⟨ρ₂, hρ₂, hρ₂sub⟩ := Metric.isOpen_iff.mp ho.open_source z₀ hsource
  have hGinj : Set.InjOn G (ball z₀ ρ₂) := by
    have h := ho.injOn.mono hρ₂sub
    rwa [hcoe] at h
  -- the working coordinate radii
  set δ₁ : ℝ := min ρ₂ r with hδ₁def
  set δ : ℝ := min ρ₂ (T * r) with hδdef
  have hδ₁pos : 0 < δ₁ := lt_min hρ₂ hr
  have hδpos : 0 < δ := lt_min hρ₂ (by positivity)
  set B : Set (E × E) := ball y₀ δ₁ ×ˢ ball (0 : E) δ with hBdef
  have hBball : B ⊆ ball z₀ ρ₂ := by
    intro z hz
    rw [mem_ball, hz₀def, Prod.dist_eq]
    exact max_lt (lt_of_lt_of_le hz.1 (min_le_left _ _))
      (lt_of_lt_of_le hz.2 (min_le_left _ _))
  have hBflow : ∀ z ∈ B, ((z.1, T⁻¹ • z.2) : E × E) ∈ closedBall z₀ r := by
    intro z hz
    rw [mem_closedBall, hz₀def, Prod.dist_eq]
    have hz1 : dist z.1 y₀ ≤ r :=
      le_of_lt (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _))
    refine max_le hz1 ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
    have hz2' : ‖z.2‖ < δ := by
      have := mem_ball.mp hz.2
      rwa [dist_zero_right] at this
    have hz2 : ‖z.2‖ < T * r := lt_of_lt_of_le hz2' (min_le_right _ _)
    rw [inv_mul_le_iff₀ hT]
    linarith [hz2]
  -- a compact chart neighbourhood of `x`, carrying the uniform Gram eigenvalue bound
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨C, hCmem, hCsub, hCcomp⟩ := local_compact_nhds
    ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  obtain ⟨lam, hlam, hlamle⟩ := exists_forall_le_chartMetricInner (I := I) g hCcomp hCsub
  -- the working neighbourhood
  set W : Set M := ((chartAt H x).source ∩ (extChartAt I x) ⁻¹' (ball y₀ δ₁))
    ∩ interior C with hWdef
  have hWopen : IsOpen W := by
    refine IsOpen.inter ?_ isOpen_interior
    have hc : ContinuousOn (extChartAt I x) (chartAt H x).source := by
      rw [← extChartAt_source (I := I) x]
      exact continuousOn_extChartAt x
    exact hc.isOpen_inter_preimage (chartAt H x).open_source isOpen_ball
  have hxW : x ∈ W := by
    refine ⟨⟨mem_chart_source H x, ?_⟩, mem_interior_iff_mem_nhds.mpr hCmem⟩
    show extChartAt I x x ∈ ball y₀ δ₁
    rw [← hy₀def]
    exact mem_ball_self hδ₁pos
  have hWC : W ⊆ C := fun q hq => interior_subset hq.2
  have hWsrc : W ⊆ (chartAt H x).source := fun q hq => hq.1.1
  -- the uniform `g`-radius
  refine ⟨W, δ * Real.sqrt lam / 2, hWopen, hxW, by positivity, ?_⟩
  -- a `g`-short vector has a short chart-`x` fibre coordinate, uniformly over `W`
  have hkey : ∀ q ∈ W, ∀ v : TangentSpace I q,
      g.metricInner q v v < (δ * Real.sqrt lam / 2) ^ 2 →
      ‖(trivializationAt E (TangentSpace I) x (⟨q, v⟩ : TangentBundle I M)).2‖ < δ := by
    intro q hq v hv
    set w : E := (trivializationAt E (TangentSpace I) x (⟨q, v⟩ : TangentBundle I M)).2
      with hw_def
    have hbridge : g.inner q v v
        = chartMetricInner (I := I) g x (extChartAt I x q) w w :=
      inner_self_eq_chartMetricInner_trivializationAt (I := I) g
        (α := x) (x := (⟨q, v⟩ : TangentBundle I M)) (hWsrc hq)
    have hlow : lam * ‖w‖ ^ 2 ≤ chartMetricInner (I := I) g x (extChartAt I x q) w w :=
      hlamle q (hWC hq) w
    have hgv : g.metricInner q v v = chartMetricInner (I := I) g x (extChartAt I x q) w w :=
      hbridge
    have hsq : (δ * Real.sqrt lam / 2) ^ 2 = δ ^ 2 * lam / 4 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hlam.le]
      ring
    rw [hsq] at hv
    have h1 : lam * ‖w‖ ^ 2 < δ ^ 2 * lam / 4 := by rw [hgv] at hv; linarith
    have h1' : lam * ‖w‖ ^ 2 < lam * (δ ^ 2 / 4) := by linarith
    have hw4 : ‖w‖ ^ 2 < δ ^ 2 / 4 := lt_of_mul_lt_mul_left h1' hlam.le
    have hw2 : ‖w‖ ^ 2 < δ ^ 2 := by nlinarith [hδpos]
    nlinarith [norm_nonneg w, hδpos, hw2]
  intro q hq v₁ hv₁ v₂ hv₂ hEq
  have hqsrc : q ∈ (chartAt H x).source := hWsrc hq
  have hqsrc_x : q ∈ (extChartAt I x).source := by rw [extChartAt_source I]; exact hqsrc
  have hqsrc_q : q ∈ (extChartAt I q).source := mem_extChartAt_source (I := I) q
  set w₁ : E := (trivializationAt E (TangentSpace I) x (⟨q, v₁⟩ : TangentBundle I M)).2
    with hw₁_def
  set w₂ : E := (trivializationAt E (TangentSpace I) x (⟨q, v₂⟩ : TangentBundle I M)).2
    with hw₂_def
  have hw₁δ : ‖w₁‖ < δ := hkey q hq v₁ hv₁
  have hw₂δ : ‖w₂‖ < δ := hkey q hq v₂ hv₂
  have hyball : extChartAt I x q ∈ ball y₀ δ₁ := hq.1.2
  have hB₁ : ((extChartAt I x q, w₁) : E × E) ∈ B := ⟨hyball, mem_ball_zero_iff.mpr hw₁δ⟩
  have hB₂ : ((extChartAt I x q, w₂) : E × E) ∈ B := ⟨hyball, mem_ball_zero_iff.mpr hw₂δ⟩
  have hmem₁ := hBflow _ hB₁
  have hmem₂ := hBflow _ hB₂
  -- the flow-window curves are the intrinsic maximal geodesics of `(q, vᵢ)`
  have h1lt : (1 : ℝ) < ε / T := (one_lt_div hT).mpr hTε
  have h0J : (0 : ℝ) ∈ Ioo (-(ε / T)) (ε / T) := ⟨by linarith, by linarith⟩
  have h1J : (1 : ℝ) ∈ Ioo (-(ε / T)) (ε / T) := ⟨by linarith, h1lt⟩
  obtain ⟨-, -, -, hsrc₁, -, -, -⟩ :=
    isGeodesicOn_flow_window (I := I) g x hT hTε hflow (y := extChartAt I x q) (w := w₁) hmem₁
  obtain ⟨-, -, -, hsrc₂, -, -, -⟩ :=
    isGeodesicOn_flow_window (I := I) g x hT hTε hflow (y := extChartAt I x q) (w := w₂) hmem₂
  have hivp₁ := isGeodesicWithInitialOn_flow_window (I := I) g x hT hTε hflow hqsrc v₁ hmem₁
  have hivp₂ := isGeodesicWithInitialOn_flow_window (I := I) g x hT hTε hflow hqsrc v₂ hmem₂
  have hmax₁ := geodesicMaximalCurve_eqOn (I := I) g isOpen_Ioo Set.ordConnected_Ioo
    h0J hivp₁ h1J
  have hmax₂ := geodesicMaximalCurve_eqOn (I := I) g isOpen_Ioo Set.ordConnected_Ioo
    h0J hivp₂ h1J
  -- equal endpoints in `M` read as equal endpoints of the chart-`x` flow
  have hEq' : geodesicMaximalCurve (I := I) g q v₁ 1
      = geodesicMaximalCurve (I := I) g q v₂ 1 := hEq
  have e₁ : extChartAt I x (geodesicMaximalCurve (I := I) g q v₁ 1)
      = (Z ((extChartAt I x q, T⁻¹ • w₁) : E × E) (1 * T)).1 := by
    rw [show geodesicMaximalCurve (I := I) g q v₁ 1
        = (extChartAt I x).symm ((Z ((extChartAt I x q, T⁻¹ • w₁) : E × E) (1 * T)).1)
        from hmax₁]
    exact (hsrc₁ 1 h1J).2
  have e₂ : extChartAt I x (geodesicMaximalCurve (I := I) g q v₂ 1)
      = (Z ((extChartAt I x q, T⁻¹ • w₂) : E × E) (1 * T)).1 := by
    rw [show geodesicMaximalCurve (I := I) g q v₂ 1
        = (extChartAt I x).symm ((Z ((extChartAt I x q, T⁻¹ • w₂) : E × E) (1 * T)).1)
        from hmax₂]
    exact (hsrc₂ 1 h1J).2
  have hend : (Z ((extChartAt I x q, T⁻¹ • w₁) : E × E) T).1
      = (Z ((extChartAt I x q, T⁻¹ • w₂) : E × E) T).1 := by
    have h := e₁.symm.trans (by rw [hEq'] : extChartAt I x
      (geodesicMaximalCurve (I := I) g q v₁ 1)
        = extChartAt I x (geodesicMaximalCurve (I := I) g q v₂ 1))
    rw [e₂] at h
    rwa [one_mul] at h
  -- injectivity of the pair map gives equal chart-`x` velocities
  have hGeq : G ((extChartAt I x q, w₁) : E × E) = G ((extChartAt I x q, w₂) : E × E) := by
    simp only [hGdef]
    rw [hend]
  have hweq : w₁ = w₂ := by
    have h := hGinj (hBball hB₁) (hBball hB₂) hGeq
    exact (Prod.ext_iff.mp h).2
  -- the fibre coordinate at `x` is injective on `T_qM`
  have hcc : tangentCoordChange I q x q v₁ = tangentCoordChange I q x q v₂ := hweq
  have := congrArg (tangentCoordChange I x q q) hcc
  rwa [tangentCoordChange_comp (I := I) ⟨⟨hqsrc_q, hqsrc_x⟩, hqsrc_q⟩,
    tangentCoordChange_comp (I := I) ⟨⟨hqsrc_q, hqsrc_x⟩, hqsrc_q⟩,
    tangentCoordChange_self (I := I) hqsrc_q,
    tangentCoordChange_self (I := I) hqsrc_q] at this

/-! ## The uniform exponential domain over a compact set -/

/-- **Math.** Petersen Ch. 5 (`cor:pet-ch5-uniform-injectivity-radius-compact`, "defined"
half): over a compact `K ⊆ M` there is a single `ε > 0` such that for every `q ∈ K` the
exponential map `exp_q v` is **defined** for every `v ∈ T_qM` with `|v|_g < ε`, i.e. the
maximal geodesic of `(q, v)` survives to time `1`.

Proof: the bounded-velocity set `{x ∈ TM | x.proj ∈ K, g(ẋ, ẋ) ≤ 1}` is compact
(`isCompact_tangentSublevel`), so uniform short-time existence
(`geodesic_uniformShortTimeExistence`) gives one `ε₀ > 0` realising every such datum on
`(-ε₀, ε₀)`.  Homogeneity converts short time into short velocity: for `|v|_g < ε₀/2` the
rescaled datum `u = (ε₀/2)⁻¹ · v` has `|u|_g ≤ 1`, and its geodesic reparametrised by
`t ↦ γ(λt)` realises `(q, v)` on `(-2, 2) ∋ 1`. -/
theorem uniform_intrinsic_domain (g : RiemannianMetric I M) [T2Space M]
    {K : Set M} (hK : IsCompact K) :
    ∃ ε > (0 : ℝ), ∀ q ∈ K, ∀ v : TangentSpace I q, g.metricInner q v v < ε ^ 2 →
      (1 : ℝ) ∈ geodesicMaximalDomain (I := I) g q v := by
  obtain ⟨ε₀, hε₀, hgeo⟩ := geodesic_uniformShortTimeExistence (I := I) g
    (isCompact_tangentSublevel (I := I) g hK 1)
  set lam : ℝ := ε₀ / 2 with hlam_def
  have hlam_pos : 0 < lam := by positivity
  refine ⟨lam, hlam_pos, ?_⟩
  intro q hq v hv
  set u : TangentSpace I q := (lam⁻¹ : ℝ) • v with hu_def
  have hscale : g.metricInner q u u = (lam⁻¹) ^ 2 * g.metricInner q v v := by
    rw [hu_def]
    simp [map_smul]
    ring
  have humem : (⟨q, u⟩ : TangentBundle I M) ∈
      {x : TangentBundle I M | x.proj ∈ K ∧ g.inner x.proj x.2 x.2 ≤ 1} := by
    refine ⟨hq, ?_⟩
    show g.metricInner q u u ≤ 1
    rw [hscale, inv_pow, inv_mul_le_iff₀ (by positivity)]
    nlinarith [hv]
  obtain ⟨γ, hcont, hstart, hvel, hgeoOn⟩ := hgeo ⟨q, u⟩ humem
  refine Set.mem_sUnion.mpr ⟨Ioo (-2 : ℝ) 2, ⟨isOpen_Ioo, Set.ordConnected_Ioo, ?_, ?_⟩, ?_⟩
  · exact ⟨by norm_num, by norm_num⟩
  · refine ⟨fun t => γ (lam * t), ?_, ?_, ?_, ?_⟩
    · apply hcont.comp (Continuous.continuousOn (by fun_prop))
      intro t ht
      exact ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
    · simpa using hstart
    · have hlin : HasDerivAt (fun s : ℝ => lam * s) lam 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_mul lam
      have hvel0 : HasDerivAt (fun s : ℝ => extChartAt I q (γ s)) u (lam * 0) := by
        simpa using hvel
      have h := hvel0.scomp (0 : ℝ) hlin
      simp only [Function.comp_def] at h
      convert h using 1
      show v = lam • u
      rw [hu_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hlam_pos), one_smul]
    · intro t ht
      refine hasGeodesicEquationAt_comp_const_mul (I := I) g lam ?_
      exact hgeoOn (lam * t) ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
  · norm_num

/-! ## Petersen Cor. 5.5.2 -/

/-- **Math.** Petersen Ch. 5, Cor. 5.5.2 (`cor:pet-ch5-uniform-injectivity-radius-compact`):
**a uniform injectivity radius on a compact set.**  For a compact `K ⊆ M` there is a single
`ε > 0` such that for **every** `q ∈ K` the exponential map `exp_q` is defined on the whole
`g`-metric ball `{v ∈ T_qM | |v|_g < ε}` and is **injective** there.

The two halves are `uniform_intrinsic_domain` (defined) and `exists_local_uniformInjOn`
(injective, locally uniform), combined by compactness: cover `K` by the finitely many
neighbourhoods `W_x` carrying a local uniform injectivity radius `ρ_x`, and take `ε` to be
the minimum of the domain radius and the finitely many `ρ_x`.

`exp_q` is the **intrinsic** exponential — the moving-foot maximal geodesic
`geodesicMaximalCurve g q v` evaluated at time `1` — not `PetersenLib.expMap`, whose
chart-anchored domain makes this statement false; see the module docstring. -/
theorem compactSet_uniformInjectivityRadius (g : RiemannianMetric I M) [T2Space M]
    {K : Set M} (hK : IsCompact K) :
    ∃ ε > (0 : ℝ), ∀ q ∈ K,
      (∀ v : TangentSpace I q, g.metricInner q v v < ε ^ 2 →
        (1 : ℝ) ∈ geodesicMaximalDomain (I := I) g q v) ∧
      Set.InjOn (fun v : TangentSpace I q => geodesicMaximalCurve (I := I) g q v 1)
        {v : TangentSpace I q | g.metricInner q v v < ε ^ 2} := by
  classical
  obtain ⟨ε₁, hε₁, hdom⟩ := uniform_intrinsic_domain (I := I) g hK
  choose W ρ hWopen hxW hρ hinj using fun x : M => exists_local_uniformInjOn (I := I) g x
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨ε₁, hε₁, by simp⟩
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover W
    fun x _ => (hWopen x).mem_nhds (hxW x)
  have htne : t.Nonempty := by
    obtain ⟨q, hq⟩ := hKne
    obtain ⟨x₀, hx₀t, -⟩ := Set.mem_iUnion₂.mp (hcover hq)
    exact ⟨x₀, hx₀t⟩
  have hinf_pos : 0 < t.inf' htne ρ := by
    obtain ⟨x₀, hx₀t, heq⟩ := Finset.exists_mem_eq_inf' htne ρ
    rw [heq]
    exact hρ x₀
  refine ⟨min ε₁ (t.inf' htne ρ), lt_min hε₁ hinf_pos, ?_⟩
  intro q hq
  obtain ⟨x₀, hx₀t, hqW⟩ := Set.mem_iUnion₂.mp (hcover hq)
  have hmin₁ : min ε₁ (t.inf' htne ρ) ≤ ε₁ := min_le_left _ _
  have hmin₂ : min ε₁ (t.inf' htne ρ) ≤ ρ x₀ :=
    le_trans (min_le_right _ _) (Finset.inf'_le ρ hx₀t)
  have hmin_pos : 0 < min ε₁ (t.inf' htne ρ) := lt_min hε₁ hinf_pos
  constructor
  · intro v hv
    refine hdom q hq v (lt_of_lt_of_le hv ?_)
    gcongr
  · refine (hinj x₀ q hqW).mono ?_
    intro v hv
    have hv' : g.metricInner q v v < min ε₁ (t.inf' htne ρ) ^ 2 := hv
    show g.metricInner q v v < ρ x₀ ^ 2
    refine lt_of_lt_of_le hv' ?_
    gcongr

end PetersenLib

end
