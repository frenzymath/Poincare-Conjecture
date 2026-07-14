import MorganTianLib.Ch01.FrameJacobi
import MorganTianLib.Ch01.CurvatureSectionalBound

/-!
# Poincaré Ch. 1, §1.4 — the curvature term of the Jacobi equation, intrinsically

`FrameJacobi` proves the **first** half of the scalar Jacobi equation at the
manifold level,

`d/dt ⟨J, V⟩_g = ⟨∇J, V⟩_g`,

for `J` a Jacobi field and `V` parallel along a geodesic `γ`.  That half is
*curvature-free*, so it transfers from the chart with no further work.  The
**second** half,

`d/dt ⟨∇J, V⟩_g = −⟨ℛ(J, γ')γ', V⟩_g = ℛ(J, γ', γ', V)`,

carries a curvature term, and the chart-level statement
(`IsJacobiFieldOn.hasDerivAt_chartInner_snd_parallel`) expresses that term with
`chartCurvature`, which is chart-dependent data.  To read it intrinsically we
need the manifold ↔ chart curvature bridge *along the curve*.  This file
supplies it.

The key observation is a **reconstruction lemma**: realizing the chart reading
of a field back in the chart frame returns the field itself,

`∑ i, (chartVectorRep γ α V τ)^i • X_i(γ τ) = V τ`   (`chartFrame_chartVectorRep`),

because the chart frame realization `∑ i, v^i • X_i(p)` *is* the inverse
trivialization `(trivializationAt E (TangentSpace I) α).symm p v`
(`trivializationAt_symm_eq_sum_chartBasisVecFiber`), which undoes the tangent
coordinate change defining `chartVectorRep`
(`trivializationAt_symm_eq_tangentCoordChange`, `tangentCoordChange_readback`).

Feeding that into `curvatureFormAt_chartFrame` turns the bridge — stated for
*coordinate* vectors — into a statement about *fields along `γ`*
(`curvatureFormAt_chartVectorRep`), and the manifold second identity follows by
the same localization argument as its curvature-free partner.

Main results:

* `chartFrame_chartVectorRep` — the reconstruction lemma;
* `curvatureFormAt_chartVectorRep` — **the along-curve curvature bridge**:
  the intrinsic curvature form of four fields at the moving foot is minus the
  chart Gram pairing of the chart curvature of their chart readings;
* `IsJacobiFieldAlongOn.hasDerivAt_metricInner_snd_parallel` — **the manifold
  second identity** `d/dt ⟨∇J, V⟩_g = ℛ(J, γ', γ', V)`.

Together with `IsJacobiFieldAlongOn.hasDerivAt_metricInner_parallel` this is the
complete scalar Jacobi system in a parallel frame, which is what `IsRadialJacobi`
consumes.

Blueprint: `lem:jacobi-frame-reduction`, `lem:geodesic-polar-form`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Filter Riemannian Riemannian.Tensor
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Reconstruction: the chart frame realization of a chart reading -/

/-- **Math.** **Reconstruction.**  The chart-frame realization of the chart
reading of a field along `γ` is the field itself:
`∑ i, (V_α(τ))^i • X_i(γ τ) = V τ` in `T_{γ τ}M`.

Indeed the realization `∑ i, v^i • X_i(p)` is exactly the inverse trivialization
`(trivializationAt E (TangentSpace I) α).symm p v`
(`trivializationAt_symm_eq_sum_chartBasisVecFiber`), which at a foot inside the
chart source is the tangent coordinate change `tangentCoordChange I α p p`
(`trivializationAt_symm_eq_tangentCoordChange`); and that inverts the coordinate
change `tangentCoordChange I p α p` defining `chartVectorRep`
(`tangentCoordChange_readback`).

This is what upgrades the *coordinate-vector* bridge `curvatureFormAt_chartFrame`
to a statement about *fields along a curve*.
Blueprint: `lem:chart-curvature-coordinates`. -/
theorem chartFrame_chartVectorRep {γ : ℝ → M} {α : M} {τ : ℝ}
    (hsrc : γ τ ∈ (chartAt H α).source) (V : ℝ → E) :
    (∑ i, Geodesic.chartCoord (E := E) i (chartVectorRep (I := I) γ α V τ)
        • chartBasisVecFiber (I := I) α i (γ τ) : TangentSpace I (γ τ))
      = V τ := by
  rw [← trivializationAt_symm_eq_sum_chartBasisVecFiber (I := I) α (γ τ)
      (chartVectorRep (I := I) γ α V τ),
    trivializationAt_symm_eq_tangentCoordChange (I := I) α hsrc,
    chartVectorRep_apply, tangentCoordChange_readback (I := I) hsrc]

/-! ### The along-curve curvature bridge -/

/-- **Math.** **The manifold ↔ chart curvature bridge, along a curve.**  For
four fields `X, Y, Z, W : ℝ → E` along `γ`, read at the moving foot `γ τ` whose
chart is `α`, the intrinsic curvature `(0,4)`-form of the Levi-Civita connection
is minus the chart Gram pairing of the chart curvature of their chart readings:

`ℛ(X, Y, Z, W)(γ τ) = −⟨ℛ_chart(φ(γ τ))(X_α, Y_α)Z_α, W_α⟩_{G(φ(γ τ))}`.

The sign is the do Carmo ↔ Morgan–Tian convention flip already recorded in
`curvatureFormAt_chartFrame`, of which this is the field-valued form obtained by
`chartFrame_chartVectorRep`.
Blueprint: `lem:chart-curvature-coordinates`, `lem:jacobi-frame-reduction`. -/
theorem curvatureFormAt_chartVectorRep [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M)
    {γ : ℝ → M} {α : M} {τ : ℝ} (hsrc : γ τ ∈ (chartAt H α).source)
    (X Y Z W : ℝ → E) :
    curvatureFormAt g g.leviCivitaConnection (γ τ)
        (X τ : TangentSpace I (γ τ)) (Y τ) (Z τ) (W τ)
      = - chartMetricInner (I := I) g α (extChartAt I α (γ τ))
          (chartCurvature (I := I) g α (extChartAt I α (γ τ))
            (chartVectorRep (I := I) γ α X τ)
            (chartVectorRep (I := I) γ α Y τ)
            (chartVectorRep (I := I) γ α Z τ))
          (chartVectorRep (I := I) γ α W τ) :=
  chartFrame_chartVectorRep (I := I) hsrc X ▸
    chartFrame_chartVectorRep (I := I) hsrc Y ▸
      chartFrame_chartVectorRep (I := I) hsrc Z ▸
        chartFrame_chartVectorRep (I := I) hsrc W ▸
          curvatureFormAt_chartFrame (I := I) g hsrc
            (chartVectorRep (I := I) γ α X τ)
            (chartVectorRep (I := I) γ α Y τ)
            (chartVectorRep (I := I) γ α Z τ)
            (chartVectorRep (I := I) γ α W τ)

/-! ### The manifold second identity -/

section Manifold

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The curvature half of the scalar Jacobi equation, on the
manifold**: along a geodesic `γ` — which may cross arbitrarily many charts —

`d/dt ⟨∇J(t), V(t)⟩_g = ℛ(J(t), γ'(t), γ'(t), V(t))`

at interior times, for `J` a Jacobi field along `γ` with covariant derivative
`DJ`, and `V` parallel along `γ`.  In Morgan–Tian's sign convention the right
side is `−⟨ℛ(J, γ')γ', V⟩`, the curvature term of `∇²J + ℛ(J, γ')γ' = 0`.

The proof mirrors its curvature-free partner
`IsJacobiFieldAlongOn.hasDerivAt_metricInner_parallel`: around an interior time
the curve stays in the chart at its own foot, both fields localize there, the
chart identity `hasDerivAt_chartInner_snd_parallel` applies, and `HasDerivAt` is
local.  The one extra step is identifying the chart-level curvature value with
the intrinsic one, which is exactly `curvatureFormAt_chartVectorRep` (with the
chart velocity `u̇` recognized as the chart reading of `γ'` by
`chartVectorRep_velocity_of_geodesicAt`).

Blueprint: `lem:jacobi-frame-reduction`, `lem:geodesic-polar-form`. -/
theorem IsJacobiFieldAlongOn.hasDerivAt_metricInner_snd_parallel
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ V : ℝ → E} {a b : ℝ}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hPar : IsParallelAlongOn (I := I) g γ V a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => g.metricInner (γ s) (DJ s) (V s) : ℝ → ℝ)
      (curvatureFormAt g g.leviCivitaConnection (γ t)
        (J t) (mfderivVelocity (I := I) (E := E) γ t)
        (mfderivVelocity (I := I) (E := E) γ t) (V t)) t := by
  classical
  have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
  -- a relative interval around `t` mapped by `γ` into the chart at `γ t`
  have hnhds : γ ⁻¹' (chartAt H (γ t)).source ∈ 𝓝 t :=
    (hγc t htI).preimage_mem_nhds
      ((chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  set a' := max a (t - ε / 2) with ha'
  set b' := min b (t + ε / 2) with hb'
  have ha't : a' < t := max_lt ht.1 (by linarith)
  have htb' : t < b' := lt_min ht.2 (by linarith)
  have ht' : t ∈ Ioo a' b' := ⟨ha't, htb'⟩
  have hsub : Icc a' b' ⊆ Icc a b :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsrc : ∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H (γ t)).source := by
    intro τ hτ
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : t - ε / 2 ≤ τ := le_trans (le_max_right _ _) hτ.1
    have h2 : τ ≤ t + ε / 2 := le_trans hτ.2 (min_le_right _ _)
    have : |τ - t| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hsrct : γ t ∈ (chartAt H (γ t)).source := hsrc t (Ioo_subset_Icc_self ht')
  -- localize both fields into the chart at `γ t`
  have hJloc := hJac.isJacobiFieldOn_of_mem_source hgeo hγc hsub hsrc
  have hVloc := hPar.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc
  -- side conditions of the chart identity
  have hu : DifferentiableAt ℝ (fun s => extChartAt I (γ t) (γ s)) t :=
    hgeo.differentiableAt_extChartAt htI (hγc t htI) hsrct
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g (γ t) i j)
      ((fun s => extChartAt I (γ t) (γ s)) t) := fun i j =>
    differentiableAt_chartGramOnE (I := I) g (γ t)
      ((extChartAt I (γ t)).map_source (by rw [extChartAt_source]; exact hsrct)) i j
  have hbase : (extChartAt I (γ t)).symm ((fun s => extChartAt I (γ t) (γ s)) t)
      ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    symm_extChartAt_mem_baseSet (I := I) hsrct
  -- the chart-level identity at `t`
  have hchart := hJloc.hasDerivAt_chartInner_snd_parallel hVloc ht' hu hG hbase
  -- the intrinsic pairing agrees with the chart Gram pairing near `t`
  have hIcc : Icc a' b' ∈ 𝓝 t := Icc_mem_nhds ha't htb'
  have hEq : (fun s => g.metricInner (γ s) (DJ s) (V s) : ℝ → ℝ)
      =ᶠ[𝓝 t] fun s => chartMetricInner (I := I) g (γ t)
        ((fun σ => extChartAt I (γ t) (γ σ)) s)
        (chartVectorRep (I := I) γ (γ t) DJ s)
        (chartVectorRep (I := I) γ (γ t) V s) := by
    filter_upwards [hIcc] with s hs
    exact metricInner_eq_chartMetricInner_rep (I := I) g (hsrc s hs) DJ V
  -- the chart velocity is the chart reading of the manifold velocity
  have hvel : chartVectorRep (I := I) γ (γ t) (mfderivVelocity (I := I) γ) t
      = deriv (fun s => extChartAt I (γ t) (γ s)) t :=
    chartVectorRep_velocity_of_geodesicAt (I := I) (hgeo t htI) (hγc t htI) hsrct
  -- identify the chart curvature value with the intrinsic curvature form
  have hval : (- chartMetricInner (I := I) g (γ t)
      ((fun σ => extChartAt I (γ t) (γ σ)) t)
      (chartCurvature (I := I) g (γ t)
        ((fun σ => extChartAt I (γ t) (γ σ)) t)
        (chartVectorRep (I := I) γ (γ t) J t)
        (deriv (fun s => extChartAt I (γ t) (γ s)) t)
        (deriv (fun s => extChartAt I (γ t) (γ s)) t))
      (chartVectorRep (I := I) γ (γ t) V t) : ℝ)
      = curvatureFormAt g g.leviCivitaConnection (γ t)
          (J t) (mfderivVelocity (I := I) (E := E) γ t)
          (mfderivVelocity (I := I) (E := E) γ t) (V t) := by
    rw [curvatureFormAt_chartVectorRep (I := I) g hsrct J
      (mfderivVelocity (I := I) (E := E) γ) (mfderivVelocity (I := I) (E := E) γ) V,
      hvel]
  rw [← hval]
  exact hchart.congr_of_eventuallyEq hEq

end Manifold

end MorganTianLib

end
