import MorganTianLib.Ch01.ParallelIsometry
import MorganTianLib.Ch01.GaussLemma

/-!
# Poincaré Ch. 1, §1.4 — the Jacobi equation in a parallel frame

Pairing a Jacobi field `J` against a **parallel** field `V` along a geodesic
kills every connection term and leaves the scalar Jacobi equation:

`d/dt ⟨J, V⟩ = ⟨∇J, V⟩`,     `d/dt ⟨∇J, V⟩ = −⟨ℛ(J, γ')γ', V⟩`.

Indeed metric compatibility gives `d/dt⟨X, V⟩ = ⟨∇X, V⟩ + ⟨X, ∇V⟩`, and the
second term vanishes because `V` is parallel; then `∇J = ∇J` and
`∇∇J = −ℛ(J, γ')γ'` are the two halves of the Jacobi pair system.  Taking `V`
to run through a parallel *orthonormal frame* turns these into the matrix ODE
`𝒥'' + ℛ𝒥 = 0` that `IsRadialJacobi` consumes — the frame is what converts the
moving inner product on `T_{γ(t)}M` into the fixed one on `E`.

`GaussLemma` is the special case `V = γ'` (the velocity of a geodesic is
parallel), where the curvature term additionally vanishes by antisymmetry.
This file records the general case.

Main results:

* `IsJacobiFieldOn.hasDerivAt_chartInner_fst_parallel`,
  `IsJacobiFieldOn.hasDerivAt_chartInner_snd_parallel` — the two chart-level
  identities, for an arbitrary parallel field `V` in place of `γ'`;
* `IsJacobiFieldAlongOn.hasDerivAt_metricInner_parallel` — the **manifold-level**
  first identity `d/dt ⟨J, V⟩_g = ⟨∇J, V⟩_g`, valid along a geodesic crossing
  arbitrarily many charts.  It is curvature-free, so it needs no chart-to-
  manifold curvature bridge: both fields localize into the chart at the moving
  foot (`ParallelAlong`, `JacobiExistence`), and `HasDerivAt` is a local
  statement, so the chart identity transfers directly.

Blueprint: `lem:parallel-frame`, `lem:jacobi-frame-reduction`,
`lem:geodesic-polar-form`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The chart-level identities -/

namespace IsJacobiFieldOn

variable {g : RiemannianMetric I M} {α : M} {u J DJ V : ℝ → E} {a b : ℝ} {t : ℝ}

/-- **Math.** Pairing a Jacobi field against a **parallel** field:
`d/dt ⟨J, V⟩ = ⟨∇J, V⟩ + ⟨J, ∇V⟩ = ⟨∇J, V⟩`, the second term vanishing because
`V` is parallel.  `GaussLemma`'s `hasDerivAt_chartInner_fst_velocity` is the
case `V = u̇`.  Blueprint: `lem:jacobi-frame-reduction`. -/
theorem hasDerivAt_chartInner_fst_parallel
    (h : IsJacobiFieldOn (I := I) g α u J DJ a b)
    (hV : IsParallelSolOn (I := I) g α u V a b)
    (ht : t ∈ Ioo a b)
    (hu : DifferentiableAt ℝ u t)
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : (extChartAt I α).symm (u t)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    HasDerivAt (fun s => chartMetricInner (I := I) g α (u s) (J s) (V s))
      (chartMetricInner (I := I) g α (u t) (DJ t) (V t)) t := by
  refine (hasDerivAt_chartMetricInner_along (I := I) g α u J V
    hu (h.differentiableAt_fst ht) (hV.differentiableAt ht) hG hbase).congr_deriv ?_
  rw [h.covariantDerivCoord_fst ht, hV.covariantDerivCoord_eq_zero ht,
    chartMetricInner_zero_right, add_zero]

/-- **Math.** Pairing the covariant derivative of a Jacobi field against a
**parallel** field: `d/dt ⟨∇J, V⟩ = ⟨∇∇J, V⟩ = −⟨ℛ(J, u̇)u̇, V⟩`, using the
Jacobi equation.  Together with `hasDerivAt_chartInner_fst_parallel` this is
the scalar Jacobi equation `y'' = −⟨ℛ(J, u̇)u̇, V⟩` for `y = ⟨J, V⟩`.
`GaussLemma`'s `hasDerivAt_chartInner_snd_velocity` is the case `V = u̇`, where
the right-hand side vanishes by curvature antisymmetry.
Blueprint: `lem:jacobi-frame-reduction`. -/
theorem hasDerivAt_chartInner_snd_parallel
    (h : IsJacobiFieldOn (I := I) g α u J DJ a b)
    (hV : IsParallelSolOn (I := I) g α u V a b)
    (ht : t ∈ Ioo a b)
    (hu : DifferentiableAt ℝ u t)
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : (extChartAt I α).symm (u t)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    HasDerivAt (fun s => chartMetricInner (I := I) g α (u s) (DJ s) (V s))
      (-chartMetricInner (I := I) g α (u t)
        (chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t))
        (V t)) t := by
  refine (hasDerivAt_chartMetricInner_along (I := I) g α u DJ V
    hu (h.differentiableAt_snd ht) (hV.differentiableAt ht) hG hbase).congr_deriv ?_
  rw [h.covariantDerivCoord_snd ht, hV.covariantDerivCoord_eq_zero ht,
    chartMetricInner_zero_right, add_zero, chartMetricInner_neg_left]

end IsJacobiFieldOn

/-! ### The manifold-level identity -/

section Manifold

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Metric compatibility against a parallel field, on the
manifold**: along a geodesic `γ` — which may cross arbitrarily many charts —
`d/dt ⟨J(t), V(t)⟩_{g,γ(t)} = ⟨∇J(t), V(t)⟩_{g,γ(t)}` at interior times, for
`J` a Jacobi field along `γ` with covariant derivative `DJ`, and `V` parallel
along `γ`.

No chart-to-manifold curvature bridge is needed, because this half of the
scalar Jacobi equation is curvature-free.  Around an interior time the curve
stays in the chart at its own foot, so both fields localize there
(`IsJacobiFieldAlongOn.isJacobiFieldOn_of_mem_source` and
`IsParallelAlongOn.isParallelSolOn_of_mem_source`); the chart identity
`hasDerivAt_chartInner_fst_parallel` applies; and since `HasDerivAt` is local
while the intrinsic pairing agrees with the chart Gram pairing throughout that
piece (`metricInner_eq_chartMetricInner_rep`), the identity transfers.

Blueprint: `lem:jacobi-frame-reduction`, `lem:geodesic-polar-form`. -/
theorem IsJacobiFieldAlongOn.hasDerivAt_metricInner_parallel
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ V : ℝ → E} {a b : ℝ}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hPar : IsParallelAlongOn (I := I) g γ V a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => g.metricInner (γ s) (J s : TangentSpace I (γ s)) (V s))
      (g.metricInner (γ t) (DJ t : TangentSpace I (γ t)) (V t)) t := by
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
  -- localize both fields into the chart at `γ t`
  have hJloc := hJac.isJacobiFieldOn_of_mem_source hgeo hγc hsub hsrc
  have hVloc := hPar.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc
  -- side conditions of the chart identity
  have hu : DifferentiableAt ℝ (fun s => extChartAt I (γ t) (γ s)) t :=
    hgeo.differentiableAt_extChartAt htI (hγc t htI) (hsrc t (Ioo_subset_Icc_self ht'))
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g (γ t) i j)
      ((fun s => extChartAt I (γ t) (γ s)) t) := fun i j =>
    differentiableAt_chartGramOnE (I := I) g (γ t)
      ((extChartAt I (γ t)).map_source
        (by rw [extChartAt_source]
            exact hsrc t (Ioo_subset_Icc_self ht'))) i j
  have hbase : (extChartAt I (γ t)).symm
      ((fun s => extChartAt I (γ t) (γ s)) t)
      ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    symm_extChartAt_mem_baseSet (I := I) (hsrc t (Ioo_subset_Icc_self ht'))
  -- the chart-level identity at `t`
  have hchart := hJloc.hasDerivAt_chartInner_fst_parallel hVloc ht' hu hG hbase
  -- the intrinsic pairing agrees with the chart Gram pairing near `t`
  have hIcc : Icc a' b' ∈ 𝓝 t := Icc_mem_nhds ha't htb'
  have hEq : (fun s => g.metricInner (γ s) (J s : TangentSpace I (γ s)) (V s))
      =ᶠ[𝓝 t] fun s => chartMetricInner (I := I) g (γ t)
        ((fun σ => extChartAt I (γ t) (γ σ)) s)
        (chartVectorRep (I := I) γ (γ t) J s)
        (chartVectorRep (I := I) γ (γ t) V s) := by
    filter_upwards [hIcc] with s hs
    exact metricInner_eq_chartMetricInner_rep (I := I) g (hsrc s hs) J V
  -- transfer, and identify the derivative value intrinsically
  have hval : chartMetricInner (I := I) g (γ t)
      ((fun σ => extChartAt I (γ t) (γ σ)) t)
      (chartVectorRep (I := I) γ (γ t) DJ t)
      (chartVectorRep (I := I) γ (γ t) V t)
      = g.metricInner (γ t) (DJ t : TangentSpace I (γ t)) (V t) :=
    (metricInner_eq_chartMetricInner_rep (I := I) g
      (hsrc t (Ioo_subset_Icc_self ht')) DJ V).symm
  rw [← hval]
  exact hchart.congr_of_eventuallyEq hEq

end Manifold

end MorganTianLib

end
