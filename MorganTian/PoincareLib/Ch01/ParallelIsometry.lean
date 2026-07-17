import PoincareLib.Ch01.ParallelAlong

/-!
# Poincaré Ch. 1, §1.3 — parallel transport is an isometry; parallel frames

`ParallelAlong` produced parallel transport along a geodesic crossing
arbitrarily many charts.  This file proves the property that makes it useful
for comparison geometry: **parallel transport preserves the metric**.  Hence a
frame that starts orthonormal at `γ a` stays orthonormal all along `γ`, which
is exactly the identification `T_{γ(t)}M ≅ E` (isometric, and turning `∇_{γ'}`
into `d/dt`) under which the Jacobi equation becomes the matrix ODE
`𝒥'' + ℛ𝒥 = 0` consumed by `IsRadialJacobi`.

Main results:

* `eqOn_const_of_locally_const` — a real function that is constant near every
  point of `[a, b]` (relatively) is constant on `[a, b]`.  This is how a
  chart-local invariant is upgraded to a global one along a curve leaving every
  chart: no supremum walk is needed once the local statement is available at
  *every* point, because a locally constant function on an interval is
  constant.
* `IsParallelAlongOn.metricInner_eq` — **parallel transport is an isometry**:
  `⟨V(t), W(t)⟩_{g,γ(t)}` is constant in `t` for `V, W` parallel along `γ`.
* `exists_parallelFrameAlong` — **a parallel frame along a geodesic**, with
  arbitrarily prescribed initial vectors, whose Gram matrix is constant; in
  particular an initially orthonormal frame stays orthonormal.

Blueprint: `lem:parallel-frame`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1;
do Carmo, *Riemannian Geometry*, Ch. 2, Prop. 2.6.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Local constancy upgrades to global constancy -/

/-- **Math.** A real function that is constant on a relative neighbourhood of
every point of `[a, b]` is constant on `[a, b]`.

This is the mechanism by which a *chart-local* invariant becomes a *global*
invariant along a curve that leaves every chart: local constancy gives
continuity on `[a, b]` and a vanishing derivative at every interior point, and
a continuous function on an interval with vanishing interior derivative is
constant. -/
theorem eqOn_const_of_locally_const {f : ℝ → ℝ} {a b : ℝ}
    (h : ∀ t₀ ∈ Icc a b, ∃ a' b' : ℝ, t₀ ∈ Icc a' b' ∧
      Icc a' b' ∈ 𝓝[Icc a b] t₀ ∧
      ∀ s ∈ Icc a' b', f s = f t₀) :
    ∀ t ∈ Icc a b, f t = f a := by
  refine eqOn_const_of_hasDerivAt_zero_interior ?_ ?_
  · -- continuity: `f` agrees with a constant on a relative neighbourhood
    intro t ht
    obtain ⟨a', b', _ht', hnbhd, hconst⟩ := h t ht
    have hEq : f =ᶠ[𝓝[Icc a b] t] fun _ => f t := by
      filter_upwards [hnbhd] with s hs using hconst s hs
    exact ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const hEq rfl
  · -- interior derivative: at an interior point the relative neighbourhood is
    -- an honest neighbourhood, so `f` is eventually constant
    intro t ht
    obtain ⟨a', b', _ht', hnbhd, hconst⟩ := h t (Ioo_subset_Icc_self ht)
    have hIcc : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hnb : Icc a' b' ∈ 𝓝 t := by
      rwa [nhdsWithin_eq_nhds.2 hIcc] at hnbhd
    have hEq : f =ᶠ[𝓝 t] fun _ => f t := by
      filter_upwards [hnb] with s hs using hconst s hs
    exact (hasDerivAt_const t (f t)).congr_of_eventuallyEq hEq

/-! ### Parallel transport preserves the metric -/

section Isometry

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **Parallel transport is an isometry.**  If `V` and `W` are
parallel along the geodesic `γ` on `[a, b]`, then their metric inner product
`⟨V(t), W(t)⟩_{g, γ(t)}` is constant in `t`.

Proof: around any time `t₀` the curve stays in the chart at `γ t₀`, so both
fields localize there (`IsParallelAlongOn.isParallelSolOn_of_mem_source`), and
the chart computation `IsParallelSolOn.chartMetricInner_eq` shows the chart
Gram pairing — which is the intrinsic pairing, by
`metricInner_eq_chartMetricInner_rep` — is constant on that piece.  So the
intrinsic pairing is locally constant on `[a, b]`, hence constant.

Blueprint: `lem:parallel-frame`. -/
theorem IsParallelAlongOn.metricInner_eq
    {g : RiemannianMetric I M} {γ : ℝ → M} {V W : ℝ → E} {a b : ℝ}
    (hV : IsParallelAlongOn (I := I) g γ V a b)
    (hW : IsParallelAlongOn (I := I) g γ W a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    ∀ t ∈ Icc a b,
      g.metricInner (γ t) (V t : TangentSpace I (γ t)) (W t)
        = g.metricInner (γ a) (V a : TangentSpace I (γ a)) (W a) := by
  classical
  refine eqOn_const_of_locally_const (f := fun τ =>
    g.metricInner (γ τ) (V τ : TangentSpace I (γ τ)) (W τ)) ?_
  intro t₀ ht₀
  -- a relative interval around `t₀` whose `γ`-image lies in the chart at `γ t₀`
  have hnhds : γ ⁻¹' (chartAt H (γ t₀)).source ∈ 𝓝 t₀ :=
    (hγc t₀ ht₀).preimage_mem_nhds
      ((chartAt H (γ t₀)).open_source.mem_nhds (mem_chart_source H (γ t₀)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  set a' := max a (t₀ - ε / 2) with ha'
  set b' := min b (t₀ + ε / 2) with hb'
  have ht' : t₀ ∈ Icc a' b' :=
    ⟨max_le ht₀.1 (by linarith), le_min ht₀.2 (by linarith)⟩
  have hsub : Icc a' b' ⊆ Icc a b :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsrc : ∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H (γ t₀)).source := by
    intro τ hτ
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : t₀ - ε / 2 ≤ τ := le_trans (le_max_right _ _) hτ.1
    have h2 : τ ≤ t₀ + ε / 2 := le_trans hτ.2 (min_le_right _ _)
    have : |τ - t₀| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hnbhd : Icc a' b' ∈ 𝓝[Icc a b] t₀ := by
    refine mem_nhdsWithin.2 ⟨Ioo (t₀ - ε / 2) (t₀ + ε / 2), isOpen_Ioo,
      ⟨by linarith, by linarith⟩, fun σ hσ => ?_⟩
    exact ⟨max_le hσ.2.1 hσ.1.1.le, le_min hσ.2.2 hσ.1.2.le⟩
  refine ⟨a', b', ht', hnbhd, ?_⟩
  -- localize both fields into the chart at `γ t₀`
  have hVloc := hV.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc
  have hWloc := hW.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc
  -- the analytic side conditions of `chartMetricInner_eq`
  have hu : ∀ τ ∈ Icc a' b',
      DifferentiableAt ℝ (fun s => extChartAt I (γ t₀) (γ s)) τ := fun τ hτ =>
    hgeo.differentiableAt_extChartAt (hsub hτ) (hγc τ (hsub hτ)) (hsrc τ hτ)
  have hG : ∀ τ ∈ Icc a' b', ∀ i j,
      DifferentiableAt ℝ (chartGramOnE (I := I) g (γ t₀) i j)
        ((fun s => extChartAt I (γ t₀) (γ s)) τ) := by
    intro τ hτ i j
    exact differentiableAt_chartGramOnE (I := I) g (γ t₀)
      ((extChartAt I (γ t₀)).map_source
        (by rw [extChartAt_source]; exact hsrc τ hτ)) i j
  have hbase : ∀ τ ∈ Icc a' b',
      (extChartAt I (γ t₀)).symm ((fun s => extChartAt I (γ t₀) (γ s)) τ)
        ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet := fun τ hτ =>
    symm_extChartAt_mem_baseSet (I := I) (hsrc τ hτ)
  have hchart := hVloc.chartMetricInner_eq hWloc hu hG hbase
  -- transport the chart identity back to the intrinsic pairing
  intro s hs
  have hs' := hchart s hs
  have ht'' := hchart t₀ ht'
  show g.metricInner (γ s) (V s : TangentSpace I (γ s)) (W s)
      = g.metricInner (γ t₀) (V t₀ : TangentSpace I (γ t₀)) (W t₀)
  rw [metricInner_eq_chartMetricInner_rep (I := I) g (hsrc s hs) V W,
    metricInner_eq_chartMetricInner_rep (I := I) g (hsrc t₀ ht') V W, hs', ht'']

/-! ### Parallel frames along a geodesic -/

/-- **Math.** **A parallel frame along a geodesic** (Morgan–Tian §1.3;
`lem:parallel-frame`).  Along a geodesic `γ` on `[a, b]` — which may cross
arbitrarily many charts — every family `e₀ : ι → T_{γ(a)}M` of initial vectors
extends to a family of fields parallel along `γ`, and the Gram matrix of the
family is **constant** along the curve.

In particular a family that is orthonormal at `γ a` is orthonormal at every
`γ t`: parallel transport supplies the isometric identification
`T_{γ(t)}M ≅ T_{γ(a)}M` under which `∇_{γ'}` becomes `d/dt`.  This is the
frame in which the Jacobi equation `∇²J + ℛ(J, γ')γ' = 0` turns into the
constant-coefficient-free matrix ODE `𝒥'' + ℛ𝒥 = 0` of `IsRadialJacobi`.

Blueprint: `lem:parallel-frame`. -/
theorem exists_parallelFrameAlong
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {ι : Type*} (e₀ : ι → TangentSpace I (γ a)) :
    ∃ e : ι → ℝ → E,
      (∀ i, e i a = e₀ i)
      ∧ (∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
      ∧ ∀ i j, ∀ t ∈ Icc a b,
          g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
            = g.metricInner (γ a) (e₀ i) (e₀ j) := by
  classical
  choose e hpar hinit using fun i : ι =>
    exists_isParallelAlongOn (I := I) hab hgeo hγc (e₀ i)
  refine ⟨e, hinit, hpar, fun i j t ht => ?_⟩
  have hgram := (hpar i).metricInner_eq (hpar j) hgeo hγc t ht
  rw [hgram, hinit i, hinit j]

end Isometry

end PoincareLib

end
