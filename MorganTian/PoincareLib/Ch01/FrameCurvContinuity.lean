import PoincareLib.Ch01.FrameJacobiSystem
import PoincareLib.Ch01.FrameReduction

/-!
# Poincaré Ch. 1, §1.4 — continuity of the curvature coefficient along a geodesic

`FrameJacobiSystem` turns the Jacobi equation along a geodesic into the closed
scalar system `c'' = ℛ c` with coefficient matrix

`ℛᵢⱼ(t) = frameCurv g γ e i j t = ℛ(Eⱼ(t), γ'(t), γ'(t), Eᵢ(t))`.

To feed that system into the ODE theory (`IsRadialJacobi`) one more analytic fact
is needed, and it is the last missing link of the comparison chain: **`t ↦ ℛ(t)`
is continuous**.  This file proves it.

The difficulty is that *none* of the three ingredients of `frameCurv` is
continuous on its own:

* `curvatureFormAt` is defined through `extendVector p v = Classical.choose …`, an
  arbitrary global smooth extension re-chosen at every point `p`, so it has **no**
  regularity in `p` that can be got by unfolding;
* a field `V` that `IsParallelAlongOn` is carried *at its own moving foot*: `V t`
  is the reading of a tangent vector in `chartAt H (γ t)`, and `chartAt` is an
  arbitrary function of the point, so `t ↦ V t : ℝ → E` genuinely **jumps** at
  every chart change.  The same goes for `mfderivVelocity γ`.

The scalar `frameCurv` is nevertheless continuous, because the moving-foot
trivialization used by the four vector slots is the *same* one used by
`curvatureFormAt (γ t)`: the jumps cancel.  The proof must therefore never
mention the raw `ℝ → E` maps, and instead route everything through the chart
bridge `curvatureFormAt_chartVectorRep`, which rewrites the intrinsic (and
choice-defined) scalar in terms of **fixed-chart** data — all of which does have
continuity lemmas:

`ℛᵢⱼ(τ) = −⟨ℛ_chart(φ(γτ))(Eⱼ,α, u̇, u̇), Eᵢ,α⟩_{G(φ(γτ))}`,  `u = φ_α ∘ γ`.

Main results:

* `frameCurv_eq_chart` — the fixed-chart formula for `frameCurv`;
* `continuousOn_frameCurv_of_mem_source` — continuity on a subinterval whose
  `γ`-image lies in one chart;
* `continuousOn_frameCurv` — continuity on **all** of `[a, b]`, for a geodesic
  crossing arbitrarily many charts, by the local-to-global glue;
* `exists_bound_frameCurv` — the resulting bound on a compact interval.

Blueprint: `lem:geodesic-polar-form`(3), `lem:jacobi-frame-reduction`,
`lem:radial-shape-riccati`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-! ### The fixed-chart formula for the frame curvature coefficient -/

/-- **Math.** **The frame curvature coefficient, read in a fixed chart.**  At a
time `τ` where the geodesic sits in the source of the chart at `α`,

`ℛᵢⱼ(τ) = −⟨ℛ_chart(u τ)(Eⱼ,α(τ), u̇(τ), u̇(τ)), Eᵢ,α(τ)⟩_{G(u τ)}`,
`u = φ_α ∘ γ`,

where `Eₖ,α = chartVectorRep γ α (e k)` is the chart-`α` reading of the frame and
`u̇` the chart velocity.  Every object on the right lives in the *fixed* chart
`α`, so — unlike the intrinsic left-hand side, whose vector slots are read at the
moving foot `γ τ` — the right-hand side is a candidate for continuity lemmas.

This is `curvatureFormAt_chartVectorRep` with the two velocity slots recognized
as the chart velocity (`chartVectorRep_velocity_of_geodesicAt`) and the curvature
packaged as the Jacobi endomorphism (`chartCurvatureEndo_apply`).

Blueprint: `lem:chart-curvature-coordinates`, `lem:jacobi-frame-reduction`. -/
theorem frameCurv_eq_chart {g : RiemannianMetric I M} {γ : ℝ → M}
    (e : Fin (Module.finrank ℝ E) → ℝ → E) {α : M} {τ : ℝ}
    (hgeo : Geodesic.HasGeodesicEquationAt (I := I) g γ τ)
    (hc : ContinuousAt γ τ) (hsrc : γ τ ∈ (chartAt H α).source)
    (i j : Fin (Module.finrank ℝ E)) :
    frameCurv (I := I) g γ e i j τ
      = - chartMetricInner (I := I) g α (extChartAt I α (γ τ))
          (chartCurvatureEndo (I := I) g α (extChartAt I α (γ τ))
            (deriv (fun s => extChartAt I α (γ s)) τ)
            (chartVectorRep (I := I) γ α (e j) τ))
          (chartVectorRep (I := I) γ α (e i) τ) := by
  have hvel : chartVectorRep (I := I) γ α (mfderivVelocity (I := I) (E := E) γ) τ
      = deriv (fun s => extChartAt I α (γ s)) τ :=
    chartVectorRep_velocity_of_geodesicAt (I := I) hgeo hc hsrc
  show curvatureFormAt g g.leviCivitaConnection (γ τ) (e j τ)
      (mfderivVelocity (I := I) (E := E) γ τ)
      (mfderivVelocity (I := I) (E := E) γ τ) (e i τ) = _
  rw [curvatureFormAt_chartVectorRep (I := I) g hsrc (e j)
      (mfderivVelocity (I := I) (E := E) γ) (mfderivVelocity (I := I) (E := E) γ) (e i),
    hvel]
  rfl

/-! ### Continuity inside one chart -/

/-- **Math.** **Continuity of the curvature coefficient on a single-chart
subinterval.**  If `γ([c,d])` lies in the source of the chart at `α`, then
`τ ↦ ℛᵢⱼ(τ)` is continuous on `[c, d]`.

All four factors of the fixed-chart formula are continuous there:

* `u = φ_α ∘ γ` and its derivative `u̇`, because `γ` is a geodesic (its chart
  reading solves the geodesic ODE, so `u̇` is continuous — `IsGeodesicOn.
  continuousAt_deriv_extChartAt`);
* the chart reading `Eₖ,α` of the parallel frame, because on this subinterval it
  satisfies the chart parallel ODE (`IsParallelAlongOn.isParallelSolOn_of_
  mem_source`), hence is differentiable, hence continuous — this is the *only*
  continuity a parallel field has, and it is exactly the one we need;
* the chart curvature endomorphism `ℛ_chart(u)(·, u̇, u̇)`, by
  `continuousOn_chartCurvatureEndo_comp` (Christoffel-symbol smoothness inside a
  chart);
* the chart Gram pairing, by `continuousOn_chartMetricInner_comp`. -/
theorem continuousOn_frameCurv_of_mem_source
    {g : RiemannianMetric I M} {γ : ℝ → M} {e : Fin (Module.finrank ℝ E) → ℝ → E}
    {a b : ℝ} (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {α : M} {c d : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (hsrc : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H α).source)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (frameCurv (I := I) g γ e i j) (Icc c d) := by
  set u : ℝ → E := fun τ => extChartAt I α (γ τ) with hu_def
  have hu_cont : ContinuousOn u (Icc c d) := by
    intro τ hτ
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc τ hτ)).comp (hγc τ (hsub hτ))).continuousWithinAt
  have hu'_cont : ContinuousOn (deriv u) (Icc c d) := fun τ hτ =>
    (hgeo.continuousAt_deriv_extChartAt (hsub hτ) (hγc τ (hsub hτ))
      (hsrc τ hτ)).continuousWithinAt
  have hmem : ∀ τ ∈ Icc c d, u τ ∈ interior (extChartAt I α).target := by
    intro τ hτ
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc τ hτ)
  -- the chart readings of the parallel frame are continuous
  have hrep : ∀ k, ContinuousOn (chartVectorRep (I := I) γ α (e k)) (Icc c d) := fun k =>
    ((hPar k).isParallelSolOn_of_mem_source hgeo hγc hsub hsrc).continuousOn
  -- the chart Jacobi endomorphism along the curve
  have hendo : ContinuousOn (fun τ => chartCurvatureEndo (I := I) g α (u τ) (deriv u τ))
      (Icc c d) := continuousOn_chartCurvatureEndo_comp (I := I) g α hu_cont hu'_cont hmem
  have hEj : ContinuousOn
      (fun τ => chartCurvatureEndo (I := I) g α (u τ) (deriv u τ)
        (chartVectorRep (I := I) γ α (e j) τ)) (Icc c d) := hendo.clm_apply (hrep j)
  have hG : ∀ τ ∈ Icc c d, ∀ p q,
      DifferentiableAt ℝ (chartGramOnE (I := I) g α p q) (u τ) := by
    intro τ hτ p q
    exact differentiableAt_chartGramOnE (I := I) g α
      ((extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc τ hτ)) p q
  have hmain : ContinuousOn (fun τ => - chartMetricInner (I := I) g α (u τ)
      (chartCurvatureEndo (I := I) g α (u τ) (deriv u τ)
        (chartVectorRep (I := I) γ α (e j) τ))
      (chartVectorRep (I := I) γ α (e i) τ)) (Icc c d) :=
    (continuousOn_chartMetricInner_comp hu_cont hEj (hrep i) hG).neg
  refine hmain.congr fun τ hτ => ?_
  exact frameCurv_eq_chart (I := I) e (hgeo τ (hsub hτ)) (hγc τ (hsub hτ)) (hsrc τ hτ) i j

/-! ### Continuity along a geodesic crossing arbitrarily many charts -/

/-- **Math.** **The curvature coefficient is continuous along the whole
geodesic.**  Continuity is a local property, and every time `t₀ ∈ [a, b]` has a
relative neighbourhood `[c, d]` whose `γ`-image lies in the single chart at
`γ t₀` (`γ` is continuous and `(chartAt H (γ t₀)).source` is an open
neighbourhood of `γ t₀`).  `continuousOn_frameCurv_of_mem_source` gives continuity
on each such `[c, d]`, and `ContinuousWithinAt.mono_of_mem_nhdsWithin` glues.

This is the last analytic ingredient of the `IsRadialJacobi` datum: the
coefficient matrix of the Jacobi system is continuous, hence (on a compact
interval) bounded, so the matrix Jacobi equation is a *bona fide* linear ODE.

Blueprint: `lem:geodesic-polar-form`(3), `lem:radial-shape-riccati`. -/
theorem continuousOn_frameCurv
    {g : RiemannianMetric I M} {γ : ℝ → M} {e : Fin (Module.finrank ℝ E) → ℝ → E}
    {a b : ℝ} (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (frameCurv (I := I) g γ e i j) (Icc a b) := by
  intro t ht
  -- a relative interval around `t` whose `γ`-image lies in the chart at `γ t`
  have hnhds : γ ⁻¹' (chartAt H (γ t)).source ∈ 𝓝 t :=
    (hγc t ht).preimage_mem_nhds
      ((chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  set c := max a (t - ε / 2) with hc
  set d := min b (t + ε / 2) with hd
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsrc : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H (γ t)).source := by
    intro τ hτ
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : t - ε / 2 ≤ τ := le_trans (le_max_right _ _) hτ.1
    have h2 : τ ≤ t + ε / 2 := le_trans hτ.2 (min_le_right _ _)
    have : |τ - t| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have htcd : t ∈ Icc c d :=
    ⟨max_le ht.1 (by linarith), le_min ht.2 (by linarith)⟩
  -- `[c, d]` is a relative neighbourhood of `t` in `[a, b]`
  have hnb : Icc c d ∈ 𝓝[Icc a b] t := by
    have hmem : Icc (t - ε / 2) (t + ε / 2) ∈ 𝓝 t :=
      Icc_mem_nhds (by linarith) (by linarith)
    have := inter_mem_nhdsWithin (Icc a b) hmem
    rwa [Icc_inter_Icc] at this
  exact ((continuousOn_frameCurv_of_mem_source hPar hgeo hγc hsub hsrc i j) t
    htcd).mono_of_mem_nhdsWithin hnb

/-- **Math.** On a compact interval the curvature coefficients are bounded: they
are continuous (`continuousOn_frameCurv`) on `[a, b]`. -/
theorem exists_bound_frameCurv
    {g : RiemannianMetric I M} {γ : ℝ → M} {e : Fin (Module.finrank ℝ E) → ℝ → E}
    {a b : ℝ} (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (i j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, ∀ t ∈ Icc a b, ‖frameCurv (I := I) g γ e i j t‖ ≤ C :=
  isCompact_Icc.exists_bound_of_continuousOn (continuousOn_frameCurv hPar hgeo hγc i j)

end PoincareLib

end
