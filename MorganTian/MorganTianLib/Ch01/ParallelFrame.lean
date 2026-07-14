import OpenGALib.Riemannian.Geodesic.CovariantDerivative

/-!
# Poincaré Ch. 1 — parallel frames along a coordinate curve

Morgan–Tian's Jacobi-field arguments (blueprint
`lem:exponential-differential-jacobi`, `lem:geodesic-polar-form`(3)) work in a
**parallel frame** along a geodesic: a family of vector fields `e i` along the
curve with `∇_{γ'} (e i) = 0`, whose pairwise inner products — hence
orthonormality — are preserved in time. This file provides that layer over
OpenGALib's chart-level covariant-derivative API
(`OpenGALib.Riemannian.Geodesic.CovariantDerivative`):

* `IsParallelSolOn g α u V a b` — `V` solves the parallel-transport ODE
  `V' = −Γ(u', V)(u)` along the coordinate curve `u` on `[a, b]`
  (one-sided derivatives at the endpoints; this is exactly the shape produced
  by OpenGALib's existence theorem `exists_isParallelCoord_Icc`);
* `exists_parallelFrame_Icc` — a parallel family with arbitrarily prescribed
  initial values `e₀ : ι → E` exists on `[a, b]`;
* `IsParallelSolOn.eqOn_of_left` — uniqueness given the initial value;
* `IsParallelSolOn.covariantDerivCoord_eq_zero` — at interior times the
  covariant derivative of a parallel field vanishes;
* `IsParallelSolOn.chartMetricInner_eq` — **metric compatibility**: the chart
  Gram inner product `⟨V(t), W(t)⟩_{u(t)}` of two parallel fields is constant
  on `[a, b]`;
* `chartMetricInner_parallelFrame_eq` — consequently a parallel frame
  preserves the full Gram matrix of its initial values; a frame that starts
  orthonormal stays orthonormal.

Blueprint: `lem:parallel-frame`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1;
do Carmo, *Riemannian Geometry*, Ch. 2, Prop. 2.6 and Ch. 3, Def. 3.1.
-/

open Set Riemannian
open scoped ContDiff Manifold Topology Bundle NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

/-! ### Constancy from a vanishing interior derivative -/

/-- **Math.** A real function continuous on `[a, b]` whose derivative vanishes
at every interior point is constant on `[a, b]`. (Endpoint-derivative-free
version of the vanishing-derivative constancy lemma.) -/
theorem eqOn_const_of_hasDerivAt_zero_interior {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) :
    ∀ t ∈ Icc a b, f t = f a := by
  have hdiff : DifferentiableOn ℝ f (interior (Icc a b)) := by
    rw [interior_Icc]
    exact fun t ht => ((hderiv t ht).differentiableAt).differentiableWithinAt
  have h0 : ∀ t ∈ interior (Icc a b), deriv f t = 0 := by
    rw [interior_Icc]
    exact fun t ht => (hderiv t ht).deriv
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff
    fun t ht => (h0 t ht).ge
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont hdiff
    fun t ht => (h0 t ht).le
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  exact le_antisymm (hanti ha ht ht.1) (hmono ha ht ht.1)

/-! ### Parallel fields along a coordinate curve -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The coordinate vector field `V` is **parallel along `u` on
`[a, b]`**: it solves the parallel-transport ODE `V' = −Γ(u', V)(u)` on
`[a, b]`, with one-sided derivatives at the endpoints. This is the
interval-relative counterpart of OpenGALib's global
`Riemannian.IsParallelCoord`, matching the shape produced by the existence
theorem `Riemannian.exists_isParallelCoord_Icc`.

Blueprint: `lem:parallel-frame`. -/
def IsParallelSolOn (g : RiemannianMetric I M) (α : M) (u V : ℝ → E) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, HasDerivWithinAt V
    (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t))
    (Icc a b) t

namespace IsParallelSolOn

variable {g : RiemannianMetric I M} {α : M} {u V W : ℝ → E} {a b : ℝ}

theorem continuousOn (h : IsParallelSolOn (I := I) g α u V a b) :
    ContinuousOn V (Icc a b) :=
  fun t ht => (h t ht).continuousWithinAt

/-- **Math.** At an interior time a parallel field is (two-sidedly)
differentiable. -/
theorem differentiableAt (h : IsParallelSolOn (I := I) g α u V a b) {t : ℝ}
    (ht : t ∈ Ioo a b) : DifferentiableAt ℝ V t :=
  ((h t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)).differentiableAt

/-- **Math.** At an interior time the covariant derivative `DV/dt` of a
parallel field vanishes: `V' = −Γ(u', V)(u)` says exactly
`DV/dt = V' + Γ(u', V)(u) = 0`. -/
theorem covariantDerivCoord_eq_zero (h : IsParallelSolOn (I := I) g α u V a b)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    covariantDerivCoord (I := I) g α u V t = 0 := by
  have hd := (h t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  rw [covariantDerivCoord_def, hd.deriv]
  exact neg_add_cancel _

/-- **Math.** Uniqueness of parallel transport: two fields parallel along `u`
on `[a, b]` that agree at `a` agree on `[a, b]` (Grönwall for the first-order
linear parallel-transport system). Blueprint: `lem:parallel-frame`. -/
theorem eqOn_of_left {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b,
      ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K)
    (hV : IsParallelSolOn (I := I) g α u V a b)
    (hW : IsParallelSolOn (I := I) g α u W a b) (ha : V a = W a) :
    EqOn V W (Icc a b) :=
  isParallelSol_eqOn_Icc (I := I) g α u hK hV hW ha

/-- **Math.** **Metric compatibility along the curve**: the chart Gram inner
product `⟨V(t), W(t)⟩_{u(t)}` of two parallel fields is constant on `[a, b]`.
The hypotheses ask that the curve be differentiable, the chart Gram
coefficients be differentiable along it, and the curve stay over the chart's
trivialization base set — all automatic for a smooth curve in the chart
domain. Blueprint: `lem:parallel-frame`. -/
theorem chartMetricInner_eq
    (hV : IsParallelSolOn (I := I) g α u V a b)
    (hW : IsParallelSolOn (I := I) g α u W a b)
    (hu : ∀ t ∈ Icc a b, DifferentiableAt ℝ u t)
    (hG : ∀ t ∈ Icc a b, ∀ i j,
      DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : ∀ t ∈ Icc a b, (extChartAt I α).symm (u t)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∀ t ∈ Icc a b, chartMetricInner (I := I) g α (u t) (V t) (W t)
      = chartMetricInner (I := I) g α (u a) (V a) (W a) := by
  have huc : ContinuousOn u (Icc a b) :=
    fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc a b) := hV.continuousOn
  have hWc : ContinuousOn W (Icc a b) := hW.continuousOn
  -- continuity of the inner-product curve
  have hfc : ContinuousOn
      (fun s => chartMetricInner (I := I) g α (u s) (V s) (W s)) (Icc a b) := by
    simp only [chartMetricInner_def]
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact fun t ht => ((hG t ht i j).continuousAt).comp_continuousWithinAt (huc t ht)
    · have := (Geodesic.chartCoordFunctional (E := E) i).continuous.comp_continuousOn hVc
      simpa [Function.comp_def, Geodesic.chartCoordFunctional_apply] using this
    · have := (Geodesic.chartCoordFunctional (E := E) j).continuous.comp_continuousOn hWc
      simpa [Function.comp_def, Geodesic.chartCoordFunctional_apply] using this
  -- the inner-product curve has vanishing derivative at interior times
  have hf0 : ∀ t ∈ Ioo a b, HasDerivAt
      (fun s => chartMetricInner (I := I) g α (u s) (V s) (W s)) 0 t := by
    intro t ht
    have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
    have hprod := hasDerivAt_chartMetricInner_along (I := I) g α u V W
      (hu t htI) (hV.differentiableAt ht) (hW.differentiableAt ht)
      (hG t htI) (hbase t htI)
    refine hprod.congr_deriv ?_
    rw [hV.covariantDerivCoord_eq_zero ht, hW.covariantDerivCoord_eq_zero ht]
    simp [chartMetricInner_def]
  exact eqOn_const_of_hasDerivAt_zero_interior hfc hf0

end IsParallelSolOn

/-- **Math.** **Existence of a parallel frame**: along a coordinate curve `u`
on `[a, b]` (with the parallel-transport coefficient continuous and bounded, as
for any `C¹` curve in the chart domain), for every family `e₀ : ι → E` of
initial vectors there is a family `e : ι → ℝ → E` of fields parallel along `u`
on `[a, b]` with `e i a = e₀ i`. Componentwise application of OpenGALib's
parallel-transport existence (`Riemannian.exists_isParallelCoord_Icc`).

Blueprint: `lem:parallel-frame`. -/
theorem exists_parallelFrame_Icc (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    {a b : ℝ} (hab : a ≤ b) {K : ℝ≥0}
    (hcont : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t))
      (Icc a b))
    (hK : ∀ t ∈ Icc a b,
      ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K)
    {ι : Type*} (e₀ : ι → E) :
    ∃ e : ι → ℝ → E, (∀ i, e i a = e₀ i)
      ∧ ∀ i, IsParallelSolOn (I := I) g α u (e i) a b := by
  choose e h1 h2 using fun i : ι =>
    exists_isParallelCoord_Icc (I := I) g α u hab (e₀ i) hcont hK
  exact ⟨e, h1, h2⟩

/-- **Math.** A parallel frame **preserves the Gram matrix** of its initial
values: for all `i, j` and `t ∈ [a, b]`,
`⟨e i (t), e j (t)⟩_{u(t)} = ⟨e i (a), e j (a)⟩_{u(a)}`. In particular a frame
that starts orthonormal for the chart Gram inner product stays orthonormal
along the curve. Blueprint: `lem:parallel-frame`. -/
theorem chartMetricInner_parallelFrame_eq {g : RiemannianMetric I M} {α : M}
    {u : ℝ → E} {a b : ℝ} {ι : Type*} {e : ι → ℝ → E}
    (he : ∀ i, IsParallelSolOn (I := I) g α u (e i) a b)
    (hu : ∀ t ∈ Icc a b, DifferentiableAt ℝ u t)
    (hG : ∀ t ∈ Icc a b, ∀ i j,
      DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : ∀ t ∈ Icc a b, (extChartAt I α).symm (u t)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∀ i j, ∀ t ∈ Icc a b,
      chartMetricInner (I := I) g α (u t) (e i t) (e j t)
        = chartMetricInner (I := I) g α (u a) (e i a) (e j a) :=
  fun i j => (he i).chartMetricInner_eq (he j) hu hG hbase

end MorganTianLib

end
