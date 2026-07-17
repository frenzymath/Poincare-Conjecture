import PoincareLib.Ch01.SecondVariation
import PoincareLib.Ch01.ChartCurvature

/-!
# Poincaré Ch. 1 — the chart metric is compatible with the chart Christoffel symbols

`SecondVariation` proves the second variation of energy for an *abstract* pair
`(G, Γ)` — a point-dependent metric and connection coefficients — subject to
`IsMetricCompatibleAt`, `∂_X G(V, W) = G(Γ(X,V), W) + G(V, Γ(X,W))`.  This file
**discharges that hypothesis for the real chart data of a Riemannian manifold**, so
the second-variation identity is not an idealization: it applies verbatim to the
Levi-Civita connection in a chart.

* `chartMetricBilin` — the chart Gram matrix `G_{ij}` packaged as a
  continuous-bilinear-map-valued function of the chart point, the metric partner of
  `chartChristoffelBilin`;
* `isMetricCompatibleAt_chartMetricBilin` — `∇g = 0` in the chart, i.e.
  `IsMetricCompatibleAt (chartMetricBilin g α) (chartChristoffelBilin g α) y`,
  obtained from do Carmo's `hasDerivAt_chartMetricInner_along` by differentiating
  along the straight line `s ↦ y + s • X` (the direction `X` is arbitrary, so the
  Fréchet derivative is pinned down);
* `eventually_isMetricCompatibleAt_chartMetricBilin` — the neighbourhood form, which
  is what `secondVariation_energyDensity` actually consumes.

Blueprint: `thm:levi-civita-connection` (metric compatibility),
`claim:second-variation-minimal-geodesic`.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The chart metric as a bilinear-map-valued function -/

/-- **Math.** The chart Gram matrix packaged as a continuous-bilinear-form-valued
function of the chart point: `chartMetricBilin g α y a b = ∑_{i,j} G_{ij}(y) aⁱ bʲ`.
This is the metric partner of `chartChristoffelBilin`, and the `G` fed to the
second-variation engine. -/
def chartMetricBilin (g : RiemannianMetric I M) (α : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, ∑ j, chartGramOnE (I := I) g α i j y •
    ((Geodesic.chartCoordFunctional (E := E) i).smulRight
      (Geodesic.chartCoordFunctional (E := E) j))

/-- **Math.** The bilinear packaging agrees with OpenGALib's `chartMetricInner`. -/
theorem chartMetricBilin_apply (g : RiemannianMetric I M) (α : M) (y a b : E) :
    chartMetricBilin (I := I) g α y a b = chartMetricInner (I := I) g α y a b := by
  simp only [chartMetricBilin, chartMetricInner, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    Geodesic.chartCoordFunctional_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Math.** The chart metric is symmetric (`G_{ij} = G_{ji}`). -/
theorem chartMetricBilin_symm (g : RiemannianMetric I M) (α : M) (y a b : E) :
    chartMetricBilin (I := I) g α y a b = chartMetricBilin (I := I) g α y b a := by
  simp only [chartMetricBilin_apply, chartMetricInner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [chartGramOnE_symm (I := I) g α j i]
  ring

/-- **Math.** A finite sum of maps differentiable at `x` is differentiable at `x`.  Stated with
the summand family explicit, so that unification does not have to guess it (the
codomain here is a space of bilinear maps, where higher-order unification stalls). -/
theorem differentiableAt_finsum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] (A : ι → E → F) {y : E}
    (hA : ∀ i, DifferentiableAt ℝ (A i) y) :
    DifferentiableAt ℝ (fun z => ∑ i, A i z) y :=
  DifferentiableAt.fun_sum (fun i _ => hA i)

/-- **Math.** The Gram components are differentiable at an interior chart point.
(`JacobiManifold.differentiableAt_chartGramOnE` is the same fact on the whole chart
target, but assumes `I.Boundaryless`; the interior hypothesis here needs no such
assumption, keeping this file's hypotheses minimal.) -/
theorem differentiableAt_chartGramOnE_interior (g : RiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (i j : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y :=
  ((chartGramOnE_contDiffOn (I := I) g α i j).contDiffAt
    (mem_interior_iff_mem_nhds.mp hy)).differentiableAt (by norm_num)

/-- **Math.** Differentiability of the chart metric at an interior chart point. -/
theorem differentiableAt_chartMetricBilin (g : RiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartMetricBilin (I := I) g α) y := by
  have hinner : ∀ i : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z : E => ∑ j, chartGramOnE (I := I) g α i j z •
        ((Geodesic.chartCoordFunctional (E := E) i).smulRight
          (Geodesic.chartCoordFunctional (E := E) j))) y := by
    intro i
    refine differentiableAt_finsum
      (F := E →L[ℝ] E →L[ℝ] ℝ)
      (fun j => fun z : E => chartGramOnE (I := I) g α i j z •
        ((Geodesic.chartCoordFunctional (E := E) i).smulRight
          (Geodesic.chartCoordFunctional (E := E) j))) (fun j => ?_)
    -- `t ↦ t • C` for the fixed bilinear form `C = e^i.smulRight e^j` used to be built as
    -- its own continuous linear map `L : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)` and composed via
    -- `HasFDerivAt.comp`/`ContinuousLinearMap.hasFDerivAt`, but `ContinuousLinearMap.hasFDerivAt`
    -- needs `IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)`, which does not synthesize here — the same
    -- model-space instance diamond `contDiffOn_chartMetricBilin` below hits for `ContDiffOn.smul`.
    -- Same fix: push the scalar into the *codomain* via nested `smulRight` instead of `•`.
    have hrw : (fun z : E => chartGramOnE (I := I) g α i j z •
        ((Geodesic.chartCoordFunctional (E := E) i).smulRight
          (Geodesic.chartCoordFunctional (E := E) j)))
        = fun z => (Geodesic.chartCoordFunctional (E := E) i).smulRight
            ((Geodesic.chartCoordFunctional (E := E) j).smulRight
              (chartGramOnE (I := I) g α i j z)) := by
      funext z
      refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      ring
    simp only [hrw]
    exact (ContDiffAt.smulRight contDiffAt_const
      (ContDiffAt.smulRight contDiffAt_const
        ((chartGramOnE_contDiffOn (I := I) g α i j).contDiffAt
          (mem_interior_iff_mem_nhds.mp hy)))).differentiableAt (by norm_num)
  exact differentiableAt_finsum (F := E →L[ℝ] E →L[ℝ] ℝ) _ hinner

/-- **Math.** Differentiability of the scalar `z ↦ ⟨a, b⟩_z` at an interior chart point. -/
theorem differentiableAt_chartMetricInner_left (g : RiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) (a b : E) :
    DifferentiableAt ℝ (fun z => chartMetricInner (I := I) g α z a b) y := by
  unfold chartMetricInner
  have hinner : ∀ i : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun z : E => ∑ j, chartGramOnE (I := I) g α i j z *
        Geodesic.chartCoord (E := E) i a * Geodesic.chartCoord (E := E) j b) y := by
    intro i
    refine differentiableAt_finsum (F := ℝ)
      (fun j => fun z : E => chartGramOnE (I := I) g α i j z *
        Geodesic.chartCoord (E := E) i a * Geodesic.chartCoord (E := E) j b) (fun j => ?_)
    exact ((differentiableAt_chartGramOnE_interior (I := I) g α hy i j).mul_const _).mul_const _
  exact differentiableAt_finsum (F := ℝ) _ hinner

/-! ### Metric compatibility -/

/-- **Math.** **`∇g = 0` in a chart.**  The chart Christoffel symbols are
metric-compatible with the chart Gram matrix:

`(∂_X G)(V, W) = G(Γ(X, V), W) + G(V, Γ(X, W))`.

*Proof.*  Both sides are the derivative of `z ↦ ⟨V, W⟩_z` at `y` in the direction
`X`.  Feed the straight line `s ↦ y + s·X` (whose velocity is the constant `X`) and
the two *constant* fields `V`, `W` into do Carmo's metric-compatibility along a
curve, `hasDerivAt_chartMetricInner_along`: the covariant derivative of a constant
field along that line is exactly `Γ(X, ·)`, so the curve identity reads

`d/ds ⟨V, W⟩_{y+sX} |₀ = ⟨Γ(X,V), W⟩_y + ⟨V, Γ(X,W)⟩_y`,

and the left side is `(∂_X G)(V, W)` by the chain rule.  Since `X` is arbitrary this
pins down the full Fréchet derivative. ∎

This is the hypothesis `secondVariation_energyDensity` takes on abstract `(G, Γ)` —
discharged here for the genuine Levi-Civita data, which is what makes the
second-variation identity applicable rather than vacuous. -/
theorem isMetricCompatibleAt_chartMetricBilin (g : RiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (hbase : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsMetricCompatibleAt (chartMetricBilin (I := I) g α)
      (chartChristoffelBilin (I := I) g α) y := by
  intro X V W
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y :=
    fun i j => differentiableAt_chartGramOnE_interior (I := I) g α hy i j
  -- the straight line through `y` in the direction `X`
  set u : ℝ → E := fun s => y + s • X with hu
  have hline : HasDerivAt u X 0 := by
    have h : HasDerivAt (fun s : ℝ => s • X) X 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
    simpa [hu] using h.const_add y
  have hu0 : u 0 = y := by simp [hu]
  have hderivu : deriv u 0 = X := hline.deriv
  -- the covariant derivative of a *constant* field along the line is `Γ(X, ·)`
  have hcov : ∀ Z : E, covariantDerivCoord (I := I) g α u (fun _ => Z) 0
      = chartChristoffelBilin (I := I) g α y X Z := by
    intro Z
    rw [covariantDerivCoord, chartChristoffelBilin_apply, hderivu, hu0]
    simp
  -- do Carmo's metric compatibility along the line
  have hkey := hasDerivAt_chartMetricInner_along (I := I) g α u (fun _ => V) (fun _ => W)
    (t := 0) hline.differentiableAt (differentiableAt_const V) (differentiableAt_const W)
    (by rw [hu0]; exact hG) (by rw [hu0]; exact hbase)
  rw [hu0, hcov V, hcov W] at hkey
  -- the same derivative, read as a directional derivative of the chart metric
  have hdiffI : DifferentiableAt ℝ (fun z => chartMetricInner (I := I) g α z V W) y :=
    differentiableAt_chartMetricInner_left (I := I) g α hy V W
  have hchain : HasDerivAt (fun s => chartMetricInner (I := I) g α (u s) V W)
      (fderiv ℝ (fun z => chartMetricInner (I := I) g α z V W) y X) 0 := by
    have hg : HasFDerivAt (fun z => chartMetricInner (I := I) g α z V W)
        (fderiv ℝ (fun z => chartMetricInner (I := I) g α z V W) y) (u 0) := by
      rw [hu0]; exact hdiffI.hasFDerivAt
    simpa [Function.comp_def] using hg.comp_hasDerivAt 0 hline
  have hfd : fderiv ℝ (fun z => chartMetricInner (I := I) g α z V W) y X
      = chartMetricInner (I := I) g α y (chartChristoffelBilin (I := I) g α y X V) W
        + chartMetricInner (I := I) g α y V
          (chartChristoffelBilin (I := I) g α y X W) := hchain.unique hkey
  -- transfer from the scalar map to the bilinear-map-valued one
  have hev : fderiv ℝ (chartMetricBilin (I := I) g α) y X V W
      = fderiv ℝ (fun z => chartMetricInner (I := I) g α z V W) y X := by
    have hB : DifferentiableAt ℝ (chartMetricBilin (I := I) g α) y :=
      differentiableAt_chartMetricBilin (I := I) g α hy
    have h1 := hB.hasFDerivAt.clm_apply (hasFDerivAt_const V y)
    have h2 := h1.clm_apply (hasFDerivAt_const W y)
    have hfun : (fun z => chartMetricBilin (I := I) g α z V W)
        = fun z => chartMetricInner (I := I) g α z V W := by
      funext z
      exact chartMetricBilin_apply (I := I) g α z V W
    rw [← hfun, h2.fderiv]
    simp
  rw [hev, hfd, chartMetricBilin_apply, chartMetricBilin_apply]

/-- **Math.** The neighbourhood form of metric compatibility: on the interior of the
chart target (intersected with the trivialization base set, where the Gram matrix is
smooth and invertible) the chart data is compatible at *every* nearby point — which
is exactly what `secondVariation_energyDensity` consumes. -/
theorem eventually_isMetricCompatibleAt_chartMetricBilin (g : RiemannianMetric I M)
    (α : M) {y : E} (hy : y ∈ interior (extChartAt I α).target)
    (hbase : ∀ᶠ z in 𝓝 y,
      (extChartAt I α).symm z ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∀ᶠ z in 𝓝 y, IsMetricCompatibleAt (chartMetricBilin (I := I) g α)
      (chartChristoffelBilin (I := I) g α) z := by
  filter_upwards [isOpen_interior.mem_nhds hy, hbase] with z hz hbz
  exact isMetricCompatibleAt_chartMetricBilin (I := I) g α hz hbz

/-! ### Smoothness of the chart metric -/

/-- **Math.** The chart metric `G_{ij}` is `C^∞` on the chart target — the metric
partner of `contDiffOn_chartChristoffelBilin`, and the hypothesis `hG` of the
second-variation engine (`PieceSecondVariation`).  It is the chart Gram matrix, whose
entries `chartGramOnE` are smooth there, assembled into a bilinear form.

Note on the proof: `ContDiffOn.smul` is *unusable* on the codomain `E →L[ℝ] E →L[ℝ] ℝ`
here — `IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)` does not synthesize (the model-space
instance diamond).  So the coefficient is pushed into the *codomain* with `smulRight`,
writing `G_{ij}(y) • (e^i ⊗ e^j)` as `e^i.smulRight (e^j.smulRight (G_{ij} y))`, and
`contDiffOn_const.smulRight` applies — exactly the shape
`contDiffOn_chartChristoffelBilin` already uses. -/
theorem contDiffOn_chartMetricBilin (g : RiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (chartMetricBilin (I := I) g α) (extChartAt I α).target := by
  have hrw : chartMetricBilin (I := I) g α
      = fun y => ∑ i, ∑ j, (Geodesic.chartCoordFunctional (E := E) i).smulRight
          ((Geodesic.chartCoordFunctional (E := E) j).smulRight
            (chartGramOnE (I := I) g α i j y)) := by
    funext y
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
    simp only [chartMetricBilin, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      Geodesic.chartCoordFunctional_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrw]
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
  exact contDiffOn_const.smulRight
    (contDiffOn_const.smulRight (chartGramOnE_contDiffOn (I := I) g α i j))

end PoincareLib

end
