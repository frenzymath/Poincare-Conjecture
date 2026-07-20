import DoCarmoLib.Riemannian.Jacobi.JacobiSectionalCurvature
import DoCarmoLib.Riemannian.Jacobi.PairJacobiField
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureNaturality

/-!
# The intrinsic reading of the frame-coefficient curvature matrix (do Carmo Ch. 8, Thm. 2.1)

do Carmo, *Riemannian Geometry*, Ch. 8, Theorem 2.1 (E. Cartan) hypothesizes that the
curvature tensors of `M` and `M̃` correspond under the parallel-transport conjugation
`φ_t`:

  `⟨R(x,y)u,v⟩ = ⟨R̃(φ_t x, φ_t y) φ_t u, φ_t v⟩`   for all `x, y, u, v ∈ T_qM`,

and uses it through exactly one consequence: the two parallel orthonormal frames have
**equal frame-coefficient curvature matrices**,

  `⟨R(e_n, e_i) e_n, e_j⟩ = ⟨R̃(ẽ_n, ẽ_i) ẽ_n, ẽ_j⟩`,

which is what makes `J = Σ yᵢ eᵢ` and `J̃ = Σ yᵢ ẽᵢ` solve the *same* scalar ODE system
(`jacobiFrameTransfer`, whose `hmatch` hypothesis is precisely this equality).

The obstacle is that the two sides speak different languages.  `jacobiFrameTransfer`'s
`hmatch` is stated with `chartCurvatureEndo` and `chartMetricInner` — the **chart** layer,
where the Jacobi ODE actually runs — while do Carmo's hypothesis is about the **intrinsic**
curvature tensor `curvatureFormAt`.  The chart layer is what the ODE needs and the
intrinsic layer is what the hypothesis gives; nothing connected them off the diagonal.
(`chartMetricInner_chartCurvatureOp_eq_curvatureFormAt` does the `(w,w)`-diagonal case
only, and `chartMetricInner_chartCurvatureEndo_isConstantCurvature` collapses the whole
question by evaluating both sides — available only in constant curvature.)

This file supplies the missing converter, curvature-hypothesis-free:

* `chartMetricInner_chartCurvatureEndo_eq_curvatureFormAt` — the chart Jacobi operator
  paired against a chart vector *is* the intrinsic curvature form on the frame
  realizations of those chart vectors.  Two mathlib-adjacent facts already in the
  library do all the work: `curvatureFormAt_chartFrame` (the manifold↔chart curvature
  bridge, which carries a sign) and `curvatureFormAt_antisymm_fst` (antisymmetry in the
  first pair, which cancels it).
* `chartFrameRealize_tangentCoordChange` — the own-foot readback: realizing the chart
  reading `tangentCoordChange I q α q w` of `w ∈ T_qM` in the chart frame at `q` returns
  `w`.  The inverse of `chartVectorRep`, by the same cocycle chain as
  `chartMetricInner_chartVectorRep_eq_metricInner`.
* `chartMetricInner_chartCurvatureEndo_chartVectorRep_eq_curvatureFormAt` — the two
  composed: for **intrinsic** `v, a, b ∈ T_qM`, the chart-read frame coefficient equals
  `curvatureFormAt g q v a v b` exactly.  No frame realizations survive in the statement.
* `chartMetricInner_chartCurvatureEndo_transfer_of_curvatureFormAt` — **the payload**:
  for any `φ : T_qM → T_{q'}M̃` under which the curvature forms correspond (do Carmo's
  hypothesis, with `φ = φ_t`), the chart-read frame coefficients of `M` and `M̃` agree.
  This is `jacobiFrameTransfer`'s `hmatch`, discharged from the intrinsic hypothesis;
  `φ` is arbitrary, so no parallel-transport theory is needed here.

Note `φ` is *not* required to be linear, continuous, or an isometry: the correspondence
of the curvature forms is the entire content.  E. Cartan's `φ_t` supplies those extra
properties elsewhere in the proof (for the orthonormality of the transported frame, in
`CartanParallelFrame.lean`), not here.

## What this does not do

It does not prove `thm:dc-ch8-2-1`.  Feeding these coefficients to `jacobiFrameTransfer`
additionally needs the intrinsic frames of `CartanParallelFrame.lean` read in a fixed
chart, and the resulting frame-expanded Jacobi field identified with the intrinsic one —
the chart↔intrinsic interface for the Jacobi *pair* system, which is unbuilt.

Blueprint: `lem:dc-ch8-2-1-curvature-bridge`, `lem:dc-ch8-2-1-hmatch-transfer`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8, Thm. 2.1; Ch. 4, Lemma 3.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### The chart Jacobi operator is the intrinsic curvature form -/

/-- **Math.** **The chart-read frame coefficient is the intrinsic curvature form**
(do Carmo Ch. 8, Thm. 2.1: the coefficients `⟨R(e_n, e_i) e_n, e_j⟩`).

Pairing the chart Jacobi operator `ℛ(·, v)v = chartCurvatureEndo g α y v` against a
chart vector `b` under the chart Gram form gives the intrinsic curvature form
`R(v̂, â, v̂, b̂)` evaluated on the chart-frame realizations `v̂, â, b̂` of `v, a, b`.

Generalizes `chartMetricInner_chartCurvatureOp_eq_curvatureFormAt`, which handles only
the `(w, w)` diagonal, to arbitrary `a`, `b` — the off-diagonal entries do Carmo's
frame-coefficient matrix needs.  Unlike
`chartMetricInner_chartCurvatureEndo_isConstantCurvature`, it assumes **nothing** about
the curvature.

Proof: `chartCurvatureEndo_apply` turns the left side into
`⟨chartCurvature y a v v, b⟩`.  The manifold↔chart bridge `curvatureFormAt_chartFrame`
identifies `R(â, v̂, v̂, b̂)` with the *negative* of that, and antisymmetry in the first
pair (`curvatureFormAt_antisymm_fst`) turns `R(â, v̂, v̂, b̂)` into `-R(v̂, â, v̂, b̂)`.
The two signs cancel. -/
theorem chartMetricInner_chartCurvatureEndo_eq_curvatureFormAt (g : RiemannianMetric I M)
    (α : M) (v a b : E) {q : M} (hq : q ∈ (chartAt H α).source)
    {y : E} (hy : y = extChartAt I α q) :
    chartMetricInner (I := I) g α y (chartCurvatureEndo (I := I) g α y v a) b
      = g.leviCivitaConnection.curvatureFormAt g q
          (∑ i, Geodesic.chartCoord (E := E) i v • chartBasisVecFiber (I := I) α i q)
          (∑ i, Geodesic.chartCoord (E := E) i a • chartBasisVecFiber (I := I) α i q)
          (∑ i, Geodesic.chartCoord (E := E) i v • chartBasisVecFiber (I := I) α i q)
          (∑ i, Geodesic.chartCoord (E := E) i b • chartBasisVecFiber (I := I) α i q) := by
  subst hy
  rw [chartCurvatureEndo_apply]
  -- the manifold ↔ chart curvature bridge on the realizations of `(a, v, v, b)` — carries a sign
  have hbridge := curvatureFormAt_chartFrame (I := I) g hq a v v b
  -- antisymmetry in the first pair moves `a` past `v`, cancelling that sign
  have hanti := curvatureFormAt_antisymm_fst (I := I) g q
    (∑ i, Geodesic.chartCoord (E := E) i a • chartBasisVecFiber (I := I) α i q)
    (∑ i, Geodesic.chartCoord (E := E) i v • chartBasisVecFiber (I := I) α i q)
    (∑ i, Geodesic.chartCoord (E := E) i v • chartBasisVecFiber (I := I) α i q)
    (∑ i, Geodesic.chartCoord (E := E) i b • chartBasisVecFiber (I := I) α i q)
  linear_combination hbridge - hanti

/-! ### The own-foot readback -/

/-- **Math.** **Realizing a chart reading returns the vector.**  For `w ∈ T_qM`, the
chart-`α` reading `tangentCoordChange I q α q w` realized back in the chart frame at `q`
is `w` itself.  This is the inverse of `chartVectorRep`, and the companion of
`chartMetricInner_chartVectorRep_eq_metricInner` (which says the reading is
norm-faithful); it goes by the same cocycle chain
`(trivializationAt).symm → tangentCoordChange → tangentCoordChange_self`. -/
theorem chartFrameRealize_tangentCoordChange (α : M) {q : M} (hq : q ∈ (chartAt H α).source)
    (w : E) :
    ∑ i, Geodesic.chartCoord (E := E) i (tangentCoordChange I q α q w)
        • chartBasisVecFiber (I := I) α i q = w := by
  rw [← trivializationAt_symm_eq_sum_chartBasisVecFiber (I := I) α q,
    trivializationAt_symm_eq_tangentCoordChange (I := I) α hq,
    tangentCoordChange_realize_comp (I := I) (mem_chart_source H q) hq,
    tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) q)]

/-- **Math.** **The frame coefficient of intrinsic vectors.**  For `v, a, b ∈ T_qM`, the
chart-read frame coefficient built from their chart readings is exactly the intrinsic
curvature form `R(v, a, v, b)` — do Carmo's `⟨R(v, a) v, b⟩`, with no chart-frame
realizations left in the statement.

This is the composite of `chartMetricInner_chartCurvatureEndo_eq_curvatureFormAt` with
the readback `chartFrameRealize_tangentCoordChange`, and it is the form in which any
*intrinsic* curvature hypothesis can address `jacobiFrameTransfer`'s `hmatch`.

Blueprint: `lem:dc-ch8-2-1-curvature-bridge`. -/
theorem chartMetricInner_chartCurvatureEndo_chartVectorRep_eq_curvatureFormAt
    (g : RiemannianMetric I M) (α : M) {q : M} (hq : q ∈ (chartAt H α).source)
    (v a b : TangentSpace I q) :
    chartMetricInner (I := I) g α (extChartAt I α q)
        (chartCurvatureEndo (I := I) g α (extChartAt I α q)
          (tangentCoordChange I q α q v) (tangentCoordChange I q α q a))
        (tangentCoordChange I q α q b)
      = g.leviCivitaConnection.curvatureFormAt g q v a v b := by
  rw [chartMetricInner_chartCurvatureEndo_eq_curvatureFormAt (I := I) g α
    (tangentCoordChange I q α q v) (tangentCoordChange I q α q a)
    (tangentCoordChange I q α q b) hq rfl,
    chartFrameRealize_tangentCoordChange (I := I) α hq v,
    chartFrameRealize_tangentCoordChange (I := I) α hq a,
    chartFrameRealize_tangentCoordChange (I := I) α hq b]

/-! ### E. Cartan's hypothesis discharges `hmatch` -/

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [SigmaCompactSpace M'] [T2Space M']

/-- **Math.** **do Carmo Ch. 8, Thm. 2.1: the curvature hypothesis, converted.**

Let `φ : T_qM → T_{q'}M̃` be *any* map under which the curvature forms correspond,

  `R(x, y, z, w) = R̃(φx, φy, φz, φw)`   for all `x, y, z, w ∈ T_qM`

— E. Cartan's hypothesis, whose `φ` is the parallel-transport conjugation
`φ_t = P̃_t ∘ i ∘ P_t⁻¹`.  Then the **chart-read frame coefficients agree**: for all
`v, a, b ∈ T_qM`,

  `⟨ℛ(a, v) v, b⟩_chart = ⟨ℛ̃(φa, φv) φv, φb⟩_chart`.

Taking `v = γ'` and `a, b` the frame vectors, this is the **intrinsic content** of
`jacobiFrameTransfer`'s `hmatch` — the hypothesis that makes `J` and `J̃` solve the same
scalar ODE system, and hence the single point at which E. Cartan's curvature hypothesis is
consumed.  It is **not yet `hmatch` itself**: unifying the two forces three further
obligations, none of them about curvature, and none currently available —

* `φ(γ'(t)) = γ̃'(t)` (`hmatch`'s velocity slots are `deriv u t`, `deriv ubar t`), which
  needs `γ̃'(a) = i(γ'(a))`;
* `hmatch`'s frame vectors being the chart readings of *these* intrinsic frame vectors
  under *this* `φ`;
* `hmatch`'s sibling `hpar` (fixed chart, two-sided `deriv`) derived from
  `IsParallelFieldAlongOn` (per-`t` chart, `HasDerivWithinAt`).

See this file's header: that chart↔intrinsic interface for the Jacobi pair system is the
unbuilt residual of `thm:dc-ch8-2-1`.

`φ` is arbitrary: no linearity, continuity or isometry is used, and no parallel-transport
theory appears.  The extra structure of `φ_t` is needed elsewhere (orthonormality of the
transported frame, `exists_transportedParallelOrthoFrame`), not for the coefficients.

Proof: rewrite each side by
`chartMetricInner_chartCurvatureEndo_chartVectorRep_eq_curvatureFormAt` into the
intrinsic curvature forms, then apply the hypothesis at `(v, a, v, b)`.

Blueprint: `lem:dc-ch8-2-1-hmatch-transfer`. -/
theorem chartMetricInner_chartCurvatureEndo_transfer_of_curvatureFormAt
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M') (α : M) (α' : M')
    {q : M} (hq : q ∈ (chartAt H α).source) {q' : M'} (hq' : q' ∈ (chartAt H' α').source)
    (φ : TangentSpace I q → TangentSpace I' q')
    (hφ : ∀ x y z w : TangentSpace I q,
      g.leviCivitaConnection.curvatureFormAt g q x y z w
        = g'.leviCivitaConnection.curvatureFormAt g' q' (φ x) (φ y) (φ z) (φ w))
    (v a b : TangentSpace I q) :
    chartMetricInner (I := I) g α (extChartAt I α q)
        (chartCurvatureEndo (I := I) g α (extChartAt I α q)
          (tangentCoordChange I q α q v) (tangentCoordChange I q α q a))
        (tangentCoordChange I q α q b)
      = chartMetricInner (I := I') g' α' (extChartAt I' α' q')
        (chartCurvatureEndo (I := I') g' α' (extChartAt I' α' q')
          (tangentCoordChange I' q' α' q' (φ v)) (tangentCoordChange I' q' α' q' (φ a)))
        (tangentCoordChange I' q' α' q' (φ b)) := by
  rw [chartMetricInner_chartCurvatureEndo_chartVectorRep_eq_curvatureFormAt (I := I) g α hq v a b,
    chartMetricInner_chartCurvatureEndo_chartVectorRep_eq_curvatureFormAt (I := I') g' α' hq'
      (φ v) (φ a) (φ b)]
  exact hφ v a v b

end Riemannian.Jacobi

end
