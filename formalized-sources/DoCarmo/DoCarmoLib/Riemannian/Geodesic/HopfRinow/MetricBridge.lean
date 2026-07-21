import DoCarmoLib.Riemannian.Geodesic.CovariantDerivative
import DoCarmoLib.Riemannian.Metric.RiemannianDistance

/-!
# Bridging the chart-Gram inner product to the intrinsic metric (do Carmo Ch. 7 §2 / Ch. 3 §2)

This file connects two descriptions of the Riemannian inner product that the
Hopf–Rinow constant-speed layer needs to compare:

* the **chart-local Gram inner product** `chartMetricInner g α y a c`, which pairs
  coordinate vectors `a, c : E` through the chart Gram matrix `chartGramOnE` at the
  chart image `y`; and
* the **intrinsic inner product** `g.metricInner b V W` of the trivialization
  readbacks `V = (trivializationAt E (TangentSpace I) α).symm b a`,
  `W = (trivializationAt E (TangentSpace I) α).symm b c` of those coordinate
  vectors into the fibre `T_bM`.

The core statement `chartMetricInner_extChartAt_eq_metricInner` shows these agree at
`y = extChartAt I α b`, so the coordinate speed `chartMetricInner g α (φ_α c t) c' c'`
of a curve is literally the intrinsic squared speed `g.metricInner (c t) c' c'`.

Finally, under the `Bundle.RiemannianBundle` instance carried by `g`, the fibre
`(e)norm` of a tangent vector is `√ (g.metricInner x v v)`
(`norm_tangent_eq_sqrt_metricInner` / `enorm_tangent_eq_sqrt_metricInner`), the last
link needed to identify `Manifold.pathELength` of a chart curve with its coordinate
length.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §2 (distance/length) and Ch. 3 §2.
-/

open scoped Manifold Topology ContDiff ENNReal
open Set Bundle


noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Readback expansion: the inverse trivialization at `α`, applied at a
foot `b` to a coordinate vector `a : E`, is the linear combination of chart-basis
fibre vectors with the chart coordinates of `a`. Holds unconditionally: off the base
set both sides are the junk-zero readback. -/
theorem trivializationAt_symm_eq_sum_chartBasisVecFiber (α : M) (b : M) (a : E) :
    (trivializationAt E (TangentSpace I) α).symm b a
      = ∑ i, Geodesic.chartCoord (E := E) i a • Tensor.chartBasisVecFiber (I := I) α i b := by
  rw [← Bundle.Trivialization.coe_symmₗ (R := ℝ) (trivializationAt E (TangentSpace I) α) b]
  conv_lhs => rw [← Module.Basis.sum_repr (Module.finBasis ℝ E) a]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Bilinear expansion of the intrinsic metric against two readbacks:
`g_b(e.symm b a, e.symm b c) = ∑ᵢⱼ G_{ij}(b) aⁱ cʲ`, where `G` is the chart Gram
matrix. -/
theorem metricInner_trivializationAt_symm (g : RiemannianMetric I M) (α : M) (b : M) (a c : E) :
    g.metricInner b ((trivializationAt E (TangentSpace I) α).symm b a)
        ((trivializationAt E (TangentSpace I) α).symm b c)
      = ∑ i, ∑ j, Tensor.chartGramMatrix (I := I) g α b i j
          * Geodesic.chartCoord (E := E) i a * Geodesic.chartCoord (E := E) j c := by
  rw [trivializationAt_symm_eq_sum_chartBasisVecFiber,
    trivializationAt_symm_eq_sum_chartBasisVecFiber]
  simp only [RiemannianMetric.metricInner_apply, map_sum, ContinuousLinearMap.sum_apply,
    map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Tensor.chartGramMatrix_apply]
  ring

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart-Gram inner product equals the intrinsic inner product of the
readbacks, at the chart image `extChartAt I α b` of a foot `b` in the chart source. -/
theorem chartMetricInner_extChartAt_eq_metricInner (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (chartAt H α).source) (a c : E) :
    chartMetricInner (I := I) g α (extChartAt I α b) a c
      = g.metricInner b ((trivializationAt E (TangentSpace I) α).symm b a)
          ((trivializationAt E (TangentSpace I) α).symm b c) := by
  rw [metricInner_trivializationAt_symm]
  have hsrc : b ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hb
  have hinv : (extChartAt I α).symm (extChartAt I α b) = b := (extChartAt I α).left_inv hsrc
  simp only [chartMetricInner_def, chartGramOnE_def, hinv]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** General foot version of the readback in terms of the tangent
coordinate change: over a foot `b` in the chart source, the inverse trivialization
at `α` is `tangentCoordChange I α b b`. -/
theorem trivializationAt_symm_eq_tangentCoordChange (α : M) {b : M}
    (hb : b ∈ (chartAt H α).source) (a : E) :
    (trivializationAt E (TangentSpace I) α).symm b a = tangentCoordChange I α b b a := by
  have h := TangentBundle.symmL_trivializationAt_eq_core (I := I) (b₀ := α) (b := b) hb
  rw [show (trivializationAt E (TangentSpace I) α).symm b a
        = (trivializationAt E (TangentSpace I) α).symmL ℝ b a from rfl, h]
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** At the basepoint the readback is the identity: the inverse
trivialization at `α`, evaluated over its own foot `α`, is the identity of the fibre. -/
theorem trivializationAt_symm_self (α : M) (a : E) :
    (trivializationAt E (TangentSpace I) α).symm α a = a := by
  rw [trivializationAt_symm_eq_tangentCoordChange α (mem_chart_source H α) a]
  exact tangentCoordChange_self (I := I) (x := α) (z := α) (v := a) (mem_extChartAt_source α)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Fibre norm under the Riemannian-bundle instance of `g`:
`‖v‖ = √ (g_x(v,v))`. -/
theorem norm_tangent_eq_sqrt_metricInner (g : RiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ‖v‖ = Real.sqrt (g.metricInner x v v) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [norm_eq_sqrt_real_inner v]
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Fibre enorm under the Riemannian-bundle instance of `g`:
`‖v‖ₑ = ENNReal.ofReal (√ (g_x(v,v)))`. -/
theorem enorm_tangent_eq_sqrt_metricInner (g : RiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner x v v)) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [← ofReal_norm_eq_enorm, norm_tangent_eq_sqrt_metricInner]

/-! ### Change of chart for the Gram data

The chart Gram matrix transforms as a `(0,2)`-tensor under a change of chart
basepoint: `G^β_{ij}(x) = ∑_{ab} G^α_{ab}(x) A^a_i A^b_j` with
`A = tangentCoordChange I β α x` the derivative of the chart transition at `x`.
This is the zeroth-order layer of the change-of-chart law for
`chartChristoffel` (the full law follows by differentiating this identity in
the chart coordinate, which brings in the second derivative of the
transition). -/

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The β-chart frame vector at a common foot `x` is the α-readback of
the tangent coordinate change of the model basis vector: the two chart frames of
`T_xM` differ by the derivative of the chart transition. -/
theorem chartBasisVecFiber_eq_symm_tangentCoordChange (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (i : Fin (Module.finrank ℝ E)) :
    Tensor.chartBasisVecFiber (I := I) β i x
      = (trivializationAt E (TangentSpace I) α).symm x
          (tangentCoordChange I β α x ((Module.finBasis ℝ E) i)) := by
  have hα : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hxα
  have hβ : x ∈ (extChartAt I β).source := by rw [extChartAt_source]; exact hxβ
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  rw [show Tensor.chartBasisVecFiber (I := I) β i x
      = (trivializationAt E (TangentSpace I) β).symm x ((Module.finBasis ℝ E) i) from rfl,
    trivializationAt_symm_eq_tangentCoordChange β hxβ,
    trivializationAt_symm_eq_tangentCoordChange α hxα,
    tangentCoordChange_comp (I := I) ⟨⟨hβ, hα⟩, hx⟩]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Change of chart for the Gram matrix** (`(0,2)`-tensor
transformation law, the zeroth-order layer of the Christoffel change-of-chart
law): at a common foot `x`,
`G^β_{ij}(x) = ∑_{ab} G^α_{ab}(x)\,A^a_i\,A^b_j` with
`A = tangentCoordChange I β α x`. -/
theorem chartGramMatrix_change (g : RiemannianMetric I M) (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (i j : Fin (Module.finrank ℝ E)) :
    Tensor.chartGramMatrix (I := I) g β x i j
      = ∑ a, ∑ b, Tensor.chartGramMatrix (I := I) g α x a b
          * Geodesic.chartCoord (E := E) a
              (tangentCoordChange I β α x ((Module.finBasis ℝ E) i))
          * Geodesic.chartCoord (E := E) b
              (tangentCoordChange I β α x ((Module.finBasis ℝ E) j)) := by
  rw [← metricInner_trivializationAt_symm g α x,
    ← chartBasisVecFiber_eq_symm_tangentCoordChange α β hxα hxβ i,
    ← chartBasisVecFiber_eq_symm_tangentCoordChange α β hxα hxβ j]
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Change of chart for the chart-Gram inner product**: reading the
same foot `x` in two charts, the β-chart Gram pairing of two coordinate vectors
is the α-chart Gram pairing of their tangent coordinate changes — the pairing
is the same intrinsic inner product on `T_xM` in two frames. -/
theorem chartMetricInner_change (g : RiemannianMetric I M) (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) (a c : E) :
    chartMetricInner (I := I) g β (extChartAt I β x) a c
      = chartMetricInner (I := I) g α (extChartAt I α x)
          (tangentCoordChange I β α x a) (tangentCoordChange I β α x c) := by
  have hα : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hxα
  have hβ : x ∈ (extChartAt I β).source := by rw [extChartAt_source]; exact hxβ
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  rw [chartMetricInner_extChartAt_eq_metricInner g β hxβ,
    chartMetricInner_extChartAt_eq_metricInner g α hxα,
    trivializationAt_symm_eq_tangentCoordChange β hxβ,
    trivializationAt_symm_eq_tangentCoordChange β hxβ,
    trivializationAt_symm_eq_tangentCoordChange α hxα,
    trivializationAt_symm_eq_tangentCoordChange α hxα,
    tangentCoordChange_comp (I := I) ⟨⟨hβ, hα⟩, hx⟩,
    tangentCoordChange_comp (I := I) ⟨⟨hβ, hα⟩, hx⟩]

end Riemannian
