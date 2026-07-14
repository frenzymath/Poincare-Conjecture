import PetersenLib.Ch01.RiemannianManifolds
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Petersen Ch. 1, §1.4.1–§1.4.3 — local representations of metrics

The Einstein summation convention (`einsteinSummationConvention`), the
coordinate representation `g = g_ij dx^i dx^j` of a metric in a chart
(`metricCoordinateComponents` and its expansion identity), the canonical
metric of Euclidean space in coordinates (`euclideanMetricCoordinates`),
and the frame representation `g = g_ij σ^i σ^j` relative to a pointwise
basis of the tangent space (`frameRepresentation`).

The chart-basis tangent sections (`chartBasisVecFiber`, `chartBasisVec`,
`chartBasisFamily`) are adapted from the shared OpenGALib infrastructure
(`OpenGALib/Riemannian/TensorBundle/SmoothOrthoFrame/ChartBasis.lean`,
identical in the openga and DoCarmo projects).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.4.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set FiberBundle Filter Module
open scoped Manifold Topology ContDiff Bundle

namespace PetersenLib

/-! ## Einstein summation convention (Petersen §1.4.1) -/

section Einstein

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Math.** Petersen §1.4.1 (Einstein summation convention): basis vectors
carry subscripts `e_i`, coefficients carry superscripts `v^i`, and a repeated
sub/superscript pair denotes a sum: `v = v^i e_i = ∑ᵢ v^i e_i`, where the
coefficients are `v^i = e^i(v)` for the dual basis `e^i`. In Lean the
convention is realized by the basis-expansion identity `v = ∑ i, (b.repr v i) • b i`,
with `b.repr · i` playing the role of the dual basis `e^i` (`dx^i` for a
coordinate basis). -/
theorem einsteinSummationConvention {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ V) (v : V) :
    ∑ i, b.repr v i • b i = v :=
  b.sum_repr v

end Einstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Chart-basis tangent sections

The coordinate vector fields `∂_i` of the chart at `α`, realized by
transporting a fixed basis of the model space `E` through the inverse of
the tangent trivialization centred at `α`. -/

section ChartBasis

/-- **Math.** The `i`-th coordinate tangent vector `∂_i|_b` of the chart at
`α`: image of the `i`-th model-space basis vector under the inverse of the
tangent trivialization centred at `α`; junk off the base set. -/
def chartBasisVecFiber (α : M) (i : Fin (Module.finrank ℝ E)) (b : M) :
    TangentSpace I b :=
  (trivializationAt E (TangentSpace I) α).symm b ((Module.finBasis ℝ E) i)

/-- **Math.** Section-form packaging of `chartBasisVecFiber α i`. -/
def chartBasisVec (α : M) (i : Fin (Module.finrank ℝ E)) :
    M → TotalSpace E (TangentSpace I : M → Type _) :=
  fun b => TotalSpace.mk' E b (chartBasisVecFiber (I := I) α i b)

/-- **Eng.** On the base set, the trivialization sends the chart-basis
vector to the constant model-basis vector. -/
lemma trivializationAt_chartBasisVec_snd
    (α : M) (i : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (trivializationAt E (TangentSpace I) α
        ⟨b, chartBasisVecFiber (I := I) α i b⟩).2
      = (Module.finBasis ℝ E) i := by
  have h := (trivializationAt E (TangentSpace I) α).apply_mk_symm hb
    ((Module.finBasis ℝ E) i)
  simpa [chartBasisVecFiber] using congrArg Prod.snd h

/-- **Math.** The coordinate vector fields are smooth on the base set of the
trivialization at `α`. -/
lemma chartBasisVec_contMDiffOn
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) α i)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) α)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun b => chartBasisVecFiber (I := I) α i b)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => (Module.finBasis ℝ E) i)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro b hb
  exact (trivializationAt_chartBasisVec_snd (I := I) α i hb)

/-- **Math.** At each point of the base set, the coordinate vectors
`∂_1|_b, …, ∂_n|_b` form a basis of `T_bM`. -/
def chartBasisFamily (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b) :=
  (Module.finBasis ℝ E).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((trivializationAt E (TangentSpace I) α).continuousLinearEquivAt ℝ b hb).symm)

lemma chartBasisFamily_apply (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisFamily (I := I) α hb i =
      chartBasisVecFiber (I := I) α i b := by
  unfold chartBasisFamily chartBasisVecFiber
  rw [Module.Basis.map_apply]
  rfl

end ChartBasis

/-! ## Coordinate representation of a metric (Petersen §1.4.2) -/

section CoordinateRepresentation

/-- **Math.** Petersen §1.4.2: the **local representation** `g_ij` of a
Riemannian metric in the chart at `α`: the positive-definite symmetric
matrix of functions `g_ij(x) = g(∂_i|_x, ∂_j|_x)`, so that
`g = g_ij dx^i dx^j` (see `metricCoordinateComponents_expansion`). -/
def metricCoordinateComponents (g : RiemannianMetric I M) (α x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.metricInner x (chartBasisVecFiber (I := I) α i x)
      (chartBasisVecFiber (I := I) α j x)

/-- **Math.** Symmetry `g_ij = g_ji` of the local representation. -/
theorem metricCoordinateComponents_symm (g : RiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    metricCoordinateComponents g α x i j = metricCoordinateComponents g α x j i :=
  g.metricInner_comm x _ _

/-- **Math.** Petersen §1.4.2, the identity `g = g_ij dx^i dx^j`: expanding
`v = dx^i(v) ∂_i` and `w = dx^j(w) ∂_j` in the coordinate basis (Einstein
convention, `einsteinSummationConvention`) and using bilinearity,
`g(v, w) = g_ij dx^i(v) dx^j(w)`, where `dx^i(v)` is the `i`-th coordinate of
`v` in the basis `∂_1, …, ∂_n`. -/
theorem metricCoordinateComponents_expansion (g : RiemannianMetric I M)
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v w : TangentSpace I x) :
    g.metricInner x v w =
      ∑ i, ∑ j,
        ((chartBasisFamily (I := I) α hx).repr v i) *
        ((chartBasisFamily (I := I) α hx).repr w j) *
        metricCoordinateComponents g α x i j := by
  set b := chartBasisFamily (I := I) α hx with hb
  conv_lhs => rw [← b.sum_repr v, ← b.sum_repr w]
  show (g.inner x (∑ i, b.repr v i • b i)) (∑ j, b.repr w j • b j) = _
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hentry : metricCoordinateComponents g α x i j = g.metricInner x (b i) (b j) := by
    rw [hb]
    simp only [metricCoordinateComponents, Matrix.of_apply, chartBasisFamily_apply]
  rw [hentry, RiemannianMetric.metricInner_apply]
  ring

/-- **Math.** Petersen Example 1.4.1: in the identity chart of Euclidean
space, `g_{ℝⁿ} = δ_ij dx^i dx^j`: the metric components relative to the
standard coordinate vector fields `∂_i = e_i` are the Kronecker delta. -/
theorem euclideanMetricCoordinates (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    (euclideanMetric n).metricInner x
      ((EuclideanSpace.basisFun (Fin n) ℝ) i : EuclideanSpace ℝ (Fin n))
      ((EuclideanSpace.basisFun (Fin n) ℝ) j : EuclideanSpace ℝ (Fin n)) =
      if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal i j
  simpa using h

end CoordinateRepresentation

/-! ## Frame representation of a metric (Petersen §1.4.3) -/

section FrameRepresentation

/-- **Math.** Petersen §1.4.3: the **frame representation** of a metric.
Relative to a frame `X_1, …, X_n` (a pointwise basis `b` of `T_xM`), the
metric is represented by the matrix `g_ij = g(X_i, X_j)`, so that
`g = g_ij σ^i σ^j` for the dual coframe `σ^i` (see
`frameRepresentation_expansion`). -/
def frameRepresentation (g : RiemannianMetric I M) {x : M} {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (TangentSpace I x)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => g.metricInner x (b i) (b j)

/-- **Math.** Symmetry `g_ij = g_ji` of the frame representation. -/
theorem frameRepresentation_symm (g : RiemannianMetric I M) {x : M} {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (TangentSpace I x)) (i j : Fin n) :
    frameRepresentation g b i j = frameRepresentation g b j i :=
  g.metricInner_comm x _ _

/-- **Math.** Petersen §1.4.3, the identity `g = g_ij σ^i σ^j`: for a frame
`X_i` with dual coframe `σ^i` (the coordinate functionals `b.repr · i`),
`g(v, w) = g(X_i, X_j) σ^i(v) σ^j(w)`. -/
theorem frameRepresentation_expansion (g : RiemannianMetric I M) {x : M} {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (TangentSpace I x)) (v w : TangentSpace I x) :
    g.metricInner x v w =
      ∑ i, ∑ j, (b.repr v i) * (b.repr w j) * frameRepresentation g b i j := by
  conv_lhs => rw [← b.sum_repr v, ← b.sum_repr w]
  show (g.inner x (∑ i, b.repr v i • b i)) (∑ j, b.repr w j • b j) = _
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show (b.repr w) j * ((b.repr v) i * (g.inner x (b i)) (b j))
      = (b.repr v) i * (b.repr w) j * (g.inner x (b i)) (b j)
  ring

/-- **Math.** For an orthonormal frame, `g = (σ^1)² + ⋯ + (σ^n)²`: the frame
representation is the identity matrix and the expansion collapses to the sum
of squares of the coframe. -/
theorem frameRepresentation_orthonormal (g : RiemannianMetric I M) {x : M} {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hb : ∀ i j, g.metricInner x (b i) (b j) = if i = j then 1 else 0)
    (v w : TangentSpace I x) :
    g.metricInner x v w = ∑ i, (b.repr v i) * (b.repr w i) := by
  rw [frameRepresentation_expansion g b v w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [show frameRepresentation g b i i = 1 by
      simpa using hb i i, mul_one]
  · intro j _ hj
    rw [show frameRepresentation g b i j = 0 by
      simpa [hj.symm] using hb i j, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end FrameRepresentation

end PetersenLib
