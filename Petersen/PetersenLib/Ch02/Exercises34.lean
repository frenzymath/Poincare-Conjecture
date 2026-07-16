import PetersenLib.Ch02.CovariantAdjoint
import PetersenLib.Ch02.IndexNotation

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.34: index notation for the covariant derivative

Petersen §2.4 writes `∇_i T` for the covariant derivative in the direction of the
`i`-th coordinate field and `∇^i T = g^{ij} ∇_j T` for its metric-raised form.
Against a positively oriented **orthonormal** frame `E_1, …, E_n` near `x` (the
standing frame hypothesis of the divergence and its adjoint) the raised index
`∇^i = g^{ij}∇_j` collapses to `∇_i`, and the three identities of Exercise 2.5.34
read:

* **(1)** for a function `f`, `df = ∇_i f\, σ^i` and `∇f = ∇^i f\, E_i` — the
  `1`-form `df` and the gradient `∇f` expand in the (co)frame with coefficients
  `∇_i f = E_i(f)` (`exercise2_5_34_differential`, `exercise2_5_34_gradient`);
* **(2)** for a vector field `X`, `(∇_i X)^i = \operatorname{div} X`, i.e. the
  trace `Σᵢ g(∇_{E_i}X, E_i)` of the covariant derivative is the divergence
  (`exercise2_5_34_divergence`, from `divergence_trace_formula` and the pairing
  identity `g(∇_{E_i}X, E_i) = ½(L_X g)(E_i, E_i)`);
* **(3)** for a `(0,2)`-tensor `T`, `(∇^i T)_{ij} = -(∇^* T)_j`, i.e. the metric
  trace over the first slot is minus the adjoint of the covariant derivative
  (`exercise2_5_34_adjoint`, immediate from the definition of
  `covariantDerivativeAdjoint`).

The `\lean{PetersenLib.exercise2_5_34}` node bundles the four identities against a
common orthonormal frame.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.4, Exercise 2.5.34.
-/

open Bundle Set Function Finset Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section IndexNotation

variable [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [hm : HasMetric I M]

/-- **Math.** **Exercise 2.5.34(1), gradient.** In index notation `∇f =
∇^i f\, E_i`: against a frame orthonormal at `x`, the gradient expands in the
frame with coefficients `∇^i f = ∇_i f = E_i(f)`,
`∇f = Σᵢ (E_i f)·E_i`.  Immediate from the orthonormal expansion of the vector
`∇f`, since `g(∇f, E_i) = df(E_i) = E_i f`. -/
theorem exercise2_5_34_gradient
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (f : M → ℝ) :
    gradient hm.metric f x = ∑ i, directionalDerivative (Efr i) f x • Efr i x := by
  conv_lhs => rw [metricInner_orthonormal_expansion (horth x (mem_of_mem_nhds hU))
    (gradient hm.metric f x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [metricInner_gradient, ← directionalDerivative_apply]

/-- **Math.** **Exercise 2.5.34(1), differential.** In index notation `df =
∇_i f\, σ^i`: against a frame orthonormal at `x`, the differential `df` expands
in the dual coframe `σ^i = g(E_i, ·)` with coefficients `∇_i f = E_i(f)`,
`df(Y) = Σᵢ (E_i f)·g(E_i, Y)`.  Derived from the gradient expansion via
`df(Y) = g(∇f, Y)`. -/
theorem exercise2_5_34_differential
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (f : M → ℝ) (Y : Π q : M, TangentSpace I q) :
    directionalDerivative Y f x
      = ∑ i, directionalDerivative (Efr i) f x * hm.metric.metricInner x (Efr i x) (Y x) := by
  rw [directionalDerivative_apply, ← metricInner_gradient hm.metric f x (Y x),
    exercise2_5_34_gradient hU horth f, hasMetric_metricInner_eq_inner, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, ← hasMetric_metricInner_eq_inner]

/-- **Math.** **Exercise 2.5.34(2).** In index notation `(∇_i X)^i =
\operatorname{div} X`: against a positively oriented normalized orthonormal frame
near `x`, the metric trace of the covariant derivative is the divergence,
`Σᵢ g(∇_{E_i}X, E_i) = \operatorname{div} X`. -/
theorem exercise2_5_34_divergence
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (D : RiemannianConnection I hm.metric)
    {X : Π q : M, TangentSpace I q} (hX : IsSmoothVectorField X)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    ∑ i, hm.metric.metricInner x (D.cov x (Efr i x) X) (Efr i x)
      = divergenceLieDerivative o X x := by
  rw [divergence_trace_formula o X hEs hU horth hvol]
  exact Finset.sum_congr rfl fun i _ =>
    RiemannianConnection.metricInner_cov_self_eq_half_lie D hX (hEs i) x

/-- **Math.** **Exercise 2.5.34(3).** In index notation `(∇^i T)_{ij} =
-(∇^* T)_j`: for a `(0,2)`-tensor `T` and any field `W`, the trace of the
covariant derivative over the first slot is minus the adjoint,
`Σᵢ (∇_{E_i}T)(E_i, W) = -(∇^* T)(W)`.  This is the defining formula of
`covariantDerivativeAdjoint`. -/
theorem exercise2_5_34_adjoint
    (D : RiemannianConnection I hm.metric)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (T : TensorOperator I M 2) (W : Π q : M, TangentSpace I q) (x : M) :
    ∑ i, covariantDerivativeTensor D.toAffineConnection (Efr i) T ![Efr i, W] x
      = -covariantDerivativeAdjoint D.toAffineConnection Efr T ![W] x := by
  rw [covariantDerivativeAdjoint_apply, neg_neg]
  rfl

/-- **Math.** **Exercise 2.5.34** (Petersen §2.4): the index-notation identities
for the covariant derivative, bundled against a positively oriented normalized
orthonormal frame `E_1, …, E_n` near `x`.  For a function `f`:
`(1)` `df = ∇_i f\, σ^i` and `∇f = ∇^i f\, E_i`; for a vector field `X`:
`(2)` `(∇_i X)^i = \operatorname{div} X`; for a `(0,2)`-tensor `T`:
`(3)` `(∇^i T)_{ij} = -(∇^* T)_j`. -/
theorem exercise2_5_34
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (finrank ℝ E)))
    (D : RiemannianConnection I hm.metric)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1)
    (f : M → ℝ) {X : Π q : M, TangentSpace I q} (hX : IsSmoothVectorField X)
    (T : TensorOperator I M 2) (Y W : Π q : M, TangentSpace I q) :
    (directionalDerivative Y f x
        = ∑ i, directionalDerivative (Efr i) f x * hm.metric.metricInner x (Efr i x) (Y x))
      ∧ (gradient hm.metric f x = ∑ i, directionalDerivative (Efr i) f x • Efr i x)
      ∧ (∑ i, hm.metric.metricInner x (D.cov x (Efr i x) X) (Efr i x)
          = divergenceLieDerivative o X x)
      ∧ (∑ i, covariantDerivativeTensor D.toAffineConnection (Efr i) T ![Efr i, W] x
          = -covariantDerivativeAdjoint D.toAffineConnection Efr T ![W] x) :=
  ⟨exercise2_5_34_differential hU horth f Y,
    exercise2_5_34_gradient hU horth f,
    exercise2_5_34_divergence o D hX hEs hU horth hvol,
    exercise2_5_34_adjoint D T W x⟩

end IndexNotation

end PetersenLib

end
