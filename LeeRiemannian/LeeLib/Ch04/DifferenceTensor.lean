/-
Chapter 4, "Connections", §"Existence of Connections": the difference tensor and
the affine-space structure of the set of connections.

Although a connection is not a tensor field (it fails `C^∞(M)`-linearity in its
section argument, satisfying instead the product rule), Lee's Proposition 4.13
shows that the *difference* of two connections is:

  `D(X, Y) = ∇¹_X Y − ∇⁰_X Y`

is bilinear over `C^∞(M)`, hence a `(1,2)`-tensor field, the **difference tensor**
between `∇⁰` and `∇¹`.  Lee's Theorem 4.14 then identifies the set of all
connections in `TM` with the affine space `{∇⁰ + D : D ∈ Γ(T^{(1,2)}TM)}`.

Both facts are already available in mathlib's Koszul-connection theory:

* the difference tensor is `Bundle.CovariantDerivative.difference`, built through
  the tensoriality criterion `TensorialAt.mkHom`; `differenceTensor_apply` records
  Lee's defining formula `D(X, Y) = ∇¹_X Y − ∇⁰_X Y`.
* the affine action `∇⁰ + A` (for `A` an endomorphism-valued 1-form) is
  `Bundle.CovariantDerivative.addOneForm`, which always yields a connection; and
  every connection `∇` is recovered from a fixed `∇⁰` as
  `∇⁰ + (∇ − ∇⁰)` on smooth sections (`eq_addOneForm_difference`).

Together these give Lee's Theorem 4.14.  We state the affine characterization
pointwise on smooth sections: `CovariantDerivative.difference` is characterised
only on sections that are differentiable at the point, so `∇⁰ + (∇ − ∇⁰)` equals
`∇` on smooth sections, which is exactly Lee's affine-space statement for the
`(1,2)`-tensor `∇ − ∇⁰`.
-/
import LeeLib.Ch04.Connection

namespace LeeLib.Ch04

open Bundle
open scoped Manifold ContDiff Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]

/-- **Difference tensor** (Lee, Proposition 4.13): the difference `∇¹ − ∇⁰` of two
connections, as an endomorphism-valued 1-form `D x : V x →L[ℝ] T_x M →L[ℝ] V x`.
This is mathlib's `Bundle.CovariantDerivative.difference`; it is a genuine
`(1,2)`-tensor field because `D x` is a *continuous linear* (hence `C^∞(M)`-linear)
map in the section argument, in contrast to a connection itself. -/
noncomputable def differenceTensor (cov cov' : Connection I F V) :
    Π x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  CovariantDerivative.difference cov cov'

omit [IsManifold I 1 M] in
/-- Lee's Proposition 4.13, defining formula: `D(X, Y) = ∇¹_X Y − ∇⁰_X Y`.
Evaluated at a point `x` on a section `σ` differentiable there and a direction
`X`, the difference tensor is the difference of the two covariant derivatives. -/
theorem differenceTensor_apply (cov cov' : Connection I F V)
    (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) :
    differenceTensor cov cov' x (σ x) (X x)
      = covariantDeriv cov X σ x - covariantDeriv cov' X σ x := by
  unfold differenceTensor CovariantDerivative.difference
  rw [cov.isCovariantDerivativeOnUniv.difference_apply (s := Set.univ) cov'.isCovariantDerivativeOnUniv
    (Set.mem_univ x) hσ]
  simp [covariantDeriv]

/-- Lee's Theorem 4.14, one inclusion: adding an endomorphism-valued 1-form `A`
to a connection `∇⁰` yields a connection `∇⁰ + A`.  (This holds for *every* `A`,
by the type of `CovariantDerivative.addOneForm`.) -/
noncomputable def addOneForm (cov : Connection I F V)
    (A : Π x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x) : Connection I F V :=
  CovariantDerivative.addOneForm cov A

omit [IsManifold I 1 M] [FiniteDimensional ℝ F] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I] in
@[simp] theorem addOneForm_apply (cov : Connection I F V)
    (A : Π x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x) (σ : Π x : M, V x) (x : M) :
    addOneForm cov A σ x = cov σ x + A x (σ x) := rfl

omit [IsManifold I 1 M] in
/-- Lee's Theorem 4.14, other inclusion: every connection `∇` is the affine
translate `∇⁰ + (∇ − ∇⁰)` of any fixed connection `∇⁰` by the difference tensor.
Stated on smooth sections (where the difference tensor is characterised): for
every section `σ` differentiable at `x`,
`(∇⁰ + (∇ − ∇⁰))_X σ|_x = ∇_X σ|_x`. -/
theorem eq_addOneForm_differenceTensor (cov cov' : Connection I F V)
    (X : Π x : M, TangentSpace I x) {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) :
    covariantDeriv (addOneForm cov' (differenceTensor cov cov')) X σ x
      = covariantDeriv cov X σ x := by
  have hD := differenceTensor_apply cov cov' X hσ
  simp only [covariantDeriv_apply, addOneForm_apply, ContinuousLinearMap.add_apply]
  rw [hD, covariantDeriv_apply, covariantDeriv_apply]
  abel

end LeeLib.Ch04
