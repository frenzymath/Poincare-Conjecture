import PetersenLib.Ch02.CovariantDerivative

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.11 (gradient fields and self-adjointness)

Exercise 2.5.11: a vector field `X` is locally a gradient field iff the `(1,1)`
tensor `Z ↦ ∇_Z X` is self-adjoint.

The formalized declaration `exercise2_5_11` establishes the **forward direction**:
if `X = ∇f` is a gradient field, then `Z ↦ ∇_Z X` is self-adjoint,
`g(∇_U ∇f, V) = g(∇_V ∇f, U)`.  This is the self-adjointness of the Hessian, which
holds because `∇ df` is symmetric (`covariantDerivative_differential_symm`, from
torsion-freeness) and equals `g(∇ ∇f, ·)` (`covariantDerivative_differential_eq_gradient`,
Prop. 2.2.6).

The converse — that a field whose covariant derivative is self-adjoint is
*locally* a gradient field — is the Poincaré lemma (a closed `1`-form is locally
exact), which is not available in this development.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.11.
-/

open Bundle Set Function
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section
namespace PetersenLib
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [FiniteDimensional ℝ E]

/-- **Math.** Petersen §2.5, Exercise 2.5.11 (forward direction): for a gradient
field `X = ∇f`, the `(1,1)` tensor `Z ↦ ∇_Z X` is **self-adjoint** —
`g(∇_U ∇f, V) = g(∇_V ∇f, U)`.

The covariant derivative of the differential `∇ df` is symmetric (torsion-freeness,
`covariantDerivative_differential_symm`) and realizes the Hessian
`(∇ df)(U, V) = g(∇_U ∇f, V)` (Prop. 2.2.6,
`covariantDerivative_differential_eq_gradient`); symmetry of the former is exactly
self-adjointness of the latter. -/
theorem exercise2_5_11 [I.Boundaryless] [CompleteSpace E]
    {g : RiemannianMetric I M} (D : RiemannianConnection I g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hgradf : IsSmoothVectorField (gradient g f))
    {U V : Π x : M, TangentSpace I x}
    (hU : IsSmoothVectorField U) (hV : IsSmoothVectorField V) (p : M) :
    g.metricInner p (D.cov p (U p) (gradient g f)) (V p)
      = g.metricInner p (D.cov p (V p) (gradient g f)) (U p) := by
  rw [← covariantDerivative_differential_eq_gradient D U V hV hgradf p,
      ← covariantDerivative_differential_eq_gradient D V U hU hgradf p,
      covariantDerivative_differential_symm D hf hU hV p]

end PetersenLib
