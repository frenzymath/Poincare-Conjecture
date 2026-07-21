/-
Chapter 4, "Connections", Problem 4-6: the torsion tensor of a connection.

Given a connection `∇` in the tangent bundle `TM`, Lee's Problem 4-6 defines the
**torsion** of `∇` to be the map

  `τ(X, Y) = ∇_X Y − ∇_Y X − [X, Y]`,

and asks one to show that (a) `τ` is a `(1,2)`-tensor field, and (b) `∇` is
*symmetric* (torsion-free) if and only if `∇_X Y − ∇_Y X = [X, Y]` for all vector
fields — equivalently, its coordinate connection coefficients are symmetric in
their lower indices.

Both facts are already available in mathlib's Koszul-connection theory
(`CovariantDerivative.torsion`, built through the bilinear tensoriality criterion
`TensorialAt.mkHom₂`).  This file records Lee's statements in the notation of this
chapter:

* `torsion` — Lee's torsion tensor `τ`, as an endomorphism-valued 1-form
  `τ x : T_x M →L[ℝ] T_x M →L[ℝ] T_x M` (a `(1,2)`-tensor field), aliasing
  `CovariantDerivative.torsion`.
* `torsion_apply` — the defining formula `τ(X, Y) = ∇_X Y − ∇_Y X − [X, Y]` (for
  vector fields differentiable at the point).
* `torsion_antisymm` — antisymmetry `τ(X, Y) = −τ(Y, X)`.
* `IsSymmetric` / `isSymmetric_iff` — Lee's Problem 4-6(b): `∇` is symmetric iff
  `∇_X Y − ∇_Y X = [X, Y]` for all differentiable `X, Y`.
-/
import LeeLib.Ch04.Connection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

namespace LeeLib.Ch04

open Bundle
open scoped Manifold ContDiff Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- **Torsion tensor** (Lee, Problem 4-6): `τ(X, Y) = ∇_X Y − ∇_Y X − [X, Y]`, as an
endomorphism-valued 1-form `τ x : T_x M →L[ℝ] T_x M →L[ℝ] T_x M`, i.e. a `(1,2)`-tensor
field on `M`.  Aliases mathlib's `CovariantDerivative.torsion`; it is a genuine tensor
field because `τ x` is *continuous bilinear*, in contrast to the connection itself. -/
noncomputable def torsion (cov : TangentConnection I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  cov.torsion x

/-- Lee's Problem 4-6 defining formula: `τ(X, Y) = ∇_X Y − ∇_Y X − [X, Y]`, for vector
fields `X, Y` differentiable at `x`. -/
theorem torsion_apply (cov : TangentConnection I M)
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    torsion cov x (X x) (Y x)
      = covariantDeriv cov X Y x - covariantDeriv cov Y X x - VectorField.mlieBracket I X Y x := by
  simpa [covariantDeriv, torsion] using cov.torsion_apply hX hY

/-- Lee's Problem 4-6: the torsion is antisymmetric, `τ(X, Y) = −τ(Y, X)`. -/
theorem torsion_antisymm (cov : TangentConnection I M) (x : M)
    (u v : TangentSpace I x) :
    torsion cov x u v = - torsion cov x v u :=
  cov.torsion_antisymm u v

/-- **Symmetric connection** (Lee, Problem 4-6): a connection in `TM` is *symmetric*
(torsion-free) if its torsion tensor vanishes identically. -/
def IsSymmetric (cov : TangentConnection I M) : Prop := cov.torsion = 0

/-- Lee's Problem 4-6(b): `∇` is symmetric if and only if `∇_X Y − ∇_Y X = [X, Y]`
for all vector fields `X, Y` differentiable at the point. -/
theorem isSymmetric_iff (cov : TangentConnection I M) :
    IsSymmetric cov ↔ ∀ {X Y : Π x : M, TangentSpace I x} {x : M},
      MDiffAt (T% X) x → MDiffAt (T% Y) x →
      covariantDeriv cov X Y x - covariantDeriv cov Y X x = VectorField.mlieBracket I X Y x := by
  simpa [covariantDeriv, IsSymmetric] using cov.torsion_eq_zero_iff

end LeeLib.Ch04
