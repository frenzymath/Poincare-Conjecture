/-
Chapter 4, "Connections", Problem 4-9: two connections and their difference tensor.

For two connections `∇⁰, ∇¹` in `TM`, Problem 4-9(a) relates their torsions to the
symmetry of their difference tensor `D(X, Y) = ∇¹_X Y − ∇⁰_X Y` (Proposition 4.13):

  `∇⁰` and `∇¹` have the same torsion  ⟺  `D` is symmetric, `D(X, Y) = D(Y, X)`.

The proof is the algebraic identity that the difference of the two torsions is the
antisymmetrization of the difference tensor: the Lie-bracket terms of the two
torsions cancel, leaving
`τ¹(X, Y) − τ⁰(X, Y) = D(Y, X) − D(X, Y)`
(`torsion_sub_eq_differenceTensor_antisymm`).  Both objects are the ones already
built in this chapter: `torsion` (Problem 4-6, via mathlib's `CovariantDerivative.torsion`)
and `differenceTensor` (Proposition 4.13, via `CovariantDerivative.difference`).
-/
import LeeLib.Ch04.DifferenceTensor
import LeeLib.Ch04.Torsion

namespace LeeLib.Ch04

open Bundle
open scoped Manifold ContDiff Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- The difference of the torsions of two connections is the antisymmetrization of their
difference tensor: `τ¹(X, Y) − τ⁰(X, Y) = D(Y, X) − D(X, Y)`, where `D(X, Y) = ∇¹_X Y − ∇⁰_X Y`
is `differenceTensor`.  The Lie-bracket `[X, Y]` terms of the two torsions cancel. -/
theorem torsion_sub_eq_differenceTensor_antisymm (cov cov' : TangentConnection I M)
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    torsion cov x (X x) (Y x) - torsion cov' x (X x) (Y x)
      = differenceTensor cov cov' x (Y x) (X x) - differenceTensor cov cov' x (X x) (Y x) := by
  rw [torsion_apply cov hX hY, torsion_apply cov' hX hY,
    differenceTensor_apply cov cov' X hY, differenceTensor_apply cov cov' Y hX]
  abel

/-- **Lee's Problem 4-9(a)**: two connections `∇⁰` and `∇¹` in `TM` have the same torsion
if and only if their difference tensor `D(X, Y) = ∇¹_X Y − ∇⁰_X Y` (Proposition 4.13) is
symmetric, `D(X, Y) = D(Y, X)` for all vector fields `X, Y` (differentiable at the point). -/
theorem sameTorsion_iff_differenceTensor_symm (cov cov' : TangentConnection I M) :
    (∀ {X Y : Π x : M, TangentSpace I x} {x : M},
        MDiffAt (T% X) x → MDiffAt (T% Y) x →
        torsion cov x (X x) (Y x) = torsion cov' x (X x) (Y x))
      ↔ (∀ {X Y : Π x : M, TangentSpace I x} {x : M},
        MDiffAt (T% X) x → MDiffAt (T% Y) x →
        differenceTensor cov cov' x (X x) (Y x) = differenceTensor cov cov' x (Y x) (X x)) := by
  constructor
  · intro h X Y x hX hY
    have hkey := torsion_sub_eq_differenceTensor_antisymm cov cov' hX hY
    rw [h hX hY, sub_self] at hkey
    exact (sub_eq_zero.mp hkey.symm).symm
  · intro h X Y x hX hY
    have hkey := torsion_sub_eq_differenceTensor_antisymm cov cov' hX hY
    rw [h hX hY, sub_self] at hkey
    exact sub_eq_zero.mp hkey

end LeeLib.Ch04
