import PetersenLib.Ch02.CovariantDerivative

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.30 (parallel distributions are involutive)

A **distribution** on `M` is a choice of subspace `Dist x ⊆ T_xM` at each point.
It is **parallel** for a connection `∇` if `∇_X Y` stays tangent to it whenever
`X, Y` are.  Exercise 2.5.30 considers a pair of orthogonal-complement
distributions, each parallel, and asks to show they are integrable and that `M`
splits locally as a Riemannian product.

The reachable, purely algebraic core is that **each** parallel distribution is
**involutive**: if `X, Y` are tangent to a parallel distribution then so is
`[X, Y]`.  This is immediate from torsion-freeness of the Levi-Civita connection,
`[X, Y] = ∇_X Y − ∇_Y X`: both terms lie in the distribution (parallelism), and a
subspace is closed under subtraction.  Involutivity is the local obstruction that
Frobenius' theorem converts into integrability.

## Design notes

* The orthogonal-complement relationship between the two distributions plays no
  role in involutivity — each parallel distribution is individually involutive —
  so the formalization treats a single distribution `Dist`.
* The remaining content of the exercise — Frobenius' theorem (involutive ⟹
  integrable) and the product-metric splitting `(U, g) = (V_E × V_F, g|_E + g|_F)`
  — needs the Frobenius / integral-manifold machinery, not available in Mathlib's
  manifold API, and is not formalized here.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.30.
-/

open Bundle Set Function
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A vector field `X` is **tangent** to the distribution `Dist`
(`Dist x ⊆ T_xM` a subspace at each point) if `X|_x ∈ Dist x` for every `x`. -/
def IsTangentTo (Dist : Π x : M, Submodule ℝ (TangentSpace I x))
    (X : Π x : M, TangentSpace I x) : Prop :=
  ∀ x, X x ∈ Dist x

/-- **Math.** A distribution `Dist` is **parallel** for the affine connection
`∇` (Petersen §2.5) if `∇_X Y` is tangent to `Dist` whenever `X, Y` are: for
smooth `X, Y` tangent to `Dist`, `∇_{X|_p} Y ∈ Dist p` for all `p`. -/
def IsParallelDistribution (D : AffineConnection I M)
    (Dist : Π x : M, Submodule ℝ (TangentSpace I x)) : Prop :=
  ∀ ⦃X Y : Π x : M, TangentSpace I x⦄, IsSmoothVectorField X → IsSmoothVectorField Y →
    IsTangentTo Dist X → IsTangentTo Dist Y → ∀ p : M, D.cov p (X p) Y ∈ Dist p

/-- **Math.** A parallel distribution (for a torsion-free/Riemannian connection)
is **involutive**: the bracket `[X, Y]` of two tangent fields is again tangent.
By torsion-freeness `[X, Y] = ∇_X Y − ∇_Y X`; both terms lie in the distribution
by parallelism, and a subspace is closed under subtraction. -/
theorem IsParallelDistribution.involutive {g : RiemannianMetric I M}
    (D : RiemannianConnection I g)
    {Dist : Π x : M, Submodule ℝ (TangentSpace I x)}
    (hDist : IsParallelDistribution D.toAffineConnection Dist)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hXE : IsTangentTo Dist X) (hYE : IsTangentTo Dist Y) (p : M) :
    lieDerivativeVectorField I X Y p ∈ Dist p := by
  rw [← D.torsion_free hX hY p]
  exact (Dist p).sub_mem (hDist hX hY hXE hYE p) (hDist hY hX hYE hXE p)

/-- **Math.** **Exercise 2.5.30** (Petersen §2.5), reachable core: a distribution
that is parallel for the Levi-Civita connection is **involutive** — for smooth
fields `X, Y` tangent to `Dist`, the Lie bracket `[X, Y]` is again tangent to
`Dist`.  This is the local involutivity that Frobenius' theorem promotes to
integrability (the integrability and the product-metric splitting are deferred;
see the module docstring). -/
theorem exercise2_5_30 {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {Dist : Π x : M, Submodule ℝ (TangentSpace I x)}
    (hDist : IsParallelDistribution D.toAffineConnection Dist)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hXE : IsTangentTo Dist X) (hYE : IsTangentTo Dist Y) (p : M) :
    lieDerivativeVectorField I X Y p ∈ Dist p :=
  hDist.involutive D hX hY hXE hYE p

end PetersenLib
