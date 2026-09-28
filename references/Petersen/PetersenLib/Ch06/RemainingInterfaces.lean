import PetersenLib.Ch06.RauchComparisonKernel
import PetersenLib.Ch06.ClosedParallelField
import PetersenLib.Ch06.SecBounds
import PetersenLib.Ch05.HopfRinowTheorem
import PetersenLib.Ch06.MyersFundamentalGroup
import Mathlib.Topology.Homeomorph.Defs

/-!
# Petersen Ch. 6 — remaining comparison interfaces

This module closes three named §6 nodes whose global geometric bridges are still
outside the current library.

* `conjugateRadius_scalarEndpointUpperBound` is the scalar radial-Jacobi core of Theorem 6.4.6.
  Its `OneOverAddBigO` coefficient and Riccati inequality are exactly the
  hypotheses consumed by the already proved Rauch/Riccati engine.  The theorem
  consequently proves the model endpoint bound and positivity (hence absence of
  model zeros) before `pi / sqrt K`.  Turning that scalar statement into
  injectivity of the manifold exponential map still needs the tensor-valued
  Jacobi-to-`D exp` bridge.
* `closedParallelField_holonomyFixedVector` packages the normal holonomy of a
  closed geodesic as a real orthogonal matrix.  It applies the existing
  determinant/fixed-vector lemma, so the conclusion is an actual nonzero fixed
  normal vector rather than an assumption of one.  The transport of that vector
  back to a tangent bundle field is intentionally an explicit interface.
* `cartanHadamard_failure_of_notEuclidean` records the failure remark as a genuine
  counterexample interface: a caller supplies a complete metric, a Ricci- or
  scalar-nonpositive bound, an explicit simply connected covering space, and a
  topological obstruction to Euclideanity.  The theorem proves that these data
  refute the Cartan--Hadamard conclusion.  Concrete product metrics remain a
  separate construction.

No declaration here is marked `\\leanok`: each statement is a conditional/core
interface, not the full global theorem from the book.
-/

open Set
open Matrix
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

/-! ## The scalar conjugate-radius core -/

/-- The radial scalar data used by the conjugate-radius comparison.  The
coefficient convention is the one used by `le_pi_div_sqrt_of_riccati_le`; the
tensor-to-coefficient sign conversion is a separate Rauch bridge. -/
structure ConjugateRadiusJacobiData (K b : ℝ) where
  K_pos : 0 < K
  rho : ℝ → ℝ
  rhoDeriv : ℝ → ℝ
  rho_deriv : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt rho (rhoDeriv t) t
  rho_asymptotic : OneOverAddBigO rho
  riccati_upper : ∀ t ∈ Ioo (0 : ℝ) b,
    rhoDeriv t + (rho t) ^ 2 ≤ -K

/-- **Math.** Petersen Theorem 6.4.6 (`thm:pet-ch6-conjugate-radius-bound`),
scalar radial-Jacobi interface.  The Riccati estimate forces the endpoint
`b ≤ pi / sqrt K`; on the whole open interval the model function is positive,
so it has no conjugate zero there, and the radial coefficient is bounded by the
model ratio.  A future tensor bridge can consume these three facts to prove
that `D exp_p` is nonsingular on the corresponding ball. -/
theorem conjugateRadius_scalarEndpointUpperBound {K b : ℝ}
    (D : ConjugateRadiusJacobiData K b) :
    b ≤ Real.pi / Real.sqrt K ∧
      (∀ t ∈ Ioo (0 : ℝ) b, 0 < snFunction K t ∧ snFunction K t ≠ 0) ∧
      (∀ t ∈ Ioo (0 : ℝ) b, D.rho t ≤ snRatio K t) := by
  have hcmp :=
    (riccatiComparisonEstimate D.rho_deriv D.rho_asymptotic).1 D.riccati_upper
  have hb : b ≤ Real.pi / Real.sqrt K := hcmp.1 D.K_pos
  refine ⟨hb, ?_, hcmp.2⟩
  intro t ht
  have hpos : 0 < snFunction K t :=
    snFunction_pos_of_pos D.K_pos ht.1 (lt_of_lt_of_le ht.2 hb)
  exact ⟨hpos, hpos.ne'⟩

/-! ## The closed-geodesic holonomy kernel -/

/-- A coordinate package for the restriction of parallel translation around a
closed geodesic to its normal space.  `determinant` is the orientation parity
condition in Petersen's argument; `period_pos` records that the underlying
geodesic has positive period. -/
structure ClosedGeodesicHolonomyData (k : ℕ) where
  period : ℝ
  period_pos : 0 < period
  holonomy : Matrix (Fin k) (Fin k) ℝ
  isometry : holonomyᵀ * holonomy = 1
  determinant : holonomy.det = (-1 : ℝ) ^ (k + 1)

/-- **Math.** Petersen's closed-parallel-field remark
(`rem:pet-ch6-closed-parallel-field-construction`): an orthogonal normal
holonomy with the required orientation determinant fixes a nonzero normal
vector.  In coordinates this is a closed parallel field around the geodesic.
The geometric parallel-transport and normal-bundle identifications are exactly
the data represented by `ClosedGeodesicHolonomyData`. -/
theorem closedParallelField_holonomyFixedVector {k : ℕ}
    (D : ClosedGeodesicHolonomyData k) :
    ∃ v : Fin k → ℝ, v ≠ 0 ∧ D.holonomy *ᵥ v = v := by
  exact isometry_det_neg_one_pow_hasFixedVector D.isometry D.determinant

/-! ## The Ricci/scalar counterexample interface -/

section RicciFailure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [SigmaCompactSpace M]
  [T2Space M] [LocallyCompactSpace M] {g : RiemannianMetric I M}

/-- Pointwise nonpositivity of the Ricci quadratic form. -/
def HasRicciNonpositive (D : RiemannianConnection I (g : RiemannianMetric I M)) : Prop :=
  ∀ p : M, ∀ v : TangentSpace I p,
    RicciCurvature D.toAffineConnection p v v ≤ 0

/-- Pointwise nonpositivity of scalar curvature. -/
def HasScalarNonpositive (D : RiemannianConnection I (g : RiemannianMetric I M)) : Prop :=
  ∀ p : M, scalarCurvature D p ≤ 0

/-- Explicit data for a counterexample to replacing sectional curvature by a
Ricci/scalar bound in Cartan--Hadamard.  `U` is the supplied simply connected
cover, `projection` is its covering map, and `notEuclidean` is the topological
obstruction (for the source examples, the sphere factor supplies it). -/
structure CartanHadamardRicciFailureData
    (g : RiemannianMetric I M) (U : Type*) [TopologicalSpace U]
    [SimplyConnectedSpace U] (n : ℕ) where
  projection : U → M
  covering : IsCoveringMap projection
  base_complete : IsGeodesicallyComplete (I := I) g
  ricci_or_scalar_nonpositive :
    HasRicciNonpositive (I := I) g.leviCivita ∨
      HasScalarNonpositive (I := I) g.leviCivita
  notEuclidean : ¬ Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin n))

/-- **Math.** Petersen's remark
(`rem:pet-ch6-cartan-hadamard-fails-ricci`): once an explicit complete
Ricci-flat/scalar-flat covering example and its topological obstruction are
provided, the Cartan--Hadamard implication is refuted.  This theorem is the
logical counterexample step; constructing the product metrics and their
universal covers is deliberately left to a future geometry module. -/
theorem cartanHadamard_failure_of_notEuclidean
    {g : RiemannianMetric I M} {U : Type*} [TopologicalSpace U]
    [SimplyConnectedSpace U] {n : ℕ}
    (D : CartanHadamardRicciFailureData (I := I) g U n) :
    ¬ ((IsGeodesicallyComplete (I := I) g ∧
        (HasRicciNonpositive (I := I) g.leviCivita ∨
          HasScalarNonpositive (I := I) g.leviCivita)) →
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin n))) := by
  intro h
  exact D.notEuclidean (h ⟨D.base_complete, D.ricci_or_scalar_nonpositive⟩)

end RicciFailure

end PetersenLib
