import PoincareMT.Statements.Ch04.Pinching
import PoincareMT.Proofs.M04

/-!
# Typed Hamilton--Ivey milestone assembly

The theorem has one explicit placeholder for the analytic maximum-principle
argument. Its conclusion retains the spectral bridge and the full project norm
bound so later milestones need not introduce unreviewed operator data.
-/

/-! M05 is the numbered review and proof entry point. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- M05: for a compact smooth three-dimensional Ricci flow on [a,b), with
0 <= a < b and Hamilton-Ivey pinching at a, the M04 curvature theory implies
pinching at every included time. It also supplies the three-eigenvalue spectral
identities and the derived bound |Rm| <= 13 * max R0 (exp 4) wherever R <= R0.

Sources: Morgan-Tian Theorem 4.32, pp. 79-80, and Claims 4.28/4.30,
pp. 77-79. The numerical full-tensor estimate is a project-derived consequence.
Retain the corrected evolution and eigenvalue-concavity conventions in
`reviews/errata/2026-09-11-tensor-evolution.md`. -/
theorem hamiltonIveyPinching
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Set.Ico a b))
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hinit : HamiltonIveyPinchedAt (F.connection a) a) :
    HamiltonIveyPinchingConclusion a b F := by
  sorry

/-- The M05 result with the reviewed M04 assembly supplied explicitly. -/
theorem hamiltonIveyPinching_from_M04
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (F : RicciFlow 3 M (Set.Ico a b))
    (hinit : HamiltonIveyPinchedAt (F.connection a) a) :
    HamiltonIveyPinchingConclusion a b F := by
  exact hamiltonIveyPinching ha hab F ricciFlowCurvatureTheory hinit

end PoincareMT
