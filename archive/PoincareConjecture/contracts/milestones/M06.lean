import PoincareMT.Statements.Ch04.Harnack
import PoincareMT.Proofs.M04

/-!
# Typed differential-Harnack milestone assembly

The analytic Harnack and ancient-flow proof is represented by one explicit
placeholder. The statement retains the corrected finite-start time factor and
the selected metric in every energy and completeness condition.
-/

/-! M06 is the numbered review and proof entry point. -/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- M06: given M04, complete Ricci flows with nonnegative curvature operator
bounded on each time slice satisfy the differential Harnack inequality and
its zero-safe integrated estimate along every C1 path. The finite estimate
retains elapsed-time factors and exp(-energy/2). Connected, nonflat ancient
flows satisfy the corresponding estimates without elapsed-time factors,
including the final time zero. Distance and path energy use the selected metric.

Sources: Morgan-Tian Theorem 4.37 and Corollary 4.39, p. 81;
Theorem 4.40, p. 82; Definition 9.2, p. 180. MT-HARNACK-ANCIENT in
`reviews/errata/2026-09-10-analytic-outline-audit.md` requires the finite-start
elapsed-time factor; the ancient limit removes it. Retain strict time ordering
and the zero-safe integrated formulation. The per-slice bound is justified
componentwise by the reviewed source derivation in
`reviews/contracts/M06-per-slice-source-argument.md`; its supporting geometry
and analysis are internal M06 proof obligations. -/
theorem differentialHarnackAncientTheory
    (hM04 : RicciFlowCurvatureTheory.{u}) : HarnackAncientTheory.{u} := by
  sorry

/-- M06 with the reviewed M04 package supplied explicitly. -/
theorem differentialHarnackAncientTheory_from_M04 : HarnackAncientTheory.{u} := by
  exact differentialHarnackAncientTheory ricciFlowCurvatureTheory

end PoincareMT
