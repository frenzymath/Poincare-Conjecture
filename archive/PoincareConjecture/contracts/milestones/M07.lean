import PoincareMT.Statements.Ch05.Compactness
import PoincareMT.Proofs.M04

/-!
# Pointed Ricci-flow compactness proof assembly

The compactness argument remains admitted at this skeleton stage.  The wrapper
records that the accepted M04 curvature theory is the predecessor interface
needed for the curvature bounds and interior completeness argument.
-/

/-! M07 is the numbered review and proof entry point. -/

set_option autoImplicit false

namespace PoincareMT

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- M07: given M04, a sequence of pointed ordinary Ricci flows on varying
carriers has a smoothly converging subsequence on an exhaustion when zero is
an interior reference time, reference balls have compact closure, the stated
spacetime embeddings have curvature control, one fixed scale is noncollapsed,
and curvature on balls at each time is controlled at independently quantified
times. The limit satisfies Ricci flow and is complete at every interior time.

Sources: Morgan-Tian Definition 5.12, Proposition 5.14 and Theorem 5.15,
pp. 90-92, specialized to ordinary flows; Topping (2014), Theorem 1.7, p. 179.
MT-COMPACTNESS-5.15 and MT-TIME-ENDPOINTS in
`reviews/errata/2026-09-10-source-audit.md` explain the stronger curvature
hypotheses and strict interior-time restriction. -/
theorem pointedRicciFlowCompactness
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hM04 : RicciFlowCurvatureTheory.{0}) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  sorry

/-- M07 wrapper using the reviewed M04 assembly. -/
theorem pointedRicciFlowCompactness_from_M04
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  exact pointedRicciFlowCompactness H ricciFlowCurvatureTheory.{0}

end PoincareMT
