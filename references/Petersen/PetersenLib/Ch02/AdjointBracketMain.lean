import PetersenLib.Ch02.AdjointBracketAd
import PetersenLib.Ch02.AdjointBracketField
import PetersenLib.Ch02.ChartMulBracket

/-!
# Lemma 2.1.7 (abstract): `ad = D(Ad)` (Petersen §2.1.4)

Assembling the two manifold ↔ chart bridges with the normed-space core identity
`PetersenLib.ChartMul.adChart_eq_bracketChart`, this file proves the abstract form
of Petersen's Lemma 2.1.7 — the last open node of Chapter 1:
`D(Ad)_e(U)(X) = ⁅U, X⁆`.
-/

open Bundle Set Function VectorField
open scoped Manifold ContDiff Topology

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G] [I.Boundaryless]

/-- **Math.** **Lemma 2.1.7** (Petersen §2.1.4) for an abstract Lie group: the
differential of the adjoint representation is the Lie-algebra bracket,
`ad_U(X) = ⁅U, X⁆`, i.e. `(D(Ad)_e(U))(X) = ⁅U, X⁆`.

Both sides are computed in the chart at `1` as second derivatives of the chart
multiplication `μ(a, b) = φ(φ⁻¹a · φ⁻¹b)`:
`D(Ad)_e(U)(X)` is the antisymmetrised mixed partial `∂₁∂₂μ(U, X) − ∂₁∂₂μ(X, U)`
(`AdjointBracket.mfderiv_adMap_eq_adChart` + `ChartMul.adChart_eq_bracketChart`,
the latter using the unit laws to kill the `∂₂∂₂μ` term and `Dφ⁻¹(0) = −id`), which
is exactly the chart commutator of the invariant fields
(`AdjointBracket.groupBracket_eq_bracketChart`) that defines `⁅U, X⁆`. -/
theorem mfderiv_adMap_apply_eq_groupBracket (U X : GroupLieAlgebra I G) :
    mfderiv I 𝓘(ℝ, E) (fun h => adMap (I := I) h X) 1 U = ⁅U, X⁆ := by
  -- All chart/normed-space reasoning is carried out over `E` (the model space),
  -- where the instances live; `GroupLieAlgebra I G = E` definitionally.
  have key : ∀ U' X' : E,
      mfderiv I 𝓘(ℝ, E) (fun h => adMap (I := I) (G := G) h X') (1 : G) U'
      = mlieBracket I (mulInvariantVectorField (I := I) (G := G) U')
          (mulInvariantVectorField (I := I) (G := G) X') (1 : G) := by
    intro U' X'
    rw [AdjointBracket.mfderiv_adMap_eq_adChart (I := I) (G := G) X' U',
      ChartMul.adChart_eq_bracketChart
        (AdjointBracket.chartMul (I := I) (G := G))
        (AdjointBracket.chartInv (I := I) (G := G))
        (AdjointBracket.chartOne (I := I) (G := G)) X' U'
        AdjointBracket.contDiffAt_chartMul AdjointBracket.contDiffAt_chartInv
        AdjointBracket.chartMul_right_id AdjointBracket.chartMul_left_id
        AdjointBracket.chartInv_chartOne AdjointBracket.chartMul_chartInv_self]
    exact (AdjointBracket.groupBracket_eq_bracketChart X' U').symm
  rw [GroupLieAlgebra.bracket_def]
  exact key U X

end PetersenLib
