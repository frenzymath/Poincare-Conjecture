import PetersenLib.Ch06.SecBounds
import PetersenLib.Ch06.SecondVariationGlobal
import PetersenLib.Ch06.MyersFundamentalGroup
import PetersenLib.Ch01.DoublyWarpedSmoothness

/-!
# Petersen Ch. 6, §6.3 — positive-curvature statement interfaces

The Bonnet--Synge and Myers files contain the analytic second-variation proofs.  Four
§6.3 nodes still need global constructions which are not present in the current library:
the punctured round sphere, the doubly warped example, the holonomy argument in Synge's
theorem, and the (open) Hopf question.  This file records those statements as explicit
interfaces.  A statement interface is intentionally a `Prop` with all of the source
hypotheses and conclusions; it is not tagged as a proof of the statement and it does not
introduce an axiom or a `sorry`.

The one proved result below is the local obstruction used by Synge's argument: a proper
variation with a parallel field and positive sectional curvature has negative second
variation.  The endpoint and regularity data remain hypotheses, exactly as in
`secondVariationEnergy_parallelField_geodesicTransversals`.
-/

open Set Filter MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace PetersenLib

/-! ## The punctured sphere (Example 6.3.4) -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-!
`PuncturedSphereExampleData` is deliberately parameterised by the carrier manifold.  In the
intended instantiation `M` is the open submanifold of the unit sphere obtained by deleting
two antipodal points.  Keeping the carrier as a parameter lets the statement use the actual
Petersen/Ch. 3 curvature and fundamental-group APIs without pretending that the open-submanifold
restriction of the round metric has already been constructed.
-/
structure PuncturedSphereExampleData (g : RiemannianMetric I M) where
  north : M
  south : M
  antipodalPoints : north ≠ south
  deletedSet : Set M
  deletedSet_eq : deletedSet = ({north, south} : Set M)
  incomplete : ¬ IsGeodesicallyComplete (I := I) g
  curvatureOne : HasConstantCurvature (g.leviCivita) 1
  basePoint : M
  infiniteFundamentalGroup : ¬ Finite (FundamentalGroup M basePoint)

/-!
The source example also records that the universal cover has diameter `π`.  We expose that
part as a separate witness so a future covering-space construction can fill it without changing
the first-order statement above.
-/
structure PuncturedSphereCoverDiameter (base : Type*) [PseudoMetricSpace base] where
  cover : Type*
  [coverMetric : PseudoMetricSpace cover]
  projection : cover → base
  diameter_eq_pi : Metric.diam (Set.univ : Set cover) = Real.pi

/-!
**Example 6.3.4 interface.**  This is the exact package of geometric facts used in the text:
an incomplete constant-curvature-one carrier with infinite fundamental group.  The concrete
round-sphere/open-submanifold constructor is intentionally left as a separate bridge.
-/
def puncturedSphereExample (g : RiemannianMetric I M) : Prop :=
  Nonempty (PuncturedSphereExampleData (I := I) g)

/-! ## The doubly warped positive-Ricci example (Example 6.3.5) -/

/-!
For a one-dimensional radial base and fibers of dimensions `1` and `2` (the `S¹ × ℝ³`
doubly-warped ansatz), the three displayed expressions are the radial, circle, and sphere
components of the Ricci tensor.  This predicate is the scalar curvature-model interface; the
remaining work is to connect it to `warpedProductForm` and the corresponding Riemannian metric.
It is a right-half-line condition: all positivity and Ricci inequalities are required only
for `t > 0`, because the collapsing endpoint has `ρ 0 = 0`.
-/
def IsDoublyWarpedRicciPositive (ρ φ : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t →
    0 < ρ t ∧ 0 < φ t ∧
    0 < -(deriv (deriv ρ) t) / ρ t - 2 * (deriv (deriv φ) t) / φ t ∧
    0 < -(deriv (deriv ρ) t) / ρ t
        - 2 * (deriv ρ t) * (deriv φ t) / (ρ t * φ t) ∧
    0 < (1 - (deriv φ t) ^ 2) / (φ t) ^ 2
        - (deriv (deriv φ) t) / φ t
        - (deriv φ t) * (deriv ρ t) / (φ t * ρ t)

/-!
**Example 6.3.5 interface.**  The asymptotic powers and endpoint smoothness are part of the
statement, rather than an opaque `True` premise.  `WarpingClosesSmoothlyAt` and
`WarpingStaysPositiveAt` are the existing Ch. 1 endpoint conditions.
-/
def dwpRicciPositiveOnS1TimesR3 : Prop :=
  ∃ ρ φ : ℝ → ℝ,
    ContDiff ℝ ∞ ρ ∧ ContDiff ℝ ∞ φ ∧
    WarpingClosesSmoothlyAt ρ 0 1 ∧ WarpingStaysPositiveAt φ 0 ∧
    (∀ t : ℝ, 1 < t →
      ρ t = Real.rpow t (-1 / 4 : ℝ) ∧ φ t = Real.rpow t (3 / 4 : ℝ)) ∧
    IsDoublyWarpedRicciPositive ρ φ

/-! ## Synge's theorem (Theorem 6.3.6) -/

/-!
`syngeTheorem` is the source-level implication.  `Subsingleton (FundamentalGroup M p)` is used
instead of a global `SimplyConnectedSpace` instance so the statement remains a proposition and
does not require a choice of basepoint.  The proof bridge still needs the parallel-transport
holonomy and closed-geodesic minimisation APIs (see `ClosedParallelField.lean`).
-/
def syngeTheorem (g : RiemannianMetric I M) : Prop :=
  IsCompact (Set.univ : Set M) →
    HasSecPos (g.leviCivita) →
      ((Even (Module.finrank ℝ E) ∧ DCIsOrientable (I := I) (M := M)) →
          ∀ p : M, Subsingleton (FundamentalGroup M p)) ∧
        (Odd (Module.finrank ℝ E) → DCIsOrientable (I := I) (M := M))

/-! ## A proved local obstruction used in Synge's proof -/

/-!
`secondVariation_negative_of_negativeCurvatureIntegral` is the sign-transfer step in
Petersen's Synge argument.  It assumes the curvature integral is already negative and
transfers that sign through the proper-variation second-variation API; no global holonomy or
closed-geodesic existence is smuggled into it.
-/
theorem secondVariation_negative_of_negativeCurvatureIntegral
    (g : RiemannianMetric I M) {f : ℝ → ℝ → M} {δ a b p₁ p₂ : ℝ}
    (hδ : 0 < δ) (h12 : p₁ < p₂)
    (hsub : Icc p₁ p₂ ⊆ Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f)
      (Ioo (-δ) δ ×ˢ Ioo a b))
    (hgeo : ∀ t ∈ Icc p₁ p₂,
      curveAcceleration (I := I) g (f 0) t = 0)
    (hpar : IsParallelAlong (I := I) g (f 0) (variationField (I := I) f))
    (htrans : ∀ t, curveAcceleration (I := I) g (fun σ => f σ t) 0 = 0)
    (hneg : (∫ t in p₁..p₂,
      -g.inner (f 0 t)
        (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
          (variationField (I := I) f t)
          (curveVelocity (I := I) (f 0) t)
          (curveVelocity (I := I) (f 0) t))
        (variationField (I := I) f t)) < 0) :
    deriv (deriv (fun s : ℝ => energyFunctional (I := I) g (f s) p₁ p₂)) 0 < 0 := by
  exact (secondVariationEnergy_parallelField_geodesicTransversals
    (I := I) g hδ h12 hsub hf hgeo hpar htrans).deriv ▸ hneg

/-! ## The Hopf problem (state only) -/

inductive HopfProblemStatus where
  | openQuestion

/-!
The Hopf question is deliberately represented by a status value, not by either an existence
claim or a nonexistence theorem.  The intended geometric question is whether `S² × S²` admits a
metric with positive sectional curvature.
-/
def hopfProblemRemark : HopfProblemStatus := .openQuestion

end PetersenLib
