import PetersenLib.Ch06.AxisDisplacement
import PetersenLib.Ch06.DeckTransformations
import PetersenLib.Ch05.LocalIsometryGeodesics

/-!
# Petersen Ch. 6, §6.2 — a deck axis projects to a closed geodesic

Lemma 6.2.8 first obtains an axis for a deck transformation whose displacement
function attains a positive minimum.  The axis then projects to a closed
geodesic because the covering projection is a local Riemannian isometry and is
invariant under the deck transformation.

This file formalizes that latter bridge.  The compactness/free-homotopy
argument producing the minimum, the lower bound by twice the injectivity
radius, and minimality in the free homotopy class remain separate geometric
inputs, so the corresponding blueprint node is not yet `\leanok`.
-/

open Set
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]
  {E' : Type*} [NormedAddCommGroup E']
  [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless]

/-- **Math.** A translation axis of a deck transformation projects to a
periodic geodesic.  The geodesic assertion is naturality under the local
Riemannian isometry `π`; periodicity is the calculation
`π(c(t+a)) = π(F(c(t))) = π(c(t))`.

The local-isometry hypothesis is explicit because `IsCoveringMap π` is a
topological assertion, while the current smooth-manifold API has no theorem
upgrading it and an immersion to bijectivity of `Dπ`. -/
theorem DeckTransformation.projectedAxis_periodic
    (gN : RiemannianMetric I' M') {π : M → M'}
    (hπimm : IsSmoothImmersion (I := I) (I' := I') π)
    (hπlocal : IsLocalRiemannianIsometry
      (coveringInducedMetric gN π hπimm) gN π)
    {F : Diffeomorph I I M M ∞} (hF : DeckTransformation (I := I) π F)
    {c : ℝ → M} (hc : Continuous c) {a : ℝ}
    (haxis : IsAxisPeriod (I := I) (coveringInducedMetric gN π hπimm)
      (F : M → M) c a) :
    IsGeodesic (I := I') gN (π ∘ c) ∧
      ∀ t : ℝ, (π ∘ c) (t + a) = (π ∘ c) t := by
  constructor
  · exact localIsometry_mapsGeodesicsToGeodesics hπlocal hc haxis.1
  · intro t
    simp only [Function.comp_apply]
    calc
      π (c (t + a)) = π (F (c t)) := congrArg π (haxis.2 t).symm
      _ = π (c t) := congrFun hF.2 (c t)

/-- **Math.** Petersen Lemma 6.2.8, the axis/closed-geodesic kernel.  A
minimizing segment from `c(0)` to `F(c(0))`, together with the endpoint
first-variation identity used in Lemma 6.2.7, extends to a translation axis of
period `1`.  For a deck transformation that axis projects to a period-one
geodesic on the base.

The positive-minimum hypotheses are retained for one-to-one alignment with the
source statement, but the current Lean axis kernel marks them as removable:
`hvel` is supplied explicitly and is the actual proof hinge.  Thus this theorem
does not assert the still-unformalized compactness argument producing such a
minimum, the injectivity-radius lower bound, or free-homotopy minimality. -/
theorem deckTransformation_minimalDisplacement_closedGeodesic
    (gN : RiemannianMetric I' M') {π : M → M'}
    (hπimm : IsSmoothImmersion (I := I) (I' := I') π)
    (hπlocal : IsLocalRiemannianIsometry
      (coveringInducedMetric gN π hπimm) gN π)
    {F : Diffeomorph I I M M ∞} (hF : DeckTransformation (I := I) π F)
    {c : ℝ → M} (hc : Continuous c)
    (hgeo : IsGeodesic (I := I) (coveringInducedMetric gN π hπimm) c)
    (hseg : IsSegment (I := I) (coveringInducedMetric gN π hπimm) c 0 1)
    (hpositive : 0 < displacementFunction (I := I)
      (coveringInducedMetric gN π hπimm) (F : M → M) (c 0))
    (hminimum : ∀ x : M,
      displacementFunction (I := I) (coveringInducedMetric gN π hπimm)
          (F : M → M) (c 0) ≤
        displacementFunction (I := I) (coveringInducedMetric gN π hπimm)
          (F : M → M) x)
    (hend : c 1 = F (c 0))
    (hvel : deriv (Geodesic.chartLocalCurve (I := I) ((F : M → M) ∘ c) 0) 0 =
      deriv (fun s => extChartAt I (((F : M → M) ∘ c) 0) (c (s + 1))) 0) :
    IsAxis (I := I) (coveringInducedMetric gN π hπimm) (F : M → M) c ∧
      IsGeodesic (I := I') gN (π ∘ c) ∧
      ∀ t : ℝ, (π ∘ c) (t + 1) = (π ∘ c) t := by
  have hFisom : IsRiemannianIsometry
      (coveringInducedMetric gN π hπimm) (coveringInducedMetric gN π hπimm)
      (F : M → M) :=
    hF.isRiemannianIsometry hπimm
  have haxis := axis_of_positiveMinimalDisplacement (I := I)
    (coveringInducedMetric gN π hπimm) hFisom hc hgeo hseg hpositive hminimum
      hend hvel
  have hperiod : IsAxisPeriod (I := I) (coveringInducedMetric gN π hπimm)
      (F : M → M) c 1 :=
    axisPeriod_one_of_endpointVelocityMatch (I := I)
      (coveringInducedMetric gN π hπimm) hFisom hc hgeo hend.symm hvel
  exact ⟨haxis, hF.projectedAxis_periodic gN hπimm hπlocal hc hperiod⟩

end PetersenLib

end
