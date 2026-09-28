import MorganTianLib.Ch03.RicciFlow.ExactSolutionConsequences
import MorganTianLib.Ch02.EpsilonNeck
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6Sphere
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Morgan--Tian Ch. 3 -- exact round-sphere consequences

This module isolates the concrete two-sphere consequences which do not depend
on the still-missing bridge from do Carmo's immersed-sphere patch to the
bundled Levi--Civita connection of `unitRoundSphereMetric`.  The metric family
and its distance/sectional-curvature laws are unconditional rescaling facts.
The final declarations expose do Carmo's unconditional patch-level curvature
and shape-operator producers under Chapter 3 names.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Filter Riemannian

noncomputable section

namespace MorganTianLib

/- The canonical metric-rescaling distance theorem needs the connectedness of
the two-sphere as an explicit typeclass.  This is the standard subtype
instance induced by the ambient sphere's preconnectedness. -/
noncomputable instance epsilonNeckSpherePreconnected :
    PreconnectedSpace EpsilonNeckSphere :=
  Subtype.preconnectedSpace
    (isPreconnected_sphere (E := EuclideanSpace ℝ (Fin (2 + 1)))
      (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1)

/-! ### The exact shrinking scale and its metric consequences -/

/-- **Math.** The scale of the round two-sphere in the shrinking cylinder is
the affine factor `1 - t`. -/
def shrinkingRoundSphereScale (t : ℝ) : ℝ := 1 - t

/-- **Math.** The round-sphere scale is positive exactly before its extinction
time `1`. -/
theorem shrinkingRoundSphereScale_pos_iff {t : ℝ} :
    0 < shrinkingRoundSphereScale t ↔ t < 1 := by
  simp [shrinkingRoundSphereScale]

/-- **Math.** The shrinking round-sphere scale has time derivative `-1`. -/
theorem hasDerivAt_shrinkingRoundSphereScale (t : ℝ) :
    HasDerivAt shrinkingRoundSphereScale (-1) t := by
  change HasDerivAt (fun s : ℝ => 1 - s) (-1) t
  exact (hasDerivAt_id t).const_sub (1 : ℝ)

/-! The extinction limit is taken from the positive-scale side.  We record it
both in the ambient real filter and as `atTop` on the directed subtype
`Iio 1`, whose coercion tends to `1` from below. -/

theorem shrinkingRoundSphereScale_tendsto_zero_at_extinction :
    Tendsto shrinkingRoundSphereScale (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hid : Tendsto id (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  change Tendsto (fun t : ℝ => 1 - t) (𝓝[<] (1 : ℝ)) (𝓝 0)
  simpa [id] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ))).sub hid)

theorem shrinkingRoundSphereScale_tendsto_zero_atTop :
    Tendsto (fun t : Iio (1 : ℝ) => shrinkingRoundSphereScale (t : ℝ))
      atTop (𝓝 0) := by
  rw [tendsto_comp_coe_Iio_atTop]
  exact shrinkingRoundSphereScale_tendsto_zero_at_extinction

/-- **Math.** The exact shrinking family of the round two-sphere, defined on
the positive-scale time interval. -/
noncomputable def shrinkingRoundSphereMetricFamily (t : ℝ) (ht : t < 1) :
    RiemannianMetric (𝓡 2) EpsilonNeckSphere :=
  rescaledMetric roundSphereMetric (shrinkingRoundSphereScale t)
    (shrinkingRoundSphereScale_pos_iff.mpr ht)

/-- **Math.** The metric coefficients of the exact shrinking sphere are
`(1 - t)` times the initial round coefficients. -/
theorem shrinkingRoundSphereMetricFamily_metricInner
    (t : ℝ) (ht : t < 1) (p : EpsilonNeckSphere)
    (v w : TangentSpace (𝓡 2) p) :
    (shrinkingRoundSphereMetricFamily t ht).metricInner p v w =
      shrinkingRoundSphereScale t * roundSphereMetric.metricInner p v w := by
  simp only [shrinkingRoundSphereMetricFamily, rescaledMetric_metricInner]

/-- **Math.** Distances in the exact shrinking sphere are multiplied by the
square root of `1 - t`. -/
theorem shrinkingRoundSphereMetricFamily_canonicalDist
    (t : ℝ) (ht : t < 1) (p q : EpsilonNeckSphere) :
    @dist EpsilonNeckSphere
      (canonicalMetricSpace (shrinkingRoundSphereMetricFamily t ht)).toDist p q =
      Real.sqrt (shrinkingRoundSphereScale t) *
        @dist EpsilonNeckSphere (canonicalMetricSpace roundSphereMetric).toDist p q := by
  exact rescaledMetric_canonicalDist roundSphereMetric
    (shrinkingRoundSphereScale t)
    (shrinkingRoundSphereScale_pos_iff.mpr ht) p q

/-! **Math.** At extinction from below, the exact canonical distance formula
converges to zero for every fixed pair of points. -/
theorem shrinkingRoundSphereMetricFamily_canonicalDist_tendsto_zero_atTop
    (p q : EpsilonNeckSphere) :
    Tendsto
      (fun t : Iio (1 : ℝ) =>
        Real.sqrt (shrinkingRoundSphereScale (t : ℝ)) *
          @dist EpsilonNeckSphere (canonicalMetricSpace roundSphereMetric).toDist p q)
      atTop (𝓝 0) := by
  have hsqrt :
      Tendsto (fun t : ℝ => Real.sqrt (shrinkingRoundSphereScale t))
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp
      shrinkingRoundSphereScale_tendsto_zero_at_extinction
    simpa [Function.comp_def] using h
  have hdist := hsqrt.mul_const
    (@dist EpsilonNeckSphere (canonicalMetricSpace roundSphereMetric).toDist p q)
  simpa using (tendsto_comp_coe_Iio_atTop).mpr hdist

/-- **Math.** Every sectional curvature in the exact shrinking sphere is
divided by `1 - t`. -/
theorem shrinkingRoundSphereMetricFamily_sectionalCurvatureAt
    (t : ℝ) (ht : t < 1) (p : EpsilonNeckSphere)
    (v w : TangentSpace (𝓡 2) p) :
    sectionalCurvatureAt (shrinkingRoundSphereMetricFamily t ht)
        (shrinkingRoundSphereMetricFamily t ht).leviCivitaConnection p v w =
      sectionalCurvatureAt roundSphereMetric roundSphereMetric.leviCivitaConnection
        p v w / shrinkingRoundSphereScale t := by
  simpa only [shrinkingRoundSphereMetricFamily] using
    (rescaledMetric_sectionalCurvatureAt roundSphereMetric
      (shrinkingRoundSphereScale t)
      (shrinkingRoundSphereScale_pos_iff.mpr ht) p v w)

/-! ### Unconditional immersed-sphere producers from do Carmo -/

section SpherePatch

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Math.** do Carmo's unit-sphere curvature calculation, re-exported for
Chapter 3: orthonormal tangent fields on the unit sphere have curvature
numerator `1`.  This is the genuine immersed-patch producer; no bundled
constant-curvature hypothesis is inserted. -/
theorem spherePatch_sectionalCurvature_one
    {X Y : SmoothVectorField 𝓘(ℝ, F) ↥(Riemannian.punctured F)}
    (hX : (Riemannian.spherePatch (F := F)).IsTangentField X)
    (hY : (Riemannian.spherePatch (F := F)).IsTangentField Y)
    (p : ↥(Riemannian.punctured F)) (hp : ‖(p : F)‖ = 1)
    (hXX : (Riemannian.opensEuclideanMetric (Riemannian.punctured F)).metricInner
      p (X p) (X p) = 1)
    (hYY : (Riemannian.opensEuclideanMetric (Riemannian.punctured F)).metricInner
      p (Y p) (Y p) = 1)
    (hXY : (Riemannian.opensEuclideanMetric (Riemannian.punctured F)).metricInner
      p (X p) (Y p) = 0) :
    (Riemannian.opensEuclideanMetric (Riemannian.punctured F)).metricInner p
        ((Riemannian.spherePatch (F := F)).inducedCurvature
          Riemannian.opensEuclideanConnection X Y X p) (Y p) = 1 := by
  exact Riemannian.sphere_sectionalCurvature_one hX hY p hp hXX hYY hXY

/-- **Math.** The inward-normal shape operator of the unit sphere is the
identity on tangent vectors. -/
theorem spherePatch_shapeOperatorAt_identity
    (p : ↥(Riemannian.punctured F))
    (hp : inner ℝ (p : F) (p : F) = 1)
    {x : TangentSpace 𝓘(ℝ, F) p}
    (hx : x ∈ (Riemannian.spherePatch (F := F)).tang p) :
    (Riemannian.spherePatch (F := F)).shapeOperatorAt
        Riemannian.opensEuclideanConnection p (-(p : F)) x = x := by
  exact Riemannian.spherePatch_shapeOperatorAt p hp hx

end SpherePatch

end MorganTianLib

end
