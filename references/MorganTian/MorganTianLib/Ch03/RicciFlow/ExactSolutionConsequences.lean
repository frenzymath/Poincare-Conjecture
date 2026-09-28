import MorganTianLib.Ch03.RicciFlow.ExactSolutions
import MorganTianLib.Ch01.MetricRescalingInjectivity

/-!
# Morgan--Tian Ch. 3 - exact-solution metric consequences

The Einstein calculation gives the Ricci-flow equation.  This file records
the geometric quantities used in the examples: on the intended time set,
distances scale by the square root of the affine factor and sectional
curvatures scale by its reciprocal.  The statements are consequences of the
checked constant-rescaling identities, rather than target-shaped assumptions.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [T2Space (TangentBundle I M)] [T3Space M] [PreconnectedSpace M]

/-- **Math.** At a time in its intended interval, the exact Einstein family
has the distance of the initial metric multiplied by the square root of its
affine scale.

Blueprint: `ex:einstein-ricci-flow` (metric-distance consequence). -/
theorem einsteinMetricFamilyOn_canonicalDist
    (g₀ : RiemannianMetric I M) (J : Set ℝ) (lam : ℝ)
    (hpos : ∀ t ∈ J, 0 < einsteinScale lam t)
    {t : ℝ} (ht : t ∈ J) (p q : M) :
    (letI : MetricSpace M :=
      canonicalMetricSpace (einsteinMetricFamilyOn g₀ J lam hpos t);
      dist p q) =
      Real.sqrt (einsteinScale lam t) *
        (letI : MetricSpace M := canonicalMetricSpace g₀; dist p q) := by
  have hscale : einsteinScaleExtension J lam hpos t = einsteinScale lam t := by
    simp [einsteinScaleExtension, ht]
  have hfamily :
      einsteinMetricFamilyOn g₀ J lam hpos t =
        rescaledMetric g₀ (einsteinScale lam t) (hpos t ht) := by
    simp [einsteinMetricFamilyOn, hscale]
  rw [hfamily]
  exact rescaledMetric_canonicalDist g₀ (einsteinScale lam t)
    (hpos t ht) p q

/-- **Math.** At a time in its intended interval, every sectional curvature of
the exact Einstein family is divided by the affine scale.

Blueprint: `ex:einstein-ricci-flow` (curvature consequence). -/
theorem einsteinMetricFamilyOn_sectionalCurvatureAt
    (g₀ : RiemannianMetric I M) (J : Set ℝ) (lam : ℝ)
    (hpos : ∀ t ∈ J, 0 < einsteinScale lam t)
    {t : ℝ} (ht : t ∈ J) (p : M) (v w : TangentSpace I p) :
    sectionalCurvatureAt (einsteinMetricFamilyOn g₀ J lam hpos t)
        (einsteinMetricFamilyOn g₀ J lam hpos t).leviCivitaConnection p v w =
      sectionalCurvatureAt g₀ g₀.leviCivitaConnection p v w /
        einsteinScale lam t := by
  have hscale : einsteinScaleExtension J lam hpos t = einsteinScale lam t := by
    simp [einsteinScaleExtension, ht]
  have hfamily :
      einsteinMetricFamilyOn g₀ J lam hpos t =
        rescaledMetric g₀ (einsteinScale lam t) (hpos t ht) := by
    simp [einsteinMetricFamilyOn, hscale]
  rw [hfamily]
  exact rescaledMetric_sectionalCurvatureAt g₀ (einsteinScale lam t)
    (hpos t ht) p v w

end MorganTianLib

end
