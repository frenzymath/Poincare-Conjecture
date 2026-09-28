import Topping.RicciFlow.Existence.DeTurckPicard
import Topping.ParabolicPDE.ContractionJointDependence

/-!
# Joint parameter dependence for the DeTurck Picard family

`RicciDeTurckPicardFamily` already exposes the selected coefficient fixed point,
but its earlier stability theorem compares maps at a common state.  This file
provides the sharper consumer for a genuinely joint state/parameter estimate.
The geometric coefficient estimate remains an explicit hypothesis; no
nonlinear DeTurck existence or smooth dependence claim is hidden here.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace NNReal
open Set Filter Function Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

namespace RicciDeTurckPicardFamily

variable {A X : Type*} [MetricSpace A] [MetricSpace X]
  [Nonempty X] [CompleteSpace X]
  (F : RicciDeTurckPicardFamily (I := I) (M := M) A X)

/-- **Math.** A joint state/parameter Lipschitz estimate for the DeTurck
Picard maps controls the selected coefficient fixed points. -/
theorem dist_fixedPoint_le_of_joint_lipschitz
    {Lstate Lparam : ℝ≥0}
    (hstate : (Lstate : ℝ) < 1)
    (hmap : ∀ a b : A, ∀ z w : X,
      dist (F.contraction.map a z) (F.contraction.map b w) ≤
        (Lstate : ℝ) * dist z w + (Lparam : ℝ) * dist a b)
    (a b : A) :
    dist (F.fixedPoint a) (F.fixedPoint b) ≤
      (Lparam : ℝ) * dist a b / (1 - (Lstate : ℝ)) := by
  exact F.contraction.dist_fixedPointAt_le_of_joint_lipschitz
    hstate hmap a b

/-- **Math.** The preceding joint estimate gives a Lipschitz selected Picard
coefficient whenever the parameter space is nonempty. -/
theorem lipschitz_fixedPoint_of_joint_lipschitz
    [Nonempty A] {Lstate Lparam : ℝ≥0}
    (hstate : (Lstate : ℝ) < 1)
    (hmap : ∀ a b : A, ∀ z w : X,
      dist (F.contraction.map a z) (F.contraction.map b w) ≤
        (Lstate : ℝ) * dist z w + (Lparam : ℝ) * dist a b) :
    LipschitzWith
      ⟨(Lparam : ℝ) / (1 - (Lstate : ℝ)), by
        exact div_nonneg (NNReal.coe_nonneg Lparam)
          (le_of_lt (sub_pos.mpr hstate))⟩
      F.fixedPoint := by
  exact F.contraction.lipschitz_fixedPointAt_of_joint_lipschitz
    hstate hmap

/-- **Math.** Jointly Lipschitz DeTurck Picard maps have continuous selected
coefficient fixed points. -/
theorem continuous_fixedPoint_of_joint_lipschitz
    [Nonempty A] {Lstate Lparam : ℝ≥0}
    (hstate : (Lstate : ℝ) < 1)
    (hmap : ∀ a b : A, ∀ z w : X,
      dist (F.contraction.map a z) (F.contraction.map b w) ≤
        (Lstate : ℝ) * dist z w + (Lparam : ℝ) * dist a b) :
    Continuous F.fixedPoint := by
  exact (F.lipschitz_fixedPoint_of_joint_lipschitz hstate hmap).continuous

end RicciDeTurckPicardFamily

#print axioms RicciDeTurckPicardFamily.dist_fixedPoint_le_of_joint_lipschitz
#print axioms RicciDeTurckPicardFamily.lipschitz_fixedPoint_of_joint_lipschitz

end Topping

end
