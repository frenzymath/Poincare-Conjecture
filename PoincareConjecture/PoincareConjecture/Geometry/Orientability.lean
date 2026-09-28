import PoincareConjecture.Topology.OrientationCover
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Simply connected three-manifolds are orientable

The determinant cocycle here is that of Mathlib's actual `tangentBundleCore`:
its coordinate changes are derivatives of the manifold's chart transitions.
No orientation cover, global orientation, or determinant-sign condition is
assumed. The preceding module constructs the cover and lifts the identity.

We additionally give actual continuous, invertible changes of local tangent
frames for which every transition determinant is positive. In dimension three
the negative identity reverses orientation, so a sign suffices for each chart.
This is the standard positive-transition criterion for orientability of the
tangent bundle, and hence of a smooth manifold.
-/

open Set Function
open scoped Manifold ContDiff

noncomputable section

namespace PoincareConjecture

/-- The model tangent space for a three-manifold. -/
abbrev TangentModel3 := EuclideanSpace ℝ (Fin 3)

/-- Keep or reverse all three axes of a local tangent frame. -/
def orientationFrame (s : Bool) : TangentModel3 →L[ℝ] TangentModel3 :=
  orientationSign s • ContinuousLinearMap.id ℝ TangentModel3

/-- The frame change is its own inverse; it cannot collapse the tangent space. -/
theorem orientationFrame_involutive (s : Bool) :
    (orientationFrame s).comp (orientationFrame s) = ContinuousLinearMap.id ℝ TangentModel3 := by
  ext v
  cases s <;> simp [orientationFrame, orientationSign]

theorem orientationFrame_det (s : Bool) : (orientationFrame s).det = orientationSign s := by
  change LinearMap.det (orientationSign s • (LinearMap.id : TangentModel3 →ₗ[ℝ] TangentModel3)) = _
  rw [LinearMap.det_smul, LinearMap.det_id]
  cases s <;> norm_num [orientationSign, TangentModel3, finrank_euclideanSpace_fin]

/-- The transformed determinant is the original determinant with its source
and target frame signs. Both frame changes are actual linear maps. -/
theorem orientationFrame_transition_det (A : TangentModel3 →L[ℝ] TangentModel3) (s t : Bool) :
    ((orientationFrame t).comp (A.comp (orientationFrame s))).det =
      orientationSign t * A.det * orientationSign s := by
  change LinearMap.det ((orientationFrame t).toLinearMap.comp
    (A.toLinearMap.comp (orientationFrame s).toLinearMap)) = _
  rw [LinearMap.det_comp, LinearMap.det_comp]
  change (orientationFrame t).det * (A.det * (orientationFrame s).det) = _
  rw [orientationFrame_det, orientationFrame_det]
  ring

variable (M : Type*) [TopologicalSpace M] [ChartedSpace TangentModel3 M]
  [IsManifold (𝓡 3) 1 M] [SimplyConnectedSpace M]

/-- The tangent atlas of every simply connected C1 three-manifold has a
consistent orientation. In particular this applies to smooth three-manifolds. -/
theorem simplyConnected_threeManifold_orientable :
    HasPositiveOrientationAtlas (tangentBundleCore (𝓡 3) M) := by
  letI : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (H := TangentModel3) (M := M)
  exact hasPositiveOrientationAtlas_of_simplyConnected (tangentBundleCore (𝓡 3) M)

/-- A literal positive-frame formulation of the orientability conclusion.
The transition maps in the conclusion are the derivative-based coordinate
changes of the original tangent bundle, conjugated by continuous invertible
local frame changes. The original atlas and topology are not replaced. -/
theorem simplyConnected_threeManifold_positiveTangentFrames :
    ∃ R : (atlas TangentModel3 M) → M → TangentModel3 →L[ℝ] TangentModel3,
      (∀ i, ContinuousOn (R i) i.1.source) ∧
      (∀ i x, (R i x).comp (R i x) = ContinuousLinearMap.id ℝ TangentModel3) ∧
      ∀ i j x, x ∈ i.1.source ∩ j.1.source →
        0 < ((R j x).comp ((tangentBundleCore (𝓡 3) M).coordChange i j x |>.comp (R i x))).det := by
  obtain ⟨σ, hcont, hpositive⟩ := simplyConnected_threeManifold_orientable M
  refine ⟨fun i x => orientationFrame (σ i x), ?_, ?_, ?_⟩
  · intro i
    exact (continuous_of_discreteTopology : Continuous orientationFrame).comp_continuousOn (hcont i)
  · intro i x
    exact orientationFrame_involutive (σ i x)
  · intro i j x hx
    rw [orientationFrame_transition_det]
    exact hpositive i j x hx

end PoincareConjecture
