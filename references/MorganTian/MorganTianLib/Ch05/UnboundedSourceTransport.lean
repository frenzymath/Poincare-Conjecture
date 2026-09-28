import MorganTianLib.Ch05.UnboundedAssembly

/-!
# Morgan--Tian Chapter 5: source-side unbounded GH transport

This module isolates the source-replacement step for unbounded pointed
Gromov--Hausdorff convergence.  It is useful when a diagonal construction
produces radius-wise models that are only identified with the canonical source
balls at pointed distance zero.
-/

open Set Filter Topology
open scoped Topology

namespace MorganTianLib

universe u

/-- **Math.** Unbounded pointed GH convergence is preserved when every fixed
positive-radius source ball is replaced pointwise by a zero-distance model,
provided the replacement balls retain a uniform diameter bound. -/
theorem pointedGHConvergesUnbounded_of_zero_distance_source
    (X X' : ℕ → BasedMetricSpaceBundle.{u})
    (Y : BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    [∀ k, LengthSpace (X' k).carrier]
    (h : PointedGHConvergesUnbounded X Y)
    (hzero : ∀ r : ℝ, ∀ hr : 0 < r, ∀ k : ℕ,
      pointedGHDistance (ballModel (X' k) r hr)
        (ballModel (X k) r hr) = 0)
    (hbound : ∀ r : ℝ, ∀ hr : 0 < r,
      UniformlyBoundedDiameter
        (fun k => ballModel (X' k) r hr)) :
    PointedGHConvergesUnbounded X' Y := by
  apply (pointedGHConvergesUnbounded_iff_fixedRadius X' Y).2
  intro r hr
  have hfixed :=
    (pointedGHConvergesUnbounded_iff_fixedRadius X Y).1 h r hr
  exact PointedGHConverges.of_zero_distance_source hfixed
    (fun k => hzero r hr k) (hbound r hr)

end MorganTianLib

#print axioms MorganTianLib.pointedGHConvergesUnbounded_of_zero_distance_source
