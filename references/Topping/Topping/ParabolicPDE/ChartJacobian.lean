import Topping.ParabolicPDE.Sym2Transition
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Chart-overlap Jacobian cocycles

The manifold tangent-coordinate change is only meaningful on the intersection
of chart sources.  `CommonChartFamily` records that domain explicitly, then
turns the resulting coordinate changes into linear equivalences and the
abstract `JacobianCocycle` consumed by the symmetric-tensor transition layer.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Filter Function

noncomputable section

namespace Topping
namespace ParabolicPDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M C X : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A family of chart centres whose chosen evaluation points lie in every
chart source.  The explicit membership field is what makes the Jacobian
composition laws available without assigning meaningful values off overlaps.
-/
structure CommonChartFamily (I : ModelWithCorners ℝ E H) (M C X : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  center : C → M
  point : X → M
  mem : ∀ c x, point x ∈ (extChartAt I (center c)).source

namespace CommonChartFamily

variable (A : CommonChartFamily I M C X)

/-- The coordinate Jacobian from chart `d` to chart `c`, made invertible by
the common-domain witnesses carried by `A`.
-/
noncomputable def chartJacobian (c d : C) (x : X) : E ≃ₗ[ℝ] E := by
  let f : E →L[ℝ] E :=
    tangentCoordChange I (A.center d) (A.center c) (A.point x)
  let g : E →L[ℝ] E :=
    tangentCoordChange I (A.center c) (A.center d) (A.point x)
  have hleft : ∀ v : E, g (f v) = v := by
    intro v
    have h := tangentCoordChange_comp (I := I)
      (w := A.center d) (x := A.center c) (y := A.center d)
      (z := A.point x) (v := v)
      (show A.point x ∈
        (extChartAt I (A.center d)).source ∩
          (extChartAt I (A.center c)).source ∩
          (extChartAt I (A.center d)).source by
        exact ⟨⟨A.mem d x, A.mem c x⟩, A.mem d x⟩)
    calc
      g (f v) = tangentCoordChange I (A.center d) (A.center d)
          (A.point x) v := by simpa [f, g] using h
      _ = v := tangentCoordChange_self (I := I) (A.mem d x)
  have hright : ∀ v : E, f (g v) = v := by
    intro v
    have h := tangentCoordChange_comp (I := I)
      (w := A.center c) (x := A.center d) (y := A.center c)
      (z := A.point x) (v := v)
      (show A.point x ∈
        (extChartAt I (A.center c)).source ∩
          (extChartAt I (A.center d)).source ∩
          (extChartAt I (A.center c)).source by
        exact ⟨⟨A.mem c x, A.mem d x⟩, A.mem c x⟩)
    calc
      f (g v) = tangentCoordChange I (A.center c) (A.center c)
          (A.point x) v := by simpa [f, g] using h
      _ = v := tangentCoordChange_self (I := I) (A.mem c x)
  have hinj : Function.Injective f := by
    intro u v huv
    apply_fun g at huv
    simpa [hleft] using huv
  have hsurj : Function.Surjective f := by
    intro v
    exact ⟨g v, hright v⟩
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

@[simp] theorem chartJacobian_apply (c d : C) (x : X) (v : E) :
    A.chartJacobian c d x v =
      tangentCoordChange I (A.center d) (A.center c) (A.point x) v := by
  rfl

/- The inverse of the Jacobian is the coordinate change in the opposite
   direction.  This makes the inverse action available to concrete tensor
   transitions without unfolding the `LinearEquiv.ofBijective` definition. -/
theorem chartJacobian_symm_apply (c d : C) (x : X) (v : E) :
    (A.chartJacobian c d x).symm v =
      tangentCoordChange I (A.center c) (A.center d) (A.point x) v := by
  apply (A.chartJacobian c d x).injective
  rw [LinearEquiv.apply_symm_apply, A.chartJacobian_apply]
  have h := tangentCoordChange_comp (I := I)
    (w := A.center c) (x := A.center d) (y := A.center c)
    (z := A.point x) (v := v)
    (show A.point x ∈
      (extChartAt I (A.center c)).source ∩
        (extChartAt I (A.center d)).source ∩
        (extChartAt I (A.center c)).source by
      exact ⟨⟨A.mem c x, A.mem d x⟩, A.mem c x⟩)
  symm
  calc
    tangentCoordChange I (A.center d) (A.center c) (A.point x)
        (tangentCoordChange I (A.center c) (A.center d) (A.point x) v) =
      tangentCoordChange I (A.center c) (A.center c) (A.point x) v := by
        simpa using h
    _ = v := tangentCoordChange_self (I := I) (A.mem c x)

/-- The chart Jacobians form the cocycle required by tensor transitions. -/
noncomputable def jacobianCocycle (A : CommonChartFamily I M C X) : JacobianCocycle X C E where
  jacobian := A.chartJacobian
  jacobian_self := by
    intro c x
    ext v
    rw [A.chartJacobian_apply, tangentCoordChange_self (I := I) (A.mem c x)]
    rfl
  jacobian_cocycle := by
    intro c d e x
    ext v
    rw [LinearEquiv.trans_apply, A.chartJacobian_apply, A.chartJacobian_apply,
      A.chartJacobian_apply]
    have h := tangentCoordChange_comp (I := I)
      (w := A.center e) (x := A.center d) (y := A.center c)
      (z := A.point x) (v := v)
      (show A.point x ∈
        (extChartAt I (A.center e)).source ∩
          (extChartAt I (A.center d)).source ∩
          (extChartAt I (A.center c)).source by
        exact ⟨⟨A.mem e x, A.mem d x⟩, A.mem c x⟩)
    exact h

@[simp] theorem jacobianCocycle_jacobian (c d : C) (x : X) :
    A.jacobianCocycle.jacobian c d x = A.chartJacobian c d x :=
  rfl

end CommonChartFamily

end ParabolicPDE
end Topping

end
