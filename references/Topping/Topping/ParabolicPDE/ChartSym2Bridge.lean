import Topping.ParabolicPDE.ChartJacobian
import DoCarmoLib.Riemannian.Exponential.GaussLemma

/-!
# Concrete chart-Gram tensors and symmetric-two-tensor transitions

This file supplies the first concrete consumer of `Sym2Transition`: a common
chart family carries enough overlap data to compare the coordinate Gram
pairings at a common foot.  DoCarmo's chart change theorem then becomes an
equality in the abstract symmetric-two-tensor package.
-/

open scoped Manifold Topology ContDiff Bundle Matrix

noncomputable section

namespace Topping
namespace ParabolicPDE

open Riemannian

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M C X : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Math.** The coordinate Gram pairing at a foot, packaged as a symmetric covariant
two-tensor on the model space.  Its symmetry and bilinearity are inherited
from the chart metric inner product. -/
def chartGramTensor (g : RiemannianMetric I M) (α p : M) :
    SymmetricTwoTensor E :=
  ⟨LinearMap.mk₂ ℝ
      (fun a b : E => chartMetricInner (I := I) g α (extChartAt I α p) a b)
      (by
        intro a a' b
        exact chartMetricInner_add_left (I := I) g α (extChartAt I α p) a a' b)
      (by
        intro s a b
        simp only [chartMetricInner_smul_left, smul_eq_mul])
      (by
        intro a b b'
        exact chartMetricInner_add_right (I := I) g α (extChartAt I α p) a b b')
      (by
        intro s a b
        simp only [chartMetricInner_smul_right, smul_eq_mul]),
    by
      exact ⟨fun a b =>
        chartMetricInner_symm (I := I) g α (extChartAt I α p) a b⟩⟩

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem chartGramTensor_apply (g : RiemannianMetric I M) (α p : M)
    (a b : E) :
    (chartGramTensor (I := I) g α p : LinearMap.BilinForm ℝ E) a b =
      chartMetricInner (I := I) g α (extChartAt I α p) a b := by
  rfl

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** DoCarmo's Gram change law, expressed as an equality in
`Sym2Transition`.
The common-foot membership is supplied by `A.mem`, so this statement is
unconditional at the API boundary. -/
theorem chartGramTensor_transition
    (A : CommonChartFamily I M C X)
    (g : RiemannianMetric I M) (c d : C) (x : X) :
    chartGramTensor (I := I) g (A.center d) (A.point x) =
      sym2Pullback (A.chartJacobian c d x)
        (chartGramTensor (I := I) g (A.center c) (A.point x)) := by
  apply Subtype.ext
  ext a b
  rw [chartGramTensor_apply, sym2Pullback_apply, chartGramTensor_apply,
    A.chartJacobian_apply]
  have hc : A.point x ∈ (chartAt H (A.center c)).source := by
    simpa only [extChartAt_source (I := I) (x := A.center c)] using A.mem c x
  have hd : A.point x ∈ (chartAt H (A.center d)).source := by
    simpa only [extChartAt_source (I := I) (x := A.center d)] using A.mem d x
  exact chartMetricInner_change (I := I) g (A.center c) (A.center d)
    hc hd a b

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The same bridge through the induced abstract transition
equivalence. -/
theorem chartGramTensor_tensorTransition
    (A : CommonChartFamily I M C X)
    (g : RiemannianMetric I M) (c d : C) (x : X) :
    chartGramTensor (I := I) g (A.center d) (A.point x) =
      A.jacobianCocycle.tensorTransition c d x
        (chartGramTensor (I := I) g (A.center c) (A.point x)) := by
  rw [JacobianCocycle.tensorTransition_apply]
  exact chartGramTensor_transition A g c d x

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The family of chart Gram tensors satisfies the abstract covariant gluing
law induced by the overlap Jacobians. -/
theorem chartGramTensor_gluing
    (A : CommonChartFamily I M C X)
    (g : RiemannianMetric I M) :
    A.jacobianCocycle.TensorGluing
      (fun c x => chartGramTensor (I := I) g (A.center c) (A.point x)) := by
  intro c d x
  exact chartGramTensor_tensorTransition A g c d x

end ParabolicPDE
end Topping

end
