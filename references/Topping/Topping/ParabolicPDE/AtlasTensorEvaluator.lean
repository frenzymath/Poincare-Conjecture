import Topping.ParabolicPDE.AtlasTensorAssembly

/-!
# Domain-aware evaluation of assembled atlas tensors

`GlobalAtlasTensorField` stores a quotient-valued tensor together with its
local chart representatives.  This file exposes the scalar bilinear
evaluation of those representatives and proves the overlap change law.  The
chart and domain witnesses stay explicit, so the result is an honest local
consumer of the quotient assembly rather than a claim that the quotient is
already a smooth tensor bundle.
-/

open scoped Manifold Topology ContDiff Bundle
open Set Filter Function

noncomputable section

namespace Topping
namespace ParabolicPDE

/-! ## Representative-level evaluation -/

namespace AtlasTensorRepresentative

variable {X C E : Type*} [AddCommMonoid E] [Module ℝ E]
  (A : PartialJacobianAtlas X C E)

/-- **Math.** Equivalent tensor representatives have the same bilinear form
after transporting both arguments by the chart Jacobian. -/
theorem equivalent_bilinForm_apply
    {p q : AtlasTensorRepresentative A}
    (hpq : Equivalent A p q) (u v : E) :
    (q.tensor : LinearMap.BilinForm ℝ E) u v =
      (p.tensor : LinearMap.BilinForm ℝ E)
        (A.jacobian p.chart q.chart p.base u)
        (A.jacobian p.chart q.chart p.base v) := by
  rw [hpq.2]
  exact sym2Pullback_apply (A.jacobian p.chart q.chart p.base) p.tensor u v

end AtlasTensorRepresentative

/-! ## Field-level chart evaluation -/

namespace GlobalAtlasTensorField

variable {X C E : Type*} [AddCommMonoid E] [Module ℝ E]
  (A : PartialJacobianAtlas X C E)

/-- **Math.** Bilinear evaluation of a global atlas field in a valid chart.
The domain witness is explicit because a chart representative is meaningful
only over its source. -/
def chartEval
    (F : GlobalAtlasTensorField A) (x : X) (c : C)
    (_hc : A.domain c x) (u v : E) : ℝ :=
  (F.localTensor c x : LinearMap.BilinForm ℝ E) u v

@[simp] theorem chartEval_apply
    (F : GlobalAtlasTensorField A) (x : X) (c : C)
    (hc : A.domain c x) (u v : E) :
    F.chartEval A x c hc u v =
      (F.localTensor c x : LinearMap.BilinForm ℝ E) u v :=
  rfl

/-- **Math.** On an overlap, evaluations in two charts are related by the
covariant Jacobian transition.  The proof extracts the representative
relation from the field's quotient-valued local equations. -/
theorem chartEval_transition
    (F : GlobalAtlasTensorField A) (x : X) (c d : C)
    (hc : A.domain c x) (hd : A.domain d x) (u v : E) :
    F.chartEval A x d hd u v =
      F.chartEval A x c hc
        (A.jacobian c d x u) (A.jacobian c d x v) := by
  have hcval := F.value_is_local x c hc
  have hdval := F.value_is_local x d hd
  have hquot :
      (⟦⟨x, c, F.localTensor c x, hc⟩⟧ : GlobalAtlasTensor A) =
        ⟦⟨x, d, F.localTensor d x, hd⟩⟧ :=
    hcval.symm.trans hdval
  have hrel :
      AtlasTensorRepresentative.Equivalent A
        ⟨x, c, F.localTensor c x, hc⟩
        ⟨x, d, F.localTensor d x, hd⟩ :=
    Quotient.exact hquot
  change (F.localTensor d x : LinearMap.BilinForm ℝ E) u v =
    (F.localTensor c x : LinearMap.BilinForm ℝ E)
      (A.jacobian c d x u) (A.jacobian c d x v)
  exact AtlasTensorRepresentative.equivalent_bilinForm_apply A hrel u v

/-- **Math.** The chart evaluator is unchanged when the same chart is used
twice; this records the identity-transition boundary case explicitly. -/
theorem chartEval_self
    (F : GlobalAtlasTensorField A) (x : X) (c : C)
    (hc : A.domain c x) (u v : E) :
    F.chartEval A x c hc u v =
      F.chartEval A x c hc
        (A.jacobian c c x u) (A.jacobian c c x v) := by
  rw [A.jacobian_self c x]
  rfl

end GlobalAtlasTensorField

end ParabolicPDE
end Topping

end
