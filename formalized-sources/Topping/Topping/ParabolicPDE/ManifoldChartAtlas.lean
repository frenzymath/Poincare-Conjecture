import Topping.ParabolicPDE.AtlasTensorAssembly

/-!
# The preferred-chart partial atlas

The preferred manifold charts are not simultaneously defined at every point.
This file therefore totalizes the tangent-coordinate changes by the identity
off an overlap, while retaining the domain hypotheses on every cocycle law.
The resulting partial atlas is strong enough to assemble the chart Gram forms
of a Riemannian metric into the quotient-valued tensor field used by the
section-space boundary.
-/

open scoped Manifold Topology ContDiff Bundle
open Set Filter Function

noncomputable section

namespace Topping
namespace ParabolicPDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-! ## Domain and totalized coordinate changes -/

/-! We use the preferred chart source itself as the atlas domain predicate. -/

/-- **Math.** The tangent-coordinate change from chart `d` to chart `c`, totalized by the
identity when the two chart sources do not overlap.  The off-domain value is
never used by the gluing and cocycle theorems below. -/
noncomputable def manifoldChartJacobian (c d x : M) : E ≃ₗ[ℝ] E := by
  classical
  by_cases h : x ∈ (chartAt H c).source ∧ x ∈ (chartAt H d).source
  · let f : E →L[ℝ] E := tangentCoordChange I d c x
    let g : E →L[ℝ] E := tangentCoordChange I c d x
    have hleft : ∀ v : E, g (f v) = v := by
      intro v
      have hcomp := tangentCoordChange_comp (I := I)
        (w := d) (x := c) (y := d) (z := x) (v := v)
        (show x ∈ (extChartAt I d).source ∩
          (extChartAt I c).source ∩ (extChartAt I d).source by
          simpa only [extChartAt_source (I := I)] using
            (show x ∈ (chartAt H d).source ∩
              (chartAt H c).source ∩ (chartAt H d).source from
              ⟨⟨h.2, h.1⟩, h.2⟩))
      calc
        g (f v) = tangentCoordChange I d d x v := by
          simpa [f, g] using hcomp
        _ = v := tangentCoordChange_self (I := I) (by
          simpa only [extChartAt_source (I := I)] using h.2)
    have hright : ∀ v : E, f (g v) = v := by
      intro v
      have hcomp := tangentCoordChange_comp (I := I)
        (w := c) (x := d) (y := c) (z := x) (v := v)
        (show x ∈ (extChartAt I c).source ∩
          (extChartAt I d).source ∩ (extChartAt I c).source by
          simpa only [extChartAt_source (I := I)] using
            (show x ∈ (chartAt H c).source ∩
              (chartAt H d).source ∩ (chartAt H c).source from
              ⟨⟨h.1, h.2⟩, h.1⟩))
      calc
        f (g v) = tangentCoordChange I c c x v := by
          simpa [f, g] using hcomp
        _ = v := tangentCoordChange_self (I := I) (by
          simpa only [extChartAt_source (I := I)] using h.1)
    have hinj : Function.Injective f := by
      intro u v huv
      apply_fun g at huv
      simpa [hleft] using huv
    have hsurj : Function.Surjective f := by
      intro v
      exact ⟨g v, hright v⟩
    exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  · exact LinearEquiv.refl ℝ E

@[simp] theorem manifoldChartJacobian_apply_of_mem
    {c d x : M} (hc : x ∈ (chartAt H c).source)
    (hd : x ∈ (chartAt H d).source) (v : E) :
    manifoldChartJacobian (I := I) c d x v =
      tangentCoordChange I d c x v := by
  classical
  rw [manifoldChartJacobian, dif_pos (And.intro hc hd)]
  rfl

theorem manifoldChartJacobian_self (c x : M) :
    manifoldChartJacobian (I := I) c c x = LinearEquiv.refl ℝ E := by
  classical
  by_cases hc : x ∈ (chartAt H c).source
  · apply LinearEquiv.ext
    intro v
    rw [manifoldChartJacobian_apply_of_mem hc hc,
      tangentCoordChange_self (I := I) (by
        simpa only [extChartAt_source (I := I)] using hc)]
    rfl
  · rw [manifoldChartJacobian, dif_neg (fun h => hc h.1)]

theorem manifoldChartJacobian_cocycle
    {c d e x : M}
    (hc : x ∈ (chartAt H c).source)
    (hd : x ∈ (chartAt H d).source)
    (he : x ∈ (chartAt H e).source) :
    (manifoldChartJacobian (I := I) d e x).trans
        (manifoldChartJacobian (I := I) c d x) =
      manifoldChartJacobian (I := I) c e x := by
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.trans_apply,
    manifoldChartJacobian_apply_of_mem hd he,
    manifoldChartJacobian_apply_of_mem hc hd,
    manifoldChartJacobian_apply_of_mem hc he]
  exact tangentCoordChange_comp (I := I)
    (w := e) (x := d) (y := c) (z := x) (v := v)
    (show x ∈ (extChartAt I e).source ∩
      (extChartAt I d).source ∩ (extChartAt I c).source by
      simpa only [extChartAt_source (I := I)] using
        (show x ∈ (chartAt H e).source ∩
          (chartAt H d).source ∩ (chartAt H c).source from
          ⟨⟨he, hd⟩, hc⟩))

/-! ## The actual preferred-chart partial atlas -/

/-- **Math.** The preferred charts of a manifold form a covered partial Jacobian atlas.
The totalized off-overlap values only make the structure total; all geometric
laws retain their source-membership hypotheses. -/
noncomputable def manifoldPartialJacobianAtlas :
    PartialJacobianAtlas M M E where
  domain := fun c x => x ∈ (chartAt H c).source
  cover := by
    intro x
    refine ⟨x, ?_⟩
    simpa only [extChartAt_source (I := I)] using
      (mem_extChartAt_source (I := I) x)
  jacobian := manifoldChartJacobian (I := I)
  jacobian_self := manifoldChartJacobian_self (I := I)
  jacobian_cocycle := by
    intro c d e x hc hd he
    exact manifoldChartJacobian_cocycle (I := I) hc hd he

@[simp] theorem manifoldPartialJacobianAtlas_domain (c x : M) :
    (manifoldPartialJacobianAtlas (I := I)).domain c x =
      (x ∈ (chartAt H c).source) :=
  rfl

/-! ## Concrete metric tensor assembly -/

section GramAssembly

open Riemannian

variable [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]

/-- **Math.** The chart Gram tensors of a Riemannian metric assemble over the genuine
preferred-chart domains.  This is a quotient-valued tensor field, so it does
not yet assert a smooth vector-bundle structure. -/
noncomputable def manifoldChartGramTensorField
    (g : RiemannianMetric I M) :
    GlobalAtlasTensorField
      (manifoldPartialJacobianAtlas (I := I) (E := E) (H := H) (M := M)) := by
  apply GlobalAtlasTensorField.ofGluing
    (manifoldPartialJacobianAtlas (I := I) (E := E) (H := H) (M := M))
    (fun c x => chartGramTensor (I := I) g c x)
  intro c d x hc hd
  change x ∈ (chartAt H c).source at hc
  change x ∈ (chartAt H d).source at hd
  apply Subtype.ext
  ext a b
  change chartMetricInner (I := I) g d (extChartAt I d x) a b =
    chartMetricInner (I := I) g c (extChartAt I c x)
      (manifoldChartJacobian (I := I) c d x a)
      (manifoldChartJacobian (I := I) c d x b)
  rw [manifoldChartJacobian_apply_of_mem hc hd,
    manifoldChartJacobian_apply_of_mem hc hd]
  have hc' : x ∈ (chartAt H c).source := by
    simpa only [extChartAt_source (I := I)] using hc
  have hd' : x ∈ (chartAt H d).source := by
    simpa only [extChartAt_source (I := I)] using hd
  exact chartMetricInner_change (I := I) g c d hc' hd' a b

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem manifoldChartGramTensorField_localTensor
    (g : RiemannianMetric I M) :
    (manifoldChartGramTensorField (I := I) g).localTensor =
      (fun c x => chartGramTensor (I := I) g c x) :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem manifoldChartGramTensorField_value_eq_chart
    (g : RiemannianMetric I M) (x c : M)
    (hc : x ∈ (chartAt H c).source) :
    (manifoldChartGramTensorField (I := I) g).value x =
      ⟦⟨x, c, chartGramTensor (I := I) g c x, hc⟩⟧ := by
  exact GlobalAtlasTensorField.ofGluing_value_eq_local
    (manifoldPartialJacobianAtlas (I := I) (E := E) (H := H) (M := M))
    (fun c x => chartGramTensor (I := I) g c x)
    (by
      intro c d x hc hd
      change x ∈ (chartAt H c).source at hc
      change x ∈ (chartAt H d).source at hd
      apply Subtype.ext
      ext a b
      change chartMetricInner (I := I) g d (extChartAt I d x) a b =
        chartMetricInner (I := I) g c (extChartAt I c x)
          (manifoldChartJacobian (I := I) c d x a)
          (manifoldChartJacobian (I := I) c d x b)
      rw [manifoldChartJacobian_apply_of_mem hc hd,
        manifoldChartJacobian_apply_of_mem hc hd]
      have hc' : x ∈ (chartAt H c).source := by
        simpa only [extChartAt_source (I := I)] using hc
      have hd' : x ∈ (chartAt H d).source := by
        simpa only [extChartAt_source (I := I)] using hd
      exact chartMetricInner_change (I := I) g c d hc' hd' a b)
    x c hc

end GramAssembly

end ParabolicPDE
end Topping

end
