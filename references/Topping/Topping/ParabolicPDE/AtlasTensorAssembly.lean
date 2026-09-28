import Topping.ParabolicPDE.ChartSym2Bridge

/-!
# Domain-indexed atlas assembly for symmetric two-tensors

The chart-Jacobian and symmetric-two-tensor files provide total transition
maps for a common-domain proxy.  This module records the next geometric
boundary explicitly: chart transitions are only used where both chart domains
contain the base point, and a covering family assembles local tensor data into
a quotient-valued global field.  No atlas, bundle, or smoothness hypothesis is
silently manufactured; all domain and cocycle data remain fields of the
interface.
-/

open scoped Manifold Topology ContDiff Bundle
open Set Filter Function

noncomputable section

namespace Topping
namespace ParabolicPDE

/-! ## Partial Jacobian atlases -/

/-- **Math.** A domain-indexed family of coordinate Jacobians.

`domain c x` says that chart `c` is available at `x`.  The cocycle law is only
required when all three charts are available at the base point. -/
structure PartialJacobianAtlas (X C E : Type*)
    [AddCommMonoid E] [Module ℝ E] where
  domain : C → X → Prop
  cover : ∀ x, ∃ c, domain c x
  jacobian : C → C → X → E ≃ₗ[ℝ] E
  jacobian_self : ∀ c x,
    jacobian c c x = LinearEquiv.refl ℝ E
  jacobian_cocycle : ∀ c d e x,
    domain c x → domain d x → domain e x →
      (jacobian d e x).trans (jacobian c d x) = jacobian c e x

namespace PartialJacobianAtlas

variable {X C E : Type*} [AddCommMonoid E] [Module ℝ E]
  (A : PartialJacobianAtlas X C E)

/-- **Math.** Two chart domains overlap at a base point. -/
def overlap (c d : C) (x : X) : Prop :=
  A.domain c x ∧ A.domain d x

theorem overlap_symm {c d : C} {x : X}
    (h : A.overlap c d x) : A.overlap d c x :=
  ⟨h.2, h.1⟩

/-- **Math.** The inverse chart Jacobian is the opposite transition, on an overlap. -/
theorem jacobian_symm_eq {c d : C} {x : X}
    (hc : A.domain c x) (hd : A.domain d x) :
    A.jacobian d c x = (A.jacobian c d x).symm := by
  apply LinearEquiv.ext
  intro v
  apply (A.jacobian c d x).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := congrArg (fun e : E ≃ₗ[ℝ] E => e v)
    (A.jacobian_cocycle c d c x hc hd hc)
  simpa [LinearEquiv.trans_apply, A.jacobian_self] using h

end PartialJacobianAtlas

/-! ## Tensor representatives and their quotient -/

/-- **Math.** A symmetric covariant tensor represented in one chart.  The
domain witness is part of the representative, so quotient constructors never
silently use a chart outside its source. -/
structure AtlasTensorRepresentative
    {X C E : Type*} [AddCommMonoid E] [Module ℝ E]
    (A : PartialJacobianAtlas X C E) where
  base : X
  chart : C
  tensor : SymmetricTwoTensor E
  valid : A.domain chart base

namespace AtlasTensorRepresentative

variable {X C E : Type*} [AddCommMonoid E] [Module ℝ E]
  (A : PartialJacobianAtlas X C E)

/-- **Math.** Representatives agree when they have the same base and are
related by the induced covariant tensor transition.  Their domain witnesses
are carried by the representatives themselves. -/
def Equivalent (p q : AtlasTensorRepresentative A) : Prop :=
  p.base = q.base ∧
    q.tensor = sym2Pullback (A.jacobian p.chart q.chart p.base) p.tensor

theorem equivalent_refl (p : AtlasTensorRepresentative A) :
    Equivalent A p p := by
  refine ⟨rfl, ?_⟩
  · rw [A.jacobian_self p.chart p.base]
    rfl

theorem equivalent_symm {p q : AtlasTensorRepresentative A}
    (hpq : Equivalent A p q) : Equivalent A q p := by
  rcases hpq with ⟨hbase, ht⟩
  refine ⟨hbase.symm, ?_⟩
  have hqvalid : A.domain q.chart p.base := by
    simpa [← hbase] using q.valid
  rw [← hbase, ht, A.jacobian_symm_eq p.valid hqvalid]
  exact (sym2Pullback_inverse_left
    (A.jacobian p.chart q.chart p.base) p.tensor).symm

theorem equivalent_trans
    {p q r : AtlasTensorRepresentative A}
    (hpq : Equivalent A p q) (hqr : Equivalent A q r) :
    Equivalent A p r := by
  rcases hpq with ⟨hpq_base, hq⟩
  rcases hqr with ⟨hqr_base, hr⟩
  refine ⟨hpq_base.trans hqr_base, ?_⟩
  have hq_valid := q.valid
  rw [← hpq_base] at hq_valid
  have hr_valid := r.valid
  rw [← hqr_base, ← hpq_base] at hr_valid
  have hr' := hr
  rw [← hpq_base] at hr'
  calc
    r.tensor = sym2Pullback (A.jacobian q.chart r.chart p.base) q.tensor := hr'
    _ = sym2Pullback (A.jacobian q.chart r.chart p.base)
        (sym2Pullback (A.jacobian p.chart q.chart p.base) p.tensor) := by
      rw [hq]
    _ = sym2Pullback
        ((A.jacobian q.chart r.chart p.base).trans
          (A.jacobian p.chart q.chart p.base)) p.tensor := by
      exact sym2Pullback_comp _ _ _
    _ = sym2Pullback (A.jacobian p.chart r.chart p.base) p.tensor := by
      rw [A.jacobian_cocycle p.chart q.chart r.chart p.base
        p.valid hq_valid hr_valid]

end AtlasTensorRepresentative

/-- **Math.** The setoid of domain-compatible tensor representatives. -/
def atlasTensorSetoid
    {X C E : Type*} [AddCommMonoid E] [Module ℝ E]
    (A : PartialJacobianAtlas X C E) :
    Setoid (AtlasTensorRepresentative A) where
  r := AtlasTensorRepresentative.Equivalent A
  iseqv := by
    constructor
    · exact AtlasTensorRepresentative.equivalent_refl A
    · intro p q hpq
      exact AtlasTensorRepresentative.equivalent_symm A hpq
    · intro p q r hpq hqr
      exact AtlasTensorRepresentative.equivalent_trans A hpq hqr

/-- **Math.** Quotient-valued global symmetric tensor representatives. -/
abbrev GlobalAtlasTensor
    {X C E : Type*} [AddCommMonoid E] [Module ℝ E]
    (A : PartialJacobianAtlas X C E) :=
  Quotient (atlasTensorSetoid A)

/-! ## Covered global fields -/

/-- **Math.** A global field represented by local chart tensors. -/
structure GlobalAtlasTensorField
    {X C E : Type*} [AddCommMonoid E] [Module ℝ E]
    (A : PartialJacobianAtlas X C E) where
  localTensor : C → X → SymmetricTwoTensor E
  value : X → GlobalAtlasTensor A
  value_is_local : ∀ (x : X) (c : C) (hc : A.domain c x),
    value x = ⟦⟨x, c, localTensor c x, hc⟩⟧

namespace GlobalAtlasTensorField

variable {X C E : Type*} [AddCommMonoid E] [Module ℝ E]
  (A : PartialJacobianAtlas X C E)

noncomputable def chosenChart (x : X) : C :=
  Classical.choose (A.cover x)

theorem chosenChart_mem (x : X) : A.domain (chosenChart A x) x :=
  Classical.choose_spec (A.cover x)

/-- **Math.** Assemble a covered local tensor family satisfying the overlap gluing law. -/
noncomputable def ofGluing
    (localTensor : C → X → SymmetricTwoTensor E)
    (hglue : ∀ c d x, A.domain c x → A.domain d x →
      localTensor d x =
        sym2Pullback (A.jacobian c d x) (localTensor c x)) :
    GlobalAtlasTensorField A where
  localTensor := localTensor
  value := fun x =>
    ⟦⟨x, chosenChart A x, localTensor (chosenChart A x) x,
      chosenChart_mem A x⟩⟧
  value_is_local := by
    intro x c hc
    apply Quotient.sound
    refine ⟨rfl, ?_⟩
    exact hglue (chosenChart A x) c x (chosenChart_mem A x) hc

@[simp] theorem ofGluing_localTensor
    (localTensor : C → X → SymmetricTwoTensor E)
    (hglue : ∀ c d x, A.domain c x → A.domain d x →
      localTensor d x =
        sym2Pullback (A.jacobian c d x) (localTensor c x)) :
    (GlobalAtlasTensorField.ofGluing A localTensor hglue).localTensor = localTensor :=
  rfl

theorem ofGluing_value_eq_local
    (localTensor : C → X → SymmetricTwoTensor E)
    (hglue : ∀ c d x, A.domain c x → A.domain d x →
      localTensor d x =
        sym2Pullback (A.jacobian c d x) (localTensor c x))
    (x : X) (c : C) (hc : A.domain c x) :
    (GlobalAtlasTensorField.ofGluing A localTensor hglue).value x =
      ⟦⟨x, c, localTensor c x, hc⟩⟧ :=
  (GlobalAtlasTensorField.ofGluing A localTensor hglue).value_is_local x c hc

end GlobalAtlasTensorField

/-! ## Instantiation by the existing chart family -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M C X : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Math.** The existing common-domain chart family becomes a covered partial atlas
once a nonempty chart index is supplied. -/
noncomputable def CommonChartFamily.toPartialJacobianAtlas
    (A : CommonChartFamily I M C X) [Nonempty C] :
    PartialJacobianAtlas X C E where
  domain := fun c x =>
    A.point x ∈ (extChartAt I (A.center c)).source
  cover := by
    intro x
    let c : C := Classical.choice (inferInstance : Nonempty C)
    exact ⟨c, A.mem c x⟩
  jacobian := A.chartJacobian
  jacobian_self := by
    intro c x
    ext v
    rw [A.chartJacobian_apply,
      tangentCoordChange_self (I := I) (A.mem c x)]
    rfl
  jacobian_cocycle := by
    intro c d e x hc hd he
    exact A.jacobianCocycle.jacobian_cocycle c d e x

@[simp] theorem CommonChartFamily.toPartialJacobianAtlas_domain
    (A : CommonChartFamily I M C X) [Nonempty C]
    (c : C) (x : X) :
    (A.toPartialJacobianAtlas (I := I)).domain c x =
      ((A.point x) ∈ (extChartAt I (A.center c)).source) :=
  rfl

/-! ## A concrete Gram-field consumer -/

section GramAssembly

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M C X : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Math.** The chart Gram tensors assemble into the quotient-valued global
field supplied by the domain-indexed atlas.  The only compatibility input is
the concrete overlap gluing law; no smooth bundle structure is assumed here. -/
noncomputable def CommonChartFamily.chartGramTensorField
    (A : CommonChartFamily I M C X) (g : RiemannianMetric I M)
    [Nonempty C] :
    GlobalAtlasTensorField (A.toPartialJacobianAtlas (I := I)) := by
  apply GlobalAtlasTensorField.ofGluing
    (A.toPartialJacobianAtlas (I := I))
    (fun c x => chartGramTensor (I := I) g (A.center c) (A.point x))
  intro c d x hc hd
  have h := chartGramTensor_gluing A g c d x
  rw [JacobianCocycle.tensorTransition_apply] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem CommonChartFamily.chartGramTensorField_localTensor
    (A : CommonChartFamily I M C X) (g : RiemannianMetric I M)
    [Nonempty C] :
    (A.chartGramTensorField g).localTensor =
      (fun c x => chartGramTensor (I := I) g (A.center c) (A.point x)) :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem CommonChartFamily.chartGramTensorField_value_eq_chart
    (A : CommonChartFamily I M C X) (g : RiemannianMetric I M)
    [Nonempty C] (x : X) (c : C)
    (hc : A.point x ∈ (extChartAt I (A.center c)).source) :
    (A.chartGramTensorField g).value x =
      ⟦⟨x, c, chartGramTensor (I := I) g (A.center c) (A.point x), hc⟩⟧ := by
  exact GlobalAtlasTensorField.ofGluing_value_eq_local
    (A.toPartialJacobianAtlas (I := I))
    (fun c x => chartGramTensor (I := I) g (A.center c) (A.point x))
    (by
      intro c d x hc hd
      have h := chartGramTensor_gluing A g c d x
      rw [JacobianCocycle.tensorTransition_apply] at h
      exact h)
    x c hc

end GramAssembly

end ParabolicPDE
end Topping

end
