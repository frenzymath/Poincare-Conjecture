/-
Chapter 2, "Riemannian Metrics": the tensor product `α ⊗ β` of two 1-forms, and
the fact that it is a **smooth section of the bilinear-form bundle** when `α` and
`β` are smooth sections of the dual bundle.

Lee writes metrics as `g = g_{ij} dx^i ⊗ dx^j` throughout the chapter, so the
tensor product of two covectors is basic vocabulary.  Mathlib has the pointwise
operation — `ContinuousLinearMap.smulRight α β : v ↦ α v • β`, the rank-one
operator — but nothing that says the resulting *field* of bilinear forms is
smooth, and that is the one thing every construction of a metric out of 1-forms
needs.

The gap is structural rather than deep.  Mathlib's bundle API is generous about
*consuming* sections of a hom-bundle — `ContMDiffWithinAt.clm_bundle_apply` and
`clm_bundle_apply₂` apply such a section to smooth sections and give back a
smooth section — but it offers nothing for *producing* one, beyond the raw
characterization `contMDiffAt_hom_bundle` ("smooth iff smooth in coordinates").
`Mathlib.Geometry.Manifold.VectorBundle.Tensoriality` builds the *pointwise*
continuous linear map out of a tensorial operation and stops short of
smoothness.  So `α ⊗ β` has to be fed through `contMDiffAt_hom_bundle` by hand.

Doing so is worthwhile because the computation is trivial once written down:
reading a rank-one operator in a trivialization gives the rank-one operator on
the coordinate representations,

  `inCoordinates (α x ⊗ β x) = (α̂ x) ⊗ (β̂ x)`,

since `inCoordinates ϕ = Λ₂ ∘ ϕ ∘ Λ₁⁻¹` is linear in `ϕ` and the trivializations
pass through the `•`.  The smoothness of the right-hand side is then model-space
algebra, where `ContinuousLinearMap.smulRightL` — mathlib's bundling of
`smulRight` as a *continuous bilinear* map — makes it two applications of
`ContMDiffAt.clm_apply`.

The proof follows the shape of `LeeLib.Ch02.contMDiffAt_bilinearCompOf`, which
is the other place in this development where `contMDiffAt_hom_bundle` has to be
unfolded by hand: get the coordinate representations out of the hypotheses with
`contMDiffAt_hom_bundle`, exhibit a smooth model-space candidate, and identify
the two with `inCoordinates_apply_eq₂` on a neighbourhood where the
trivializations are defined.

Stated for a general vector bundle rather than for `TM`, matching
`Bundle.ContMDiffPseudoMetric`: nothing in the argument sees the tangent bundle.
-/
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Geometry.Manifold.VectorBundle.Hom

namespace Bundle

open Bundle ContinuousLinearMap Manifold
open scoped Manifold ContDiff Topology

section FormProduct

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- **The tensor product of two 1-forms**, `(α ⊗ β)(v, w) = α(v) · β(w)`.

Pointwise this is mathlib's `ContinuousLinearMap.smulRight`, the rank-one
operator `v ↦ α(v) • β`; the content of this file is that the *field* `x ↦ α_x ⊗ β_x`
is a smooth section of the bilinear-form bundle whenever `α` and `β` are smooth
sections of the dual bundle (`contMDiffAt_formProduct`).

Note `α ⊗ β` is not symmetric; Lee's `g = g_{ij} dx^i ⊗ dx^j` is symmetric only
because the coefficient matrix is. -/
noncomputable def formProduct (α β : ∀ x : B, E x →L[ℝ] ℝ) (x : B) :
    E x →L[ℝ] E x →L[ℝ] ℝ :=
  (α x).smulRight (β x)

omit [TopologicalSpace B] [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
@[simp] theorem formProduct_apply (α β : ∀ x : B, E x →L[ℝ] ℝ) (x : B) (v w : E x) :
    formProduct α β x v w = α x v * β x w := by
  simp [formProduct]

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- **Reading a 1-form in a trivialization**: the coordinate representation of a section
of the dual bundle, applied to a coordinate vector, is the form applied to the vector it
represents.

This is the one-slot analogue of `inCoordinates_apply_eq₂`, which mathlib states only for
the bilinear case.  The dual bundle is the hom-bundle into the trivial line bundle, whose
trivialization is the identity — that is the whole content. -/
theorem inCoordinates_dual_apply {α : ∀ x : B, E x →L[ℝ] ℝ} {x₀ x : B} {ξ : F}
    (hx : x ∈ (trivializationAt F E x₀).baseSet) :
    ContinuousLinearMap.inCoordinates F E ℝ (Bundle.Trivial B ℝ) x₀ x x₀ x (α x) ξ
      = α x ((trivializationAt F E x₀).symm x ξ) := by
  rw [ContinuousLinearMap.inCoordinates_eq hx (by simp)]
  simp

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- **The tensor product of two smooth 1-forms is a smooth section of the bilinear-form
bundle.**

This is the piece mathlib is missing: `clm_bundle_apply`/`clm_bundle_apply₂` *consume* a
smooth section of a hom-bundle, and nothing *produces* one, so `α ⊗ β` has to be pushed
through the raw characterization `contMDiffAt_hom_bundle` by hand.

The computation is the identity `inCoordinates (α ⊗ β) = (inCoordinates α) ⊗ (inCoordinates β)`:
reading a rank-one operator in a trivialization gives the rank-one operator on the coordinate
representations, because `inCoordinates ϕ = Λ₂ ∘ ϕ ∘ Λ₁⁻¹` is linear and so passes through the
`•` defining `smulRight`.  The coordinate representations are smooth by hypothesis, and
`ContinuousLinearMap.smulRightL` — `smulRight` bundled as a continuous *bilinear* map — turns
the model-space claim into two applications of `ContMDiffAt.clm_apply`. -/
theorem contMDiffAt_formProduct {α β : ∀ x : B, E x →L[ℝ] ℝ} {x₀ : B}
    (hα : ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun x ↦ E x →L[ℝ] Bundle.Trivial B ℝ x) x (α x)) x₀)
    (hβ : ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun x ↦ E x →L[ℝ] Bundle.Trivial B ℝ x) x (β x)) x₀) :
    ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) x (formProduct α β x)) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  -- the coordinate representations of `α` and `β`, smooth by hypothesis
  set A : B → (F →L[ℝ] ℝ) := fun x ↦
    ContinuousLinearMap.inCoordinates F E ℝ (Bundle.Trivial B ℝ) x₀ x x₀ x (α x) with hAdef
  set A' : B → (F →L[ℝ] ℝ) := fun x ↦
    ContinuousLinearMap.inCoordinates F E ℝ (Bundle.Trivial B ℝ) x₀ x x₀ x (β x) with hA'def
  have hAs : ContMDiffAt IB 𝓘(ℝ, F →L[ℝ] ℝ) n A x₀ := ((contMDiffAt_hom_bundle _).mp hα).2
  have hA's : ContMDiffAt IB 𝓘(ℝ, F →L[ℝ] ℝ) n A' x₀ := ((contMDiffAt_hom_bundle _).mp hβ).2
  -- the model-space candidate `ξ ↦ A ξ ⊗ A' ξ`, smooth because `smulRight` is bilinear.
  -- Note this cannot go through `ContMDiffAt.clm_apply` on the bundled `smulRightL`: that
  -- would need the model space `𝓘(ℝ, (F →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)`,
  -- and mathlib's operator-norm instance does not reach a `NormedAddCommGroup` there (it
  -- stops once the *domain* is itself an operator space).  Composing the bounded bilinear
  -- map on the outside keeps every type at depth ≤ 2, where the instances do exist.
  have hpair : ContMDiffAt IB 𝓘(ℝ, (F →L[ℝ] ℝ) × (F →L[ℝ] ℝ)) n (fun x ↦ (A x, A' x)) x₀ :=
    hAs.prodMk_space hA's
  have hbil : ContDiff ℝ n (fun p : (F →L[ℝ] ℝ) × (F →L[ℝ] ℝ) ↦ p.1.smulRight p.2) :=
    ContDiff.smulRight contDiff_fst contDiff_snd
  have hcand : ContMDiffAt IB 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n
      (fun x ↦ (A x).smulRight (A' x)) x₀ :=
    hbil.contDiffAt.comp_contMDiffAt hpair
  refine hcand.congr_of_eventuallyEq ?_
  -- on the base set of the trivialization the two agree, by `inCoordinates_apply_eq₂`
  filter_upwards [(trivializationAt F E x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x₀)] with x hx
  refine ContinuousLinearMap.ext fun ξ ↦ ContinuousLinearMap.ext fun η ↦ ?_
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial B ℝ) hx hx (by simp)]
  simp [hAdef, hA'def, inCoordinates_dual_apply hx, Bundle.Trivial.eq_trivialization B ℝ _]

end FormProduct

end Bundle
