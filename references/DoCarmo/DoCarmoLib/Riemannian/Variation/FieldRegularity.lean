import DoCarmoLib.Riemannian.Variation.Basic
import Mathlib.Algebra.Group.Ext
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Regularity of the variational field

This file packages the raw model-space value `variationalField I f t` together
with its foot `f (0, t)`.  On each smooth strip of a variation this bundled
field is the tangent map of the surface applied to the parameter-axis vector
`(1, 0)`, so smoothness of tangent maps gives the expected loss of one
derivative.
-/

open Bundle Set
open scoped ContDiff Manifold Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** The variational field as an intrinsic field along the zero
slice, rather than as its own-foot model-space coordinate alone. -/
def variationalFieldBundle (I : ModelWithCorners ℝ E H)
    (f : ℝ × ℝ → M) (t : ℝ) : TangentBundle I M :=
  by
    refine ⟨f (0, t), ?_⟩
    change E
    exact variationalField I f t

@[simp] theorem variationalFieldBundle_proj (I : ModelWithCorners ℝ E H)
    (f : ℝ × ℝ → M) (t : ℝ) :
    (variationalFieldBundle I f t).1 = f (0, t) :=
  rfl

@[simp] theorem variationalFieldBundle_snd (I : ModelWithCorners ℝ E H)
    (f : ℝ × ℝ → M) (t : ℝ) :
    (variationalFieldBundle I f t).2 = variationalField I f t := by
  change variationalField I f t = variationalField I f t
  rfl

/-- **Math.** The bundled variational field lies over the curve being varied. -/
theorem IsVariationOfOrder.variationalFieldBundle_proj_eq
    {r : ℕ∞ω} {c : ℝ → M} {a ε t : ℝ} {f : ℝ × ℝ → M}
    (hf : IsVariationOfOrder I r c a ε f) (ht : t ∈ Icc 0 a) :
    (variationalFieldBundle I f t).1 = c t := by
  rw [variationalFieldBundle_proj]
  exact hf.zero_slice t ht

private theorem contMDiff_parameterAxisTangent (m : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ).tangent m
      (fun t : ℝ =>
        (⟨(0, t), (1, 0)⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) := by
  change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ).tangent m
    ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ × ℝ)).symm ∘
      fun t : ℝ => (((0, t), (1, 0)) : (ℝ × ℝ) × (ℝ × ℝ)))
  exact contMDiff_tangentBundleModelSpaceHomeomorph_symm.comp
    ((contMDiff_const.prodMk_space contMDiff_id).prodMk_space contMDiff_const)

private theorem mfderivWithin_parameterAxis_eq_variationalField
    {f : ℝ × ℝ → M} {ε u v t : ℝ}
    (hε : 0 < ε) (ht : t ∈ Icc u v)
    (hf : MDifferentiableWithinAt 𝓘(ℝ, ℝ × ℝ) I f
      (Ioo (-ε) ε ×ˢ Icc u v) (0, t)) :
    mfderivWithin 𝓘(ℝ, ℝ × ℝ) I f
        (Ioo (-ε) ε ×ˢ Icc u v) (0, t) (1, 0) =
      variationalField I f t := by
  let A : Set ℝ := Ioo (-ε) ε
  let j : ℝ → ℝ × ℝ := fun s => (s, t)
  have h0A : (0 : ℝ) ∈ A := by
    constructor <;> linarith
  have hA_nhds : A ∈ nhds (0 : ℝ) := isOpen_Ioo.mem_nhds h0A
  have hA_unique : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) A (0 : ℝ) :=
    isOpen_Ioo.uniqueMDiffOn 0 h0A
  have hj : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) j 0 := by
    have hid : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id : ℝ → ℝ) 0 :=
      mdifferentiableAt_id
    have hconst : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun _ : ℝ => t) 0 :=
      mdifferentiableAt_const
    simpa only [j, id_eq] using hid.prodMk_space hconst
  have hmaps : A ⊆ j ⁻¹' (Ioo (-ε) ε ×ˢ Icc u v) := by
    intro s hs
    exact ⟨hs, ht⟩
  have hcompWithin : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (f ∘ j) A 0 :=
    hf.comp 0 hj.mdifferentiableWithinAt hmaps
  have hcompAt : MDifferentiableAt 𝓘(ℝ, ℝ) I (f ∘ j) 0 :=
    hcompWithin.mdifferentiableAt hA_nhds
  have hchain := mfderivWithin_comp (I := 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, ℝ × ℝ)) (I'' := I) (x := (0 : ℝ))
    (f := j) (g := f) hf hj.mdifferentiableWithinAt hmaps hA_unique
  rw [mfderivWithin_eq_mfderiv hA_unique hcompAt,
    mfderivWithin_eq_mfderiv hA_unique hj] at hchain
  dsimp only [j] at hchain
  have happ := congrArg (fun L => L (1 : ℝ)) hchain
  have hjF : HasFDerivAt (fun s : ℝ => (s, t))
      (ContinuousLinearMap.inl ℝ ℝ ℝ) 0 := by
    convert (hasFDerivAt_id (0 : ℝ)).prodMk
      (hasFDerivAt_const t (0 : ℝ)) using 1
    · exact AddCommGroup.ext rfl
    · exact Module.ext rfl
    · rfl
    · apply ContinuousLinearMap.ext
      intro x
      simp
  have hj_apply : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun s : ℝ => (s, t)) 0 (1 : ℝ) = (1, 0) := by
    rw [mfderiv_eq_fderiv, hjF.fderiv]
    rfl
  change (mfderiv 𝓘(ℝ, ℝ) I (f ∘ fun s : ℝ => (s, t)) 0) 1 =
    mfderivWithin 𝓘(ℝ, ℝ × ℝ) I f
      (Ioo (-ε) ε ×ˢ Icc u v) (0, t)
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
          (fun s : ℝ => (s, t)) 0) 1) at happ
  rw [hj_apply] at happ
  change variationalField I f t =
    mfderivWithin 𝓘(ℝ, ℝ × ℝ) I f
      (Ioo (-ε) ε ×ˢ Icc u v) (0, t) (1, 0) at happ
  exact happ.symm

/-- **Math.** If a variation is piecewise `C^r`, then its intrinsic
variational field is piecewise `C^m` whenever `m + 1 ≤ r`.

The statement is bundle-valued: `variationalFieldBundle I f t` has foot
`f (0,t) = c(t)`, so it genuinely is a field along the zero slice. On each
strip it is the within-tangent map of `f` applied to the parameter-axis vector
`(1,0)`. -/
theorem IsVariationOfOrder.variationalFieldBundle_piecewise_contMDiff
    {r m : ℕ∞ω} {c : ℝ → M} {a ε : ℝ} {f : ℝ × ℝ → M}
    (hf : IsVariationOfOrder I r c a ε f) (hm : m + 1 ≤ r) :
    ∃ (n : ℕ) (τ : ℕ → ℝ),
      0 < n ∧ τ 0 = 0 ∧ τ n = a ∧
        (∀ i < n, τ i < τ (i + 1)) ∧
        ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I.tangent m
          (variationalFieldBundle I f) (Icc (τ i) (τ (i + 1))) := by
  rcases hf.piecewise_contMDiff with ⟨n, τ, hn, hτ0, hτn, hτ, hpieces⟩
  refine ⟨n, τ, hn, hτ0, hτn, hτ, ?_⟩
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := by
    constructor <;> linarith [hf.epsilon_pos]
  have hr0 : r ≠ 0 :=
    ne_of_gt ((by simp : (0 : ℕ∞ω) < m + 1).trans_le hm)
  intro i hi
  let S : Set (ℝ × ℝ) := Ioo (-ε) ε ×ˢ Icc (τ i) (τ (i + 1))
  have hS_unique : UniqueMDiffOn 𝓘(ℝ, ℝ × ℝ) S := by
    have hdiff : UniqueDiffOn ℝ S :=
      isOpen_Ioo.uniqueDiffOn.prod (uniqueDiffOn_Icc (hτ i hi))
    exact hdiff.uniqueMDiffOn
  have htangent := (hpieces i hi).contMDiffOn_tangentMapWithin hm hS_unique
  have hcomp := htangent.comp
    (contMDiff_parameterAxisTangent m).contMDiffOn
    (fun _ ht => ⟨hzero, ht⟩)
  refine hcomp.congr ?_
  intro t ht
  rw [Function.comp_apply, tangentMapWithin, variationalFieldBundle,
    Bundle.TotalSpace.mk_inj]
  have hmd : MDifferentiableWithinAt 𝓘(ℝ, ℝ × ℝ) I f
      (Ioo (-ε) ε ×ˢ Icc (τ i) (τ (i + 1))) (0, t) :=
    ((hpieces i hi) (0, t) ⟨hzero, ht⟩).mdifferentiableWithinAt hr0
  simpa using (mfderivWithin_parameterAxis_eq_variationalField
    (f := f) (ε := ε) (u := τ i) (v := τ (i + 1)) (t := t)
    hf.epsilon_pos ht hmd).symm

end Riemannian.Variation
