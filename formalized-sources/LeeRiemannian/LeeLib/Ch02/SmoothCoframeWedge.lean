/-
Chapter 2, "Riemannian Metrics": **smoothness of the wedge of a smooth coframe**.

The bundle Hodge star of Lee's Problem 2-18(a) is assembled locally from wedges of a smooth
orthonormal coframe, `x ↦ ε^{i_1}(x) ∧ ⋯ ∧ ε^{i_l}(x)`.  Making that a *smooth* section of
`Λ^l T^*M` is the one analytic ingredient the pointwise Hodge theory does not provide (the volume
form is only the top-degree case `l = n`, where `Λ^n` is a line and the "top forms are a line"
trick of `contMDiffAt_volumeForm` applies; it does not generalise to intermediate degree).

This file supplies it in two layers:

* **Pointwise** — `wedgeCovectors`, as a function of its family of covectors, is a *smooth*
  (indeed continuous multilinear) map `(V^*)^l → Λ^l(V^*)` (`contDiff_wedgeCovectors`).  It is
  bundled as `wedgeCovectorsL`, a `ContinuousMultilinearMap`, built from the multilinear map
  `wedgeCovectorsM` (multilinearity is the row-linearity of the determinant, `Matrix.det_updateRow_add`
  and `_smul`) together with the Leibniz bound `‖f_1 ∧ ⋯ ∧ f_l‖ ≤ l! · ∏ ‖f_i‖`
  (`norm_wedgeCovectors_apply_le`).
* **Bundle** — `contMDiffAt_wedgeCovectors_section`: if `α_1, …, α_l` are smooth sections of the
  dual bundle `T^*M`, then `x ↦ α_1(x) ∧ ⋯ ∧ α_l(x)` is a smooth section of `Λ^l T^*M`.  The proof
  reads the section through the trivialisation of the bundle of `l`-forms, where the fibre value is
  `wedgeCovectors (α x) ∘ e.symmL x = wedgeCovectors (fun r ↦ α_r x ∘ e.symmL x)`
  (`wedgeCovectors_compContinuousLinearMap`), whose covector arguments are the smooth coordinate
  representations of the `α_r`; the pointwise `contDiff_wedgeCovectors` then finishes it, exactly as
  `Bundle.contMDiffAt_formProduct` handles the tensor product of two smooth `1`-forms.
-/
import LeeLib.Ch02.VolumeForm
import LeeLib.Ch02.FormProduct

namespace LeeLib.Ch02

open Bundle Module InnerProductSpace ContinuousLinearMap
open scoped Manifold ContDiff InnerProductSpace Matrix

noncomputable section

/-! ### Pointwise: the wedge of covectors is a smooth function of the covectors -/

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {l : ℕ}

/-- Writing the matrix `[(update f i z)_a(v_b)]` as a row-update of `[f_a(v_b)]`. -/
theorem wedgeCovectors_matrix_updateRow (f : Fin l → V →L[ℝ] ℝ) (i : Fin l)
    (z : V →L[ℝ] ℝ) (v : Fin l → V) :
    (Matrix.of fun a b => (Function.update f i z) a (v b))
      = (Matrix.of fun a b => f a (v b)).updateRow i (fun b => z (v b)) :=
  Matrix.ext fun a b => by
    rcases eq_or_ne a i with rfl | ha
    · simp [Function.update_self, Matrix.updateRow_self]
    · simp [Matrix.updateRow_ne ha, Function.update_of_ne ha]

/-- Additivity of `wedgeCovectors` in one covector slot: row-additivity of the determinant. -/
theorem wedgeCovectors_update_add (f : Fin l → V →L[ℝ] ℝ) (i : Fin l) (x y : V →L[ℝ] ℝ) :
    wedgeCovectors (Function.update f i (x + y))
      = wedgeCovectors (Function.update f i x) + wedgeCovectors (Function.update f i y) := by
  ext v
  rw [ContinuousAlternatingMap.add_apply, wedgeCovectors_apply, wedgeCovectors_apply,
    wedgeCovectors_apply, wedgeCovectors_matrix_updateRow, wedgeCovectors_matrix_updateRow,
    wedgeCovectors_matrix_updateRow,
    show (fun b => (x + y) (v b)) = (fun b => x (v b)) + (fun b => y (v b)) from by ext b; simp,
    Matrix.det_updateRow_add]

/-- Homogeneity of `wedgeCovectors` in one covector slot: row-homogeneity of the determinant. -/
theorem wedgeCovectors_update_smul (f : Fin l → V →L[ℝ] ℝ) (i : Fin l) (c : ℝ) (x : V →L[ℝ] ℝ) :
    wedgeCovectors (Function.update f i (c • x)) = c • wedgeCovectors (Function.update f i x) := by
  ext v
  rw [ContinuousAlternatingMap.smul_apply, wedgeCovectors_apply, wedgeCovectors_apply, smul_eq_mul,
    wedgeCovectors_matrix_updateRow, wedgeCovectors_matrix_updateRow,
    show (fun b => (c • x) (v b)) = c • (fun b => x (v b)) from by ext b; simp,
    Matrix.det_updateRow_smul]

/-- **The wedge of covectors as a multilinear map** in its family of covectors. -/
def wedgeCovectorsM : MultilinearMap ℝ (fun _ : Fin l => (V →L[ℝ] ℝ)) (V [⋀^Fin l]→L[ℝ] ℝ) where
  toFun := wedgeCovectors
  map_update_add' := by
    intro inst f i x y
    have e : ∀ z : V →L[ℝ] ℝ,
        @Function.update (Fin l) (fun _ => V →L[ℝ] ℝ) inst f i z
          = @Function.update (Fin l) (fun _ => V →L[ℝ] ℝ) (instDecidableEqFin l) f i z :=
      fun z => congrArg (fun d : DecidableEq (Fin l) =>
        @Function.update (Fin l) (fun _ => V →L[ℝ] ℝ) d f i z)
        (Subsingleton.elim inst (instDecidableEqFin l))
    rw [e, e, e]
    exact wedgeCovectors_update_add f i x y
  map_update_smul' := by
    intro inst f i c x
    have e : ∀ z : V →L[ℝ] ℝ,
        @Function.update (Fin l) (fun _ => V →L[ℝ] ℝ) inst f i z
          = @Function.update (Fin l) (fun _ => V →L[ℝ] ℝ) (instDecidableEqFin l) f i z :=
      fun z => congrArg (fun d : DecidableEq (Fin l) =>
        @Function.update (Fin l) (fun _ => V →L[ℝ] ℝ) d f i z)
        (Subsingleton.elim inst (instDecidableEqFin l))
    rw [e, e]
    exact wedgeCovectors_update_smul f i c x

@[simp] theorem wedgeCovectorsM_apply (f : Fin l → (V →L[ℝ] ℝ)) :
    wedgeCovectorsM f = wedgeCovectors f := rfl

/-- **The Leibniz bound** `‖f_1 ∧ ⋯ ∧ f_l‖ ≤ l! · (∏ ‖f_i‖) · (∏ ‖v_j‖)`, the operator-norm
estimate needed to promote `wedgeCovectorsM` to a continuous multilinear map.  Each of the `l!`
permutation terms of the determinant is bounded by `∏_i ‖f_i‖ · ∏_j ‖v_j‖`. -/
theorem norm_wedgeCovectors_apply_le (f : Fin l → (V →L[ℝ] ℝ)) (v : Fin l → V) :
    ‖wedgeCovectors f v‖ ≤ (l.factorial : ℝ) * (∏ i, ‖f i‖) * ∏ j, ‖v j‖ := by
  rw [wedgeCovectors_apply, Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun _ : Equiv.Perm (Fin l) => (∏ i, ‖f i‖) * ∏ j, ‖v j‖)
    fun σ _ => ?_).trans ?_
  · have hnorm : ‖Equiv.Perm.sign σ • ∏ a, (Matrix.of fun a b => f a (v b)) (σ a) a‖
        = ‖∏ a, (Matrix.of fun a b => f a (v b)) (σ a) a‖ := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
    rw [hnorm]
    simp only [Matrix.of_apply]
    refine (Finset.norm_prod_le _ _).trans ?_
    refine (Finset.prod_le_prod (fun a _ => norm_nonneg _)
      (fun a _ => (f (σ a)).le_opNorm (v a))).trans ?_
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => ‖f i‖)]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
      mul_assoc]

/-- **The wedge of covectors as a continuous multilinear map** in its family of covectors. -/
def wedgeCovectorsL :
    ContinuousMultilinearMap ℝ (fun _ : Fin l => (V →L[ℝ] ℝ)) (V [⋀^Fin l]→L[ℝ] ℝ) :=
  wedgeCovectorsM.mkContinuous (l.factorial : ℝ) fun f => by
    rw [ContinuousAlternatingMap.opNorm_le_iff (by positivity)]
    intro v
    exact norm_wedgeCovectors_apply_le f v

@[simp] theorem wedgeCovectorsL_apply (f : Fin l → (V →L[ℝ] ℝ)) :
    wedgeCovectorsL f = wedgeCovectors f := rfl

/-- **The wedge of covectors depends smoothly on the covectors** — a continuous multilinear map is
`C^∞`.  This is the pointwise core of the smoothness of the bundle Hodge star. -/
theorem contDiff_wedgeCovectors :
    ContDiff ℝ ∞ (fun f : Fin l → (V →L[ℝ] ℝ) => wedgeCovectors f) := by
  have h : (fun f : Fin l → (V →L[ℝ] ℝ) => wedgeCovectors f)
      = ⇑(wedgeCovectorsL (V := V) (l := l)) := funext fun f => (wedgeCovectorsL_apply f).symm
  rw [h]
  exact (wedgeCovectorsL (V := V) (l := l)).contDiff

end Pointwise

/-! ### `wedgeCovectors` commutes with precomposition by a continuous linear map -/

/-- Precomposing `f_1 ∧ ⋯ ∧ f_l` with a continuous linear map `φ` wedges the precomposed covectors:
`(f_1 ∧ ⋯ ∧ f_l) ∘ φ = (f_1 ∘ φ) ∧ ⋯ ∧ (f_l ∘ φ)`.  Both sides are `det [f_r(φ v_s)]`.  This is the
identity that reads the wedge of a coframe in a trivialisation. -/
theorem wedgeCovectors_compContinuousLinearMap {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] {l : ℕ}
    (f : Fin l → (V →L[ℝ] ℝ)) (φ : W →L[ℝ] V) :
    (wedgeCovectors f).compContinuousLinearMap φ = wedgeCovectors (fun r => (f r).comp φ) := by
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, wedgeCovectors_apply,
    wedgeCovectors_apply]
  rfl

/-! ### The bundle layer: a wedge of smooth coframe sections is a smooth `l`-form -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
/-- **A wedge of smooth `1`-form fields is a smooth `l`-form field.**

If `α_1, …, α_l` are smooth sections of the cotangent bundle `T^*M`, then the pointwise wedge
`x ↦ α_1(x) ∧ ⋯ ∧ α_l(x)` is a smooth section of `Λ^l T^*M`.  This is the wedge-covector analogue of
`Bundle.contMDiffAt_formProduct` and the intermediate-degree generalisation of
`contMDiffAt_volumeForm`.  Read through the trivialisation of the bundle of `l`-forms over `x₀`, the
fibre value at `x` is `wedgeCovectors (α · x) ∘ e.symmL x`, which by
`wedgeCovectors_compContinuousLinearMap` is `wedgeCovectors (fun r ↦ α_r x ∘ e.symmL x)`; the
covector arguments `α_r x ∘ e.symmL x` are the smooth coordinate representations of the `α_r`
(`contMDiffAt_hom_bundle`), and the pointwise `contDiff_wedgeCovectors` finishes it. -/
theorem contMDiffAt_wedgeCovectors_section {l : ℕ}
    {α : Fin l → ∀ x : M, (TangentSpace I x →L[ℝ] ℝ)} {x₀ : M}
    (hα : ∀ r, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) →L[ℝ] ℝ) x (α r x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] ℝ)
        (E := fun x => (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ) x
          (wedgeCovectors (fun r => α r x))) x₀ := by
  set e := trivializationAt E (TangentSpace I) x₀ with he
  have hx₀e : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  set A : Fin l → M → (E →L[ℝ] ℝ) := fun r x =>
    ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (Bundle.Trivial M ℝ) x₀ x x₀ x (α r x)
    with hA
  have hAs : ∀ r, ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ∞ (A r) x₀ :=
    fun r => ((contMDiffAt_hom_bundle _).mp (hα r)).2
  have hcand : ContMDiffAt I 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] ℝ) ∞
      (fun x => wedgeCovectors (fun r => A r x)) x₀ :=
    (contDiff_wedgeCovectors (V := E) (l := l)).contDiffAt.comp_contMDiffAt
      (contMDiffAt_pi_space.2 hAs)
  rw [contMDiffAt_section]
  refine hcand.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx₀e] with x hx
  show (trivializationAt (E [⋀^Fin l]→L[ℝ] ℝ)
      (fun x : M => (TangentSpace I x) [⋀^Fin l]→L[ℝ] ℝ) x₀
        ⟨x, wedgeCovectors (fun r => α r x)⟩).2 = wedgeCovectors (fun r => A r x)
  show (wedgeCovectors (fun r => α r x)).compContinuousLinearMap (e.symmL ℝ x)
      = wedgeCovectors (fun r => A r x)
  rw [wedgeCovectors_compContinuousLinearMap]
  refine congrArg wedgeCovectors (funext fun r => ContinuousLinearMap.ext fun ξ => ?_)
  rw [hA]
  simp only [ContinuousLinearMap.comp_apply]
  rw [inCoordinates_dual_apply hx]
  rfl

end

end LeeLib.Ch02
