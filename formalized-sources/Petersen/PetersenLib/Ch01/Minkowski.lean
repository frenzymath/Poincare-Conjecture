import PetersenLib.Ch01.RiemannianManifolds

/-!
# Petersen Ch. 1, Example 1.1.6 — Minkowski space

The pseudo-Riemannian metric of index `n₂` on `ℝ^{n₁,n₂} = ℝ^{n₁} × ℝ^{n₂}`,
`g(v, w) = v₁ ⋅ w₁ - v₂ ⋅ w₂`, formalized for a product `F₁ × F₂` of real
inner product spaces:

* `constantForm_contMDiff`: a constant-coefficient bilinear form on a vector
  space (viewed as a manifold over itself) is a smooth section of the bundle
  of bilinear forms on the tangent spaces.
* `pullbackPseudoForm` / `pullbackPseudoForm_contMDiff`: the pullback of a
  pseudo-Riemannian metric along a smooth map, and its smoothness (the
  pseudo-Riemannian analogue of `pullbackForm_contMDiff`).
* `minkowskiForm`: the bilinear form `⟪v₁, w₁⟫ - ⟪v₂, w₂⟫` on `F₁ × F₂`.
* `minkowskiMetric`: the corresponding pseudo-Riemannian metric
  (Petersen Example 1.1.6).
* `minkowskiMetric_index`: its index is `dim F₂`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Example 1.1.6.
-/

open Bundle Bornology
open scoped ContDiff Manifold Topology RealInnerProductSpace

noncomputable section

namespace PetersenLib

/-! ## Constant bilinear forms are smooth sections -/

section ConstantForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** On a vector space `F` viewed as a manifold over itself, a
*constant* family of bilinear forms `x ↦ B` is a smooth section of the bundle
of bilinear forms on the tangent spaces: in the canonical trivialization
`TF ≃ F × F` the section is literally constant. This is the smoothness input
for constant-coefficient (pseudo-)metrics such as the Euclidean and Minkowski
metrics (Petersen Examples 1.1.1, 1.1.6). -/
theorem constantForm_contMDiff (B : F →L[ℝ] F →L[ℝ] ℝ) :
    ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, B⟩ : Bundle.TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x →L[ℝ] ℝ))) := by
  intro x
  rw [contMDiffAt_section]
  convert contMDiffAt_const (c := B)
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

end ConstantForm

/-! ## Pullback of pseudo-Riemannian metrics

The pseudo-Riemannian analogue of `pullbackForm`: the induced form
`(F^*g)(u, v) = g(DF(u), DF(v))` and its smoothness. Positivity is of course
not inherited in general; it must be established separately (as in the
hyperbolic-space example, Petersen Example 1.1.7). -/

section PullbackPseudo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** The **pullback of a pseudo-Riemannian metric** along `F : M → M'`:
the bilinear form `(F^*g_N)(u, v) = g_N(DF(u), DF(v))` on `T_pM` (Petersen
§1.1; used with the Minkowski metric in Example 1.1.7). -/
def pullbackPseudoForm (gN : PseudoRiemannianMetric I' M') (F : M → M') (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let A : E →L[ℝ] E' := mfderiv I I' F p
  let B : E' →L[ℝ] E' →L[ℝ] ℝ := gN.inner (F p)
  (B.bilinearComp A A : E →L[ℝ] E →L[ℝ] ℝ)

omit [IsManifold I ∞ M] in
@[simp]
theorem pullbackPseudoForm_apply (gN : PseudoRiemannianMetric I' M') (F : M → M') (p : M)
    (u v : TangentSpace I p) :
    pullbackPseudoForm gN F p u v =
      gN.inner (F p) (mfderiv I I' F p u) (mfderiv I I' F p v) :=
  rfl

omit [IsManifold I ∞ M] in
/-- **Math.** The pullback of a pseudo-Riemannian metric is symmetric,
inherited from the symmetry of `gN`. -/
theorem pullbackPseudoForm_symm (gN : PseudoRiemannianMetric I' M') (F : M → M') (p : M)
    (u v : TangentSpace I p) :
    pullbackPseudoForm gN F p u v = pullbackPseudoForm gN F p v u := by
  simp only [pullbackPseudoForm_apply]
  exact gN.symm _ _ _

/-- **Math.** The pullback-form section of a smooth map along a
pseudo-Riemannian metric varies smoothly. Identical in proof to
`pullbackForm_contMDiff`: in tangent coordinates around `x₀` the section
`x ↦ g_N(DF_x ·, DF_x ·)` is the composition of the coordinate differential
(smooth by `ContMDiffAt.mfderiv_const`) with the target metric read in
coordinates (smooth by `gN.contMDiff`). -/
theorem pullbackPseudoForm_contMDiff (gN : PseudoRiemannianMetric I' M') {F : M → M'}
    (hF : ContMDiff I I' ∞ F) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, pullbackPseudoForm gN F x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set sT := trivializationAt E (TangentSpace I) x₀ with hsT
  set tT := trivializationAt E' (TangentSpace I') (F x₀) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hfx₀ : F x₀ ∈ tT.baseSet := mem_baseSet_trivializationAt E' (TangentSpace I') (F x₀)
  set D : M → (E →L[ℝ] E') := inTangentCoordinates I I' id F (fun x => mfderiv I I' F x) x₀ with hD
  have hDsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ D x₀ :=
    hF.contMDiffAt.mfderiv_const (by simp)
  set G : M' → (E' →L[ℝ] E' →L[ℝ] ℝ) := fun y =>
    ContinuousLinearMap.inCoordinates E' (TangentSpace I') (E' →L[ℝ] ℝ)
      (fun y => TangentSpace I' y →L[ℝ] ℝ) (F x₀) y (F x₀) y (gN.inner y) with hG
  have hGsmooth : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞ G (F x₀) :=
    ((contMDiffAt_hom_bundle _).mp gN.contMDiff.contMDiffAt).2
  have hΨ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => ((D x).precomp ℝ).comp ((G (F x)).comp (D x))) x₀ := by
    have h1 : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E' →L[ℝ] ℝ) ∞
        (fun x => (G (F x)).comp (D x)) x₀ :=
      (hGsmooth.comp x₀ hF.contMDiffAt).clm_comp hDsmooth
    exact (ContMDiffAt.clm_precomp (F₃ := ℝ) hDsmooth).clm_comp h1
  refine hΨ.congr_of_eventuallyEq ?_
  have hUs : {x | x ∈ sT.baseSet} ∈ 𝓝 x₀ := sT.open_baseSet.mem_nhds hx₀
  have hUt : {x | F x ∈ tT.baseSet} ∈ 𝓝 x₀ :=
    hF.continuous.continuousAt (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [hUs, hUt] with x hx hfx
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  have hRHS : (((ContinuousLinearMap.precomp ℝ (D x)).comp ((G (F x)).comp (D x))) a) b
      = G (F x) (D x a) (D x b) := rfl
  have hkey : ∀ u : E, tT.symm (F x) (D x u) = mfderiv I I' F x (sT.symm x u) := by
    intro u
    have hDu : D x u = tT.continuousLinearEquivAt ℝ (F x) hfx
        (mfderiv I I' F x ((sT.continuousLinearEquivAt ℝ x hx).symm u)) := by
      rw [hD]
      simp only [inTangentCoordinates, id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
      rfl
    have hcoeT : (tT.symm (F x) : E' → TangentSpace I' (F x))
        = ⇑(tT.continuousLinearEquivAt ℝ (F x) hfx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq tT hfx]; rfl
    have hcoeS : (sT.symm x : E → TangentSpace I x)
        = ⇑(sT.continuousLinearEquivAt ℝ x hx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq sT hx]; rfl
    rw [hDu, hcoeT, ContinuousLinearEquiv.symm_apply_apply, hcoeS]
  rw [hRHS, hG]
  have htrivM' : trivializationAt ℝ (Bundle.Trivial M' ℝ) (F x₀)
      = Bundle.Trivial.trivialization M' ℝ :=
    Bundle.Trivial.eq_trivialization M' ℝ _
  have htrivM : trivializationAt ℝ (Bundle.Trivial M ℝ) x₀ = Bundle.Trivial.trivialization M ℝ :=
    Bundle.Trivial.eq_trivialization M ℝ _
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M' ℝ) hfx hfx (by simp)]
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hx hx (by simp)]
  simp only [htrivM', htrivM, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
    pullbackPseudoForm_apply, ← htT, ← hsT, hkey]

end PullbackPseudo

/-! ## Minkowski space (Petersen Example 1.1.6) -/

section Minkowski

variable (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂]

/-- **Math.** Petersen Example 1.1.6: the **Minkowski form** on
`ℝ^{n₁,n₂} = ℝ^{n₁} × ℝ^{n₂}`, formalized on a product `F₁ × F₂` of real inner
product spaces: writing `v = v₁ + v₂`, the form is
`g(v, w) = ⟪v₁, w₁⟫ - ⟪v₂, w₂⟫`. -/
def minkowskiForm : (F₁ × F₂) →L[ℝ] (F₁ × F₂) →L[ℝ] ℝ :=
  ((innerSL ℝ (E := F₁) : F₁ →L[ℝ] F₁ →L[ℝ] ℝ).bilinearComp
      (ContinuousLinearMap.fst ℝ F₁ F₂) (ContinuousLinearMap.fst ℝ F₁ F₂)) -
    ((innerSL ℝ (E := F₂) : F₂ →L[ℝ] F₂ →L[ℝ] ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ F₁ F₂) (ContinuousLinearMap.snd ℝ F₁ F₂))

@[simp]
theorem minkowskiForm_apply (v w : F₁ × F₂) :
    minkowskiForm F₁ F₂ v w = ⟪v.1, w.1⟫ - ⟪v.2, w.2⟫ :=
  rfl

/-- **Math.** The Minkowski form is symmetric. -/
theorem minkowskiForm_comm (v w : F₁ × F₂) :
    minkowskiForm F₁ F₂ v w = minkowskiForm F₁ F₂ w v := by
  simp only [minkowskiForm_apply, real_inner_comm]

/-- **Math.** Nondegeneracy witness for the Minkowski form: for `v ≠ 0`, the
"time-reflected" vector `w = (v₁, -v₂)` pairs to
`g(v, w) = ‖v₁‖² + ‖v₂‖² > 0`. -/
theorem minkowskiForm_self_flip_ne_zero {v : F₁ × F₂} (hv : v ≠ 0) :
    minkowskiForm F₁ F₂ v (v.1, -v.2) ≠ 0 := by
  have hval : minkowskiForm F₁ F₂ v (v.1, -v.2) = ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
    rw [minkowskiForm_apply, inner_neg_right, sub_neg_eq_add,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  rw [hval]
  intro hzero
  apply hv
  have h1 : ‖v.1‖ ^ 2 = 0 ∧ ‖v.2‖ ^ 2 = 0 := by
    constructor <;> nlinarith [sq_nonneg ‖v.1‖, sq_nonneg ‖v.2‖]
  have hv1 : v.1 = 0 := by
    have := h1.1
    rwa [pow_eq_zero_iff (two_ne_zero), norm_eq_zero] at this
  have hv2 : v.2 = 0 := by
    have := h1.2
    rwa [pow_eq_zero_iff (two_ne_zero), norm_eq_zero] at this
  exact Prod.ext hv1 hv2

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Petersen Example 1.1.6 — **Minkowski space**. For
`n = n₁ + n₂` write `ℝ^{n₁,n₂} = ℝ^{n₁} × ℝ^{n₂}` and split vectors as
`v = v₁ + v₂`. The pseudo-Riemannian metric of index `n₂`
`g((p,v), (p,w)) = v₁ ⋅ w₁ - v₂ ⋅ w₂` is natural on `ℝ^{n₁,n₂}`. When
`n₁ = 1` or `n₂ = 1` this is (a version of) Minkowski space, describing the
geometry of special-relativistic space-time. Formalized on `F₁ × F₂` for real
inner product spaces `F₁`, `F₂`; the index computation is
`minkowskiMetric_index`. -/
def minkowskiMetric : PseudoRiemannianMetric 𝓘(ℝ, F₁ × F₂) (F₁ × F₂) where
  inner _ := minkowskiForm F₁ F₂
  symm _ u v := minkowskiForm_comm F₁ F₂ u v
  nondegenerate _x v hv :=
    let v' : F₁ × F₂ := v
    ⟨(v'.1, -v'.2), minkowskiForm_self_flip_ne_zero F₁ F₂ hv⟩
  contMDiff := constantForm_contMDiff (minkowskiForm F₁ F₂)

@[simp]
theorem minkowskiMetric_inner (x : F₁ × F₂) :
    (minkowskiMetric F₁ F₂).inner x = minkowskiForm F₁ F₂ :=
  rfl

variable [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Petersen Example 1.1.6: the Minkowski metric on
`F₁ × F₂` has **index `dim F₂`**. The subspace `0 × F₂` is negative definite
of dimension `dim F₂`; conversely any negative-definite subspace `W` meets
`F₁ × 0` trivially (on it the form is `‖v₁‖² ≥ 0`), so the projection to `F₂`
is injective on `W` and `dim W ≤ dim F₂`. -/
theorem minkowskiMetric_index (x : F₁ × F₂) :
    pseudoRiemannianIndex (minkowskiMetric F₁ F₂) x = Module.finrank ℝ F₂ := by
  show sSup {m : ℕ | ∃ W : Submodule ℝ (TangentSpace 𝓘(ℝ, F₁ × F₂) x),
      Module.finrank ℝ W = m ∧ IsNegDefOn (minkowskiMetric F₁ F₂) x W}
    = Module.finrank ℝ F₂
  -- the subspace `0 × F₂` is negative definite of full index dimension
  have hmem : Module.finrank ℝ F₂ ∈ {m : ℕ |
      ∃ W : Submodule ℝ (TangentSpace 𝓘(ℝ, F₁ × F₂) x),
        Module.finrank ℝ W = m ∧ IsNegDefOn (minkowskiMetric F₁ F₂) x W} := by
    refine ⟨Submodule.snd ℝ F₁ F₂, (Submodule.sndEquiv ℝ F₁ F₂).finrank_eq, ?_⟩
    intro v hv hvne
    let v' : F₁ × F₂ := v
    have hv1 : v'.1 = 0 := by
      simpa [Submodule.snd, Submodule.mem_comap] using hv
    have hv2 : v'.2 ≠ 0 := by
      intro h2
      exact hvne (Prod.ext hv1 h2)
    show minkowskiForm F₁ F₂ v' v' < 0
    rw [minkowskiForm_apply, hv1, inner_zero_left, zero_sub, neg_lt_zero,
      real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hv2) 2
  -- any negative-definite subspace injects into `F₂` under the projection
  have hub : ∀ m ∈ {m : ℕ | ∃ W : Submodule ℝ (TangentSpace 𝓘(ℝ, F₁ × F₂) x),
      Module.finrank ℝ W = m ∧ IsNegDefOn (minkowskiMetric F₁ F₂) x W},
      m ≤ Module.finrank ℝ F₂ := by
    rintro m ⟨W, hWm, hWneg⟩
    subst hWm
    let f : W →ₗ[ℝ] F₂ :=
      (LinearMap.snd ℝ F₁ F₂).comp (W.subtype : W →ₗ[ℝ] (F₁ × F₂))
    have hker : ∀ u : W, f u = 0 → u = 0 := by
      intro u hu
      by_contra hne
      have hune : (u : TangentSpace 𝓘(ℝ, F₁ × F₂) x) ≠ 0 := fun h => hne (Subtype.ext h)
      have hneg := hWneg u u.2 hune
      let u' : F₁ × F₂ := (u : TangentSpace 𝓘(ℝ, F₁ × F₂) x)
      have hu2 : u'.2 = 0 := hu
      have hval : minkowskiForm F₁ F₂ u' u' = ‖u'.1‖ ^ 2 - ‖u'.2‖ ^ 2 := by
        rw [minkowskiForm_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      have hlt : minkowskiForm F₁ F₂ u' u' < 0 := hneg
      rw [hval, hu2, norm_zero] at hlt
      have hge : (0 : ℝ) ≤ ‖u'.1‖ ^ 2 := sq_nonneg _
      nlinarith [hlt, hge]
    have hinj : Function.Injective f :=
      LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
    exact LinearMap.finrank_le_finrank_of_injective hinj
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨_, hub⟩ hmem)

end Minkowski

end PetersenLib
