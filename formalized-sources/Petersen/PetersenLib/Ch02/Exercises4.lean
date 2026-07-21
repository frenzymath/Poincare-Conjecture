import PetersenLib.Ch02.DirectionalDerivative
import PetersenLib.Riemannian.Manifold.DoCarmoCh2
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.4 (extending a curve velocity to a field)

If a smooth curve `c : ℝ → M` has nonzero speed at `t₀` (`ċ(t₀) ≠ 0`), there is a
smooth vector field `X` on `M` with `X|_{c(t)} = ċ(t)` for `t` near `t₀`
(`exercise2_5_4`).

The proof is the classical *curve rectification*.  Read the curve through a chart
`φ = extChartAt I (c t₀)` to get `γ = φ ∘ c : ℝ → E`, an immersion at `t₀`
(`deriv γ t₀ = ċ(t₀) ≠ 0`, via `mfderiv_extChartAt_self`).  Pair the velocity with a
coordinate functional `L = ⟪ċ(t₀), ·⟫`; then `h = L ∘ γ` has `h'(t₀) = ‖ċ(t₀)‖² > 0`,
so the inverse function theorem gives a smooth local inverse `σ` on an open set with
`σ(h(s)) = s` near `t₀` (`smoothLocalInverse_open`).  The Euclidean field
`V(y) = γ'(σ(L y))` is smooth on an open neighbourhood of `φ(c t₀)` and satisfies
`V(γ s) = γ'(s)` near `t₀` (`exists_vectorField_extends_velocity_euclidean`).
Pushing `V` forward through the chart (`VectorField.mpullback`) gives a smooth field
near `c t₀` whose value on the curve is `ċ`, which the germ-globaliser
`exists_smoothVectorField_eventuallyEq` upgrades to a global smooth vector field.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.4
(`rem:pet-ch2-ex-4`).
-/

open scoped ContDiff RealInnerProductSpace Topology Manifold
open Bundle Set Filter VectorField

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Smooth local inverse on an open set.**  A `C^∞` function `h : ℝ → ℝ` on an
open set `O` with `h'(t₀) ≠ 0` has a `C^∞` local inverse `σ` defined on an open set
`J ∋ h t₀`, mapping `J` back into `O`, with `σ(h s) = s` for `s` near `t₀`.  This is
the open-domain form of the inverse function theorem (mathlib's
`ContDiffAt.localInverse` only gives smoothness *at a point*, which is too weak for
the germ-globaliser used below). -/
private theorem smoothLocalInverse_open {h : ℝ → ℝ} {t₀ : ℝ} {O : Set ℝ} (hO : IsOpen O)
    (ht₀ : t₀ ∈ O) (hh : ContDiffOn ℝ ∞ h O) (hd : deriv h t₀ ≠ 0) :
    ∃ (σ : ℝ → ℝ) (J : Set ℝ), IsOpen J ∧ h t₀ ∈ J ∧ ContDiffOn ℝ ∞ σ J ∧
      Set.MapsTo σ J O ∧ (∀ᶠ s in 𝓝 t₀, σ (h s) = s) := by
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by norm_num
  have hcd : ContDiffAt ℝ ∞ h t₀ := hh.contDiffAt (hO.mem_nhds ht₀)
  have hderiv_cont : ContinuousOn (deriv h) O := hh.continuousOn_deriv_of_isOpen hO (by norm_cast)
  set G : Set ℝ := O ∩ (deriv h) ⁻¹' {y | y ≠ 0} with hGdef
  have hG_open : IsOpen G := hderiv_cont.isOpen_inter_preimage hO isOpen_ne
  have ht₀G : t₀ ∈ G := ⟨ht₀, hd⟩
  set e₀ : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv h t₀) hd) with he₀
  have hcoe₀ : (e₀ : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv h t₀) := by
    ext; simp [he₀, ContinuousLinearEquiv.unitsEquivAut_apply]
  have hfd0 : HasFDerivAt h (e₀ : ℝ →L[ℝ] ℝ) t₀ := by
    rw [hcoe₀]; exact ((hcd.differentiableAt hne).hasDerivAt).hasFDerivAt
  set pe := hcd.toOpenPartialHomeomorph h hfd0 hne with hpe
  have hcoe_pe : ⇑pe = h := ContDiffAt.toOpenPartialHomeomorph_coe hcd hfd0 hne
  have ht₀src : t₀ ∈ pe.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hcd hfd0 hne
  refine ⟨pe.symm, pe.target ∩ pe.symm ⁻¹' G, ?_, ?_, ?_, ?_, ?_⟩
  · exact pe.continuousOn_invFun.isOpen_inter_preimage pe.open_target hG_open
  · refine ⟨ContDiffAt.image_mem_toOpenPartialHomeomorph_target hcd hfd0 hne, ?_⟩
    have hsi : pe.symm (h t₀) = t₀ := ContDiffAt.localInverse_apply_image hcd hfd0 hne
    simp only [Set.mem_preimage, hsi]; exact ht₀G
  · intro a ha
    obtain ⟨ha_tgt, ha_G⟩ := ha
    have hsa_O : pe.symm a ∈ O := ha_G.1
    have hsa_ne : deriv h (pe.symm a) ≠ 0 := ha_G.2
    have hcd_a : ContDiffAt ℝ ∞ h (pe.symm a) := hh.contDiffAt (hO.mem_nhds hsa_O)
    set ea : ℝ ≃L[ℝ] ℝ :=
      ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv h (pe.symm a)) hsa_ne) with hea
    have hcoea : (ea : ℝ →L[ℝ] ℝ)
        = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv h (pe.symm a)) := by
      ext; simp [hea, ContinuousLinearEquiv.unitsEquivAut_apply]
    have hfda : HasFDerivAt h (ea : ℝ →L[ℝ] ℝ) (pe.symm a) := by
      rw [hcoea]; exact ((hcd_a.differentiableAt hne).hasDerivAt).hasFDerivAt
    exact (pe.contDiffAt_symm ha_tgt (f₀' := ea) hfda hcd_a).contDiffWithinAt
  · intro a ha; exact ha.2.1
  · filter_upwards [pe.open_source.mem_nhds ht₀src] with x hx
    rw [← hcoe_pe]; exact pe.left_inv hx

/-- **Euclidean rectification.**  A `C^∞` curve `γ : ℝ → E` on an open set `O` with
nonzero velocity at `t₀` admits a `C^∞` vector field `V` on an open neighbourhood `W`
of `γ t₀` with `V(γ s) = γ'(s)` for `s` near `t₀`. -/
private theorem exists_vectorField_extends_velocity_euclidean
    {γ : ℝ → E} {t₀ : ℝ} {O : Set ℝ} (hO : IsOpen O) (ht₀ : t₀ ∈ O)
    (hγ : ContDiffOn ℝ ∞ γ O) (hv : deriv γ t₀ ≠ 0) :
    ∃ (V : E → E) (W : Set E), IsOpen W ∧ γ t₀ ∈ W ∧ ContDiffOn ℝ ∞ V W ∧
      (∀ᶠ s in 𝓝 t₀, V (γ s) = deriv γ s) := by
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by norm_num
  set v := deriv γ t₀ with hvdef
  set L : E →L[ℝ] ℝ := innerSL ℝ v with hL
  have hO_nhds : O ∈ 𝓝 t₀ := hO.mem_nhds ht₀
  have hγ' : HasDerivAt γ v t₀ := ((hγ.contDiffAt hO_nhds).differentiableAt hne).hasDerivAt
  set h : ℝ → ℝ := fun s => L (γ s) with hh_def
  have hh_On : ContDiffOn ℝ ∞ h O := L.contDiff.comp_contDiffOn hγ
  have hh_hd : HasDerivAt h (L v) t₀ := L.hasFDerivAt.comp_hasDerivAt t₀ hγ'
  have hLv : L v = ‖v‖ ^ 2 := by simp [hL, innerSL_apply_apply]
  have hd : deriv h t₀ ≠ 0 := by rw [hh_hd.deriv, hLv]; positivity
  obtain ⟨σ, J, hJ_open, hht₀J, hσ_On, hσ_maps, hσ_left⟩ :=
    smoothLocalInverse_open hO ht₀ hh_On hd
  have hdγ_On : ContDiffOn ℝ ∞ (deriv γ) O := hγ.deriv_of_isOpen hO (by norm_cast)
  refine ⟨fun y => deriv γ (σ (L y)), L ⁻¹' J, hJ_open.preimage L.continuous, ?_, ?_, ?_⟩
  · show L (γ t₀) ∈ J; exact hht₀J
  · have hcomp1 : ContDiffOn ℝ ∞ (deriv γ ∘ σ) J := hdγ_On.comp hσ_On hσ_maps
    have hmapsL : Set.MapsTo (⇑L) (L ⁻¹' J) J := fun y hy => hy
    exact hcomp1.comp L.contDiff.contDiffOn hmapsL
  · filter_upwards [hσ_left] with s hs
    show deriv γ (σ (L (γ s))) = deriv γ s
    have hs' : σ (L (γ s)) = s := hs
    rw [hs']

/-- **Exercise 2.5.4.**  If a smooth curve `c` has nonzero speed at `t₀`, there is a
smooth vector field `X` with `X|_{c(t)} = ċ(t)` for `t` near `t₀`. -/
theorem exercise2_5_4 (c : ℝ → M) (t₀ : ℝ) (hc : ContMDiff 𝓘(ℝ) I ∞ c)
    (hspeed : mfderiv 𝓘(ℝ) I c t₀ (1 : ℝ) ≠ 0) :
    ∃ X : Π x : M, TangentSpace I x, IsSmoothVectorField X ∧
      ∀ᶠ t in 𝓝 t₀, X (c t) = mfderiv 𝓘(ℝ) I c t (1 : ℝ) := by
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by norm_num
  set p := c t₀ with hp
  have hsrc_open : IsOpen (extChartAt I p).source := isOpen_extChartAt_source (I := I) p
  have hp_src : p ∈ (extChartAt I p).source := mem_extChartAt_source (I := I) p
  have hsrc_eq : (extChartAt I p).source = (chartAt H p).source := extChartAt_source I p
  set O : Set ℝ := c ⁻¹' (extChartAt I p).source with hO_def
  have hO_open : IsOpen O := hsrc_open.preimage hc.continuous
  have ht₀O : t₀ ∈ O := by simp only [hO_def, Set.mem_preimage, ← hp]; exact hp_src
  -- `γ = φ ∘ c` is smooth on `O`.
  set γ : ℝ → E := fun t => extChartAt I p (c t) with hγ_def
  have hmaps_c : Set.MapsTo c O (chartAt H p).source := fun t ht => hsrc_eq ▸ ht
  have hγ_mOn : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ O :=
    (contMDiffOn_extChartAt (I := I) (x := p)).comp hc.contMDiffOn hmaps_c
  have hγ_On : ContDiffOn ℝ ∞ γ O := hγ_mOn.contDiffOn
  -- Speed bridge: `deriv γ t₀ = ċ(t₀)`.
  have hφs : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I p) p := contMDiffAt_extChartAt (I := I) (x := p)
  have hspeed_bridge : deriv γ t₀ = (mfderiv 𝓘(ℝ) I c t₀ (1 : ℝ) : E) := by
    have hmf : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t₀
        = (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p).comp (mfderiv 𝓘(ℝ) I c t₀) :=
      mfderiv_comp t₀ (hφs.mdifferentiableAt hne) (hc.contMDiffAt.mdifferentiableAt hne)
    rw [mfderiv_extChartAt_self] at hmf
    have hd : deriv γ t₀ = mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t₀ (1 : ℝ) := by rw [mfderiv_eq_fderiv]; rfl
    rw [hd, hmf]; rfl
  have hv : deriv γ t₀ ≠ 0 := by rw [hspeed_bridge]; exact hspeed
  obtain ⟨V, W, hW_open, hγt₀W, hV_On, hV_val⟩ :=
    exists_vectorField_extends_velocity_euclidean hO_open ht₀O hγ_On hv
  -- Push `V` forward through the chart.
  set σM : Π x : M, TangentSpace I x := mpullback I 𝓘(ℝ, E) (extChartAt I p) V with hσM_def
  set U : Set M := (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' W with hU_def
  have hU_open : IsOpen U :=
    (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage hsrc_open hW_open
  have hpU : p ∈ U := ⟨hp_src, by simp only [Set.mem_preimage]; exact hγt₀W⟩
  -- Smoothness of the pushed-forward field on `U`.
  have hσM_smoothOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun q => (⟨q, σM q⟩ : TangentBundle I M)) U := by
    intro q hq
    obtain ⟨hq_src, hq_W⟩ := hq
    have hVq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) E)) (extChartAt I p q) :=
      contMDiffAt_vectorSpace_iff_contDiffAt.mpr (hV_On.contDiffAt (hW_open.mem_nhds hq_W))
    have hfq : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I p) q :=
      contMDiffAt_extChartAt' (I := I) (hsrc_eq ▸ hq_src)
    have hf'q : (mfderiv I 𝓘(ℝ, E) (extChartAt I p) q).IsInvertible :=
      isInvertible_mfderiv_extChartAt hq_src
    exact (ContMDiffAt.mpullback_vectorField_preimage hVq hfq hf'q (by simp)).contMDiffWithinAt
  -- Globalise to a genuine smooth vector field agreeing with `σM` near `p`.
  obtain ⟨Z, hZ_ev⟩ := exists_smoothVectorField_eventuallyEq hU_open hσM_smoothOn hpU
  -- Value of `σM` along the curve equals the velocity `ċ`.
  have hσM_curve : ∀ᶠ t in 𝓝 t₀, σM (c t) = mfderiv 𝓘(ℝ) I c t (1 : ℝ) := by
    have hct : ∀ᶠ t in 𝓝 t₀, c t ∈ (extChartAt I p).source := hO_open.mem_nhds ht₀O
    filter_upwards [hct, hV_val] with t hct_t hV_t
    have hchain : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t
        = (mfderiv I 𝓘(ℝ, E) (extChartAt I p) (c t)).comp (mfderiv 𝓘(ℝ) I c t) :=
      mfderiv_comp t (mdifferentiableAt_extChartAt (hsrc_eq ▸ hct_t))
        (hc.contMDiffAt.mdifferentiableAt hne)
    have hderivγ : deriv γ t
        = mfderiv I 𝓘(ℝ, E) (extChartAt I p) (c t) (mfderiv 𝓘(ℝ) I c t (1 : ℝ)) := by
      have hd : deriv γ t = mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) := by rw [mfderiv_eq_fderiv]; rfl
      rw [hd, hchain]; rfl
    have hVval : V (extChartAt I p (c t)) = deriv γ t := hV_t
    have hinv := (isInvertible_mfderiv_extChartAt hct_t).inverse_apply_self
      (mfderiv 𝓘(ℝ) I c t (1 : ℝ))
    rw [hσM_def, mpullback_apply, hVval, hderivγ, hinv]
  -- Combine.
  refine ⟨⇑Z, Z.smooth, ?_⟩
  have hZ_curve : ∀ᶠ t in 𝓝 t₀, (⇑Z) (c t) = σM (c t) :=
    (hc.continuous.continuousAt (x := t₀)).tendsto.eventually hZ_ev
  filter_upwards [hZ_curve, hσM_curve] with t hZ_t hσ_t
  rw [hZ_t, hσ_t]

end PetersenLib
