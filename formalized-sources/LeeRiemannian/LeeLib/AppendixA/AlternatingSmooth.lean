import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of pullback of alternating maps along a continuous linear map

Mathlib knows that `f ↦ (ω ↦ ω.compContinuousLinearMap f)` is continuous
(`ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM`), but not that it is smooth.
Smoothness is what a bundle of alternating maps needs for its coordinate changes, so we prove it
here.

The map is homogeneous of degree `card ι` in `f`, so it is *not* linear and the usual
`IsBoundedBilinearMap.contDiff` route does not apply. Instead we exhibit it as the restriction to
the diagonal of the continuous multilinear map
`ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`, which is smooth by
`ContinuousMultilinearMap.contDiff`. That multilinear map takes values in *multilinear* maps rather
than alternating ones, so we return to alternating maps along `alternatizeCLM`, a continuous-linear
packaging of `ContinuousMultilinearMap.alternatization`. On the diagonal alternatization is
multiplication by `(card ι)!` (`alternatizeCLM_toContinuousMultilinearMap`), which is where the
characteristic-zero hypothesis enters.

## Main results

* `ContinuousMultilinearMap.alternatizeCLM`: alternatization as a continuous linear map.
* `ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM`: the pullback of alternating maps
  along a continuous linear map is `C^n` in that linear map.
-/

open scoped Nat

namespace ContinuousMultilinearMap

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Alternatization of a continuous multilinear map, as a linear map. This is
`ContinuousMultilinearMap.alternatization` (an `AddMonoidHom`) upgraded with its scalar action. -/
noncomputable def alternatizeₗ :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N →ₗ[𝕜] (M [⋀^ι]→L[𝕜] N) where
  toFun := alternatization
  map_add' f g := by simp
  map_smul' c f := by
    ext v
    simp only [alternatization_apply_apply, RingHom.id_apply, ContinuousAlternatingMap.smul_apply,
      ContinuousMultilinearMap.smul_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => smul_comm _ _ _

@[simp]
theorem alternatizeₗ_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N) :
    alternatizeₗ 𝕜 f = alternatization f := rfl

theorem norm_alternatization_le (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N) :
    ‖alternatization f‖ ≤ (Fintype.card ι)! * ‖f‖ := by
  have h : ‖(alternatization f).toContinuousMultilinearMap‖ ≤ (Fintype.card ι)! * ‖f‖ := by
    have : (alternatization f).toContinuousMultilinearMap
        = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.domDomCongr σ := rfl
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ σ : Equiv.Perm ι, ‖(Equiv.Perm.sign σ : ℤ) • f.domDomCongr σ‖ ≤ ‖f‖ := by
      intro σ
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        simp [h, norm_domDomCongr]
    calc ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • f.domDomCongr σ‖
        ≤ ∑ _σ : Equiv.Perm ι, ‖f‖ := Finset.sum_le_sum fun σ _ => hb σ
      _ = (Fintype.card (Equiv.Perm ι)) * ‖f‖ := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = (Fintype.card ι)! * ‖f‖ := by rw [Fintype.card_perm]
  simpa using h

/-- Alternatization of a continuous multilinear map, as a continuous linear map. -/
noncomputable def alternatizeCLM :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N →L[𝕜] (M [⋀^ι]→L[𝕜] N) :=
  LinearMap.mkContinuous (alternatizeₗ 𝕜) ((Fintype.card ι)! : ℝ)
    fun f => norm_alternatization_le 𝕜 f

@[simp]
theorem alternatizeCLM_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => M) N) :
    alternatizeCLM 𝕜 f = alternatization f := rfl

/-- Alternatizing a map that is already alternating multiplies it by `(card ι)!`. This is the
continuous counterpart of `AlternatingMap.coe_alternatization`. -/
theorem alternatizeCLM_toContinuousMultilinearMap (ω : M [⋀^ι]→L[𝕜] N) :
    alternatizeCLM 𝕜 ω.toContinuousMultilinearMap = ((Fintype.card ι)! : ℕ) • ω := by
  refine ContinuousAlternatingMap.toAlternatingMap_injective ?_
  rw [alternatizeCLM_apply, alternatization_apply_toAlternatingMap]
  exact ω.toAlternatingMap.coe_alternatization

end ContinuousMultilinearMap

namespace ContinuousAlternatingMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pullback of alternating maps along a continuous linear map, factored through
multilinear maps: restrict along the inclusion of alternating maps into multilinear maps, pull back
there, then alternatize. This equals `(card ι)! • compContinuousLinearMapCLM f`, see
`alternatizedCompCLM_eq`.

We deliberately keep this as a composite of maps between spaces of *bounded* maps rather than
bundling it as a continuous linear map on an operator space: operator norms do not chain when the
domain is itself an operator space, and `ContDiff.clm_comp` handles the composite directly. -/
noncomputable def alternatizedCompCLM (f : E →L[𝕜] F) :
    (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G) :=
  (ContinuousMultilinearMap.alternatizeCLM 𝕜).comp
    ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
        (fun _ : ι => E) (fun _ : ι => F) G fun _ => f).comp
      (toContinuousMultilinearMapCLM (E := F) (F := G) (ι := ι) 𝕜))

theorem alternatizedCompCLM_eq (f : E →L[𝕜] F) :
    alternatizedCompCLM (ι := ι) (G := G) f
      = ((Fintype.card ι)! : ℕ) • compContinuousLinearMapCLM f := by
  ext ω
  have hco : (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
      (fun _ : ι => E) (fun _ : ι => F) G fun _ => f)
        (toContinuousMultilinearMapCLM (E := F) (F := G) (ι := ι) 𝕜 ω)
      = (ω.compContinuousLinearMap f).toContinuousMultilinearMap := rfl
  have hval : alternatizedCompCLM (ι := ι) (G := G) f ω
      = ((Fintype.card ι)! : ℕ) • ω.compContinuousLinearMap f := by
    show ContinuousMultilinearMap.alternatizeCLM 𝕜
        ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
          (fun _ : ι => E) (fun _ : ι => F) G fun _ => f)
            (toContinuousMultilinearMapCLM (E := F) (F := G) (ι := ι) 𝕜 ω)) = _
    rw [hco, ContinuousMultilinearMap.alternatizeCLM_toContinuousMultilinearMap]
  rw [hval, ContinuousLinearMap.smul_apply, compContinuousLinearMapCLM_apply]

theorem contDiff_alternatizedCompCLM {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (fun f : E →L[𝕜] F => alternatizedCompCLM (ι := ι) (G := G) f) := by
  have hdiag : ContDiff 𝕜 n (fun f : E →L[𝕜] F => (fun _ : ι => f)) :=
    (ContinuousLinearMap.pi fun _ : ι => ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).contDiff
  have hmul : ContDiff 𝕜 n (fun f : E →L[𝕜] F =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
        (fun _ : ι => E) (fun _ : ι => F) G fun _ => f)) :=
    (ContinuousMultilinearMap.contDiff _).comp hdiag
  exact contDiff_const.clm_comp (hmul.clm_comp contDiff_const)

/-- The pullback of alternating maps along a continuous linear map is smooth in that linear map.

Mathlib has only the continuity of this map
(`ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM`); smoothness is what a bundle of
alternating maps needs for its coordinate changes.

The map is homogeneous of degree `card ι` in `f`, so it is not linear; we obtain smoothness by
writing it as `(card ι)!⁻¹` times the restriction to the diagonal of a continuous multilinear map. -/
theorem contDiff_compContinuousLinearMapCLM [CharZero 𝕜] {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (fun f : E →L[𝕜] F =>
      (compContinuousLinearMapCLM f : (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G))) := by
  have hfac : ((Fintype.card ι)! : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hrw : (fun f : E →L[𝕜] F =>
      (compContinuousLinearMapCLM f : (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)))
      = fun f => (((Fintype.card ι)! : 𝕜)⁻¹) • alternatizedCompCLM (ι := ι) (G := G) f := by
    funext f
    rw [alternatizedCompCLM_eq, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ hfac,
      one_smul]
  rw [hrw]
  exact contDiff_alternatizedCompCLM.const_smul _

end ContinuousAlternatingMap
