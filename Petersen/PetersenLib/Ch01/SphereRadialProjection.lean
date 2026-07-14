import PetersenLib.Ch01.Sphere
import PetersenLib.Ch01.SphereCodRestrictLocal

/-!
# The radial projection onto the unit sphere

The map `y ↦ ‖y‖⁻¹ • y`, as a sphere-valued map `unitSphereProj` (junk value
at `0`). Away from the origin it is smooth, and its differential is computed
on the radial/tangential decomposition:

* `fderiv_inv_norm_smul_orthogonal`: on vectors `u ⊥ x` the ambient
  differential is `u ↦ ‖x‖⁻¹ • u`;
* `fderiv_inv_norm_smul_self`: the radial direction is killed.

Both are obtained from one-dimensional directional derivatives along lines
(`HasDerivAt` computations), avoiding any global derivative formula.

This is the ambient half of the "quotient map `𝔽ⁿ⁺¹ − {0} → 𝔽Pⁿ`" analysis
of Petersen Exercise 1.6.15: the projection `ℂ² − {0} → S³` composed with
the Hopf fibration realizes the projective quotient map.
-/

open Metric Module
open scoped Classical ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Eng.** The radial projection `y ↦ ‖y‖⁻¹ • y` onto the unit sphere, as
a globally defined sphere-valued map (junk value at `0`). -/
noncomputable def unitSphereProj [Nontrivial E] (y : E) : sphere (0 : E) 1 :=
  if hy : y = 0 then
    ⟨(NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).mpr zero_le_one |>.some,
      (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).mpr zero_le_one |>.some_mem⟩
  else
    ⟨‖y‖⁻¹ • y, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]⟩

@[simp]
theorem coe_unitSphereProj [Nontrivial E] {y : E} (hy : y ≠ 0) :
    (unitSphereProj y : E) = ‖y‖⁻¹ • y := by
  rw [unitSphereProj, dif_neg hy]

/-- **Eng.** The radial projection formula is smooth away from the origin. -/
theorem contDiffAt_inv_norm_smul {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : E => ‖y‖⁻¹ • y) x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

/-- **Math.** Directional derivative of the radial projection along a
tangential line: for `u ⊥ x`, `‖x + tu‖ = √(‖x‖² + t²‖u‖²)` has vanishing
derivative at `t = 0`, so only the linear term survives:
`d/dt|₀ (‖x + tu‖⁻¹ (x + tu)) = ‖x‖⁻¹ u`. -/
theorem hasDerivAt_inv_norm_smul_line_orthogonal {x u : E} (hx : x ≠ 0)
    (hxu : ⟪x, u⟫ = 0) :
    HasDerivAt (fun t : ℝ => ‖x + t • u‖⁻¹ • (x + t • u)) (‖x‖⁻¹ • u) 0 := by
  have hnorm : ∀ t : ℝ, ‖x + t • u‖ = Real.sqrt (‖x‖ ^ 2 + t ^ 2 * ‖u‖ ^ 2) := by
    intro t
    rw [← Real.sqrt_sq (norm_nonneg (x + t • u))]
    congr 1
    rw [← real_inner_self_eq_norm_sq, real_inner_add_add_self,
      real_inner_smul_right, hxu, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hpoly : HasDerivAt (fun t : ℝ => ‖x‖ ^ 2 + t ^ 2 * ‖u‖ ^ 2) 0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (‖u‖ ^ 2)).const_add (‖x‖ ^ 2)
  have hval : ‖x‖ ^ 2 + (0 : ℝ) ^ 2 * ‖u‖ ^ 2 = ‖x‖ ^ 2 := by ring
  have hpos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (‖x‖ ^ 2 + t ^ 2 * ‖u‖ ^ 2)) 0 0 := by
    have h := (Real.hasDerivAt_sqrt (by rw [hval]; exact hpos.ne')).comp 0 hpoly
    simpa using h
  have hinv : HasDerivAt (fun t : ℝ => (Real.sqrt (‖x‖ ^ 2 + t ^ 2 * ‖u‖ ^ 2))⁻¹) 0 0 := by
    have h0 : Real.sqrt (‖x‖ ^ 2 + (0 : ℝ) ^ 2 * ‖u‖ ^ 2) ≠ 0 := by
      rw [hval]
      exact Real.sqrt_ne_zero'.mpr hpos
    simpa using hsqrt.inv h0
  have hline : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
  have hfun : (fun t : ℝ => ‖x + t • u‖⁻¹ • (x + t • u))
      = fun t => (Real.sqrt (‖x‖ ^ 2 + t ^ 2 * ‖u‖ ^ 2))⁻¹ • (x + t • u) := by
    funext t
    rw [hnorm t]
  rw [hfun]
  have h00 : Real.sqrt (‖x‖ ^ 2 + (0 : ℝ) ^ 2 * ‖u‖ ^ 2) = ‖x‖ := by
    rw [hval]
    exact Real.sqrt_sq (norm_nonneg x)
  have h := hinv.smul hline
  convert h using 1
  rw [h00]
  simp

/-- **Math.** The radial projection is constant along rays: its directional
derivative in the radial direction vanishes. -/
theorem hasDerivAt_inv_norm_smul_line_radial (x : E) :
    HasDerivAt (fun t : ℝ => ‖x + t • x‖⁻¹ • (x + t • x)) 0 0 := by
  have hev : (fun t : ℝ => ‖x + t • x‖⁻¹ • (x + t • x))
      =ᶠ[𝓝 (0 : ℝ)] fun _ => ‖x‖⁻¹ • x := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0)] with t ht
    have h1t : (0 : ℝ) < 1 + t := by
      have : (-1 : ℝ) < t := ht
      linarith
    have hxt : x + t • x = (1 + t) • x := by
      rw [add_smul, one_smul]
    rw [hxt, norm_smul, Real.norm_eq_abs, abs_of_pos h1t, mul_inv, smul_smul,
      mul_assoc, mul_comm ‖x‖⁻¹ (1 + t), ← mul_assoc,
      inv_mul_cancel₀ h1t.ne', one_mul]
  exact (hasDerivAt_const (0 : ℝ) (‖x‖⁻¹ • x)).congr_of_eventuallyEq hev

/-- **Math.** The ambient differential of the radial projection on
tangential vectors: `D(‖·‖⁻¹ ·)_x(u) = ‖x‖⁻¹ u` for `u ⊥ x`. -/
theorem fderiv_inv_norm_smul_orthogonal {x u : E} (hx : x ≠ 0)
    (hxu : ⟪x, u⟫ = 0) :
    fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x u = ‖x‖⁻¹ • u := by
  have hdiff : DifferentiableAt ℝ (fun y : E => ‖y‖⁻¹ • y) x :=
    (contDiffAt_inv_norm_smul hx).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
  have hF : HasFDerivAt (fun y : E => ‖y‖⁻¹ • y)
      (fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x) (x + (0 : ℝ) • u) := by
    rw [zero_smul, add_zero]
    exact hdiff.hasFDerivAt
  have hcomp := hF.comp_hasDerivAt 0 hline
  have hfun : ((fun y : E => ‖y‖⁻¹ • y) ∘ fun t : ℝ => x + t • u)
      = fun t : ℝ => ‖x + t • u‖⁻¹ • (x + t • u) := rfl
  rw [hfun] at hcomp
  exact hcomp.unique (hasDerivAt_inv_norm_smul_line_orthogonal hx hxu)

/-- **Math.** The ambient differential of the radial projection kills the
radial direction. -/
theorem fderiv_inv_norm_smul_self {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x x = 0 := by
  have hdiff : DifferentiableAt ℝ (fun y : E => ‖y‖⁻¹ • y) x :=
    (contDiffAt_inv_norm_smul hx).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => x + t • x) x 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const x).const_add x
  have hF : HasFDerivAt (fun y : E => ‖y‖⁻¹ • y)
      (fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x) (x + (0 : ℝ) • x) := by
    rw [zero_smul, add_zero]
    exact hdiff.hasFDerivAt
  have hcomp := hF.comp_hasDerivAt 0 hline
  have hfun : ((fun y : E => ‖y‖⁻¹ • y) ∘ fun t : ℝ => x + t • x)
      = fun t : ℝ => ‖x + t • x‖⁻¹ • (x + t • x) := rfl
  rw [hfun] at hcomp
  exact hcomp.unique (hasDerivAt_inv_norm_smul_line_radial x)

/-! ## Manifold-level differential of the radial projection -/

section Manifold

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [Nontrivial E]

/-- **Math.** The radial projection is smooth away from the origin, as a map
into the unit sphere. -/
theorem contMDiffAt_unitSphereProj {x : E} (hx : x ≠ 0) :
    ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ (unitSphereProj (E := E)) x := by
  rw [contMDiffAt_sphere_iff_ambient]
  have hev : (fun y : E => ‖y‖⁻¹ • y) =ᶠ[𝓝 x]
      fun y => (unitSphereProj y : E) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact (coe_unitSphereProj hy).symm
  exact (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_inv_norm_smul hx)).congr_of_eventuallyEq
    hev.symm

/-- **Eng.** The chain-rule bridge for the radial projection: composing the
intrinsic differential of `unitSphereProj` with the sphere inclusion gives
the ambient differential of `y ↦ ‖y‖⁻¹ • y`. -/
theorem mfderiv_coe_unitSphereProj_apply {x : E} (hx : x ≠ 0) (u : E) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (unitSphereProj x)
      (mfderiv 𝓘(ℝ, E) (𝓡 n) unitSphereProj x u)
    = fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x u := by
  have hS : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) unitSphereProj x :=
    (contMDiffAt_unitSphereProj hx).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E)
      (unitSphereProj x) :=
    (contMDiff_coe_sphere (m := ∞) (unitSphereProj x)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp x hι hS
  have hev : (((↑) : sphere (0 : E) 1 → E) ∘ unitSphereProj)
      =ᶠ[𝓝 x] fun y : E => ‖y‖⁻¹ • y := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact coe_unitSphereProj hy
  have h1 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (((↑) : sphere (0 : E) 1 → E) ∘ unitSphereProj) x
      = fderiv ℝ (fun y : E => ‖y‖⁻¹ • y) x := by
    rw [hev.mfderiv_eq, mfderiv_eq_fderiv]
  rw [← h1, hcomp]
  rfl

/-- **Math.** The intrinsic differential of the radial projection kills the
radial direction. -/
theorem mfderiv_unitSphereProj_self {x : E} (hx : x ≠ 0) :
    mfderiv 𝓘(ℝ, E) (𝓡 n) unitSphereProj x x = 0 := by
  apply mfderiv_coe_sphere_injective
  rw [mfderiv_coe_unitSphereProj_apply hx x, fderiv_inv_norm_smul_self hx, map_zero]
  rfl

/-- **Math.** The radial projection is a submersion away from the origin:
the scaled inclusion `p ↦ ‖x‖ • p` is a smooth right inverse through `x`,
so the differential of `unitSphereProj` is surjective. -/
theorem mfderiv_unitSphereProj_surjective {x : E} (hx : x ≠ 0) :
    Function.Surjective (mfderiv 𝓘(ℝ, E) (𝓡 n) unitSphereProj x) := by
  set A : sphere (0 : E) 1 → E := fun p => ‖x‖ • (p : E) with hA
  have hAsm : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ A :=
    (contDiff_const_smul ‖x‖).contMDiff.comp contMDiff_coe_sphere
  have hAx : A (unitSphereProj x) = x := by
    rw [hA]
    show ‖x‖ • (unitSphereProj x : E) = x
    rw [coe_unitSphereProj hx, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),
      one_smul]
  have hid : unitSphereProj (E := E) ∘ A = id := by
    funext p
    have hnp : ‖(p : E)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
    have hAp : A p ≠ 0 := by
      rw [hA]
      simp only [ne_eq, smul_eq_zero, norm_eq_zero, not_or]
      exact ⟨hx, fun h0 => by simp [h0] at hnp⟩
    refine Subtype.ext ?_
    show (unitSphereProj (A p) : E) = (p : E)
    rw [coe_unitSphereProj hAp, hA]
    show ‖‖x‖ • (p : E)‖⁻¹ • ‖x‖ • (p : E) = (p : E)
    rw [norm_smul, norm_norm, hnp, mul_one, smul_smul,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  intro t
  have hSd : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) unitSphereProj (A (unitSphereProj x)) := by
    rw [hAx]
    exact (contMDiffAt_unitSphereProj hx).mdifferentiableAt (by simp)
  have hAd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) A (unitSphereProj x) :=
    (hAsm (unitSphereProj x)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (I' := 𝓘(ℝ, E)) (unitSphereProj x) hSd hAd
  rw [hid] at hcomp
  have hmid : mfderiv (𝓡 n) (𝓡 n) (id : sphere (0 : E) 1 → sphere (0 : E) 1)
      (unitSphereProj x) = ContinuousLinearMap.id ℝ _ := mfderiv_id
  refine ⟨mfderiv (𝓡 n) 𝓘(ℝ, E) A (unitSphereProj x) t, ?_⟩
  have := DFunLike.congr_fun hcomp t
  rw [hmid] at this
  simp only [id_eq] at this
  rw [hAx] at this
  exact this.symm

end Manifold

end PetersenLib
