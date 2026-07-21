import PetersenLib.Ch01.HopfCoordinates
import PetersenLib.Ch01.WithLpProduct

/-!
# Petersen Example 1.4.10 — the Hopf fibration in doubly-warped coordinates

`HopfCoordinates.lean` builds the two coordinate parametrizations of Example 1.4.10

* `Φ(t, e^{iθ₁}, e^{iθ₂}) = (sin(t)·e^{iθ₁}, cos(t)·e^{iθ₂}) ∈ S³(1) ⊆ ℂ²`,
* `Ψ(r, e^{iθ}) = (½cos(2r), ½sin(2r)·e^{iθ}) ∈ S²(1/2) ⊆ ℝ ⊕ ℂ`,

and proves that Wilhelm's Hopf map, read through them, is Petersen's
`(t, e^{iθ₁}, e^{iθ₂}) ↦ (t, e^{i(θ₁−θ₂)})` (`hopfMap_sphereThreeParam`).  What was missing was the
*metric* half of the example: that in these coordinates the two round metrics really are

* `ds²_{S³(1)} = dt² + sin²(t) dθ₁² + cos²(t) dθ₂²`  (`pullbackForm_sphereThreeParam`),
* `ds²_{S²(1/2)} = dr² + ¼sin²(2r) dθ²`              (`pullbackForm_sphereTwoParam`).

The obstruction was a *type*, not a computation.  `sphereAsDoublyWarpedProduct` (`SpaceForms.lean`)
already contains the whole analytic content of the first identity, but it computes the pullback into
the **plain product** `E₁ × E₂` with `productMetric`, whereas an ambient sphere forces the
**`ℓ²`-product** `WithLp 2 (E₁ × E₂)`.  `WithLpProduct.lean` bridges the two models; here that bridge
is used to transport `sphereAsDoublyWarpedProduct` to the `ℓ²`-model once and for all
(`sphereAsDoublyWarpedProductWithLp`, stated for arbitrary factors `E₁, E₂` so that it also serves
the higher-dimensional `S^{2n+3}` decomposition of Example 1.4.14), and the `S²(1/2)` identity is
computed directly.

`hopfFibrationRevisited` then assembles Example 1.4.10 in full.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Example 1.4.10.
-/

open Metric Module ComplexConjugate
open scoped ContDiff Manifold Topology RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace PetersenLib

/-! ## The doubly warped sphere in the `ℓ²`-model -/

section SphereDoublyWarpedWithLp

variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {n₁ n₂ : ℕ} [Fact (finrank ℝ E₁ = n₁ + 1)] [Fact (finrank ℝ E₂ = n₂ + 1)]

/-- **Eng.** The first warped component `q ↦ sin(t)·x` of the doubly warped sphere map is
smooth. -/
theorem mdifferentiableAt_sinSmul (p : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1) :
    MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₁)
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => Real.sin q.1 • (q.2.1 : E₁)) p := by
  have hfstM : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 → ℝ) p :=
    (contMDiffAt_fst : ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, ℝ) ∞
      Prod.fst p).mdifferentiableAt (by simp)
  have h21C : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) (𝓡 n₁) ∞
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => q.2.1) :=
    (contMDiff_fst (I := 𝓡 n₁) (J := 𝓡 n₂)).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓡 n₁).prod (𝓡 n₂)))
  have hι₁M : MDifferentiableAt (𝓡 n₁) 𝓘(ℝ, E₁)
      ((↑) : sphere (0 : E₁) 1 → E₁) p.2.1 :=
    (contMDiff_coe_sphere (m := 1) p.2.1).mdifferentiableAt one_ne_zero
  have hw1M : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₁)
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.1 : E₁)) p :=
    hι₁M.comp p ((h21C p).mdifferentiableAt (by simp))
  exact ((Real.hasDerivAt_sin p.1).differentiableAt.comp_mdifferentiableAt hfstM).smul hw1M

/-- **Eng.** The second warped component `q ↦ cos(t)·y` of the doubly warped sphere map is
smooth. -/
theorem mdifferentiableAt_cosSmul (p : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1) :
    MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₂)
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => Real.cos q.1 • (q.2.2 : E₂)) p := by
  have hfstM : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 → ℝ) p :=
    (contMDiffAt_fst : ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, ℝ) ∞
      Prod.fst p).mdifferentiableAt (by simp)
  have h22C : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) (𝓡 n₂) ∞
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => q.2.2) :=
    (contMDiff_snd (I := 𝓡 n₁) (J := 𝓡 n₂)).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓡 n₁).prod (𝓡 n₂)))
  have hι₂M : MDifferentiableAt (𝓡 n₂) 𝓘(ℝ, E₂)
      ((↑) : sphere (0 : E₂) 1 → E₂) p.2.2 :=
    (contMDiff_coe_sphere (m := 1) p.2.2).mdifferentiableAt one_ne_zero
  have hw2M : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₂)
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.2 : E₂)) p :=
    hι₂M.comp p ((h22C p).mdifferentiableAt (by simp))
  exact ((Real.hasDerivAt_cos p.1).differentiableAt.comp_mdifferentiableAt hfstM).smul hw2M

/-- **Math.** Petersen Example 1.4.9, in the `ℓ²`-model: the map
`(t, x, y) ↦ (sin(t)·x, cos(t)·y) : ℝ × Sᵖ × S^q → ℝ^{p+1} ⊕₂ ℝ^{q+1}` pulls the ambient
inner product back to the doubly warped product metric `dt² + sin²(t) ds²_p + cos²(t) ds²_q`.

This is `sphereAsDoublyWarpedProduct` transported from the plain-product model to the `ℓ²`-model
along `pullbackForm_toLp_prodMk_eq_productMetric`: the two pullbacks are *equal*, because both
compute as `⟪Df₁ u, Df₁ v⟫ + ⟪Df₂ u, Df₂ v⟫` on the components.  Since the image of this map is
exactly the ambient unit sphere (`doublyWarpedSphereMap_mem_sphere`), it is the statement that the
round sphere `S^{p+q+1}(1)` *is* the doubly warped product, in the type where the sphere lives. -/
theorem sphereAsDoublyWarpedProductWithLp
    (p : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) p) :
    pullbackForm (I := 𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂)))
        (innerProductSpaceMetric (WithLp 2 (E₁ × E₂)))
        (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
          (WithLp.toLp 2 (Real.sin q.1 • (q.2.1 : E₁), Real.cos q.1 • (q.2.2 : E₂))
            : WithLp 2 (E₁ × E₂))) p u v
      = doublyWarpedProductForm (sphereMetricUnit E₁) (sphereMetricUnit E₂)
          Real.sin Real.cos p u v := by
  rw [pullbackForm_toLp_prodMk_eq_productMetric (mdifferentiableAt_sinSmul p)
    (mdifferentiableAt_cosSmul p) u v]
  exact sphereAsDoublyWarpedProduct p u v

end SphereDoublyWarpedWithLp

/-! ## `ds²_{S³(1)} = dt² + sin²(t) dθ₁² + cos²(t) dθ₂²` -/

/-- **Math.** Petersen Example 1.4.10, first coordinate representation: the parametrization
`Φ(t, e^{iθ₁}, e^{iθ₂}) = (sin(t)·e^{iθ₁}, cos(t)·e^{iθ₂})` pulls the round metric of `S³(1)` back
to the doubly warped product metric

  `dt² + sin²(t) dθ₁² + cos²(t) dθ₂²`

on `ℝ × S¹ × S¹` — the `n₁ = n₂ = 1`, `E₁ = E₂ = ℂ` case of `sphereAsDoublyWarpedProductWithLp`,
after replacing the round metric of the ambient sphere by the ambient inner product it is pulled
back from. -/
theorem pullbackForm_sphereThreeParam (p : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1))
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 1).prod (𝓡 1))) p) :
    pullbackForm (I := 𝓘(ℝ, ℝ).prod ((𝓡 1).prod (𝓡 1)))
        (sphereMetricUnit (n := 3) (WithLp 2 (ℂ × ℂ))) sphereThreeParam p u v
      = doublyWarpedProductForm (sphereMetricUnit ℂ) (sphereMetricUnit ℂ)
          Real.sin Real.cos p u v := by
  have hΦ : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓡 3) sphereThreeParam p :=
    (contMDiff_sphereThreeParam p).mdifferentiableAt (by simp)
  rw [pullbackForm_sphereMetricUnit_eq_pullbackForm_ambient hΦ u v]
  exact sphereAsDoublyWarpedProductWithLp (E₁ := ℂ) (E₂ := ℂ) p u v

/-! ## `ds²_{S²(1/2)} = dr² + ¼sin²(2r) dθ²` -/

section SphereWarpedWithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- **Math.** The rotationally symmetric parametrization of the sphere of radius `1/2` in
`ℝ ⊕₂ E`, `Ψ(r, e) = (½cos(2r), ½sin(2r)·e)`, pulls the ambient inner product back to the warped
product metric

  `dr² + ¼sin²(2r) ds²_{Sⁿ}`

on `ℝ × Sⁿ`.  (Petersen Example 1.4.10 is the case `E = ℂ`, `n = 1`, giving `S²(1/2)`.)

The computation: `DΨ(u) = (−sin(2r)·u₁, cos(2r)·u₁·e + ½sin(2r)·Dι(u₂))`, so

  `⟪DΨ(u), DΨ(v)⟫ = sin²(2r) u₁v₁ + cos²(2r) u₁v₁⟪e,e⟫ + ¼sin²(2r) ⟪Dι(u₂), Dι(v₂)⟫`,

the two cross terms vanishing because tangent vectors of the unit sphere are orthogonal to the base
point (`inner_coe_mfderiv_coe_unitSphere`).  With `⟪e,e⟫ = 1` the first two terms collapse to `u₁v₁`
by `sin² + cos² = 1`, leaving exactly `dr² + (½sin(2r))² ds²_{Sⁿ}`.

Stated over a general factor `E` rather than directly at `ℂ`: at `ℂ` the real-scalar `smul` and
`inner` instances form a diamond and the `real_inner_smul_left/right` simp set does not fire. -/
theorem sphereAsWarpedProductWithLp (p : ℝ × sphere (0 : E) 1)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p) :
    pullbackForm (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) (innerProductSpaceMetric (WithLp 2 (ℝ × E)))
        (fun q : ℝ × sphere (0 : E) 1 =>
          (WithLp.toLp 2 (Real.cos (2 * q.1) / 2, (Real.sin (2 * q.1) / 2) • (q.2 : E))
            : WithLp 2 (ℝ × E))) p u v
      = warpedProductForm (sphereMetricUnit E) (fun _ => 1)
          (fun r => Real.sin (2 * r) / 2) p u v := by
  -- smoothness of the pieces
  have hfstM : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × sphere (0 : E) 1 → ℝ) p :=
    (contMDiffAt_fst : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ Prod.fst p).mdifferentiableAt
      (by simp)
  have hsndM : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n)
      (Prod.snd : ℝ × sphere (0 : E) 1 → sphere (0 : E) 1) p :=
    (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Prod.snd p).mdifferentiableAt
      (by simp)
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 :=
    (contMDiff_coe_sphere (m := 1) p.2).mdifferentiableAt one_ne_zero
  have heM : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
      (fun q : ℝ × sphere (0 : E) 1 => (q.2 : E)) p := hι.comp p hsndM
  -- derivatives of `r ↦ ½cos(2r)` and `r ↦ ½sin(2r)`
  have hcos : HasDerivAt (fun r : ℝ => Real.cos (2 * r) / 2) (-Real.sin (2 * p.1)) p.1 := by
    have h := ((Real.hasDerivAt_cos (2 * p.1)).comp p.1
      ((hasDerivAt_id p.1).const_mul 2)).div_const 2
    convert h using 1
    ring
  have hsin : HasDerivAt (fun r : ℝ => Real.sin (2 * r) / 2) (Real.cos (2 * p.1)) p.1 := by
    have h := ((Real.hasDerivAt_sin (2 * p.1)).comp p.1
      ((hasDerivAt_id p.1).const_mul 2)).div_const 2
    convert h using 1
    ring
  have h₁ : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
      (fun q : ℝ × sphere (0 : E) 1 => Real.cos (2 * q.1) / 2) p :=
    hcos.differentiableAt.comp_mdifferentiableAt hfstM
  have h₂ : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
      (fun q : ℝ × sphere (0 : E) 1 => (Real.sin (2 * q.1) / 2) • (q.2 : E)) p :=
    (hsin.differentiableAt.comp_mdifferentiableAt hfstM).smul heM
  -- the two component differentials
  have hfstD : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × sphere (0 : E) 1 → ℝ) p w = w.1 :=
    fun w => by rw [mfderiv_fst]; rfl
  have hsndD : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n)
        (Prod.snd : ℝ × sphere (0 : E) 1 → sphere (0 : E) 1) p w = w.2 :=
    fun w => by rw [mfderiv_snd]; rfl
  have heD : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
          (fun q : ℝ × sphere (0 : E) 1 => (q.2 : E)) p w
        = mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 w.2 := by
    intro w
    have hcomp : (fun q : ℝ × sphere (0 : E) 1 => (q.2 : E))
        = ((↑) : sphere (0 : E) 1 → E) ∘ (fun q : ℝ × sphere (0 : E) 1 => q.2) := rfl
    rw [hcomp, mfderiv_comp p hι hsndM, ContinuousLinearMap.comp_apply, hsndD w]
  have hD₁ : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
          (fun q : ℝ × sphere (0 : E) 1 => Real.cos (2 * q.1) / 2) p w
        = -Real.sin (2 * p.1) * w.1 :=
    fun w => mfderiv_comp_fst_apply hcos w
  have hD₂ : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
          (fun q : ℝ × sphere (0 : E) 1 => (Real.sin (2 * q.1) / 2) • (q.2 : E)) p w
        = (Real.cos (2 * p.1) * w.1) • ((p.2 : E))
          + (Real.sin (2 * p.1) / 2) • NormedSpace.fromTangentSpace _
              (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 w.2) := by
    intro w
    have h := mfderiv_warpSmul_apply (c := Prod.fst)
      (w := fun q : ℝ × sphere (0 : E) 1 => (q.2 : E))
      (f := fun r : ℝ => Real.sin (2 * r) / 2) hfstM heM hsin w
    rw [hfstD w, heD w] at h
    exact h
  -- assemble
  have hinner : ∀ a b : ℝ, (inner ℝ a b : ℝ) = b * a := fun _ _ => rfl
  rw [pullbackForm_toLp_prodMk h₁ h₂ u v, hD₁ u, hD₁ v, hD₂ u, hD₂ v, warpedProductForm_apply,
    hfstD u, hfstD v, hsndD u, hsndD v, sphereMetricUnit_apply, innerProductSpaceMetric_apply]
  simp only [hinner, fromTangentSpace_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_coe_mfderiv_coe_unitSphere,
    inner_mfderiv_coe_sphere_coe, real_inner_coe_self_sphere]
  linear_combination (u.1 * v.1) * Real.sin_sq_add_cos_sq (2 * p.1)

end SphereWarpedWithLp

/-- **Math.** `Ψ : ℝ × S¹ → S²(1/2)` is smooth.  As in `contMDiff_hopfMap`, smoothness into a
sphere of radius `r ≠ 1` is obtained by rescaling to the unit sphere (where mathlib's
`ContMDiff.codRestrict_sphere` applies) and transporting back along
`sphereHomeomorphUnitSphere`. -/
theorem contMDiff_sphereTwoParam :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 2) ∞ sphereTwoParam := by
  haveI : NormSMulClass ℝ (WithLp 2 (ℝ × ℂ)) := NormedSpace.toNormSMulClass
  have hmem : ∀ q : ℝ × sphere (0 : ℂ) 1,
      (2 : ℝ) • sphereTwoParamAmbient q ∈ sphere (0 : WithLp 2 (ℝ × ℂ)) 1 := by
    intro q
    rw [mem_sphere_zero_iff_norm, norm_smul,
      mem_sphere_zero_iff_norm.mp (sphereTwoParamAmbient_mem_sphere q)]
    norm_num
  have key : sphereTwoParam = ⇑(sphereHomeomorphUnitSphere (E := WithLp 2 (ℝ × ℂ)) (1 / 2)).symm
      ∘ Set.codRestrict (fun q : ℝ × sphere (0 : ℂ) 1 => (2 : ℝ) • sphereTwoParamAmbient q)
          (sphere (0 : WithLp 2 (ℝ × ℂ)) 1) hmem := by
    funext q
    refine Subtype.ext ?_
    show sphereTwoParamAmbient q = (1 / 2 : ℝ) • ((2 : ℝ) • sphereTwoParamAmbient q)
    module
  rw [key]
  refine (contMDiff_sphereHomeomorphUnitSphere_symm (1 / 2)).comp ?_
  exact ContMDiff.codRestrict_sphere
    (((contDiff_const_smul (2 : ℝ)).contMDiff).comp contMDiff_sphereTwoParamAmbient) hmem

/-- **Math.** Petersen Example 1.4.10, second coordinate representation: the parametrization
`Ψ(r, e^{iθ}) = (½cos(2r), ½sin(2r)·e^{iθ})` pulls the round metric of `S²(1/2)` back to
`dr² + ¼sin²(2r) dθ²` on `ℝ × S¹` — the `E = ℂ`, `n = 1` case of
`sphereAsWarpedProductWithLp`, after replacing the round metric of the ambient sphere by the
ambient inner product it is pulled back from. -/
theorem pullbackForm_sphereTwoParam (p : ℝ × sphere (0 : ℂ) 1)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 1)) p) :
    pullbackForm (I := 𝓘(ℝ, ℝ).prod (𝓡 1))
        (sphereMetric (n := 2) (WithLp 2 (ℝ × ℂ)) (1 / 2)) sphereTwoParam p u v
      = warpedProductForm (sphereMetricUnit ℂ) (fun _ => 1)
          (fun r => Real.sin (2 * r) / 2) p u v := by
  have hΨ : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 2) sphereTwoParam p :=
    (contMDiff_sphereTwoParam p).mdifferentiableAt (by simp)
  rw [pullbackForm_sphereMetric_eq_pullbackForm_ambient (1 / 2) hΨ u v]
  exact sphereAsWarpedProductWithLp (E := ℂ) p u v

/-! ## Example 1.4.10, assembled -/

/-- **Math.** Petersen Example 1.4.10 — **the Hopf fibration revisited**, in full, **on the genuine
spheres**.

`hopfFibrationRevisited` (`DoublyWarpedSmoothness.lean`) states the submersion property on the
*universal-cover coordinate model* `ℝ × ℝ × ℝ → ℝ × ℝ`, and its docstring notes that identifying
that model with the genuine spheres `S³(1) → S²(1/2)` (and with `SU(2)`) "needs the coordinate
immersions and is beyond the present API".  That is exactly what the `ℓ²`-product bridge supplies,
so this is the honest sphere-level statement of the example.

1. Via `Φ(t, e^{iθ₁}, e^{iθ₂}) = (sin(t)·e^{iθ₁}, cos(t)·e^{iθ₂})` the round metric of `S³(1)` is the
   doubly warped product `dt² + sin²(t) dθ₁² + cos²(t) dθ₂²`, `t ∈ [0, π/2]`.
2. Via `Ψ(r, e^{iθ}) = (½cos(2r), ½sin(2r)·e^{iθ})` the round metric of `S²(1/2)` is the warped
   product `dr² + ¼sin²(2r) dθ²`.
3. In these coordinates the Hopf map is `(t, e^{iθ₁}, e^{iθ₂}) ↦ (t, e^{i(θ₁−θ₂)})`, and it agrees
   with Wilhelm's map `H(z, w) = (½(|w|² − |z|²), z·conj w)` of Example 1.3.9 — the Hopf fibres are
   the circles `θ ↦ (t, e^{i(θ₁+θ)}, e^{i(θ₂+θ)})`, along which `θ₁ − θ₂` is constant.
4. It is a Riemannian submersion `S³(1) → S²(1/2)`.
5. Composed with Petersen's matrix `(t, e^{iθ₁}, e^{iθ₂}) ↦ [[cos(t)e^{iθ₁}, sin(t)e^{iθ₂}],
   [−sin(t)e^{−iθ₂}, cos(t)e^{−iθ₁}]]` it gives the identification `S³(1) ≅ SU(2)`, an isometry onto
   `SU(2)` with its left-invariant metric — because that left-invariant metric *is* the round metric
   of `S³(1)` (Example 1.3.5, `suTwoMetric_eq_sphereMetricUnit`). -/
theorem hopfFibrationRevisitedSphere :
    (∀ (p : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1))
        (u v : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 1).prod (𝓡 1))) p),
      pullbackForm (I := 𝓘(ℝ, ℝ).prod ((𝓡 1).prod (𝓡 1)))
          (sphereMetricUnit (n := 3) (WithLp 2 (ℂ × ℂ))) sphereThreeParam p u v
        = doublyWarpedProductForm (sphereMetricUnit ℂ) (sphereMetricUnit ℂ)
            Real.sin Real.cos p u v)
    ∧ (∀ (p : ℝ × sphere (0 : ℂ) 1) (u v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 1)) p),
      pullbackForm (I := 𝓘(ℝ, ℝ).prod (𝓡 1))
          (sphereMetric (n := 2) (WithLp 2 (ℝ × ℂ)) (1 / 2)) sphereTwoParam p u v
        = warpedProductForm (sphereMetricUnit ℂ) (fun _ => 1)
            (fun r => Real.sin (2 * r) / 2) p u v)
    ∧ (∀ q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1),
      hopfMap (sphereThreeParam q) = sphereTwoParam (hopfCoordMap q))
    ∧ IsRiemannianSubmersion (sphereMetricUnit (n := 3) (WithLp 2 (ℂ × ℂ)))
        (sphereMetric (n := 2) (WithLp 2 (ℝ × ℂ)) (1 / 2)) hopfMap
    ∧ (∀ (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1))
        (u v : TangentSpace (𝓡 3) (suTwoEquivSphere (suTwoParam q))),
      suTwoMetric.metricInner (suTwoEquivSphere (suTwoParam q)) u v
        = (sphereMetricUnit (WithLp 2 (ℂ × ℂ))).metricInner
            (suTwoEquivSphere (suTwoParam q)) u v) :=
  ⟨pullbackForm_sphereThreeParam, pullbackForm_sphereTwoParam, hopfMap_sphereThreeParam,
    hopfMap_isRiemannianSubmersion, suTwoMetric_eq_round_at_suTwoParam⟩

/-! ## `S^{2n+3}` as a doubly warped product (Petersen Example 1.4.14, source side) -/

section GeneralizedHopfSource

variable {n : ℕ}

/-- **Math.** Petersen Example 1.4.14, the **source identification**: taking `ρ = sin`, `φ = cos`
in Example 1.4.12, the doubly warped product

  `I × S^{2n+1} × S¹`,  `dt² + sin²(t) ds²_{2n+1} + cos²(t) dθ²`,  `t ∈ [0, π/2]`,

*is* the round sphere `S^{2n+3}` — the `E₁ = ℂ^{n+1}`, `E₂ = ℂ` case of
`sphereAsDoublyWarpedProductWithLp`, which applies verbatim because the `ℓ²`-product bridge is
stated for arbitrary factors.  (`doublyWarpedSphereMap_mem_sphere` says the map really does land in
the unit sphere, so this is the round metric of `S^{2n+3}`, of real dimension `2(n+1) + 2 = 2n+4`.)

**Scope.** The ambient `ℂ^{n+2}` is realized here as the `ℓ²`-product `WithLp 2 (ℂ^{n+1} × ℂ)`
rather than as `EuclideanSpace ℂ (Fin (n+2))`; the two are isometric (via `Fin.snoc`), but that
identification is neither needed for nor supplied by this statement.

This settles clause (i) of Example 1.4.14.  Clause (ii) — that the *quotient* is `ℂP^{n+1}` with the
Fubini–Study metric — remains open: `fubiniStudyMetric` takes the quotient manifold as a hypothesis,
and exhibiting `ℂP^{n+1}` as a smooth quotient manifold is genuinely missing infrastructure.  So the
blueprint node `ex:pet-ch1-generalized-hopf` is deliberately *not* marked `\leanok`. -/
theorem sphereOddAsDoublyWarpedProduct
    (p : ℝ × sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 × sphere (0 : ℂ) 1)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1))) p) :
    pullbackForm (I := 𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1)))
        (innerProductSpaceMetric (WithLp 2 (EuclideanSpace ℂ (Fin (n + 1)) × ℂ)))
        (fun q : ℝ × sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 × sphere (0 : ℂ) 1 =>
          (WithLp.toLp 2 (Real.sin q.1 • (q.2.1 : EuclideanSpace ℂ (Fin (n + 1))),
              Real.cos q.1 • (q.2.2 : ℂ))
            : WithLp 2 (EuclideanSpace ℂ (Fin (n + 1)) × ℂ))) p u v
      = doublyWarpedProductForm
          (sphereMetricUnit (n := 2 * n + 1) (EuclideanSpace ℂ (Fin (n + 1))))
          (sphereMetricUnit (n := 1) ℂ) Real.sin Real.cos p u v :=
  sphereAsDoublyWarpedProductWithLp p u v

end GeneralizedHopfSource

end PetersenLib
