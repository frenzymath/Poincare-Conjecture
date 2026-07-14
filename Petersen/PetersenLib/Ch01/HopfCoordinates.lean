import PetersenLib.Ch01.HopfSphereSubmersion
import PetersenLib.Ch01.SpaceForms
import PetersenLib.Ch01.LieGroupMetrics
import PetersenLib.Ch01.DoublyWarpedSmoothness

/-!
# Petersen Ch. 1, Example 1.4.10 — the Hopf fibration revisited (the coordinate model)

Petersen's Example 1.4.10 writes the Hopf fibration in the doubly warped coordinates of
Example 1.4.9:

* `S³(1)` is parametrized by `Φ(t, e^{iθ₁}, e^{iθ₂}) = (sin(t) e^{iθ₁}, cos(t) e^{iθ₂}) ∈ ℂ²`,
  carrying the metric `dt² + sin²(t) dθ₁² + cos²(t) dθ₂²`;
* `S²(1/2)` is parametrized by `Ψ(r, e^{iθ}) = (½cos(2r), ½sin(2r) e^{iθ}) ∈ ℝ × ℂ`, carrying
  the metric `dr² + ¼ sin²(2r) dθ²`;
* in these coordinates the Hopf map is `(t, e^{iθ₁}, e^{iθ₂}) ↦ (t, e^{i(θ₁−θ₂)})`, and it
  **agrees with Wilhelm's map** `H(z, w) = ((|w|² − |z|²)/2, z·conj w)` of Example 1.3.9.

The *submersion* half of the example is `PetersenLib.hopfFibrationRevisited`
(`Ch01/DoublyWarpedSmoothness.lean`), proved on the universal-cover coordinate model
`ℝ × ℝ × ℝ → ℝ × ℝ` as the case `ρ = sin`, `φ = cos` of `hopfFibrationGeneralSubmersion`, with
target warping `√((sin·cos)²/(sin²+cos²)) = ½sin(2r)`.

This file supplies the **genuine-sphere side** of the example: the two parametrizations `Φ`, `Ψ`
as smooth maps into the honest spheres `S³(1) ⊆ ℂ²` and `S²(1/2) ⊆ ℝ × ℂ`, the coordinate Hopf
map `(t, u, v) ↦ (t, u·conj v)`, the commuting square

  `hopfMap ∘ Φ = Ψ ∘ hopfCoordMap`   (`hopfMap_sphereThreeParam`)

identifying Petersen's coordinate Hopf map with Wilhelm's `H`, and the identification of `S³(1)`
with `SU(2)` by Petersen's explicit matrix

  `(t, e^{iθ₁}, e^{iθ₂}) ↦ [[cos(t)e^{iθ₁}, sin(t)e^{iθ₂}], [−sin(t)e^{−iθ₂}, cos(t)e^{−iθ₁}]]`,

which is an isometry onto `SU(2)` with its left-invariant metric because that metric *is* the
round metric of `S³(1)` (`suTwoMetric_eq_sphereMetricUnit`).

**Still open** (so the blueprint node `ex:pet-ch1-hopf-revisited` is not `\leanok`): that `Φ`
pulls the round metric of `S³` back to `dt² + sin²(t) dθ₁² + cos²(t) dθ₂²` and that `Ψ` pulls the
round metric of `S²(1/2)` back to `dr² + ¼sin²(2r) dθ²`.  The first is `sphereAsDoublyWarpedProduct`
(`Ch01/SpaceForms.lean`) *modulo a change of ambient model*: that lemma computes the pullback into
the plain product `E₁ × E₂` with `productMetric`, whereas `hopfMap` and `suTwoEquivSphere` need the
`L²`-product `WithLp 2 (ℂ × ℂ)`.  Bridging the two requires `mfderiv (L ∘ f) = L ∘ mfderiv f` for the
continuous linear equiv `L : ℂ × ℂ ≃L[ℝ] WithLp 2 (ℂ × ℂ)`, which is where the typeclass elaboration
currently gets stuck.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Example 1.4.10.
-/

open Metric Module ComplexConjugate
open scoped ContDiff Manifold Topology RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace PetersenLib

/-! ## `L²`-product bookkeeping -/

section WithLpAlgebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Eng.** Addition of `L²`-pairs is componentwise. -/
theorem toLp_add_toLp (a c : E) (b d : F) :
    (WithLp.toLp 2 (a, b) : WithLp 2 (E × F)) + WithLp.toLp 2 (c, d)
      = WithLp.toLp 2 (a + c, b + d) :=
  rfl

/-- **Eng.** Scalar multiplication of an `L²`-pair is componentwise. -/
theorem smul_toLp (r : ℝ) (a : E) (b : F) :
    r • (WithLp.toLp 2 (a, b) : WithLp 2 (E × F)) = WithLp.toLp 2 (r • a, r • b) :=
  rfl

end WithLpAlgebra

/-! ## The `S³` parametrization `Φ(t, e^{iθ₁}, e^{iθ₂}) = (sin(t) e^{iθ₁}, cos(t) e^{iθ₂})` -/

section SphereThree

/-- **Eng.** The `ℂ`-inclusion of the first `L²`-factor of `ℂ²`. -/
def inlC : ℂ →L[ℝ] WithLp 2 (ℂ × ℂ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm : ℂ × ℂ →L[ℝ] WithLp 2 (ℂ × ℂ)).comp
    (ContinuousLinearMap.inl ℝ ℂ ℂ)

/-- **Eng.** The `ℂ`-inclusion of the second `L²`-factor of `ℂ²`. -/
def inrC : ℂ →L[ℝ] WithLp 2 (ℂ × ℂ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).symm : ℂ × ℂ →L[ℝ] WithLp 2 (ℂ × ℂ)).comp
    (ContinuousLinearMap.inr ℝ ℂ ℂ)

@[simp] theorem inlC_apply (a : ℂ) : inlC a = WithLp.toLp 2 (a, 0) := rfl

@[simp] theorem inrC_apply (b : ℂ) : inrC b = WithLp.toLp 2 (0, b) := rfl

/-- **Math.** Petersen Example 1.4.10: the ambient parametrization of `S³(1)`,
`Φ(t, e^{iθ₁}, e^{iθ₂}) = (sin(t)·e^{iθ₁}, cos(t)·e^{iθ₂}) ∈ ℂ²`. -/
def sphereThreeParamAmbient (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) :
    WithLp 2 (ℂ × ℂ) :=
  WithLp.toLp 2 (Real.sin q.1 • (q.2.1 : ℂ), Real.cos q.1 • (q.2.2 : ℂ))

/-- **Eng.** `Φ` as a sum of two warped `L²`-components — the shape in which its smoothness is
read off from the smoothness of `sin`, `cos` and the two sphere inclusions. -/
theorem sphereThreeParamAmbient_eq_add :
    sphereThreeParamAmbient
      = (fun q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1) =>
          Real.sin q.1 • inlC (q.2.1 : ℂ))
        + fun q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1) =>
          Real.cos q.1 • inrC (q.2.2 : ℂ) := by
  funext q
  have hsum : (Real.sin q.1 • inlC (q.2.1 : ℂ) + Real.cos q.1 • inrC (q.2.2 : ℂ)
        : WithLp 2 (ℂ × ℂ))
      = WithLp.toLp 2 (Real.sin q.1 • (q.2.1 : ℂ) + Real.cos q.1 • (0 : ℂ),
          Real.sin q.1 • (0 : ℂ) + Real.cos q.1 • (q.2.2 : ℂ)) := rfl
  show sphereThreeParamAmbient q
      = Real.sin q.1 • inlC (q.2.1 : ℂ) + Real.cos q.1 • inrC (q.2.2 : ℂ)
  rw [hsum, sphereThreeParamAmbient]
  simp

/-- **Math.** Petersen Example 1.4.10: `Φ` takes values in the unit sphere `S³(1) ⊆ ℂ²`, since
`|sin(t)|² + |cos(t)|² = 1`. -/
theorem sphereThreeParamAmbient_mem_sphere
    (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) :
    sphereThreeParamAmbient q ∈ sphere (0 : WithLp 2 (ℂ × ℂ)) 1 :=
  doublyWarpedSphereMap_mem_sphere q.1 q.2.1 q.2.2

/-- **Math.** Petersen Example 1.4.10: the parametrization `Φ : ℝ × S¹ × S¹ → S³(1)`. -/
def sphereThreeParam (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) :
    sphere (0 : WithLp 2 (ℂ × ℂ)) 1 :=
  ⟨sphereThreeParamAmbient q, sphereThreeParamAmbient_mem_sphere q⟩

@[simp]
theorem coe_sphereThreeParam (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) :
    (sphereThreeParam q : WithLp 2 (ℂ × ℂ)) = sphereThreeParamAmbient q :=
  rfl

/-- **Math.** The ambient parametrization `Φ` is smooth. -/
theorem contMDiff_sphereThreeParamAmbient :
    ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) ∞
      sphereThreeParamAmbient := by
  have hfst : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1) => q.1) := contMDiff_fst
  have h21 : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ, ℂ) ∞
      (fun q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1) => (q.2.1 : ℂ)) :=
    (contMDiff_coe_sphere).comp
      ((contMDiff_fst (I := 𝓡 1) (J := 𝓡 1)).comp contMDiff_snd)
  have h22 : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ, ℂ) ∞
      (fun q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1) => (q.2.2 : ℂ)) :=
    (contMDiff_coe_sphere).comp
      ((contMDiff_snd (I := 𝓡 1) (J := 𝓡 1)).comp contMDiff_snd)
  rw [sphereThreeParamAmbient_eq_add]
  refine ContMDiff.add ?_ ?_
  · exact (Real.contDiff_sin.contMDiff.comp hfst).smul (inlC.contMDiff.comp h21)
  · exact (Real.contDiff_cos.contMDiff.comp hfst).smul (inrC.contMDiff.comp h22)

/-- **Math.** The parametrization `Φ : ℝ × S¹ × S¹ → S³(1)` is smooth. -/
theorem contMDiff_sphereThreeParam :
    ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓡 3) ∞ sphereThreeParam :=
  ContMDiff.codRestrict_sphere contMDiff_sphereThreeParamAmbient
    sphereThreeParamAmbient_mem_sphere

end SphereThree

/-! ## The `S²(1/2)` parametrization `Ψ(r, e^{iθ}) = (½cos(2r), ½sin(2r) e^{iθ})` -/

section SphereTwo

/-- **Eng.** The `ℝ`-inclusion of the first `L²`-factor of `ℝ × ℂ`. -/
def inlR : ℝ →L[ℝ] WithLp 2 (ℝ × ℂ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℂ).symm : ℝ × ℂ →L[ℝ] WithLp 2 (ℝ × ℂ)).comp
    (ContinuousLinearMap.inl ℝ ℝ ℂ)

/-- **Eng.** The `ℂ`-inclusion of the second `L²`-factor of `ℝ × ℂ`. -/
def inrR : ℂ →L[ℝ] WithLp 2 (ℝ × ℂ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℂ).symm : ℝ × ℂ →L[ℝ] WithLp 2 (ℝ × ℂ)).comp
    (ContinuousLinearMap.inr ℝ ℝ ℂ)

@[simp] theorem inlR_apply (a : ℝ) : inlR a = WithLp.toLp 2 (a, 0) := rfl

@[simp] theorem inrR_apply (b : ℂ) : inrR b = WithLp.toLp 2 (0, b) := rfl

/-- **Math.** Petersen Example 1.4.10: the ambient parametrization of `S²(1/2) ⊆ ℝ × ℂ = ℝ³`,
`Ψ(r, e^{iθ}) = (½cos(2r), ½sin(2r)·e^{iθ})`. -/
def sphereTwoParamAmbient (q : ℝ × sphere (0 : ℂ) 1) : WithLp 2 (ℝ × ℂ) :=
  WithLp.toLp 2 (Real.cos (2 * q.1) / 2, (Real.sin (2 * q.1) / 2) • (q.2 : ℂ))

/-- **Eng.** `Ψ` as a sum of two `L²`-components. -/
theorem sphereTwoParamAmbient_eq_add :
    sphereTwoParamAmbient
      = (fun q : ℝ × sphere (0 : ℂ) 1 => inlR (Real.cos (2 * q.1) / 2))
        + fun q : ℝ × sphere (0 : ℂ) 1 =>
          (Real.sin (2 * q.1) / 2) • inrR (q.2 : ℂ) := by
  funext q
  have hsum : (inlR (Real.cos (2 * q.1) / 2)
        + (Real.sin (2 * q.1) / 2) • inrR (q.2 : ℂ) : WithLp 2 (ℝ × ℂ))
      = WithLp.toLp 2 (Real.cos (2 * q.1) / 2 + (Real.sin (2 * q.1) / 2) • (0 : ℝ),
          (0 : ℂ) + (Real.sin (2 * q.1) / 2) • (q.2 : ℂ)) := rfl
  show sphereTwoParamAmbient q
      = inlR (Real.cos (2 * q.1) / 2) + (Real.sin (2 * q.1) / 2) • inrR (q.2 : ℂ)
  rw [hsum, sphereTwoParamAmbient]
  simp

/-- **Math.** Petersen Example 1.4.10: `Ψ` takes values in the sphere of radius `1/2`:
`|½cos(2r)|² + |½sin(2r)|² = ¼`. -/
theorem sphereTwoParamAmbient_mem_sphere (q : ℝ × sphere (0 : ℂ) 1) :
    sphereTwoParamAmbient q ∈ sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) := by
  have he : ‖(q.2 : ℂ)‖ = 1 := norm_coe_unitSphere q.2
  have hn : ‖(Real.sin (2 * q.1) / 2) • (q.2 : ℂ)‖ = |Real.sin (2 * q.1) / 2| := by
    rw [Complex.real_smul, norm_mul, Complex.norm_real, he, mul_one, Real.norm_eq_abs]
  rw [mem_sphere_zero_iff_norm, WithLp.prod_norm_eq_of_L2]
  show Real.sqrt (‖Real.cos (2 * q.1) / 2‖ ^ 2
      + ‖(Real.sin (2 * q.1) / 2) • (q.2 : ℂ)‖ ^ 2) = 1 / 2
  rw [hn, Real.norm_eq_abs, sq_abs, sq_abs]
  have h : (Real.cos (2 * q.1) / 2) ^ 2 + (Real.sin (2 * q.1) / 2) ^ 2 = (1 / 2 : ℝ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (2 * q.1)]
  rw [h, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)]

/-- **Math.** Petersen Example 1.4.10: the parametrization `Ψ : ℝ × S¹ → S²(1/2)`. -/
def sphereTwoParam (q : ℝ × sphere (0 : ℂ) 1) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) :=
  ⟨sphereTwoParamAmbient q, sphereTwoParamAmbient_mem_sphere q⟩

@[simp]
theorem coe_sphereTwoParam (q : ℝ × sphere (0 : ℂ) 1) :
    (sphereTwoParam q : WithLp 2 (ℝ × ℂ)) = sphereTwoParamAmbient q :=
  rfl

/-- **Math.** The ambient parametrization `Ψ` is smooth. -/
theorem contMDiff_sphereTwoParamAmbient :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, WithLp 2 (ℝ × ℂ)) ∞ sphereTwoParamAmbient := by
  have hfst : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × sphere (0 : ℂ) 1 => q.1) := contMDiff_fst
  have h2 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun q : ℝ × sphere (0 : ℂ) 1 => (q.2 : ℂ)) :=
    (contMDiff_coe_sphere).comp contMDiff_snd
  have hang : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × sphere (0 : ℂ) 1 => 2 * q.1) :=
    (contDiff_const.mul contDiff_id).contMDiff.comp hfst
  rw [sphereTwoParamAmbient_eq_add]
  refine ContMDiff.add ?_ ?_
  · exact inlR.contMDiff.comp ((Real.contDiff_cos.contMDiff.comp hang).div_const 2)
  · exact ((Real.contDiff_sin.contMDiff.comp hang).div_const 2).smul (inrR.contMDiff.comp h2)

end SphereTwo

/-! ## The coordinate Hopf map, and Wilhelm's map -/

section Wilhelm

/-- **Math.** Petersen Example 1.4.10: the Hopf map **in the coordinates of Example 1.4.9**,
`(t, e^{iθ₁}, e^{iθ₂}) ↦ (t, e^{i(θ₁ − θ₂)})`, i.e. `(t, u, v) ↦ (t, u·conj v)`. -/
def hopfCoordMap (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) : ℝ × sphere (0 : ℂ) 1 :=
  (q.1, ⟨(q.2.1 : ℂ) * conj (q.2.2 : ℂ), by
    have h1 : ‖(q.2.1 : ℂ)‖ = 1 := norm_coe_unitSphere q.2.1
    have h2 : ‖(q.2.2 : ℂ)‖ = 1 := norm_coe_unitSphere q.2.2
    rw [mem_sphere_zero_iff_norm, norm_mul, RCLike.norm_conj, h1, h2, one_mul]⟩)

@[simp]
theorem hopfCoordMap_fst (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) :
    (hopfCoordMap q).1 = q.1 := rfl

@[simp]
theorem coe_hopfCoordMap_snd (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) :
    ((hopfCoordMap q).2 : ℂ) = (q.2.1 : ℂ) * conj (q.2.2 : ℂ) := rfl

/-- **Math.** Petersen Example 1.4.10 — **the coordinate Hopf map agrees with Wilhelm's map.**
Substituting `z = sin(t)·u`, `w = cos(t)·v` (with `|u| = |v| = 1`) into Wilhelm's
`H(z, w) = ((|w|² − |z|²)/2, z·conj w)` of Example 1.3.9 gives

  `H(Φ(t, u, v)) = (½(cos²t − sin²t), sin(t)cos(t)·(u·conj v)) = (½cos(2t), ½sin(2t)·(u·conj v))`,

which is exactly `Ψ(t, u·conj v)`.  So Wilhelm's Hopf map `S³(1) → S²(1/2)`, read through the two
coordinate parametrizations, *is* Petersen's `(t, e^{iθ₁}, e^{iθ₂}) ↦ (t, e^{i(θ₁ − θ₂)})`. -/
theorem hopfMap_sphereThreeParam (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) :
    hopfMap (sphereThreeParam q) = sphereTwoParam (hopfCoordMap q) := by
  have hu : ‖(q.2.1 : ℂ)‖ = 1 := norm_coe_unitSphere q.2.1
  have hv : ‖(q.2.2 : ℂ)‖ = 1 := norm_coe_unitSphere q.2.2
  refine Subtype.ext ?_
  show hopfMapAmbient (sphereThreeParam q : WithLp 2 (ℂ × ℂ))
      = sphereTwoParamAmbient (hopfCoordMap q)
  -- the two ambient components
  have hnu : ‖Real.sin q.1 • (q.2.1 : ℂ)‖ = |Real.sin q.1| := by
    rw [Complex.real_smul, norm_mul, Complex.norm_real, hu, mul_one, Real.norm_eq_abs]
  have hnv : ‖Real.cos q.1 • (q.2.2 : ℂ)‖ = |Real.cos q.1| := by
    rw [Complex.real_smul, norm_mul, Complex.norm_real, hv, mul_one, Real.norm_eq_abs]
  have hfst : ‖(sphereThreeParamAmbient q).snd‖ ^ 2 - ‖(sphereThreeParamAmbient q).fst‖ ^ 2
      = Real.cos (2 * q.1) := by
    show ‖Real.cos q.1 • (q.2.2 : ℂ)‖ ^ 2 - ‖Real.sin q.1 • (q.2.1 : ℂ)‖ ^ 2 = _
    rw [hnu, hnv, sq_abs, sq_abs, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq q.1]
  have hsnd : (sphereThreeParamAmbient q).fst * conj (sphereThreeParamAmbient q).snd
      = (Real.sin (2 * q.1) / 2) • ((q.2.1 : ℂ) * conj (q.2.2 : ℂ)) := by
    show (Real.sin q.1 • (q.2.1 : ℂ)) * conj (Real.cos q.1 • (q.2.2 : ℂ)) = _
    rw [Complex.real_smul, Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal,
      Real.sin_two_mul]
    push_cast
    ring
  show WithLp.toLp 2
      ((‖(sphereThreeParamAmbient q).snd‖ ^ 2 - ‖(sphereThreeParamAmbient q).fst‖ ^ 2) / 2,
        (sphereThreeParamAmbient q).fst * conj (sphereThreeParamAmbient q).snd)
    = WithLp.toLp 2 (Real.cos (2 * (hopfCoordMap q).1) / 2,
        (Real.sin (2 * (hopfCoordMap q).1) / 2) • ((hopfCoordMap q).2 : ℂ))
  rw [hfst, hsnd, hopfCoordMap_fst, coe_hopfCoordMap_snd]

end Wilhelm

/-! ## The identification `S³(1) ≅ SU(2)` -/

section SUTwo

open Matrix

/-- **Math.** Petersen Example 1.4.10: the explicit matrix of the identification
`S³(1) → SU(2)`,
`(t, e^{iθ₁}, e^{iθ₂}) ↦ [[cos(t)e^{iθ₁}, sin(t)e^{iθ₂}], [−sin(t)e^{−iθ₂}, cos(t)e^{−iθ₁}]]`.
Its first row is `(cos(t)·u, sin(t)·v)`, and the second row is forced to be `(−conj w, conj z)`
by `mem_specialUnitaryGroup_fin_two_iff` — the matrix is exactly the `SU(2)` element attached to
the sphere point `(cos(t)·u, sin(t)·v)`. -/
def suTwoParamMatrix (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos q.1 : ℂ) * (q.2.1 : ℂ), (Real.sin q.1 : ℂ) * (q.2.2 : ℂ);
     -conj ((Real.sin q.1 : ℂ) * (q.2.2 : ℂ)), conj ((Real.cos q.1 : ℂ) * (q.2.1 : ℂ))]

/-- **Math.** Petersen Example 1.4.10: the matrix above lies in `SU(2)`, because
`|cos(t)u|² + |sin(t)v|² = cos²(t) + sin²(t) = 1`. -/
theorem suTwoParamMatrix_mem (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) :
    suTwoParamMatrix q ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hu : ‖(q.2.1 : ℂ)‖ = 1 := norm_coe_unitSphere q.2.1
  have hv : ‖(q.2.2 : ℂ)‖ = 1 := norm_coe_unitSphere q.2.2
  refine mem_specialUnitaryGroup_fin_two_iff.mpr
    ⟨(Real.cos q.1 : ℂ) * (q.2.1 : ℂ), (Real.sin q.1 : ℂ) * (q.2.2 : ℂ), ?_, rfl⟩
  rw [norm_mul, norm_mul, hu, hv, mul_one, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq q.1]

/-- **Math.** Petersen Example 1.4.10: the identification `ℝ × S¹ × S¹ → SU(2)`. -/
def suTwoParam (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) :
    Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  ⟨suTwoParamMatrix q, suTwoParamMatrix_mem q⟩

/-- **Math.** Petersen Example 1.4.10: under the identification `SU(2) ≅ S³(1)` of
Example 1.3.5 (`suTwoEquivSphere`, "take the first row"), Petersen's matrix corresponds to the
sphere point `(cos(t)·e^{iθ₁}, sin(t)·e^{iθ₂})` — the parametrization `Φ` with `sin` and `cos`
interchanged. -/
theorem suTwoEquivSphere_suTwoParam (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1)) :
    (suTwoEquivSphere (suTwoParam q) : WithLp 2 (ℂ × ℂ))
      = WithLp.toLp 2 ((Real.cos q.1 : ℂ) * (q.2.1 : ℂ),
          (Real.sin q.1 : ℂ) * (q.2.2 : ℂ)) :=
  rfl

/-- **Math.** Petersen Example 1.4.10 (the last clause): the identification `S³(1) → SU(2)` is a
**Riemannian isometry** onto `SU(2)` with its left-invariant metric — because that left-invariant
metric *is* the round metric of `S³(1)` (`suTwoMetric_eq_sphereMetricUnit`, Example 1.3.5: the
left-invariant frame `X₁, X₂, X₃` is orthonormal for the round metric).  Stated at the points in
the image of Petersen's matrix parametrization. -/
theorem suTwoMetric_eq_round_at_suTwoParam (q : ℝ × (sphere (0 : ℂ) 1 × sphere (0 : ℂ) 1))
    (u v : TangentSpace (𝓡 3) (suTwoEquivSphere (suTwoParam q))) :
    suTwoMetric.metricInner (suTwoEquivSphere (suTwoParam q)) u v
      = (sphereMetricUnit (WithLp 2 (ℂ × ℂ))).metricInner
          (suTwoEquivSphere (suTwoParam q)) u v :=
  suTwoMetric_eq_sphereMetricUnit _ u v

end SUTwo

end PetersenLib
