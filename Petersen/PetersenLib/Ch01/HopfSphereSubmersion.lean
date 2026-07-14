import PetersenLib.Ch01.HopfHigherDim
import PetersenLib.Ch01.HomogeneousMetrics
import PetersenLib.Ch01.HopfFibration
import PetersenLib.Ch01.SpaceForms

/-!
# Petersen Ch. 1, §1.4.6 — the higher-dimensional Hopf fibration, on the genuine sphere
(Examples 1.4.12–1.4.14)

Petersen's Example 1.4.12 considers `I × S^{2n+1} × S¹` with the doubly warped metric
`dt² + ρ²(t) ds²_{2n+1} + φ²(t) dθ²`, splits the round metric of the odd sphere as
`ds²_{2n+1} = h + g` into the Hopf-fibre direction `h` and its orthogonal complement `g`,
and lets the circle act by *simultaneous* complex scalar multiplication on both factors.
The quotient `(S^{2n+1} × S¹)/S¹` is again `S^{2n+1}` (via `(z, w) ↦ w⁻¹ · z`), and the
quotient map is a Riemannian submersion onto

  `dt² + ρ²(t) g + ((ρφ)²/(ρ² + φ²))(t) · h`.

Unlike `PetersenLib.Ch01.HopfHigherDim` — which proves these statements on a linear
*coordinate model* `ℝ × (ℝ × F) × ℝ` — everything here happens on the **genuine round
sphere** `S^{2n+1} = sphere (0 : ℂ^{n+1}) 1`, with the genuine circle
`S¹ = sphere (0 : ℂ) 1`, the genuine simultaneous circle action, and the genuine Hopf
splitting of the round metric.  No product structure on `T S^{2n+1}` is assumed (there is
none: the Hopf bundle is nontrivial); the splitting `h + g` is defined pointwise from the
*unit Hopf field* `z ↦ i·z`, which is a globally defined unit tangent field on the odd
sphere.

The concrete data:

* `hopfAngleForm z` — the Hopf 1-form `θ_z(u) = ⟪u, i·z⟫` on `T_z S^{2n+1}` (Petersen's
  `σ¹`, the coframe field dual to the Hopf-fibre direction).  Then `h = θ ⊗ θ` and
  `g = ds²_{2n+1} − h`.
* `hopfSphereQuotientMap (t, z, w) = (t, w⁻¹ • z)` — the quotient map realizing
  `I × (S^{2n+1} × S¹)/S¹ = I × S^{2n+1}`; its fibres are exactly the orbits of the
  simultaneous action `a · (z, w) = (a·z, a·w)` (`hopfSphereQuotientMap_eq_iff`).
* `hopfQuotientForm σ ρ` — the target form `dt² + ρ²(t) g + σ²(t) h` on `I × S^{2n+1}`.

Main results:

* `hopfFibrationHigherDimSphere` (Example 1.4.12) — the quotient map is a Riemannian
  submersion from `dt² + ρ²(t) ds²_{2n+1} + φ²(t) dθ²` onto
  `dt² + ρ²(t) g + ((ρφ)²/(ρ² + φ²))(t) h`, for arbitrary warping functions `ρ, φ`
  (which may vanish — hence the possibly degenerate *forms* `IsFormRiemannianSubmersion`).
* `hopfFibrationSUTwoCoframeSphere` (Example 1.4.13) — the case `n = 1`, where
  `S^{2n+1} = S³` and `h = (σ¹)²`, `g = (σ²)² + (σ³)²` in the `SU(2)` coframe.
* `generalizedHopfFibrationSphere` (Example 1.4.14) — the case `ρ = sin`, `φ = cos`, where
  `(sin·cos)²/(sin² + cos²) = sin²cos²`, so the target is `dt² + sin²(t)(g + cos²(t) h)`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Examples 1.4.12–1.4.14.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Metric Module
open scoped ContDiff Manifold Topology RealInnerProductSpace

namespace PetersenLib

/-! ## The circle `S¹ = sphere (0 : ℂ) 1` as a Riemannian manifold -/

section ComplexAmbient

/-- **Eng.** `ℂ` has real dimension `2 = 1 + 1`; this `Fact` feeds the unit circle
`S¹ = sphere (0 : ℂ) 1` its stereographic charted-space structure over
`EuclideanSpace ℝ (Fin 1)`, making it a `1`-dimensional smooth manifold. -/
instance fact_finrank_real_complex : Fact (finrank ℝ ℂ = 1 + 1) :=
  ⟨by simpa using Complex.finrank_real_complex⟩

/-- **Eng.** The real inner product of `ℂ` in real coordinates:
`⟪v, w⟫_ℝ = re(v)re(w) + im(v)im(w)`. -/
theorem real_inner_complex (v w : ℂ) : (inner ℝ v w : ℝ) = v.re * w.re + v.im * w.im := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  simp
  ring

/-- **Eng.** Multiplication by `i` preserves the norm of a complex number. -/
theorem norm_I_mul (w : ℂ) : ‖Complex.I * w‖ = ‖w‖ := by
  rw [norm_mul, Complex.norm_I, one_mul]

/-- **Eng.** The real and imaginary parts of `i·w`. -/
theorem I_mul_re (w : ℂ) : (Complex.I * w).re = -w.im := by simp [Complex.mul_re]

/-- **Eng.** The real and imaginary parts of `i·w`. -/
theorem I_mul_im (w : ℂ) : (Complex.I * w).im = w.re := by simp [Complex.mul_im]

/-- **Math.** `i·w` is real-orthogonal to `w`: it is the tangent direction of the circle
`|z| = ‖w‖` at `w`. -/
theorem real_inner_self_I_mul (w : ℂ) : (inner ℝ w (Complex.I * w) : ℝ) = 0 := by
  rw [real_inner_complex, I_mul_re, I_mul_im]
  ring

/-- **Eng.** Real scalars pull out of both slots of the real inner product of `ℂ`. -/
theorem real_inner_real_smul_smul (a b : ℝ) (x y : ℂ) :
    (inner ℝ (a • x) (b • y) : ℝ) = a * b * (inner ℝ x y : ℝ) := by
  simp only [real_inner_complex, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Math.** For a *unit* `w ∈ ℂ`, the pair `(w, i·w)` is a real orthonormal basis of `ℂ`;
hence any `v` real-orthogonal to `w` is the real multiple `⟪i·w, v⟫ · (i·w)` of `i·w`.
This is the (one-dimensional) tangent space of the unit circle at `w`. -/
theorem eq_real_smul_I_mul {v w : ℂ} (hw : ‖w‖ = 1) (h : (inner ℝ w v : ℝ) = 0) :
    v = (inner ℝ (Complex.I * w) v : ℝ) • (Complex.I * w) := by
  have hn : w.re * w.re + w.im * w.im = 1 := by
    have h1 : (inner ℝ w w : ℝ) = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
    rw [real_inner_complex, hw] at h1
    simpa using h1
  rw [real_inner_complex] at h
  have hi : (inner ℝ (Complex.I * w) v : ℝ) = -w.im * v.re + w.re * v.im := by
    rw [real_inner_complex, I_mul_re, I_mul_im]
  rw [hi]
  refine Complex.ext ?_ ?_
  · simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linear_combination w.re * h - v.re * hn
  · simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linear_combination w.im * h - v.im * hn

/-- **Math.** Multiplication by a *unit* complex scalar is a real linear isometry of `ℂ^m`:
`⟪c·x, c·y⟫_ℝ = re⟪c·x, c·y⟫_ℂ = re(c̄c⟪x, y⟫_ℂ) = ⟪x, y⟫_ℝ` when `|c| = 1`.  (This
generalizes `real_inner_circle_smul_smul` from `a : Circle` to an arbitrary unit scalar,
which is what the quotient map `w ↦ w⁻¹` produces.) -/
theorem real_inner_unit_smul_smul {m : ℕ} {c : ℂ} (hc : ‖c‖ = 1)
    (x y : EuclideanSpace ℂ (Fin m)) :
    (inner ℝ (c • x) (c • y) : ℝ) = inner ℝ x y := by
  rw [real_inner_eq_re_inner_euclideanSpace, real_inner_eq_re_inner_euclideanSpace]
  congr 1
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hc]
  simp

/-- **Eng.** A unit complex scalar satisfies `conj(c)·c = 1`. -/
theorem conj_mul_self_of_norm_one {c : ℂ} (hc : ‖c‖ = 1) : (starRingEnd ℂ) c * c = 1 := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    exact zero_ne_one hc
  rw [← Complex.inv_eq_conj hc, inv_mul_cancel₀ hc0]

/-- **Eng.** A *real* scalar `s` in front of the Hopf direction `i·z` pulls out of the real
inner product.  Mathlib's `real_inner_smul_left` cannot be used on
`EuclideanSpace ℂ (Fin m)`: the `Module ℝ` diamond between the `PiLp` instance and the
restriction-of-scalars instance makes its unification diverge.  Writing the real scalar as
the *complex* scalar `(s : ℂ) · i` keeps everything inside the `ℂ`-inner-product API. -/
theorem real_inner_ofReal_I_smul_left {m : ℕ} (s : ℝ) (z a : EuclideanSpace ℂ (Fin m)) :
    (inner ℝ ((((s : ℝ) : ℂ) * Complex.I) • z) a : ℝ)
      = s * (inner ℝ (Complex.I • z) a : ℝ) := by
  rw [real_inner_eq_re_inner_euclideanSpace, real_inner_eq_re_inner_euclideanSpace,
    inner_smul_left, inner_smul_left, map_mul, Complex.conj_ofReal, mul_assoc,
    Complex.re_ofReal_mul]

/-- **Eng.** The same on the right, via symmetry of the real inner product. -/
theorem real_inner_ofReal_I_smul_right {m : ℕ} (s : ℝ) (z a : EuclideanSpace ℂ (Fin m)) :
    (inner ℝ a ((((s : ℝ) : ℂ) * Complex.I) • z) : ℝ)
      = s * (inner ℝ (Complex.I • z) a : ℝ) := by
  rw [real_inner_comm, real_inner_ofReal_I_smul_left]

/-- **Eng.** `⟪i·z, (s·i)·z⟫_ℝ = s` for a unit `z`: the Hopf direction is a unit vector. -/
theorem real_inner_I_smul_ofReal_I_smul {m : ℕ} (s : ℝ) {z : EuclideanSpace ℂ (Fin m)}
    (hz : ‖z‖ = 1) :
    (inner ℝ (Complex.I • z) ((((s : ℝ) : ℂ) * Complex.I) • z) : ℝ) = s := by
  have hzz : (inner ℂ z z : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hz]
    norm_num
  rw [real_inner_eq_re_inner_euclideanSpace, inner_smul_left, inner_smul_right, hzz,
    Complex.conj_I]
  have hval : (-Complex.I) * ((((s : ℝ) : ℂ) * Complex.I) * 1) = (((s : ℝ) : ℂ)) := by
    linear_combination (-((s : ℝ) : ℂ)) * Complex.I_sq
  rw [hval, Complex.ofReal_re]

end ComplexAmbient

/-! ## The Hopf 1-form on the odd-dimensional sphere -/

section HopfSphere

variable {n : ℕ}

/-- Local shorthand for the ambient space `ℂ^{n+1}` carrying `S^{2n+1}`. -/
local notation "𝔼" => EuclideanSpace ℂ (Fin (n + 1))

/-- **Eng.** The ambient tangent vector of `S^{2n+1} ⊆ ℂ^{n+1}` attached to an intrinsic
tangent vector, i.e. the image under the differential of the inclusion. -/
abbrev sphereAmbient (z : sphere (0 : 𝔼) 1) (u : TangentSpace (𝓡 (2 * n + 1)) z) : 𝔼 :=
  mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) z u

/-- **Eng.** The ambient tangent vector of `S¹ ⊆ ℂ` attached to an intrinsic tangent
vector. -/
abbrev circleAmbient (w : sphere (0 : ℂ) 1) (c : TangentSpace (𝓡 1) w) : ℂ :=
  mfderiv (𝓡 1) 𝓘(ℝ, ℂ) ((↑) : sphere (0 : ℂ) 1 → ℂ) w c

/-- **Math.** The **Hopf 1-form** `θ` of `S^{2n+1} ⊆ ℂ^{n+1}`: the coframe field dual to
the Hopf-fibre direction.  The Hopf fibres are the orbits of the circle action
`a · z = a z`, whose velocity at `z` is the *unit* tangent vector `i·z`; so
`θ_z(u) = ⟪i·z, u⟫` is the component of `u` along the fibre.  Petersen's `σ¹` in the
`SU(2)` coframe of Example 1.4.13. -/
def hopfAngleForm (z : sphere (0 : 𝔼) 1) : TangentSpace (𝓡 (2 * n + 1)) z →L[ℝ] ℝ :=
  (innerSL ℝ (Complex.I • (z : 𝔼))).comp
    (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) z)

@[simp]
theorem hopfAngleForm_apply (z : sphere (0 : 𝔼) 1) (u : TangentSpace (𝓡 (2 * n + 1)) z) :
    hopfAngleForm z u = (inner ℝ (Complex.I • (z : 𝔼)) (sphereAmbient z u) : ℝ) := rfl

/-- **Math.** The **angle form** `dθ` of the circle `S¹ ⊆ ℂ`: the component of a tangent
vector along the unit tangent `i·w`. -/
def circleAngleForm (w : sphere (0 : ℂ) 1) : TangentSpace (𝓡 1) w →L[ℝ] ℝ :=
  (innerSL ℝ (Complex.I * (w : ℂ))).comp
    (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) ((↑) : sphere (0 : ℂ) 1 → ℂ) w)

@[simp]
theorem circleAngleForm_apply (w : sphere (0 : ℂ) 1) (c : TangentSpace (𝓡 1) w) :
    circleAngleForm w c = (inner ℝ (Complex.I * (w : ℂ)) (circleAmbient w c) : ℝ) := rfl

/-- **Eng.** The norm of a point of the unit sphere is `1`. -/
theorem norm_coe_unitSphere {E : Type*} [NormedAddCommGroup E] (x : sphere (0 : E) 1) :
    ‖(x : E)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2

/-- **Math.** Since `S¹ ⊆ ℂ` is one-dimensional, every ambient tangent vector of the
circle at `w` is the real multiple `dθ(c) · (i·w)` of the unit tangent `i·w`. -/
theorem circleAmbient_eq (w : sphere (0 : ℂ) 1) (c : TangentSpace (𝓡 1) w) :
    circleAmbient w c = (circleAngleForm w c) • (Complex.I * (w : ℂ)) :=
  eq_real_smul_I_mul (norm_coe_unitSphere w) (inner_coe_mfderiv_coe_unitSphere w c)

/-- **Eng.** `i·w` is a unit vector when `w` is. -/
theorem norm_I_mul_coe_circle (w : sphere (0 : ℂ) 1) : ‖Complex.I * (w : ℂ)‖ = 1 := by
  rw [norm_I_mul, norm_coe_unitSphere]

/-- **Math.** The round metric of `S¹` in terms of the angle form: `dθ² `, i.e.
`⟪c, c'⟫ = dθ(c) dθ(c')`.  (One-dimensionality again.) -/
theorem real_inner_circleAmbient (w : sphere (0 : ℂ) 1) (c c' : TangentSpace (𝓡 1) w) :
    (inner ℝ (circleAmbient w c) (circleAmbient w c') : ℝ)
      = circleAngleForm w c * circleAngleForm w c' := by
  have hu : (inner ℝ (Complex.I * (w : ℂ)) (Complex.I * (w : ℂ)) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_I_mul_coe_circle, one_pow]
  rw [circleAmbient_eq w c, circleAmbient_eq w c', real_inner_real_smul_smul, hu]
  ring

/-- **Eng.** `i·z` is a unit ambient vector when `z ∈ S^{2n+1}`. -/
theorem norm_I_smul_coe_sphere (z : sphere (0 : 𝔼) 1) : ‖Complex.I • (z : 𝔼)‖ = 1 := by
  rw [norm_smul, Complex.norm_I, one_mul, norm_coe_unitSphere]

/-- **Eng.** `⟪i·z, i·z⟫ = 1`. -/
theorem real_inner_I_smul_self (z : sphere (0 : 𝔼) 1) :
    (inner ℝ (Complex.I • (z : 𝔼)) (Complex.I • (z : 𝔼)) : ℝ) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_I_smul_coe_sphere, one_pow]

/-- **Math.** The Hopf field `i·z` is tangent to `S^{2n+1}` at `z`: it is real-orthogonal to
the position vector, since `⟪i·z, z⟫_ℝ = re(conj(i·z)·z)... = re(-i‖z‖²) = 0`. -/
theorem real_inner_I_smul_coe_sphere (z : sphere (0 : 𝔼) 1) :
    (inner ℝ ((z : 𝔼)) (Complex.I • (z : 𝔼)) : ℝ) = 0 := by
  rw [real_inner_eq_re_inner_euclideanSpace, inner_smul_right]
  have h : (inner ℂ (z : 𝔼) (z : 𝔼) : ℂ) = ((‖(z : 𝔼)‖ : ℝ) : ℂ) ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h, norm_coe_unitSphere]
  simp

end HopfSphere

/-! ## The quotient map `I × S^{2n+1} × S¹ → I × S^{2n+1}` (Petersen Example 1.4.12) -/

section HopfQuotient

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin (n + 1))

/-- **Math.** Petersen Example 1.4.12: the circle acts on `S^{2n+1} × S¹` by *simultaneous*
complex scalar multiplication, `a · (z, w) = (a z, a w)`, freely and isometrically; the orbit
space is again `S^{2n+1}`, identified via `(z, w) ↦ w⁻¹ z`.  This is the quotient map
`I × S^{2n+1} × S¹ → I × (S^{2n+1} × S¹)/S¹ = I × S^{2n+1}`, `(t, z, w) ↦ (t, w⁻¹ · z)`. -/
def hopfSphereQuotientMap :
    ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) → ℝ × sphere (0 : 𝔼) 1 :=
  fun q => (q.1, q.2.2⁻¹ • q.2.1)

/-- **Math.** The fibres of the quotient map are exactly the orbits of the simultaneous
circle action `a · (z, w) = (a z, a w)`: this is what makes `S^{2n+1}` the honest quotient
`(S^{2n+1} × S¹)/S¹` of Petersen's Example 1.4.12. -/
theorem hopfSphereQuotientMap_eq_iff
    (q q' : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1)) :
    hopfSphereQuotientMap q = hopfSphereQuotientMap q' ↔
      q.1 = q'.1 ∧ ∃ a : sphere (0 : ℂ) 1,
        a • q.2.1 = q'.2.1 ∧ a * q.2.2 = q'.2.2 := by
  constructor
  · intro h
    have h1 : q.1 = q'.1 := by
      simpa [hopfSphereQuotientMap] using congrArg Prod.fst h
    have h2 : q.2.2⁻¹ • q.2.1 = q'.2.2⁻¹ • q'.2.1 := by
      simpa [hopfSphereQuotientMap] using congrArg Prod.snd h
    refine ⟨h1, q'.2.2 * q.2.2⁻¹, ?_, ?_⟩
    · rw [mul_smul, h2, smul_inv_smul]
    · rw [mul_assoc, inv_mul_cancel, mul_one]
  · rintro ⟨h1, a, ha, hb⟩
    refine Prod.ext h1 ?_
    show q.2.2⁻¹ • q.2.1 = q'.2.2⁻¹ • q'.2.1
    rw [← ha, ← hb, mul_inv_rev, mul_smul, inv_smul_smul]

/-- **Eng.** The ambient expression of the quotient map's spherical component: on the unit
circle `w⁻¹ = conj w`, so `w⁻¹ · z` has ambient representative `conj(w) · z`. -/
def hopfAmbientMap : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) → 𝔼 :=
  fun q => (starRingEnd ℂ) (q.2.2 : ℂ) • (q.2.1 : 𝔼)

theorem coe_hopfSphereQuotientMap (q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1)) :
    ((hopfSphereQuotientMap q).2 : 𝔼) = hopfAmbientMap q := by
  show ((q.2.2⁻¹ : sphere (0 : ℂ) 1) : ℂ) • (q.2.1 : 𝔼) = _
  rw [hopfAmbientMap]
  congr 1
  have hinv : ((q.2.2⁻¹ : sphere (0 : ℂ) 1) : ℂ) = ((q.2.2 : ℂ))⁻¹ := rfl
  rw [hinv, Complex.inv_eq_conj (norm_coe_unitSphere q.2.2)]

/-- **Eng.** `conj w` is a unit scalar, hence `conj(w) · z` again lies on the unit sphere. -/
theorem norm_hopfAmbientMap (q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1)) :
    ‖hopfAmbientMap q‖ = 1 := by
  rw [hopfAmbientMap, norm_smul, RCLike.norm_conj, norm_coe_unitSphere,
    norm_coe_unitSphere, one_mul]

/-! ### The conjugate scalar multiplication as a continuous bilinear map

`ℂ^{n+1}` carries both an `ℝ`-module and a `ℂ`-module structure, and Mathlib's
`IsScalarTower ℝ ℂ (EuclideanSpace ℂ (Fin (n+1)))` does not fire in the elaboration
contexts of `ContinuousLinearMap.lsmul` / `HasFDerivAt.smul` (a `Module ℝ` diamond between
the `PiLp` instance and the restriction-of-scalars instance).  We therefore build the
bilinear map by hand out of the real and imaginary parts, `conj(c)·x = re(c)·x − im(c)·(i·x)`,
which uses only the `ℝ`-linear structure together with the *fixed* `ℂ`-scalar `i`. -/

/-- **Eng.** Multiplication by `i` on `ℂ^{n+1}`, as a real-linear continuous map. -/
def mulIL : 𝔼 →L[ℝ] 𝔼 := Complex.I • ContinuousLinearMap.id ℝ 𝔼

@[simp]
theorem mulIL_apply (x : 𝔼) : (mulIL : 𝔼 →L[ℝ] 𝔼) x = Complex.I • x := rfl

/-- **Eng.** The `ℝ`-bilinear "conjugate scalar multiplication" `ℂ × ℂ^{n+1} → ℂ^{n+1}`,
`(c, x) ↦ conj(c) · x`, as a continuous linear map into the space of continuous linear maps.
It is the ambient model of the quotient map, and being bilinear it is its own derivative. -/
def conjSmulL : ℂ →L[ℝ] 𝔼 →L[ℝ] 𝔼 :=
  Complex.reCLM.smulRight (ContinuousLinearMap.id ℝ 𝔼) -
    Complex.imCLM.smulRight (mulIL : 𝔼 →L[ℝ] 𝔼)

theorem conjSmulL_apply' (c : ℂ) (x : 𝔼) :
    (conjSmulL : ℂ →L[ℝ] 𝔼 →L[ℝ] 𝔼) c x = c.re • x - c.im • (Complex.I • x) := rfl

/-- **Math.** `conj(c) · x = re(c)·x − im(c)·(i·x)`: the real/imaginary decomposition of the
conjugate scalar action, checked coordinatewise in `ℂ^{n+1}`. -/
theorem conj_smul_eq_re_sub_im {m : ℕ} (c : ℂ) (x : EuclideanSpace ℂ (Fin m)) :
    (starRingEnd ℂ) c • x = c.re • x - c.im • (Complex.I • x) := by
  ext i
  simp [Complex.real_smul, Complex.ext_iff, Complex.mul_re, Complex.mul_im]
  ring

@[simp]
theorem conjSmulL_apply (c : ℂ) (x : 𝔼) :
    (conjSmulL : ℂ →L[ℝ] 𝔼 →L[ℝ] 𝔼) c x = (starRingEnd ℂ) c • x := by
  rw [conjSmulL_apply', conj_smul_eq_re_sub_im]

theorem hopfAmbientMap_eq_conjSmulL (q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1)) :
    hopfAmbientMap q = (conjSmulL : ℂ →L[ℝ] 𝔼 →L[ℝ] 𝔼) ((q.2.2 : ℂ)) ((q.2.1 : 𝔼)) := by
  rw [conjSmulL_apply, hopfAmbientMap]

/-! ### Smoothness and the differential of the quotient map -/

set_option quotPrecheck false in
local notation "𝕀ₛ" => (ModelWithCorners.prod 𝓘(ℝ, ℝ)
  (ModelWithCorners.prod (𝓡 (2 * n + 1)) (𝓡 1)))
set_option quotPrecheck false in
local notation "𝕀ₜ" => (ModelWithCorners.prod 𝓘(ℝ, ℝ) (𝓡 (2 * n + 1)))

theorem contMDiff_srcSphereCoe :
    ContMDiff 𝕀ₛ 𝓘(ℝ, 𝔼) ∞
      (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => (q.2.1 : 𝔼)) :=
  (contMDiff_coe_sphere (E := 𝔼) (n := 2 * n + 1) (m := ∞)).comp
    ((contMDiff_fst (I := 𝓡 (2 * n + 1)) (J := 𝓡 1)).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓡 (2 * n + 1)).prod (𝓡 1))))

theorem contMDiff_srcCircleCoe :
    ContMDiff 𝕀ₛ 𝓘(ℝ, ℂ) ∞
      (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => (q.2.2 : ℂ)) :=
  (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞)).comp
    ((contMDiff_snd (I := 𝓡 (2 * n + 1)) (J := 𝓡 1)).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓡 (2 * n + 1)).prod (𝓡 1))))

theorem mfderiv_srcSphereCoe_apply (p : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1))
    (u : TangentSpace 𝕀ₛ p) :
    mfderiv 𝕀ₛ 𝓘(ℝ, 𝔼) (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => (q.2.1 : 𝔼)) p u
      = sphereAmbient p.2.1 u.2.1 := by
  have hcomp : (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => (q.2.1 : 𝔼)) =
      ((↑) : sphere (0 : 𝔼) 1 → 𝔼) ∘
        (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => q.2.1) := rfl
  have hg : MDifferentiableAt 𝕀ₛ (𝓡 (2 * n + 1))
      (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => q.2.1) p :=
    (((contMDiff_fst (I := 𝓡 (2 * n + 1)) (J := 𝓡 1) (n := ∞)).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓡 (2 * n + 1)).prod (𝓡 1)) (n := ∞)))
        p).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼)
      ((↑) : sphere (0 : 𝔼) 1 → 𝔼) p.2.1 :=
    (contMDiff_coe_sphere (E := 𝔼) (n := 2 * n + 1) (m := ∞) p.2.1).mdifferentiableAt (by simp)
  have h := mfderiv_comp_apply (I' := 𝓡 (2 * n + 1)) (I'' := 𝓘(ℝ, 𝔼)) p hf hg u
  rw [mfderiv_proj21_apply] at h
  rw [hcomp]
  exact h

theorem mfderiv_srcCircleCoe_apply (p : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1))
    (u : TangentSpace 𝕀ₛ p) :
    mfderiv 𝕀ₛ 𝓘(ℝ, ℂ) (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => (q.2.2 : ℂ)) p u
      = circleAmbient p.2.2 u.2.2 := by
  have hcomp : (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => (q.2.2 : ℂ)) =
      ((↑) : sphere (0 : ℂ) 1 → ℂ) ∘
        (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => q.2.2) := rfl
  have hg : MDifferentiableAt 𝕀ₛ (𝓡 1)
      (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => q.2.2) p :=
    (((contMDiff_snd (I := 𝓡 (2 * n + 1)) (J := 𝓡 1) (n := ∞)).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓡 (2 * n + 1)).prod (𝓡 1)) (n := ∞)))
        p).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) ((↑) : sphere (0 : ℂ) 1 → ℂ) p.2.2 :=
    (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞) p.2.2).mdifferentiableAt (by simp)
  have h := mfderiv_comp_apply (I' := 𝓡 1) (I'' := 𝓘(ℝ, ℂ)) p hf hg u
  rw [mfderiv_proj22_apply] at h
  rw [hcomp]
  exact h

/-- **Eng.** The ambient pair `q ↦ (w, z) ∈ ℂ × ℂ^{n+1}`; the quotient map's ambient
representative is the bilinear `conjSmulL` composed with it. -/
def hopfPairMap : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) → ℂ × 𝔼 :=
  fun q => ((q.2.2 : ℂ), (q.2.1 : 𝔼))

theorem contMDiff_hopfPairMap :
    ContMDiff 𝕀ₛ 𝓘(ℝ, ℂ × 𝔼) ∞ (hopfPairMap (n := n)) :=
  contMDiff_srcCircleCoe.prodMk_space contMDiff_srcSphereCoe

theorem mfderiv_hopfPairMap_apply (p : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1))
    (u : TangentSpace 𝕀ₛ p) :
    mfderiv 𝕀ₛ 𝓘(ℝ, ℂ × 𝔼) (hopfPairMap (n := n)) p u
      = (circleAmbient p.2.2 u.2.2, sphereAmbient p.2.1 u.2.1) := by
  have hd : MDifferentiableAt 𝕀ₛ 𝓘(ℝ, ℂ × 𝔼) (hopfPairMap (n := n)) p :=
    (contMDiff_hopfPairMap p).mdifferentiableAt (by simp)
  have hfst : MDifferentiableAt 𝓘(ℝ, ℂ × 𝔼) 𝓘(ℝ, ℂ) (Prod.fst : ℂ × 𝔼 → ℂ)
      (hopfPairMap p) :=
    ((ContinuousLinearMap.fst ℝ ℂ 𝔼).contMDiff (n := ∞) _).mdifferentiableAt (by simp)
  have hsnd : MDifferentiableAt 𝓘(ℝ, ℂ × 𝔼) 𝓘(ℝ, 𝔼) (Prod.snd : ℂ × 𝔼 → 𝔼)
      (hopfPairMap p) :=
    ((ContinuousLinearMap.snd ℝ ℂ 𝔼).contMDiff (n := ∞) _).mdifferentiableAt (by simp)
  have hDfst : mfderiv 𝓘(ℝ, ℂ × 𝔼) 𝓘(ℝ, ℂ) (Prod.fst : ℂ × 𝔼 → ℂ) (hopfPairMap p)
      = ContinuousLinearMap.fst ℝ ℂ 𝔼 := by
    rw [mfderiv_eq_fderiv]; exact (ContinuousLinearMap.fst ℝ ℂ 𝔼).fderiv
  have hDsnd : mfderiv 𝓘(ℝ, ℂ × 𝔼) 𝓘(ℝ, 𝔼) (Prod.snd : ℂ × 𝔼 → 𝔼) (hopfPairMap p)
      = ContinuousLinearMap.snd ℝ ℂ 𝔼 := by
    rw [mfderiv_eq_fderiv]; exact (ContinuousLinearMap.snd ℝ ℂ 𝔼).fderiv
  have hcfst : (Prod.fst : ℂ × 𝔼 → ℂ) ∘ (hopfPairMap (n := n)) =
      fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => (q.2.2 : ℂ) := rfl
  have hcsnd : (Prod.snd : ℂ × 𝔼 → 𝔼) ∘ (hopfPairMap (n := n)) =
      fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => (q.2.1 : 𝔼) := rfl
  have h1 := mfderiv_comp_apply (I' := 𝓘(ℝ, ℂ × 𝔼)) (I'' := 𝓘(ℝ, ℂ)) p hfst hd u
  have h2 := mfderiv_comp_apply (I' := 𝓘(ℝ, ℂ × 𝔼)) (I'' := 𝓘(ℝ, 𝔼)) p hsnd hd u
  rw [hDfst, hcfst, mfderiv_srcCircleCoe_apply] at h1
  rw [hDsnd, hcsnd, mfderiv_srcSphereCoe_apply] at h2
  exact Prod.ext h1.symm h2.symm

theorem contMDiff_hopfAmbientMap :
    ContMDiff 𝕀ₛ 𝓘(ℝ, 𝔼) ∞ (hopfAmbientMap (n := n)) := by
  have h : (hopfAmbientMap (n := n)) =
      fun q => (conjSmulL : ℂ →L[ℝ] 𝔼 →L[ℝ] 𝔼) ((q.2.2 : ℂ)) ((q.2.1 : 𝔼)) :=
    funext hopfAmbientMap_eq_conjSmulL
  rw [h]
  exact (conjSmulL.contMDiff (n := ∞)).comp contMDiff_srcCircleCoe |>.clm_apply
    contMDiff_srcSphereCoe

/-- **Math.** The differential of the ambient quotient map `q ↦ conj(w)·z`, by the product
rule for the bilinear `conjSmulL`: `D(a, u, c) = conj(Dc)·z + conj(w)·Du`. -/
theorem mfderiv_hopfAmbientMap_apply (p : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1))
    (u : TangentSpace 𝕀ₛ p) :
    mfderiv 𝕀ₛ 𝓘(ℝ, 𝔼) (hopfAmbientMap (n := n)) p u
      = (starRingEnd ℂ) ((p.2.2 : ℂ)) • (sphereAmbient p.2.1 u.2.1)
        + (starRingEnd ℂ) (circleAmbient p.2.2 u.2.2) • ((p.2.1 : 𝔼)) := by
  have hbil : IsBoundedBilinearMap ℝ
      (fun y : ℂ × 𝔼 => (conjSmulL : ℂ →L[ℝ] 𝔼 →L[ℝ] 𝔼) y.1 y.2) :=
    (conjSmulL : ℂ →L[ℝ] 𝔼 →L[ℝ] 𝔼).isBoundedBilinearMap
  have hcomp : (hopfAmbientMap (n := n))
      = (fun y : ℂ × 𝔼 => (conjSmulL : ℂ →L[ℝ] 𝔼 →L[ℝ] 𝔼) y.1 y.2)
          ∘ (hopfPairMap (n := n)) := by
    funext q
    rw [hopfAmbientMap_eq_conjSmulL]
    rfl
  have hΨd : MDifferentiableAt 𝓘(ℝ, ℂ × 𝔼) 𝓘(ℝ, 𝔼)
      (fun y : ℂ × 𝔼 => (conjSmulL : ℂ →L[ℝ] 𝔼 →L[ℝ] 𝔼) y.1 y.2) (hopfPairMap p) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact (hbil.hasFDerivAt (hopfPairMap p)).differentiableAt
  have hpd : MDifferentiableAt 𝕀ₛ 𝓘(ℝ, ℂ × 𝔼) (hopfPairMap (n := n)) p :=
    (contMDiff_hopfPairMap p).mdifferentiableAt (by simp)
  have hDΨ : mfderiv 𝓘(ℝ, ℂ × 𝔼) 𝓘(ℝ, 𝔼)
      (fun y : ℂ × 𝔼 => (conjSmulL : ℂ →L[ℝ] 𝔼 →L[ℝ] 𝔼) y.1 y.2) (hopfPairMap p)
      = hbil.deriv (hopfPairMap p) := by
    rw [mfderiv_eq_fderiv]
    exact (hbil.hasFDerivAt (hopfPairMap p)).fderiv
  have s1 := mfderiv_comp_apply (I' := 𝓘(ℝ, ℂ × 𝔼)) (I'' := 𝓘(ℝ, 𝔼)) p hΨd hpd u
  rw [hDΨ, mfderiv_hopfPairMap_apply] at s1
  simp only [hbil.deriv_apply, hopfPairMap, conjSmulL_apply] at s1
  rw [hcomp]
  exact s1

/-! ### The differential of the quotient map, intrinsically -/

/-- **Eng.** `conj(w)·A + conj(s·(i·w))·z = conj(w)·(A − s·(i·z))`: the ambient differential
of the quotient map, rearranged so that the whole `S^{2n+1}`-tangent output is visibly
`conj(w)` applied to a vector of `T_z S^{2n+1}`.  Checked coordinatewise in `ℂ^{n+1}`. -/
theorem conj_smul_add_conj_smul_I_mul (w : ℂ) (s : ℝ) (A z : 𝔼) :
    (starRingEnd ℂ) w • A + (starRingEnd ℂ) (s • (Complex.I * w)) • z
      = (starRingEnd ℂ) w • (A - ((((s : ℝ) : ℂ) * Complex.I) • z)) := by
  have hc : (starRingEnd ℂ) (s • (Complex.I * w))
      = -((starRingEnd ℂ) w * ((((s : ℝ) : ℂ)) * Complex.I)) := by
    rw [Complex.real_smul, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hc, smul_sub, smul_smul, neg_smul, ← sub_eq_add_neg]

theorem contMDiff_hopfSphereQuotientSnd :
    ContMDiff 𝕀ₛ (𝓡 (2 * n + 1)) ∞
      (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
        (hopfSphereQuotientMap q).2) := by
  have hmem : ∀ q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1),
      hopfAmbientMap (n := n) q ∈ sphere (0 : 𝔼) 1 := fun q =>
    mem_sphere_zero_iff_norm.mpr (norm_hopfAmbientMap q)
  have heq : (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
      (hopfSphereQuotientMap q).2)
      = fun q => (⟨hopfAmbientMap q, hmem q⟩ : sphere (0 : 𝔼) 1) := by
    funext q
    exact Subtype.ext (coe_hopfSphereQuotientMap q)
  rw [heq]
  exact contMDiff_hopfAmbientMap.codRestrict_sphere hmem

theorem contMDiff_hopfSphereQuotientMap :
    ContMDiff 𝕀ₛ 𝕀ₜ ∞ (hopfSphereQuotientMap (n := n)) :=
  (contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := (𝓡 (2 * n + 1)).prod (𝓡 1)) (n := ∞)).prodMk
    contMDiff_hopfSphereQuotientSnd

/-- **Math.** The differential of the quotient map, read through the sphere inclusion:
`Dι(DQ(a, u, c)) = conj(w)·(Du − (dθ(c)·i)·z)`, where `dθ(c)` is the circle component.
The subtracted vector is written with the *complex* scalar `(s : ℂ)·i` throughout: on
`EuclideanSpace ℂ (Fin (n+1))` the real-scalar action lives in a `Module ℝ` diamond that
makes Mathlib's `real_inner_smul_left` diverge, so all scalars are kept complex. -/
theorem sphereAmbient_mfderiv_hopfSphereQuotientSnd
    (p : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1)) (u : TangentSpace 𝕀ₛ p) :
    sphereAmbient (hopfSphereQuotientMap p).2
        (mfderiv 𝕀ₛ (𝓡 (2 * n + 1))
          (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
            (hopfSphereQuotientMap q).2) p u)
      = (starRingEnd ℂ) ((p.2.2 : ℂ)) •
          (sphereAmbient p.2.1 u.2.1
            - (((circleAngleForm p.2.2 u.2.2 : ℝ) : ℂ) * Complex.I) • ((p.2.1 : 𝔼))) := by
  have hQd : MDifferentiableAt 𝕀ₛ (𝓡 (2 * n + 1))
      (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => (hopfSphereQuotientMap q).2) p :=
    (contMDiff_hopfSphereQuotientSnd p).mdifferentiableAt (by simp)
  have hcoed : MDifferentiableAt (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼)
      ((↑) : sphere (0 : 𝔼) 1 → 𝔼) (hopfSphereQuotientMap p).2 :=
    (contMDiff_coe_sphere (E := 𝔼) (n := 2 * n + 1) (m := ∞)
      (hopfSphereQuotientMap p).2).mdifferentiableAt (by simp)
  have hcomp : ((↑) : sphere (0 : 𝔼) 1 → 𝔼) ∘
      (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => (hopfSphereQuotientMap q).2)
      = hopfAmbientMap (n := n) := funext coe_hopfSphereQuotientMap
  have h := mfderiv_comp_apply (I' := 𝓡 (2 * n + 1)) (I'' := 𝓘(ℝ, 𝔼)) p hcoed hQd u
  rw [hcomp, mfderiv_hopfAmbientMap_apply, circleAmbient_eq p.2.2 u.2.2,
    conj_smul_add_conj_smul_I_mul] at h
  exact h.symm

/-! ### The Hopf splitting `ds²_{2n+1} = h + g` and the target form -/

/-- **Math.** The Hopf 1-form of `S^{2n+1}`, pulled back to `I × S^{2n+1}`. -/
def hopfAngleFormProd (p : ℝ × sphere (0 : 𝔼) 1) : TangentSpace 𝕀ₜ p →L[ℝ] ℝ :=
  (hopfAngleForm p.2).comp (mfderiv 𝕀ₜ (𝓡 (2 * n + 1)) Prod.snd p)

@[simp]
theorem hopfAngleFormProd_apply (p : ℝ × sphere (0 : 𝔼) 1) (x : TangentSpace 𝕀ₜ p) :
    hopfAngleFormProd p x = hopfAngleForm p.2 x.2 := by
  show hopfAngleForm p.2 (mfderiv 𝕀ₜ (𝓡 (2 * n + 1)) Prod.snd p x) = _
  rw [mfderiv_snd]
  rfl

/-- **Math.** Petersen Example 1.4.12: the Hopf-fibre part `h = (σ¹)² = θ ⊗ θ` of the round
metric of `S^{2n+1}`, as a form on `I × S^{2n+1}`. The complementary part is
`g = ds²_{2n+1} − h`. -/
def hopfFibreForm (p : ℝ × sphere (0 : 𝔼) 1) :
    TangentSpace 𝕀ₜ p →L[ℝ] TangentSpace 𝕀ₜ p →L[ℝ] ℝ :=
  (hopfAngleFormProd p).smulRight (hopfAngleFormProd p)

@[simp]
theorem hopfFibreForm_apply (p : ℝ × sphere (0 : 𝔼) 1) (x y : TangentSpace 𝕀ₜ p) :
    hopfFibreForm p x y = hopfAngleForm p.2 x.2 * hopfAngleForm p.2 y.2 := by
  show (hopfAngleFormProd p x) • (hopfAngleFormProd p) y = _
  simp only [hopfAngleFormProd_apply, smul_eq_mul]

/-- **Math.** Petersen Example 1.4.12: the target form on `I × S^{2n+1}`,
`dt² + ρ²(t)·g + σ²(t)·h`, where `ds²_{2n+1} = h + g` is the Hopf splitting of the round
metric (so `g = ds²_{2n+1} − h`). -/
def hopfQuotientForm (σ ρ : ℝ → ℝ) (p : ℝ × sphere (0 : 𝔼) 1) :
    TangentSpace 𝕀ₜ p →L[ℝ] TangentSpace 𝕀ₜ p →L[ℝ] ℝ :=
  pullbackForm (I := 𝕀ₜ) (innerProductSpaceMetric ℝ) Prod.fst p
    + ((ρ p.1) ^ 2 •
        (pullbackForm (I := 𝕀ₜ) (sphereMetricUnit (n := 2 * n + 1) 𝔼) Prod.snd p
          - hopfFibreForm p)
      + (σ p.1) ^ 2 • hopfFibreForm p)

theorem hopfQuotientForm_apply (σ ρ : ℝ → ℝ) (p : ℝ × sphere (0 : 𝔼) 1)
    (x y : TangentSpace 𝕀ₜ p) :
    hopfQuotientForm σ ρ p x y
      = x.1 * y.1
        + ((ρ p.1) ^ 2 *
            ((inner ℝ (sphereAmbient p.2 x.2) (sphereAmbient p.2 y.2) : ℝ)
              - hopfAngleForm p.2 x.2 * hopfAngleForm p.2 y.2)
          + (σ p.1) ^ 2 * (hopfAngleForm p.2 x.2 * hopfAngleForm p.2 y.2)) := by
  have hfx : mfderiv 𝕀ₜ 𝓘(ℝ, ℝ) Prod.fst p x = x.1 := by rw [mfderiv_fst]; rfl
  have hfy : mfderiv 𝕀ₜ 𝓘(ℝ, ℝ) Prod.fst p y = y.1 := by rw [mfderiv_fst]; rfl
  have hsx : mfderiv 𝕀ₜ (𝓡 (2 * n + 1)) Prod.snd p x = x.2 := by rw [mfderiv_snd]; rfl
  have hsy : mfderiv 𝕀ₜ (𝓡 (2 * n + 1)) Prod.snd p y = y.2 := by rw [mfderiv_snd]; rfl
  show pullbackForm (I := 𝕀ₜ) (innerProductSpaceMetric ℝ) Prod.fst p x y
      + ((ρ p.1) ^ 2 •
          (pullbackForm (I := 𝕀ₜ) (sphereMetricUnit (n := 2 * n + 1) 𝔼) Prod.snd p
            - hopfFibreForm p)
        + (σ p.1) ^ 2 • hopfFibreForm p) x y = _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, pullbackForm_apply,
    hopfFibreForm_apply, hfx, hfy, hsx, hsy, innerProductSpaceMetric_apply,
    sphereMetricUnit_apply]
  have hreal : (inner ℝ (x.1 : ℝ) (y.1 : ℝ) : ℝ) = x.1 * y.1 := by
    rw [real_inner_comm]; rfl
  rw [hreal]

/-! ### The source form -/

theorem hopfSourceForm_apply (ρ φ : ℝ → ℝ)
    (p : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1)) (u v : TangentSpace 𝕀ₛ p) :
    doublyWarpedProductForm (sphereMetricUnit (n := 2 * n + 1) 𝔼)
        (sphereMetricUnit (n := 1) ℂ) ρ φ p u v
      = u.1 * v.1
        + ((ρ p.1) ^ 2 *
            (inner ℝ (sphereAmbient p.2.1 u.2.1) (sphereAmbient p.2.1 v.2.1) : ℝ)
          + (φ p.1) ^ 2 *
            (circleAngleForm p.2.2 u.2.2 * circleAngleForm p.2.2 v.2.2)) := by
  have hfu : mfderiv 𝕀ₛ 𝓘(ℝ, ℝ) Prod.fst p u = u.1 := by rw [mfderiv_fst]; rfl
  have hfv : mfderiv 𝕀ₛ 𝓘(ℝ, ℝ) Prod.fst p v = v.1 := by rw [mfderiv_fst]; rfl
  rw [doublyWarpedProductForm_apply, hfu, hfv,
    mfderiv_proj21_apply (I₁ := 𝓡 (2 * n + 1)) (I₂ := 𝓡 1) p u,
    mfderiv_proj21_apply (I₁ := 𝓡 (2 * n + 1)) (I₂ := 𝓡 1) p v,
    mfderiv_proj22_apply (I₁ := 𝓡 (2 * n + 1)) (I₂ := 𝓡 1) p u,
    mfderiv_proj22_apply (I₁ := 𝓡 (2 * n + 1)) (I₂ := 𝓡 1) p v,
    sphereMetricUnit_apply, sphereMetricUnit_apply, real_inner_circleAmbient,
    innerProductSpaceMetric_apply]
  have hreal : (inner ℝ (u.1 : ℝ) (v.1 : ℝ) : ℝ) = u.1 * v.1 := by
    rw [real_inner_comm]; rfl
  rw [hreal]

/-! ### The kernel of the differential, and the main theorem -/

/-- **Math.** The velocity of the simultaneous circle action at `(z, w)`: the tangent vector
whose ambient components are `(i·z, i·w)`.  It spans `ker DQ`. -/
theorem exists_hopfVerticalVector (p : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1)) :
    ∃ K : TangentSpace 𝕀ₛ p,
      K.1 = 0 ∧ sphereAmbient p.2.1 K.2.1 = Complex.I • (p.2.1 : 𝔼)
        ∧ circleAmbient p.2.2 K.2.2 = Complex.I * (p.2.2 : ℂ) := by
  obtain ⟨uK, huK⟩ := exists_mfderiv_coe_sphere_eq (E := 𝔼) (n := 2 * n + 1) p.2.1
    (real_inner_I_smul_coe_sphere p.2.1)
  obtain ⟨cK, hcK⟩ := exists_mfderiv_coe_sphere_eq (E := ℂ) (n := 1) p.2.2
    (real_inner_self_I_mul (p.2.2 : ℂ))
  exact ⟨(0, uK, cK), rfl, huK, hcK⟩

@[simp] private theorem hopfSphereQuotientMap_fst
    (p : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1)) :
    (hopfSphereQuotientMap (n := n) p).1 = p.1 := rfl

set_option maxHeartbeats 1600000 in
/-- **Math.** Petersen Example 1.4.12 — **the higher-dimensional Hopf fibration**, on the
genuine sphere.  Write the round metric of `S^{2n+1} ⊆ ℂ^{n+1}` as `h + g`, where
`h = θ ⊗ θ` is the square of the Hopf coframe field `θ_z = ⟪·, i·z⟫` dual to the Hopf-fibre
direction and `g = ds²_{2n+1} − h` its orthogonal complement.  On `I × S^{2n+1} × S¹` carry
the doubly warped metric `dt² + ρ²(t) ds²_{2n+1} + φ²(t) dθ²`.  The circle acts
isometrically and freely by *simultaneous* complex scalar multiplication, the orbit space is
`I × S^{2n+1}` via `(t, z, w) ↦ (t, w⁻¹ z)` (`hopfSphereQuotientMap_eq_iff`), and that
quotient map is a Riemannian submersion onto

  `dt² + ρ²(t) g + ((ρφ)²/(ρ² + φ²))(t) · h`.

The `S¹`-and-Hopf-direction part is the three-variable computation of Example 1.4.11
(`hopfSubmersion_horizontal_algebra`); the directions of `S^{2n+1}` orthogonal to the Hopf
fibre are carried along isometrically with their `ρ²(t)` warping.

Stated for *forms* rather than bundled metrics because `ρ, φ` are allowed to vanish (e.g.
`ρ = sin`, `φ = cos` in Example 1.4.14), where the forms are only positive semidefinite. -/
theorem hopfFibrationHigherDimSphere (ρ φ : ℝ → ℝ) :
    IsFormRiemannianSubmersion
      (doublyWarpedProductForm (sphereMetricUnit (n := 2 * n + 1) 𝔼)
        (sphereMetricUnit (n := 1) ℂ) ρ φ)
      (hopfQuotientForm (fun t => ρ t * φ t / Real.sqrt (ρ t ^ 2 + φ t ^ 2)) ρ)
      (hopfSphereQuotientMap (n := n)) := by
  -- Notation for the ambient data at a point `p = (t, z, w)`.
  have hDsplit : ∀ (p : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1)) (x : TangentSpace 𝕀ₛ p),
      mfderiv 𝕀ₛ 𝕀ₜ (hopfSphereQuotientMap (n := n)) p x
        = (x.1, mfderiv 𝕀ₛ (𝓡 (2 * n + 1))
            (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
              (hopfSphereQuotientMap q).2) p x) := by
    intro p x
    have hD := mfderiv_prodMk (I := 𝕀ₛ) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓡 (2 * n + 1))
      (f := fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => q.1)
      (g := fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
        (hopfSphereQuotientMap q).2)
      (x := p) mdifferentiableAt_fst
      ((contMDiff_hopfSphereQuotientSnd p).mdifferentiableAt (by simp))
    have hDeq : mfderiv 𝕀ₛ 𝕀ₜ (hopfSphereQuotientMap (n := n)) p = _ := hD
    rw [hDeq]
    refine Prod.ext ?_ rfl
    show mfderiv 𝕀ₛ 𝓘(ℝ, ℝ)
      (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) => q.1) p x = x.1
    rw [mfderiv_fst]; rfl
  refine ⟨contMDiff_hopfSphereQuotientMap, ?_, ?_⟩
  · -- Surjectivity of `DQ`: lift `(a, v)` at `(t, w⁻¹z)` by `(a, u₀, 0)` with `Dι u₀ = w · Dι v`.
    intro p y
    have hwnorm : ‖((p.2.2 : ℂ))‖ = 1 := norm_coe_unitSphere p.2.2
    have hcwnorm : ‖(starRingEnd ℂ) ((p.2.2 : ℂ))‖ = 1 := by rw [RCLike.norm_conj, hwnorm]
    have hone : (starRingEnd ℂ) ((p.2.2 : ℂ)) * ((p.2.2 : ℂ)) = 1 :=
      conj_mul_self_of_norm_one hwnorm
    have hζamb : (((hopfSphereQuotientMap p).2 : sphere (0 : 𝔼) 1) : 𝔼)
        = (starRingEnd ℂ) ((p.2.2 : ℂ)) • (p.2.1 : 𝔼) := coe_hopfSphereQuotientMap p
    -- `w · Dι(y.2)` is orthogonal to `z`, hence in the range of `Dι` at `z`
    have horth : (inner ℝ ((p.2.1 : 𝔼))
        (((p.2.2 : ℂ)) • (sphereAmbient (hopfSphereQuotientMap p).2 y.2)) : ℝ) = 0 := by
      have h0 : (inner ℝ ((((hopfSphereQuotientMap p).2 : sphere (0 : 𝔼) 1) : 𝔼))
          (sphereAmbient (hopfSphereQuotientMap p).2 y.2) : ℝ) =
          0 := inner_coe_mfderiv_coe_unitSphere _ y.2
      rw [hζamb] at h0
      rw [← real_inner_unit_smul_smul (c := (starRingEnd ℂ) ((p.2.2 : ℂ))) hcwnorm,
        smul_smul, hone, one_smul]
      exact h0
    obtain ⟨u₀, hu₀⟩ := exists_mfderiv_coe_sphere_eq (E := 𝔼) (n := 2 * n + 1) p.2.1 horth
    refine ⟨(y.1, u₀, 0), ?_⟩
    rw [hDsplit p (show TangentSpace 𝕀ₛ p from (y.1, u₀, 0))]
    refine Prod.ext rfl ?_
    apply mfderiv_coe_sphere_injective (n := 2 * n + 1) (hopfSphereQuotientMap p).2
    show sphereAmbient (hopfSphereQuotientMap p).2
        (mfderiv 𝕀ₛ (𝓡 (2 * n + 1))
          (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
            (hopfSphereQuotientMap q).2) p (show TangentSpace 𝕀ₛ p from (y.1, u₀, 0)))
      = sphereAmbient (hopfSphereQuotientMap p).2 y.2
    rw [sphereAmbient_mfderiv_hopfSphereQuotientSnd p
      (show TangentSpace 𝕀ₛ p from (y.1, u₀, 0))]
    have hcf0 : circleAngleForm p.2.2
        (show TangentSpace (𝓡 1) p.2.2 from (0 : TangentSpace (𝓡 1) p.2.2)) = 0 := by
      simp [circleAngleForm]
    show (starRingEnd ℂ) ((p.2.2 : ℂ)) •
        (sphereAmbient p.2.1 u₀
          - (((circleAngleForm p.2.2
                (show TangentSpace (𝓡 1) p.2.2 from (0 : TangentSpace (𝓡 1) p.2.2)) : ℝ) : ℂ)
              * Complex.I) • ((p.2.1 : 𝔼)))
      = sphereAmbient (hopfSphereQuotientMap p).2 y.2
    have hu₀' : sphereAmbient p.2.1 u₀
        = ((p.2.2 : ℂ)) • (sphereAmbient (hopfSphereQuotientMap p).2 y.2) := hu₀
    rw [hcf0]
    simp only [Complex.ofReal_zero, zero_mul, zero_smul, sub_zero]
    rw [hu₀', smul_smul, hone, one_smul]
  · -- The metric identity on vectors orthogonal to `ker DQ`.
    intro p u v hu _hv
    have hwnorm : ‖((p.2.2 : ℂ))‖ = 1 := norm_coe_unitSphere p.2.2
    have hcwnorm : ‖(starRingEnd ℂ) ((p.2.2 : ℂ))‖ = 1 := by rw [RCLike.norm_conj, hwnorm]
    have hznorm : ‖((p.2.1 : 𝔼))‖ = 1 := norm_coe_unitSphere p.2.1
    obtain ⟨K, hK1, hK2, hK3⟩ := exists_hopfVerticalVector p
    have hcfK : circleAngleForm p.2.2 K.2.2 = 1 := by
      show (inner ℝ (Complex.I * (p.2.2 : ℂ)) (circleAmbient p.2.2 K.2.2) : ℝ) = 1
      rw [hK3, real_inner_self_eq_norm_sq, norm_I_mul_coe_circle, one_pow]
    -- `K` spans `ker DQ`
    have hKker : mfderiv 𝕀ₛ 𝕀ₜ (hopfSphereQuotientMap (n := n)) p K = 0 := by
      rw [hDsplit p K]
      refine Prod.ext hK1 ?_
      show mfderiv 𝕀ₛ (𝓡 (2 * n + 1))
        (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
          (hopfSphereQuotientMap q).2) p K = 0
      apply mfderiv_coe_sphere_injective (n := 2 * n + 1) (hopfSphereQuotientMap p).2
      have hzero : sphereAmbient (hopfSphereQuotientMap p).2
          (mfderiv 𝕀ₛ (𝓡 (2 * n + 1))
            (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
              (hopfSphereQuotientMap q).2) p K) = 0 := by
        rw [sphereAmbient_mfderiv_hopfSphereQuotientSnd p K, hK2, hcfK,
          Complex.ofReal_one, one_mul, sub_self, smul_zero]
      show sphereAmbient (hopfSphereQuotientMap p).2
          (mfderiv 𝕀ₛ (𝓡 (2 * n + 1))
            (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
              (hopfSphereQuotientMap q).2) p K)
        = sphereAmbient (hopfSphereQuotientMap p).2 0
      have hz0 : sphereAmbient (hopfSphereQuotientMap p).2
          (0 : TangentSpace (𝓡 (2 * n + 1)) (hopfSphereQuotientMap p).2) = 0 := map_zero _
      rw [hzero, hz0]
    -- horizontality of `u` against `K`
    have hu' : (ρ p.1) ^ 2 * hopfAngleForm p.2.1 u.2.1
        + (φ p.1) ^ 2 * circleAngleForm p.2.2 u.2.2 = 0 := by
      have h := hu K hKker
      rw [hopfSourceForm_apply] at h
      have hinnK : (inner ℝ (sphereAmbient p.2.1 u.2.1) (sphereAmbient p.2.1 K.2.1) : ℝ)
          = hopfAngleForm p.2.1 u.2.1 := by
        rw [hK2]
        show _ = (inner ℝ (Complex.I • (p.2.1 : 𝔼)) (sphereAmbient p.2.1 u.2.1) : ℝ)
        exact real_inner_comm _ _
      rw [hK1, hcfK, hinnK, mul_one, mul_zero, zero_add] at h
      exact h
    set β := hopfAngleForm p.2.1 u.2.1 with hβ
    set s := circleAngleForm p.2.2 u.2.2 with hs
    set β' := hopfAngleForm p.2.1 v.2.1 with hβ'
    set s' := circleAngleForm p.2.2 v.2.2 with hs'
    -- the Hopf 1-form of the target, on the image of a tangent vector
    have hθ : ∀ x : TangentSpace 𝕀ₛ p,
        hopfAngleForm (hopfSphereQuotientMap p).2
            (mfderiv 𝕀ₛ (𝓡 (2 * n + 1))
              (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
                (hopfSphereQuotientMap q).2) p x)
          = hopfAngleForm p.2.1 x.2.1 - circleAngleForm p.2.2 x.2.2 := by
      intro x
      show (inner ℝ (Complex.I • ((((hopfSphereQuotientMap p).2 : sphere (0 : 𝔼) 1)) : 𝔼))
        (sphereAmbient (hopfSphereQuotientMap p).2
          (mfderiv 𝕀ₛ (𝓡 (2 * n + 1))
            (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
              (hopfSphereQuotientMap q).2) p x)) : ℝ) = _
      rw [sphereAmbient_mfderiv_hopfSphereQuotientSnd p x, coe_hopfSphereQuotientMap p]
      show (inner ℝ (Complex.I • ((starRingEnd ℂ) ((p.2.2 : ℂ)) • (p.2.1 : 𝔼)))
        ((starRingEnd ℂ) ((p.2.2 : ℂ)) •
          (sphereAmbient p.2.1 x.2.1
            - (((circleAngleForm p.2.2 x.2.2 : ℝ) : ℂ) * Complex.I) • ((p.2.1 : 𝔼)))) : ℝ) = _
      rw [smul_smul, mul_comm Complex.I ((starRingEnd ℂ) ((p.2.2 : ℂ))), ← smul_smul,
        real_inner_unit_smul_smul hcwnorm, inner_sub_right,
        real_inner_I_smul_ofReal_I_smul _ hznorm]
      rfl
    -- the round part of the target, on the images of `u` and `v`
    have hround : (inner ℝ
        (sphereAmbient (hopfSphereQuotientMap p).2
          (mfderiv 𝕀ₛ (𝓡 (2 * n + 1))
            (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
              (hopfSphereQuotientMap q).2) p u))
        (sphereAmbient (hopfSphereQuotientMap p).2
          (mfderiv 𝕀ₛ (𝓡 (2 * n + 1))
            (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
              (hopfSphereQuotientMap q).2) p v)) : ℝ)
        = (inner ℝ (sphereAmbient p.2.1 u.2.1) (sphereAmbient p.2.1 v.2.1) : ℝ)
          - s' * β - s * β' + s * s' := by
      rw [sphereAmbient_mfderiv_hopfSphereQuotientSnd p u,
        sphereAmbient_mfderiv_hopfSphereQuotientSnd p v,
        real_inner_unit_smul_smul hcwnorm, inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_ofReal_I_smul_right, real_inner_ofReal_I_smul_left,
        real_inner_ofReal_I_smul_left, real_inner_I_smul_ofReal_I_smul _ hznorm]
      show (inner ℝ (sphereAmbient p.2.1 u.2.1) (sphereAmbient p.2.1 v.2.1) : ℝ)
          - s' * β - (s * β' - s * s') = _
      ring
    have hD1 : ∀ x : TangentSpace 𝕀ₛ p,
        (mfderiv 𝕀ₛ 𝕀ₜ (hopfSphereQuotientMap (n := n)) p x).1 = x.1 := fun x => by
      rw [hDsplit p x]
    have hD2 : ∀ x : TangentSpace 𝕀ₛ p,
        (mfderiv 𝕀ₛ 𝕀ₜ (hopfSphereQuotientMap (n := n)) p x).2
          = mfderiv 𝕀ₛ (𝓡 (2 * n + 1))
              (fun q : ℝ × (sphere (0 : 𝔼) 1 × sphere (0 : ℂ) 1) =>
                (hopfSphereQuotientMap q).2) p x := fun x => by
      rw [hDsplit p x]
    have hp1 : (hopfSphereQuotientMap (n := n) p).1 = p.1 := rfl
    rw [hopfSourceForm_apply, hopfQuotientForm_apply, hD1 u, hD1 v, hD2 u, hD2 v,
      hθ u, hθ v, hround, ← hβ, ← hβ', ← hs, ← hs']
    simp only [hp1]
    linear_combination hopfSubmersion_horizontal_algebra (ρ := ρ p.1) (φ := φ p.1) β' s' hu'

/-- **Math.** Petersen Example 1.4.13 (the `SU(2)` coframe case, `n = 1`): the case
`S^{2n+1} = S³ ⊆ ℂ²` of `hopfFibrationHigherDimSphere`.  Here the Hopf splitting of the
round metric of `S³` is `h = (σ¹)²` — the square of the coframe field dual to the Hopf-fibre
direction `i·z` — and `g = (σ²)² + (σ³)²` its orthogonal complement, in the left-invariant
`SU(2) ≅ S³` coframe.  The simultaneous rotation descends to the Riemannian submersion of
`I × S³ × S¹` with `dt² + ρ²(t)((σ¹)² + (σ²)² + (σ³)²) + φ²(t) dθ²` onto `I × S³` with
`dt² + ρ²(t)((σ²)² + (σ³)²) + ((ρφ)²/(ρ² + φ²))(t)(σ¹)²`. -/
theorem hopfFibrationSUTwoCoframeSphere (ρ φ : ℝ → ℝ) :
    IsFormRiemannianSubmersion
      (doublyWarpedProductForm (sphereMetricUnit (n := 3) (EuclideanSpace ℂ (Fin 2)))
        (sphereMetricUnit (n := 1) ℂ) ρ φ)
      (hopfQuotientForm (n := 1) (fun t => ρ t * φ t / Real.sqrt (ρ t ^ 2 + φ t ^ 2)) ρ)
      (hopfSphereQuotientMap (n := 1)) :=
  hopfFibrationHigherDimSphere (n := 1) ρ φ

/-- **Math.** Petersen Example 1.4.14 (the generalized Hopf fibration): the case `ρ = sin`,
`φ = cos` of `hopfFibrationHigherDimSphere`.  Since `(sin·cos)²/(sin² + cos²) = sin²cos²`,
the target form is `dt² + sin²(t) g + sin²(t)cos²(t) h = dt² + sin²(t)(g + cos²(t) h)` —
Petersen's form of the Fubini–Study metric on `ℂP^{n+1}`, obtained here as a form on the
quotient `I × S^{2n+1}` of `I × S^{2n+1} × S¹` (which for `t ∈ (0, π/2)` is the doubly warped
description of `S^{2n+3}`, cf. `sphereAsDoublyWarpedProduct`). -/
theorem generalizedHopfFibrationSphere :
    IsFormRiemannianSubmersion
      (doublyWarpedProductForm (sphereMetricUnit (n := 2 * n + 1) 𝔼)
        (sphereMetricUnit (n := 1) ℂ) Real.sin Real.cos)
      (hopfQuotientForm (n := n) (fun t => Real.sin t * Real.cos t) Real.sin)
      (hopfSphereQuotientMap (n := n)) := by
  have hfun : (fun t => Real.sin t * Real.cos t /
      Real.sqrt (Real.sin t ^ 2 + Real.cos t ^ 2)) =
      fun t => Real.sin t * Real.cos t := by
    funext t
    rw [Real.sin_sq_add_cos_sq, Real.sqrt_one, div_one]
  simpa only [hfun] using hopfFibrationHigherDimSphere (n := n) Real.sin Real.cos

end HopfQuotient

end PetersenLib
