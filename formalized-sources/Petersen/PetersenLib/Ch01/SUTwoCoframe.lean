import PetersenLib.Ch01.HopfSphereSubmersion

/-!
# Petersen Ch. 1, Example 1.4.13 — the `SU(2)` coframe of `S³` and the Hopf splitting

Petersen's Example 1.4.13 specializes the Hopf construction of Example 1.4.12 to `n = 1`,
where `S^{2n+1} = S³ ≅ SU(2)` and the round metric is written in the left-invariant coframe
`σ¹, σ², σ³` dual to the left-invariant frame `i·z, j·z, k·z`:

  `ds²_{S³} = (σ¹)² + (σ²)² + (σ³)²`,   `h = (σ¹)²`,   `g = (σ²)² + (σ³)²`.

The Riemannian-submersion half of the example is `PetersenLib.hopfFibrationSUTwoCoframeSphere`
(`PetersenLib.Ch01.HopfSphereSubmersion`).  This file supplies the missing *coframe
identification*, in the same ambient model `𝔼 = EuclideanSpace ℂ (Fin 2)`,
`S³ = sphere (0 : 𝔼) 1`.

The data:

* `suTwoFieldE z` — the left-invariant frame of `SU(2) = S³` in ambient coordinates:
  `X₁ z = i·z`, `X₂ z = (-conj z₁, conj z₀)` (`= j·z`), `X₃ z = i·X₂ z` (`= k·z`).
* `suTwoTForm z a = z₀ a₁ − z₁ a₀` — the complex symplectic pairing; together with the
  complex inner product `⟪z, a⟫_ℂ` it carries the whole coframe: the four real functionals
  `⟪z, ·⟫_ℝ, σ¹, σ², σ³` are `Re⟪z, ·⟫_ℂ, Im⟪z, ·⟫_ℂ, Re T(·), Im T(·)`.
* `suTwo_parseval_complex` — the key algebraic identity of `ℂ²`,
  `conj⟪z,a⟫·⟪z,b⟫ + conj T(a)·T(b) = ⟪z,z⟫·⟪a,b⟫`, whose real part is full Parseval for
  the real orthonormal basis `{z, i·z, j·z, k·z}` of `ℂ² ≅ ℝ⁴` at a unit `z`.
* `suTwoCoframe z i` — the dual coframe `σ^{i+1}` on `T_z S³`; `σ¹` is exactly the Hopf
  1-form `hopfAngleForm`.

Main results:

* `real_inner_eq_sum_suTwoFieldE` — Parseval on `ℝ⁴`.
* `sphereMetricUnit_eq_sum_suTwoCoframe` — `ds²_{S³} = (σ¹)² + (σ²)² + (σ³)²`.
* `suTwoCoframe_zero_eq_hopfAngleForm`, `hopfFibreForm_eq_suTwoCoframe_sq` — `h = (σ¹)²`.
* `hopfComplement_eq_suTwoCoframe` — `g = ds²_{S³} − h = (σ²)² + (σ³)²`.
* `hopfQuotientForm_eq_suTwoCoframe` — the Example 1.4.12 target form of the submersion,
  written in the coframe: `dt² + ρ²(t)((σ²)² + (σ³)²) + σ²(t)(σ¹)²`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Example 1.4.13.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Metric Module
open scoped ContDiff Manifold Topology RealInnerProductSpace

namespace PetersenLib

section SUTwoCoframe

/-- Local shorthand for the ambient space `ℂ²` of `S³`. -/
local notation "𝔼" => EuclideanSpace ℂ (Fin 2)

/-! ## The complex inner product and the symplectic pairing of `ℂ²` -/

/-- **Eng.** The complex inner product of `ℂ²` in coordinates:
`⟪x, y⟫_ℂ = conj(x₀)·y₀ + conj(x₁)·y₁`. -/
theorem inner_euclideanSpace_two (x y : 𝔼) :
    (inner ℂ x y : ℂ)
      = (starRingEnd ℂ) (x 0) * y 0 + (starRingEnd ℂ) (x 1) * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, mul_comm]

/-- **Math.** The complex *symplectic* pairing of `ℂ²`, `T_z(a) = z₀ a₁ − z₁ a₀`.  It is the
complex determinant of the pair `(z, a)`, and it is the second half of the `SU(2)` coframe:
`⟪j·z, a⟫_ℂ = T_z(a)` (`inner_suTwoFieldE_one`). -/
def suTwoTForm (z a : 𝔼) : ℂ := z 0 * a 1 - z 1 * a 0

theorem suTwoTForm_apply (z a : 𝔼) : suTwoTForm z a = z 0 * a 1 - z 1 * a 0 := rfl

/-- **Math.** `T_z(z) = 0`: the symplectic pairing is alternating. -/
@[simp]
theorem suTwoTForm_self (z : 𝔼) : suTwoTForm z z = 0 := by
  rw [suTwoTForm_apply]
  ring

/-! ## The left-invariant frame of `SU(2) = S³` in ambient coordinates -/

/-- **Math.** Petersen Example 1.4.13: the left-invariant frame of `SU(2) ≅ S³ ⊆ ℂ²`, in
ambient coordinates.  Under the identification `ℂ² ≅ ℍ`, `z = z₀ + z₁ j`, the three fields
are right multiplication by the imaginary quaternions:
`X₁ z = i·z`, `X₂ z = j·z = (-conj z₁, conj z₀)`, `X₃ z = k·z = i·(j·z)`.
At a unit `z` they form a real orthonormal basis of `T_z S³`
(`real_inner_suTwoFieldE_suTwoFieldE`, `real_inner_coe_suTwoFieldE`); the dual coframe is
Petersen's `σ¹, σ², σ³` (`suTwoCoframe`). -/
def suTwoFieldE (z : 𝔼) : Fin 3 → 𝔼 :=
  ![Complex.I • z,
    !₂[-(starRingEnd ℂ) (z 1), (starRingEnd ℂ) (z 0)],
    Complex.I • !₂[-(starRingEnd ℂ) (z 1), (starRingEnd ℂ) (z 0)]]

/-- **Math.** `X₁ z = i·z`, the Hopf (vertical) field. -/
@[simp]
theorem suTwoFieldE_zero (z : 𝔼) : suTwoFieldE z 0 = Complex.I • z := rfl

/-- **Math.** `X₂ z = j·z = (-conj z₁, conj z₀)`. -/
@[simp]
theorem suTwoFieldE_one (z : 𝔼) :
    suTwoFieldE z 1 = !₂[-(starRingEnd ℂ) (z 1), (starRingEnd ℂ) (z 0)] := rfl

/-- **Math.** `X₃ z = k·z = i·(j·z)`. -/
@[simp]
theorem suTwoFieldE_two (z : 𝔼) : suTwoFieldE z 2 = Complex.I • suTwoFieldE z 1 := rfl

/-- **Eng.** The first coordinate of `X₂ z`. -/
theorem suTwoFieldE_one_apply_zero (z : 𝔼) :
    suTwoFieldE z 1 0 = -(starRingEnd ℂ) (z 1) := rfl

/-- **Eng.** The second coordinate of `X₂ z`. -/
theorem suTwoFieldE_one_apply_one (z : 𝔼) :
    suTwoFieldE z 1 1 = (starRingEnd ℂ) (z 0) := rfl

/-! ## The complex form of the coframe -/

/-- **Math.** `⟪i·z, a⟫_ℂ = conj(i)·⟪z, a⟫_ℂ = −i·⟪z, a⟫_ℂ`. -/
theorem inner_suTwoFieldE_zero (z a : 𝔼) :
    (inner ℂ (suTwoFieldE z 0) a : ℂ) = -Complex.I * inner ℂ z a := by
  rw [suTwoFieldE_zero, inner_smul_left, Complex.conj_I]

/-- **Math.** `⟪j·z, a⟫_ℂ = −z₁ a₀ + z₀ a₁ = T_z(a)`: the second frame field pairs with `a`
through the symplectic form. -/
theorem inner_suTwoFieldE_one (z a : 𝔼) :
    (inner ℂ (suTwoFieldE z 1) a : ℂ) = suTwoTForm z a := by
  rw [inner_euclideanSpace_two, suTwoFieldE_one_apply_zero, suTwoFieldE_one_apply_one,
    suTwoTForm_apply]
  simp only [map_neg, Complex.conj_conj]
  ring

/-- **Math.** `⟪k·z, a⟫_ℂ = conj(i)·T_z(a) = −i·T_z(a)`. -/
theorem inner_suTwoFieldE_two (z a : 𝔼) :
    (inner ℂ (suTwoFieldE z 2) a : ℂ) = -Complex.I * suTwoTForm z a := by
  rw [suTwoFieldE_two, inner_smul_left, Complex.conj_I, inner_suTwoFieldE_one]

/-! ## The key algebraic identity of `ℂ²` -/

/-- **Math.** The key algebraic identity behind Example 1.4.13: on `ℂ²`,
`conj⟪z, a⟫·⟪z, b⟫ + conj T_z(a)·T_z(b) = ⟪z, z⟫·⟪a, b⟫`.
Expanding both sides in coordinates, all cross terms cancel identically.  Its real part is
full Parseval for the real orthonormal basis `{z, i·z, j·z, k·z}` of `ℂ² ≅ ℝ⁴` at a unit
`z` (`real_inner_eq_sum_suTwoFieldE`); this is what makes `ds²_{S³} = (σ¹)² + (σ²)² + (σ³)²`
true. -/
theorem suTwo_parseval_complex (z a b : 𝔼) :
    (starRingEnd ℂ) (inner ℂ z a) * (inner ℂ z b)
        + (starRingEnd ℂ) (suTwoTForm z a) * suTwoTForm z b
      = (inner ℂ z z) * (inner ℂ a b) := by
  simp only [inner_euclideanSpace_two, suTwoTForm_apply, map_add, map_sub, map_mul,
    Complex.conj_conj]
  ring

/-! ## The four real functionals -/

/-- **Math.** `⟪z, a⟫_ℝ = Re⟪z, a⟫_ℂ` (the radial functional). -/
theorem real_inner_eq_re_inner_two (z a : 𝔼) :
    (inner ℝ z a : ℝ) = Complex.re (inner ℂ z a) :=
  real_inner_eq_re_inner_euclideanSpace z a

/-- **Math.** `σ¹`: `⟪i·z, a⟫_ℝ = Re(−i·⟪z, a⟫_ℂ) = Im⟪z, a⟫_ℂ`. -/
theorem real_inner_suTwoFieldE_zero (z a : 𝔼) :
    (inner ℝ (suTwoFieldE z 0) a : ℝ) = Complex.im (inner ℂ z a) := by
  rw [real_inner_eq_re_inner_euclideanSpace, inner_suTwoFieldE_zero]
  simp [Complex.mul_re]

/-- **Math.** `σ²`: `⟪j·z, a⟫_ℝ = Re T_z(a)`. -/
theorem real_inner_suTwoFieldE_one (z a : 𝔼) :
    (inner ℝ (suTwoFieldE z 1) a : ℝ) = Complex.re (suTwoTForm z a) := by
  rw [real_inner_eq_re_inner_euclideanSpace, inner_suTwoFieldE_one]

/-- **Math.** `σ³`: `⟪k·z, a⟫_ℝ = Re(−i·T_z(a)) = Im T_z(a)`. -/
theorem real_inner_suTwoFieldE_two (z a : 𝔼) :
    (inner ℝ (suTwoFieldE z 2) a : ℝ) = Complex.im (suTwoTForm z a) := by
  rw [real_inner_eq_re_inner_euclideanSpace, inner_suTwoFieldE_two]
  simp [Complex.mul_re]

/-! ## Parseval on `ℂ² ≅ ℝ⁴` -/

/-- **Eng.** `⟪z, z⟫_ℂ = ‖z‖²` as a complex number. -/
theorem inner_self_eq_normSq (z : 𝔼) : (inner ℂ z z : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Math.** **Parseval** for the real basis `{z, i·z, j·z, k·z}` of `ℂ² ≅ ℝ⁴`: for all
`a, b`,
`⟪z,a⟫⟪z,b⟫ + ⟪i·z,a⟫⟪i·z,b⟫ + ⟪j·z,a⟫⟪j·z,b⟫ + ⟪k·z,a⟫⟪k·z,b⟫ = ‖z‖²·⟪a,b⟫`
(all real inner products).  This is the real part of `suTwo_parseval_complex`, using
`Re(conj(w)·w') = Re w · Re w' + Im w · Im w'`.  At a unit `z` the four vectors are a real
orthonormal basis, and this is the completeness relation. -/
theorem real_inner_eq_sum_suTwoFieldE (z a b : 𝔼) :
    (inner ℝ z a : ℝ) * (inner ℝ z b : ℝ)
        + (inner ℝ (suTwoFieldE z 0) a : ℝ) * (inner ℝ (suTwoFieldE z 0) b : ℝ)
        + (inner ℝ (suTwoFieldE z 1) a : ℝ) * (inner ℝ (suTwoFieldE z 1) b : ℝ)
        + (inner ℝ (suTwoFieldE z 2) a : ℝ) * (inner ℝ (suTwoFieldE z 2) b : ℝ)
      = ‖z‖ ^ 2 * (inner ℝ a b : ℝ) := by
  have key := suTwo_parseval_complex z a b
  rw [inner_self_eq_normSq] at key
  have hre := congrArg Complex.re key
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im] at hre
  rw [real_inner_eq_re_inner_two z a, real_inner_eq_re_inner_two z b,
    real_inner_suTwoFieldE_zero, real_inner_suTwoFieldE_zero,
    real_inner_suTwoFieldE_one, real_inner_suTwoFieldE_one,
    real_inner_suTwoFieldE_two, real_inner_suTwoFieldE_two,
    real_inner_eq_re_inner_euclideanSpace a b]
  linear_combination hre

/-! ## Orthonormality of the frame -/

/-- **Eng.** `⟪z, j·z⟫_ℂ = 0`: the second frame field is *complex* orthogonal to `z`. -/
theorem inner_coe_suTwoFieldE_one (z : 𝔼) : (inner ℂ z (suTwoFieldE z 1) : ℂ) = 0 := by
  rw [inner_euclideanSpace_two, suTwoFieldE_one_apply_zero, suTwoFieldE_one_apply_one]
  ring

/-- **Eng.** `T_z(i·z) = 0`. -/
theorem suTwoTForm_suTwoFieldE_zero (z : 𝔼) : suTwoTForm z (suTwoFieldE z 0) = 0 := by
  have h0 : suTwoFieldE z 0 0 = Complex.I * z 0 := rfl
  have h1 : suTwoFieldE z 0 1 = Complex.I * z 1 := rfl
  rw [suTwoTForm_apply, h0, h1]
  ring

/-- **Eng.** `T_z(j·z) = ⟪z, z⟫_ℂ = ‖z‖²`. -/
theorem suTwoTForm_suTwoFieldE_one (z : 𝔼) :
    suTwoTForm z (suTwoFieldE z 1) = inner ℂ z z := by
  rw [suTwoTForm_apply, suTwoFieldE_one_apply_zero, suTwoFieldE_one_apply_one,
    inner_euclideanSpace_two]
  ring

/-- **Math.** Each frame field is real-orthogonal to the position vector `z`, hence tangent
to the sphere: `⟪z, X i z⟫_ℝ = 0`. -/
theorem real_inner_coe_suTwoFieldE (z : 𝔼) (i : Fin 3) :
    (inner ℝ z (suTwoFieldE z i) : ℝ) = 0 := by
  have hzz : Complex.im (inner ℂ z z : ℂ) = 0 := by
    rw [inner_self_eq_normSq]
    exact Complex.ofReal_im _
  have hi : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rw [real_inner_comm]
  rcases hi i with rfl | rfl | rfl
  · rw [real_inner_suTwoFieldE_zero, hzz]
  · rw [real_inner_suTwoFieldE_one, suTwoTForm_self]
    simp
  · rw [real_inner_suTwoFieldE_two, suTwoTForm_self]
    simp

/-- **Math.** On the unit sphere, `X₁ z = i·z`, `X₂ z = j·z`, `X₃ z = k·z` are a real
*orthonormal* triple: `⟪X i z, X j z⟫_ℝ = δ_{ij}`.  Together with
`real_inner_coe_suTwoFieldE` this says `{z, i·z, j·z, k·z}` is a real orthonormal basis of
`ℂ² ≅ ℝ⁴`, i.e. the frame is orthonormal in `T_z S³`. -/
theorem real_inner_suTwoFieldE_suTwoFieldE {z : 𝔼} (hz : ‖z‖ = 1) (i j : Fin 3) :
    (inner ℝ (suTwoFieldE z i) (suTwoFieldE z j) : ℝ) = if i = j then 1 else 0 := by
  have hzz : (inner ℂ z z : ℂ) = 1 := by
    rw [inner_self_eq_normSq, hz]
    norm_num
  have hS0 : (inner ℂ z (suTwoFieldE z 0) : ℂ) = Complex.I := by
    rw [suTwoFieldE_zero, inner_smul_right, hzz, mul_one]
  have hS1 : (inner ℂ z (suTwoFieldE z 1) : ℂ) = 0 := inner_coe_suTwoFieldE_one z
  have hS2 : (inner ℂ z (suTwoFieldE z 2) : ℂ) = 0 := by
    rw [suTwoFieldE_two, inner_smul_right, hS1, mul_zero]
  have hT0 : suTwoTForm z (suTwoFieldE z 0) = 0 := suTwoTForm_suTwoFieldE_zero z
  have hT1 : suTwoTForm z (suTwoFieldE z 1) = 1 := by
    rw [suTwoTForm_suTwoFieldE_one, hzz]
  have hT2 : suTwoTForm z (suTwoFieldE z 2) = Complex.I := by
    have h0 : suTwoFieldE z 2 0 = Complex.I * suTwoFieldE z 1 0 := rfl
    have h1 : suTwoFieldE z 2 1 = Complex.I * suTwoFieldE z 1 1 := rfl
    have : suTwoTForm z (suTwoFieldE z 2) = Complex.I * suTwoTForm z (suTwoFieldE z 1) := by
      rw [suTwoTForm_apply, suTwoTForm_apply, h0, h1]
      ring
    rw [this, hT1, mul_one]
  have hi : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rcases hi i with rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl <;>
    simp only [real_inner_suTwoFieldE_zero, real_inner_suTwoFieldE_one,
      real_inner_suTwoFieldE_two, hS0, hS1, hS2, hT0, hT1, hT2] <;> norm_num <;> decide

/-! ## The coframe `σ¹, σ², σ³` on `T S³` -/

/-- **Math.** Petersen Example 1.4.13: the left-invariant **coframe** `σ¹, σ², σ³` of
`SU(2) ≅ S³`, dual to the frame `i·z, j·z, k·z`: `σ^{i+1}_z(u) = ⟪X i z, Dι(u)⟫_ℝ`, where
`ι : S³ ↪ ℂ²`.  The first one is the Hopf 1-form `hopfAngleForm`
(`suTwoCoframe_zero_eq_hopfAngleForm`). -/
def suTwoCoframe (z : sphere (0 : 𝔼) 1) (i : Fin 3) : TangentSpace (𝓡 3) z →L[ℝ] ℝ :=
  (innerSL ℝ (suTwoFieldE (z : 𝔼) i)).comp
    (mfderiv (𝓡 3) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) z)

@[simp]
theorem suTwoCoframe_apply (z : sphere (0 : 𝔼) 1) (i : Fin 3)
    (u : TangentSpace (𝓡 3) z) :
    suTwoCoframe z i u
      = (inner ℝ (suTwoFieldE (z : 𝔼) i)
          (mfderiv (𝓡 3) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) z u) : ℝ) := rfl

/-- **Math.** Petersen Example 1.4.13: `σ¹` *is* the Hopf 1-form of Example 1.4.12 — both
are `u ↦ ⟪i·z, Dι(u)⟫`. -/
theorem suTwoCoframe_zero_eq_hopfAngleForm (z : sphere (0 : 𝔼) 1)
    (u : TangentSpace (𝓡 3) z) :
    suTwoCoframe z 0 u = hopfAngleForm (n := 1) z u := rfl

/-! ## The round metric of `S³` in the coframe -/

/-- **Math.** Petersen Example 1.4.13: the round metric of `S³` in the left-invariant
`SU(2)` coframe,
`ds²_{S³} = (σ¹)² + (σ²)² + (σ³)²`.
Indeed `ds²_{S³}(u, v) = ⟪Dι(u), Dι(v)⟫`, and Parseval
(`real_inner_eq_sum_suTwoFieldE`) at the unit vector `z` expands this in the orthonormal
basis `{z, i·z, j·z, k·z}`; the radial term `⟪z, Dι(u)⟫⟪z, Dι(v)⟫` vanishes because tangent
vectors of the sphere are orthogonal to the base point. -/
theorem sphereMetricUnit_eq_sum_suTwoCoframe (z : sphere (0 : 𝔼) 1)
    (u v : TangentSpace (𝓡 3) z) :
    (sphereMetricUnit (n := 3) 𝔼).metricInner z u v
      = suTwoCoframe z 0 u * suTwoCoframe z 0 v
        + suTwoCoframe z 1 u * suTwoCoframe z 1 v
        + suTwoCoframe z 2 u * suTwoCoframe z 2 v := by
  set a : 𝔼 := mfderiv (𝓡 3) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) z u with ha
  set b : 𝔼 := mfderiv (𝓡 3) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) z v with hb
  have hza : (inner ℝ (z : 𝔼) a : ℝ) = 0 := inner_coe_mfderiv_coe_unitSphere z u
  have hzb : (inner ℝ (z : 𝔼) b : ℝ) = 0 := inner_coe_mfderiv_coe_unitSphere z v
  have hnorm : ‖(z : 𝔼)‖ = 1 := norm_coe_unitSphere z
  have key := real_inner_eq_sum_suTwoFieldE (z : 𝔼) a b
  rw [hza, hzb, hnorm] at key
  rw [sphereMetricUnit_apply]
  show (inner ℝ a b : ℝ) = _
  simp only [suTwoCoframe_apply, ← ha, ← hb]
  linear_combination -key

/-! ## The Hopf splitting `ds²_{S³} = h + g` in the coframe -/

/-- **Math.** Petersen Example 1.4.13: the complementary form `g = ds²_{S³} − h` of the Hopf
splitting is `(σ²)² + (σ³)²`, since `h = (σ¹)²` and
`ds²_{S³} = (σ¹)² + (σ²)² + (σ³)²`. -/
theorem hopfComplement_eq_suTwoCoframe (z : sphere (0 : 𝔼) 1)
    (u v : TangentSpace (𝓡 3) z) :
    (sphereMetricUnit (n := 3) 𝔼).metricInner z u v
        - hopfAngleForm (n := 1) z u * hopfAngleForm (n := 1) z v
      = suTwoCoframe z 1 u * suTwoCoframe z 1 v
        + suTwoCoframe z 2 u * suTwoCoframe z 2 v := by
  rw [sphereMetricUnit_eq_sum_suTwoCoframe z u v,
    ← suTwoCoframe_zero_eq_hopfAngleForm z u, ← suTwoCoframe_zero_eq_hopfAngleForm z v]
  ring

/-- **Math.** Petersen Example 1.4.13: the Hopf-fibre form `h` of Example 1.4.12, as a form
on `ℝ × S³`, is the square of the first coframe field: `h = (σ¹)²`. -/
theorem hopfFibreForm_eq_suTwoCoframe_sq (p : ℝ × sphere (0 : 𝔼) 1)
    (x y : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 (2 * 1 + 1))) p) :
    hopfFibreForm (n := 1) p x y
      = suTwoCoframe p.2 0 x.2 * suTwoCoframe p.2 0 y.2 := by
  rw [hopfFibreForm_apply, suTwoCoframe_zero_eq_hopfAngleForm,
    suTwoCoframe_zero_eq_hopfAngleForm]

/-- **Math.** Petersen Example 1.4.13: the target form of the Hopf submersion of
Example 1.4.12, written in the `SU(2)` coframe:
`dt² + ρ²(t)((σ²)² + (σ³)²) + σ²(t)(σ¹)²`.
(Compare `hopfFibrationSUTwoCoframeSphere`, which is the submersion statement itself.) -/
theorem hopfQuotientForm_eq_suTwoCoframe (σ ρ : ℝ → ℝ) (p : ℝ × sphere (0 : 𝔼) 1)
    (x y : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 (2 * 1 + 1))) p) :
    hopfQuotientForm (n := 1) σ ρ p x y
      = x.1 * y.1
        + ρ p.1 ^ 2 * (suTwoCoframe p.2 1 x.2 * suTwoCoframe p.2 1 y.2
            + suTwoCoframe p.2 2 x.2 * suTwoCoframe p.2 2 y.2)
          + σ p.1 ^ 2 * (suTwoCoframe p.2 0 x.2 * suTwoCoframe p.2 0 y.2) := by
  have hg := hopfComplement_eq_suTwoCoframe p.2 x.2 y.2
  rw [sphereMetricUnit_apply, ← suTwoCoframe_zero_eq_hopfAngleForm p.2 x.2,
    ← suTwoCoframe_zero_eq_hopfAngleForm p.2 y.2] at hg
  rw [hopfQuotientForm_apply, ← suTwoCoframe_zero_eq_hopfAngleForm p.2 x.2,
    ← suTwoCoframe_zero_eq_hopfAngleForm p.2 y.2]
  linear_combination (ρ p.1 ^ 2) * hg

end SUTwoCoframe

end PetersenLib
