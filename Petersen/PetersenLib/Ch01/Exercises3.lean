import PetersenLib.Ch01.HopfFibration
import PetersenLib.Ch01.MetricConstructions
import PetersenLib.Ch01.IsometryGroups
import PetersenLib.Ch01.ArcLength
import PetersenLib.Ch01.DoublyWarpedSmoothness
import PetersenLib.Ch01.BiinvariantExistence
import PetersenLib.Ch01.AdjointRepresentation
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Petersen Ch. 1, §1.6 — Exercises 1.6.22–1.6.29

The last block of the §1.6 exercises: the quaternionic Hopf fibrations, the
Euler-number vector bundles over `S²`, and the Lie-group exercises
(bi-invariant metrics, the Killing form, `SL(n, ℝ)`, and the 2-dimensional
Lie group with no bi-invariant pseudo-metric).

* **Exercise 1.6.22** (`exercise1_6_22`): quaternions as a complex `2 × 2`
  matrix algebra (`quaternionMatrixRep`), the norm/conjugation identities,
  the two quaternionic Hopf maps `H^l, H^r : S⁷(1) → S⁴(1/2)`
  (`quaternionHopfLeft`, `quaternionHopfRight`), the identification of their
  fibres with the orbits of left/right multiplication by unit quaternions
  (`quaternionHopfLeft_fiber`, `quaternionHopfRight_fiber`), and the
  statements that both maps are Riemannian submersions (deferred, as is the
  complex case `hopfMap` of Example 1.1.5).
* **Exercise 1.6.23** (`exercise1_6_23`): for the submersion
  `(0,∞) × S³ × S¹ → (0,∞) × S³` of Exercise 1.6.13/Example 1.4.11 with
  `f = ρ` and `h = (ρφ)²/(ρ² + φ²)`, the boundary conditions `f(0) > 0`,
  `f^{odd}(0) = 0`, `h(0) = 0`, `h'(0) = k`, `h^{even}(0) = 0` are exactly
  the smoothness conditions of Props. 1.4.7/1.4.8 for the metric on the
  Euler-number-`±k` disc bundle over `S²` (fibre model `h/k`).
* **Exercise 1.6.24** (`exercise1_6_24`): bi-invariant metrics on compact
  Lie groups: existence by averaging (statement; proof deferred),
  conjugation is an isometry (`biinvariantMetric_conj_isometry`, proved),
  `Ad_h` is a linear isometry of the Lie algebra
  (`biinvariantMetric_conj_mfderiv_isometry`, proved), `ad_U` is
  skew-symmetric (statement; proof needs `Ad' = ad`, Petersen §2.1.4).
* **Exercise 1.6.25** (`exercise1_6_25`, fully proved): a nondegenerate
  symmetric bilinear form on `T_eG` defines a bi-invariant pseudo-Riemannian
  metric iff it is `Ad`-invariant (`leftInvariantPseudoMetric`).
* **Exercise 1.6.26** (`exercise1_6_26`, in `AveragedMetricCompact.lean`): a compact
  Lie group acting smoothly (jointly) on `M` preserves some Riemannian metric — the
  Haar-averaged metric, with regularity and invariance proved and only the `C^∞`
  parametric-integral smoothness of the average deferred (Mathlib gap).
* **Exercise 1.6.27** (`exercise1_6_27`): the Killing form is symmetric,
  `ad`-invariant, `≤ 0` on the diagonal in the presence of a bi-invariant
  metric, and invariant under Lie algebra automorphisms (all proved), and
  nondegenerate for semisimple algebras (`exercise1_6_27_nondegenerate`).
* **Exercise 1.6.28** (`exercise1_6_28`, fully proved): the trace form
  `(X, Y) ↦ tr(XY)` on `𝔰𝔩(n, ℝ)` is symmetric, nondegenerate, and
  `Ad`-invariant — the bi-invariant pseudo-metric of `SL(n, ℝ)`.
* **Exercise 1.6.29** (`exercise1_6_29`, fully proved): the matrices
  `diag(a⁻¹, (a, b)-affine block, 1)` form a 2-dimensional Lie group
  (`affineMatrixGroup`) admitting no bi-invariant pseudo-Riemannian metric:
  no nondegenerate symmetric `Ad`-invariant bilinear form exists on its Lie
  algebra `span{X, Y}`, `[X, Y] = Y`.

## Formalization notes

* Mathlib has no abstract Lie-group `Ad`/`ad` theory, so the adjoint action
  is realized as `mfderiv I I (fun x => h * x * h⁻¹) 1` on Lie groups
  (Exercises 24/25), as an abstract Lie algebra automorphism `L ≃ₗ⁅ℝ⁆ L`
  (Exercise 27(4)), and as literal matrix conjugation on matrix groups
  (Exercises 28/29). These agree with the classical `Ad` in each setting.
* The "yields a smooth metric on the vector bundle with Euler number `±k`"
  clause of Exercise 1.6.23 is formalized through its analytic content: the
  fibre warping function `h/k` of the `S³/ℤ_k` model (the `ℤ_k` quotient
  divides the fibre angle period by `k`) satisfies the endpoint smoothness
  criterion `WarpingClosesSmoothlyAt` of Props. 1.4.7/1.4.8, while the base
  warping `f` satisfies `WarpingStaysPositiveAt`; the bundle topology
  (Euler number, `TS²` for `k = 2`) has no formal counterpart yet and is
  recorded in prose only.
* Riemannian-submersion claims for the quaternionic Hopf maps are stated
  over the same sphere manifolds/metrics as `hopfMap` (Example 1.1.5) and
  deferred with `sorry`, exactly like the complex case.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.6, pp. 40–43.
-/

open Metric Module Function
open scoped ContDiff Manifold Topology Quaternion InnerProductSpace

noncomputable section

namespace PetersenLib

/-! ## Exercise 1.6.22 — the quaternionic Hopf fibrations (F. Wilhelm)

Quaternions `q = a + bi + cj + dk = z + wj` (`z = a + bi`, `w = c + di`) are
realized as the matrix algebra `q = !![z, w; -w̄, z̄]`; the two quaternionic
Hopf maps `ℍ² → ℝ ⊕ ℍ` are `H^l(p, q) = (½(|p|² − |q|²), p̄q)` and
`H^r(p, q) = (½(|p|² − |q|²), pq̄)`. -/

section Exercise22

/-- **Math.** Petersen Exercise 1.6.22 (1): the matrix realization of the
quaternions, `q = a + bi + cj + dk = z + wj ↦ !![z, w; -w̄, z̄]` with
`z = a + bi`, `w = c + di`. Sends `i ↦ !![i, 0; 0, -i]`, `j ↦ !![0, 1; -1, 0]`,
`k ↦ !![0, i; i, 0]` (`quaternionToMatrix_i` etc.); it is an injective
`ℝ`-algebra homomorphism (`quaternionMatrixRep`), which exhibits the
quaternion product as `ℝ`-bilinear and associative. -/
def quaternionToMatrix (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩; ⟨-q.imJ, q.imK⟩, ⟨q.re, -q.imI⟩]

theorem quaternionToMatrix_one : quaternionToMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · apply Complex.ext <;> simp [quaternionToMatrix, Matrix.one_apply]

theorem quaternionToMatrix_zero : quaternionToMatrix 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · apply Complex.ext <;> simp [quaternionToMatrix]

theorem quaternionToMatrix_add (p q : ℍ[ℝ]) :
    quaternionToMatrix (p + q) = quaternionToMatrix p + quaternionToMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · apply Complex.ext <;> simp [quaternionToMatrix] <;> ring

/-- **Math.** Multiplicativity of the matrix realization: the quaternion
product `(z + wj)(z' + w'j) = (zz' − w w̄') + (zw' + w z̄')j` matches the
`2 × 2` matrix product. -/
theorem quaternionToMatrix_mul (p q : ℍ[ℝ]) :
    quaternionToMatrix (p * q) = quaternionToMatrix p * quaternionToMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · apply Complex.ext <;>
        simp [quaternionToMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          Complex.mul_re, Complex.mul_im, Quaternion.re_mul, Quaternion.imI_mul,
          Quaternion.imJ_mul, Quaternion.imK_mul] <;>
        ring

/-- **Math.** Petersen Exercise 1.6.22 (1): the quaternions realized as a
complex `2 × 2` matrix algebra, as a bundled `ℝ`-algebra homomorphism
`ℍ → M₂(ℂ)`. Injectivity is `quaternionMatrixRep_injective`. -/
def quaternionMatrixRep : ℍ[ℝ] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := quaternionToMatrix
  map_one' := quaternionToMatrix_one
  map_mul' := quaternionToMatrix_mul
  map_zero' := quaternionToMatrix_zero
  map_add' := quaternionToMatrix_add
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      · apply Complex.ext <;>
          simp [quaternionToMatrix, Matrix.algebraMap_matrix_apply]

@[simp]
theorem quaternionMatrixRep_apply (q : ℍ[ℝ]) :
    quaternionMatrixRep q = quaternionToMatrix q := rfl

/-- **Math.** The matrix realization of the quaternions is injective, so `ℍ`
is (isomorphic to) a subalgebra of `M₂(ℂ)`. -/
theorem quaternionMatrixRep_injective : Function.Injective quaternionMatrixRep := by
  intro p q h
  have h' : quaternionToMatrix p = quaternionToMatrix q := h
  have h00 := Matrix.ext_iff.mpr h' 0 0
  have h01 := Matrix.ext_iff.mpr h' 0 1
  simp only [quaternionToMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.mk.injEq] at h00 h01
  exact QuaternionAlgebra.ext h00.1 h00.2 h01.1 h01.2

/-- **Math.** The image of `i` under the matrix realization. -/
theorem quaternionToMatrix_i :
    quaternionToMatrix (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) = !![Complex.I, 0; 0, -Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · apply Complex.ext <;> simp [quaternionToMatrix]

/-- **Math.** The image of `j` under the matrix realization. -/
theorem quaternionToMatrix_j :
    quaternionToMatrix (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · apply Complex.ext <;> simp [quaternionToMatrix]

/-- **Math.** The image of `k` under the matrix realization. -/
theorem quaternionToMatrix_k :
    quaternionToMatrix (⟨0, 0, 0, 1⟩ : ℍ[ℝ]) = !![0, Complex.I; Complex.I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · apply Complex.ext <;> simp [quaternionToMatrix]

/-- **Math.** Petersen Exercise 1.6.22 (2): the determinant of the matrix
realization is the quaternionic norm-square,
`det !![z, w; -w̄, z̄] = |z|² + |w|² = |q|²`. -/
theorem quaternionToMatrix_det (q : ℍ[ℝ]) :
    (quaternionToMatrix q).det = ((Quaternion.normSq q : ℝ) : ℂ) := by
  rw [quaternionToMatrix, Matrix.det_fin_two_of]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Quaternion.normSq_def'] <;>
    ring

/-- **Math.** Petersen Exercise 1.6.22 (2): `|q|² = |z|² + |w|²` for
`q = z + wj`. -/
theorem quaternion_normSq_eq_add_complex_normSq (q : ℍ[ℝ]) :
    Quaternion.normSq q
      = Complex.normSq ⟨q.re, q.imI⟩ + Complex.normSq ⟨q.imJ, q.imK⟩ := by
  simp [Quaternion.normSq_def', Complex.normSq_apply]; ring

/-! ### The two quaternionic Hopf maps `ℍ² → ℝ ⊕ ℍ` -/

/-- **Eng.** `ℍ² = WithLp 2 (ℍ × ℍ)` has real dimension `8 = 7 + 1`; this
`Fact` feeds the sphere `S⁷ ⊆ ℍ²` its charted-space structure over
`EuclideanSpace ℝ (Fin 7)`. -/
instance fact_finrank_quaternion_prod :
    Fact (finrank ℝ (WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) = 7 + 1) :=
  ⟨by
    rw [(WithLp.linearEquiv 2 ℝ (ℍ[ℝ] × ℍ[ℝ])).finrank_eq, Module.finrank_prod,
      Quaternion.finrank_eq_four]⟩

/-- **Eng.** `ℝ ⊕ ℍ = WithLp 2 (ℝ × ℍ)` has real dimension `5 = 4 + 1`; this
`Fact` feeds the sphere `S⁴ ⊆ ℝ ⊕ ℍ` its charted-space structure over
`EuclideanSpace ℝ (Fin 4)`. -/
instance fact_finrank_real_quaternion_prod :
    Fact (finrank ℝ (WithLp 2 (ℝ × ℍ[ℝ])) = 4 + 1) :=
  ⟨by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × ℍ[ℝ])).finrank_eq, Module.finrank_prod,
      Quaternion.finrank_eq_four, Module.finrank_self]⟩

/-- **Math.** Petersen Exercise 1.6.22 (3): the **left quaternionic Hopf
map** on the ambient space, `H^l(p, q) = (½(|p|² − |q|²), p̄q) : ℍ² → ℝ ⊕ ℍ`.
Its restriction to the unit sphere is `quaternionHopfLeft : S⁷(1) → S⁴(1/2)`. -/
def quaternionHopfLeftAmbient (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) : WithLp 2 (ℝ × ℍ[ℝ]) :=
  WithLp.toLp 2 ((‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2) / 2, star x.fst * x.snd)

/-- **Math.** Petersen Exercise 1.6.22 (3): the **right quaternionic Hopf
map** on the ambient space, `H^r(p, q) = (½(|p|² − |q|²), pq̄) : ℍ² → ℝ ⊕ ℍ`.
Its restriction to the unit sphere is `quaternionHopfRight : S⁷(1) → S⁴(1/2)`. -/
def quaternionHopfRightAmbient (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) : WithLp 2 (ℝ × ℍ[ℝ]) :=
  WithLp.toLp 2 ((‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2) / 2, x.fst * star x.snd)

@[simp]
theorem quaternionHopfLeftAmbient_fst (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    (quaternionHopfLeftAmbient x).fst = (‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2) / 2 := rfl

@[simp]
theorem quaternionHopfLeftAmbient_snd (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    (quaternionHopfLeftAmbient x).snd = star x.fst * x.snd := rfl

@[simp]
theorem quaternionHopfRightAmbient_fst (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    (quaternionHopfRightAmbient x).fst = (‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2) / 2 := rfl

@[simp]
theorem quaternionHopfRightAmbient_snd (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    (quaternionHopfRightAmbient x).snd = x.fst * star x.snd := rfl

/-- **Math.** The left ambient Hopf map squares norms up to the factor `1/2`:
`|H^l(p,q)| = ½(|p|² + |q|²)`, because
`|H^l|² = ¼(|p|² − |q|²)² + |p|²|q|² = ¼(|p|² + |q|²)²`. -/
theorem norm_quaternionHopfLeftAmbient (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    ‖quaternionHopfLeftAmbient x‖ = ‖x‖ ^ 2 / 2 := by
  have h1 : ‖quaternionHopfLeftAmbient x‖ ^ 2 = (‖x‖ ^ 2 / 2) ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2 x,
      quaternionHopfLeftAmbient_fst, quaternionHopfLeftAmbient_snd, norm_mul,
      norm_star]
    rw [Real.norm_eq_abs, sq_abs, mul_pow]
    ring
  have h2 : (0 : ℝ) ≤ ‖quaternionHopfLeftAmbient x‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ ‖x‖ ^ 2 / 2 := by positivity
  exact (sq_eq_sq₀ h2 h3).mp h1

/-- **Math.** The right ambient Hopf map squares norms up to the factor
`1/2`, as the left one does. -/
theorem norm_quaternionHopfRightAmbient (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    ‖quaternionHopfRightAmbient x‖ = ‖x‖ ^ 2 / 2 := by
  have h1 : ‖quaternionHopfRightAmbient x‖ ^ 2 = (‖x‖ ^ 2 / 2) ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2 x,
      quaternionHopfRightAmbient_fst, quaternionHopfRightAmbient_snd, norm_mul,
      norm_star]
    rw [Real.norm_eq_abs, sq_abs, mul_pow]
    ring
  have h2 : (0 : ℝ) ≤ ‖quaternionHopfRightAmbient x‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ ‖x‖ ^ 2 / 2 := by positivity
  exact (sq_eq_sq₀ h2 h3).mp h1

/-- **Math.** Petersen Exercise 1.6.22 (3): `H^l` maps `S⁷(1) ⊆ ℍ²` into
`S⁴(1/2) ⊆ ℝ ⊕ ℍ`. -/
theorem quaternionHopfLeftAmbient_mem_sphere (x : sphere (0 : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) 1) :
    quaternionHopfLeftAmbient ↑x ∈ sphere (0 : WithLp 2 (ℝ × ℍ[ℝ])) (1 / 2) := by
  rw [mem_sphere_zero_iff_norm, norm_quaternionHopfLeftAmbient,
    mem_sphere_zero_iff_norm.mp x.2]
  norm_num

/-- **Math.** Petersen Exercise 1.6.22 (3): `H^r` maps `S⁷(1) ⊆ ℍ²` into
`S⁴(1/2) ⊆ ℝ ⊕ ℍ`. -/
theorem quaternionHopfRightAmbient_mem_sphere (x : sphere (0 : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) 1) :
    quaternionHopfRightAmbient ↑x ∈ sphere (0 : WithLp 2 (ℝ × ℍ[ℝ])) (1 / 2) := by
  rw [mem_sphere_zero_iff_norm, norm_quaternionHopfRightAmbient,
    mem_sphere_zero_iff_norm.mp x.2]
  norm_num

/-- **Math.** Petersen Exercise 1.6.22: the **left quaternionic Hopf
fibration** `H^l : S⁷(1) → S⁴(1/2)`, `H^l(p, q) = (½(|p|² − |q|²), p̄q)`.
Its fibres are the orbits of left multiplication by unit quaternions
(`quaternionHopfLeft_fiber`), so it is a fibration with fibre `S³`. -/
def quaternionHopfLeft (x : sphere (0 : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) 1) :
    sphere (0 : WithLp 2 (ℝ × ℍ[ℝ])) (1 / 2) :=
  ⟨quaternionHopfLeftAmbient ↑x, quaternionHopfLeftAmbient_mem_sphere x⟩

/-- **Math.** Petersen Exercise 1.6.22: the **right quaternionic Hopf
fibration** `H^r : S⁷(1) → S⁴(1/2)`, `H^r(p, q) = (½(|p|² − |q|²), pq̄)`.
Its fibres are the orbits of right multiplication by unit quaternions
(`quaternionHopfRight_fiber`). -/
def quaternionHopfRight (x : sphere (0 : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) 1) :
    sphere (0 : WithLp 2 (ℝ × ℍ[ℝ])) (1 / 2) :=
  ⟨quaternionHopfRightAmbient ↑x, quaternionHopfRightAmbient_mem_sphere x⟩

/-- **Math.** The key algebraic step for Petersen Exercise 1.6.22 (4): two
points of `S⁷(1)` with the same image under `H^l` lie on a common orbit of
*left* multiplication by a unit quaternion. If `p₁ ≠ 0` the unit is
`u = q₁p₁⁻¹ = |p₁|⁻²q₁p̄₁` (then `up₂ = |p₁|⁻²q₁(p̄₁p₂) = |p₁|⁻²q₁(q̄₁q₂) = q₂`);
if `p₁ = 0` then `q₁ = 0`, `|p₂| = 1`, and `u = q₂p̄₂` works. -/
theorem exists_unit_quaternion_left_mul {p₁ p₂ q₁ q₂ : ℍ[ℝ]}
    (hp : ‖p₁‖ ^ 2 + ‖p₂‖ ^ 2 = 1) (hq : ‖q₁‖ ^ 2 + ‖q₂‖ ^ 2 = 1)
    (hdiff : ‖p₁‖ ^ 2 - ‖p₂‖ ^ 2 = ‖q₁‖ ^ 2 - ‖q₂‖ ^ 2)
    (hcross : star p₁ * p₂ = star q₁ * q₂) :
    ∃ u : ℍ[ℝ], ‖u‖ = 1 ∧ q₁ = u * p₁ ∧ q₂ = u * p₂ := by
  have h1 : ‖q₁‖ ^ 2 = ‖p₁‖ ^ 2 := by linarith
  have h2 : ‖q₂‖ ^ 2 = ‖p₂‖ ^ 2 := by linarith
  have hnormSq : ∀ a : ℍ[ℝ], Quaternion.normSq a = ‖a‖ ^ 2 := fun a => by
    rw [Quaternion.normSq_eq_norm_mul_self, sq]
  by_cases hp₁ : p₁ = 0
  · have hq₁ : q₁ = 0 := by
      have : ‖q₁‖ ^ 2 = 0 := by rw [h1, hp₁]; simp
      simpa using this
    have hp₂ : ‖p₂‖ = 1 := by
      have h : ‖p₂‖ ^ 2 = 1 := by rw [hp₁] at hp; simpa using hp
      nlinarith [norm_nonneg p₂]
    have hq₂ : ‖q₂‖ = 1 := by
      have h : ‖q₂‖ ^ 2 = 1 := by rw [h2, hp₂]; norm_num
      nlinarith [norm_nonneg q₂]
    refine ⟨q₂ * star p₂, ?_, ?_, ?_⟩
    · rw [norm_mul, norm_star, hp₂, hq₂, mul_one]
    · rw [hp₁, hq₁, mul_zero]
    · rw [mul_assoc, Quaternion.star_mul_self, hnormSq, hp₂]
      norm_num
  · have hp₁norm : (0 : ℝ) < ‖p₁‖ := norm_pos_iff.mpr hp₁
    have hq₁norm : ‖q₁‖ = ‖p₁‖ := by nlinarith [norm_nonneg p₁, norm_nonneg q₁]
    refine ⟨(‖p₁‖ ^ 2)⁻¹ • (q₁ * star p₁), ?_, ?_, ?_⟩
    · rw [norm_smul, norm_mul, norm_star, hq₁norm, norm_inv, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      field_simp
    · rw [smul_mul_assoc, mul_assoc, Quaternion.star_mul_self, hnormSq,
        Quaternion.mul_coe_eq_smul, smul_smul,
        inv_mul_cancel₀ (by positivity), one_smul]
    · rw [smul_mul_assoc, mul_assoc, hcross, ← mul_assoc,
        Quaternion.self_mul_star, hnormSq, hq₁norm,
        Quaternion.coe_mul_eq_smul, smul_smul,
        inv_mul_cancel₀ (by positivity), one_smul]

/-- **Math.** The key algebraic step for Petersen Exercise 1.6.22 (5): two
points of `S⁷(1)` with the same image under `H^r` lie on a common orbit of
*right* multiplication by a unit quaternion. -/
theorem exists_unit_quaternion_right_mul {p₁ p₂ q₁ q₂ : ℍ[ℝ]}
    (hp : ‖p₁‖ ^ 2 + ‖p₂‖ ^ 2 = 1) (hq : ‖q₁‖ ^ 2 + ‖q₂‖ ^ 2 = 1)
    (hdiff : ‖p₁‖ ^ 2 - ‖p₂‖ ^ 2 = ‖q₁‖ ^ 2 - ‖q₂‖ ^ 2)
    (hcross : p₁ * star p₂ = q₁ * star q₂) :
    ∃ u : ℍ[ℝ], ‖u‖ = 1 ∧ q₁ = p₁ * u ∧ q₂ = p₂ * u := by
  have h1 : ‖q₁‖ ^ 2 = ‖p₁‖ ^ 2 := by linarith
  have h2 : ‖q₂‖ ^ 2 = ‖p₂‖ ^ 2 := by linarith
  have hnormSq : ∀ a : ℍ[ℝ], Quaternion.normSq a = ‖a‖ ^ 2 := fun a => by
    rw [Quaternion.normSq_eq_norm_mul_self, sq]
  -- reduce to the left-multiplication case via `star`
  have hcross' : star (star p₂) * star p₁ = star (star q₂) * star q₁ := by
    rw [← star_mul, ← star_mul, hcross]
  obtain ⟨u, hu, h₂, h₁⟩ :=
    exists_unit_quaternion_left_mul
      (p₁ := star p₂) (p₂ := star p₁) (q₁ := star q₂) (q₂ := star q₁)
      (by rw [norm_star, norm_star]; linarith)
      (by rw [norm_star, norm_star]; linarith)
      (by rw [norm_star, norm_star, norm_star, norm_star]; linarith) hcross'
  refine ⟨star u, by rw [norm_star, hu], ?_, ?_⟩
  · calc q₁ = star (star q₁) := (star_star q₁).symm
      _ = star (u * star p₁) := by rw [← h₁]
      _ = p₁ * star u := by rw [star_mul, star_star]
  · calc q₂ = star (star q₂) := (star_star q₂).symm
      _ = star (u * star p₂) := by rw [← h₂]
      _ = p₂ * star u := by rw [star_mul, star_star]

/-- **Eng.** Sphere membership in `ℍ²` unfolded to the two quaternionic
components: `x ∈ S⁷(1)` iff `‖x₁‖² + ‖x₂‖² = 1`. -/
theorem mem_sphere_quaternion_prod_iff (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    x ∈ sphere (0 : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) 1 ↔ ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1 := by
  rw [mem_sphere_zero_iff_norm, ← WithLp.prod_norm_sq_eq_of_L2]
  constructor
  · intro h; rw [h]; norm_num
  · intro h
    have h' : ‖x‖ ^ 2 = 1 ^ 2 := by rw [h]; norm_num
    exact (sq_eq_sq₀ (norm_nonneg _) one_pos.le).mp h'

/-- **Math.** Petersen Exercise 1.6.22 (4): the fibres of
`H^l : S⁷(1) → S⁴(1/2)` are exactly the orbits of **left** multiplication by
unit quaternions on `ℍ²`. -/
theorem quaternionHopfLeft_fiber (x y : sphere (0 : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) 1) :
    quaternionHopfLeft x = quaternionHopfLeft y ↔
      ∃ u : ℍ[ℝ], ‖u‖ = 1 ∧
        (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst = u * (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst ∧
        (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd = u * (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd := by
  have hx := (mem_sphere_quaternion_prod_iff _).mp x.2
  have hy := (mem_sphere_quaternion_prod_iff _).mp y.2
  have hval : quaternionHopfLeft x = quaternionHopfLeft y ↔
      (‖(x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst‖ ^ 2 - ‖(x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd‖ ^ 2) / 2
          = (‖(y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst‖ ^ 2 - ‖(y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd‖ ^ 2) / 2
        ∧ star (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst * (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd
          = star (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst * (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd := by
    rw [Subtype.ext_iff]
    show quaternionHopfLeftAmbient _ = quaternionHopfLeftAmbient _ ↔ _
    rw [quaternionHopfLeftAmbient, quaternionHopfLeftAmbient,
      (WithLp.toLp_injective 2).eq_iff, Prod.ext_iff]
  rw [hval]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨u, hu, hu1, hu2⟩ := exists_unit_quaternion_left_mul hx hy
      (by linarith) h2
    exact ⟨u, hu, hu1, hu2⟩
  · rintro ⟨u, hu, hu1, hu2⟩
    have hnormSqu : Quaternion.normSq u = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, hu, mul_one]
    constructor
    · rw [hu1, hu2, norm_mul, norm_mul, hu, one_mul, one_mul]
    · rw [hu1, hu2, star_mul, mul_assoc, ← mul_assoc (star u),
        Quaternion.star_mul_self, hnormSqu]
      norm_num

/-- **Math.** Petersen Exercise 1.6.22 (5): the fibres of
`H^r : S⁷(1) → S⁴(1/2)` are exactly the orbits of **right** multiplication
by unit quaternions on `ℍ²`. -/
theorem quaternionHopfRight_fiber (x y : sphere (0 : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) 1) :
    quaternionHopfRight x = quaternionHopfRight y ↔
      ∃ u : ℍ[ℝ], ‖u‖ = 1 ∧
        (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst = (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst * u ∧
        (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd = (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd * u := by
  have hx := (mem_sphere_quaternion_prod_iff _).mp x.2
  have hy := (mem_sphere_quaternion_prod_iff _).mp y.2
  have hval : quaternionHopfRight x = quaternionHopfRight y ↔
      (‖(x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst‖ ^ 2 - ‖(x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd‖ ^ 2) / 2
          = (‖(y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst‖ ^ 2 - ‖(y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd‖ ^ 2) / 2
        ∧ (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst * star (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd
          = (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst * star (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd := by
    rw [Subtype.ext_iff]
    show quaternionHopfRightAmbient _ = quaternionHopfRightAmbient _ ↔ _
    rw [quaternionHopfRightAmbient, quaternionHopfRightAmbient,
      (WithLp.toLp_injective 2).eq_iff, Prod.ext_iff]
  rw [hval]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨u, hu, hu1, hu2⟩ := exists_unit_quaternion_right_mul hx hy
      (by linarith) h2
    exact ⟨u, hu, hu1, hu2⟩
  · rintro ⟨u, hu, hu1, hu2⟩
    have hnormSqu : Quaternion.normSq u = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, hu, mul_one]
    constructor
    · rw [hu1, hu2, norm_mul, norm_mul, hu, mul_one, mul_one]
    · rw [hu1, hu2, star_mul, ← mul_assoc, mul_assoc _ u,
        Quaternion.self_mul_star, hnormSqu]
      norm_num

/-! ### Quaternion algebra for the Riemannian-submersion computation

The whole submersion computation for `H^l, H^r` is carried out *abstractly*
in the quaternion algebra — no expansion into the four real coordinates is
needed. The three facts that make it collapse are

* cyclicity of the real part, `Re(ab) = Re(ba)`;
* `a ā = ā a = |a|²` (a central real scalar);
* the polarization identity `Re(a b̄) = 2 Re(a) Re(b) − Re(ab)`, coming from
  `b̄ = 2 Re(b) − b`.

Throughout, the Euclidean inner product of `ℍ ≅ ℝ⁴` is `⟪a, b⟫ = Re(a b̄)`
(`real_inner_quaternion`, true by `rfl` in Mathlib). -/

/-- **Eng.** The real part is additive. -/
theorem quaternion_re_add (a b : ℍ[ℝ]) : (a + b).re = a.re + b.re := rfl

/-- **Eng.** The real part commutes with negation. -/
theorem quaternion_re_neg (a : ℍ[ℝ]) : (-a).re = -a.re := rfl

/-- **Math.** The real part of a quaternion product is **cyclic**:
`Re(ab) = Re(ba)`. -/
theorem quaternion_re_mul_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := by
  simp only [Quaternion.re_mul]; ring

/-- **Math.** Symmetry of the Euclidean inner product `⟪a, b⟫ = Re(a b̄)`. -/
theorem quaternion_re_mul_star_comm (a b : ℍ[ℝ]) :
    (a * star b).re = (b * star a).re := by
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- **Math.** The polarization identity `Re(a b̄) = 2 Re(a) Re(b) − Re(ab)`,
obtained from `b̄ = 2 Re(b) − b`. This is the identity that makes the
quaternionic Hopf computation collapse. -/
theorem quaternion_re_mul_star (a b : ℍ[ℝ]) :
    (a * star b).re = 2 * a.re * b.re - (a * b).re := by
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- **Math.** `ā a = |a|²`, a central real scalar. -/
theorem quaternion_star_mul_self (a : ℍ[ℝ]) :
    star a * a = ((‖a‖ ^ 2 : ℝ) : ℍ[ℝ]) := by
  rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, sq]

/-- **Math.** `a ā = |a|²`, a central real scalar. -/
theorem quaternion_self_mul_star (a : ℍ[ℝ]) :
    a * star a = ((‖a‖ ^ 2 : ℝ) : ℍ[ℝ]) := by
  rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, sq]

/-- **Eng.** Real part of a left multiple by a real scalar. -/
theorem quaternion_re_coe_mul (r : ℝ) (a : ℍ[ℝ]) :
    ((r : ℍ[ℝ]) * a).re = r * a.re := by
  simp [Quaternion.re_mul]

/-- **Eng.** Real part of a right multiple by a real scalar. -/
theorem quaternion_re_mul_coe (r : ℝ) (a : ℍ[ℝ]) :
    (a * (r : ℍ[ℝ])).re = r * a.re := by
  simp [Quaternion.re_mul]; ring

/-- **Eng.** Real scalars are central. -/
theorem quaternion_coe_mid (r : ℝ) (a b : ℍ[ℝ]) :
    a * ((r : ℝ) : ℍ[ℝ]) * b = ((r : ℝ) : ℍ[ℝ]) * (a * b) := by
  rw [Quaternion.mul_coe_eq_smul, smul_mul_assoc, Quaternion.coe_mul_eq_smul]

/-- **Eng.** A quaternion with vanishing components is zero. -/
theorem quaternion_eq_zero (a : ℍ[ℝ]) (h1 : a.re = 0) (h2 : a.imI = 0)
    (h3 : a.imJ = 0) (h4 : a.imK = 0) : a = 0 := by
  apply Quaternion.ext <;> simp [h1, h2, h3, h4]

/-- **Math.** `Re(s ā)` is the Euclidean inner product of `s` and `a` in
coordinates — the identity that lets one read off the four components of `a`
by testing against `s = 1, i, j, k`. -/
theorem quaternion_re_mul_star_expand (s a : ℍ[ℝ]) :
    (s * star a).re
      = s.re * a.re + s.imI * a.imI + s.imJ * a.imJ + s.imK * a.imK := by
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- **Eng.** The Euclidean inner product of `ℍ ≅ ℝ⁴` in algebraic form. -/
theorem real_inner_quaternion (a b : ℍ[ℝ]) : ⟪a, b⟫_ℝ = (a * star b).re := rfl

/-- **Eng.** The Euclidean inner product of `ℍ² ≅ ℝ⁸` in algebraic form. -/
theorem real_inner_quaternion_prod (x y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    ⟪x, y⟫_ℝ = (x.fst * star y.fst).re + (x.snd * star y.snd).re := by
  rw [WithLp.prod_inner_apply]; rfl

/-- **Eng.** The Euclidean inner product of `ℝ ⊕ ℍ ≅ ℝ⁵` in algebraic form. -/
theorem real_inner_real_quaternion_prod (x y : WithLp 2 (ℝ × ℍ[ℝ])) :
    ⟪x, y⟫_ℝ = x.fst * y.fst + (x.snd * star y.snd).re := by
  rw [WithLp.prod_inner_apply]
  show y.fst * x.fst + (x.snd * star y.snd).re = _
  ring

/-- **Math.** The standard basis `1, i, j, k` of `ℍ ≅ ℝ⁴`. -/
def quaternionUnit : Fin 4 → ℍ[ℝ] :=
  ![1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- **Math.** `1, i, j, k` is an orthonormal basis of `ℍ`. -/
theorem quaternionUnit_re_mul_star (i j : Fin 4) :
    (quaternionUnit i * star (quaternionUnit j)).re = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [quaternionUnit, Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star]

/-- **Eng.** Quaternion conjugation as a continuous `ℝ`-linear map (it is an
`ℝ`-linear isometry of `ℍ ≅ ℝ⁴`). -/
noncomputable def quaternionStarCLM : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  LinearMap.mkContinuous
    { toFun := star
      map_add' := star_add
      map_smul' := fun r x => by apply Quaternion.ext <;> simp } 1 (by simp)

@[simp]
theorem quaternionStarCLM_apply (a : ℍ[ℝ]) : quaternionStarCLM a = star a := rfl

/-! ### The differential of the ambient quaternionic Hopf maps

Expanding `H^l((p, q) + t(u, v))` to first order gives

  `DH^l|_{(p,q)}(u, v) = (⟪p, u⟫ − ⟪q, v⟫, ū q + p̄ v)`,

and symmetrically `DH^r|_{(p,q)}(u, v) = (⟪p, u⟫ − ⟪q, v⟫, u q̄ + p v̄)`. -/

/-- **Math.** The differential of the ambient left Hopf map at `(p, q)`. -/
noncomputable def quaternionHopfLeftDeriv (p q : ℍ[ℝ]) :
    WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) →L[ℝ] WithLp 2 (ℝ × ℍ[ℝ]) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ[ℝ]).symm :
      ℝ × ℍ[ℝ] →L[ℝ] WithLp 2 (ℝ × ℍ[ℝ])).comp <|
    ContinuousLinearMap.prod
      ((innerSL ℝ p).comp (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]) -
        (innerSL ℝ q).comp (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]))
      (((ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip q).comp
          (quaternionStarCLM.comp (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ])) +
        (ContinuousLinearMap.mul ℝ ℍ[ℝ] (star p)).comp
          (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]))

@[simp]
theorem quaternionHopfLeftDeriv_fst (p q : ℍ[ℝ]) (v : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    (quaternionHopfLeftDeriv p q v).fst = ⟪p, v.fst⟫_ℝ - ⟪q, v.snd⟫_ℝ := rfl

@[simp]
theorem quaternionHopfLeftDeriv_snd (p q : ℍ[ℝ]) (v : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    (quaternionHopfLeftDeriv p q v).snd = star v.fst * q + star p * v.snd := rfl

/-- **Math.** The differential of the ambient right Hopf map at `(p, q)`. -/
noncomputable def quaternionHopfRightDeriv (p q : ℍ[ℝ]) :
    WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) →L[ℝ] WithLp 2 (ℝ × ℍ[ℝ]) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ[ℝ]).symm :
      ℝ × ℍ[ℝ] →L[ℝ] WithLp 2 (ℝ × ℍ[ℝ])).comp <|
    ContinuousLinearMap.prod
      ((innerSL ℝ p).comp (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]) -
        (innerSL ℝ q).comp (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]))
      (((ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip (star q)).comp
          (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]) +
        (ContinuousLinearMap.mul ℝ ℍ[ℝ] p).comp
          (quaternionStarCLM.comp (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ])))

@[simp]
theorem quaternionHopfRightDeriv_fst (p q : ℍ[ℝ]) (v : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    (quaternionHopfRightDeriv p q v).fst = ⟪p, v.fst⟫_ℝ - ⟪q, v.snd⟫_ℝ := rfl

@[simp]
theorem quaternionHopfRightDeriv_snd (p q : ℍ[ℝ]) (v : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    (quaternionHopfRightDeriv p q v).snd = v.fst * star q + p * star v.snd := rfl

/-- **Eng.** The two quadratic ambient maps are `C^∞`. -/
theorem contDiff_quaternionHopfLeftAmbient :
    ContDiff ℝ ∞ quaternionHopfLeftAmbient := by
  have hfst : ContDiff ℝ ∞ (fun x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => x.fst) :=
    (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]).contDiff
  have hsnd : ContDiff ℝ ∞ (fun x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => x.snd) :=
    (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]).contDiff
  have h₁ : ContDiff ℝ ∞
      (fun x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => (‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2) / 2) :=
    ((hfst.norm_sq ℝ).sub (hsnd.norm_sq ℝ)).div_const 2
  have h₂ : ContDiff ℝ ∞
      (fun x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => star x.fst * x.snd) :=
    (quaternionStarCLM.contDiff.comp hfst).mul hsnd
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ[ℝ]).symm.contDiff.comp (h₁.prodMk h₂)

theorem contDiff_quaternionHopfRightAmbient :
    ContDiff ℝ ∞ quaternionHopfRightAmbient := by
  have hfst : ContDiff ℝ ∞ (fun x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => x.fst) :=
    (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]).contDiff
  have hsnd : ContDiff ℝ ∞ (fun x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => x.snd) :=
    (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]).contDiff
  have h₁ : ContDiff ℝ ∞
      (fun x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => (‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2) / 2) :=
    ((hfst.norm_sq ℝ).sub (hsnd.norm_sq ℝ)).div_const 2
  have h₂ : ContDiff ℝ ∞
      (fun x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => x.fst * star x.snd) :=
    hfst.mul (quaternionStarCLM.contDiff.comp hsnd)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ[ℝ]).symm.contDiff.comp (h₁.prodMk h₂)

/-- **Eng.** The squared-norm half-difference `x ↦ ½(|x₁|² − |x₂|²)` has the
stated differential. -/
private theorem hasFDerivAt_quaternionNormDiff (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    HasFDerivAt (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => (‖y.fst‖ ^ 2 - ‖y.snd‖ ^ 2) / 2)
      ((innerSL ℝ x.fst).comp (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]) -
        (innerSL ℝ x.snd).comp (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ])) x := by
  have hfst : HasFDerivAt (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => y.fst)
      (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]) x := (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]).hasFDerivAt
  have hsnd : HasFDerivAt (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => y.snd)
      (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]) x := (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]).hasFDerivAt
  have h := (hfst.norm_sq.sub hsnd.norm_sq).const_smul (2⁻¹ : ℝ)
  have harg : (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => (‖y.fst‖ ^ 2 - ‖y.snd‖ ^ 2) / 2)
      = (2⁻¹ : ℝ) • fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => ‖y.fst‖ ^ 2 - ‖y.snd‖ ^ 2 := by
    funext y
    simp [div_eq_inv_mul]
  rw [harg]
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- **Math.** `quaternionHopfLeftDeriv p q` is the derivative of the ambient
left Hopf map at `(p, q)`. -/
theorem hasFDerivAt_quaternionHopfLeftAmbient (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    HasFDerivAt quaternionHopfLeftAmbient
      (quaternionHopfLeftDeriv x.fst x.snd) x := by
  have hfst : HasFDerivAt (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => y.fst)
      (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]) x := (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]).hasFDerivAt
  have hsnd : HasFDerivAt (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => y.snd)
      (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]) x := (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]).hasFDerivAt
  have hstar : HasFDerivAt (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => star y.fst)
      (quaternionStarCLM.comp (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ])) x :=
    quaternionStarCLM.hasFDerivAt.comp x hfst
  have h₂ : HasFDerivAt (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => star y.fst * y.snd)
      ((((ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip x.snd).comp
          (quaternionStarCLM.comp (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]))) +
        (ContinuousLinearMap.mul ℝ ℍ[ℝ] (star x.fst)).comp
          (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ])) x := by
    refine (hstar.mul' hsnd).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    show star x.fst * v.snd + star v.fst * x.snd
        = star v.fst * x.snd + star x.fst * v.snd
    exact add_comm _ _
  have h := ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ[ℝ]).symm.hasFDerivAt
    (x := ((‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2) / 2, star x.fst * x.snd))).comp x
      ((hasFDerivAt_quaternionNormDiff x).prodMk h₂)
  exact h

/-- **Math.** `quaternionHopfRightDeriv p q` is the derivative of the ambient
right Hopf map at `(p, q)`. -/
theorem hasFDerivAt_quaternionHopfRightAmbient (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    HasFDerivAt quaternionHopfRightAmbient
      (quaternionHopfRightDeriv x.fst x.snd) x := by
  have hfst : HasFDerivAt (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => y.fst)
      (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]) x := (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ]).hasFDerivAt
  have hsnd : HasFDerivAt (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => y.snd)
      (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]) x := (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]).hasFDerivAt
  have hstar : HasFDerivAt (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => star y.snd)
      (quaternionStarCLM.comp (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ])) x :=
    quaternionStarCLM.hasFDerivAt.comp x hsnd
  have h₂ : HasFDerivAt (fun y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) => y.fst * star y.snd)
      ((((ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip (star x.snd)).comp
          (WithLp.fstL 2 ℝ ℍ[ℝ] ℍ[ℝ])) +
        (ContinuousLinearMap.mul ℝ ℍ[ℝ] x.fst).comp
          (quaternionStarCLM.comp (WithLp.sndL 2 ℝ ℍ[ℝ] ℍ[ℝ]))) x := by
    refine (hfst.mul' hstar).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    show x.fst * star v.snd + v.fst * star x.snd
        = v.fst * star x.snd + x.fst * star v.snd
    exact add_comm _ _
  have h := ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ[ℝ]).symm.hasFDerivAt
    (x := ((‖x.fst‖ ^ 2 - ‖x.snd‖ ^ 2) / 2, x.fst * star x.snd))).comp x
      ((hasFDerivAt_quaternionNormDiff x).prodMk h₂)
  exact h

/-! ### Vertical and horizontal vectors

The fibre of `H^l` through `(p, q)` is the `S³`-orbit `u ↦ (up, uq)` of left
multiplication by unit quaternions (`quaternionHopfLeft_fiber`), so the
**vertical** space at `(p, q)` is `{(sp, sq) : s ∈ Im ℍ}`, of real dimension
`3`. A tangent vector `(u₁, u₂)` of `S⁷` is **horizontal** — orthogonal to
the point *and* to the whole vertical space — exactly when

  `u₁ p̄ + u₂ q̄ = 0`,

a single quaternionic equation cutting out a `4`-dimensional real subspace
(`quaternionHopfLeft_horizontal_eq_zero`); indeed
`⟪(sp, sq), u⟫ = Re(s · conj(u₁p̄ + u₂q̄))`, and taking `s = 1, i, j, k` recovers
the four real components. For `H^r` the fibres are the *right* orbits
`u ↦ (pu, qu)`, the vertical space is `{(ps, qs) : s ∈ Im ℍ}`, and
horizontality reads `p̄ u₁ + q̄ u₂ = 0`. -/

/-- **Eng.** `WithLp` eta. -/
theorem quaternion_prod_eta (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    WithLp.toLp 2 (x.fst, x.snd) = x := rfl

/-- **Math.** The inner product against a point of `ℍ²`, in algebraic form:
`⟪(p, q), u⟫ = Re(u₁p̄ + u₂q̄)`. -/
theorem real_inner_quaternion_point (p q : ℍ[ℝ]) (u : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    ⟪WithLp.toLp 2 (p, q), u⟫_ℝ = (u.fst * star p + u.snd * star q).re := by
  rw [real_inner_quaternion_prod, quaternion_re_add]
  show (p * star u.fst).re + (q * star u.snd).re = _
  rw [quaternion_re_mul_star_comm p u.fst, quaternion_re_mul_star_comm q u.snd]

/-- **Math.** `real_inner_quaternion_point` with the base point given as a
vector of `ℍ²` rather than a pair. -/
theorem real_inner_quaternion_point' (x u : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    ⟪x, u⟫_ℝ = (u.fst * star x.fst + u.snd * star x.snd).re :=
  real_inner_quaternion_point x.fst x.snd u

/-- **Math.** The **vertical vector** `(sp, sq)` of `H^l` at `(p, q)`: the
velocity of the fibre `t ↦ (exp(ts)p, exp(ts)q)` for `s ∈ Im ℍ`. -/
def quaternionHopfLeftVertical (p q s : ℍ[ℝ]) : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) :=
  WithLp.toLp 2 (s * p, s * q)

/-- **Math.** The **vertical vector** `(ps, qs)` of `H^r` at `(p, q)`. -/
def quaternionHopfRightVertical (p q s : ℍ[ℝ]) : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) :=
  WithLp.toLp 2 (p * s, q * s)

/-- **Math.** The key expansion: the inner product of a vertical vector of
`H^l` against any `u` is `Re(s · conj(u₁p̄ + u₂q̄))`. -/
theorem real_inner_quaternionHopfLeftVertical (p q s : ℍ[ℝ])
    (u : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    ⟪quaternionHopfLeftVertical p q s, u⟫_ℝ
      = (s * star (u.fst * star p + u.snd * star q)).re := by
  rw [real_inner_quaternion_prod]
  show (s * p * star u.fst).re + (s * q * star u.snd).re = _
  have h : s * star (u.fst * star p + u.snd * star q)
      = s * p * star u.fst + s * q * star u.snd := by
    simp only [star_add, star_mul, star_star]; noncomm_ring
  rw [h, quaternion_re_add]

/-- **Math.** The same expansion for `H^r`: `⟪(ps, qs), u⟫ = Re(s · conj(p̄u₁ + q̄u₂))`. -/
theorem real_inner_quaternionHopfRightVertical (p q s : ℍ[ℝ])
    (u : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    ⟪quaternionHopfRightVertical p q s, u⟫_ℝ
      = (s * star (star p * u.fst + star q * u.snd)).re := by
  rw [real_inner_quaternion_prod]
  show (p * s * star u.fst).re + (q * s * star u.snd).re = _
  have h : s * star (star p * u.fst + star q * u.snd)
      = s * star u.fst * p + s * star u.snd * q := by
    simp only [star_add, star_mul, star_star]; noncomm_ring
  rw [h, quaternion_re_add]
  congr 1
  · rw [mul_assoc]; exact quaternion_re_mul_comm p (s * star u.fst)
  · rw [mul_assoc]; exact quaternion_re_mul_comm q (s * star u.snd)

/-- **Math.** Vertical vectors of `H^l` are tangent to `S⁷`: the fibres lie on
the sphere. -/
theorem real_inner_quaternionHopfLeftVertical_point (p q s : ℍ[ℝ]) (hs : s.re = 0) :
    ⟪WithLp.toLp 2 (p, q), quaternionHopfLeftVertical p q s⟫_ℝ = 0 := by
  rw [real_inner_quaternion_prod]
  show (p * star (s * p)).re + (q * star (s * q)).re = 0
  have e1 : p * star (s * p) = ((‖p‖ ^ 2 : ℝ) : ℍ[ℝ]) * star s := by
    rw [star_mul, ← mul_assoc, quaternion_self_mul_star]
  have e2 : q * star (s * q) = ((‖q‖ ^ 2 : ℝ) : ℍ[ℝ]) * star s := by
    rw [star_mul, ← mul_assoc, quaternion_self_mul_star]
  rw [e1, e2, quaternion_re_coe_mul, quaternion_re_coe_mul, Quaternion.re_star, hs]
  ring

/-- **Math.** Vertical vectors of `H^r` are tangent to `S⁷`. -/
theorem real_inner_quaternionHopfRightVertical_point (p q s : ℍ[ℝ]) (hs : s.re = 0) :
    ⟪WithLp.toLp 2 (p, q), quaternionHopfRightVertical p q s⟫_ℝ = 0 := by
  rw [real_inner_quaternion_prod]
  show (p * star (p * s)).re + (q * star (q * s)).re = 0
  have e1 : (p * star (p * s)).re = ‖p‖ ^ 2 * (star s).re := by
    rw [star_mul, ← mul_assoc, quaternion_re_mul_comm, ← mul_assoc,
      quaternion_star_mul_self, quaternion_re_coe_mul]
  have e2 : (q * star (q * s)).re = ‖q‖ ^ 2 * (star s).re := by
    rw [star_mul, ← mul_assoc, quaternion_re_mul_comm, ← mul_assoc,
      quaternion_star_mul_self, quaternion_re_coe_mul]
  rw [e1, e2, Quaternion.re_star, hs]
  ring

/-- **Math.** The differential of `H^l` **kills the vertical direction**:
`DH^l(sp, sq) = (|p|²Re s − |q|²Re s, p̄(s̄ + s)q) = 0` for `s ∈ Im ℍ`. -/
theorem quaternionHopfLeftDeriv_vertical (p q s : ℍ[ℝ]) (hs : s.re = 0) :
    quaternionHopfLeftDeriv p q (quaternionHopfLeftVertical p q s) = 0 := by
  have hss : star s + s = 0 := by
    apply Quaternion.ext <;> simp [hs]
  apply WithLp.ofLp_injective
  refine Prod.ext ?_ ?_
  · show ⟪p, s * p⟫_ℝ - ⟪q, s * q⟫_ℝ = (0 : WithLp 2 (ℝ × ℍ[ℝ])).fst
    have h := real_inner_quaternionHopfLeftVertical_point p q s hs
    rw [real_inner_quaternion_prod] at h
    show ⟪p, s * p⟫_ℝ - ⟪q, s * q⟫_ℝ = 0
    have e1 : (p * star (s * p)).re = ‖p‖ ^ 2 * (star s).re := by
      rw [star_mul, ← mul_assoc, quaternion_self_mul_star, quaternion_re_coe_mul]
    have e2 : (q * star (s * q)).re = ‖q‖ ^ 2 * (star s).re := by
      rw [star_mul, ← mul_assoc, quaternion_self_mul_star, quaternion_re_coe_mul]
    rw [real_inner_quaternion, real_inner_quaternion, e1, e2, Quaternion.re_star, hs]
    ring
  · show star (s * p) * q + star p * (s * q) = (0 : WithLp 2 (ℝ × ℍ[ℝ])).snd
    show star (s * p) * q + star p * (s * q) = 0
    have e : star (s * p) * q + star p * (s * q) = star p * (star s + s) * q := by
      simp only [star_mul]; noncomm_ring
    rw [e, hss]
    simp

/-- **Math.** The differential of `H^r` kills its vertical direction. -/
theorem quaternionHopfRightDeriv_vertical (p q s : ℍ[ℝ]) (hs : s.re = 0) :
    quaternionHopfRightDeriv p q (quaternionHopfRightVertical p q s) = 0 := by
  have hss : s + star s = 0 := by
    apply Quaternion.ext <;> simp [hs]
  apply WithLp.ofLp_injective
  refine Prod.ext ?_ ?_
  · show ⟪p, p * s⟫_ℝ - ⟪q, q * s⟫_ℝ = 0
    have e1 : (p * star (p * s)).re = ‖p‖ ^ 2 * (star s).re := by
      rw [star_mul, ← mul_assoc, quaternion_re_mul_comm, ← mul_assoc,
        quaternion_star_mul_self, quaternion_re_coe_mul]
    have e2 : (q * star (q * s)).re = ‖q‖ ^ 2 * (star s).re := by
      rw [star_mul, ← mul_assoc, quaternion_re_mul_comm, ← mul_assoc,
        quaternion_star_mul_self, quaternion_re_coe_mul]
    rw [real_inner_quaternion, real_inner_quaternion, e1, e2, Quaternion.re_star, hs]
    ring
  · show p * s * star q + p * star (q * s) = 0
    have e : p * s * star q + p * star (q * s) = p * (s + star s) * star q := by
      simp only [star_mul]; noncomm_ring
    rw [e, hss]
    simp

/-- **Math.** Petersen Exercise 1.6.22: a tangent vector of `S⁷` orthogonal to
the whole vertical space of `H^l` satisfies the horizontality equation
`u₁p̄ + u₂q̄ = 0`. Testing `⟪(sp, sq), u⟫ = Re(s · conj A)` against
`s = i, j, k` kills the three imaginary components of `A = u₁p̄ + u₂q̄`, and
orthogonality to the point `(p, q)` kills its real part. -/
theorem quaternionHopfLeft_horizontal_eq_zero (p q : ℍ[ℝ])
    (u : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]))
    (hp : (u.fst * star p + u.snd * star q).re = 0)
    (hv : ∀ s : ℍ[ℝ], s.re = 0 →
      ⟪quaternionHopfLeftVertical p q s, u⟫_ℝ = 0) :
    u.fst * star p + u.snd * star q = 0 := by
  set A : ℍ[ℝ] := u.fst * star p + u.snd * star q with hA
  have hv' : ∀ s : ℍ[ℝ], s.re = 0 → (s * star A).re = 0 := by
    intro s hs
    have h := hv s hs
    rw [real_inner_quaternionHopfLeftVertical, ← hA] at h
    exact h
  have h1 := hv' ⟨0, 1, 0, 0⟩ rfl
  have h2 := hv' ⟨0, 0, 1, 0⟩ rfl
  have h3 := hv' ⟨0, 0, 0, 1⟩ rfl
  rw [quaternion_re_mul_star_expand] at h1 h2 h3
  simp only [zero_mul, one_mul, zero_add, add_zero] at h1 h2 h3
  exact quaternion_eq_zero A hp h1 h2 h3

/-- **Math.** The horizontality equation for `H^r`: `p̄u₁ + q̄u₂ = 0`. -/
theorem quaternionHopfRight_horizontal_eq_zero (p q : ℍ[ℝ])
    (u : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]))
    (hp : (u.fst * star p + u.snd * star q).re = 0)
    (hv : ∀ s : ℍ[ℝ], s.re = 0 →
      ⟪quaternionHopfRightVertical p q s, u⟫_ℝ = 0) :
    star p * u.fst + star q * u.snd = 0 := by
  have hp' : (star p * u.fst + star q * u.snd).re = 0 := by
    rw [quaternion_re_add] at hp
    rw [quaternion_re_add, quaternion_re_mul_comm (star p) u.fst,
      quaternion_re_mul_comm (star q) u.snd]
    exact hp
  set B : ℍ[ℝ] := star p * u.fst + star q * u.snd with hB
  have hv' : ∀ s : ℍ[ℝ], s.re = 0 → (s * star B).re = 0 := by
    intro s hs
    have h := hv s hs
    rw [real_inner_quaternionHopfRightVertical, ← hB] at h
    exact h
  have h1 := hv' ⟨0, 1, 0, 0⟩ rfl
  have h2 := hv' ⟨0, 0, 1, 0⟩ rfl
  have h3 := hv' ⟨0, 0, 0, 1⟩ rfl
  rw [quaternion_re_mul_star_expand] at h1 h2 h3
  simp only [zero_mul, one_mul, zero_add, add_zero] at h1 h2 h3
  exact quaternion_eq_zero B hp' h1 h2 h3

/-! ### The differential is an isometry on horizontal vectors

This is the heart of the computation. With `S = q ū₂`, `S' = q v̄₂` and the
horizontality relations `u₁p̄ = −u₂q̄`, `p ū₁ = −q ū₂` one gets

* `|p|²⟪u₁, v₁⟫ = ⟪u₁p̄, p v̄₁⟫ = ⟪u₂q̄, q v̄₂⟫ = |q|²⟪u₂, v₂⟫`;
* `Re(S S̄') = |q|²⟪u₂, v₂⟫`;
* `Re(S S̄') = 2 Re(S) Re(S') − Re(S S')` (polarization);

and the four cross terms of `⟪DH(u), DH(v)⟫` combine, using `|p|² + |q|² = 1`,
to exactly `⟪u, v⟫`. -/

/-- **Math.** The algebraic core: `DH^l` preserves inner products of
horizontal vectors on the unit sphere. -/
theorem quaternionHopfLeft_inner_deriv_algebra (p q u₁ u₂ v₁ v₂ : ℍ[ℝ])
    (hpq : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1)
    (hu : u₁ * star p + u₂ * star q = 0) (hv : v₁ * star p + v₂ * star q = 0) :
    ((p * star u₁).re - (q * star u₂).re) * ((p * star v₁).re - (q * star v₂).re)
      + ((star u₁ * q + star p * u₂) * star (star v₁ * q + star p * v₂)).re
    = (u₁ * star v₁).re + (u₂ * star v₂).re := by
  have hu' : p * star u₁ + q * star u₂ = 0 := by
    have := congrArg star hu; simpa [star_add, star_mul, mul_comm] using this
  have hv' : p * star v₁ + q * star v₂ = 0 := by
    have := congrArg star hv; simpa [star_add, star_mul, mul_comm] using this
  have hu1 : u₁ * star p = -(u₂ * star q) := by linear_combination (norm := module) hu
  have hu2 : p * star u₁ = -(q * star u₂) := by linear_combination (norm := module) hu'
  have hv1 : v₁ * star p = -(v₂ * star q) := by linear_combination (norm := module) hv
  have hv2 : p * star v₁ = -(q * star v₂) := by linear_combination (norm := module) hv'
  set S := q * star u₂ with hS
  set S' := q * star v₂ with hS'
  set A := (u₁ * star v₁).re with hA
  set B := (u₂ * star v₂).re with hB
  have key1 : ‖p‖ ^ 2 * A = ‖q‖ ^ 2 * B := by
    have e : (u₁ * star p) * (p * star v₁) = (u₂ * star q) * (q * star v₂) := by
      rw [hu1, hv2, hS']; noncomm_ring
    have eL : (u₁ * star p) * (p * star v₁)
        = ((‖p‖ ^ 2 : ℝ) : ℍ[ℝ]) * (u₁ * star v₁) := by
      calc (u₁ * star p) * (p * star v₁) = u₁ * (star p * p) * star v₁ := by noncomm_ring
        _ = u₁ * ((‖p‖ ^ 2 : ℝ) : ℍ[ℝ]) * star v₁ := by rw [quaternion_star_mul_self]
        _ = ((‖p‖ ^ 2 : ℝ) : ℍ[ℝ]) * (u₁ * star v₁) := quaternion_coe_mid _ _ _
    have eR : (u₂ * star q) * (q * star v₂)
        = ((‖q‖ ^ 2 : ℝ) : ℍ[ℝ]) * (u₂ * star v₂) := by
      calc (u₂ * star q) * (q * star v₂) = u₂ * (star q * q) * star v₂ := by noncomm_ring
        _ = u₂ * ((‖q‖ ^ 2 : ℝ) : ℍ[ℝ]) * star v₂ := by rw [quaternion_star_mul_self]
        _ = ((‖q‖ ^ 2 : ℝ) : ℍ[ℝ]) * (u₂ * star v₂) := quaternion_coe_mid _ _ _
    have h := congrArg (fun z : ℍ[ℝ] => z.re) (eL.symm.trans (e.trans eR))
    simp only at h
    rw [quaternion_re_coe_mul, quaternion_re_coe_mul] at h
    exact h
  have key3 : (S * star S').re = ‖q‖ ^ 2 * B := by
    have e : S * star S' = q * (star u₂ * v₂) * star q := by
      rw [hS, hS']; simp only [star_mul, star_star]; noncomm_ring
    rw [e, quaternion_re_mul_comm, ← mul_assoc, quaternion_star_mul_self,
      quaternion_re_coe_mul, hB]
    congr 1
    rw [quaternion_re_mul_comm, quaternion_re_mul_star_comm]
  have key2 : (S * star S').re = 2 * S.re * S'.re - (S * S').re :=
    quaternion_re_mul_star S S'
  have hb : (star u₁ * q + star p * u₂) * star (star v₁ * q + star p * v₂)
      = star u₁ * q * (star q * v₁) + star u₁ * q * (star v₂ * p)
        + star p * u₂ * (star q * v₁) + star p * u₂ * (star v₂ * p) := by
    simp only [star_add, star_mul, star_star]; noncomm_ring
  have t1 : (star u₁ * q * (star q * v₁)).re = ‖q‖ ^ 2 * A := by
    have e : star u₁ * q * (star q * v₁) = star u₁ * (q * star q) * v₁ := by noncomm_ring
    rw [e, quaternion_self_mul_star, quaternion_coe_mid, quaternion_re_coe_mul, hA]
    congr 1
    rw [quaternion_re_mul_comm, quaternion_re_mul_star_comm]
  have t4 : (star p * u₂ * (star v₂ * p)).re = ‖p‖ ^ 2 * B := by
    have e : star p * u₂ * (star v₂ * p) = star p * (u₂ * star v₂ * p) := by noncomm_ring
    rw [e, quaternion_re_mul_comm, mul_assoc, quaternion_self_mul_star,
      quaternion_re_mul_coe, hB]
  have t2 : (star u₁ * q * (star v₂ * p)).re = -(S * S').re := by
    have e : star u₁ * q * (star v₂ * p) = (star u₁ * S') * p := by rw [hS']; noncomm_ring
    rw [e, quaternion_re_mul_comm, ← mul_assoc, hu2]; simp
  have t3 : (star p * u₂ * (star q * v₁)).re = -(S * S').re := by
    have e : star p * u₂ * (star q * v₁) = (star p * (u₂ * star q)) * v₁ := by noncomm_ring
    rw [e, quaternion_re_mul_comm, ← mul_assoc, hv1, neg_mul, quaternion_re_neg]
    congr 1
    have h : star ((v₂ * star q) * (u₂ * star q)) = S * S' := by
      rw [hS, hS']; simp only [star_mul, star_star]
    rw [← h, Quaternion.re_star]
  rw [hb]
  simp only [quaternion_re_add, t1, t2, t3, t4, hu2, hv2, quaternion_re_neg]
  linear_combination (A + B) * hpq - key1 - 2 * (key3.symm.trans key2)

/-- **Math.** The algebraic core for `H^r`, obtained from the left case by
conjugating all six arguments (conjugation is an `ℝ`-linear isometry of `ℍ`
exchanging left and right multiplication). -/
theorem quaternionHopfRight_inner_deriv_algebra (p q u₁ u₂ v₁ v₂ : ℍ[ℝ])
    (hpq : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1)
    (hu : star p * u₁ + star q * u₂ = 0) (hv : star p * v₁ + star q * v₂ = 0) :
    ((p * star u₁).re - (q * star u₂).re) * ((p * star v₁).re - (q * star v₂).re)
      + ((u₁ * star q + p * star u₂) * star (v₁ * star q + p * star v₂)).re
    = (u₁ * star v₁).re + (u₂ * star v₂).re := by
  have hu' : star u₁ * p + star u₂ * q = 0 := by
    have := congrArg star hu; simpa [star_add, star_mul] using this
  have hv' : star v₁ * p + star v₂ * q = 0 := by
    have := congrArg star hv; simpa [star_add, star_mul] using this
  have h := quaternionHopfLeft_inner_deriv_algebra (star p) (star q) (star u₁) (star u₂)
    (star v₁) (star v₂) (by rw [norm_star, norm_star]; exact hpq)
    (by simpa only [star_star] using hu') (by simpa only [star_star] using hv')
  simp only [star_star] at h
  have e : ∀ a b : ℍ[ℝ], (star a * b).re = (b * star a).re :=
    fun a b => quaternion_re_mul_comm _ _
  rw [e p u₁, e q u₂, e p v₁, e q v₂, e u₁ v₁, e u₂ v₂] at h
  rw [quaternion_re_mul_star_comm u₁ p, quaternion_re_mul_star_comm u₂ q,
    quaternion_re_mul_star_comm v₁ p, quaternion_re_mul_star_comm v₂ q] at h
  rw [quaternion_re_mul_star_comm v₁ u₁, quaternion_re_mul_star_comm v₂ u₂] at h
  exact h

/-- **Math.** `DH^l` is an isometry on horizontal vectors of `S⁷(1)`. -/
theorem real_inner_quaternionHopfLeftDeriv (p q : ℍ[ℝ])
    (hpq : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1) (u v : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]))
    (hu : u.fst * star p + u.snd * star q = 0)
    (hv : v.fst * star p + v.snd * star q = 0) :
    ⟪quaternionHopfLeftDeriv p q u, quaternionHopfLeftDeriv p q v⟫_ℝ = ⟪u, v⟫_ℝ := by
  rw [real_inner_real_quaternion_prod, real_inner_quaternion_prod]
  simp only [quaternionHopfLeftDeriv_fst, quaternionHopfLeftDeriv_snd,
    real_inner_quaternion]
  exact quaternionHopfLeft_inner_deriv_algebra p q u.fst u.snd v.fst v.snd hpq hu hv

/-- **Math.** `DH^r` is an isometry on horizontal vectors of `S⁷(1)`. -/
theorem real_inner_quaternionHopfRightDeriv (p q : ℍ[ℝ])
    (hpq : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1) (u v : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]))
    (hu : star p * u.fst + star q * u.snd = 0)
    (hv : star p * v.fst + star q * v.snd = 0) :
    ⟪quaternionHopfRightDeriv p q u, quaternionHopfRightDeriv p q v⟫_ℝ = ⟪u, v⟫_ℝ := by
  rw [real_inner_real_quaternion_prod, real_inner_quaternion_prod]
  simp only [quaternionHopfRightDeriv_fst, quaternionHopfRightDeriv_snd,
    real_inner_quaternion]
  exact quaternionHopfRight_inner_deriv_algebra p q u.fst u.snd v.fst v.snd hpq hu hv

/-! ### The horizontal frame

The horizontal space is a *left* `ℍ`-submodule for `H^l` (and a *right* one
for `H^r`), free of rank one: `u ↦ l·u` preserves `u₁p̄ + u₂q̄ = 0`. So a
single unit horizontal vector `k` generates an orthonormal frame
`l ↦ l·k`, `l ∈ {1, i, j, k}`. Such a `k` exists at every point of `S⁷`:
`k = |p|⁻¹(−q̄p, |p|)` if `p ≠ 0` (then `‖k‖² = |q|² + |p|² = 1`), and
`k = (1, 0)` if `p = 0`. -/

/-- **Math.** Left multiplication of a vector of `ℍ²` by a quaternion. -/
def quaternionLeftLift (l : ℍ[ℝ]) (k : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) :=
  WithLp.toLp 2 (l * k.fst, l * k.snd)

/-- **Math.** Right multiplication of a vector of `ℍ²` by a quaternion. -/
def quaternionRightLift (l : ℍ[ℝ]) (k : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    WithLp 2 (ℍ[ℝ] × ℍ[ℝ]) :=
  WithLp.toLp 2 (k.fst * l, k.snd * l)

/-- **Math.** `l ↦ l·k` is a similarity of `ℍ` onto the left `ℍ`-line of `k`:
`⟪l·k, m·k⟫ = Re(l m̄)·‖k‖²`. -/
theorem real_inner_quaternionLeftLift (l m : ℍ[ℝ]) (k : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    ⟪quaternionLeftLift l k, quaternionLeftLift m k⟫_ℝ
      = (l * star m).re * (‖k.fst‖ ^ 2 + ‖k.snd‖ ^ 2) := by
  have e : ∀ a : ℍ[ℝ], ((l * a) * star (m * a)).re = ‖a‖ ^ 2 * (l * star m).re := by
    intro a
    have h : (l * a) * star (m * a) = l * (a * star a) * star m := by
      simp only [star_mul]; noncomm_ring
    rw [h, quaternion_self_mul_star, quaternion_coe_mid, quaternion_re_coe_mul]
  rw [real_inner_quaternion_prod]
  show ((l * k.fst) * star (m * k.fst)).re + ((l * k.snd) * star (m * k.snd)).re = _
  rw [e, e]
  ring

/-- **Math.** `l ↦ k·l` is a similarity of `ℍ` onto the right `ℍ`-line of `k`. -/
theorem real_inner_quaternionRightLift (l m : ℍ[ℝ]) (k : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) :
    ⟪quaternionRightLift l k, quaternionRightLift m k⟫_ℝ
      = (l * star m).re * (‖k.fst‖ ^ 2 + ‖k.snd‖ ^ 2) := by
  have e : ∀ a : ℍ[ℝ], ((a * l) * star (a * m)).re = ‖a‖ ^ 2 * (l * star m).re := by
    intro a
    have h : (a * l) * star (a * m) = a * (l * star m) * star a := by
      simp only [star_mul]; noncomm_ring
    rw [h, quaternion_re_mul_comm, ← mul_assoc, quaternion_star_mul_self,
      quaternion_re_coe_mul]
  rw [real_inner_quaternion_prod]
  show ((k.fst * l) * star (k.fst * m)).re + ((k.snd * l) * star (k.snd * m)).re = _
  rw [e, e]
  ring

/-- **Math.** Left multiples of a horizontal vector are horizontal (`H^l`). -/
theorem quaternionLeftLift_horizontal (p q l : ℍ[ℝ]) (k : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]))
    (hk : k.fst * star p + k.snd * star q = 0) :
    (quaternionLeftLift l k).fst * star p + (quaternionLeftLift l k).snd * star q = 0 := by
  show (l * k.fst) * star p + (l * k.snd) * star q = 0
  have e : (l * k.fst) * star p + (l * k.snd) * star q
      = l * (k.fst * star p + k.snd * star q) := by noncomm_ring
  rw [e, hk, mul_zero]

/-- **Math.** Right multiples of a horizontal vector are horizontal (`H^r`). -/
theorem quaternionRightLift_horizontal (p q l : ℍ[ℝ]) (k : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]))
    (hk : star p * k.fst + star q * k.snd = 0) :
    star p * (quaternionRightLift l k).fst + star q * (quaternionRightLift l k).snd = 0 := by
  show star p * (k.fst * l) + star q * (k.snd * l) = 0
  have e : star p * (k.fst * l) + star q * (k.snd * l)
      = (star p * k.fst + star q * k.snd) * l := by noncomm_ring
  rw [e, hk, zero_mul]

/-- **Math.** Every point of `S⁷(1)` carries a **unit horizontal vector** for
`H^l`. If `p ≠ 0` take `k = |p|⁻¹(−q̄p, |p|)`: horizontality is
`−|p|⁻¹ q̄ p p̄ + |p| q̄ = −|p| q̄ + |p| q̄ = 0`, and
`‖k‖² = |p|⁻²|q|²|p|² + |p|² = |q|² + |p|² = 1`. If `p = 0` take `k = (1, 0)`. -/
theorem exists_quaternionHopfLeftUnitHorizontal (p q : ℍ[ℝ])
    (hpq : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1) :
    ∃ k : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]),
      k.fst * star p + k.snd * star q = 0 ∧ ‖k.fst‖ ^ 2 + ‖k.snd‖ ^ 2 = 1 := by
  by_cases hp : p = 0
  · have hq : ‖q‖ ^ 2 = 1 := by rw [hp] at hpq; simpa using hpq
    refine ⟨WithLp.toLp 2 ((1 : ℍ[ℝ]), (0 : ℍ[ℝ])), ?_, ?_⟩
    · show (1 : ℍ[ℝ]) * star p + (0 : ℍ[ℝ]) * star q = 0
      rw [hp]; simp
    · show ‖(1 : ℍ[ℝ])‖ ^ 2 + ‖(0 : ℍ[ℝ])‖ ^ 2 = 1
      simp
  · have hpn : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
    refine ⟨WithLp.toLp 2 (-((‖p‖ : ℝ)⁻¹ • (star q * p)), ((‖p‖ : ℝ) : ℍ[ℝ])), ?_, ?_⟩
    · show -((‖p‖ : ℝ)⁻¹ • (star q * p)) * star p + ((‖p‖ : ℝ) : ℍ[ℝ]) * star q = 0
      have e : (star q * p) * star p = ((‖p‖ ^ 2 : ℝ) : ℍ[ℝ]) * star q := by
        rw [mul_assoc, quaternion_self_mul_star, Quaternion.mul_coe_eq_smul,
          Quaternion.coe_mul_eq_smul]
      rw [neg_mul, smul_mul_assoc, e, Quaternion.coe_mul_eq_smul,
        Quaternion.coe_mul_eq_smul, smul_smul]
      rw [show (‖p‖ : ℝ)⁻¹ * ‖p‖ ^ 2 = ‖p‖ by field_simp]
      simp
    · show ‖-((‖p‖ : ℝ)⁻¹ • (star q * p))‖ ^ 2 + ‖((‖p‖ : ℝ) : ℍ[ℝ])‖ ^ 2 = 1
      have h1 : ‖-((‖p‖ : ℝ)⁻¹ • (star q * p))‖ = ‖q‖ := by
        rw [norm_neg, norm_smul, norm_mul, norm_star, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < (‖p‖ : ℝ)⁻¹)]
        field_simp
      have h2 : ‖((‖p‖ : ℝ) : ℍ[ℝ])‖ = ‖p‖ := by
        rw [Quaternion.norm_coe, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg p)]
      rw [h1, h2]
      linarith [hpq]

/-- **Math.** Every point of `S⁷(1)` carries a unit horizontal vector for
`H^r`; if `p ≠ 0` take `k = |p|⁻¹(−p q̄, |p|)`. -/
theorem exists_quaternionHopfRightUnitHorizontal (p q : ℍ[ℝ])
    (hpq : ‖p‖ ^ 2 + ‖q‖ ^ 2 = 1) :
    ∃ k : WithLp 2 (ℍ[ℝ] × ℍ[ℝ]),
      star p * k.fst + star q * k.snd = 0 ∧ ‖k.fst‖ ^ 2 + ‖k.snd‖ ^ 2 = 1 := by
  by_cases hp : p = 0
  · refine ⟨WithLp.toLp 2 ((1 : ℍ[ℝ]), (0 : ℍ[ℝ])), ?_, ?_⟩
    · show star p * (1 : ℍ[ℝ]) + star q * (0 : ℍ[ℝ]) = 0
      rw [hp]; simp
    · show ‖(1 : ℍ[ℝ])‖ ^ 2 + ‖(0 : ℍ[ℝ])‖ ^ 2 = 1
      simp
  · have hpn : (0 : ℝ) < ‖p‖ := norm_pos_iff.mpr hp
    refine ⟨WithLp.toLp 2 (-((‖p‖ : ℝ)⁻¹ • (p * star q)), ((‖p‖ : ℝ) : ℍ[ℝ])), ?_, ?_⟩
    · show star p * -((‖p‖ : ℝ)⁻¹ • (p * star q)) + star q * ((‖p‖ : ℝ) : ℍ[ℝ]) = 0
      have e : star p * (p * star q) = ((‖p‖ ^ 2 : ℝ) : ℍ[ℝ]) * star q := by
        rw [← mul_assoc, quaternion_star_mul_self]
      rw [mul_neg, mul_smul_comm, e, Quaternion.coe_mul_eq_smul,
        Quaternion.mul_coe_eq_smul, smul_smul]
      rw [show (‖p‖ : ℝ)⁻¹ * ‖p‖ ^ 2 = ‖p‖ by field_simp]
      simp
    · show ‖-((‖p‖ : ℝ)⁻¹ • (p * star q))‖ ^ 2 + ‖((‖p‖ : ℝ) : ℍ[ℝ])‖ ^ 2 = 1
      have h1 : ‖-((‖p‖ : ℝ)⁻¹ • (p * star q))‖ = ‖q‖ := by
        rw [norm_neg, norm_smul, norm_mul, norm_star, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < (‖p‖ : ℝ)⁻¹)]
        field_simp
      have h2 : ‖((‖p‖ : ℝ) : ℍ[ℝ])‖ = ‖p‖ := by
        rw [Quaternion.norm_coe, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg p)]
      rw [h1, h2]
      linarith [hpq]

/-! ### The generic sphere-submersion bridge

Both quaternionic Hopf maps (and, for that matter, the complex `hopfMap` of
Example 1.1.5) fit the following pattern: an ambient `C^∞` map `f : X → Y`
with `|f(x)| = |x|²/2` restricts to `F : S(X, 1) → S(Y, 1/2)`; at each point
of the unit sphere its differential kills a "vertical" family of tangent
vectors, is an isometry on the vectors orthogonal to the point and to that
family, and admits an orthonormal horizontal frame of the target dimension.
Then `F` is a Riemannian submersion. -/

private theorem isRiemannianSubmersion_sphere_of_ambient
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    {n m : ℕ} [Fact (finrank ℝ X = n + 1)] [Fact (finrank ℝ Y = m + 1)]
    (hm : 0 < m)
    (f : X → Y) (Df : X → (X →L[ℝ] Y))
    (hderiv : ∀ x : X, HasFDerivAt f (Df x) x)
    (hsmooth : ContDiff ℝ ∞ f)
    (hnorm : ∀ x : X, ‖f x‖ = ‖x‖ ^ 2 / 2)
    (F : sphere (0 : X) 1 → sphere (0 : Y) (1 / 2))
    (hF : ∀ x : sphere (0 : X) 1, (F x : Y) = f (x : X))
    (vert : X → X → Prop)
    (hvert_tangent : ∀ x w : X, vert x w → ⟪x, w⟫_ℝ = 0)
    (hvert_ker : ∀ x w : X, vert x w → Df x w = 0)
    (hiso : ∀ x : X, ‖x‖ = 1 → ∀ u v : X,
        ⟪x, u⟫_ℝ = 0 → (∀ w, vert x w → ⟪w, u⟫_ℝ = 0) →
        ⟪x, v⟫_ℝ = 0 → (∀ w, vert x w → ⟪w, v⟫_ℝ = 0) →
        ⟪Df x u, Df x v⟫_ℝ = ⟪u, v⟫_ℝ)
    (hframe : ∀ x : X, ‖x‖ = 1 → ∃ h : Fin m → X, Orthonormal ℝ h ∧
        (∀ i, ⟪x, h i⟫_ℝ = 0) ∧ ∀ i w, vert x w → ⟪w, h i⟫_ℝ = 0) :
    IsRiemannianSubmersion (sphereMetricUnit (n := n) X)
      (sphereMetric (n := m) Y (1 / 2)) F := by
  haveI : NormSMulClass ℝ Y := NormedSpace.toNormSMulClass
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hmem2 : ∀ x : sphere (0 : X) 1, (2 : ℝ) • f (x : X) ∈ sphere (0 : Y) 1 := by
    intro x
    rw [mem_sphere_zero_iff_norm, norm_smul, hnorm, mem_sphere_zero_iff_norm.mp x.2]
    norm_num
  -- smoothness of the restriction
  have hFsmooth : ContMDiff (𝓡 n) (𝓡 m) ∞ F := by
    have key : F = ⇑(sphereHomeomorphUnitSphere (E := Y) (1 / 2)).symm ∘
        Set.codRestrict (fun x : sphere (0 : X) 1 => (2 : ℝ) • f (x : X))
          (sphere (0 : Y) 1) hmem2 := by
      funext x
      refine Subtype.ext ?_
      show (F x : Y) = (1 / 2 : ℝ) • ((2 : ℝ) • f (x : X))
      rw [hF]
      module
    rw [key]
    refine (contMDiff_sphereHomeomorphUnitSphere_symm (1 / 2)).comp ?_
    exact ContMDiff.codRestrict_sphere
      (((contDiff_const_smul (2 : ℝ)).contMDiff).comp
        (hsmooth.contMDiff.comp contMDiff_coe_sphere)) hmem2
  -- the chain-rule bridge `Dι' ∘ DF = Df ∘ Dι`
  have hbridge : ∀ (x : sphere (0 : X) 1) (u : TangentSpace (𝓡 n) x),
      mfderiv (𝓡 m) 𝓘(ℝ, Y) ((↑) : sphere (0 : Y) (1 / 2) → Y) (F x)
          (mfderiv (𝓡 n) (𝓡 m) F x u)
        = Df (x : X) (mfderiv (𝓡 n) 𝓘(ℝ, X) ((↑) : sphere (0 : X) 1 → X) x u) := by
    intro x u
    have hFd : MDifferentiableAt (𝓡 n) (𝓡 m) F x := (hFsmooth x).mdifferentiableAt (by simp)
    have hι' : MDifferentiableAt (𝓡 m) 𝓘(ℝ, Y)
        ((↑) : sphere (0 : Y) (1 / 2) → Y) (F x) :=
      (contMDiff_coe_sphere_radius (m := 1) (1 / 2) (F x)).mdifferentiableAt one_ne_zero
    have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, X) ((↑) : sphere (0 : X) 1 → X) x :=
      (contMDiff_coe_sphere (m := 1) x).mdifferentiableAt one_ne_zero
    have hamb : MDifferentiableAt 𝓘(ℝ, X) 𝓘(ℝ, Y) f (x : X) :=
      (hderiv (x : X)).differentiableAt.mdifferentiableAt
    have h1 := mfderiv_comp x hι' hFd
    have h2 := mfderiv_comp x hamb hι
    have hfun : (((↑) : sphere (0 : Y) (1 / 2) → Y) ∘ F)
        = f ∘ ((↑) : sphere (0 : X) 1 → X) := by
      funext z; exact hF z
    have h3 : (mfderiv (𝓡 m) 𝓘(ℝ, Y) ((↑) : sphere (0 : Y) (1 / 2) → Y) (F x)).comp
          (mfderiv (𝓡 n) (𝓡 m) F x)
        = (mfderiv 𝓘(ℝ, X) 𝓘(ℝ, Y) f (x : X)).comp
            (mfderiv (𝓡 n) 𝓘(ℝ, X) ((↑) : sphere (0 : X) 1 → X) x) := by
      rw [← h1, hfun]; exact h2
    have h4 := DFunLike.congr_fun h3 u
    simpa [mfderiv_eq_fderiv, (hderiv (x : X)).fderiv] using h4
  -- a tangent vector orthogonal to `ker DF` has horizontal ambient image
  have hhoriz : ∀ (x : sphere (0 : X) 1) (u : TangentSpace (𝓡 n) x),
      (∀ w : TangentSpace (𝓡 n) x, mfderiv (𝓡 n) (𝓡 m) F x w = 0 →
        (sphereMetricUnit (n := n) X).metricInner x u w = 0) →
      ⟪(x : X), mfderiv (𝓡 n) 𝓘(ℝ, X) ((↑) : sphere (0 : X) 1 → X) x u⟫_ℝ = 0 ∧
        ∀ w : X, vert (x : X) w →
          ⟪w, mfderiv (𝓡 n) 𝓘(ℝ, X) ((↑) : sphere (0 : X) 1 → X) x u⟫_ℝ = 0 := by
    intro x u hu
    constructor
    · have hmem : mfderiv (𝓡 n) 𝓘(ℝ, X) ((↑) : sphere (0 : X) 1 → X) x u
          ∈ (mfderiv (𝓡 n) 𝓘(ℝ, X) ((↑) : sphere (0 : X) 1 → X) x :
            TangentSpace (𝓡 n) x →L[ℝ] X).range :=
        LinearMap.mem_range.mpr ⟨u, rfl⟩
      rw [range_mfderiv_coe_sphere x] at hmem
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem
    · intro w hw
      obtain ⟨tw, htw⟩ := exists_mfderiv_coe_sphere_eq (n := n) x
        (hvert_tangent (x : X) w hw)
      have htwker : mfderiv (𝓡 n) (𝓡 m) F x tw = 0 :=
        mfderiv_coe_sphere_radius_injective (1 / 2) (F x)
          (by rw [hbridge x tw, htw, hvert_ker (x : X) w hw]; exact (map_zero _).symm)
      have h := hu tw htwker
      rw [sphereMetricUnit_apply, htw] at h
      rw [real_inner_comm]
      exact h
  refine ⟨hFsmooth, ?_, ?_⟩
  · -- surjectivity of `DF`
    intro x
    obtain ⟨h, hon, htan, hvperp⟩ := hframe (x : X) (mem_sphere_zero_iff_norm.mp x.2)
    choose t ht using fun i => exists_mfderiv_coe_sphere_eq (n := n) x (htan i)
    set y : Fin m → TangentSpace (𝓡 m) (F x) :=
      fun i => mfderiv (𝓡 n) (𝓡 m) F x (t i) with hy_def
    have hy : ∀ i, mfderiv (𝓡 m) 𝓘(ℝ, Y) ((↑) : sphere (0 : Y) (1 / 2) → Y) (F x) (y i)
        = Df (x : X) (h i) := by
      intro i
      rw [hy_def, hbridge x (t i), ht i]
    have hon' : Orthonormal ℝ fun i => Df (x : X) (h i) := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [hiso (x : X) (mem_sphere_zero_iff_norm.mp x.2) (h i) (h j) (htan i)
        (fun w hw => hvperp i w hw) (htan j) (fun w hw => hvperp j w hw)]
      exact (orthonormal_iff_ite.mp hon) i j
    have hli : LinearIndependent ℝ y := by
      have hindep : LinearIndependent ℝ fun i => Df (x : X) (h i) := hon'.linearIndependent
      have hcomp : (fun i => Df (x : X) (h i))
          = (mfderiv (𝓡 m) 𝓘(ℝ, Y) ((↑) : sphere (0 : Y) (1 / 2) → Y) (F x)) ∘ y := by
        funext i; exact (hy i).symm
      rw [hcomp] at hindep
      exact hindep.of_comp
        (mfderiv (𝓡 m) 𝓘(ℝ, Y) ((↑) : sphere (0 : Y) (1 / 2) → Y) (F x)).toLinearMap
    have hspan : Submodule.span ℝ (Set.range y) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank
        (by rw [Fintype.card_fin]; exact (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm)
    intro z
    have hz : z ∈ Submodule.span ℝ (Set.range y) := by rw [hspan]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hz
    refine ⟨∑ i, c i • t i, ?_⟩
    rw [map_sum]
    simp only [map_smul]
    exact hc
  · -- the metric identity on the orthogonal complement of `ker DF`
    intro x u v hu hv
    obtain ⟨hu1, hu2⟩ := hhoriz x u hu
    obtain ⟨hv1, hv2⟩ := hhoriz x v hv
    rw [sphereMetricUnit_apply, sphereMetric_apply, hbridge x u, hbridge x v]
    exact (hiso (x : X) (mem_sphere_zero_iff_norm.mp x.2) _ _ hu1 hu2 hv1 hv2).symm

/-- **Math.** Petersen Exercise 1.6.22 (6): the **left quaternionic Hopf map**
`H^l : (S⁷(1), g) → (S⁴(1/2), g)` is a **Riemannian submersion** for the
canonical (round) sphere metrics.

At `(p, q)` the vertical space is the tangent to the `S³`-orbit of left
multiplication, `{(sp, sq) : s ∈ Im ℍ}`, which `DH^l` kills; a tangent vector
orthogonal to it satisfies `u₁p̄ + u₂q̄ = 0`, and on those `DH^l` preserves
inner products (`real_inner_quaternionHopfLeftDeriv`). Surjectivity comes from
the orthonormal horizontal frame `{1, i, j, k}·k` generated by a unit
horizontal vector `k` (`exists_quaternionHopfLeftUnitHorizontal`), whose four
images are orthonormal, hence span the `4`-dimensional tangent space of
`S⁴(1/2)`. -/
theorem quaternionHopfLeft_isRiemannianSubmersion :
    IsRiemannianSubmersion (sphereMetricUnit (n := 7) (WithLp 2 (ℍ[ℝ] × ℍ[ℝ])))
      (sphereMetric (n := 4) (WithLp 2 (ℝ × ℍ[ℝ])) (1 / 2)) quaternionHopfLeft := by
  refine isRiemannianSubmersion_sphere_of_ambient (by norm_num)
    quaternionHopfLeftAmbient (fun x => quaternionHopfLeftDeriv x.fst x.snd)
    hasFDerivAt_quaternionHopfLeftAmbient contDiff_quaternionHopfLeftAmbient
    norm_quaternionHopfLeftAmbient quaternionHopfLeft (fun _ => rfl)
    (fun x w => ∃ s : ℍ[ℝ], s.re = 0 ∧ w = quaternionHopfLeftVertical x.fst x.snd s)
    ?_ ?_ ?_ ?_
  · rintro x w ⟨s, hs, rfl⟩
    exact real_inner_quaternionHopfLeftVertical_point x.fst x.snd s hs
  · rintro x w ⟨s, hs, rfl⟩
    exact quaternionHopfLeftDeriv_vertical x.fst x.snd s hs
  · intro x hx u v hu1 hu2 hv1 hv2
    have hpq : ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1 := by
      rw [← WithLp.prod_norm_sq_eq_of_L2, hx, one_pow]
    rw [real_inner_quaternion_point'] at hu1 hv1
    refine real_inner_quaternionHopfLeftDeriv x.fst x.snd hpq u v ?_ ?_
    · exact quaternionHopfLeft_horizontal_eq_zero x.fst x.snd u hu1
        (fun s hs => hu2 _ ⟨s, hs, rfl⟩)
    · exact quaternionHopfLeft_horizontal_eq_zero x.fst x.snd v hv1
        (fun s hs => hv2 _ ⟨s, hs, rfl⟩)
  · intro x hx
    have hpq : ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1 := by
      rw [← WithLp.prod_norm_sq_eq_of_L2, hx, one_pow]
    obtain ⟨k, hk, hknorm⟩ := exists_quaternionHopfLeftUnitHorizontal x.fst x.snd hpq
    refine ⟨fun i => quaternionLeftLift (quaternionUnit i) k, ?_, ?_, ?_⟩
    · rw [orthonormal_iff_ite]
      intro i j
      rw [real_inner_quaternionLeftLift, hknorm, mul_one, quaternionUnit_re_mul_star]
    · intro i
      rw [real_inner_quaternion_point',
        quaternionLeftLift_horizontal x.fst x.snd (quaternionUnit i) k hk]
      rfl
    · rintro i w ⟨s, hs, rfl⟩
      rw [real_inner_quaternionHopfLeftVertical,
        quaternionLeftLift_horizontal x.fst x.snd (quaternionUnit i) k hk]
      simp

/-- **Math.** Petersen Exercise 1.6.22 (6): the **right quaternionic Hopf map**
`H^r : (S⁷(1), g) → (S⁴(1/2), g)` is a **Riemannian submersion**. Same proof
with the *right* `S³`-orbit `{(ps, qs) : s ∈ Im ℍ}` as vertical space and
horizontality `p̄u₁ + q̄u₂ = 0`. -/
theorem quaternionHopfRight_isRiemannianSubmersion :
    IsRiemannianSubmersion (sphereMetricUnit (n := 7) (WithLp 2 (ℍ[ℝ] × ℍ[ℝ])))
      (sphereMetric (n := 4) (WithLp 2 (ℝ × ℍ[ℝ])) (1 / 2)) quaternionHopfRight := by
  refine isRiemannianSubmersion_sphere_of_ambient (by norm_num)
    quaternionHopfRightAmbient (fun x => quaternionHopfRightDeriv x.fst x.snd)
    hasFDerivAt_quaternionHopfRightAmbient contDiff_quaternionHopfRightAmbient
    norm_quaternionHopfRightAmbient quaternionHopfRight (fun _ => rfl)
    (fun x w => ∃ s : ℍ[ℝ], s.re = 0 ∧ w = quaternionHopfRightVertical x.fst x.snd s)
    ?_ ?_ ?_ ?_
  · rintro x w ⟨s, hs, rfl⟩
    exact real_inner_quaternionHopfRightVertical_point x.fst x.snd s hs
  · rintro x w ⟨s, hs, rfl⟩
    exact quaternionHopfRightDeriv_vertical x.fst x.snd s hs
  · intro x hx u v hu1 hu2 hv1 hv2
    have hpq : ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1 := by
      rw [← WithLp.prod_norm_sq_eq_of_L2, hx, one_pow]
    rw [real_inner_quaternion_point'] at hu1 hv1
    refine real_inner_quaternionHopfRightDeriv x.fst x.snd hpq u v ?_ ?_
    · exact quaternionHopfRight_horizontal_eq_zero x.fst x.snd u hu1
        (fun s hs => hu2 _ ⟨s, hs, rfl⟩)
    · exact quaternionHopfRight_horizontal_eq_zero x.fst x.snd v hv1
        (fun s hs => hv2 _ ⟨s, hs, rfl⟩)
  · intro x hx
    have hpq : ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1 := by
      rw [← WithLp.prod_norm_sq_eq_of_L2, hx, one_pow]
    obtain ⟨k, hk, hknorm⟩ := exists_quaternionHopfRightUnitHorizontal x.fst x.snd hpq
    refine ⟨fun i => quaternionRightLift (quaternionUnit i) k, ?_, ?_, ?_⟩
    · rw [orthonormal_iff_ite]
      intro i j
      rw [real_inner_quaternionRightLift, hknorm, mul_one, quaternionUnit_re_mul_star]
    · intro i
      -- horizontality for `H^r` reads `p̄u₁ + q̄u₂ = 0`, while tangency is the vanishing
      -- of `Re(u₁p̄ + u₂q̄)` — the same real number, by cyclicity of `Re`.
      have h := quaternionRightLift_horizontal x.fst x.snd (quaternionUnit i) k hk
      have hre : (star x.fst * (quaternionRightLift (quaternionUnit i) k).fst).re
          + (star x.snd * (quaternionRightLift (quaternionUnit i) k).snd).re = 0 := by
        rw [← quaternion_re_add, h]
        rfl
      rw [real_inner_quaternion_point', quaternion_re_add,
        quaternion_re_mul_comm (quaternionRightLift (quaternionUnit i) k).fst (star x.fst),
        quaternion_re_mul_comm (quaternionRightLift (quaternionUnit i) k).snd (star x.snd)]
      exact hre
    · rintro i w ⟨s, hs, rfl⟩
      rw [real_inner_quaternionHopfRightVertical,
        quaternionRightLift_horizontal x.fst x.snd (quaternionUnit i) k hk]
      simp

/-- **Math.** Petersen Exercise 1.6.22 (F. Wilhelm) — **the quaternionic Hopf
fibrations.** (1) The quaternions embed in `M₂(ℂ)` as `q = z + wj ↦
!![z, w; -w̄, z̄]` by an injective `ℝ`-algebra homomorphism (so the product is
`ℝ`-bilinear and associative); (2) `|q|² = q q̄ = |z|² + |w|² = det`, norms
are multiplicative, and conjugation is an antihomomorphism; (3) both
`H^l(p,q) = (½(|p|² − |q|²), p̄q)` and `H^r(p,q) = (½(|p|² − |q|²), pq̄)` map
`S⁷(1) ⊆ ℍ²` to `S⁴(1/2) ⊆ ℝ ⊕ ℍ`; (4)/(5) the fibres of `H^l` (resp. `H^r`)
are the orbits of left (resp. right) multiplication by unit quaternions;
(6) both are Riemannian submersions (deferred, see
`quaternionHopfLeft_isRiemannianSubmersion`). -/
theorem exercise1_6_22 :
    Function.Injective quaternionMatrixRep
    ∧ (∀ q : ℍ[ℝ],
        Quaternion.normSq q = q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2)
    ∧ (∀ q : ℍ[ℝ], q * star q = ((Quaternion.normSq q : ℝ) : ℍ[ℝ]))
    ∧ (∀ q : ℍ[ℝ], (quaternionMatrixRep q).det = ((Quaternion.normSq q : ℝ) : ℂ))
    ∧ (∀ p q : ℍ[ℝ], ‖p * q‖ = ‖p‖ * ‖q‖)
    ∧ (∀ p q : ℍ[ℝ], star (p * q) = star q * star p)
    ∧ (∀ x : sphere (0 : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) 1,
        quaternionHopfLeftAmbient ↑x ∈ sphere (0 : WithLp 2 (ℝ × ℍ[ℝ])) (1 / 2)
        ∧ quaternionHopfRightAmbient ↑x ∈ sphere (0 : WithLp 2 (ℝ × ℍ[ℝ])) (1 / 2))
    ∧ (∀ x y : sphere (0 : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) 1,
        quaternionHopfLeft x = quaternionHopfLeft y ↔
          ∃ u : ℍ[ℝ], ‖u‖ = 1 ∧
            (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst = u * (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst ∧
            (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd = u * (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd)
    ∧ (∀ x y : sphere (0 : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])) 1,
        quaternionHopfRight x = quaternionHopfRight y ↔
          ∃ u : ℍ[ℝ], ‖u‖ = 1 ∧
            (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst = (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).fst * u ∧
            (y : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd = (x : WithLp 2 (ℍ[ℝ] × ℍ[ℝ])).snd * u)
    ∧ IsRiemannianSubmersion (sphereMetricUnit (n := 7) (WithLp 2 (ℍ[ℝ] × ℍ[ℝ])))
        (sphereMetric (n := 4) (WithLp 2 (ℝ × ℍ[ℝ])) (1 / 2)) quaternionHopfLeft
    ∧ IsRiemannianSubmersion (sphereMetricUnit (n := 7) (WithLp 2 (ℍ[ℝ] × ℍ[ℝ])))
        (sphereMetric (n := 4) (WithLp 2 (ℝ × ℍ[ℝ])) (1 / 2)) quaternionHopfRight :=
  ⟨quaternionMatrixRep_injective,
    fun q => by rw [Quaternion.normSq_def'],
    fun q => Quaternion.self_mul_star q,
    fun q => quaternionToMatrix_det q,
    fun p q => norm_mul p q,
    fun p q => star_mul p q,
    fun x => ⟨quaternionHopfLeftAmbient_mem_sphere x,
      quaternionHopfRightAmbient_mem_sphere x⟩,
    quaternionHopfLeft_fiber,
    quaternionHopfRight_fiber,
    quaternionHopfLeft_isRiemannianSubmersion,
    quaternionHopfRight_isRiemannianSubmersion⟩

end Exercise22

/-! ## Exercise 1.6.23 — Euler-number vector bundles over `S²` -/

section Exercise23

/-- **Math.** Petersen Exercise 1.6.23 — **Euler-number-`±k` vector bundles
over `S²`.** For positive `ρ, φ` on `(0, ∞)` consider the Riemannian
submersion `((0,∞) × S³ × S¹, dt² + ρ²[(σ¹)² + (σ²)² + (σ³)²] + φ² dθ²) →
((0,∞) × S³, dt² + ρ²[(σ²)² + (σ³)²] + h (σ¹)²)` with `f = ρ` and
`h = (ρφ)²/(ρ² + φ²)`, and suppose `f(0) > 0`, `f^{odd}(0) = 0`, `h(0) = 0`,
`h'(0) = k ∈ ℕ⁺`, `h^{even}(0) = 0`. Then the construction yields a smooth
metric on the vector bundle over `S²` with Euler number `±k`.

**Formalization.** The conclusion has three formal components, over the
coordinate model of this development:

1. the submersion display itself, on the universal-cover model
   `ℝ × ℝ × ℝ → ℝ × ℝ` of the torus fibres, with target warping
   `ρφ/√(ρ² + φ²)` (whose square is `h`) — this is
   `hopfFibrationGeneralSubmersion`, fully proved;
2. the `S²`-direction smoothness condition: `f` satisfies the
   `WarpingStaysPositiveAt` criterion of Props. 1.4.7/1.4.8 at `t = 0`;
3. the fibre-direction smoothness condition: away from the zero section the
   bundle is `(0,∞) × S³/ℤ_k`, and the `ℤ_k`-quotient divides the period of
   the fibre angle by `k`, so the fibre `ℝ²` carries the rotationally
   symmetric metric `dr² + (h(r)/k)² dψ²`; the hypothesis `h'(0) = k` says
   exactly that `h/k` satisfies the closing-up criterion
   `WarpingClosesSmoothlyAt (h/k) 0 1` of Props. 1.4.7/1.4.8.

The topological identification of the resulting bundle (Euler number `±k`;
`TS²` for `k = 2`, `ℝP² − {pt}` for `k = 1`) has no formal counterpart in
Mathlib and is recorded here in prose only. -/
theorem exercise1_6_23 (k : ℕ) (hk : 0 < k) (ρ φ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hφ : ContDiff ℝ ∞ φ)
    (hρpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < ρ t)
    (hφpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < φ t)
    (f h : ℝ → ℝ) (hf_def : f = ρ)
    (hh_def : h = fun t => (ρ t * φ t) ^ 2 / ((ρ t) ^ 2 + (φ t) ^ 2))
    (hf0 : 0 < f 0) (hfodd : ∀ l : ℕ, iteratedDeriv (2 * l + 1) f 0 = 0)
    (hh0 : h 0 = 0) (hh1 : deriv h 0 = k)
    (hheven : ∀ l : ℕ, 1 ≤ l → iteratedDeriv (2 * l) h 0 = 0) :
    IsFormRiemannianSubmersion
      (doublyWarpedProductForm (innerProductSpaceMetric ℝ)
        (innerProductSpaceMetric ℝ) ρ φ)
      (warpedProductForm (innerProductSpaceMetric ℝ) (fun _ => 1)
        (fun t => ρ t * φ t / Real.sqrt (ρ t ^ 2 + φ t ^ 2)))
      hopfSubmersionMap
    ∧ WarpingStaysPositiveAt f 0
    ∧ WarpingClosesSmoothlyAt (fun t => h t / k) 0 1 := by
  refine ⟨hopfFibrationGeneralSubmersion ρ φ, ⟨hf0, hfodd⟩, ?_, ?_, ?_⟩
  · simp only [hh0, zero_div]
  · rw [show (fun t => h t / (k : ℝ)) = fun t => h t * (k : ℝ)⁻¹ from
      funext fun t => div_eq_mul_inv _ _]
    rw [deriv_mul_const_field, hh1]
    field_simp
  · intro l hl
    have hsmul : (fun t => h t / (k : ℝ)) = (k : ℝ)⁻¹ • h := by
      funext t
      simp [div_eq_mul_inv, mul_comm]
    rw [hsmul, iteratedDeriv_const_smul_field, hheven l hl, smul_zero]

end Exercise23

/-! ## Lie group setting for Exercises 1.6.24–1.6.25 -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G]

/-! ## Exercise 1.6.24 — bi-invariant metrics on compact Lie groups -/

section Exercise24

variable (I) in
/-- **Math.** Petersen Exercise 1.6.24: a Riemannian metric on a Lie group is
**bi-invariant** if all left translations *and* all right translations are
Riemannian isometries. -/
def IsBiinvariantMetric (g : RiemannianMetric I G) : Prop :=
  (∀ x : G, IsRiemannianIsometry g g (x * ·)) ∧
    ∀ x : G, IsRiemannianIsometry g g (· * x)

variable (I) in
/-- **Math.** The **left-invariant extension** of a tangent vector
`V ∈ T_eG` to a vector field on the Lie group: `X_x = d(L_x)_e V`. These are
the left-invariant vector fields; `V ↦ X` identifies `T_eG` with the Lie
algebra of `G`. -/
def leftInvariantExtension (V : TangentSpace I (1 : G)) : Π x : G, TangentSpace I x :=
  fun x => (mfderiv I I (x * ·) 1 V : TangentSpace I x)

/-- **Math.** Petersen Exercise 1.6.24 (2), first half: for a bi-invariant
metric, conjugation `x ↦ hxh⁻¹` is a Riemannian isometry (it is the
composition of the left translation by `h` and the right translation by
`h⁻¹`, both isometries). -/
theorem biinvariantMetric_conj_isometry (g : RiemannianMetric I G)
    (hg : IsBiinvariantMetric I g) (h : G) :
    IsRiemannianIsometry g g (fun x => h * x * h⁻¹) :=
  (hg.2 h⁻¹).comp (hg.1 h)

/-- **Math.** Petersen Exercise 1.6.24 (2), second half: for a bi-invariant
metric, the differential of conjugation at the identity — the **adjoint
representation** `Ad_h = D(x ↦ hxh⁻¹)_e : 𝔤 → 𝔤` — is a linear isometry of
`(T_eG, g_e)`. -/
theorem biinvariantMetric_conj_mfderiv_isometry (g : RiemannianMetric I G)
    (hg : IsBiinvariantMetric I g) (h : G) (u v : TangentSpace I (1 : G)) :
    g.metricInner 1 (mfderiv I I (fun x => h * x * h⁻¹) 1 u)
        (mfderiv I I (fun x => h * x * h⁻¹) 1 v)
      = g.metricInner 1 u v := by
  have hpres := (biinvariantMetric_conj_isometry g hg h).preservesMetric 1 u v
  rw [mul_one, mul_inv_cancel] at hpres
  exact hpres.symm

/-- **Math.** Petersen Exercise 1.6.24 (1): every **compact** Lie group
admits a bi-invariant metric.

Rather than average a metric over right translations against the volume form
(which would need parametric integration of tensor *fields*), we average on the
**Lie algebra** `𝔤 = T_eG`, which sidesteps all base-point-smoothness issues.
`exists_adInvariant_innerProduct` produces — by the compact "unitary trick",
averaging the standard inner product over the adjoint action against the
normalised Haar measure — a symmetric, positive-definite, `Ad`-invariant inner
product `b` on `𝔤`. Its left-invariant extension `leftInvariantMetric b` is
left-invariant by construction (`leftInvariantMetric_isRiemannianIsometry`), and
`Ad`-invariance of `b` is exactly the condition that makes every right
translation an isometry too — this is the reverse direction of the
characterization proved in `exercise1_6_25`, transcribed here at the level of
`leftInvariantForm` via `mfderiv_mul_right_conj`. -/
theorem exercise1_6_24_exists_biinvariant [CompactSpace G] [T2Space G]
    [FiniteDimensional ℝ E] :
    ∃ g : RiemannianMetric I G, IsBiinvariantMetric I g := by
  obtain ⟨b, hsymm, hpos, hAd⟩ := exists_adInvariant_innerProduct (I := I) (G := G)
  refine ⟨leftInvariantMetric (I := I) b hsymm hpos, ?_, ?_⟩
  · -- left translations are isometries, unconditionally
    exact fun x => leftInvariantMetric_isRiemannianIsometry b hsymm hpos x
  · -- right translations are isometries, using `Ad`-invariance of `b`
    intro x
    refine ⟨⟨⟨⟨(· * x), (· * x⁻¹), fun z => by simp, fun z => by simp⟩,
        contMDiff_mul_right, contMDiff_mul_right⟩, rfl⟩, ?_⟩
    intro p u v
    show leftInvariantForm (I := I) b p u v
        = leftInvariantForm (I := I) b (p * x)
            (mfderiv I I (· * x) p u) (mfderiv I I (· * x) p v)
    simp only [leftInvariantForm_apply]
    rw [mfderiv_mul_right_conj x p u, mfderiv_mul_right_conj x p v]
    have hinv := hAd x⁻¹ (mfderiv I I (p⁻¹ * ·) p u) (mfderiv I I (p⁻¹ * ·) p v)
    rw [inv_inv] at hinv
    rw [hinv]

/-- **Math.** *Reduction of Exercise 1.6.24 (3) to the `Ad`/`ad` correspondence.*
Let `g` be a bi-invariant metric. If, for some smooth curve `φ : ℝ → G` through
the identity (`φ 0 = 1`), the adjoint orbit `t ↦ Ad_{φ t}` has derivative `A` at
`t = 0`, then that infinitesimal generator `A` is `g`-skew:
`g(A X, Y) + g(X, A Y) = 0`.

This packages the whole analytic content of Exercise 1.6.24 (3) — differentiating
the isometry identity `g(Ad_{φ t} X, Ad_{φ t} Y) = g(X, Y)` at `t = 0` — via the
general `curveIsometry_generator_skew` lemma, applied to the bilinear form
`g.metricToDual 1` and the curve of isometries `Ad_{φ t}`
(`biinvariantMetric_conj_mfderiv_isometry`, with `Ad_{φ 0} = Ad_1 = id`). All that
then remains to conclude ad-skewness is the identification `A = ad_U = [U, ·]`. -/
theorem biinvariantMetric_adGenerator_skew (g : RiemannianMetric I G)
    (hg : IsBiinvariantMetric I g)
    (A : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G)) (φ : ℝ → G)
    (hφ0 : φ 0 = 1) (hderiv : HasDerivAt (fun t => adjointMap I (φ t)) A 0)
    (X Y : TangentSpace I (1 : G)) :
    g.metricInner 1 (A X) Y + g.metricInner 1 X (A Y) = 0 := by
  have hρ0 : (fun t => adjointMap I (φ t)) 0
      = ContinuousLinearMap.id ℝ (TangentSpace I (1 : G)) := by
    simp only [hφ0, adjointMap_one]
  have hiso : ∀ (t : ℝ) (x y : TangentSpace I (1 : G)),
      (g.metricToDual 1) ((fun t => adjointMap I (φ t)) t x)
          ((fun t => adjointMap I (φ t)) t y) = (g.metricToDual 1) x y := by
    intro t x y
    simp only [RiemannianMetric.metricToDual_apply, adjointMap_apply]
    exact biinvariantMetric_conj_mfderiv_isometry g hg (φ t) x y
  -- `TangentSpace I 1` is definitionally `E`; instantiate the general lemma over
  -- `E` (whose normed instances are available) and let defeq carry the arguments.
  have hskew := curveIsometry_generator_skew (V := E) (g.metricToDual 1)
    (fun t => adjointMap I (φ t)) A hderiv hρ0 hiso X Y
  simpa only [RiemannianMetric.metricToDual_apply] using hskew

/-- **Math.** Petersen Exercise 1.6.24 (3): for a bi-invariant metric the
adjoint action `ad_U = [U, ·]` of the Lie algebra on itself is
**skew-symmetric**: `g([U, X], Y) = −g(X, [U, Y])`, where `[·,·]` is the Lie
bracket of the left-invariant extensions, evaluated at `e`.

The analytic half — differentiating `t ↦ g(Ad_{φ t} X, Ad_{φ t} Y) = g(X, Y)` at
`t = 0` to get a skew generator — is fully proved in
`biinvariantMetric_adGenerator_skew` (via `curveIsometry_generator_skew`). The
**only** remaining gap is the `Ad`/`ad` correspondence of Petersen §2.1.4: that a
curve `φ` realising `U` has adjoint orbit `t ↦ Ad_{φ t}` with velocity
`ad_U = [U, ·]` at `t = 0`. Mathlib has neither the Lie-group exponential map nor
this correspondence for abstract Lie groups, so that existence — isolated below as
`sorry` with the exact type it must have — is not yet formalizable. -/
theorem exercise1_6_24_ad_skew [CompleteSpace E] (g : RiemannianMetric I G)
    (hg : IsBiinvariantMetric I g) (U X Y : TangentSpace I (1 : G)) :
    g.metricInner 1
        (VectorField.mlieBracket I (leftInvariantExtension I U)
          (leftInvariantExtension I X) 1) Y
      = - g.metricInner 1 X
          (VectorField.mlieBracket I (leftInvariantExtension I U)
            (leftInvariantExtension I Y) 1) := by
  -- The single remaining mathematical gap (Petersen §2.1.4, `exp`/`Ad`–`ad`):
  -- a curve `φ` through `e` whose adjoint orbit has velocity `ad_U = [U, ·]`.
  obtain ⟨φ, A, hφ0, hderiv, hAX, hAY⟩ :
      ∃ (φ : ℝ → G) (A : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G)),
        φ 0 = 1 ∧ HasDerivAt (fun t => adjointMap I (φ t)) A 0
        ∧ A X = VectorField.mlieBracket I (leftInvariantExtension I U)
            (leftInvariantExtension I X) 1
        ∧ A Y = VectorField.mlieBracket I (leftInvariantExtension I U)
            (leftInvariantExtension I Y) 1 :=
    sorry
  have hskew := biinvariantMetric_adGenerator_skew g hg A φ hφ0 hderiv X Y
  rw [hAX, hAY] at hskew
  linarith [hskew]

/-- **Math.** Petersen Exercise 1.6.24 — **bi-invariant metrics on compact
Lie groups.** (1) A compact Lie group admits a bi-invariant metric (by
averaging over right translations); (2) for any bi-invariant metric,
conjugation is a Riemannian isometry, so `Ad_h : 𝔤 → 𝔤` is a linear
isometry; (3) hence `ad_U X = [U, X]` is skew-symmetric:
`g([U, X], Y) = −g(X, [U, Y])`. Parts (1) and (2) are fully proved
(`exercise1_6_24_exists_biinvariant` via the compact unitary trick on `𝔤`,
`biinvariantMetric_conj_isometry`/`biinvariantMetric_conj_mfderiv_isometry`);
part (3) is deferred (`exercise1_6_24_ad_skew`, needs the Lie-group `exp`/`Ad`
correspondence of Petersen §2.1.4, not yet in Mathlib). -/
theorem exercise1_6_24 [CompactSpace G] [T2Space G] [CompleteSpace E]
    [FiniteDimensional ℝ E] :
    (∃ g : RiemannianMetric I G, IsBiinvariantMetric I g)
    ∧ (∀ g : RiemannianMetric I G, IsBiinvariantMetric I g → ∀ h : G,
        IsRiemannianIsometry g g (fun x => h * x * h⁻¹))
    ∧ (∀ g : RiemannianMetric I G, IsBiinvariantMetric I g →
        ∀ (h : G) (u v : TangentSpace I (1 : G)),
        g.metricInner 1 (mfderiv I I (fun x => h * x * h⁻¹) 1 u)
            (mfderiv I I (fun x => h * x * h⁻¹) 1 v)
          = g.metricInner 1 u v)
    ∧ (∀ g : RiemannianMetric I G, IsBiinvariantMetric I g →
        ∀ U X Y : TangentSpace I (1 : G),
        g.metricInner 1
            (VectorField.mlieBracket I (leftInvariantExtension I U)
              (leftInvariantExtension I X) 1) Y
          = - g.metricInner 1 X
              (VectorField.mlieBracket I (leftInvariantExtension I U)
                (leftInvariantExtension I Y) 1)) :=
  ⟨exercise1_6_24_exists_biinvariant,
    fun g hg h => biinvariantMetric_conj_isometry g hg h,
    fun g hg h u v => biinvariantMetric_conj_mfderiv_isometry g hg h u v,
    fun g hg U X Y => exercise1_6_24_ad_skew g hg U X Y⟩

end Exercise24

/-! ## Exercise 1.6.25 — characterization of bi-invariant pseudo-metrics -/

section Exercise25

/-- **Math.** `F : (M, γ_M) → (N, γ_N)` **preserves the pseudo-Riemannian
metric** if its differential carries `γ_M` to `γ_N` at every point —
verbatim `PreservesMetric`, for pseudo-Riemannian metrics. -/
def PreservesPseudoMetric {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    (γM : PseudoRiemannianMetric I M) (γN : PseudoRiemannianMetric I' M')
    (F : M → M') : Prop :=
  ∀ (p : M) (u v : TangentSpace I p),
    γM.inner p u v = γN.inner (F p) (mfderiv I I' F p u) (mfderiv I I' F p v)

/-- **Math.** The differential of left translation by `x` at `e` composed
with the differential of left translation by `x⁻¹` at `x` is the identity:
`d(L_{x⁻¹})_x ∘ d(L_x)_e = d(L_{x⁻¹} ∘ L_x)_e = id`. -/
theorem mfderiv_mul_left_inv_mul_left (x : G) (w : TangentSpace I (1 : G)) :
    mfderiv I I (x⁻¹ * ·) (x * 1) (mfderiv I I (x * ·) 1 w) = w := by
  have hcomp : mfderiv I I ((x⁻¹ * ·) ∘ (x * ·)) 1
      = (mfderiv I I (x⁻¹ * ·) (x * 1)).comp (mfderiv I I (x * ·) 1) :=
    mfderiv_comp 1 (mdifferentiableAt_mul_left (I := I) (a := x⁻¹) (b := x * 1))
      (mdifferentiableAt_mul_left (I := I) (a := x) (b := 1))
  have hfun : ((x⁻¹ * ·) ∘ (x * ·) : G → G) = id := by
    funext y; simp [inv_mul_cancel_left]
  rw [hfun, mfderiv_id] at hcomp
  have := congrArg
    (fun T : TangentSpace I (1 : G) →L[ℝ] TangentSpace I (1 : G) => T w) hcomp
  simpa using this.symm

/-- **Math.** The differential of left translation by `x⁻¹` at `x` is
surjective (with explicit section `d(L_x)_e`); together with
`mfderiv_mul_left_inv_injective` it is a linear isomorphism `T_xG ≃ T_eG`. -/
theorem mfderiv_mul_left_inv_surjective (x : G) :
    Function.Surjective (mfderiv I I (x⁻¹ * ·) x) := by
  intro w
  refine ⟨mfderiv I I (x * ·) 1 w, ?_⟩
  have h := mfderiv_mul_left_inv_mul_left (I := I) x w
  rw [mul_one] at h
  exact h

/-- **Math.** At the identity, the left-invariant form reduces to the seed
form: `L_{e⁻¹} = id`, so `⟨u, v⟩_e = b(u, v)`. -/
theorem leftInvariantForm_one (b : E →L[ℝ] E →L[ℝ] ℝ)
    (u v : TangentSpace I (1 : G)) :
    leftInvariantForm (I := I) b 1 u v = b u v := by
  have hfun : (((1 : G)⁻¹ * ·) : G → G) = id := by funext y; simp
  rw [leftInvariantForm_apply, hfun, mfderiv_id]
  rfl

-- `mfderiv_mul_right_conj` (the chain-rule identity reading `d(R_h)` through the
-- left-invariant trivializations as `Ad_{h⁻¹}`) is provided by
-- `PetersenLib.Ch01.BiinvariantExistence`, imported above.

/-- **Math.** Petersen Exercise 1.6.25 (construction): a nondegenerate,
symmetric bilinear form `b` on the Lie algebra `T_eG` defines a
(left-invariant) **pseudo-Riemannian metric** on `G` by
`⟨u, v⟩_x = b(d(L_{x⁻¹})_x u, d(L_{x⁻¹})_x v)`. Nondegeneracy transports
through the linear isomorphism `d(L_{x⁻¹})_x` (injectivity
`mfderiv_mul_left_inv_injective` and surjectivity
`mfderiv_mul_left_inv_surjective`), symmetry and smoothness exactly as for
`leftInvariantMetric`. -/
def leftInvariantPseudoMetric [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hnondeg : ∀ u : E, u ≠ 0 → ∃ w : E, b u w ≠ 0) :
    PseudoRiemannianMetric I G where
  inner x := leftInvariantForm (I := I) b x
  symm x u v := leftInvariantForm_symm b hsymm x u v
  nondegenerate x v hv := by
    obtain ⟨w₀, hw₀⟩ := hnondeg (mfderiv I I (x⁻¹ * ·) x v)
      (fun h0 => hv (mfderiv_mul_left_inv_injective x (h0.trans (map_zero _).symm)))
    obtain ⟨w, hw⟩ := mfderiv_mul_left_inv_surjective (I := I) x w₀
    exact ⟨w, by rwa [leftInvariantForm_apply, hw]⟩
  contMDiff := leftInvariantForm_contMDiff b

/-- **Math.** The pseudo-Riemannian metric induced by a form on the Lie
algebra is always **left**-invariant — the proof of
`leftInvariantMetric_leftInvariant` verbatim (positivity is never used). -/
theorem leftInvariantPseudoMetric_leftInvariant [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hnondeg : ∀ u : E, u ≠ 0 → ∃ w : E, b u w ≠ 0) (x : G) :
    PreservesPseudoMetric (leftInvariantPseudoMetric (I := I) b hsymm hnondeg)
      (leftInvariantPseudoMetric (I := I) b hsymm hnondeg) (x * ·) := by
  intro y u v
  have hxy : ∀ w : TangentSpace I y,
      mfderiv I I ((x * y)⁻¹ * ·) (x * y) (mfderiv I I (x * ·) y w)
        = mfderiv I I (y⁻¹ * ·) y w := by
    intro w
    have hfun : (((x * y)⁻¹ * ·) ∘ (x * ·) : G → G) = (y⁻¹ * ·) := by
      funext z
      show (x * y)⁻¹ * (x * z) = y⁻¹ * z
      simp [mul_assoc]
    have h1 : mfderiv I I (((x * y)⁻¹ * ·) ∘ (x * ·)) y w
        = mfderiv I I ((x * y)⁻¹ * ·) (x * y) (mfderiv I I (x * ·) y w) :=
      mfderiv_comp_apply y
        (mdifferentiableAt_mul_left (I := I) (a := (x * y)⁻¹) (b := x * y))
        (mdifferentiableAt_mul_left (I := I) (a := x) (b := y)) w
    rw [← h1, hfun]
  show leftInvariantForm (I := I) b y u v
      = leftInvariantForm (I := I) b (x * y)
          (mfderiv I I (x * ·) y u) (mfderiv I I (x * ·) y v)
  simp only [leftInvariantForm_apply]
  rw [hxy u, hxy v]

set_option maxHeartbeats 1600000 in
/-- **Math.** Petersen Exercise 1.6.25 — **characterization of bi-invariant
pseudo-metrics.** For a Lie group `G` with Lie algebra `𝔤 = T_eG`, a
nondegenerate symmetric bilinear form `(X, Y) = b(X, Y)` on `𝔤` defines a
bi-invariant pseudo-Riemannian metric (its left-invariant extension
`leftInvariantPseudoMetric b` is invariant under all left *and* right
translations) **iff** `b` is `Ad`-invariant:
`b(X, Y) = b(Ad_h X, Ad_h Y)` for all `h ∈ G`, where
`Ad_h = D(x ↦ hxh⁻¹)_e`. Left invariance holds unconditionally
(`leftInvariantPseudoMetric_leftInvariant`); reading `d(R_h)` through the
left-invariant trivializations turns right invariance into `Ad`-invariance
(`mfderiv_mul_right_conj`). Fully proved. -/
theorem exercise1_6_25 [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hnondeg : ∀ u : E, u ≠ 0 → ∃ w : E, b u w ≠ 0) :
    ((∀ x : G, PreservesPseudoMetric
        (leftInvariantPseudoMetric (I := I) b hsymm hnondeg)
        (leftInvariantPseudoMetric (I := I) b hsymm hnondeg) (x * ·))
      ∧ (∀ h : G, PreservesPseudoMetric
        (leftInvariantPseudoMetric (I := I) b hsymm hnondeg)
        (leftInvariantPseudoMetric (I := I) b hsymm hnondeg) (· * h)))
    ↔ ∀ (h : G) (u v : E),
        b (mfderiv I I (fun y => h * y * h⁻¹) 1 u)
          (mfderiv I I (fun y => h * y * h⁻¹) 1 v) = b u v := by
  constructor
  · rintro ⟨-, hR⟩ h u v
    have H := hR h⁻¹ 1 u v
    have h1 : ∀ w : TangentSpace I (1 : G),
        mfderiv I I ((1 : G)⁻¹ * ·) 1 w = w := by
      intro w
      have hfun : (((1 : G)⁻¹ * ·) : G → G) = id := by funext y; simp
      rw [hfun, mfderiv_id]
      rfl
    have hkey : ∀ w : TangentSpace I (1 : G),
        mfderiv I I (((1 : G) * h⁻¹)⁻¹ * ·) ((1 : G) * h⁻¹)
            (mfderiv I I (· * h⁻¹) 1 w)
          = mfderiv I I (fun y => h * y * h⁻¹) 1 w := by
      intro w
      have := mfderiv_mul_right_conj (I := I) h⁻¹ (1 : G) w
      rw [h1 w] at this
      rw [inv_inv] at this
      exact this
    -- unfold both sides of the invariance identity at the identity
    have HL : (leftInvariantPseudoMetric (I := I) b hsymm hnondeg).inner (1 : G) u v
        = b u v := by
      show leftInvariantForm (I := I) b (1 : G) u v = b u v
      exact leftInvariantForm_one b u v
    have HR : (leftInvariantPseudoMetric (I := I) b hsymm hnondeg).inner
          ((1 : G) * h⁻¹) (mfderiv I I (· * h⁻¹) 1 u) (mfderiv I I (· * h⁻¹) 1 v)
        = b (mfderiv I I (fun y => h * y * h⁻¹) 1 u)
            (mfderiv I I (fun y => h * y * h⁻¹) 1 v) := by
      show leftInvariantForm (I := I) b ((1 : G) * h⁻¹) _ _ = _
      rw [leftInvariantForm_apply, hkey u, hkey v]
    rw [HL, HR] at H
    exact H.symm
  · intro hAd
    refine ⟨fun x => leftInvariantPseudoMetric_leftInvariant b hsymm hnondeg x,
      fun h p u v => ?_⟩
    show leftInvariantForm (I := I) b p u v
        = leftInvariantForm (I := I) b (p * h)
            (mfderiv I I (· * h) p u) (mfderiv I I (· * h) p v)
    simp only [leftInvariantForm_apply]
    rw [mfderiv_mul_right_conj h p u, mfderiv_mul_right_conj h p v]
    have := hAd h⁻¹ (mfderiv I I (p⁻¹ * ·) p u) (mfderiv I I (p⁻¹ * ·) p v)
    rw [inv_inv] at this
    rw [this]

end Exercise25

/-! ## Exercise 1.6.26 — averaging to a `Γ`-invariant metric

The finite-group case (`exercise1_6_26_finite`) is in `PetersenLib/Ch01/AveragedMetric.lean`;
the general **compact Lie group** case (`exercise1_6_26`) is in
`PetersenLib/Ch01/AveragedMetricCompact.lean`, where a jointly smooth action of a compact Lie
group is averaged against the Haar probability measure.  There the regularity and invariance
of the average are fully proved; the sole remaining gap is the `C^∞` smoothness of the
parametric integral in the base point (a `C^∞` parametric-integral theorem for bundle sections
that Mathlib lacks), isolated in the `contMDiff` field of `avgMetricCompact`. -/

/-! ## Exercise 1.6.27 — the Killing form -/

section Exercise27

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [Module.Finite ℝ L]

/-- **Math.** Reusable linear algebra for Petersen Exercise 1.6.27 (2): a
skew-adjoint endomorphism `A` of a finite-dimensional real inner product
space has `tr(A²) ≤ 0`: in an orthonormal basis,
`tr(A²) = Σ ⟪eᵢ, A(A eᵢ)⟫ = −Σ ‖A eᵢ‖² ≤ 0`. -/
theorem trace_comp_self_nonpos_of_skew {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (A : F →ₗ[ℝ] F)
    (hA : ∀ x y : F, ⟪A x, y⟫_ℝ = - ⟪x, A y⟫_ℝ) :
    LinearMap.trace ℝ F (A ∘ₗ A) ≤ 0 := by
  classical
  let b := stdOrthonormalBasis ℝ F
  rw [LinearMap.trace_eq_sum_inner (A ∘ₗ A) b]
  refine Finset.sum_nonpos fun i _ => ?_
  have h1 : ⟪b i, A (A (b i))⟫_ℝ = - ⟪A (b i), A (b i)⟫_ℝ := by
    have h2 := hA (b i) (A (b i))
    linarith [h2]
  rw [LinearMap.comp_apply, h1, real_inner_self_eq_norm_sq]
  exact neg_nonpos.mpr (sq_nonneg _)

variable {L} in
/-- **Math.** Petersen Exercise 1.6.27 (2): if the Lie algebra `𝔤` carries an
inner product `B'` making every `ad_U` skew-symmetric — which is what a
bi-invariant metric on `G` induces on `𝔤`, by Exercise 1.6.24 (3) — then the
Killing form is negative semidefinite: `B(X, X) ≤ 0`. Indeed `ad_X` is then
skew-adjoint, so `B(X, X) = tr(ad_X ∘ ad_X) ≤ 0`. -/
theorem exercise1_6_27_self_nonpos (B' : LinearMap.BilinForm ℝ L)
    (hsymm : ∀ X Y : L, B' X Y = B' Y X)
    (hpos : ∀ X : L, X ≠ 0 → 0 < B' X X)
    (hskew : ∀ U X Y : L, B' ⁅U, X⁆ Y = - B' X ⁅U, Y⁆) (X : L) :
    killingForm ℝ L X X ≤ 0 := by
  -- promote the abstract inner product `B'` to an `InnerProductSpace` instance
  letI cd : InnerProductSpace.Core ℝ L :=
    { inner := fun x y => B' x y
      conj_inner_symm := fun x y => by simpa using hsymm y x
      re_inner_nonneg := fun x => by
        rcases eq_or_ne x 0 with rfl | hx
        · simp
        · simpa using (hpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra hx0
        exact (hpos x hx0).ne' (by simpa using hx) }
  letI : NormedAddCommGroup L := cd.toNormedAddCommGroup
  letI : InnerProductSpace ℝ L := InnerProductSpace.ofCore cd.toCore
  have hinner : ∀ x y : L, ⟪x, y⟫_ℝ = B' x y := fun x y => rfl
  have hAd : ∀ x y : L,
      ⟪(LieAlgebra.ad ℝ L X) x, y⟫_ℝ = - ⟪x, (LieAlgebra.ad ℝ L X) y⟫_ℝ := by
    intro x y
    rw [hinner, hinner, LieAlgebra.ad_apply, LieAlgebra.ad_apply]
    exact hskew X x y
  have := trace_comp_self_nonpos_of_skew (LieAlgebra.ad ℝ L X) hAd
  rwa [killingForm_apply_apply]

/-- **Math.** Petersen Exercise 1.6.27, closing remark: when `𝔤` is
**semisimple** (Mathlib: `LieAlgebra.IsKilling`, which characterizes
semisimplicity over a field of characteristic zero), the Killing form is
nondegenerate — and hence, by Exercise 1.6.25 and part (4), defines a
bi-invariant pseudo-Riemannian metric on `G` (traditionally `−B`, to get a
Riemannian metric when `G` is also compact). -/
theorem exercise1_6_27_nondegenerate [LieAlgebra.IsKilling ℝ L] :
    (killingForm ℝ L).Nondegenerate :=
  LieAlgebra.IsKilling.killingForm_nondegenerate ℝ L

/-- **Math.** Petersen Exercise 1.6.27 — **the Killing form**
`B(X, Y) = tr(ad_X ∘ ad_Y)` on the Lie algebra `𝔤` (finite-dimensional, over
`ℝ`). (1) `B` is symmetric (and bilinear by construction, being bundled as
`killingForm ℝ L : LinearMap.BilinForm ℝ L`); (2) if `G` admits a
bi-invariant metric — inducing an inner product on `𝔤` with all `ad_U`
skew-symmetric, Exercise 1.6.24 (3) — then `B(X, X) ≤ 0`; (3) `B` is
`ad`-invariant: `B(ad_Z X, Y) = −B(X, ad_Z Y)`; (4) `B` is invariant under
every Lie algebra automorphism, in particular under `Ad_h` for `h` in the
identity component of `G` (Mathlib has no `Ad` for abstract Lie groups, so
part (4) is stated for automorphisms `e : L ≃ₗ⁅ℝ⁆ L`, which is what
`t ↦ Ad_{exp(tZ)}` produces; the derivative argument
`d/dt B(Ad_{exp tZ}X, Ad_{exp tZ}Y) = 0` is subsumed by the algebraic
invariance). Fully proved. -/
theorem exercise1_6_27 :
    (∀ X Y : L, killingForm ℝ L X Y = killingForm ℝ L Y X)
    ∧ (∀ B' : LinearMap.BilinForm ℝ L, (∀ X Y : L, B' X Y = B' Y X) →
        (∀ X : L, X ≠ 0 → 0 < B' X X) →
        (∀ U X Y : L, B' ⁅U, X⁆ Y = - B' X ⁅U, Y⁆) →
        ∀ X : L, killingForm ℝ L X X ≤ 0)
    ∧ (∀ Z X Y : L, killingForm ℝ L ⁅Z, X⁆ Y = - killingForm ℝ L X ⁅Z, Y⁆)
    ∧ (∀ (e : L ≃ₗ⁅ℝ⁆ L) (X Y : L),
        killingForm ℝ L (e X) (e Y) = killingForm ℝ L X Y) :=
  ⟨fun X Y => LieModule.traceForm_comm ℝ L L X Y,
    fun B' hsymm hpos hskew X => exercise1_6_27_self_nonpos B' hsymm hpos hskew X,
    fun Z X Y => LieModule.traceForm_apply_lie_apply' ℝ L L Z X Y,
    fun e X Y => LieAlgebra.killingForm_of_equiv_apply e X Y⟩

end Exercise27

/-! ## Exercise 1.6.28 — `SL(n, ℝ)` -/

section Exercise28

open Matrix LieAlgebra.SpecialLinear

/-- **Math.** Elements of `𝔰𝔩(n, ℝ)` are the trace-zero matrices. -/
theorem sl_trace_eq_zero (n : ℕ) (X : sl (Fin n) ℝ) :
    (X : Matrix (Fin n) (Fin n) ℝ).trace = 0 :=
  LinearMap.mem_ker.mp X.2

/-- **Math.** Petersen Exercise 1.6.28, nondegeneracy: if `tr(XY) = 0` for
all `Y ∈ 𝔰𝔩(n, ℝ)`, then `X = 0` — test against `Y = Xᵀ` (which is again
trace-free) and use `tr(XXᵀ) = Σᵢⱼ Xᵢⱼ²`. -/
theorem sl_traceForm_nondegenerate (n : ℕ) (X : sl (Fin n) ℝ)
    (hX : ∀ Y : sl (Fin n) ℝ,
      ((X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ)).trace = 0) :
    X = 0 := by
  classical
  have hXt : (X : Matrix (Fin n) (Fin n) ℝ)ᵀ ∈ sl (Fin n) ℝ := by
    rw [← LieSubalgebra.mem_toSubmodule]
    exact LinearMap.mem_ker.mpr
      (by rw [Matrix.traceLinearMap_apply, Matrix.trace_transpose]
          exact sl_trace_eq_zero n X)
  have h0 := hX ⟨(X : Matrix (Fin n) (Fin n) ℝ)ᵀ, hXt⟩
  have hsum : ((X : Matrix (Fin n) (Fin n) ℝ) * (X : Matrix (Fin n) (Fin n) ℝ)ᵀ).trace
      = ∑ i, ∑ j, ((X : Matrix (Fin n) (Fin n) ℝ) i j) ^ 2 := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, sq]
  rw [hsum] at h0
  have hzero : ∀ i j, (X : Matrix (Fin n) (Fin n) ℝ) i j = 0 := by
    intro i j
    have hnn : ∀ i ∈ Finset.univ,
        (0 : ℝ) ≤ ∑ j, ((X : Matrix (Fin n) (Fin n) ℝ) i j) ^ 2 :=
      fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 i (Finset.mem_univ i)
    have hentry := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg ((X : Matrix (Fin n) (Fin n) ℝ) i j))).mp hrow j
      (Finset.mem_univ j)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hentry
  ext i j
  exact hzero i j

/-- **Math.** Petersen Exercise 1.6.28 — **`SL(n, ℝ)`.** On the Lie algebra
`𝔰𝔩(n, ℝ)` of trace-zero matrices, the symmetric bilinear form
`(X, Y) = tr(XY)` is (i) symmetric, (ii) nondegenerate, (iii) invariant
under the adjoint action `Ad_h X = hXh⁻¹` of `SL(n, ℝ)` (which moreover
preserves `𝔰𝔩(n, ℝ)`, (iv)). By the characterization of Exercise 1.6.25 it
therefore defines a bi-invariant pseudo-Riemannian metric on `SL(n, ℝ)`
(the metric itself is not constructed here: Mathlib has no smooth-manifold
structure on `SL(n, ℝ)`). Fully proved. -/
theorem exercise1_6_28 (n : ℕ) :
    (∀ X Y : sl (Fin n) ℝ,
        ((X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ)).trace
          = ((Y : Matrix (Fin n) (Fin n) ℝ) * (X : Matrix (Fin n) (Fin n) ℝ)).trace)
    ∧ (∀ X : sl (Fin n) ℝ,
        (∀ Y : sl (Fin n) ℝ,
          ((X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ)).trace = 0)
        → X = 0)
    ∧ (∀ (h : SpecialLinearGroup (Fin n) ℝ) (X Y : sl (Fin n) ℝ),
        (((h : Matrix (Fin n) (Fin n) ℝ) * (X : Matrix (Fin n) (Fin n) ℝ)
            * ((h⁻¹ : SpecialLinearGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ))
          * ((h : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ)
            * ((h⁻¹ : SpecialLinearGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ))).trace
        = ((X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ)).trace)
    ∧ (∀ (h : SpecialLinearGroup (Fin n) ℝ) (X : sl (Fin n) ℝ),
        ((h : Matrix (Fin n) (Fin n) ℝ) * (X : Matrix (Fin n) (Fin n) ℝ)
          * ((h⁻¹ : SpecialLinearGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)).trace = 0) := by
  classical
  have hinv : ∀ h : SpecialLinearGroup (Fin n) ℝ,
      ((h⁻¹ : SpecialLinearGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
        * (h : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    intro h
    rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
  refine ⟨fun X Y => Matrix.trace_mul_comm _ _, sl_traceForm_nondegenerate n, ?_, ?_⟩
  · intro h X Y
    set A := (h : Matrix (Fin n) (Fin n) ℝ)
    set B := ((h⁻¹ : SpecialLinearGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
    have hBA : B * A = 1 := hinv h
    have hassoc : (A * (X : Matrix (Fin n) (Fin n) ℝ) * B)
        * (A * (Y : Matrix (Fin n) (Fin n) ℝ) * B)
        = A * ((X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ)) * B := by
      calc (A * (X : Matrix (Fin n) (Fin n) ℝ) * B) * (A * (Y : Matrix (Fin n) (Fin n) ℝ) * B)
          = A * (X : Matrix (Fin n) (Fin n) ℝ)
              * ((B * A) * ((Y : Matrix (Fin n) (Fin n) ℝ) * B)) := by
            simp only [Matrix.mul_assoc]
        _ = A * ((X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ)) * B := by
            rw [hBA, Matrix.one_mul]
            simp only [Matrix.mul_assoc]
    rw [hassoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
  · intro h X
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hinv h, Matrix.one_mul]
    exact sl_trace_eq_zero n X

end Exercise28

/-! ## Exercise 1.6.29 — a group with no bi-invariant pseudo-metric -/

section Exercise29

open Matrix

/-- **Math.** Petersen Exercise 1.6.29: the affine matrices
`!![a⁻¹, 0, 0; 0, a, b; 0, 0, 1]`, `a > 0`, `b ∈ ℝ` — a faithful `3 × 3`
(determinant-one) representation of the affine group
`{x ↦ ax + b, a > 0}` of the line. -/
def affMat (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a⁻¹, 0, 0; 0, a, b; 0, 0, 1]

/-- **Math.** The affine matrices are closed under multiplication:
`(a, b) · (a', b') = (aa', ab' + b)` — the affine group law. -/
theorem affMat_mul (a b a' b' : ℝ) :
    affMat a b * affMat a' b' = affMat (a * a') (a * b' + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

theorem affMat_one : affMat 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [affMat, Matrix.one_apply]

/-- **Math.** The inverse of `(a, b)` is `(a⁻¹, −b/a)`. -/
theorem affMat_mul_inv (a b : ℝ) (ha : a ≠ 0) :
    affMat a b * affMat a⁻¹ (-b / a) = 1 := by
  rw [affMat_mul, mul_inv_cancel₀ ha,
    show a * (-b / a) + b = 0 by field_simp; ring, affMat_one]

theorem affMat_inv_mul (a b : ℝ) (ha : a ≠ 0) :
    affMat a⁻¹ (-b / a) * affMat a b = 1 := by
  rw [affMat_mul, inv_mul_cancel₀ ha,
    show a⁻¹ * b + -b / a = 0 by field_simp; ring, affMat_one]

/-- **Math.** The parametrization `(a, b) ↦ affMat a b` is injective — the
group is 2-dimensional, with global coordinates `(a, b)`. -/
theorem affMat_injective : Function.Injective (fun p : ℝ × ℝ => affMat p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h11 := Matrix.ext_iff.mpr h 1 1
  have h12 := Matrix.ext_iff.mpr h 1 2
  simp [affMat] at h11 h12
  exact Prod.ext h11 h12

/-- **Math.** The affine matrix `affMat a b`, `a ≠ 0`, as a unit of the
matrix ring. -/
def affUnit (a b : ℝ) (ha : a ≠ 0) : (Matrix (Fin 3) (Fin 3) ℝ)ˣ :=
  ⟨affMat a b, affMat a⁻¹ (-b / a), affMat_mul_inv a b ha, affMat_inv_mul a b ha⟩

/-- **Math.** Petersen Exercise 1.6.29: the matrices
`!![a⁻¹, 0, 0; 0, a, b; 0, 0, 1]`, `a > 0`, `b ∈ ℝ` form a **group** (a
subgroup of the invertible `3 × 3` matrices): the affine group of the line.
Two-dimensionality is `affineMatrixGroup_two_parameters`. (Its smooth
structure — an open half-plane `(0, ∞) × ℝ` — is not formalized; Mathlib
has no Lie-subgroup machinery.) -/
def affineMatrixGroup : Subgroup (Matrix (Fin 3) (Fin 3) ℝ)ˣ where
  carrier := {g | ∃ a b : ℝ, 0 < a ∧ (g : Matrix (Fin 3) (Fin 3) ℝ) = affMat a b}
  mul_mem' := by
    rintro g g' ⟨a, b, ha, hg⟩ ⟨a', b', ha', hg'⟩
    exact ⟨a * a', a * b' + b, mul_pos ha ha', by
      rw [Units.val_mul, hg, hg', affMat_mul]⟩
  one_mem' := ⟨1, 0, one_pos, by rw [Units.val_one, affMat_one]⟩
  inv_mem' := by
    rintro g ⟨a, b, ha, hg⟩
    refine ⟨a⁻¹, -b / a, inv_pos.mpr ha, ?_⟩
    have h1 : affMat a⁻¹ (-b / a) * (g : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
      rw [hg]; exact affMat_inv_mul a b ha.ne'
    exact (Units.inv_eq_of_mul_eq_one_left h1) ▸ rfl

/-- **Math.** The group `affineMatrixGroup` is **two-dimensional**: each of
its elements has unique coordinates `(a, b) ∈ (0, ∞) × ℝ`. -/
theorem affineMatrixGroup_two_parameters (g : (Matrix (Fin 3) (Fin 3) ℝ)ˣ)
    (hg : g ∈ affineMatrixGroup) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ (g : Matrix (Fin 3) (Fin 3) ℝ) = affMat p.1 p.2 := by
  obtain ⟨a, b, ha, hab⟩ := hg
  refine ⟨(a, b), ⟨ha, hab⟩, ?_⟩
  rintro ⟨a', b'⟩ ⟨ha', hab'⟩
  have h : (fun p : ℝ × ℝ => affMat p.1 p.2) (a', b')
      = (fun p : ℝ × ℝ => affMat p.1 p.2) (a, b) := hab'.symm.trans hab
  exact affMat_injective h

/-- **Math.** The infinitesimal generator `X = d/da|_{(1,0)}` of the affine
matrix group: `X = diag(−1, 1, 0)`. -/
def affMatX : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, 1, 0; 0, 0, 0]

/-- **Math.** The infinitesimal generator `Y = d/db|_{(1,0)}` of the affine
matrix group: the elementary matrix `E₁₂` (0-indexed). -/
def affMatY : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 1; 0, 0, 0]

/-- **Math.** The Lie algebra of the affine matrix group: the span of the
two generators `X, Y` inside `M₃(ℝ)`. It is the nonabelian 2-dimensional
Lie algebra: `[X, Y] = Y` (`affMat_commutator`). -/
def affineMatrixLieAlgebra : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  Submodule.span ℝ {affMatX, affMatY}

/-- **Math.** The structure equation `[X, Y] = XY − YX = Y` of the affine
Lie algebra — the nonabelian 2-dimensional Lie algebra. -/
theorem affMat_commutator : affMatX * affMatY - affMatY * affMatX = affMatY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [affMatX, affMatY, Matrix.mul_apply, Fin.sum_univ_three]

/-- **Math.** `Ad` of the group element `(a, b)` on the generator `Y`:
`Ad_{(a,b)} Y = (a,b) Y (a,b)⁻¹ = aY`. -/
theorem affMat_conj_Y (a b : ℝ) (ha : a ≠ 0) :
    affMat a b * affMatY * affMat a⁻¹ (-b / a) = a • affMatY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [affMat, affMatY, Matrix.mul_apply, Fin.sum_univ_three]

/-- **Math.** `Ad` of the group element `(a, b)` on the generator `X`:
`Ad_{(a,b)} X = (a,b) X (a,b)⁻¹ = X − bY`. -/
theorem affMat_conj_X (a b : ℝ) (ha : a ≠ 0) :
    affMat a b * affMatX * affMat a⁻¹ (-b / a) = affMatX - b • affMatY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [affMat, affMatX, affMatY, Matrix.mul_apply, Fin.sum_univ_three]
      try field_simp

theorem affMatY_ne_zero : affMatY ≠ 0 := by
  intro h
  have := Matrix.ext_iff.mpr h 1 2
  simp [affMatY] at this

/-- **Math.** Petersen Exercise 1.6.29 — **a 2-dimensional Lie group with no
bi-invariant pseudo-Riemannian metric.** The matrices
`!![a⁻¹, 0, 0; 0, a, b; 0, 0, 1]`, `a > 0`, `b ∈ ℝ`: (i)–(iii) they form a
group under matrix multiplication (with the affine group law
`(a,b)(a',b') = (aa', ab' + b)`; bundled as `affineMatrixGroup`);
(iv) the parametrization by `(a, b)` is injective, so the group is
2-dimensional (`affineMatrixGroup_two_parameters`); (v) there is **no**
nondegenerate symmetric `Ad`-invariant bilinear form on its Lie algebra
`𝔤 = span{X, Y} ⊆ M₃(ℝ)` — by Exercise 1.6.25 (whose criterion converts a
bi-invariant pseudo-metric into exactly such a form, `Ad` being matrix
conjugation here), the group admits no bi-invariant pseudo-Riemannian
metric.

Proof of (v): `Ad_{(a,0)} Y = aY` and `Ad_{(a,0)} X = X`, so invariance with
`a = 2` forces `4 B(Y,Y) = B(Y,Y)` and `2 B(X,Y) = B(X,Y)`, i.e.
`B(Y, ·) = 0` on `𝔤` — contradicting nondegeneracy at `Y ≠ 0`. (This is the
infinitesimal statement `B([X,Y],Y) = B(Y,Y) = −B(Y,[X,Y])` from
`[X, Y] = Y`.) Fully proved. -/
theorem exercise1_6_29 :
    (∀ a b a' b' : ℝ, affMat a b * affMat a' b' = affMat (a * a') (a * b' + b))
    ∧ affMat 1 0 = 1
    ∧ (∀ a b : ℝ, a ≠ 0 → affMat a b * affMat a⁻¹ (-b / a) = 1)
    ∧ Function.Injective (fun p : ℝ × ℝ => affMat p.1 p.2)
    ∧ ¬ ∃ B : LinearMap.BilinForm ℝ (Matrix (Fin 3) (Fin 3) ℝ),
        (∀ v w, v ∈ affineMatrixLieAlgebra → w ∈ affineMatrixLieAlgebra →
          B v w = B w v)
        ∧ (∀ v ∈ affineMatrixLieAlgebra, v ≠ 0 →
            ∃ w ∈ affineMatrixLieAlgebra, B v w ≠ 0)
        ∧ (∀ a b : ℝ, 0 < a →
            ∀ v ∈ affineMatrixLieAlgebra, ∀ w ∈ affineMatrixLieAlgebra,
            B (affMat a b * v * affMat a⁻¹ (-b / a))
              (affMat a b * w * affMat a⁻¹ (-b / a)) = B v w) := by
  refine ⟨affMat_mul, affMat_one, affMat_mul_inv, affMat_injective, ?_⟩
  rintro ⟨B, hsymm, hnondeg, hinv⟩
  have hXmem : affMatX ∈ affineMatrixLieAlgebra :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hYmem : affMatY ∈ affineMatrixLieAlgebra :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  -- invariance under conjugation by `(2, 0)` kills `B(Y, Y)` and `B(X, Y)`
  have hYY : B affMatY affMatY = 0 := by
    have h := hinv 2 0 (by norm_num) affMatY hYmem affMatY hYmem
    rw [affMat_conj_Y 2 0 (by norm_num)] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    linarith
  have hXY : B affMatX affMatY = 0 := by
    have h := hinv 2 0 (by norm_num) affMatX hXmem affMatY hYmem
    rw [affMat_conj_Y 2 0 (by norm_num), affMat_conj_X 2 0 (by norm_num)] at h
    simp only [zero_smul, sub_zero, map_smul, smul_eq_mul] at h
    linarith
  have hYX : B affMatY affMatX = 0 := by
    rw [hsymm affMatY affMatX hYmem hXmem, hXY]
  -- nondegeneracy at `Y` fails
  obtain ⟨w, hwmem, hw⟩ := hnondeg affMatY hYmem affMatY_ne_zero
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hwmem
  apply hw
  simp only [map_add, map_smul, smul_eq_mul, hYX, hYY]
  ring

end Exercise29

end PetersenLib
