import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dimension.Constructions
import LeeSmoothLib.Ch08.Sec08_59.Proposition_8_30
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Semantic recall note: `lean_leansearch` surfaced `IsLocalFrameOn`, while local precedent from
-- `Problem_8_6` fixes the sphere endpoint here: keep the Cayley-Dickson formulas on `ℍ × ℍ`,
-- package them through a bundled bilinear multiplication map on `𝕆`, and transport
-- the right-multiplication fields to `S^7` through the sphere
-- tangent-space/orthogonal-complement equivalence.

open scoped Quaternion RealInnerProductSpace ContDiff Manifold

local notation "𝕆" => ℍ × ℍ
local notation "𝕆₂" => WithLp 2 𝕆
local notation "unitOctonionSphere" => Metric.sphere (0 : 𝕆₂) 1
local instance : Coe unitOctonionSphere 𝕆 := ⟨fun Q ↦ WithLp.ofLp (Q : 𝕆₂)⟩

/-- The octonion multiplication on `ℍ × ℍ` is the Cayley-Dickson product
`(p, q) (r, s) = (pr - s q^*, p^* s + rq)`. -/
def octonionMul (P Q : 𝕆) : 𝕆 :=
  (P.1 * Q.1 - Q.2 * star P.2, star P.1 * Q.2 + Q.1 * P.2)

/-- Expanded form of the octonion multiplication. -/
theorem octonionMul_apply (P Q : 𝕆) :
    octonionMul P Q = (P.1 * Q.1 - Q.2 * star P.2, star P.1 * Q.2 + Q.1 * P.2) := by
  -- This is just the defining Cayley-Dickson formula.
  rfl

/-- Octonion conjugation is given by `(p, q)^* = (p^*, -q)`. -/
def octonionStar (P : 𝕆) : 𝕆 :=
  (star P.1, -P.2)

/-- Expanded form of octonion conjugation. -/
theorem octonionStar_apply (P : 𝕆) :
    octonionStar P = (star P.1, -P.2) := by
  -- This is just the defining conjugation formula.
  rfl

/-- The seven standard imaginary unit octonions coming from the quaternion basis of `ℍ × ℍ`. -/
def problem_8_7_basisVec : Fin 7 → 𝕆 :=
  ![(((⟨0, 1, 0, 0⟩ : ℍ)), (0 : ℍ)),
    (((⟨0, 0, 1, 0⟩ : ℍ)), (0 : ℍ)),
    (((⟨0, 0, 0, 1⟩ : ℍ)), (0 : ℍ)),
    ((0 : ℍ), (1 : ℍ)),
    ((0 : ℍ), ((⟨0, 1, 0, 0⟩ : ℍ))),
    ((0 : ℍ), ((⟨0, 0, 1, 0⟩ : ℍ))),
    ((0 : ℍ), ((⟨0, 0, 0, 1⟩ : ℍ)))]

/-- Explicit form of the standard imaginary basis of octonions. -/
theorem problem_8_7_basisVec_apply :
    problem_8_7_basisVec =
      ![(((⟨0, 1, 0, 0⟩ : ℍ)), (0 : ℍ)),
        (((⟨0, 0, 1, 0⟩ : ℍ)), (0 : ℍ)),
        (((⟨0, 0, 0, 1⟩ : ℍ)), (0 : ℍ)),
        ((0 : ℍ), (1 : ℍ)),
        ((0 : ℍ), ((⟨0, 1, 0, 0⟩ : ℍ))),
        ((0 : ℍ), ((⟨0, 0, 1, 0⟩ : ℍ))),
        ((0 : ℍ), ((⟨0, 0, 0, 1⟩ : ℍ)))] := by
  -- The basis family is defined by this `Fin 7` tuple.
  rfl

/-- The octonions form an `8`-dimensional real vector space. -/
theorem octonion_finrank :
    Module.finrank ℝ 𝕆 = 8 := by
  -- The ambient space is the product of two quaternion copies.
  simp [Module.finrank_prod, Quaternion.finrank_eq_four]

private theorem problem_8_7_finrank_real_octonion_l2_fact : Fact (Module.finrank ℝ 𝕆₂ = 7 + 1) := by
  have hfinrank : Module.finrank ℝ 𝕆₂ = Module.finrank ℝ 𝕆 := by
    simpa using (LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ 𝕆))
  exact ⟨by rw [hfinrank]; simpa using octonion_finrank⟩

attribute [local instance] problem_8_7_finrank_real_octonion_l2_fact

/-- The Cayley-Dickson product on `𝕆` is additive in the left variable. -/
theorem octonionMul_add_left (P₁ P₂ Q : 𝕆) :
    octonionMul (P₁ + P₂) Q = octonionMul P₁ Q + octonionMul P₂ Q := by
  -- Route correction: expand componentwise so quaternion distributivity does the work directly.
  ext <;>
    simp [octonionMul, sub_eq_add_neg, mul_add, add_mul]
  all_goals ac_rfl

/-- The Cayley-Dickson product on `𝕆` is `ℝ`-linear in the left variable. -/
theorem octonionMul_smul_left (a : ℝ) (P Q : 𝕆) :
    octonionMul (a • P) Q = a • octonionMul P Q := by
  -- Route correction: normalize scalar multiplication in each quaternion coordinate explicitly.
  ext <;>
    simp [octonionMul, sub_eq_add_neg, Algebra.smul_def, mul_assoc]
  all_goals ring

/-- The Cayley-Dickson product on `𝕆` is additive in the right variable. -/
theorem octonionMul_add_right (P Q₁ Q₂ : 𝕆) :
    octonionMul P (Q₁ + Q₂) = octonionMul P Q₁ + octonionMul P Q₂ := by
  -- Route correction: expand componentwise so quaternion distributivity does the work directly.
  ext <;>
    simp [octonionMul, sub_eq_add_neg, mul_add, add_mul]
  all_goals ac_rfl

/-- The Cayley-Dickson product on `𝕆` is `ℝ`-linear in the right variable. -/
theorem octonionMul_smul_right (a : ℝ) (P Q : 𝕆) :
    octonionMul P (a • Q) = a • octonionMul P Q := by
  -- Route correction: normalize scalar multiplication in each quaternion coordinate explicitly.
  ext <;>
    simp [octonionMul, sub_eq_add_neg, Algebra.smul_def, mul_assoc]
  all_goals ring

/-- The Cayley-Dickson product packaged as the canonical `ℝ`-bilinear multiplication map on
the octonion algebra `𝕆 = ℍ × ℍ`. -/
def octonionMulBilinear : 𝕆 →ₗ[ℝ] 𝕆 →ₗ[ℝ] 𝕆 :=
  LinearMap.mk₂ ℝ octonionMul
    octonionMul_add_left octonionMul_smul_left
    octonionMul_add_right octonionMul_smul_right

/-- Expanded form of the bundled octonion multiplication map. -/
theorem octonionMulBilinear_apply (P Q : 𝕆) :
    octonionMulBilinear P Q = octonionMul P Q := rfl

/-- The textbook hint identity `(P Q^*) Q = P (Q^* Q)` for octonions. -/
theorem octonion_mul_star_right_assoc (P Q : 𝕆) :
    octonionMul (octonionMul P (octonionStar Q)) Q =
      octonionMul P (octonionMul (octonionStar Q) Q) := by
  rcases P with ⟨p₁, p₂⟩
  rcases Q with ⟨q₁, q₂⟩
  apply Prod.ext
  · -- Expand the first octonion coordinate all the way to quaternion coordinates.
    ext <;>
      simp [octonionMul, octonionStar, Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul, sub_eq_add_neg]
    all_goals ring
  · -- The second coordinate is another polynomial identity in the quaternion coordinates.
    ext <;>
      simp [octonionMul, octonionStar, Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul, sub_eq_add_neg]
    all_goals ring

/-- Explicit octonion witness showing that the Cayley-Dickson product on `𝕆 = ℍ × ℍ`
is not commutative. -/
theorem octonion_noncommutative :
    octonionMul (problem_8_7_basisVec 0) (problem_8_7_basisVec 1) ≠
      octonionMul (problem_8_7_basisVec 1) (problem_8_7_basisVec 0) := by
  -- Compare the two products on explicit basis vectors in quaternion coordinates.
  intro h
  have himK := congrArg (fun x : 𝕆 ↦ x.1.imK) h
  norm_num [problem_8_7_basisVec, octonionMul] at himK

/-- Explicit octonion witness showing that the Cayley-Dickson product on `𝕆 = ℍ × ℍ`
is not associative. -/
theorem octonion_nonassociative :
    octonionMul (octonionMul (problem_8_7_basisVec 0) (problem_8_7_basisVec 1))
        (problem_8_7_basisVec 3) ≠
      octonionMul (problem_8_7_basisVec 0)
        (octonionMul (problem_8_7_basisVec 1) (problem_8_7_basisVec 3)) := by
  have hleft :
      octonionMul (octonionMul (problem_8_7_basisVec 0) (problem_8_7_basisVec 1))
          (problem_8_7_basisVec 3) =
        ((0 : ℍ), -((⟨0, 0, 0, 1⟩ : ℍ))) := by
    -- Expand the left-associated witness product to the explicit octonion `(0, -k)`.
    apply Prod.ext
    · simp [problem_8_7_basisVec, octonionMul]
    · ext <;> simp [problem_8_7_basisVec, octonionMul]
  have hright :
      octonionMul (problem_8_7_basisVec 0)
          (octonionMul (problem_8_7_basisVec 1) (problem_8_7_basisVec 3)) =
        ((0 : ℍ), ((⟨0, 0, 0, 1⟩ : ℍ))) := by
    -- Expand the right-associated witness product to the explicit octonion `(0, k)`.
    apply Prod.ext
    · simp [problem_8_7_basisVec, octonionMul]
    · ext <;> simp [problem_8_7_basisVec, octonionMul]
  intro h
  have himK : (-1 : ℝ) = 1 := by
    -- Project the contradictory octonion equality to the `imK` coordinate of the second quaternion.
    simpa using congrArg (fun x : 𝕆 ↦ x.2.imK) (hleft.symm.trans (h.trans hright))
  norm_num at himK

/-- The seven octonionic ambient vector fields on `ℍ × ℍ` are obtained by right multiplication by
the standard imaginary basis vectors. -/
def problem_8_7_vectorField (i : Fin 7) : 𝕆 → 𝕆 :=
  fun Q ↦ octonionMul Q (problem_8_7_basisVec i)

/-- Expanded form of the octonionic ambient vector fields. -/
theorem problem_8_7_vectorField_apply (i : Fin 7) (Q : 𝕆) :
    problem_8_7_vectorField i Q = octonionMul Q (problem_8_7_basisVec i) := by
  -- This is the defining ambient vector-field formula.
  rfl

/-- Helper: right multiplication by a real scalar octonion is ordinary scalar
multiplication on `𝕆`. -/
theorem octonionMul_realScalar (P : 𝕆) (a : ℝ) :
    octonionMul P ((a : ℍ), 0) = a • P := by
  -- The second component vanishes, so the Cayley-Dickson formula reduces to scalar multiplication.
  ext <;> simp [octonionMul, Algebra.smul_def, mul_comm]

/-- Helper: the product `Q^* Q` is the real scalar octonion given by the sum of
the quaternion norm-squares of the two components, in the source-hint order. -/
theorem octonionMul_star_self (Q : 𝕆) :
    octonionMul (octonionStar Q) Q =
      ((((Quaternion.normSq Q.1 + Quaternion.normSq Q.2 : ℝ)) : ℍ), 0) := by
  -- Expand the Cayley-Dickson formula and use the standard quaternion norm identities.
  ext <;>
    simp [octonionMul, octonionStar, Quaternion.star_mul_self, Quaternion.self_mul_star,
      sub_eq_add_neg]

/-- Helper: the product `Q Q^*` is the same real scalar octonion. -/
theorem octonionMul_self_star (Q : 𝕆) :
    octonionMul Q (octonionStar Q) =
      ((((Quaternion.normSq Q.1 + Quaternion.normSq Q.2 : ℝ)) : ℍ), 0) := by
  -- Expand the Cayley-Dickson formula and use the standard quaternion norm identities.
  ext <;>
    simp [octonionMul, octonionStar, Quaternion.self_mul_star, sub_eq_add_neg]

/-- Helper: a unit octonion in the ambient sphere has nonzero quaternion
norm-square sum. -/
theorem octonionNormSqSum_ne_zero_of_unitSphere (Q : unitOctonionSphere) :
    Quaternion.normSq ((Q : 𝕆).1) + Quaternion.normSq ((Q : 𝕆).2) ≠ 0 := by
  intro hNormSq
  have hfst_zero : Quaternion.normSq ((Q : 𝕆).1) = 0 := by
    -- Both quaternion norm-squares are nonnegative, so a zero sum forces the first to vanish.
    have hfst_nonneg : 0 ≤ Quaternion.normSq ((Q : 𝕆).1) := Quaternion.normSq_nonneg
    have hsnd_nonneg : 0 ≤ Quaternion.normSq ((Q : 𝕆).2) := Quaternion.normSq_nonneg
    nlinarith
  have hsnd_zero : Quaternion.normSq ((Q : 𝕆).2) = 0 := by
    -- The same zero-sum argument forces the second norm-square to vanish as well.
    have hfst_nonneg : 0 ≤ Quaternion.normSq ((Q : 𝕆).1) := Quaternion.normSq_nonneg
    have hsnd_nonneg : 0 ≤ Quaternion.normSq ((Q : 𝕆).2) := Quaternion.normSq_nonneg
    nlinarith
  have hzero_octonion : (Q : 𝕆) = 0 := by
    -- Vanishing norm-square is equivalent to vanishing quaternion coordinate.
    have hfst : ((Q : 𝕆).1) = 0 := Quaternion.normSq_eq_zero.mp hfst_zero
    have hsnd : ((Q : 𝕆).2) = 0 := Quaternion.normSq_eq_zero.mp hsnd_zero
    exact Prod.ext hfst hsnd
  have hzero_lp : (Q : 𝕆₂) = 0 := by
    -- Transport the zero statement back to the `WithLp` ambient model.
    exact (WithLp.ofLp_injective 2).eq_iff.mp hzero_octonion
  have hnorm : ‖(Q : 𝕆₂)‖ = 1 := by
    -- Points of the radius-`1` sphere have ambient norm exactly `1`.
    exact mem_sphere_zero_iff_norm.mp Q.property
  have hzero_norm : ‖(Q : 𝕆₂)‖ = 0 := by simp [hzero_lp]
  linarith [hnorm, hzero_norm]

/-- Helper for Problem 8-7: project an octonion to its seven imaginary coordinates. -/
def problem_8_7_imaginaryCoords : 𝕆 →ₗ[ℝ] Fin 7 → ℝ where
  toFun P := ![P.1.imI, P.1.imJ, P.1.imK, P.2.re, P.2.imI, P.2.imJ, P.2.imK]
  map_add' P Q := by
    -- The quaternion coordinate functions are linear, so the seven-coordinate tuple adds
    -- componentwise.
    ext i
    fin_cases i <;> simp
  map_smul' a P := by
    -- Scalar multiplication acts componentwise on the chosen seven coordinates.
    ext i
    fin_cases i <;> simp

/-- Helper for Problem 8-7: the imaginary-coordinate projection sends the seven standard octonion
basis vectors to the standard basis of `ℝ^7`. -/
theorem problem_8_7_imaginaryCoords_apply_basisVec (i : Fin 7) :
    problem_8_7_imaginaryCoords (problem_8_7_basisVec i) = Pi.basisFun ℝ (Fin 7) i := by
  -- Check the seven basis vectors directly in the chosen coordinate system.
  ext j
  fin_cases i <;> fin_cases j <;> simp [problem_8_7_imaginaryCoords, problem_8_7_basisVec]

/-- Helper: the seven standard imaginary octonion basis vectors are linearly
independent over `ℝ`. -/
theorem problem_8_7_basisVec_linearIndependent :
    LinearIndependent ℝ problem_8_7_basisVec := by
  -- Apply the seven imaginary coordinates so the basis vectors become the standard basis of `ℝ^7`.
  refine Fintype.linearIndependent_iff.mpr ?_
  intro g hg i
  have hcoords :
      ∑ j, g j • Pi.basisFun ℝ (Fin 7) j = 0 := by
    -- The coordinate projection turns the vanishing octonion combination into the vanishing
    -- standard-basis combination.
    simpa [problem_8_7_imaginaryCoords_apply_basisVec] using
      congrArg problem_8_7_imaginaryCoords hg
  have heq :
      ∑ j, g j • Pi.basisFun ℝ (Fin 7) j =
        ∑ j, (0 : Fin 7 → ℝ) j • Pi.basisFun ℝ (Fin 7) j := by
    -- Compare the standard-basis combination with the zero combination.
    simpa using hcoords
  simpa using (Pi.basisFun ℝ (Fin 7)).linearIndependent.eq_coords_of_eq heq i

/-- Helper: right multiplication by a fixed octonion is an `ℝ`-linear map. -/
def octonionRightMulLinear (Q : 𝕆) : 𝕆 →ₗ[ℝ] 𝕆 where
  toFun := fun P ↦ octonionMul P Q
  map_add' := fun P₁ P₂ ↦ octonionMul_add_left P₁ P₂ Q
  map_smul' := fun a P ↦ octonionMul_smul_left a P Q

/-- Helper: expanded form of `octonionRightMulLinear`. -/
theorem octonionRightMulLinear_apply (Q P : 𝕆) :
    octonionRightMulLinear Q P = octonionMul P Q := by
  -- This is the defining linearization of right multiplication.
  rfl

/-- Helper for Problem 8-7: octonion conjugation reverses the Cayley-Dickson product. -/
theorem octonionStar_mul (P Q : 𝕆) :
    octonionStar (octonionMul P Q) = octonionMul (octonionStar Q) (octonionStar P) := by
  -- Route correction: expand conjugation and multiplication together, then normalize signs.
  rcases P with ⟨p₁, p₂⟩
  rcases Q with ⟨q₁, q₂⟩
  ext <;>
    simp [octonionMul, octonionStar, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]

/-- Helper for Problem 8-7: a nonzero octonionic norm-square sum is enough to cancel right
multiplication by `Q`. -/
private theorem octonionRightMul_injective_of_normSqSum_ne_zero
    (Q : 𝕆) (hQ : Quaternion.normSq Q.1 + Quaternion.normSq Q.2 ≠ 0) :
    Function.Injective (fun P : 𝕆 ↦ octonionMul P Q) := by
  intro P₁ P₂ hMul
  have hstarstar : octonionStar (octonionStar Q) = Q := by
    -- Conjugating twice returns the original octonion coordinatewise.
    ext <;> simp [octonionStar]
  have hcancel (P : 𝕆) :
      octonionMul (octonionMul P Q) (octonionStar Q) =
        (Quaternion.normSq Q.1 + Quaternion.normSq Q.2) • P := by
    -- Rewrite the right-associated product to the scalar octonion `Q Q^*`.
    calc
      octonionMul (octonionMul P Q) (octonionStar Q) =
          octonionMul P (octonionMul Q (octonionStar Q)) := by
            simpa [hstarstar] using octonion_mul_star_right_assoc P (octonionStar Q)
      _ = octonionMul P ((((Quaternion.normSq Q.1 + Quaternion.normSq Q.2 : ℝ)) : ℍ), 0) := by
            rw [octonionMul_self_star]
      _ = (Quaternion.normSq Q.1 + Quaternion.normSq Q.2) • P := by
            rw [octonionMul_realScalar]
  have hsmul :
      (Quaternion.normSq Q.1 + Quaternion.normSq Q.2) • P₁ =
        (Quaternion.normSq Q.1 + Quaternion.normSq Q.2) • P₂ := by
    -- Postcompose by right multiplication with `Q^*` and rewrite both sides to the same scalar.
    calc
      (Quaternion.normSq Q.1 + Quaternion.normSq Q.2) • P₁ =
          octonionMul (octonionMul P₁ Q) (octonionStar Q) := by
            symm
            exact hcancel P₁
      _ = octonionMul (octonionMul P₂ Q) (octonionStar Q) := by
            simpa using congrArg (fun X ↦ octonionMul X (octonionStar Q)) hMul
      _ = (Quaternion.normSq Q.1 + Quaternion.normSq Q.2) • P₂ := by
            exact hcancel P₂
  exact smul_right_injective _ hQ hsmul

/-- Helper: right multiplication by a unit octonion is injective. -/
theorem octonionRightMul_injective_of_unitSphere (Q : unitOctonionSphere) :
    Function.Injective (fun P : 𝕆 ↦ octonionMul P (Q : 𝕆)) := by
  -- The sphere hypothesis gives the nonzero scalar needed by the cancellation lemma.
  exact octonionRightMul_injective_of_normSqSum_ne_zero (Q : 𝕆)
    (octonionNormSqSum_ne_zero_of_unitSphere Q)

/-- Helper for Problem 8-7: left multiplication by a unit octonion is injective. -/
theorem octonionLeftMul_injective_of_unitSphere (Q : unitOctonionSphere) :
    Function.Injective (fun P : 𝕆 ↦ octonionMul (Q : 𝕆) P) := by
  intro P₁ P₂ hMul
  have hNormSq :
      Quaternion.normSq (octonionStar (Q : 𝕆)).1 +
        Quaternion.normSq (octonionStar (Q : 𝕆)).2 ≠ 0 := by
    -- Octonion conjugation preserves the quaternion norm-square sum used in the cancellation lemma.
    simpa [octonionStar, Quaternion.normSq_star, Quaternion.normSq_neg] using
      octonionNormSqSum_ne_zero_of_unitSphere Q
  have hstar :
      octonionMul (octonionStar P₁) (octonionStar (Q : 𝕆)) =
        octonionMul (octonionStar P₂) (octonionStar (Q : 𝕆)) := by
    -- Star both sides so the problem becomes a right-cancellation statement.
    simpa [octonionStar_mul] using congrArg octonionStar hMul
  have hright :=
    octonionRightMul_injective_of_normSqSum_ne_zero (octonionStar (Q : 𝕆)) hNormSq
  have hstar_eq : octonionStar P₁ = octonionStar P₂ := hright hstar
  -- Conjugate once more to recover the original octonions.
  simpa [octonionStar] using congrArg octonionStar hstar_eq

/-- Helper: each octonionic ambient right-multiplication field is smooth on
`ℍ × ℍ`. -/
theorem problem_8_7_vectorField_contDiff (i : Fin 7) :
    ContDiff ℝ ∞ (problem_8_7_vectorField i) := by
  let L : 𝕆 →L[ℝ] 𝕆 :=
    LinearMap.toContinuousLinearMap (octonionRightMulLinear (problem_8_7_basisVec i))
  -- Right multiplication by a fixed octonion is linear, hence smooth in finite dimensions.
  simpa [L, problem_8_7_vectorField, octonionRightMulLinear_apply] using L.contDiff

/-- Helper: the ambient inner product of `Q` with `Eᵢ Q` vanishes. -/
theorem problem_8_7_vectorField_innerZero (i : Fin 7) (Q : unitOctonionSphere) :
    inner ℝ (Q : 𝕆₂) (WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆))) = 0 := by
  -- Rewrite the `L²` inner product as the sum of the two quaternion inner products and then check
  -- the seven explicit basis cases directly.
  rcases Q with ⟨Q, hQ⟩
  rcases Q with ⟨p, q⟩
  change
    inner ℝ p (problem_8_7_vectorField i (p, q)).1 +
      inner ℝ q (problem_8_7_vectorField i (p, q)).2 = 0
  fin_cases i <;>
    simp [problem_8_7_vectorField, problem_8_7_basisVec, octonionMul, Quaternion.inner_def,
      Quaternion.re_mul, sub_eq_add_neg]
  all_goals ring

/-- For each unit octonion `Q`, the vector `Eᵢ Q` is tangent to the unit sphere `S^7`; in the
ambient `L²` inner-product-space structure on pairs of quaternions, this is membership in the
orthogonal complement of `ℝ ∙ Q`.
-/
theorem problem_8_7_vectorField_mem_orthogonal (i : Fin 7) (Q : unitOctonionSphere) :
    WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)) ∈ (ℝ ∙ (Q : 𝕆₂))ᗮ := by
  -- Rewrite tangency as vanishing of the ambient inner product with the radial vector.
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simpa using problem_8_7_vectorField_innerZero i Q

/-- The sphere tangent space identifies with the orthogonal complement of the radial line in the
ambient octonion space. -/
private def problem_8_7_tangentOrthogonalEquiv (Q : unitOctonionSphere) :
    TangentSpace (𝓡 7) Q ≃ₗ[ℝ] (ℝ ∙ (Q : 𝕆₂))ᗮ :=
  let coeMfderiv : TangentSpace (𝓡 7) Q →L[ℝ] 𝕆₂ :=
    mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q
  (LinearEquiv.ofInjective coeMfderiv (mfderiv_coe_sphere_injective Q)).trans
    (LinearEquiv.ofEq _ _ (range_mfderiv_coe_sphere Q))

/-- Helper for Problem 8-7: transporting an ambient tangent vector through
`problem_8_7_tangentOrthogonalEquiv Q` and then differentiating the sphere inclusion recovers the
original ambient vector. -/
private theorem problem_8_7_tangentOrthogonalEquiv_symm_apply_coe
    {Q : unitOctonionSphere} {v : 𝕆₂} (hv : v ∈ (ℝ ∙ (Q : 𝕆₂))ᗮ) :
    mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q
      ((problem_8_7_tangentOrthogonalEquiv Q).symm ⟨v, hv⟩) = v := by
  -- Rewrite the target into the ambient-value statement recorded by the equivalence itself.
  change
    Subtype.val
        (problem_8_7_tangentOrthogonalEquiv Q
          ((problem_8_7_tangentOrthogonalEquiv Q).symm ⟨v, hv⟩)) = v
  exact congrArg Subtype.val ((problem_8_7_tangentOrthogonalEquiv Q).apply_symm_apply _)

/-- The intrinsic octonionic frame on `S^7` is obtained by transporting the ambient
right-multiplication fields through the sphere tangent-space identification. -/
def problem_8_7_frame : Fin 7 → (Q : unitOctonionSphere) → TangentSpace (𝓡 7) Q :=
  fun i Q ↦
    (problem_8_7_tangentOrthogonalEquiv Q).symm
      ⟨WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)),
        problem_8_7_vectorField_mem_orthogonal i Q⟩

/-- Expanded form of the intrinsic octonionic frame on `S^7`. -/
theorem problem_8_7_frame_apply (i : Fin 7) (Q : unitOctonionSphere) :
    problem_8_7_frame i Q =
      (problem_8_7_tangentOrthogonalEquiv Q).symm
        ⟨WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)),
          problem_8_7_vectorField_mem_orthogonal i Q⟩ := by
  -- This is the defining tangent-space transport formula.
  rfl

/-- At each unit octonion, the seven octonionic vectors `Eᵢ Q` are linearly independent in the
ambient `ℍ × ℍ`. -/
theorem problem_8_7_vectorField_linearIndependent (Q : unitOctonionSphere) :
    LinearIndependent ℝ (fun i : Fin 7 ↦ problem_8_7_vectorField i (Q : 𝕆)) := by
  let L : 𝕆 →ₗ[ℝ] 𝕆 := octonionMulBilinear (Q : 𝕆)
  have hker : LinearMap.ker L = ⊥ := by
    -- Left multiplication by a unit octonion is injective, so its kernel is trivial.
    exact LinearMap.ker_eq_bot.mpr (octonionLeftMul_injective_of_unitSphere Q)
  -- The ambient frame is the image of the fixed imaginary basis under this injective linear map.
  simpa [L, problem_8_7_vectorField, Function.comp, octonionMulBilinear_apply] using
    problem_8_7_basisVec_linearIndependent.map' L hker

/-- The intrinsic octonionic frame is pointwise linearly independent on the unit sphere. -/
theorem problem_8_7_frame_linearIndependent (Q : unitOctonionSphere) :
    LinearIndependent ℝ (fun i : Fin 7 ↦ problem_8_7_frame i Q) := by
  let ambientSubtype : Fin 7 → (ℝ ∙ (Q : 𝕆₂))ᗮ := fun i ↦
    ⟨WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)),
      problem_8_7_vectorField_mem_orthogonal i Q⟩
  have hambient :
      LinearIndependent ℝ (fun i : Fin 7 ↦ WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆))) := by
    -- Transport ambient independence from `𝕆` to the `WithLp` model of the sphere.
    simpa [WithLp.linearEquiv_symm_apply] using
      (problem_8_7_vectorField_linearIndependent Q).map'
        ((WithLp.linearEquiv 2 ℝ 𝕆).symm.toLinearMap) (by simp)
  have hSubtype : LinearIndependent ℝ ambientSubtype := by
    let inc : (ℝ ∙ (Q : 𝕆₂))ᗮ →ₗ[ℝ] 𝕆₂ := Submodule.subtype _
    have hker : LinearMap.ker inc = ⊥ := by
      -- The subtype inclusion is injective, so independence can be checked in the ambient space.
      exact LinearMap.ker_eq_bot.mpr Subtype.val_injective
    exact (inc.linearIndependent_iff hker).mp <|
      by simpa [ambientSubtype, inc, Function.comp] using hambient
  -- Finally transport the orthogonal-complement basis through the tangent-space equivalence.
  simpa [problem_8_7_frame, ambientSubtype, Function.comp] using
    hSubtype.map' (problem_8_7_tangentOrthogonalEquiv Q).symm.toLinearMap (by simp)

/-- Helper for Problem 8-7: the ambient octonionic right-multiplication field remains smooth after
restricting from `𝕆₂` to the unit sphere. -/
private theorem problem_8_7_ambientVectorFieldOnSphere_contMDiff (i : Fin 7) :
    ContMDiff (𝓡 7) 𝓘(ℝ, 𝕆₂) ∞
      (fun Q : unitOctonionSphere ↦ WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆))) := by
  let e : 𝕆₂ ≃L[ℝ] 𝕆 := WithLp.prodContinuousLinearEquiv 2 ℝ ℍ ℍ
  let eInv : 𝕆 ≃L[ℝ] 𝕆₂ := e.symm
  have hOfLp : ContDiff ℝ ∞ (fun Q : 𝕆₂ ↦ WithLp.ofLp Q) := by
    -- Use the canonical `WithLp` continuous linear equivalence for products.
    simpa [e] using e.toContinuousLinearMap.contDiff
  have hToLp : ContDiff ℝ ∞ (fun Q : 𝕆 ↦ WithLp.toLp 2 Q) := by
    -- Its inverse is the canonical inclusion back into the `WithLp` model.
    simpa [eInv, e] using eInv.toContinuousLinearMap.contDiff
  have hAmbient :
      ContMDiff 𝓘(ℝ, 𝕆₂) 𝓘(ℝ, 𝕆₂) ∞
        (fun Q : 𝕆₂ ↦ WithLp.toLp 2 (problem_8_7_vectorField i (WithLp.ofLp Q))) := by
    -- Compose the smooth ambient octonion field with the two identity transports.
    rw [contMDiff_iff_contDiff]
    exact hToLp.comp ((problem_8_7_vectorField_contDiff i).comp hOfLp)
  -- Compose the ambient model-space field with the smooth sphere inclusion.
  simpa using hAmbient.comp contMDiff_coe_sphere

/-- Helper for Problem 8-7: in the preferred tangent-bundle trivialization at `Q₀`, the
intrinsic octonionic frame is read by differentiating the fixed preferred chart at the current
point. -/
private theorem problem_8_7_frameTrivialization_eq_mfderiv
    (i : Fin 7) (Q₀ Q : unitOctonionSphere)
    (hQ : Q ∈ (chartAt (EuclideanSpace ℝ (Fin 7)) Q₀).source) :
    (trivializationAt (EuclideanSpace ℝ (Fin 7)) (TangentSpace (𝓡 7)) Q₀
      ⟨Q, problem_8_7_frame i Q⟩).2 =
      NormedSpace.fromTangentSpace (extChartAt (𝓡 7) Q₀ Q)
        (mfderiv (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) (extChartAt (𝓡 7) Q₀) Q
          (problem_8_7_frame i Q)) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin 7)) (TangentSpace (𝓡 7)) Q₀
  have hQBase :
      Q ∈ e.baseSet := by
    -- The tangent-bundle base set is exactly the preferred chart source.
    simpa [e, TangentBundle.trivializationAt_baseSet] using hQ
  have hApply :
      Bundle.Trivialization.continuousLinearMapAt ℝ e Q (problem_8_7_frame i Q) =
        (e ⟨Q, problem_8_7_frame i Q⟩).2 := by
    change (e.linearMapAt ℝ Q) (problem_8_7_frame i Q) = (e ⟨Q, problem_8_7_frame i Q⟩).2
    rw [e.coe_linearMapAt_of_mem hQBase]
  -- First rewrite the bundle coordinate through the fiberwise linear map carried by the
  -- tangent-bundle trivialization.
  change (e ⟨Q, problem_8_7_frame i Q⟩).2 = _
  rw [← hApply]
  -- Then replace that linear map by the derivative of the fixed preferred chart.
  have hMap :
      Bundle.Trivialization.continuousLinearMapAt ℝ e Q =
        mfderiv (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) (extChartAt (𝓡 7) Q₀) Q := by
    simpa [e] using (TangentBundle.continuousLinearMapAt_trivializationAt hQ :
      Bundle.Trivialization.continuousLinearMapAt ℝ e Q =
        mfderiv (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) (extChartAt (𝓡 7) Q₀) Q)
  exact congrArg (fun f ↦ f (problem_8_7_frame i Q)) hMap

/-- Helper for Problem 8-7: differentiating the sphere inclusion along the intrinsic octonionic
frame recovers the ambient right-multiplication field. -/
private theorem problem_8_7_frame_coe_mfderiv_apply
    (i : Fin 7) (Q : unitOctonionSphere) :
    mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q
      (problem_8_7_frame i Q) = WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)) := by
  let v : 𝕆₂ := WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆))
  have hv : v ∈ (ℝ ∙ (Q : 𝕆₂))ᗮ := by
    simpa [v] using problem_8_7_vectorField_mem_orthogonal i Q
  -- Expand the frame definition and cancel the tangent/orthogonal-complement equivalence.
  simpa [problem_8_7_frame] using
    (@problem_8_7_tangentOrthogonalEquiv_symm_apply_coe Q v hv)

/-- Helper for Problem 8-7: near `Q₀`, the fixed tangent-bundle trivialization of the intrinsic
frame agrees with the preferred-chart derivative expression. -/
private theorem problem_8_7_frameTrivialization_eventuallyEq_mfderiv
    (i : Fin 7) (Q₀ : unitOctonionSphere) :
    (fun Q : unitOctonionSphere ↦
      (trivializationAt (EuclideanSpace ℝ (Fin 7)) (TangentSpace (𝓡 7)) Q₀
        ⟨Q, problem_8_7_frame i Q⟩).2) =ᶠ[nhds Q₀]
      (fun Q : unitOctonionSphere ↦
        NormedSpace.fromTangentSpace (extChartAt (𝓡 7) Q₀ Q)
          (mfderiv (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) (extChartAt (𝓡 7) Q₀) Q
            (problem_8_7_frame i Q))) := by
  have hSource : (extChartAt (𝓡 7) Q₀).source ∈ nhds Q₀ := extChartAt_source_mem_nhds Q₀
  filter_upwards [hSource] with Q hQ
  -- On the preferred chart source, the tangent-bundle trivialization is already the chart
  -- derivative from `problem_8_7_frameTrivialization_eq_mfderiv`.
  exact problem_8_7_frameTrivialization_eq_mfderiv i Q₀ Q (by simpa [extChartAt] using hQ)

/-- Helper for Problem 8-7: the antipode of a unit octonion again has ambient norm `1`. -/
private theorem problem_8_7_negBase_norm_eq_one (Q₀ : unitOctonionSphere) :
    ‖(-(Q₀ : 𝕆₂) : 𝕆₂)‖ = 1 := by
  -- Points of the unit sphere have norm `1`, and negation preserves the norm.
  rw [norm_neg]
  exact mem_sphere_zero_iff_norm.mp Q₀.property

/-- Helper for Problem 8-7: a unit octonion is not equal to its antipode in the ambient model. -/
private theorem problem_8_7_self_ne_neg (Q₀ : unitOctonionSphere) :
    (Q₀ : 𝕆₂) ≠ -(Q₀ : 𝕆₂) := by
  intro h
  have htwo : (2 : ℝ) • (Q₀ : 𝕆₂) = 0 := by
    -- Adding `Q₀` to both sides of `Q₀ = -Q₀` collapses to the zero vector.
    have hadd := congrArg (fun x : 𝕆₂ ↦ x + (Q₀ : 𝕆₂)) h
    simpa [two_smul] using hadd
  have hnorm : ‖(Q₀ : 𝕆₂)‖ = 1 := by
    -- The sphere condition rules out the zero vector.
    exact mem_sphere_zero_iff_norm.mp Q₀.property
  have hnormTwo : ‖(2 : ℝ) • (Q₀ : 𝕆₂)‖ = 0 := by
    simp [htwo]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hnormTwo
  linarith

/-- Helper for Problem 8-7: if a sphere point is not the antipode of `Q₀`, then its inner product
with `-Q₀` is not `1`, so stereographic coordinates centred at `-Q₀` are regular there. -/
private theorem problem_8_7_inner_negBase_ne_one_of_ne
    (Q₀ Q : unitOctonionSphere) (hQ : (Q : 𝕆₂) ≠ -(Q₀ : 𝕆₂)) :
    innerSL ℝ (-(Q₀ : 𝕆₂)) (Q : 𝕆₂) ≠ (1 : ℝ) := by
  intro hInner
  have hnormQ : ‖(Q : 𝕆₂)‖ = 1 := by
    -- Every sphere point has ambient norm `1`.
    exact mem_sphere_zero_iff_norm.mp Q.property
  have hEq :
      (-(Q₀ : 𝕆₂) : 𝕆₂) = (Q : 𝕆₂) := by
    -- On the unit sphere, inner product `1` forces equality.
    have hInner' : inner ℝ (-(Q₀ : 𝕆₂)) (Q : 𝕆₂) = 1 := by
      simpa [innerSL_apply_apply] using hInner
    exact
      (inner_eq_one_iff_of_norm_eq_one (problem_8_7_negBase_norm_eq_one Q₀) hnormQ).mp hInner'
  exact hQ hEq.symm

/-- Helper for Problem 8-7: the ambient stereographic retraction centred at `-Q₀` lands in the
unit sphere and agrees there with the identity away from the antipode. -/
private def problem_8_7_localSphereRetraction (Q₀ : unitOctonionSphere) : 𝕆₂ → unitOctonionSphere :=
  fun x ↦ stereoInvFun (problem_8_7_negBase_norm_eq_one Q₀) (stereoToFun (-(Q₀ : 𝕆₂)) x)

/-- Helper for Problem 8-7: on sphere points away from the antipode of `Q₀`, the local
stereographic retraction is literally the identity. -/
private theorem problem_8_7_localSphereRetraction_eq_self_of_ne
    (Q₀ Q : unitOctonionSphere) (hQ : (Q : 𝕆₂) ≠ -(Q₀ : 𝕆₂)) :
    problem_8_7_localSphereRetraction Q₀ (Q : 𝕆₂) = Q := by
  -- The stereographic left-inverse theorem identifies the ambient values.
  simpa [problem_8_7_localSphereRetraction] using
    stereo_left_inv (problem_8_7_negBase_norm_eq_one Q₀) hQ

/-- Helper for Problem 8-7: near any sphere point different from the antipode of `Q₀`, the
ambient retraction followed by the sphere inclusion agrees with the identity. -/
private theorem problem_8_7_localSphereRetraction_comp_coe_eventuallyEq
    (Q₀ Q : unitOctonionSphere) (hQ : (Q : 𝕆₂) ≠ -(Q₀ : 𝕆₂)) :
    (fun R : unitOctonionSphere ↦ problem_8_7_localSphereRetraction Q₀ (R : 𝕆₂)) =ᶠ[nhds Q] id := by
  have hOpen :
      IsOpen {R : unitOctonionSphere | (R : 𝕆₂) ≠ -(Q₀ : 𝕆₂)} := by
    -- Excluding the antipode cuts out an open neighborhood in the sphere.
    have hClosed :
        IsClosed {R : unitOctonionSphere | (R : 𝕆₂) = -(Q₀ : 𝕆₂)} := by
      simpa [Set.preimage, Set.setOf_eq_eq_singleton] using
        ((isClosed_singleton : IsClosed ({-(Q₀ : 𝕆₂)} : Set 𝕆₂)).preimage
          continuous_subtype_val)
    simpa [Set.compl_setOf] using hClosed.isOpen_compl
  have hNhds :
      {R : unitOctonionSphere | (R : 𝕆₂) ≠ -(Q₀ : 𝕆₂)} ∈ nhds Q :=
    hOpen.mem_nhds hQ
  filter_upwards [hNhds] with R hR
  -- On this neighborhood, the stereographic retraction is pointwise the identity.
  simpa using problem_8_7_localSphereRetraction_eq_self_of_ne Q₀ R hR

/-- Helper for Problem 8-7: the ambient stereographic retraction is smooth at every point where
the stereographic denominator centred at `-Q₀` does not vanish. -/
private theorem problem_8_7_localSphereRetraction_contMDiffAt_of_ne
    (Q₀ : unitOctonionSphere) {x : 𝕆₂}
    (hx : innerSL ℝ (-(Q₀ : 𝕆₂)) x ≠ (1 : ℝ)) :
    ContMDiffAt 𝓘(ℝ, 𝕆₂) (𝓡 7) ∞ (problem_8_7_localSphereRetraction Q₀) x := by
  let s : Set 𝕆₂ := {y : 𝕆₂ | innerSL ℝ (-(Q₀ : 𝕆₂)) y ≠ (1 : ℝ)}
  have hsOpen : IsOpen s := by
    -- The exceptional hyperplane is closed because `innerSL` is continuous.
    have hClosed :
        IsClosed {y : 𝕆₂ | innerSL ℝ (-(Q₀ : 𝕆₂)) y = (1 : ℝ)} := by
      simpa [Set.preimage, Set.setOf_eq_eq_singleton] using
        ((isClosed_singleton : IsClosed ({(1 : ℝ)} : Set ℝ)).preimage
          (innerSL ℝ (-(Q₀ : 𝕆₂))).continuous)
    simpa [s, Set.compl_setOf] using hClosed.isOpen_compl
  let U : TopologicalSpace.Opens 𝕆₂ := ⟨s, hsOpen⟩
  have hStereoU :
      ContMDiff 𝓘(ℝ, 𝕆₂) 𝓘(ℝ, (ℝ ∙ (-(Q₀ : 𝕆₂)))ᗮ) ∞
        (fun y : U ↦ stereoToFun (-(Q₀ : 𝕆₂)) y) := by
    let g : 𝕆₂ → (ℝ ∙ (-(Q₀ : 𝕆₂)))ᗮ := stereoToFun (-(Q₀ : 𝕆₂))
    have hStereoOn :
        ContMDiffOn 𝓘(ℝ, 𝕆₂) 𝓘(ℝ, (ℝ ∙ (-(Q₀ : 𝕆₂)))ᗮ) ∞ g s :=
      contDiffOn_stereoToFun.contMDiffOn
    intro y
    -- The regular locus is open, so the ambient `ContDiffOn` theorem upgrades to `ContDiffAt`.
    exact contMDiffAt_subtype_iff.2
      (hStereoOn.contMDiffAt (hsOpen.mem_nhds y.2))
  have hInv :
      ContMDiff 𝓘(ℝ, (ℝ ∙ (-(Q₀ : 𝕆₂)))ᗮ) (𝓡 7) ∞
        (stereoInvFun (problem_8_7_negBase_norm_eq_one Q₀)) := by
    let f : (ℝ ∙ (-(Q₀ : 𝕆₂)))ᗮ → 𝕆₂ := fun w ↦ stereoInvFunAux (-(Q₀ : 𝕆₂)) w
    have hAux : ContDiff ℝ ∞ f := by
      change ContDiff ℝ ∞ (stereoInvFunAux (-(Q₀ : 𝕆₂)) ∘ Subtype.val)
      simpa using
        contDiff_stereoInvFunAux.comp
          (ℝ ∙ (-(Q₀ : 𝕆₂)))ᗮ.subtypeL.contDiff
    have hSphere : ∀ w, f w ∈ unitOctonionSphere := by
      intro w
      exact stereoInvFunAux_mem (problem_8_7_negBase_norm_eq_one Q₀) w.2
    simpa [f, stereoInvFun] using ContMDiff.codRestrict_sphere hAux.contMDiff hSphere
  have hRetU :
      ContMDiff 𝓘(ℝ, 𝕆₂) (𝓡 7) ∞ (fun y : U ↦ problem_8_7_localSphereRetraction Q₀ y) := by
    -- Compose the smooth stereographic chart on the regular neighborhood with the smooth inverse
    -- stereographic parametrization of the sphere.
    simpa [problem_8_7_localSphereRetraction] using hInv.comp hStereoU
  have hRetAt :
      ContMDiffAt 𝓘(ℝ, 𝕆₂) (𝓡 7) ∞
        (fun y : U ↦ problem_8_7_localSphereRetraction Q₀ y) ⟨x, hx⟩ :=
    hRetU.contMDiffAt
  -- Finally forget the open-subtype domain and return to the ambient point `x`.
  exact contMDiffAt_subtype_iff.mp hRetAt

/-- Helper for Problem 8-7: the ambient stereographic retraction is smooth at the chosen sphere
basepoint `Q₀`. -/
private theorem problem_8_7_localSphereRetraction_contMDiffAt
    (Q₀ : unitOctonionSphere) :
    ContMDiffAt 𝓘(ℝ, 𝕆₂) (𝓡 7) ∞ (problem_8_7_localSphereRetraction Q₀) (Q₀ : 𝕆₂) := by
  have hx :
      innerSL ℝ (-(Q₀ : 𝕆₂)) (Q₀ : 𝕆₂) ≠ (1 : ℝ) :=
    problem_8_7_inner_negBase_ne_one_of_ne Q₀ Q₀ (problem_8_7_self_ne_neg Q₀)
  -- The basepoint lies in the regular stereographic neighborhood centred at its antipode.
  exact problem_8_7_localSphereRetraction_contMDiffAt_of_ne Q₀ hx

/-- Helper for Problem 8-7: differentiating the local stereographic retraction along the smooth
ambient octonion field recovers the intrinsic frame away from the antipode of `Q₀`. -/
private theorem problem_8_7_localSphereRetraction_mfderiv_apply_ambientField_of_ne
    (i : Fin 7) (Q₀ Q : unitOctonionSphere) (hQ : (Q : 𝕆₂) ≠ -(Q₀ : 𝕆₂)) :
    mfderiv 𝓘(ℝ, 𝕆₂) (𝓡 7) (problem_8_7_localSphereRetraction Q₀) (Q : 𝕆₂)
      ((NormedSpace.fromTangentSpace (Q : 𝕆₂)).symm
        (WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)))) =
      problem_8_7_frame i Q := by
  have hRetDiff :
      MDifferentiableAt 𝓘(ℝ, 𝕆₂) (𝓡 7) (problem_8_7_localSphereRetraction Q₀) (Q : 𝕆₂) :=
    (problem_8_7_localSphereRetraction_contMDiffAt_of_ne Q₀
      (problem_8_7_inner_negBase_ne_one_of_ne Q₀ Q hQ)).mdifferentiableAt (by simp)
  have hCoeDiff :
      MDifferentiableAt (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q := by
    -- The sphere inclusion is smooth, hence differentiable.
    simpa using
      (contMDiff_coe_sphere : ContMDiff (𝓡 7) 𝓘(ℝ, 𝕆₂) ∞
        ((↑) : unitOctonionSphere → 𝕆₂)).contMDiffAt.mdifferentiableAt (by simp)
  have hLocalEq :
      (fun R : unitOctonionSphere ↦ problem_8_7_localSphereRetraction Q₀ (R : 𝕆₂)) =ᶠ[nhds Q] id :=
    problem_8_7_localSphereRetraction_comp_coe_eventuallyEq Q₀ Q hQ
  have hComp :
      mfderiv (𝓡 7) (𝓡 7)
        (problem_8_7_localSphereRetraction Q₀ ∘ ((↑) : unitOctonionSphere → 𝕆₂)) Q
        (problem_8_7_frame i Q) =
      mfderiv 𝓘(ℝ, 𝕆₂) (𝓡 7) (problem_8_7_localSphereRetraction Q₀) (Q : 𝕆₂)
        (mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q
          (problem_8_7_frame i Q)) := by
    -- Differentiate the composition `retraction ∘ coe` at `Q`.
    simpa [Function.comp] using
      (mfderiv_comp_apply_of_eq Q hRetDiff hCoeDiff rfl (problem_8_7_frame i Q))
  have hId :
      mfderiv (𝓡 7) (𝓡 7)
        (problem_8_7_localSphereRetraction Q₀ ∘ ((↑) : unitOctonionSphere → 𝕆₂)) Q
        (problem_8_7_frame i Q) =
      problem_8_7_frame i Q := by
    -- On a neighborhood of `Q`, the composition is the identity map on the sphere.
    have hmf :
        mfderiv (𝓡 7) (𝓡 7)
          (problem_8_7_localSphereRetraction Q₀ ∘ ((↑) : unitOctonionSphere → 𝕆₂)) Q =
        mfderiv (𝓡 7) (𝓡 7) id Q :=
      hLocalEq.mfderiv_eq
    simpa [mfderiv_id] using congrArg (fun L ↦ L (problem_8_7_frame i Q)) hmf
  -- Replace the inclusion derivative by the already normalized ambient octonion field.
  have hAmbient :
      mfderiv 𝓘(ℝ, 𝕆₂) (𝓡 7) (problem_8_7_localSphereRetraction Q₀) (Q : 𝕆₂)
        ((NormedSpace.fromTangentSpace (Q : 𝕆₂)).symm
          (WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)))) =
      mfderiv 𝓘(ℝ, 𝕆₂) (𝓡 7) (problem_8_7_localSphereRetraction Q₀) (Q : 𝕆₂)
        (mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q
          (problem_8_7_frame i Q)) := by
    rw [problem_8_7_frame_coe_mfderiv_apply]
    rfl
  exact hAmbient.trans (hComp.symm.trans hId)

/-- Helper for Problem 8-7: the preferred-chart coordinates obtained by differentiating the local
stereographic retraction against the ambient octonion field are smooth at `Q₀`. -/
private theorem problem_8_7_retractionChartRep_contMDiffAt
    (i : Fin 7) (Q₀ : unitOctonionSphere) :
    ContMDiffAt (𝓡 7) (𝓡 7) ∞
      (fun Q : unitOctonionSphere ↦
        NormedSpace.fromTangentSpace
          ((extChartAt (𝓡 7) Q₀) (problem_8_7_localSphereRetraction Q₀ (Q : 𝕆₂)))
          (mfderiv 𝓘(ℝ, 𝕆₂) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7))
            ((extChartAt (𝓡 7) Q₀) ∘ problem_8_7_localSphereRetraction Q₀) (Q : 𝕆₂)
            ((NormedSpace.fromTangentSpace (Q : 𝕆₂)).symm
              (WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)))))) Q₀ := by
  let Y : ∀ x : 𝕆₂, TangentSpace 𝓘(ℝ, 𝕆₂) x := fun x ↦
    (NormedSpace.fromTangentSpace x).symm
      (WithLp.toLp 2 (problem_8_7_vectorField i (WithLp.ofLp x)))
  let g : 𝕆₂ → EuclideanSpace ℝ (Fin 7) :=
    (extChartAt (𝓡 7) Q₀) ∘ problem_8_7_localSphereRetraction Q₀
  have hRetEq :
      problem_8_7_localSphereRetraction Q₀ (Q₀ : 𝕆₂) = Q₀ :=
    problem_8_7_localSphereRetraction_eq_self_of_ne Q₀ Q₀ (problem_8_7_self_ne_neg Q₀)
  have hComposite :
      ContMDiffAt 𝓘(ℝ, 𝕆₂) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) ∞
        g (Q₀ : 𝕆₂) := by
    -- Compose the local stereographic retraction with the preferred chart at the basepoint.
    exact (show
      ContMDiffAt (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) ∞ (extChartAt (𝓡 7) Q₀) Q₀ from
        contMDiffAt_extChartAt).comp_of_eq
      (problem_8_7_localSphereRetraction_contMDiffAt Q₀) hRetEq
  have hAmbientField :
      ContMDiff 𝓘(ℝ, 𝕆₂) 𝓘(ℝ, 𝕆₂) ∞
        (fun x : 𝕆₂ ↦ WithLp.toLp 2 (problem_8_7_vectorField i (WithLp.ofLp x))) := by
    have hOfLp : ContDiff ℝ ∞ (fun x : 𝕆₂ ↦ WithLp.ofLp x) := by
      -- The canonical `WithLp` equivalence gives a smooth identification back to `𝕆`.
      simpa using ((WithLp.linearEquiv 2 ℝ 𝕆).toContinuousLinearMap.contDiff)
    have hToLp : ContDiff ℝ ∞ (fun x : 𝕆 ↦ WithLp.toLp 2 x) := by
      -- The inverse equivalence packages the ambient octonion coordinates back into `𝕆₂`.
      simpa using (((WithLp.linearEquiv 2 ℝ 𝕆).symm.toContinuousLinearMap).contDiff)
    -- The ambient octonion field is smooth on the model vector space itself.
    rw [contMDiff_iff_contDiff]
    exact hToLp.comp ((problem_8_7_vectorField_contDiff i).comp hOfLp)
  have hY :
      ContMDiffAt 𝓘(ℝ, 𝕆₂) (𝓘(ℝ, 𝕆₂)).tangent ∞ (T% Y) (Q₀ : 𝕆₂) := by
    -- On the vector-space model, tangent-bundle coordinates of `Y` are exactly the ambient field.
    rw [Bundle.contMDiffAt_section (Q₀ : 𝕆₂)]
    simpa [Y] using hAmbientField.contMDiffAt
  have hAmbientAt := contMDiffAt_mfderiv_applyField hComposite hY
  have hCoe :
      ContMDiffAt (𝓡 7) 𝓘(ℝ, 𝕆₂) ∞ ((↑) : unitOctonionSphere → 𝕆₂) Q₀ := by
    -- Restrict the ambient smooth field back to the sphere via the inclusion map.
    simpa using
      (contMDiff_coe_sphere : ContMDiff (𝓡 7) 𝓘(ℝ, 𝕆₂) ∞
        ((↑) : unitOctonionSphere → 𝕆₂)).contMDiffAt
  -- Route correction: differentiate the genuine stereographic retraction instead of trying to
  -- invert the forward ambient coordinate map by hand. The chart map is bundled into the
  -- retraction here so the codomain is again a vector space.
  simpa [g, Y, Function.comp] using hAmbientAt.comp Q₀ hCoe

/-- Helper for Problem 8-7: the fixed-base ambient coordinate map sends tangent coordinates in the
preferred chart at `Q₀` to ambient `𝕆₂` coordinates through the derivative of the sphere
inclusion. -/
private def problem_8_7_frameAmbientCoordMap
    (Q₀ Q : unitOctonionSphere) :
    EuclideanSpace ℝ (Fin 7) →L[ℝ] 𝕆₂ :=
  inTangentCoordinates (𝓡 7) 𝓘(ℝ, 𝕆₂) id ((↑) : unitOctonionSphere → 𝕆₂)
    (fun x ↦ mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) x) Q₀ Q

/-- Helper for Problem 8-7: for a fixed basepoint `Q₀`, the ambient coordinate map coming from the
sphere inclusion is smooth in fixed-base coordinates. -/
private theorem problem_8_7_frameAmbientCoordMap_contMDiffAt
    (Q₀ : unitOctonionSphere) :
    ContMDiffAt (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7) →L[ℝ] 𝕆₂) ∞
      (fun Q : unitOctonionSphere ↦ problem_8_7_frameAmbientCoordMap Q₀ Q) Q₀ := by
  -- `ContMDiffAt.mfderiv_const` is already stated in these fixed-base tangent coordinates for the
  -- sphere inclusion, so only the local name of the coordinate map needs to be unfolded.
  simpa [problem_8_7_frameAmbientCoordMap] using
    ((contMDiff_coe_sphere : ContMDiff (𝓡 7) 𝓘(ℝ, 𝕆₂) ∞
      ((↑) : unitOctonionSphere → 𝕆₂)).contMDiffAt.mfderiv_const (by simp))

/-- Helper for Problem 8-7: unfolding `inTangentCoordinates` identifies the fixed-base ambient
coordinate map with the derivative of the sphere inclusion followed by the inverse tangent-bundle
trivialization at `Q₀`. -/
private theorem problem_8_7_frameAmbientCoordMap_eq_trivializationComposition
    (Q₀ Q : unitOctonionSphere) :
    problem_8_7_frameAmbientCoordMap Q₀ Q =
      (mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q).comp
        ((trivializationAt (EuclideanSpace ℝ (Fin 7)) (TangentSpace (𝓡 7)) Q₀).symmL ℝ Q) := by
  have hModelBase :
      ((Q : 𝕆₂) ∈
        (trivializationAt 𝕆₂ (TangentSpace 𝓘(ℝ, 𝕆₂)) (Q₀ : 𝕆₂)).baseSet) := by
    simp
  -- Unfold the fixed-base tangent coordinates. Because the codomain is the model space `𝕆₂`,
  -- the target-side tangent coordinates are the identity.
  ext v
  simp only [problem_8_7_frameAmbientCoordMap, inTangentCoordinates,
    ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    TangentBundle.continuousLinearMapAt_model_space]
  change (1 : 𝕆₂ →L[ℝ] 𝕆₂)
      ((mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q)
        (((trivializationAt (EuclideanSpace ℝ (Fin 7)) (TangentSpace (𝓡 7)) Q₀).symm Q) v)) =
    (mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q)
      (((trivializationAt (EuclideanSpace ℝ (Fin 7)) (TangentSpace (𝓡 7)) Q₀).symm Q) v)
  simp

/-- Helper for Problem 8-7: on the preferred-chart source of `Q₀`, applying the fixed-base ambient
coordinate map to the intrinsic frame coordinates recovers the explicit ambient octonion field. -/
private theorem problem_8_7_frameAmbientCoordMap_apply_frameChartRep
    (i : Fin 7) (Q₀ Q : unitOctonionSphere)
    (hQ : Q ∈ (extChartAt (𝓡 7) Q₀).source) :
    problem_8_7_frameAmbientCoordMap Q₀ Q
      (NormedSpace.fromTangentSpace (extChartAt (𝓡 7) Q₀ Q)
        (mfderiv (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) (extChartAt (𝓡 7) Q₀) Q
          (problem_8_7_frame i Q))) =
      WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin 7)) (TangentSpace (𝓡 7)) Q₀
  have hQBase : Q ∈ e.baseSet := by
    -- The tangent-bundle trivialization at `Q₀` is defined exactly on the preferred chart source.
    simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt] using hQ
  have hCoords :
      (e ⟨Q, problem_8_7_frame i Q⟩).2 =
        NormedSpace.fromTangentSpace (extChartAt (𝓡 7) Q₀ Q)
          (mfderiv (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) (extChartAt (𝓡 7) Q₀) Q
            (problem_8_7_frame i Q)) := by
    -- The preferred-chart tangent coordinates agree with the fixed tangent-bundle trivialization.
    simpa [e] using
      problem_8_7_frameTrivialization_eq_mfderiv i Q₀ Q (by simpa [extChartAt] using hQ)
  have hCoords' :
      NormedSpace.fromTangentSpace (extChartAt (𝓡 7) Q₀ Q)
        (mfderiv (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) (extChartAt (𝓡 7) Q₀) Q
          (problem_8_7_frame i Q)) =
        (e ⟨Q, problem_8_7_frame i Q⟩).2 :=
    hCoords.symm
  have hTrivApply :
      (e ⟨Q, problem_8_7_frame i Q⟩).2 =
        e.continuousLinearMapAt ℝ Q (problem_8_7_frame i Q) := by
    -- Rewrite the second trivialization component as the associated fiberwise linear map.
    symm
    exact e.continuousLinearMapAt_apply_of_mem ℝ hQBase
      (problem_8_7_frame i Q)
  have hCancel :
      e.symmL ℝ Q (e ⟨Q, problem_8_7_frame i Q⟩).2 = problem_8_7_frame i Q := by
    -- Applying the inverse fiber coordinate map to the trivialized vector recovers the original
    -- tangent vector.
    rw [hTrivApply]
    simpa [e] using
      (e.symmL_continuousLinearMapAt hQBase (problem_8_7_frame i Q))
  let x :
      EuclideanSpace ℝ (Fin 7) :=
    NormedSpace.fromTangentSpace (extChartAt (𝓡 7) Q₀ Q)
      (mfderiv (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) (extChartAt (𝓡 7) Q₀) Q
        (problem_8_7_frame i Q))
  -- Rewrite the ambient coordinate map as the derivative of the sphere inclusion after the fixed
  -- source inverse trivialization, then identify the chart-side frame coordinates.
  have hStep1 :
      problem_8_7_frameAmbientCoordMap Q₀ Q x =
        ((mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q).comp
          (e.symmL ℝ Q)) x := by
    simpa [e, x] using
      congrArg (fun L : EuclideanSpace ℝ (Fin 7) →L[ℝ] 𝕆₂ ↦ L x)
        (problem_8_7_frameAmbientCoordMap_eq_trivializationComposition Q₀ Q)
  have hStep2 :
      ((mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q).comp
          (e.symmL ℝ Q)) x =
        mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q
          (e.symmL ℝ Q (e ⟨Q, problem_8_7_frame i Q⟩).2) := by
    simp [x, ContinuousLinearMap.comp_apply, hCoords']
  have hStep3 :
      mfderiv (𝓡 7) 𝓘(ℝ, 𝕆₂) ((↑) : unitOctonionSphere → 𝕆₂) Q
          (e.symmL ℝ Q (e ⟨Q, problem_8_7_frame i Q⟩).2) =
        WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)) := by
    rw [hCancel]
    simpa using problem_8_7_frame_coe_mfderiv_apply i Q
  exact hStep1.trans (hStep2.trans hStep3)

/-- Helper for Problem 8-7: near `Q₀`, the fixed-base ambient coordinate map carries the intrinsic
frame coordinates to the explicit ambient octonion field. -/
private theorem problem_8_7_frameAmbientCoordMap_apply_frameChartRep_eventuallyEq
    (i : Fin 7) (Q₀ : unitOctonionSphere) :
    (fun Q : unitOctonionSphere ↦
      problem_8_7_frameAmbientCoordMap Q₀ Q
        (NormedSpace.fromTangentSpace (extChartAt (𝓡 7) Q₀ Q)
          (mfderiv (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) (extChartAt (𝓡 7) Q₀) Q
            (problem_8_7_frame i Q)))) =ᶠ[nhds Q₀]
      (fun Q : unitOctonionSphere ↦ WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆))) := by
  have hSource : (extChartAt (𝓡 7) Q₀).source ∈ nhds Q₀ := extChartAt_source_mem_nhds Q₀
  filter_upwards [hSource] with Q hQ
  -- The pointwise normalization holds everywhere on the preferred-chart source.
  exact problem_8_7_frameAmbientCoordMap_apply_frameChartRep i Q₀ Q hQ

/-- Helper for Problem 8-7: smoothness of the intrinsic frame reduces to the fixed-base
preferred-chart expression. -/
private theorem problem_8_7_frame_contMDiffAt
    (i : Fin 7) (Q₀ : unitOctonionSphere) :
    ContMDiffAt (𝓡 7) (𝓡 7).tangent ∞ (T% (problem_8_7_frame i)) Q₀ := by
  -- Reduce section smoothness to the fixed tangent-bundle trivialization at `Q₀`.
  rw [Bundle.contMDiffAt_section Q₀]
  have hRetSmooth :
      ContMDiffAt (𝓡 7) (𝓡 7) ∞
        (fun Q : unitOctonionSphere ↦
          NormedSpace.fromTangentSpace
            ((extChartAt (𝓡 7) Q₀) (problem_8_7_localSphereRetraction Q₀ (Q : 𝕆₂)))
            (mfderiv 𝓘(ℝ, 𝕆₂) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7))
              ((extChartAt (𝓡 7) Q₀) ∘ problem_8_7_localSphereRetraction Q₀) (Q : 𝕆₂)
              ((NormedSpace.fromTangentSpace (Q : 𝕆₂)).symm
                (WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)))))) Q₀ :=
    problem_8_7_retractionChartRep_contMDiffAt i Q₀
  have hRetEq :
      (fun Q : unitOctonionSphere ↦
        NormedSpace.fromTangentSpace (extChartAt (𝓡 7) Q₀ Q)
          (mfderiv (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) (extChartAt (𝓡 7) Q₀) Q
            (problem_8_7_frame i Q))) =ᶠ[nhds Q₀]
      (fun Q : unitOctonionSphere ↦
        NormedSpace.fromTangentSpace
          ((extChartAt (𝓡 7) Q₀) (problem_8_7_localSphereRetraction Q₀ (Q : 𝕆₂)))
          (mfderiv 𝓘(ℝ, 𝕆₂) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7))
            ((extChartAt (𝓡 7) Q₀) ∘ problem_8_7_localSphereRetraction Q₀) (Q : 𝕆₂)
            ((NormedSpace.fromTangentSpace (Q : 𝕆₂)).symm
              (WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)))))) := by
    have hOpen :
        IsOpen {Q : unitOctonionSphere | (Q : 𝕆₂) ≠ -(Q₀ : 𝕆₂)} := by
      -- Near `Q₀`, sphere points avoid the antipode used as the stereographic center.
      have hClosed :
          IsClosed {Q : unitOctonionSphere | (Q : 𝕆₂) = -(Q₀ : 𝕆₂)} := by
        simpa [Set.preimage, Set.setOf_eq_eq_singleton] using
          ((isClosed_singleton : IsClosed ({-(Q₀ : 𝕆₂)} : Set 𝕆₂)).preimage
            continuous_subtype_val)
      simpa [Set.compl_setOf] using hClosed.isOpen_compl
    have hNear :
        {Q : unitOctonionSphere | (Q : 𝕆₂) ≠ -(Q₀ : 𝕆₂)} ∈ nhds Q₀ :=
      hOpen.mem_nhds (problem_8_7_self_ne_neg Q₀)
    have hSource : (extChartAt (𝓡 7) Q₀).source ∈ nhds Q₀ :=
      extChartAt_source_mem_nhds Q₀
    filter_upwards [hNear, hSource] with Q hQ hQSource
    have hRetEqPoint :
        problem_8_7_localSphereRetraction Q₀ (Q : 𝕆₂) = Q :=
      problem_8_7_localSphereRetraction_eq_self_of_ne Q₀ Q hQ
    have hRetDiff :
        MDifferentiableAt 𝓘(ℝ, 𝕆₂) (𝓡 7) (problem_8_7_localSphereRetraction Q₀) (Q : 𝕆₂) :=
      (problem_8_7_localSphereRetraction_contMDiffAt_of_ne Q₀
        (problem_8_7_inner_negBase_ne_one_of_ne Q₀ Q hQ)).mdifferentiableAt
          (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hQChart : Q ∈ (chartAt (EuclideanSpace ℝ (Fin 7)) Q₀).source := by
      -- The extended chart uses the same source as the preferred chart.
      simpa [extChartAt] using hQSource
    have hChartDiff :
        MDifferentiableAt (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7))
          (extChartAt (𝓡 7) Q₀) Q :=
      (contMDiffAt_extChartAt' hQChart).mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hComp :
        mfderiv 𝓘(ℝ, 𝕆₂) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7))
          ((extChartAt (𝓡 7) Q₀) ∘ problem_8_7_localSphereRetraction Q₀) (Q : 𝕆₂)
          ((NormedSpace.fromTangentSpace (Q : 𝕆₂)).symm
            (WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)))) =
        mfderiv (𝓡 7) 𝓘(ℝ, EuclideanSpace ℝ (Fin 7)) (extChartAt (𝓡 7) Q₀) Q
          (mfderiv 𝓘(ℝ, 𝕆₂) (𝓡 7) (problem_8_7_localSphereRetraction Q₀) (Q : 𝕆₂)
            ((NormedSpace.fromTangentSpace (Q : 𝕆₂)).symm
              (WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆))))) := by
      -- Differentiate the charted retraction by the chain rule at the non-antipodal point `Q`.
      simpa [Function.comp, extChartAt] using
        (mfderiv_comp_apply_of_eq (Q : 𝕆₂) hChartDiff hRetDiff hRetEqPoint
          ((NormedSpace.fromTangentSpace (Q : 𝕆₂)).symm
            (WithLp.toLp 2 (problem_8_7_vectorField i (Q : 𝕆)))))
    -- On the intersection of the chart source and the non-antipodal neighborhood, the charted
    -- retraction derivative reproduces the preferred-chart coordinates of the intrinsic frame.
    rw [hRetEqPoint, hComp]
    rw [problem_8_7_localSphereRetraction_mfderiv_apply_ambientField_of_ne i Q₀ Q hQ]
  -- Transfer smoothness from the retraction-based chart representative to the actual frame
  -- coordinates, then back to the fixed tangent-bundle trivialization coordinates.
  exact (hRetSmooth.congr_of_eventuallyEq hRetEq).congr_of_eventuallyEq
    (problem_8_7_frameTrivialization_eventuallyEq_mfderiv i Q₀)

/-- The intrinsic octonionic frame is smooth on the unit sphere. -/
theorem problem_8_7_frame_contMDiffOn (i : Fin 7) :
    -- Route correction: the intrinsic/ambient identification is now factored through
    -- `problem_8_7_frame_coe_mfderiv_apply`, so only the chart-side transport from the preferred
    -- tangent-bundle trivialization to an explicit ambient-field formula remains unresolved.
    ContMDiffOn (𝓡 7) (𝓡 7).tangent ∞ (T% (problem_8_7_frame i)) Set.univ := by
  intro Q₀ hQ₀
  -- Smoothness on `Set.univ` is pointwise smoothness, already isolated in
  -- `problem_8_7_frame_contMDiffAt`.
  simpa using (problem_8_7_frame_contMDiffAt i Q₀).contMDiffWithinAt

/-- The explicit octonionic right-multiplication fields by the seven standard imaginary basis
vectors form a smooth global frame on the unit sphere `S^7`. -/
theorem problem_8_7_frame_isLocalFrameOn :
    IsLocalFrameOn (𝓡 7) (EuclideanSpace ℝ (Fin 7)) ∞ problem_8_7_frame Set.univ := by
  -- Package the pointwise independence, spanning, and smoothness data into the local-frame owner.
  refine
    { linearIndependent := by
        intro Q hQ
        exact problem_8_7_frame_linearIndependent Q
      generating := by
        intro Q hQ
        letI : FiniteDimensional ℝ (TangentSpace (𝓡 7) Q) := by
          change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 7))
          infer_instance
        have hcard :
            Fintype.card (Fin 7) = Module.finrank ℝ (TangentSpace (𝓡 7) Q) := by
          change Fintype.card (Fin 7) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 7))
          exact (@finrank_euclideanSpace_fin ℝ _ 7).symm
        exact
          (problem_8_7_frame_linearIndependent Q).span_eq_top_of_card_eq_finrank' hcard |>.ge
      contMDiffOn := by
        intro i
        exact problem_8_7_frame_contMDiffOn i }

/-- First part of Problem 8-7: the octonion algebra on `𝕆 = ℍ × ℍ` is noncommutative. -/
theorem problem_8_7_noncommutative :
    ∃ P Q : 𝕆, octonionMul P Q ≠ octonionMul Q P :=
  ⟨problem_8_7_basisVec 0, problem_8_7_basisVec 1, octonion_noncommutative⟩

/-- Second part of Problem 8-7: the octonion algebra on `𝕆 = ℍ × ℍ` is nonassociative. -/
theorem problem_8_7_nonassociative :
    ∃ P Q R : 𝕆, octonionMul (octonionMul P Q) R ≠ octonionMul P (octonionMul Q R) :=
  ⟨problem_8_7_basisVec 0, problem_8_7_basisVec 1, problem_8_7_basisVec 3,
    octonion_nonassociative⟩

/-- Problem 8-7 (3). There exists a smooth global frame on the unit sphere `S^7`. -/
theorem problem_8_7_isLocalFrameOn :
    ∃ Φ : Fin 7 → (Q : unitOctonionSphere) → TangentSpace (𝓡 7) Q,
      IsLocalFrameOn (𝓡 7) (EuclideanSpace ℝ (Fin 7)) ∞ Φ Set.univ :=
  ⟨problem_8_7_frame, problem_8_7_frame_isLocalFrameOn⟩

end
