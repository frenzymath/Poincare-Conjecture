import Mathlib

namespace Topping
namespace ParabolicPDE

open scoped Topology

/-!
A scalar second-order operator is represented here by its coefficient fields.
The `a` field is the principal (second-order) coefficient; `b` and `c` retain
the lower-order coefficients from the coordinate expression.
-/
structure ScalarSecondOrderCoefficients (Ω : Type*) (n : ℕ) where
  a : Ω → Matrix (Fin n) (Fin n) ℝ
  b : Ω → Fin n → ℝ
  c : Ω → ℝ

/-- A scalar second-order jet in local coordinates. -/
structure ScalarSecondOrderJet (n : ℕ) where
  value : ℝ
  first : Fin n → ℝ
  second : Fin n → Fin n → ℝ


/-!
The formal product-rule jet after conjugation by an exponential phase.

This is an algebraic jet construction: it records the coefficients of the
conjugated product after the common exponential factor has been cancelled,
without asserting that the formal jets come from smooth functions.
-/
def normalizedConjugatedJet {n : ℕ} (s : ℝ)
    (φ f : ScalarSecondOrderJet n) : ScalarSecondOrderJet n where
  value := f.value
  first := fun i => s * φ.first i * f.value + f.first i
  second := fun i k =>
    s ^ 2 * φ.first i * φ.first k * f.value +
      s * (φ.second i k * f.value + φ.first i * f.first k +
        φ.first k * f.first i) + f.second i k

namespace ScalarSecondOrderCoefficients

variable {Ω : Type*} {n : ℕ} (A : ScalarSecondOrderCoefficients Ω n)

/-- Evaluation of the local scalar operator on a formal second-order jet. -/
def applyJet (x : Ω) (j : ScalarSecondOrderJet n) : ℝ :=
  (∑ i, ∑ k, A.a x i k * j.second i k) +
    (∑ i, A.b x i * j.first i) + A.c x * j.value

/-! The operator evaluated on the normalized conjugated jet. -/
def conjugatedScalarOperator (x : Ω) (s : ℝ)
    (φ f : ScalarSecondOrderJet n) : ℝ :=
  A.applyJet x (normalizedConjugatedJet s φ f)

/-! The coefficient of the term linear in the conjugation parameter. -/
def conjugatedScalarOperatorLinearTerm (x : Ω)
    (φ f : ScalarSecondOrderJet n) : ℝ :=
  (∑ i, ∑ k, A.a x i k *
      (φ.second i k * f.value + φ.first i * f.first k +
        φ.first k * f.first i)) +
    ∑ i, A.b x i * (φ.first i * f.value)

/-! The parameter-independent part of the conjugated operator. -/
def conjugatedScalarOperatorConstantTerm (x : Ω)
    (f : ScalarSecondOrderJet n) : ℝ :=
  (∑ i, ∑ k, A.a x i k * f.second i k) +
    ∑ i, A.b x i * f.first i + A.c x * f.value

end ScalarSecondOrderCoefficients

/-- The squared Euclidean length of a coordinate covector. -/
def euclideanNormSq {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  ∑ i, ξ i ^ 2

/-- The scalar principal symbol of a matrix of second-order coefficients. -/
def symbol {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) : ℝ :=
  dotProduct ξ (a.mulVec ξ)

/-- The principal symbol of a coefficient field at a base point. -/
def ScalarSecondOrderCoefficients.principalSymbol
    {Ω : Type*} {n : ℕ} (A : ScalarSecondOrderCoefficients Ω n)
    (x : Ω) (ξ : Fin n → ℝ) : ℝ :=
  symbol (A.a x) ξ

/-- Positivity of a scalar quadratic form away from the zero covector. -/
def IsPositiveDefinite {n : ℕ}
    (a : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ ξ, ξ ≠ 0 → 0 < symbol a ξ

/-- Pointwise parabolicity of scalar coefficients. -/
def PointwiseParabolic {Ω : Type*} {n : ℕ}
    (A : ScalarSecondOrderCoefficients Ω n) : Prop :=
  ∀ x, IsPositiveDefinite (A.a x)

/-- Uniform parabolicity with a common coercivity constant. -/
def UniformlyParabolic {Ω : Type*} {n : ℕ}
    (A : ScalarSecondOrderCoefficients Ω n) : Prop :=
  ∃ ell : ℝ, 0 < ell ∧
    ∀ x ξ, ell * euclideanNormSq ξ ≤ A.principalSymbol x ξ

theorem pointwiseParabolic_iff_symbol_positive
    {Ω : Type*} {n : ℕ} {A : ScalarSecondOrderCoefficients Ω n} :
    PointwiseParabolic A ↔
      ∀ x ξ, ξ ≠ 0 → 0 < A.principalSymbol x ξ := by
  rfl

theorem symbol_zero {n : ℕ} (ξ : Fin n → ℝ) :
    symbol (0 : Matrix (Fin n) (Fin n) ℝ) ξ = 0 := by
  simp [symbol]

theorem symbol_add {n : ℕ}
    (a₁ a₂ : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    symbol (a₁ + a₂) ξ =
      symbol a₁ ξ + symbol a₂ ξ := by
  unfold symbol
  rw [Matrix.add_mulVec]
  simp only [dotProduct]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply, mul_add]

theorem symbol_smul {n : ℕ} (r : ℝ)
    (a : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    symbol (r • a) ξ = r * symbol a ξ := by
  unfold symbol
  rw [Matrix.smul_mulVec]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, ξ i * (r * a.mulVec ξ i)) =
        ∑ i, r * (ξ i * a.mulVec ξ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = r * ∑ i, ξ i * a.mulVec ξ i := by
      rw [Finset.mul_sum]

theorem symbol_smul_covector {n : ℕ} (r : ℝ)
    (a : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    symbol a (r • ξ) = r ^ 2 * symbol a ξ := by
  unfold symbol
  rw [Matrix.mulVec_smul]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, (r * ξ i) * (r * a.mulVec ξ i)) =
        ∑ i, r ^ 2 * (ξ i * a.mulVec ξ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = r ^ 2 * ∑ i, ξ i * a.mulVec ξ i := by
      rw [Finset.mul_sum]

theorem symbol_eq_sum {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (ξ : Fin n → ℝ) :
    symbol a ξ = ∑ i, ∑ k, a i k * ξ i * ξ k := by
  unfold symbol
  simp only [dotProduct, Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    ξ i * ∑ k, a i k * ξ k =
        ∑ k, ξ i * (a i k * ξ k) := by rw [Finset.mul_sum]
    _ = ∑ k, a i k * ξ i * ξ k := by
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem symbol_one {n : ℕ} (ξ : Fin n → ℝ) :
    symbol (1 : Matrix (Fin n) (Fin n) ℝ) ξ =
      euclideanNormSq ξ := by
  simp [symbol, euclideanNormSq, dotProduct, pow_two]

theorem euclideanNormSq_nonneg {n : ℕ} (ξ : Fin n → ℝ) :
    0 ≤ euclideanNormSq ξ := by
  exact Finset.sum_nonneg' (fun i => sq_nonneg (ξ i))

theorem euclideanNormSq_pos {n : ℕ} {ξ : Fin n → ℝ} (hξ : ξ ≠ 0) :
    0 < euclideanNormSq ξ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hξ
  have hi' : ξ i ≠ 0 := by simpa using hi
  have hiff :
      0 < ∑ j : Fin n, ξ j ^ 2 ↔
        ∃ j ∈ (Finset.univ : Finset (Fin n)), 0 < ξ j ^ 2 :=
    Finset.sum_pos_iff_of_nonneg (fun j hj => sq_nonneg (ξ j))
  rw [euclideanNormSq, hiff]
  exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi'⟩

theorem uniformlyParabolic_pointwiseParabolic
    {Ω : Type*} {n : ℕ} {A : ScalarSecondOrderCoefficients Ω n}
    (hA : UniformlyParabolic A) : PointwiseParabolic A := by
  obtain ⟨ell, hell, hbound⟩ := hA
  intro x ξ hξ
  have hnorm : 0 < euclideanNormSq ξ := euclideanNormSq_pos hξ
  have hscaled : 0 < ell * euclideanNormSq ξ := mul_pos hell hnorm
  exact lt_of_lt_of_le hscaled (hbound x ξ)

/-- Coefficients for the Euclidean heat equation. -/
def heatCoefficients (Ω : Type*) (n : ℕ) :
    ScalarSecondOrderCoefficients Ω n where
  a := fun _ => 1
  b := fun _ _ => 0
  c := fun _ => 0

theorem heatCoefficients_principalSymbol {Ω : Type*} {n : ℕ}
    (x : Ω) (ξ : Fin n → ℝ) :
    (heatCoefficients Ω n).principalSymbol x ξ = euclideanNormSq ξ := by
  change symbol (1 : Matrix (Fin n) (Fin n) ℝ) ξ = _
  exact symbol_one ξ

theorem heatCoefficients_uniformlyParabolic (Ω : Type*) (n : ℕ) :
    UniformlyParabolic (heatCoefficients Ω n) := by
  refine ⟨1, by norm_num, ?_⟩
  intro x ξ
  rw [heatCoefficients_principalSymbol]
  simp

theorem heatCoefficients_pointwiseParabolic (Ω : Type*) (n : ℕ) :
    PointwiseParabolic (heatCoefficients Ω n) :=
  uniformlyParabolic_pointwiseParabolic (heatCoefficients_uniformlyParabolic Ω n)

theorem principalSymbol_congr
    {Ω : Type*} {n : ℕ}
    {A B : ScalarSecondOrderCoefficients Ω n}
    (h : ∀ x, A.a x = B.a x) (x : Ω) (ξ : Fin n → ℝ) :
    A.principalSymbol x ξ = B.principalSymbol x ξ := by
  simp [ScalarSecondOrderCoefficients.principalSymbol, h x]

/-- The scalar symbol is covariant under a linear change of cotangent
coordinates.  If `J` sends new covector coordinates to old ones, then the
leading matrix in the new coordinates is `J.transpose * a * J`. -/
theorem symbol_congruence {m n : ℕ}
    (J : Matrix (Fin m) (Fin n) ℝ)
    (a : Matrix (Fin m) (Fin m) ℝ) (ξ : Fin n → ℝ) :
    symbol (J.transpose * a * J) ξ = symbol a (J.mulVec ξ) := by
  unfold symbol
  calc
    ξ ⬝ᵥ (J.transpose * a * J).mulVec ξ =
        ξ ⬝ᵥ (J.transpose * a).mulVec (J.mulVec ξ) :=
      congrArg (fun z => ξ ⬝ᵥ z)
        (Matrix.mulVec_mulVec ξ (J.transpose * a) J).symm
    _ = ξ ⬝ᵥ J.transpose.mulVec (a.mulVec (J.mulVec ξ)) :=
      congrArg (fun z => ξ ⬝ᵥ z)
        (Matrix.mulVec_mulVec (J.mulVec ξ) J.transpose a).symm
    _ = a.mulVec (J.mulVec ξ) ⬝ᵥ J.mulVec ξ :=
      Matrix.dotProduct_transpose_mulVec J ξ (a.mulVec (J.mulVec ξ))
    _ = J.mulVec ξ ⬝ᵥ a.mulVec (J.mulVec ξ) :=
      dotProduct_comm _ _

/-- Positive definiteness is preserved by an injective linear change of
covector coordinates.  In coordinate changes, injectivity is supplied by the
invertible chart Jacobian. -/
theorem IsPositiveDefinite.congruence {m n : ℕ}
    (J : Matrix (Fin m) (Fin n) ℝ)
    (a : Matrix (Fin m) (Fin m) ℝ)
    (ha : IsPositiveDefinite a)
    (hJ : Function.Injective J.mulVec) :
    IsPositiveDefinite (J.transpose * a * J) := by
  intro ξ hξ
  rw [symbol_congruence]
  apply ha
  intro hzero
  apply hξ
  apply hJ
  simpa using hzero

theorem conjugatedScalarOperator_eq_quadratic_plus_lower
    {Ω : Type*} {n : ℕ}
    (A : ScalarSecondOrderCoefficients Ω n)
    (x : Ω) (s : ℝ) (φ f : ScalarSecondOrderJet n) :
    A.conjugatedScalarOperator x s φ f =
      s ^ 2 * (f.value * A.principalSymbol x φ.first) +
        s * A.conjugatedScalarOperatorLinearTerm x φ f +
        A.conjugatedScalarOperatorConstantTerm x f := by
  have hquad :
      (∑ i, ∑ k, A.a x i k *
          (s ^ 2 * φ.first i * φ.first k * f.value)) =
        s ^ 2 * (f.value * symbol (A.a x) φ.first) := by
    simp only [symbol, dotProduct, Matrix.mulVec]
    have hinner :
        (∑ i, ∑ k, φ.first i * (A.a x i k * φ.first k)) =
          ∑ i, φ.first i * ∑ k, A.a x i k * φ.first k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    calc
      (∑ i, ∑ k, A.a x i k *
          (s ^ 2 * φ.first i * φ.first k * f.value)) =
          ∑ i, ∑ k, s ^ 2 * f.value *
            (φ.first i * (A.a x i k * φ.first k)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = ∑ i, s ^ 2 * f.value *
          ∑ k, φ.first i * (A.a x i k * φ.first k) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = s ^ 2 * f.value *
          ∑ i, ∑ k, φ.first i * (A.a x i k * φ.first k) := by
        rw [Finset.mul_sum]
      _ = s ^ 2 * (f.value *
          ∑ i, φ.first i * ∑ k, A.a x i k * φ.first k) := by
        rw [hinner]
        ring
  have hlinA :
      (∑ i, ∑ k, A.a x i k *
          (s * (φ.second i k * f.value + φ.first i * f.first k +
            φ.first k * f.first i))) =
        s * (∑ i, ∑ k, A.a x i k *
          (φ.second i k * f.value + φ.first i * f.first k +
            φ.first k * f.first i)) := by
    calc
      (∑ i, ∑ k, A.a x i k *
          (s * (φ.second i k * f.value + φ.first i * f.first k +
            φ.first k * f.first i))) =
          ∑ i, ∑ k, s * (A.a x i k *
            (φ.second i k * f.value + φ.first i * f.first k +
              φ.first k * f.first i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = ∑ i, s * ∑ k, A.a x i k *
          (φ.second i k * f.value + φ.first i * f.first k +
            φ.first k * f.first i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = s * (∑ i, ∑ k, A.a x i k *
          (φ.second i k * f.value + φ.first i * f.first k +
            φ.first k * f.first i)) := by
        rw [Finset.mul_sum]
  have hlinB :
      (∑ i, A.b x i * (s * φ.first i * f.value)) =
        s * (∑ i, A.b x i * (φ.first i * f.value)) := by
    calc
      (∑ i, A.b x i * (s * φ.first i * f.value)) =
          ∑ i, s * (A.b x i * (φ.first i * f.value)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = s * (∑ i, A.b x i * (φ.first i * f.value)) := by
        rw [Finset.mul_sum]
  unfold ScalarSecondOrderCoefficients.conjugatedScalarOperator
    ScalarSecondOrderCoefficients.applyJet normalizedConjugatedJet
  dsimp
  calc
    (∑ i, ∑ k, A.a x i k *
        (s ^ 2 * φ.first i * φ.first k * f.value +
          s * (φ.second i k * f.value + φ.first i * f.first k +
            φ.first k * f.first i) + f.second i k)) +
        (∑ i, A.b x i *
          (s * φ.first i * f.value + f.first i)) + A.c x * f.value =
      (∑ i, ∑ k, A.a x i k *
        (s ^ 2 * φ.first i * φ.first k * f.value)) +
      (∑ i, ∑ k, A.a x i k *
        (s * (φ.second i k * f.value + φ.first i * f.first k +
          φ.first k * f.first i))) +
      (∑ i, ∑ k, A.a x i k * f.second i k) +
      (∑ i, A.b x i * (s * φ.first i * f.value)) +
      (∑ i, A.b x i * f.first i) + A.c x * f.value := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        ring
    _ = s ^ 2 * (f.value * A.principalSymbol x φ.first) +
        s * A.conjugatedScalarOperatorLinearTerm x φ f +
        A.conjugatedScalarOperatorConstantTerm x f := by
      rw [hquad, hlinA, hlinB]
      unfold ScalarSecondOrderCoefficients.conjugatedScalarOperatorLinearTerm
        ScalarSecondOrderCoefficients.conjugatedScalarOperatorConstantTerm
        ScalarSecondOrderCoefficients.principalSymbol
      ring

theorem tendsto_normalized_quadratic_polynomial
    {q r t : ℝ} :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 * (s ^ 2 * q + s * r + t))
      Filter.atTop (𝓝 q) := by
  have hinv : Filter.Tendsto (fun s : ℝ => s⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hinv2 : Filter.Tendsto (fun s : ℝ => s⁻¹ ^ 2) Filter.atTop (𝓝 0) := by
    simpa [pow_two] using hinv.mul hinv
  have hlin : Filter.Tendsto (fun s : ℝ => s⁻¹ * r)
      Filter.atTop (𝓝 0) := by
    simpa using hinv.mul tendsto_const_nhds
  have hconst : Filter.Tendsto (fun _ : ℝ => q) Filter.atTop (𝓝 q) :=
    tendsto_const_nhds
  have hsum :
      Filter.Tendsto (fun s : ℝ => q + s⁻¹ * r + s⁻¹ ^ 2 * t)
        Filter.atTop (𝓝 q) := by
    have hquad : Filter.Tendsto (fun s : ℝ => s⁻¹ ^ 2 * t)
        Filter.atTop (𝓝 0) := by
      simpa using hinv2.mul tendsto_const_nhds
    have hfirst := hconst.add hlin
    have hsecond := hfirst.add hquad
    simpa [add_assoc] using hsecond
  apply hsum.congr'
  filter_upwards [Filter.eventually_atTop.2
      ⟨(1 : ℝ), fun s hs => ne_of_gt (lt_of_lt_of_le zero_lt_one hs)⟩] with s hs
  field_simp [hs]

theorem conjugatedScalarOperator_normalized_tendsto
    {Ω : Type*} {n : ℕ}
    (A : ScalarSecondOrderCoefficients Ω n)
    (x : Ω) (φ f : ScalarSecondOrderJet n) :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 * A.conjugatedScalarOperator x s φ f)
      Filter.atTop (𝓝 (f.value * A.principalSymbol x φ.first)) := by
  simpa only [conjugatedScalarOperator_eq_quadratic_plus_lower] using
    (tendsto_normalized_quadratic_polynomial
      (q := f.value * A.principalSymbol x φ.first)
      (r := A.conjugatedScalarOperatorLinearTerm x φ f)
      (t := A.conjugatedScalarOperatorConstantTerm x f))

theorem scalarPrincipalSymbol_limit
    {Ω : Type*} {n : ℕ}
    (A : ScalarSecondOrderCoefficients Ω n)
    (x : Ω) (φ f : ScalarSecondOrderJet n) :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 * A.conjugatedScalarOperator x s φ f)
      Filter.atTop (𝓝 (f.value * A.principalSymbol x φ.first)) :=
  conjugatedScalarOperator_normalized_tendsto A x φ f

end ParabolicPDE
end Topping
