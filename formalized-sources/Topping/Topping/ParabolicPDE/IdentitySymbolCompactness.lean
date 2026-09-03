import Topping.ParabolicPDE.Compactness

namespace Topping
namespace ParabolicPDE

noncomputable section

open scoped Topology

/-!
# Continuous multipliers for positive identity symbols

The compactness consumers in `Compactness.lean` take a scalar multiplier as
input.  A pointwise positive identity representation initially supplies only
an existential scalar at each nonzero covector.  This file makes the scalar
canonical: evaluate the symbol on one fixed nonzero fibre vector and divide
by its squared norm.  The resulting multiplier is continuous whenever the
CLM-valued symbol is continuous, and the pointwise existential representation
then identifies it with the original scalar.
-/

/-- Recover the scalar coefficient of an endomorphism-valued symbol by testing
it on a fixed nonzero fibre vector. -/
def identitySymbolMultiplier {X ι V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (sigma : X → (ι → ℝ) → V →L[ℝ] V) (v₀ : V) :
    X → (ι → ℝ) → ℝ :=
  fun x xi => inner ℝ (sigma x xi v₀) v₀ / ‖v₀‖ ^ 2

/-- The evaluation formula recovers an identity coefficient exactly. -/
theorem identitySymbolMultiplier_eq_of_identity
    {X ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (sigma : X → (ι → ℝ) → V →L[ℝ] V) (v₀ : V) (hv₀ : v₀ ≠ 0)
    {x : X} {xi : ι → ℝ} {a : ℝ}
    (hrep : sigma x xi = a • ContinuousLinearMap.id ℝ V) :
    identitySymbolMultiplier sigma v₀ x xi = a := by
  unfold identitySymbolMultiplier
  rw [hrep]
  simp only [smul_apply, ContinuousLinearMap.id_apply]
  rw [real_inner_smul_left]
  rw [real_inner_self_eq_norm_sq]
  field_simp [pow_two, (norm_ne_zero_iff.mpr hv₀)]

/-- The recovered multiplier is continuous on the base/covector product. -/
theorem continuous_identitySymbolMultiplier
    {X ι V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (sigma : X → (ι → ℝ) → V →L[ℝ] V) (v₀ : V)
    (hsigma : Continuous (fun p : X × (ι → ℝ) => sigma p.1 p.2)) :
    Continuous (fun p : X × (ι → ℝ) =>
      identitySymbolMultiplier sigma v₀ p.1 p.2) := by
  have hnum : Continuous (fun p : X × (ι → ℝ) =>
      inner ℝ (sigma p.1 p.2 v₀) v₀) := by
    exact (hsigma.clm_apply continuous_const).inner continuous_const
  simpa [identitySymbolMultiplier] using
    hnum.div_const (‖v₀‖ ^ 2)

/-- Homogeneity of the CLM-valued symbol transfers to the recovered scalar. -/
theorem identitySymbolMultiplier_homogeneous
    {X ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (sigma : X → (ι → ℝ) → V →L[ℝ] V) (v₀ : V)
    (hsigma_hom : ∀ (x : X) (r : ℝ) (xi : ι → ℝ),
      sigma x (r • xi) = r ^ 2 • sigma x xi) :
    ∀ (x : X) (r : ℝ) (xi : ι → ℝ),
      identitySymbolMultiplier sigma v₀ x (r • xi) =
        r ^ 2 * identitySymbolMultiplier sigma v₀ x xi := by
  intro x r xi
  unfold identitySymbolMultiplier
  rw [hsigma_hom]
  simp only [smul_apply]
  rw [real_inner_smul_left]
  ring

/-- Degree-two homogeneity forces an endomorphism-valued symbol to vanish at
the zero covector. -/
theorem identitySymbol_zero_of_homogeneous
    {X ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {sigma : X → (ι → ℝ) → V →L[ℝ] V}
    (hsigma_hom : ∀ (x : X) (r : ℝ) (xi : ι → ℝ),
      sigma x (r • xi) = r ^ 2 • sigma x xi) :
    ∀ x, sigma x 0 = 0 := by
  intro x
  simpa using hsigma_hom x 0 (0 : ι → ℝ)

/-- At a nonzero covector, the recovered scalar is positive whenever the
symbol has a positive identity representation. -/
theorem identitySymbolMultiplier_pos_of_positive_identity
    {X ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (sigma : X → (ι → ℝ) → V →L[ℝ] V) (v₀ : V) (hv₀ : v₀ ≠ 0)
    (hpositive : IsPositiveMultipleOfIdentity sigma) :
    ∀ (x : X) (xi : ι → ℝ), xi ≠ 0 →
      0 < identitySymbolMultiplier sigma v₀ x xi := by
  intro x xi hxi
  obtain ⟨a, ha, hrep⟩ := hpositive x xi hxi
  rw [identitySymbolMultiplier_eq_of_identity sigma v₀ hv₀ hrep]
  exact ha

/-- The pointwise existential identity representation becomes a single global
representation after choosing the canonical multiplier.  The zero-covector
case uses the supplied vanishing hypothesis. -/
theorem identitySymbolMultiplier_representation
    {X ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (sigma : X → (ι → ℝ) → V →L[ℝ] V) (v₀ : V) (hv₀ : v₀ ≠ 0)
    (hzero : ∀ x, sigma x 0 = 0)
    (hpositive : IsPositiveMultipleOfIdentity sigma) :
    ∀ (x : X) (xi : ι → ℝ),
      sigma x xi =
        identitySymbolMultiplier sigma v₀ x xi •
          ContinuousLinearMap.id ℝ V := by
  intro x xi
  by_cases hxi : xi = 0
  · subst xi
    have hmu : identitySymbolMultiplier sigma v₀ x 0 = 0 := by
      simp [identitySymbolMultiplier, hzero x]
    rw [hzero x, hmu]
    simp
  · obtain ⟨a, _ha, hrep⟩ := hpositive x xi hxi
    rw [identitySymbolMultiplier_eq_of_identity sigma v₀ hv₀ hrep]
    exact hrep

/-- Package the canonical multiplier and all properties needed by the compact
unit-cosphere argument.  This is the non-tautological extraction step from a
continuous homogeneous CLM-valued symbol. -/
theorem exists_continuous_identitySymbolMultiplier
    {X ι V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (sigma : X → (ι → ℝ) → V →L[ℝ] V) (v₀ : V) (hv₀ : v₀ ≠ 0)
    (hsigma : Continuous (fun p : X × (ι → ℝ) => sigma p.1 p.2))
    (hsigma_hom : ∀ (x : X) (r : ℝ) (xi : ι → ℝ),
      sigma x (r • xi) = r ^ 2 • sigma x xi)
    (hpositive : IsPositiveMultipleOfIdentity sigma) :
    ∃ mu : X → (ι → ℝ) → ℝ,
      Continuous (fun p : X × (ι → ℝ) => mu p.1 p.2) ∧
      (∀ x xi, sigma x xi = mu x xi • ContinuousLinearMap.id ℝ V) ∧
      (∀ x xi, xi ≠ 0 → 0 < mu x xi) ∧
      (∀ x r xi, mu x (r • xi) = r ^ 2 * mu x xi) := by
  let mu := identitySymbolMultiplier sigma v₀
  refine ⟨mu, ?_, ?_, ?_, ?_⟩
  · exact continuous_identitySymbolMultiplier sigma v₀ hsigma
  · exact identitySymbolMultiplier_representation sigma v₀ hv₀
      (identitySymbol_zero_of_homogeneous hsigma_hom) hpositive
  · exact identitySymbolMultiplier_pos_of_positive_identity sigma v₀ hv₀ hpositive
  · exact identitySymbolMultiplier_homogeneous sigma v₀ hsigma_hom

/-! ## Uniform certificates -/

/-- Extract the uniform positive-multiple certificate consumed by the strict
parabolicity and fibre-metric comparison APIs. -/
theorem hasUniformPositiveMultiple_of_continuous_identitySymbol_compact_unitCosphere
    {X ι V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {sigma : X → (ι → ℝ) → V →L[ℝ] V}
    {q : X → (ι → ℝ) → ℝ}
    (v₀ : V) (hv₀ : v₀ ≠ 0)
    (hq : IsSquaredCovectorNorm q)
    (hsigma : Continuous (fun p : X × (ι → ℝ) => sigma p.1 p.2))
    (hsigma_hom : ∀ (x : X) (r : ℝ) (xi : ι → ℝ),
      sigma x (r • xi) = r ^ 2 • sigma x xi)
    (hpositive : IsPositiveMultipleOfIdentity sigma)
    (hcompact : IsCompact (unitCosphere q)) :
    HasUniformPositiveMultiple sigma q := by
  obtain ⟨mu, hmu_cont, hmu_rep, hmu_pos, hmu_hom⟩ :=
    exists_continuous_identitySymbolMultiplier sigma v₀ hv₀ hsigma hsigma_hom
      hpositive
  exact hasUniformPositiveMultiple_of_compact_unitCosphere hq hmu_rep hmu_pos
    hmu_hom hcompact hmu_cont.continuousOn

/-- A compact unit-cosphere and a continuous positive identity multiplier imply
strict parabolicity.  The multiplier is extracted from the symbol rather than
being supplied as an additional target-shaped hypothesis. -/
theorem StrictlyParabolic.of_continuous_identitySymbol_compact_unitCosphere
    {X ι V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {sigma : X → (ι → ℝ) → V →L[ℝ] V}
    {q : X → (ι → ℝ) → ℝ}
    (v₀ : V) (hv₀ : v₀ ≠ 0)
    (hq : IsSquaredCovectorNorm q)
    (hsigma : Continuous (fun p : X × (ι → ℝ) => sigma p.1 p.2))
    (hsigma_hom : ∀ (x : X) (r : ℝ) (xi : ι → ℝ),
      sigma x (r • xi) = r ^ 2 • sigma x xi)
    (hpositive : IsPositiveMultipleOfIdentity sigma)
    (hcompact : IsCompact (unitCosphere q)) :
    StrictlyParabolic sigma q := by
  apply StrictlyParabolic.of_hasUniformPositiveMultiple hq
  exact hasUniformPositiveMultiple_of_continuous_identitySymbol_compact_unitCosphere
    v₀ hv₀ hq hsigma hsigma_hom hpositive hcompact

/-- Euclidean compact-base specialization of the uniform positive-multiple
certificate. -/
theorem hasUniformPositiveMultiple_of_continuous_identitySymbol_euclideanNormSq_compactSpace
    {X V : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} {sigma : X → (Fin n → ℝ) → V →L[ℝ] V}
    (v₀ : V) (hv₀ : v₀ ≠ 0)
    (hsigma : Continuous (fun p : X × (Fin n → ℝ) => sigma p.1 p.2))
    (hsigma_hom : ∀ (x : X) (r : ℝ) (xi : Fin n → ℝ),
      sigma x (r • xi) = r ^ 2 • sigma x xi)
    (hpositive : IsPositiveMultipleOfIdentity sigma) :
    HasUniformPositiveMultiple sigma
      (fun _ xi => euclideanNormSq xi) := by
  obtain ⟨mu, hmu_cont, hmu_rep, hmu_pos, hmu_hom⟩ :=
    exists_continuous_identitySymbolMultiplier sigma v₀ hv₀ hsigma hsigma_hom
      hpositive
  exact hasUniformPositiveMultiple_euclideanNormSq_of_compactSpace hmu_rep
    hmu_pos hmu_hom hmu_cont

/-- Euclidean specialization: on a compact base, a continuous homogeneous
CLM-valued positive identity symbol is strictly parabolic for the Euclidean
covector norm. -/
theorem StrictlyParabolic.of_continuous_identitySymbol_euclideanNormSq_compactSpace
    {X V : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} {sigma : X → (Fin n → ℝ) → V →L[ℝ] V}
    (v₀ : V) (hv₀ : v₀ ≠ 0)
    (hsigma : Continuous (fun p : X × (Fin n → ℝ) => sigma p.1 p.2))
    (hsigma_hom : ∀ (x : X) (r : ℝ) (xi : Fin n → ℝ),
      sigma x (r • xi) = r ^ 2 • sigma x xi)
    (hpositive : IsPositiveMultipleOfIdentity sigma) :
    StrictlyParabolic sigma
      (fun _ xi => euclideanNormSq xi) := by
  apply StrictlyParabolic.of_hasUniformPositiveMultiple
    (euclideanNormSq_isSquaredCovectorNorm X n)
  exact hasUniformPositiveMultiple_of_continuous_identitySymbol_euclideanNormSq_compactSpace
    v₀ hv₀ hsigma hsigma_hom hpositive

#print axioms identitySymbolMultiplier_eq_of_identity
#print axioms continuous_identitySymbolMultiplier
#print axioms identitySymbolMultiplier_homogeneous
#print axioms identitySymbol_zero_of_homogeneous
#print axioms identitySymbolMultiplier_representation
#print axioms exists_continuous_identitySymbolMultiplier
#print axioms hasUniformPositiveMultiple_of_continuous_identitySymbol_compact_unitCosphere
#print axioms StrictlyParabolic.of_continuous_identitySymbol_compact_unitCosphere
#print axioms hasUniformPositiveMultiple_of_continuous_identitySymbol_euclideanNormSq_compactSpace
#print axioms StrictlyParabolic.of_continuous_identitySymbol_euclideanNormSq_compactSpace

end
end ParabolicPDE
end Topping
