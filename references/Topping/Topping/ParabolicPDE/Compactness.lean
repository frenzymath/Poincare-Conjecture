import Topping.ParabolicPDE.Scalar
import Topping.ParabolicPDE.Vector

/-!
# Compactness producers for strict parabolicity

This file supplies the concrete squared Euclidean covector norm and the
compact-unit-cosphere argument turning pointwise positive identity symbols
into a uniform strict-parabolicity bound.
-/

namespace Topping

noncomputable section

open scoped Topology

/-- The sum of squares in Euclidean cotangent coordinates is a squared
covector norm, uniformly over any base type. -/
theorem euclideanNormSq_isSquaredCovectorNorm (X : Type*) (n : ℕ) :
    IsSquaredCovectorNorm
      (fun (_ : X) (xi : Fin n → ℝ) => ParabolicPDE.euclideanNormSq xi) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp [ParabolicPDE.euclideanNormSq]
  · intro x xi
    exact ParabolicPDE.euclideanNormSq_nonneg xi
  · intro x xi hxi
    exact ParabolicPDE.euclideanNormSq_pos hxi
  · intro x r xi
    change ParabolicPDE.euclideanNormSq (r • xi) =
      r ^ 2 * ParabolicPDE.euclideanNormSq xi
    rw [← ParabolicPDE.symbol_one, ParabolicPDE.symbol_smul_covector,
      ParabolicPDE.symbol_one]

namespace ParabolicPDE

/-- The squared Euclidean coordinate norm is continuous. -/
theorem continuous_euclideanNormSq {n : ℕ} :
    Continuous (@euclideanNormSq n) := by
  unfold euclideanNormSq
  fun_prop

end ParabolicPDE

/-- The unit covectors for the Euclidean sum-of-squares norm. -/
def euclideanUnitCovectors (n : ℕ) : Set (Fin n → ℝ) :=
  {xi | ParabolicPDE.euclideanNormSq xi = 1}

@[simp] theorem mem_euclideanUnitCovectors {n : ℕ} {xi : Fin n → ℝ} :
    xi ∈ euclideanUnitCovectors n ↔ ParabolicPDE.euclideanNormSq xi = 1 :=
  Iff.rfl

/-- The Euclidean sum-of-squares unit level set is compact in the standard
finite-dimensional topology on `Fin n → ℝ`.

The ambient Pi norm is the maximum coordinate norm, so this is proved as a
closed, bounded set rather than identifying it definitionally with its metric
unit sphere. -/
theorem isCompact_euclideanUnitCovectors (n : ℕ) :
    IsCompact (euclideanUnitCovectors n) := by
  have hclosed : IsClosed (euclideanUnitCovectors n) := by
    change IsClosed ((@ParabolicPDE.euclideanNormSq n) ⁻¹' {1})
    exact isClosed_singleton.preimage
      ParabolicPDE.continuous_euclideanNormSq
  have hbounded : Bornology.IsBounded (euclideanUnitCovectors n) := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : Fin n → ℝ)]
    refine ⟨1, ?_⟩
    intro xi hxi
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro i
    have hsqi : xi i ^ 2 ≤ 1 := by
      calc
        xi i ^ 2 ≤ ∑ j, xi j ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (xi j))
            (Finset.mem_univ i)
        _ = 1 := hxi
    simpa [Real.norm_eq_abs] using
      (sq_le_one_iff_abs_le_one (xi i)).1 hsqi
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded

/-- The unit cosphere associated to a squared covector norm candidate. -/
def unitCosphere {X ι : Type*} (q : X → (ι → ℝ) → ℝ) :
    Set (X × (ι → ℝ)) :=
  {p | q p.1 p.2 = 1}

@[simp] theorem mem_unitCosphere {X ι : Type*}
    {q : X → (ι → ℝ) → ℝ} {p : X × (ι → ℝ)} :
    p ∈ unitCosphere q ↔ q p.1 p.2 = 1 :=
  Iff.rfl

/-- A covector on the unit cosphere is nonzero. -/
theorem unitCosphere_covector_ne_zero {X ι : Type*}
    {q : X → (ι → ℝ) → ℝ} (hq : IsSquaredCovectorNorm q)
    {p : X × (ι → ℝ)} (hp : p ∈ unitCosphere q) : p.2 ≠ 0 := by
  intro hpzero
  have hunit : q p.1 p.2 = 1 := hp
  rw [hpzero, hq.1 p.1] at hunit
  norm_num at hunit

/-- For the base-independent Euclidean norm, the unit cosphere is the product
of the base with the Euclidean unit-covector level set. -/
theorem unitCosphere_euclideanNormSq_eq (X : Type*) (n : ℕ) :
    unitCosphere
        (fun (_ : X) (xi : Fin n → ℝ) => ParabolicPDE.euclideanNormSq xi) =
      Set.univ ×ˢ euclideanUnitCovectors n := by
  ext p
  simp [unitCosphere, euclideanUnitCovectors]

/-- The Euclidean unit cosphere over a compact base is compact. -/
theorem isCompact_unitCosphere_euclideanNormSq
    (X : Type*) [TopologicalSpace X] [CompactSpace X] (n : ℕ) :
    IsCompact (unitCosphere
      (fun (_ : X) (xi : Fin n → ℝ) =>
        ParabolicPDE.euclideanNormSq xi)) := by
  rw [unitCosphere_euclideanNormSq_eq]
  exact isCompact_univ.prod (isCompact_euclideanUnitCovectors n)

/-- Compactness of the unit cosphere upgrades a continuous pointwise positive
identity symbol to a uniform positive multiple.

The lower bound is produced by minimizing `mu` on `unitCosphere q`.  A nonzero
covector is normalized by `sqrt (q x xi)` and degree-two homogeneity transports
the unit-cosphere minimum back to the original covector. -/
theorem hasUniformPositiveMultiple_of_compact_unitCosphere
    {X ι V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {sigma : X → (ι → ℝ) → V →L[ℝ] V}
    {q mu : X → (ι → ℝ) → ℝ}
    (hq : IsSquaredCovectorNorm q)
    (hsigma : ∀ x xi,
      sigma x xi = mu x xi • ContinuousLinearMap.id ℝ V)
    (hmu_pos : ∀ x xi, xi ≠ 0 → 0 < mu x xi)
    (hmu_hom : ∀ x r xi, mu x (r • xi) = r ^ 2 * mu x xi)
    (hcompact : IsCompact (unitCosphere q))
    (hmu_cont : ContinuousOn (fun p => mu p.1 p.2) (unitCosphere q)) :
    HasUniformPositiveMultiple sigma q := by
  obtain ⟨hq_zero, hq_nonneg, hq_pos, hq_hom⟩ := hq
  have hunit_pos : ∀ p ∈ unitCosphere q, 0 < mu p.1 p.2 := by
    intro p hp
    exact hmu_pos p.1 p.2
      (unitCosphere_covector_ne_zero
        ⟨hq_zero, hq_nonneg, hq_pos, hq_hom⟩ hp)
  obtain ⟨lam, hlam_pos, hlam⟩ :=
    hcompact.exists_forall_le' (a := (0 : ℝ)) hmu_cont hunit_pos
  refine ⟨mu, hsigma, hmu_pos, ⟨lam, hlam_pos, ?_⟩⟩
  intro x xi
  by_cases hxi : xi = 0
  · have hmu_zero : mu x (0 : ι → ℝ) = 0 := by
      simpa using hmu_hom x 0 (0 : ι → ℝ)
    simp [hxi, hq_zero x, hmu_zero]
  · have hqxi_pos : 0 < q x xi := hq_pos x xi hxi
    set rho : ℝ := Real.sqrt (q x xi)
    set eta : ι → ℝ := rho⁻¹ • xi
    have hrho_pos : 0 < rho := by
      simpa [rho] using Real.sqrt_pos.2 hqxi_pos
    have hrho_ne : rho ≠ 0 := ne_of_gt hrho_pos
    have hrho_sq : rho ^ 2 = q x xi := by
      simpa [rho] using Real.sq_sqrt (hq_nonneg x xi)
    have heta_unit : (x, eta) ∈ unitCosphere q := by
      change q x (rho⁻¹ • xi) = 1
      rw [hq_hom x rho⁻¹ xi, ← hrho_sq]
      field_simp
    have hlam_eta : lam ≤ mu x eta := hlam (x, eta) heta_unit
    have hxi_eta : xi = rho • eta := by
      change xi = rho • (rho⁻¹ • xi)
      rw [smul_smul, mul_inv_cancel₀ hrho_ne, one_smul]
    have hmu_xi : mu x xi = q x xi * mu x eta := by
      calc
        mu x xi = mu x (rho • eta) := congrArg (mu x) hxi_eta
        _ = rho ^ 2 * mu x eta := hmu_hom x rho eta
        _ = q x xi * mu x eta := by rw [hrho_sq]
    rw [hmu_xi]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_right hlam_eta (hq_nonneg x xi)

/-- The compact unit-cosphere criterion directly yields Topping's strict
parabolicity inequality. -/
theorem StrictlyParabolic.of_compact_unitCosphere
    {X ι V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {sigma : X → (ι → ℝ) → V →L[ℝ] V}
    {q mu : X → (ι → ℝ) → ℝ}
    (hq : IsSquaredCovectorNorm q)
    (hsigma : ∀ x xi,
      sigma x xi = mu x xi • ContinuousLinearMap.id ℝ V)
    (hmu_pos : ∀ x xi, xi ≠ 0 → 0 < mu x xi)
    (hmu_hom : ∀ x r xi, mu x (r • xi) = r ^ 2 * mu x xi)
    (hcompact : IsCompact (unitCosphere q))
    (hmu_cont : ContinuousOn (fun p => mu p.1 p.2) (unitCosphere q)) :
    StrictlyParabolic sigma q := by
  apply StrictlyParabolic.of_hasUniformPositiveMultiple hq
  exact hasUniformPositiveMultiple_of_compact_unitCosphere hq hsigma hmu_pos
    hmu_hom hcompact hmu_cont

/-- A continuous positive degree-two homogeneous identity symbol over a
compact base has a uniform positive multiple with respect to the Euclidean
sum-of-squares norm. -/
theorem hasUniformPositiveMultiple_euclideanNormSq_of_compactSpace
    {X V : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} {sigma : X → (Fin n → ℝ) → V →L[ℝ] V}
    {mu : X → (Fin n → ℝ) → ℝ}
    (hsigma : ∀ x xi,
      sigma x xi = mu x xi • ContinuousLinearMap.id ℝ V)
    (hmu_pos : ∀ x xi, xi ≠ 0 → 0 < mu x xi)
    (hmu_hom : ∀ x r xi, mu x (r • xi) = r ^ 2 * mu x xi)
    (hmu_cont : Continuous (fun p : X × (Fin n → ℝ) => mu p.1 p.2)) :
    HasUniformPositiveMultiple sigma
      (fun _ xi => ParabolicPDE.euclideanNormSq xi) := by
  exact hasUniformPositiveMultiple_of_compact_unitCosphere
    (euclideanNormSq_isSquaredCovectorNorm X n) hsigma hmu_pos hmu_hom
    (isCompact_unitCosphere_euclideanNormSq X n) hmu_cont.continuousOn

/-- Over a compact base, continuity and pointwise positive degree-two
homogeneity suffice for strict parabolicity of a Euclidean identity symbol. -/
theorem StrictlyParabolic.of_euclideanNormSq_compactSpace
    {X V : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} {sigma : X → (Fin n → ℝ) → V →L[ℝ] V}
    {mu : X → (Fin n → ℝ) → ℝ}
    (hsigma : ∀ x xi,
      sigma x xi = mu x xi • ContinuousLinearMap.id ℝ V)
    (hmu_pos : ∀ x xi, xi ≠ 0 → 0 < mu x xi)
    (hmu_hom : ∀ x r xi, mu x (r • xi) = r ^ 2 * mu x xi)
    (hmu_cont : Continuous (fun p : X × (Fin n → ℝ) => mu p.1 p.2)) :
    StrictlyParabolic sigma
      (fun _ xi => ParabolicPDE.euclideanNormSq xi) := by
  apply StrictlyParabolic.of_hasUniformPositiveMultiple
    (euclideanNormSq_isSquaredCovectorNorm X n)
  exact hasUniformPositiveMultiple_euclideanNormSq_of_compactSpace hsigma
    hmu_pos hmu_hom hmu_cont

#print axioms euclideanNormSq_isSquaredCovectorNorm
#print axioms isCompact_euclideanUnitCovectors
#print axioms isCompact_unitCosphere_euclideanNormSq
#print axioms hasUniformPositiveMultiple_of_compact_unitCosphere
#print axioms StrictlyParabolic.of_compact_unitCosphere
#print axioms hasUniformPositiveMultiple_euclideanNormSq_of_compactSpace
#print axioms StrictlyParabolic.of_euclideanNormSq_compactSpace

end

end Topping
