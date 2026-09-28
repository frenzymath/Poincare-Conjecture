import GilbargTrudinger.Ch05.FredholmAlternative
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Perfect

/-! # The spectrum of a compact operator from Gilbarg--Trudinger, Chapter 5 -/

namespace GilbargTrudinger

open Filter Set Topology
open Module End

section CompactSpectrum

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The set of real eigenvalues of a bounded linear endomorphism. -/
def eigenvalueSet (T : X →L[ℝ] X) : Set ℝ :=
  {μ | IsEigenvalue T μ}

private theorem finite_eigenvalues_away_from_zero (T : X →L[ℝ] X)
    (hT : IsCompactMap T) {ε : ℝ} (hε : 0 < ε) :
    {μ : ℝ | IsEigenvalue T μ ∧ ε ≤ |μ|}.Finite := by
  let S : Set ℝ := {μ : ℝ | IsEigenvalue T μ ∧ ε ≤ |μ|}
  change S.Finite
  by_contra hSfinite
  have hSinf : S.Infinite := hSfinite
  let emb : ℕ ↪ S := Set.Infinite.natEmbedding S hSinf
  let μ : ℕ → ℝ := fun n ↦ emb n
  have hμmem (n : ℕ) : IsEigenvalue T (μ n) ∧ ε ≤ |μ n| :=
    (emb n).property
  have hμinj : Function.Injective μ := by
    intro m n hmn
    apply emb.injective
    exact Subtype.ext hmn
  choose v hv_mem hv_ne using fun n ↦ (hμmem n).1.exists_hasEigenvector
  have hv_eig (n : ℕ) : HasEigenvector (T : End ℝ X) (μ n) (v n) :=
    ⟨hv_mem n, hv_ne n⟩
  have hTv (n : ℕ) : T (v n) = μ n • v n :=
    mem_eigenspace_iff.mp (hv_mem n)
  have hvlin : LinearIndependent ℝ v :=
    Module.End.eigenvectors_linearIndependent' (T : End ℝ X) μ hμinj v hv_eig
  let W (n : ℕ) : Submodule ℝ X := Submodule.span ℝ (v '' Set.Iio n)
  have hWmono : Monotone W := by
    intro m n hmn
    apply Submodule.span_mono
    exact Set.image_mono (Set.Iio_subset_Iio hmn)
  have hWclosed (n : ℕ) : IsClosed (W n : Set X) := by
    letI : FiniteDimensional ℝ (W n) :=
      FiniteDimensional.span_of_finite ℝ ((Set.finite_Iio n).image v)
    exact Submodule.closed_of_finiteDimensional _
  have hy_exists (n : ℕ) :
      ∃ y : X, y ∈ W (n + 1) ∧ ‖y‖ = 1 ∧
        ∀ z ∈ W n, (1 : ℝ) / 2 ≤ ‖y - z‖ := by
    let M : Submodule ℝ (W (n + 1)) := (W n).comap (W (n + 1)).subtype
    have hMclosed : IsClosed (M : Set (W (n + 1))) := by
      exact (hWclosed n).preimage continuous_subtype_val
    have hv_succ : v n ∈ W (n + 1) := by
      apply Submodule.subset_span
      exact ⟨n, by simp, rfl⟩
    have hv_not : v n ∉ W n := hvlin.notMem_span_image (by simp)
    have hMproper : ∃ x : W (n + 1), x ∉ M :=
      ⟨⟨v n, hv_succ⟩, hv_not⟩
    obtain ⟨yn, hynot, hynorm, hyfar⟩ :=
      riesz_lemma_of_lt_one hMclosed hMproper (show (1 : ℝ) / 2 < 1 by norm_num)
    refine ⟨yn, yn.property, hynorm, ?_⟩
    intro z hz
    let zM : M := ⟨⟨z, hWmono (Nat.le_succ n) hz⟩, hz⟩
    simpa [zM] using hyfar zM zM.property
  choose y hyW hynorm hyfar using hy_exists
  have hWT (n : ℕ) (x : X) (hx : x ∈ W n) : T x ∈ W n := by
    refine Submodule.span_induction (p := fun z _ ↦ T z ∈ W n) ?_ ?_ ?_ ?_ hx
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := hz
      rw [hTv i]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro a b ha hb hTa hTb
      rw [map_add]
      exact Submodule.add_mem _ hTa hTb
    · intro a z hz hTz
      rw [map_smul]
      exact Submodule.smul_mem _ _ hTz
  have hshift (n : ℕ) (x : X) (hx : x ∈ W (n + 1)) :
      (T - μ n • 1 : X →L[ℝ] X) x ∈ W n := by
    refine Submodule.span_induction
      (p := fun z _ ↦ (T - μ n • 1 : X →L[ℝ] X) z ∈ W n) ?_ ?_ ?_ ?_ hx
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := hz
      have hilte : i ≤ n := Nat.lt_succ_iff.mp hi
      by_cases hin : i = n
      · subst i
        simp [hTv n]
      · have hilt : i < n := lt_of_le_of_ne hilte hin
        have hvi : v i ∈ W n := Submodule.subset_span ⟨i, hilt, rfl⟩
        change T (v i) - μ n • v i ∈ W n
        rw [hTv i]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hvi) (Submodule.smul_mem _ _ hvi)
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro a b ha hb hAa hAb
      rw [map_add]
      exact Submodule.add_mem _ hAa hAb
    · intro a z hz hAz
      rw [map_smul]
      exact Submodule.smul_mem _ _ hAz
  have hμne (n : ℕ) : μ n ≠ 0 := by
    intro hn
    have := (hμmem n).2
    simp [hn] at this
    linarith
  let u (n : ℕ) : X := (μ n)⁻¹ • y n
  have hunorm (n : ℕ) : ‖u n‖ ≤ ε⁻¹ := by
    rw [show ‖u n‖ = |μ n|⁻¹ by simp [u, norm_smul, hynorm]]
    exact (inv_le_inv₀ (abs_pos.mpr (hμne n)) hε).2 (hμmem n).2
  have hubounded : Bornology.IsBounded (Set.range u) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    exact ⟨ε⁻¹, fun z ⟨n, hn⟩ ↦ by
      subst z
      simpa only [Metric.mem_closedBall, dist_zero_right] using hunorm n⟩
  have hdiff_mem (n : ℕ) : T (u n) - y n ∈ W n := by
    have hs := Submodule.smul_mem (W n) (μ n)⁻¹ (hshift n (y n) (hyW n))
    rw [show T (u n) - y n =
        (μ n)⁻¹ • ((T - μ n • 1 : X →L[ℝ] X) (y n)) by
      rw [show u n = (μ n)⁻¹ • y n by rfl, map_smul]
      change (μ n)⁻¹ • T (y n) - y n =
        (μ n)⁻¹ • (T (y n) - μ n • y n)
      rw [smul_sub, inv_smul_smul₀ (hμne n)]]
    exact hs
  have hsep : Pairwise fun m n ↦ (1 : ℝ) / 2 ≤ ‖T (u m) - T (u n)‖ := by
    have hsymm : Std.Symm fun m n ↦ (1 : ℝ) / 2 ≤ ‖T (u m) - T (u n)‖ := by
      grind [symm_def, norm_sub_rev]
    apply Pairwise.of_lt
    intro m n hmn
    have humem : u m ∈ W n := by
      apply hWmono (Nat.succ_le_iff.mpr hmn)
      exact Submodule.smul_mem _ _ (hyW m)
    have hTumem : T (u m) ∈ W n := hWT n _ humem
    let z : X := T (u m) - (T (u n) - y n)
    have hz : z ∈ W n := Submodule.sub_mem _ hTumem (hdiff_mem n)
    have hfar := hyfar n z hz
    rw [show y n - z = T (u n) - T (u m) by
      simp only [z]
      abel] at hfar
    simpa only [norm_sub_rev] using hfar
  obtain ⟨a, φ, hφ, hlim⟩ :=
    (compact_map_iff_bounded_sequence T).mp hT u hubounded
  have hcauchy := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ((1 : ℝ) / 2) (by norm_num)
  have hlt : ‖T (u (φ (N + 1))) - T (u (φ N))‖ < (1 : ℝ) / 2 := by
    simpa [dist_eq_norm_sub] using hN (N + 1)
  exact (not_le_of_gt hlt) (hsep (by simp [hφ.injective.eq_iff]))

private theorem compact_operator_eigenvalues_countable (T : X →L[ℝ] X)
    (hT : IsCompactMap T) :
    (eigenvalueSet T).Countable := by
  let A (n : ℕ) : Set ℝ :=
    {μ | IsEigenvalue T μ ∧ 1 / ((n : ℝ) + 1) ≤ |μ|}
  have hAfinite (n : ℕ) : (A n).Finite := by
    apply finite_eigenvalues_away_from_zero T hT
    positivity
  have hAcount : (⋃ n, A n).Countable :=
    Set.countable_iUnion fun n ↦ (hAfinite n).countable
  apply ((Set.countable_singleton (0 : ℝ)).union hAcount).mono
  intro μ hμ
  by_cases hμzero : μ = 0
  · simp [hμzero]
  · apply Set.mem_union_right
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hμzero)
    exact Set.mem_iUnion.mpr ⟨n, hμ, hn.le⟩

private theorem compact_operator_eigenvalue_accumulation_only_zero (T : X →L[ℝ] X)
    (hT : IsCompactMap T) {μ : ℝ}
    (hacc : AccPt μ (𝓟 (eigenvalueSet T))) :
    μ = 0 := by
  by_contra hμ
  let ε : ℝ := |μ| / 2
  have hε : 0 < ε := half_pos (abs_pos.mpr hμ)
  let A : Set ℝ := {a | IsEigenvalue T a ∧ ε ≤ |a|}
  have hAfinite : A.Finite := finite_eigenvalues_away_from_zero T hT hε
  let U : Set ℝ := {a | ε < |a|}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_abs
  have hμU : μ ∈ U := by
    dsimp [U, ε]
    linarith [abs_pos.mpr hμ]
  have haccU : AccPt μ (𝓟 (U ∩ eigenvalueSet T)) :=
    hacc.nhds_inter (hUopen.mem_nhds hμU)
  have hsubset : U ∩ eigenvalueSet T ⊆ A := by
    intro a ha
    exact ⟨ha.2, ha.1.le⟩
  exact hAfinite.not_infinite ((Set.Infinite.of_accPt haccU).mono hsubset)

private theorem compact_operator_finite_dimensional_eigenspace (T : X →L[ℝ] X)
    (hT : IsCompactMap T) (μ : ℝ) (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (eigenspace T.toLinearMap μ) := by
  have hTop : IsCompactOperator (T : X →ₗ[ℝ] X) := by
    apply (compact_map_linear_iff_isCompactOperator T.toLinearMap).mp
    simpa using hT
  have hclosed : IsClosed (eigenspace T.toLinearMap μ : Set X) := by
    have heq : eigenspace T.toLinearMap μ =
        ((T - μ • 1 : X →L[ℝ] X).toLinearMap).ker := by
      ext x
      simp [sub_eq_zero]
    rw [heq]
    exact (T - μ • 1).isClosed_ker
  replace hTop := hTop.restrict
    ((mem_invtSubmodule_iff_forall_mem_of_mem _).mp
      (eigenspace_mem_invtSubmodule T.toLinearMap μ)) hclosed
  rw [restrict_eigenspace, LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at hTop
  rwa [← isCompactOperator_id_iff_finiteDimensional]

/-- The eigenvalues of a compact operator are countable, can accumulate only at zero, and have
finite-dimensional eigenspaces away from zero. -/
theorem spectrum_of_compact_operator (T : X →L[ℝ] X) (hT : IsCompactMap T) :
    (eigenvalueSet T).Countable ∧
      (∀ μ, AccPt μ (𝓟 (eigenvalueSet T)) → μ = 0) ∧
      (∀ μ, IsEigenvalue T μ → μ ≠ 0 →
        FiniteDimensional ℝ (eigenspace T.toLinearMap μ)) := by
  exact ⟨compact_operator_eigenvalues_countable T hT,
    ⟨fun _ hacc ↦ compact_operator_eigenvalue_accumulation_only_zero T hT hacc,
      fun μ _ hμ ↦ compact_operator_finite_dimensional_eigenspace T hT μ hμ⟩⟩

end CompactSpectrum

end GilbargTrudinger
