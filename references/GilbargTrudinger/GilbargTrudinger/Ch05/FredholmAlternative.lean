import GilbargTrudinger.Ch05.BanachSpaces

/-! # The Fredholm alternative from Gilbarg--Trudinger, Chapter 5 -/

namespace GilbargTrudinger

open Filter Set Topology
open Module End

section FredholmAlternative

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem compact_sub_smul_id_closedEmbedding (T : X →L[ℝ] X) (hT : IsCompactMap T)
    {μ : ℝ} (hμ : μ ≠ 0) {K : NNReal}
    (hanti : AntilipschitzWith K (T - μ • 1 : X →L[ℝ] X)) :
    Topology.IsClosedEmbedding (T - μ • 1 : X →L[ℝ] X) := by
  let S : X →L[ℝ] X := T - μ • 1
  have hSembed : Topology.IsEmbedding S := hanti.isEmbedding S.continuous
  refine ⟨hSembed, ?_⟩
  rw [← closure_eq_iff_isClosed]
  apply Set.Subset.antisymm _ subset_closure
  intro y hy
  obtain ⟨z, hzrange, hzlim⟩ := mem_closure_iff_seq_limit.mp hy
  choose x hx using hzrange
  have hzbounded : Bornology.IsBounded (Set.range z) := hzlim.cauchySeq.isBounded_range
  have hxbounded : Bornology.IsBounded (Set.range x) := by
    rw [Metric.isBounded_range_iff] at hzbounded ⊢
    obtain ⟨D, hD⟩ := hzbounded
    refine ⟨(K : ℝ) * D, fun m n ↦ ?_⟩
    have hdist := (antilipschitzWith_iff_le_mul_dist.mp hanti) (x m) (x n)
    rw [show S (x m) = z m from hx m, show S (x n) = z n from hx n] at hdist
    exact hdist.trans (mul_le_mul_of_nonneg_left (hD m n) K.coe_nonneg)
  obtain ⟨q, φ, hφ, hTlim⟩ :=
    (compact_map_iff_bounded_sequence T).mp hT x hxbounded
  have hzsub : Tendsto (fun n ↦ z (φ n)) atTop (nhds y) :=
    hzlim.comp hφ.tendsto_atTop
  have hxdiff : Tendsto (fun n ↦ μ⁻¹ • (T (x (φ n)) - z (φ n))) atTop
      (nhds (μ⁻¹ • (q - y))) :=
    (hTlim.sub hzsub).const_smul μ⁻¹
  have hxeq (n : ℕ) : μ⁻¹ • (T (x (φ n)) - z (φ n)) = x (φ n) := by
    rw [← hx (φ n)]
    simp only [sub_apply, smul_apply]
    rw [show (1 : X →L[ℝ] X) (x (φ n)) = x (φ n) by rfl]
    rw [show T (x (φ n)) - (T (x (φ n)) - μ • x (φ n)) = μ • x (φ n) by
      abel]
    exact inv_smul_smul₀ hμ _
  have hxlim : Tendsto (fun n ↦ x (φ n)) atTop (nhds (μ⁻¹ • (q - y))) :=
    hxdiff.congr' (Eventually.of_forall hxeq)
  have hSlim : Tendsto (fun n ↦ S (x (φ n))) atTop
      (nhds (S (μ⁻¹ • (q - y)))) :=
    S.continuous.continuousAt.tendsto.comp hxlim
  have hSy : S (μ⁻¹ • (q - y)) = y := by
    apply tendsto_nhds_unique hSlim
    exact hzsub.congr' (Eventually.of_forall fun n ↦ (hx (φ n)).symm)
  exact ⟨μ⁻¹ • (q - y), hSy⟩

private theorem exists_separated_iterateRange {S : End ℝ X}
    (hS_not_surj : ¬(S : X → X).Surjective)
    (hS_closed : Topology.IsClosedEmbedding S)
    {c : ℝ} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) :
    ∃ f : ℕ → X,
      (∀ n, 1 ≤ ‖f n‖) ∧ (∀ n, ‖f n‖ ≤ R) ∧ (∀ n, f n ∈ (S ^ n).range) ∧
      (∀ n, ∀ y ∈ (S ^ (n + 1)).range, 1 ≤ ‖f n - y‖) := by
  let W (n : ℕ) : Submodule ℝ X := S.iterateRange n
  have hW_succ (n : ℕ) : W (n + 1) = (W n).map (S : End ℝ X) :=
    LinearMap.iterateRange_succ
  have hW_closed (n : ℕ) : IsClosed (W n : Set X) := by
    induction n with
    | zero => simp [W, Module.End.one_eq_id]
    | succ n ih =>
      rw [hW_succ]
      apply hS_closed.isClosedMap _ ih
  have hx (n : ℕ) :
      ∃ x ∈ W n, 1 ≤ ‖x‖ ∧ ‖x‖ ≤ R ∧ ∀ y ∈ W (n + 1), 1 ≤ ‖x - y‖ := by
    have h₁ : IsClosed ((W (n + 1)).comap (W n).subtype : Set (W n)) := by
      simpa using! (hW_closed (n + 1)).preimage_val
    have h₂ : ∃ x : W n, x ∉ (W (n + 1)).comap (W n).subtype := by
      simpa [iterate_succ, W, (iterate_injective hS_closed.injective n).eq_iff,
        Function.Surjective] using! hS_not_surj
    obtain ⟨⟨x, hx⟩, hxn, hxy⟩ := riesz_lemma_of_norm_lt hc hR h₁ h₂
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Subtype.forall] at hxn hxy
    exact ⟨x, hx, by simpa using! hxy 0, hxn,
      fun y hy ↦ hxy y (S.iterateRange.monotone (by simp) hy) hy⟩
  choose x hxW hxn hxn' hxy using hx
  exact ⟨x, hxn, hxn', hxW, hxy⟩

/-- If a nonzero scalar is not an eigenvalue of a compact operator, subtracting that scalar
multiple of the identity gives a surjective map. This version does not require completeness of
the ambient normed space. -/
theorem compact_operator_surjective_sub_smul_id_of_not_hasEigenvalue
    (T : X →L[ℝ] X) (hT : IsCompactMap T) {μ : ℝ} (hμ : μ ≠ 0)
    (hneig : ¬HasEigenvalue (T : End ℝ X) μ) :
    Function.Surjective (T - μ • 1 : X →L[ℝ] X) := by
  have hTop : IsCompactOperator (T : X →ₗ[ℝ] X) := by
    apply (compact_map_linear_iff_isCompactOperator T.toLinearMap).mp
    simpa using hT
  let S := T - μ • 1
  obtain ⟨K, hK : AntilipschitzWith K S⟩ :=
    IsCompactOperator.antilipschitz_of_not_hasEigenvalue hTop hμ hneig
  have hSclosed : Topology.IsClosedEmbedding S :=
    compact_sub_smul_id_closedEmbedding T hT hμ hK
  by_contra hnot
  change ¬Function.Surjective S at hnot
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm ℝ
  obtain ⟨f, hf_norm_lower, hf_norm_upper, hf_mem, hf_far⟩ :=
    exists_separated_iterateRange hnot hSclosed hc (R := ‖c‖ + 1) (by simp)
  replace hf_mem {n m : ℕ} (h : m ≤ n) : f n ∈ ((S : End ℝ X) ^ m).range :=
    (S : End ℝ X).iterateRange.monotone (by lia) (hf_mem _)
  have hf_mem' {n m : ℕ} (h : m ≤ n) :
      S (f n) ∈ ((S : End ℝ X) ^ (m + 1)).range := by
    rw [iterate_succ', LinearMap.range_comp]
    exact ⟨f n, hf_mem h, rfl⟩
  have hp : Pairwise fun x₁ x₂ ↦ ‖μ‖ ≤ ‖T (f x₁) - T (f x₂)‖ := by
    have hsymm : Std.Symm fun x₁ x₂ ↦ ‖μ‖ ≤ ‖T (f x₁) - T (f x₂)‖ := by
      grind [symm_def, norm_sub_rev]
    apply Pairwise.of_lt
    intro m n hmn
    let u : X := μ⁻¹ • (S (f n) - S (f m) + μ • f n)
    have hu : μ • (f m - u) = T (f m) - T (f n) := by
      rw [smul_sub, smul_inv_smul₀ hμ]
      simp [S]
      linear_combination (norm := module)
    have hu_mem : u ∈ ((S : End ℝ X) ^ (m + 1)).range := by
      apply Submodule.smul_mem _ _ (Submodule.add_mem _ _ _)
      · exact Submodule.sub_mem _ (hf_mem' hmn.le) (hf_mem' le_rfl)
      · exact Submodule.smul_mem _ μ (hf_mem hmn)
    grw [← hu, norm_smul, mul_comm, ← hf_far _ u hu_mem, one_mul]
  obtain ⟨Kc, hKc, hKc'⟩ := hTop.image_closedBall_subset_compact (‖c‖ + 1)
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ :=
    hKc.tendsto_subseq (fun n ↦ hKc' ⟨f n, by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hf_norm_upper n,
      rfl⟩)
  replace hψy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hψy
  obtain ⟨N, hN⟩ := hψy ‖μ‖ (by positivity)
  have hlt : ‖T (f (ψ (N + 1))) - T (f (ψ N))‖ < ‖μ‖ := by
    simpa [dist_eq_norm_sub] using hN (N + 1)
  exact hlt.not_ge (hp (by simp [hψ.injective.eq_iff]))

/-- A scalar is an eigenvalue when its eigenspace contains a nonzero vector. -/
abbrev IsEigenvalue (T : X →L[ℝ] X) (μ : ℝ) : Prop :=
  HasEigenvalue (T : End ℝ X) μ

/-- The dimension of the kernel of `μ I - T`. -/
noncomputable def eigenvalueMultiplicity (T : X →L[ℝ] X) (μ : ℝ) : Cardinal :=
  Module.rank ℝ (LinearMap.ker (μ • (1 : X →L[ℝ] X) - T).toLinearMap)

/-- A nonzero scalar which is not an eigenvalue of a compact operator has a bounded two-sided
inverse for `μ I - T`. -/
theorem compact_operator_bounded_inverse_of_not_eigenvalue
    (T : X →L[ℝ] X) (hT : IsCompactMap T) {μ : ℝ} (hμ : μ ≠ 0)
    (hneig : ¬IsEigenvalue T μ) :
    ∃ R : X →L[ℝ] X,
      (∀ x : X, R (μ • x - T x) = x) ∧
      (∀ y : X, μ • R y - T (R y) = y) := by
  have hTop : IsCompactOperator (T : X →ₗ[ℝ] X) := by
    apply (compact_map_linear_iff_isCompactOperator T.toLinearMap).mp
    simpa using hT
  have hsurj :=
    compact_operator_surjective_sub_smul_id_of_not_hasEigenvalue T hT hμ hneig
  obtain ⟨K, hK⟩ :=
    IsCompactOperator.antilipschitz_of_not_hasEigenvalue hTop hμ hneig
  let A : X →L[ℝ] X := μ • 1 - T
  have hS_eq : T - μ • 1 = -A := by
    simp only [A]
    module
  have hAinj : Function.Injective A := by
    intro x z hxz
    apply hK.injective
    rw [hS_eq]
    simp only [neg_apply, hxz]
  have hAsurj : Function.Surjective A := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (-y)
    refine ⟨x, ?_⟩
    rw [hS_eq, neg_apply] at hx
    exact neg_injective hx
  let e : X ≃ₗ[ℝ] X := LinearEquiv.ofBijective A.toLinearMap ⟨hAinj, hAsurj⟩
  have he_apply (x : X) : e x = A x := rfl
  have he_bound (y : X) : ‖e.symm y‖ ≤ (K : ℝ) * ‖y‖ := by
    have hb := (antilipschitzWith_iff_le_mul_dist.mp hK) (e.symm y) 0
    rw [dist_zero_right, map_zero, dist_zero_right, hS_eq, neg_apply, norm_neg,
      ← he_apply, e.apply_symm_apply] at hb
    exact hb
  let R : X →L[ℝ] X := LinearMap.mkContinuous e.symm.toLinearMap (K : ℝ) he_bound
  have hA_apply (x : X) : A x = μ • x - T x := by simp [A]
  refine ⟨R, ?_, ?_⟩
  · intro x
    rw [← hA_apply]
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  · intro y
    rw [← hA_apply]
    change e (e.symm y) = y
    exact e.apply_symm_apply y

/-- The Fredholm alternative for a compact linear endomorphism of a normed space. -/
theorem fredholm_alternative (T : X →L[ℝ] X) (hT : IsCompactMap T) :
    Xor
      (∃ x : X, x ≠ 0 ∧ x - T x = 0)
      ((∀ y : X, ∃! x : X, x - T x = y) ∧
        ∃ R : X →L[ℝ] X,
          (∀ x : X, R (x - T x) = x) ∧
          (∀ y : X, R y - T (R y) = y)) := by
  have hTop : IsCompactOperator (T : X →ₗ[ℝ] X) := by
    apply (compact_map_linear_iff_isCompactOperator T.toLinearMap).mp
    simpa using hT
  by_cases heig : HasEigenvalue (T : End ℝ X) 1
  · have hsing : ∃ x : X, x ≠ 0 ∧ x - T x = 0 := by
      obtain ⟨x, hxmem, hxne⟩ := heig.exists_hasEigenvector
      rw [mem_eigenspace_iff] at hxmem
      exact ⟨x, hxne, sub_eq_zero.mpr (by simpa using hxmem.symm)⟩
    refine Or.inl ⟨hsing, ?_⟩
    rintro ⟨hunique, -⟩
    obtain ⟨x, hxne, hx⟩ := hsing
    obtain ⟨z, hz, huniq⟩ := hunique 0
    have hzero : (0 : X) - T 0 = 0 := by simp
    exact hxne ((huniq x hx).trans (huniq 0 hzero).symm)
  · have hsurj :=
      compact_operator_surjective_sub_smul_id_of_not_hasEigenvalue T hT one_ne_zero heig
    obtain ⟨K, hK⟩ :=
      IsCompactOperator.antilipschitz_of_not_hasEigenvalue hTop one_ne_zero heig
    let A : X →L[ℝ] X := 1 - T
    have hS_eq : T - (1 : ℝ) • 1 = -A := by
      simp only [A]
      module
    have hAinj : Function.Injective A := by
      intro x z hxz
      apply hK.injective
      rw [hS_eq]
      simp only [neg_apply, hxz]
    have hAsurj : Function.Surjective A := by
      intro y
      obtain ⟨x, hx⟩ := hsurj (-y)
      refine ⟨x, ?_⟩
      rw [hS_eq, neg_apply] at hx
      exact neg_injective hx
    let e : X ≃ₗ[ℝ] X := LinearEquiv.ofBijective A.toLinearMap ⟨hAinj, hAsurj⟩
    have he_apply (x : X) : e x = A x := rfl
    have he_bound (y : X) : ‖e.symm y‖ ≤ (K : ℝ) * ‖y‖ := by
      have hb := (antilipschitzWith_iff_le_mul_dist.mp hK) (e.symm y) 0
      rw [dist_zero_right, map_zero, dist_zero_right, hS_eq, neg_apply, norm_neg,
        ← he_apply, e.apply_symm_apply] at hb
      exact hb
    let R : X →L[ℝ] X := LinearMap.mkContinuous e.symm.toLinearMap (K : ℝ) he_bound
    have hA_apply (x : X) : A x = x - T x := by simp [A]
    have hregular :
        (∀ y : X, ∃! x : X, x - T x = y) ∧
          ∃ R : X →L[ℝ] X,
            (∀ x : X, R (x - T x) = x) ∧
            (∀ y : X, R y - T (R y) = y) := by
      constructor
      · intro y
        obtain ⟨x, hx⟩ := hAsurj y
        refine ⟨x, by simpa only [← hA_apply] using hx, ?_⟩
        intro z hz
        apply hAinj
        rw [hA_apply, hA_apply, hz]
        exact hx.symm
      · refine ⟨R, ?_, ?_⟩
        · intro x
          change e.symm (e x) = x
          exact e.symm_apply_apply x
        · intro y
          rw [← hA_apply]
          change e (e.symm y) = y
          exact e.apply_symm_apply y
    refine Or.inr ⟨hregular, ?_⟩
    rintro ⟨x, hxne, hx⟩
    apply heig
    apply hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hxne⟩
    rw [mem_eigenspace_iff]
    simpa using (sub_eq_zero.mp hx).symm

end FredholmAlternative

end GilbargTrudinger
