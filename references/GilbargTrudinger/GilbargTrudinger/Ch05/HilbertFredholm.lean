import GilbargTrudinger.Ch05.CompactSpectrum
import GilbargTrudinger.Ch05.HilbertSpaces
import Mathlib.Analysis.Normed.Module.Normalize

/-! # The Hilbert-space Fredholm alternative from Gilbarg--Trudinger, Chapter 5 -/

namespace GilbargTrudinger

open Filter Set Topology
open Module End

section HilbertFredholm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A nonzero scalar shift of a compact operator has closed range. -/
private theorem compact_shift_isClosed_range (T : H →L[ℝ] H) (hT : IsCompactMap T)
    {μ : ℝ} (hμ : μ ≠ 0) :
    IsClosed (((μ • (1 : H →L[ℝ] H) - T : H →L[ℝ] H) : Module.End ℝ H).range : Set H) := by
  let A : H →L[ℝ] H := μ • 1 - T
  let N : Submodule ℝ H := (A : Module.End ℝ H).ker
  let R : Nᗮ →L[ℝ] H := A.comp Nᗮ.subtypeL
  have hNclosed : IsClosed (N : Set H) := by
    simpa only [N] using A.isClosed_ker
  letI : CompleteSpace N := hNclosed.completeSpace_coe
  letI : N.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace N
  letI : CompleteSpace Nᗮ := N.isClosed_orthogonal.completeSpace_coe
  have hRanti : ∃ K, AntilipschitzWith K R := by
    rw [antilipschitzWith_iff_exists_mul_le_norm]
    by_contra hlower
    push Not at hlower
    have hv_exists (n : ℕ) :
        ∃ v : Nᗮ, ‖v‖ = 1 ∧ ‖R v‖ < (1 : ℝ) / (n + 1) := by
      have hc : 0 < (1 : ℝ) / (n + 1) := by positivity
      obtain ⟨x, hx⟩ := hlower ((1 : ℝ) / (n + 1)) hc
      have hxne : x ≠ 0 := by
        intro hxzero
        subst x
        simp at hx
      refine ⟨NormedSpace.normalize x, NormedSpace.norm_normalize hxne, ?_⟩
      calc
        ‖R (NormedSpace.normalize x)‖ = ‖x‖⁻¹ * ‖R x‖ := by
          simp [NormedSpace.normalize, norm_smul]
        _ < ‖x‖⁻¹ * (((1 : ℝ) / (n + 1)) * ‖x‖) := by
          gcongr
        _ = (1 : ℝ) / (n + 1) := by
          field_simp
    choose v hvnorm hvsmall using hv_exists
    have hvbounded : Bornology.IsBounded (Set.range fun n ↦ (v n : H)) := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, ?_⟩
      rintro z ⟨n, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖v n‖ ≤ 1
      rw [hvnorm]
    obtain ⟨y, φ, hφ, hTlim⟩ :=
      (compact_map_iff_bounded_sequence T).mp hT (fun n ↦ (v n : H)) hvbounded
    have hRlim : Tendsto (fun n ↦ R (v n)) atTop (nhds 0) := by
      apply squeeze_zero_norm (fun n ↦ (hvsmall n).le)
      exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hvlim : Tendsto (fun n ↦ (v (φ n) : H)) atTop (nhds (μ⁻¹ • y)) := by
      have hsum := (hRlim.comp hφ.tendsto_atTop).add hTlim
      have hscaled := hsum.const_smul μ⁻¹
      have hpoint (n : ℕ) :
          μ⁻¹ • (R (v (φ n)) + T (v (φ n))) = (v (φ n) : H) := by
        change μ⁻¹ • ((μ • (v (φ n) : H) - T (v (φ n))) + T (v (φ n))) =
          (v (φ n) : H)
        rw [sub_add_cancel, inv_smul_smul₀ hμ]
      simpa only [Function.comp_apply, zero_add] using
        hscaled.congr' (Eventually.of_forall hpoint)
    have hzperp : μ⁻¹ • y ∈ Nᗮ := by
      apply N.isClosed_orthogonal.mem_of_tendsto hvlim
      exact Eventually.of_forall fun n ↦ (v (φ n)).property
    have hAzero : A (μ⁻¹ • y) = 0 := by
      apply tendsto_nhds_unique (A.continuous.continuousAt.tendsto.comp hvlim)
      exact (hRlim.comp hφ.tendsto_atTop).congr'
        (Eventually.of_forall fun n ↦ by rfl)
    have hzker : μ⁻¹ • y ∈ N := by
      change A (μ⁻¹ • y) = 0
      exact hAzero
    have hz : μ⁻¹ • y = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      exact (N.mem_orthogonal _).mp hzperp _ hzker
    have hznorm : ‖μ⁻¹ • y‖ = 1 := by
      apply tendsto_nhds_unique hvlim.norm
      have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
      convert hone using 1
      funext n
      change ‖v (φ n)‖ = 1
      exact hvnorm _
    simp [hz] at hznorm
  obtain ⟨K, hK⟩ := hRanti
  have hRclosed : IsClosed (Set.range R) := hK.isClosed_range R.uniformContinuous
  have hrange : (R : Nᗮ →ₗ[ℝ] H).range = (A : Module.End ℝ H).range := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨n, hn, z, hz, hx⟩ := Submodule.exists_add_mem_mem_orthogonal (K := N) x
      refine ⟨⟨z, hz⟩, ?_⟩
      rw [hx, map_add]
      have hAn : A n = 0 := by
        change A n = 0 at hn
        exact hn
      change A z = A n + A z
      rw [hAn, zero_add]
  change IsClosed ((A : Module.End ℝ H).range : Set H)
  rw [← hrange]
  change IsClosed (Set.range fun x : Nᗮ ↦ R x)
  exact hRclosed

/-- A scalar is regular for an operator when every shifted equation has a unique solution and the
shift admits a bounded two-sided inverse. -/
def IsRegularValue (T : H →L[ℝ] H) (μ : ℝ) : Prop :=
  (∀ y : H, ∃! x : H, μ • x - T x = y) ∧
    ∃ R : H →L[ℝ] H,
      (∀ x : H, R (μ • x - T x) = x) ∧
      (∀ y : H, μ • R y - T (R y) = y)

omit [CompleteSpace H] in
private theorem isRegularValue_of_not_isEigenvalue (T : H →L[ℝ] H)
    (hT : IsCompactMap T) {μ : ℝ} (hμ : μ ≠ 0) (hneig : ¬IsEigenvalue T μ) :
    IsRegularValue T μ := by
  obtain ⟨R, hleft, hright⟩ :=
    compact_operator_bounded_inverse_of_not_eigenvalue T hT hμ hneig
  refine ⟨?_, ⟨R, hleft, hright⟩⟩
  intro y
  refine ⟨R y, hright y, ?_⟩
  intro x hx
  calc
    x = R (μ • x - T x) := (hleft x).symm
    _ = R y := congrArg R hx

private theorem not_isEigenvalue_adjoint_of_not_isEigenvalue (T : H →L[ℝ] H)
    (hT : IsCompactMap T) {μ : ℝ} (hμ : μ ≠ 0) (hneig : ¬IsEigenvalue T μ) :
    ¬IsEigenvalue (ContinuousLinearMap.adjoint T) μ := by
  have hregular := isRegularValue_of_not_isEigenvalue T hT hμ hneig
  have hsurj : Function.Surjective (μ • (1 : H →L[ℝ] H) - T : H →L[ℝ] H) := by
    intro y
    obtain ⟨x, hx, -⟩ := hregular.1 y
    refine ⟨x, ?_⟩
    simpa using hx
  intro hadj
  obtain ⟨z, hzmem, hzne⟩ := hadj.exists_hasEigenvector
  have hz : ContinuousLinearMap.adjoint T z = μ • z := mem_eigenspace_iff.mp hzmem
  apply hzne
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  obtain ⟨x, hx⟩ := hsurj z
  calc
    inner ℝ z z = inner ℝ z ((μ • (1 : H →L[ℝ] H) - T) x) :=
      congrArg (fun w ↦ inner ℝ z w) hx.symm
    _ = inner ℝ z (μ • x - T x) := rfl
    _ = 0 := by
      rw [inner_sub_right, ← ContinuousLinearMap.adjoint_inner_left T x z, hz,
        real_inner_smul_right, real_inner_smul_left, sub_self]

/-- A compact operator and its adjoint have the same nonzero real eigenvalues. -/
private theorem isEigenvalue_adjoint_iff (T : H →L[ℝ] H) (hT : IsCompactMap T)
    {μ : ℝ} (hμ : μ ≠ 0) :
    IsEigenvalue (ContinuousLinearMap.adjoint T) μ ↔ IsEigenvalue T μ := by
  constructor
  · intro hadj
    by_contra hTneig
    exact not_isEigenvalue_adjoint_of_not_isEigenvalue T hT hμ hTneig hadj
  · intro hTeig
    by_contra hadjneig
    have hnot := not_isEigenvalue_adjoint_of_not_isEigenvalue
      (ContinuousLinearMap.adjoint T) (compact_adjoint T hT) hμ hadjneig
    apply hnot
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hTeig

private theorem compact_shift_solvable_iff_orthogonal_adjoint_kernel
    (T : H →L[ℝ] H) (hT : IsCompactMap T) {μ : ℝ} (hμ : μ ≠ 0) (y : H) :
    (∃ x : H, μ • x - T x = y) ↔
      y ∈ (((μ • (1 : H →L[ℝ] H) - ContinuousLinearMap.adjoint T : H →L[ℝ] H) :
        Module.End ℝ H).ker)ᗮ := by
  let A : H →L[ℝ] H := μ • 1 - T
  have hclosed : IsClosed ((A : Module.End ℝ H).range : Set H) := by
    simpa only [A] using compact_shift_isClosed_range T hT hμ
  have hclosure : (A : Module.End ℝ H).range.topologicalClosure =
      (A : Module.End ℝ H).range := hclosed.submodule_topologicalClosure_eq
  have hrange : (A : Module.End ℝ H).range =
      (((μ • (1 : H →L[ℝ] H) - ContinuousLinearMap.adjoint T : H →L[ℝ] H) :
        Module.End ℝ H).ker)ᗮ := by
    calc
      (A : Module.End ℝ H).range = (A : Module.End ℝ H).range.topologicalClosure :=
        hclosure.symm
      _ = ((ContinuousLinearMap.adjoint A : H →L[ℝ] H) : Module.End ℝ H).kerᗮ :=
        closure_range_eq_orthogonal_ker_adjoint A
      _ = (((μ • (1 : H →L[ℝ] H) - ContinuousLinearMap.adjoint T : H →L[ℝ] H) :
        Module.End ℝ H).ker)ᗮ := by simp [A]
  constructor
  · rintro ⟨x, hx⟩
    rw [← hrange]
    refine ⟨x, ?_⟩
    change μ • x - T x = y
    exact hx
  · intro hy
    rw [← hrange] at hy
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    change μ • x - T x = y at hx
    exact hx

omit [CompleteSpace H] in
private theorem compact_shift_ker_eq_eigenspace (T : H →L[ℝ] H) (μ : ℝ) :
    ((μ • (1 : H →L[ℝ] H) - T : H →L[ℝ] H) : Module.End ℝ H).ker =
      eigenspace T.toLinearMap μ := by
  ext x
  rw [LinearMap.mem_ker, mem_eigenspace_iff]
  change (μ • x - T x = 0) ↔ T x = μ • x
  rw [sub_eq_zero, eq_comm]

/-- The nonzero real eigenvalues of a bounded linear endomorphism. -/
def nonzeroEigenvalueSet (T : H →L[ℝ] H) : Set ℝ :=
  {μ | μ ≠ 0 ∧ IsEigenvalue T μ}

/-- The Hilbert-space Fredholm alternative for a compact operator. -/
theorem hilbert_space_fredholm_alternative (T : H →L[ℝ] H) (hT : IsCompactMap T) :
    ∃ Λ : Set ℝ,
      Λ.Countable ∧
      (∀ μ : ℝ, AccPt μ (𝓟 Λ) → μ = 0) ∧
      (∀ μ : ℝ, μ ≠ 0 → μ ∉ Λ →
        IsRegularValue T μ ∧ IsRegularValue (ContinuousLinearMap.adjoint T) μ) ∧
      (∀ μ : ℝ, μ ∈ Λ →
        FiniteDimensional ℝ
          (((μ • (1 : H →L[ℝ] H) - T : H →L[ℝ] H) : Module.End ℝ H).ker) ∧
        FiniteDimensional ℝ
          (((μ • (1 : H →L[ℝ] H) - ContinuousLinearMap.adjoint T : H →L[ℝ] H) :
            Module.End ℝ H).ker) ∧
        (∀ y : H, (∃ x : H, μ • x - T x = y) ↔
          y ∈ (((μ • (1 : H →L[ℝ] H) - ContinuousLinearMap.adjoint T : H →L[ℝ] H) :
            Module.End ℝ H).ker)ᗮ) ∧
        (∀ y : H, (∃ x : H, μ • x - ContinuousLinearMap.adjoint T x = y) ↔
          y ∈ (((μ • (1 : H →L[ℝ] H) - T : H →L[ℝ] H) : Module.End ℝ H).ker)ᗮ)) := by
  let Λ : Set ℝ := nonzeroEigenvalueSet T
  obtain ⟨hcount, hacc, hfinite⟩ := spectrum_of_compact_operator T hT
  have hsubset : Λ ⊆ eigenvalueSet T := by
    intro μ hμ
    change μ ≠ 0 ∧ IsEigenvalue T μ at hμ
    exact hμ.2
  have hΛcount : Λ.Countable := hcount.mono hsubset
  have hΛacc : ∀ μ : ℝ, AccPt μ (𝓟 Λ) → μ = 0 := by
    intro μ hμ
    exact hacc μ (hμ.mono (Filter.principal_mono.mpr hsubset))
  have hregular : ∀ μ : ℝ, μ ≠ 0 → μ ∉ Λ →
      IsRegularValue T μ ∧ IsRegularValue (ContinuousLinearMap.adjoint T) μ := by
    intro μ hμ hμΛ
    have hneig : ¬IsEigenvalue T μ := by
      intro heig
      apply hμΛ
      exact ⟨hμ, heig⟩
    have hadjneig : ¬IsEigenvalue (ContinuousLinearMap.adjoint T) μ :=
      not_isEigenvalue_adjoint_of_not_isEigenvalue T hT hμ hneig
    exact ⟨isRegularValue_of_not_isEigenvalue T hT hμ hneig,
      isRegularValue_of_not_isEigenvalue (ContinuousLinearMap.adjoint T)
        (compact_adjoint T hT) hμ hadjneig⟩
  have hsingular : ∀ μ : ℝ, μ ∈ Λ →
      FiniteDimensional ℝ
        (((μ • (1 : H →L[ℝ] H) - T : H →L[ℝ] H) : Module.End ℝ H).ker) ∧
      FiniteDimensional ℝ
        (((μ • (1 : H →L[ℝ] H) - ContinuousLinearMap.adjoint T : H →L[ℝ] H) :
          Module.End ℝ H).ker) ∧
      (∀ y : H, (∃ x : H, μ • x - T x = y) ↔
        y ∈ (((μ • (1 : H →L[ℝ] H) - ContinuousLinearMap.adjoint T : H →L[ℝ] H) :
          Module.End ℝ H).ker)ᗮ) ∧
      (∀ y : H, (∃ x : H, μ • x - ContinuousLinearMap.adjoint T x = y) ↔
        y ∈ (((μ • (1 : H →L[ℝ] H) - T : H →L[ℝ] H) : Module.End ℝ H).ker)ᗮ) := by
    intro μ hμΛ
    change μ ≠ 0 ∧ IsEigenvalue T μ at hμΛ
    obtain ⟨hμ, hμeig⟩ := hμΛ
    have hadjCompact : IsCompactMap (ContinuousLinearMap.adjoint T) := compact_adjoint T hT
    have hadjeig : IsEigenvalue (ContinuousLinearMap.adjoint T) μ :=
      (isEigenvalue_adjoint_iff T hT hμ).mpr hμeig
    obtain ⟨-, -, hadjfinite⟩ :=
      spectrum_of_compact_operator (ContinuousLinearMap.adjoint T) hadjCompact
    have hfinT : FiniteDimensional ℝ
        (((μ • (1 : H →L[ℝ] H) - T : H →L[ℝ] H) : Module.End ℝ H).ker) := by
      rw [compact_shift_ker_eq_eigenspace]
      exact hfinite μ hμeig hμ
    have hfinAdj : FiniteDimensional ℝ
        (((μ • (1 : H →L[ℝ] H) - ContinuousLinearMap.adjoint T : H →L[ℝ] H) :
          Module.End ℝ H).ker) := by
      rw [compact_shift_ker_eq_eigenspace]
      exact hadjfinite μ hadjeig hμ
    refine ⟨hfinT, hfinAdj, compact_shift_solvable_iff_orthogonal_adjoint_kernel T hT hμ, ?_⟩
    intro y
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      compact_shift_solvable_iff_orthogonal_adjoint_kernel
        (ContinuousLinearMap.adjoint T) hadjCompact hμ y
  exact ⟨Λ, hΛcount, hΛacc, hregular, hsingular⟩

end HilbertFredholm

end GilbargTrudinger
