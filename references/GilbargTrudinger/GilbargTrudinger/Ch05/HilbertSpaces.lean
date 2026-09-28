import GilbargTrudinger.Ch05.BanachSpaces
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.WeakDual

/-! # Hilbert-space results from Gilbarg--Trudinger, Chapter 5 -/

namespace GilbargTrudinger

abbrev RealInnerProductSpace (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  InnerProductSpace ℝ H

section InnerProductBasics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Cauchy--Schwarz, the triangle inequality, and the parallelogram identity. -/
theorem inner_product_identities (x y : H) :
    |inner ℝ x y| ≤ ‖x‖ * ‖y‖ ∧
      ‖x + y‖ ≤ ‖x‖ + ‖y‖ ∧
        ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  refine ⟨abs_real_inner_le_norm x y, norm_add_le x y, ?_⟩
  simpa [real_inner_self_eq_norm_sq] using
    (parallelogram_law (𝕜 := ℝ) (x := x) (y := y))

/-- A Hilbert space is a complete real inner-product space. -/
def IsHilbertSpace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] : Prop :=
  CompleteSpace H

/-- Orthogonality of two vectors in a real inner-product space. -/
def AreOrthogonal (x y : H) : Prop :=
  inner ℝ x y = 0

/-- The orthogonal complement of an arbitrary set. -/
def orthogonalComplement (M : Set H) : Set H :=
  {x | ∀ y ∈ M, inner ℝ x y = 0}

end InnerProductBasics

section Projection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The unique decomposition into a closed subspace and its orthogonal complement. -/
theorem projection_theorem (M : Submodule ℝ H) (hM : IsClosed (M : Set H)) (x : H) :
    ∃! yz : M × Mᗮ, x = (yz.1 : H) + (yz.2 : H) := by
  letI : IsClosed (M : Set H) := hM
  letI : CompleteSpace M := IsClosed.completeSpace_coe
  letI : M.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace M
  obtain ⟨u, v, huv, huniq⟩ :=
    Submodule.existsUnique_add_of_isCompl (Submodule.isCompl_orthogonal M) x
  refine ⟨(u, v), huv.symm, ?_⟩
  rintro ⟨r, s⟩ hrs
  obtain ⟨hr, hs⟩ := huniq r s hrs.symm
  exact Prod.ext hr hs

/-- The real Riesz representation theorem, including preservation of the norm. -/
theorem riesz_representation (F : StrongDual ℝ H) :
    ∃! f : H, (∀ x, F x = inner ℝ x f) ∧ ‖F‖ = ‖f‖ := by
  let f := (InnerProductSpace.toDual ℝ H).symm F
  have hrep (x : H) : F x = inner ℝ x f := by
    calc
      F x = inner ℝ f x := InnerProductSpace.toDual_symm_apply.symm
      _ = inner ℝ x f := real_inner_comm x f
  have hnorm : ‖F‖ = ‖f‖ := by
    change ‖F‖ = ‖(InnerProductSpace.toDual ℝ H).symm F‖
    exact ((InnerProductSpace.toDual ℝ H).symm.norm_map F).symm
  refine ⟨f, ⟨hrep, hnorm⟩, ?_⟩
  intro g hg
  apply ext_inner_left ℝ
  intro x
  rw [← hrep x, ← hg.1 x]

end Projection

section LaxMilgram

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The boundedness condition for a real bilinear form. -/
def IsBoundedBilinearForm (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) : Prop :=
  ∃ K : ℝ, ∀ x y, |B x y| ≤ K * ‖x‖ * ‖y‖

/-- The coercivity condition for a real bilinear form. -/
def IsCoerciveBilinearForm (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) : Prop :=
  ∃ ν : ℝ, 0 < ν ∧ ∀ x, ν * ‖x‖ ^ 2 ≤ B x x

/-- The Lax--Milgram theorem in the second-argument convention of Gilbarg--Trudinger. -/
private theorem lax_milgram_continuous (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : IsCoercive B)
    (F : StrongDual ℝ H) :
    ∃! f : H, ∀ x, B x f = F x := by
  let B' : H →L[ℝ] H →L[ℝ] ℝ := B.flip
  have hB' : IsCoercive B' := by
    obtain ⟨ν, hν, hcoercive⟩ := hB
    exact ⟨ν, hν, fun u => by simpa [B'] using hcoercive u⟩
  let e : H ≃L[ℝ] H := hB'.continuousLinearEquivOfBilin
  let g : H := (InnerProductSpace.toDual ℝ H).symm F
  let f : H := e.symm g
  have hf (x : H) : B x f = F x := by
    calc
      B x f = B' f x := rfl
      _ = inner ℝ (e f) x := (hB'.continuousLinearEquivOfBilin_apply f x).symm
      _ = inner ℝ g x := by rw [e.apply_symm_apply]
      _ = F x := InnerProductSpace.toDual_symm_apply
  refine ⟨f, hf, ?_⟩
  intro q hq
  apply e.injective
  apply ext_inner_right ℝ
  intro x
  rw [hB'.continuousLinearEquivOfBilin_apply, hB'.continuousLinearEquivOfBilin_apply]
  change B x q = B x f
  rw [hq x, hf x]

/-- The Lax--Milgram theorem for a bounded, coercive bilinear form. -/
theorem lax_milgram (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (hB_bound : IsBoundedBilinearForm B)
    (hB_coercive : IsCoerciveBilinearForm B) (F : StrongDual ℝ H) :
    ∃! f : H, ∀ x, B x f = F x := by
  obtain ⟨K, hK⟩ := hB_bound
  have hK_norm : ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖ := by
    intro x y
    simpa only [Real.norm_eq_abs] using hK x y
  let Bc : H →L[ℝ] H →L[ℝ] ℝ := B.mkContinuous₂ K hK_norm
  have hBc : IsCoercive Bc := by
    obtain ⟨ν, hν, hcoercive⟩ := hB_coercive
    refine ⟨ν, hν, ?_⟩
    intro u
    simpa only [Bc, LinearMap.mkContinuous₂_apply, pow_two, mul_assoc] using hcoercive u
  obtain ⟨f, hf, huniq⟩ := lax_milgram_continuous Bc hBc F
  refine ⟨f, ?_, ?_⟩
  · intro x
    simpa only [Bc, LinearMap.mkContinuous₂_apply] using hf x
  · intro g hg
    apply huniq
    intro x
    simpa only [Bc, LinearMap.mkContinuous₂_apply] using hg x

end LaxMilgram

section Adjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The defining identity and norm equality for the adjoint of a Hilbert-space operator. -/
theorem hilbert_adjoint_characterization (T : H →L[ℝ] H) :
    (∀ x y, inner ℝ (ContinuousLinearMap.adjoint T y) x = inner ℝ y (T x)) ∧
      ‖ContinuousLinearMap.adjoint T‖ = ‖T‖ :=
  ⟨ContinuousLinearMap.adjoint_inner_left T, ContinuousLinearMap.adjoint.norm_map T⟩

/-- The adjoint of a compact operator on a Hilbert space is compact. -/
theorem compact_adjoint (T : H →L[ℝ] H) (hT : IsCompactMap T) :
    IsCompactMap (ContinuousLinearMap.adjoint T) := by
  rw [compact_map_iff_bounded_sequence]
  intro u hu
  let A : H →L[ℝ] H := ContinuousLinearMap.adjoint T
  have hAu : Bornology.IsBounded (Set.range fun n ↦ A (u n)) := by
    rw [show Set.range (fun n ↦ A (u n)) = A '' Set.range u by
      simpa only [Function.comp_def] using Set.range_comp A u]
    exact A.lipschitz.isBounded_image hu
  obtain ⟨y, φ, hφ, hconv⟩ :=
    (compact_map_iff_bounded_sequence T).mp hT (fun n ↦ A (u n)) hAu
  have hTTcauchy : CauchySeq (fun n ↦ T (A (u (φ n)))) := hconv.cauchySeq
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp hu
  have hC0 : 0 ≤ C := by simpa using hC 0 0
  have hAcauchy : CauchySeq (fun n ↦ A (u (φ n))) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    let δ : ℝ := ε ^ 2 / (C + 1)
    have hδ : 0 < δ := div_pos (sq_pos_of_pos hε) (by linarith)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hTTcauchy δ hδ
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    let d : H := u (φ m) - u (φ n)
    have hd : ‖d‖ ≤ C := by
      simpa only [d, dist_eq_norm] using hC (φ m) (φ n)
    have hTd : ‖T (A d)‖ < δ := by
      simpa only [d, map_sub, dist_eq_norm] using hN m hm n hn
    have hsq : ‖A d‖ ^ 2 = inner ℝ d (T (A d)) := by
      simpa only [A, ContinuousLinearMap.adjoint_adjoint,
        ContinuousLinearMap.comp_apply, RCLike.re_to_real] using
        ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right A d
    have hnormsq : ‖A d‖ ^ 2 ≤ ‖d‖ * ‖T (A d)‖ := by
      rw [hsq]
      exact real_inner_le_norm d (T (A d))
    have hlt : ‖A d‖ ^ 2 < ε ^ 2 := calc
      ‖A d‖ ^ 2 ≤ ‖d‖ * ‖T (A d)‖ := hnormsq
      _ ≤ C * ‖T (A d)‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hTd.le hC0
      _ < ε ^ 2 := by
        dsimp [δ]
        rw [show C * (ε ^ 2 / (C + 1)) = (C / (C + 1)) * ε ^ 2 by ring]
        simpa only [one_mul] using
          mul_lt_mul_of_pos_right ((div_lt_one (by linarith)).2 (by linarith))
            (sq_pos_of_pos hε)
    have hnorm : ‖A d‖ < ε := (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hlt
    simpa only [d, map_sub, dist_eq_norm] using hnorm
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hAcauchy
  exact ⟨a, φ, hφ, ha⟩

/-- The closure of an operator's range is the orthogonal complement of its adjoint's kernel. -/
theorem closure_range_eq_orthogonal_ker_adjoint (T : H →L[ℝ] H) :
    (T : Module.End ℝ H).range.topologicalClosure =
      ((ContinuousLinearMap.adjoint T : H →L[ℝ] H) : Module.End ℝ H).kerᗮ := by
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    (ContinuousLinearMap.orthogonal_ker (ContinuousLinearMap.adjoint T)).symm

end Adjoint

section WeakConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weak convergence tested against every bounded linear functional. -/
def WeaklyConverges (u : ℕ → E) (x : E) : Prop :=
  ∀ F : StrongDual ℝ E, Filter.Tendsto (fun n => F (u n)) Filter.atTop (nhds (F x))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- In a Hilbert space, weak convergence is equivalently tested by inner products. -/
theorem weaklyConverges_iff_inner {u : ℕ → H} {x : H} :
    WeaklyConverges u x ↔
      ∀ y : H, Filter.Tendsto (fun n => inner ℝ (u n) y) Filter.atTop
        (nhds (inner ℝ x y)) := by
  constructor
  · intro hu y
    simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      hu ((InnerProductSpace.toDual ℝ H) y)
  · intro hu F
    let y := (InnerProductSpace.toDual ℝ H).symm F
    simpa only [← InnerProductSpace.toDual_symm_apply, real_inner_comm] using hu y

/-- Every bounded sequence in a Hilbert space has a weakly convergent subsequence. -/
theorem weak_sequential_compactness (u : ℕ → H)
    (hu : Bornology.IsBounded (Set.range u)) :
    ∃ x : H, ∃ φ : ℕ → ℕ, StrictMono φ ∧ WeaklyConverges (fun n ↦ u (φ n)) x := by
  let M : Submodule ℝ H := (Submodule.span ℝ (Set.range u)).topologicalClosure
  have huM (n : ℕ) : u n ∈ M := by
    change u n ∈ closure (Submodule.span ℝ (Set.range u) : Set H)
    exact subset_closure (Submodule.subset_span ⟨n, rfl⟩)
  let uM : ℕ → M := fun n ↦ ⟨u n, huM n⟩
  letI : IsClosed (M : Set H) := Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace M := IsClosed.completeSpace_coe
  have hsep : TopologicalSpace.IsSeparable (M : Set H) := by
    rw [show (M : Set H) = closure (Submodule.span ℝ (Set.range u) : Set H) by
      exact Submodule.topologicalClosure_coe _]
    exact Set.countable_range u |>.isSeparable.span.closure
  letI : TopologicalSpace.SeparableSpace M := hsep.separableSpace
  have huMbdd : Bornology.IsBounded (Set.range uM) := by
    rw [Metric.isBounded_range_iff] at hu ⊢
    obtain ⟨C, hC⟩ := hu
    refine ⟨C, fun i j ↦ ?_⟩
    rw [Subtype.dist_eq]
    exact hC i j
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : M)).mp huMbdd
  let f : ℕ → WeakDual ℝ M := fun n ↦
    StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ M) (uM n))
  have hfmem : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 r := by
    intro n
    dsimp [f]
    change WeakDual.toStrongDual
      (StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ M) (uM n))) ∈
        Metric.closedBall 0 r
    rw [StrongDual.toStrongDual_toWeakDual]
    change dist ((InnerProductSpace.toDual ℝ M) (uM n)) 0 ≤ r
    have hn := Metric.mem_closedBall.mp (hr ⟨n, rfl⟩)
    simpa only [LinearIsometryEquiv.norm_map, dist_zero_right] using hn
  obtain ⟨g, -, φ, hφ, hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ M 0 r) hfmem
  let xM : M := (InnerProductSpace.toDual ℝ M).symm (WeakDual.toStrongDual g)
  have hinner (z : M) : Filter.Tendsto (fun n ↦ inner ℝ (uM (φ n)) z) Filter.atTop
      (nhds (inner ℝ xM z)) := by
    have hz := tendsto_iff_forall_eval_tendsto_topDualPairing.mp hlim z
    change Filter.Tendsto (fun i ↦ ((InnerProductSpace.toDual ℝ M) (uM (φ i))) z)
      Filter.atTop (nhds ((WeakDual.toStrongDual g) z)) at hz
    simpa only [InnerProductSpace.toDual_apply_apply, xM,
      InnerProductSpace.toDual_symm_apply] using hz
  have hweakM : WeaklyConverges (fun n ↦ uM (φ n)) xM :=
    weaklyConverges_iff_inner.mpr hinner
  refine ⟨xM, φ, hφ, ?_⟩
  intro F
  have hF := hweakM (F.comp M.subtypeL)
  simpa only [uM, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using hF

end WeakConvergence

end GilbargTrudinger
