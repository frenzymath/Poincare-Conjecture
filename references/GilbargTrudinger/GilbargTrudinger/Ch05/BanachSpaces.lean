import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.MetricSpace.Contracting

/-! # Banach-space results from Gilbarg--Trudinger, Chapter 5 -/

namespace GilbargTrudinger

section ContractionMapping

variable {E : Type*} [NormedAddCommGroup E]

/-- A self-map is a contraction when it is Lipschitz with a constant strictly below one. -/
def IsContraction (T : E → E) : Prop :=
  ∃ K : NNReal, ContractingWith K T

/-- The contraction mapping principle on a Banach space. -/
theorem contraction_mapping_principle [CompleteSpace E] (T : E → E) (hT : IsContraction T) :
    ∃! x, Function.IsFixedPt T x := by
  obtain ⟨K, hK⟩ := hT
  refine ⟨hK.fixedPoint, hK.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact hK.fixedPoint_unique hy

end ContractionMapping

section BoundedLinearOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev BoundedLinearOperator (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  E →L[ℝ] F

def operatorNormRatios (T : E →L[ℝ] F) : Set ℝ :=
  {r | ∃ x : E, x ≠ 0 ∧ r = ‖T x‖ / ‖x‖}

/-- The operator norm is the supremum of `‖T x‖ / ‖x‖` over nonzero vectors. -/
theorem operator_norm_eq_sSup_ratio (T : E →L[ℝ] F) :
    ‖T‖ = sSup (operatorNormRatios T) := by
  cases subsingleton_or_nontrivial E with
  | inl hE =>
      have hT : T = 0 := by
        ext x
        rw [Subsingleton.elim x 0, map_zero]
        rfl
      have hratios : operatorNormRatios T = ∅ := by
        ext r
        simp only [operatorNormRatios, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨x, hx, -⟩
        exact hx (Subsingleton.elim x 0)
      rw [hratios, hT]
      simp
  | inr hE =>
      letI : Nontrivial E := hE
      obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
      have hratios : (operatorNormRatios T).Nonempty :=
        ⟨‖T x₀‖ / ‖x₀‖, x₀, hx₀, rfl⟩
      have hbdd : BddAbove (operatorNormRatios T) := by
        refine ⟨‖T‖, ?_⟩
        rintro r ⟨x, -, rfl⟩
        exact T.ratio_le_opNorm x
      apply le_antisymm
      · rw [← T.sSup_sphere_eq_norm]
        refine csSup_le ((NormedSpace.sphere_nonempty (E := E)).mpr zero_le_one |>.image _) ?_
        rintro r ⟨x, hx, rfl⟩
        have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
        apply le_csSup hbdd
        refine ⟨x, ?_, ?_⟩
        · intro hzero
          simp [hzero] at hxnorm
        · simp [hxnorm]
      · refine csSup_le hratios ?_
        rintro r ⟨x, -, rfl⟩
        exact T.ratio_le_opNorm x

/-- A map between real normed spaces is bounded linear exactly when it is linear and continuous. -/
theorem bounded_linear_iff_linear_continuous (T : E → F) :
    IsBoundedLinearMap ℝ T ↔ IsLinearMap ℝ T ∧ Continuous T :=
  (IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap T).symm

end BoundedLinearOperators

section CompactMaps

open Filter Set Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- A map is compact when the closure of the image of every bounded set is compact. -/
def IsCompactMap (T : E → F) : Prop :=
  ∀ S : Set E, Bornology.IsBounded S → IsCompact (closure (T '' S))

/-- The sequential formulation of compactness: bounded sequences have image subsequences that
converge. -/
def MapsBoundedSequencesToConvergentSubsequences (T : E → F) : Prop :=
  ∀ u : ℕ → E, Bornology.IsBounded (Set.range u) →
    ∃ y : F, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ T (u (φ n))) atTop (nhds y)

/-- A map between normed spaces is compact exactly when every bounded sequence has an image
subsequence that converges. -/
theorem compact_map_iff_bounded_sequence (T : E → F) :
    IsCompactMap T ↔ MapsBoundedSequencesToConvergentSubsequences T := by
  constructor
  · intro hT u hu
    obtain ⟨y, -, φ, hφ, hlim⟩ :=
      (hT (Set.range u) hu).tendsto_subseq
        (x := fun n ↦ T (u n)) (fun n ↦ subset_closure ⟨u n, ⟨n, rfl⟩, rfl⟩)
    exact ⟨y, φ, hφ, hlim⟩
  · intro hT S hS
    rw [isCompact_iff_isSeqCompact]
    intro x hx
    have happ : ∀ n : ℕ, ∃ y ∈ T '' S, dist (x n) y < (1 : ℝ) / (n + 1) := by
      intro n
      exact Metric.mem_closure_iff.mp (hx n) _ (one_div_pos.mpr (by positivity))
    choose y hy hxy using happ
    have hy' : ∀ n : ℕ, ∃ u ∈ S, T u = y n := by
      intro n
      rcases hy n with ⟨u, hu, hTu⟩
      exact ⟨u, hu, hTu⟩
    choose u hu hTu using hy'
    have hubdd : Bornology.IsBounded (Set.range u) :=
      hS.subset (fun z ⟨n, hn⟩ ↦ hn ▸ hu n)
    obtain ⟨a, φ, hφ, hlim⟩ := hT u hubdd
    have hbound : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (φ n + 1)) atTop (nhds 0) := by
      simpa [Function.comp_def] using
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop)
    have hdist : Tendsto (fun n ↦ dist (x (φ n)) (T (u (φ n)))) atTop (nhds 0) := by
      apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_) hbound
      simpa [hTu (φ n)] using (hxy (φ n)).le
    refine ⟨a, ?_, φ, hφ, ?_⟩
    · apply isClosed_closure.mem_of_tendsto hlim
      exact Eventually.of_forall fun n ↦ subset_closure ⟨u (φ n), hu (φ n), rfl⟩
    · exact hlim.congr_dist (by simpa [dist_comm] using hdist)

section Linear

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- For linear maps, the bounded-set definition of compactness agrees with mathlib's compact
operator predicate. -/
theorem compact_map_linear_iff_isCompactOperator (T : E →ₗ[ℝ] F) :
    IsCompactMap T ↔ IsCompactOperator T := by
  constructor
  · intro hT
    rw [isCompactOperator_iff_isCompact_closure_image_closedBall T zero_lt_one]
    exact hT (Metric.closedBall 0 1) Metric.isBounded_closedBall
  · intro hT S hS
    exact hT.isCompact_closure_image_of_bounded hS

/-- A compact linear map between normed spaces is continuous. -/
theorem compact_linear_map_continuous (T : E →ₗ[ℝ] F) (hT : IsCompactMap T) :
    Continuous T :=
  (compact_map_linear_iff_isCompactOperator T).mp hT |>.continuous

end Linear

end CompactMaps

section RieszLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Riesz's lemma in the unit-vector, distance-to-subspace form. -/
theorem almost_orthogonal_vectors {M : Submodule ℝ E} (hM : IsClosed (M : Set E))
    (hM_proper : ∃ x, x ∉ M) {θ : ℝ} (hθ : θ < 1) :
    ∃ x : E, ‖x‖ = 1 ∧ θ ≤ Metric.infDist x M := by
  obtain ⟨x, -, hx_norm, hx_dist⟩ := riesz_lemma_of_lt_one hM hM_proper hθ
  refine ⟨x, hx_norm, (Metric.le_infDist M.nonempty).2 ?_⟩
  intro y hy
  simpa [dist_eq_norm] using hx_dist y hy

end RieszLemma

section DualSpaces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev DualSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  StrongDual ℝ E

/-- The continuous dual of a normed space is complete. -/
theorem dual_space_complete : CompleteSpace (DualSpace E) := inferInstance

/-- The dual norm is the supremum of the absolute-value ratios on nonzero vectors. -/
theorem dual_norm_eq_sSup_ratio (f : DualSpace E) :
    ‖f‖ = sSup {r | ∃ x : E, x ≠ 0 ∧ r = |f x| / ‖x‖} := by
  simpa only [operatorNormRatios, Real.norm_eq_abs] using operator_norm_eq_sSup_ratio f

/-- The canonical linear isometry from a normed space into its double dual. -/
noncomputable def canonicalEmbedding : E →ₗᵢ[ℝ] DualSpace (DualSpace E) :=
  NormedSpace.inclusionInDoubleDualLi ℝ

/-- A normed space is reflexive when its canonical embedding is onto. -/
def IsReflexiveSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  Function.Surjective (canonicalEmbedding (E := E))

@[simp]
theorem canonicalEmbedding_apply (x : E) (f : DualSpace E) : canonicalEmbedding x f = f x :=
  rfl

end DualSpaces

section DualAdjoint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The adjoint between Banach duals, defined by precomposition. -/
noncomputable def dualAdjoint (T : E →L[ℝ] F) : DualSpace F →L[ℝ] DualSpace E :=
  ContinuousLinearMap.precomp ℝ T

@[simp]
theorem dualAdjoint_apply (T : E →L[ℝ] F) (g : DualSpace F) (x : E) :
    dualAdjoint T g x = g (T x) :=
  rfl

end DualAdjoint

end GilbargTrudinger
