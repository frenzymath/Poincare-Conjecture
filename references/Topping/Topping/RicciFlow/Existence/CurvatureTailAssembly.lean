import Topping.RicciFlow.Existence.CurvatureSupAttainment
import Topping.MaximumPrinciple.CurvatureNormShift
import Topping.RicciFlow.Existence.IntrinsicNormSpacetime

/-!
# Prefix and tail assembly for finite-time curvature control

This module records the order-theoretic assembly which sits between the
non-blow-up alternative and the endpoint extension theorem.  A compact
continuous prefix supplies one bound, while the affine-time curvature
comparison supplies a second bound on a short tail.  The endpoint smoothness
and restart arguments remain separate.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Filter Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [Nonempty M] [CompactSpace M]

/-! ## Compact prefix bounds -/

omit [I.Boundaryless] [Nonempty M] in
/-- **Math.** A jointly continuous curvature norm on a compact prefix has a
finite pointwise upper bound. -/
theorem exists_uniform_curvature_bound_on_Icc_of_continuous
    {g : ℝ → RiemannianMetric I M} {a : ℝ}
    (hcont : ContinuousOn
      (fun z : M × ℝ => riemannNormAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc (0 : ℝ) a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc (0 : ℝ) a, ∀ p : M, riemannNormAt (g t) p ≤ C := by
  let K : Set (M × ℝ) := (Set.univ : Set M) ×ˢ Icc (0 : ℝ) a
  have hK : IsCompact K := by
    dsimp [K]
    exact isCompact_univ.prod isCompact_Icc
  have himage : IsCompact
      ((fun z : M × ℝ => riemannNormAt (g z.2) z.1) '' K) :=
    hK.image_of_continuousOn hcont
  obtain ⟨C, hC⟩ := himage.bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht p
  have hp : (p, t) ∈ K := by
    exact ⟨Set.mem_univ p, ht⟩
  have him : riemannNormAt (g t) p ∈
      ((fun z : M × ℝ => riemannNormAt (g z.2) z.1) '' K) :=
    ⟨(p, t), hp, rfl⟩
  exact (hC him).trans (le_max_left _ _)

/-! ## Short tails from an anchored comparison -/

omit [Nonempty M] in
/-- **Math.** An anchored curvature comparison with a uniformly positive
denominator gives a bound on every later point before the chosen endpoint. -/
theorem exists_uniform_curvature_bound_on_Ico_of_anchored_comparison
    : ∃ c : ℝ, 0 ≤ c ∧
      ∀ (g : ℝ → RiemannianMetric I M) (T a m : ℝ),
        0 < a → a < T → 0 < m →
        ContinuousOn
          (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
          ((Set.univ : Set M) ×ˢ Ico 0 T) →
        MorganTianLib.IsRicciFlowOn g (Ico 0 T) →
        (∀ t ∈ Icc a T, 0 < 1 - c * m * (t - a) / 2) →
        (∀ p : M, riemannNormAt (g a) p ≤ m) →
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ t ∈ Ico a T, ∀ p : M, riemannNormAt (g t) p ≤ C := by
  obtain ⟨Ccomp, hCcomp, hcomp⟩ :=
    exists_uniform_riemannNormAt_le_on_Icc_of_morganTian_isRicciFlowOn_of_subset
      (I := I) (M := M)
  refine ⟨Ccomp, hCcomp, ?_⟩
  intro g T a m ha0 haT hm hcont hflow hdenom hanchor
  let C : ℝ := m / (1 - Ccomp * m * (T - a) / 2)
  have hCpos : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (le_of_lt hm)
      (le_of_lt (hdenom T ⟨le_of_lt haT, le_rfl⟩))
  refine ⟨C, hCpos, ?_⟩
  intro t ht p
  have htT : t < T := ht.2
  have htb : t ∈ Icc a ((t + T) / 2) := by
    constructor
    · exact ht.1
    · linarith
  have hab : a < (t + T) / 2 := by
    linarith [htT, ht.1]
  have hsubset : Icc a ((t + T) / 2) ⊆ Ico 0 T := by
    intro u hu
    constructor
    · exact le_trans (le_of_lt ha0) hu.1
    · linarith [hu.2, htT]
  have hcont' : ContinuousOn
      (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
      ((Set.univ : Set M) ×ˢ Icc a ((t + T) / 2)) := by
    apply hcont.mono
    have hmidT : (t + T) / 2 < T := by linarith [htT]
    exact Set.prod_mono subset_rfl (by
      intro u hu
      exact ⟨le_trans (le_of_lt ha0) hu.1,
        lt_of_le_of_lt hu.2 hmidT⟩)
  have hdenom' : ∀ u ∈ Icc a ((t + T) / 2),
      0 < 1 - Ccomp * m * (u - a) / 2 := by
    intro u hu
    have hmidT : (t + T) / 2 < T := by linarith [htT]
    exact hdenom u ⟨hu.1, le_of_lt (lt_of_le_of_lt hu.2 hmidT)⟩
  have hbound := hcomp g (Ico 0 T) m a ((t + T) / 2) hab hm hcont'
    hflow hsubset hdenom' hanchor
  have hpoint := hbound p t htb
  have hdenomT :
      1 - Ccomp * m * (T - a) / 2 ≤
        1 - Ccomp * m * (t - a) / 2 := by
    have hmono : Ccomp * m * (t - a) / 2 ≤
        Ccomp * m * (T - a) / 2 := by
      have hcm : 0 ≤ Ccomp * m := mul_nonneg hCcomp (le_of_lt hm)
      have hta : t - a ≤ T - a := by linarith [htT]
      nlinarith [hcm, hta]
    linarith
  have hfrac : m / (1 - Ccomp * m * (t - a) / 2) ≤ C := by
    dsimp [C]
    exact div_le_div_of_nonneg_left (le_of_lt hm)
      (hdenom T ⟨le_of_lt haT, le_rfl⟩) hdenomT
  exact hpoint.trans hfrac

/-! ## Combined prefix/tail consumer -/

omit [I.Boundaryless] [Nonempty M] [CompactSpace M] in
/-- **Math.** Prefix and tail bounds combine into the uniform pre-endpoint
curvature contract used by the finite-time extension argument. -/
theorem hasUniformCurvatureBoundBefore_of_prefix_and_tail
    {g : ℝ → RiemannianMetric I M} {T a C₀ C₁ : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hprefix : ∀ t ∈ Icc (0 : ℝ) a, ∀ p : M,
      riemannNormAt (g t) p ≤ C₀)
    (htail : ∀ t ∈ Ico a T, ∀ p : M,
      riemannNormAt (g t) p ≤ C₁) :
    HasUniformCurvatureBoundBefore g T := by
  have hmax : 0 ≤ max C₀ C₁ := by
    rcases le_total C₀ C₁ with h | h
    · exact hC₁.trans (le_max_right _ _)
    · exact hC₀.trans (le_max_left _ _)
  refine ⟨max C₀ C₁, hmax, ?_⟩
  intro t ht p
  by_cases hta : t ≤ a
  · exact (hprefix t ⟨ht.1, hta⟩ p).trans (le_max_left _ _)
  · exact (htail t ⟨le_of_lt (lt_of_not_ge hta), ht.2⟩ p).trans
      (le_max_right _ _)

#print axioms exists_uniform_curvature_bound_on_Icc_of_continuous
#print axioms exists_uniform_curvature_bound_on_Ico_of_anchored_comparison
#print axioms hasUniformCurvatureBoundBefore_of_prefix_and_tail

end Topping

end
