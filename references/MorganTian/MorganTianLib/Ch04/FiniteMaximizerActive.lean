import MorganTianLib.Ch04.CompactTensorEnvelope

/-!
# Positive finite-family maxima expose an active support branch

The compact support envelope includes a constant-zero competitor.  At a
strictly positive maximum the maximizing index therefore lies in the support
branch `Sum.inr`, which is the index needed by the active-fibre estimate.
-/

open Set
open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace MorganTianLib

theorem exists_inr_positive_maximizer
    {P : Type*} [TopologicalSpace P] [CompactSpace P] [Nonempty P]
    {F : (Unit ⊕ P) → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (t : ℝ)
    (hpos : 0 < ⨆ q : Unit ⊕ P, F q t)
    (hzero : ∀ z : Unit, F (Sum.inl z) t = 0) :
    ∃ p : P, F (Sum.inr p) t = ⨆ q : Unit ⊕ P, F q t ∧
      0 < F (Sum.inr p) t := by
  obtain ⟨q, hq, hqpos⟩ :=
    exists_finiteTensorSupport_positive_maximizer hF t hpos
  cases q with
  | inl z =>
      rw [hzero z] at hqpos
      linarith
  | inr p =>
      exact ⟨p, hq, hqpos⟩

/-- **Math.** A positive maximizer of a compact family also maximizes any dominating
fibre-value family when the two suprema agree.  This is the order bridge from
the finite support index to the concrete tensor fibre. -/
theorem exists_positive_maximizer_attaining_dominating_value
    {P X : Type*} [TopologicalSpace P] [CompactSpace P] [Nonempty P]
    {F : P → ℝ → ℝ} {D : X → ℝ} {proj : P → X}
    (hF : Continuous (Function.uncurry F)) (t : ℝ)
    (hle : ∀ q : P, F q t ≤ D (proj q))
    (hDb : BddAbove (Set.range D))
    (hsup : (⨆ q : P, F q t) = ⨆ x : X, D x)
    (hpos : 0 < ⨆ q : P, F q t) :
    ∃ q : P, F q t = ⨆ r : P, F r t ∧ 0 < F q t ∧
      D (proj q) = ⨆ x : X, D x := by
  obtain ⟨q, hq, hqpos⟩ := exists_finiteTensorSupport_positive_maximizer hF t hpos
  have hDle : D (proj q) ≤ ⨆ x : X, D x :=
    le_ciSup hDb (proj q)
  have hFleD : F q t ≤ D (proj q) := hle q
  have hDleF : D (proj q) ≤ F q t := by
    rw [hq, hsup]
    exact le_ciSup hDb (proj q)
  refine ⟨q, hq, hqpos, ?_⟩
  linarith

/-- **Math.** Equality with a supremum is the global maximum property needed by the
local tensor-support Laplacian producer. -/
theorem isMaxOn_univ_of_eq_ciSup
    {X : Type*} {D : X → ℝ} {x : X}
    (hD : BddAbove (Set.range D)) (hx : D x = ⨆ y : X, D y) :
    IsMaxOn D (Set.univ : Set X) x := by
  intro y _
  rw [hx]
  exact le_ciSup hD y

/-- **Math.** The combined bridge used by Hamilton's tensor argument: a positive finite
support maximum exposes a concrete index whose dominating fibre value is a
global maximum, hence supplies the spatial `IsMaxOn` hypothesis. -/
theorem exists_positive_maximizer_with_dominating_global_max
    {P X : Type*} [TopologicalSpace P] [CompactSpace P] [Nonempty P]
    {F : P → ℝ → ℝ} {D : X → ℝ} {proj : P → X}
    (hF : Continuous (Function.uncurry F)) (t : ℝ)
    (hle : ∀ q : P, F q t ≤ D (proj q))
    (hDb : BddAbove (Set.range D))
    (hsup : (⨆ q : P, F q t) = ⨆ x : X, D x)
    (hpos : 0 < ⨆ q : P, F q t) :
    ∃ q : P, F q t = ⨆ r : P, F r t ∧ 0 < F q t ∧
      D (proj q) = ⨆ x : X, D x ∧
      IsMaxOn D (Set.univ : Set X) (proj q) := by
  obtain ⟨q, hq, hqpos, hDq⟩ :=
    exists_positive_maximizer_attaining_dominating_value hF t hle hDb hsup hpos
  refine ⟨q, hq, hqpos, hDq, isMaxOn_univ_of_eq_ciSup hDb hDq⟩

theorem exists_positive_finiteTensorSupport_patch_with_fibre_max
    {E H M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M]
    (g : RiemannianMetric I M) {k : ℕ} (s : Finset M) (K : M → Set M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x)))
    (R : M → ℝ)
    (F : (Unit ⊕ Σ p : s, K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) →
      ℝ → ℝ)
    (D : M → ℝ) (hK : ∀ p, IsCompact (K p)) (hZ : ∀ p, IsClosed (Z p))
    (hF : Continuous (Function.uncurry F)) (t : ℝ)
    (hzero : ∀ z : Unit, F (Sum.inl z) t = 0)
    (hDnonneg : ∀ x, 0 ≤ D x)
    (hpointwise : ∀ (p : s) (x : K p)
      (q : BoundedConvexSupportPair
        (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)),
      F (Sum.inr ⟨p, x, q⟩) t ≤ D x)
    (hDb : BddAbove (Set.range D))
    (hsup : (⨆ q, F q t) = ⨆ x : M, D x)
    (hpos : 0 < ⨆ q, F q t),
    ∃ (p : s) (x : K p)
      (q : BoundedConvexSupportPair
        (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)),
      F (Sum.inr ⟨p, x, q⟩) t = (⨆ r, F r t) ∧
        0 < F (Sum.inr ⟨p, x, q⟩) t ∧ D x = ⨆ y : M, D y ∧
        IsMaxOn D (Set.univ : Set M) x := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z R F D hK hZ hF t hzero hDnonneg hpointwise hDb hsup hpos
  letI (p : s) : CompactSpace (K p) :=
    isCompact_iff_compactSpace.mp (hK p)
  letI (p : s) : CompactSpace
      (BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) :=
    compactSpace_boundedConvexSupportPair _ _
      ((hZ p).preimage hilbertCovariantTensorEquiv.continuous)
  letI : CompactSpace (Σ p : s, K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) := inferInstance
  letI : CompactSpace (Unit ⊕ Σ p : s, K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) := inferInstance
  let proj : (Unit ⊕ Σ p : s, K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) → M :=
    fun o => match o with
      | Sum.inl _ => Classical.arbitrary M
      | Sum.inr q => q.2.1
  have hle : ∀ q, F q t ≤ D (proj q) := by
    intro q
    cases q with
    | inl z => simpa [proj, hzero z] using hDnonneg (Classical.arbitrary M)
    | inr q =>
        exact hpointwise q.1 q.2.1 q.2.2
  obtain ⟨q, hq, hqpos, hDq, hmax⟩ :=
    exists_positive_maximizer_with_dominating_global_max hF t hle hDb hsup hpos
  cases q with
  | inl z =>
      rw [hzero z] at hqpos
      linarith
  | inr q =>
      rcases q with ⟨⟨p, hp⟩, ⟨x, hx⟩, q⟩
      exact ⟨⟨p, hp⟩, ⟨x, hx⟩, q, hq, hqpos, hDq, hmax⟩

/-! The tensor-envelope index is a dependent sum over finitely many compact
patches.  This wrapper exposes the patch, point, and bounded support pair
hidden by the generic `Sum.inr` branch, so the geometric active-support
estimate can consume the actual fibre data. -/

theorem exists_positive_finiteTensorSupport_patch
    {E H M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M]
    (g : RiemannianMetric I M) {k : ℕ} (s : Finset M) (K : M → Set M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x)))
      (R : M → ℝ) (hK : ∀ p, IsCompact (K p)) (hZ : ∀ p, IsClosed (Z p))
      (F : (Unit ⊕ Σ p : s, K p ×
        BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) →
        ℝ → ℝ),
      Continuous (Function.uncurry F) → (t : ℝ) →
      (hzero : ∀ z : Unit, F (Sum.inl z) t = 0) →
      (0 < ⨆ q, F q t) →
      ∃ (p : s) (x : K p)
        (q : BoundedConvexSupportPair
          (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)),
        F (Sum.inr ⟨p, x, q⟩) t = (⨆ r, F r t) ∧
          0 < F (Sum.inr ⟨p, x, q⟩) t := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z R hK hZ F hF t hzero hpos
  letI (p : s) : CompactSpace (K p) :=
    isCompact_iff_compactSpace.mp (hK p)
  letI (p : s) : CompactSpace
      (BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) :=
    compactSpace_boundedConvexSupportPair _ _
      ((hZ p).preimage hilbertCovariantTensorEquiv.continuous)
  letI : CompactSpace (Σ p : s, K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) := inferInstance
  letI : CompactSpace (Unit ⊕ Σ p : s, K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) := inferInstance
  obtain ⟨o, ho, hopos⟩ :=
    exists_finiteTensorSupport_positive_maximizer
      (P := Unit ⊕ Σ p : s, K p ×
        BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p))
      (F := F) hF t hpos
  cases o with
  | inl z =>
      rw [hzero z] at hopos
      linarith
  | inr q =>
      rcases q with ⟨⟨p, hp⟩, ⟨x, hx⟩, q⟩
      exact ⟨⟨p, hp⟩, ⟨x, hx⟩, q, ho, hopos⟩

end MorganTianLib

#print axioms MorganTianLib.exists_inr_positive_maximizer
#print axioms MorganTianLib.exists_positive_maximizer_attaining_dominating_value
#print axioms MorganTianLib.isMaxOn_univ_of_eq_ciSup
#print axioms MorganTianLib.exists_positive_maximizer_with_dominating_global_max
#print axioms MorganTianLib.exists_positive_finiteTensorSupport_patch_with_fibre_max
#print axioms MorganTianLib.exists_positive_finiteTensorSupport_patch
