import MorganTianLib.Ch05.Packing

/-!
# Morgan--Tian Chapter 5: completion and properness adapters

The packing producer supplies total boundedness of closed balls.  This module
records the standard complete-space bridge that turns those boundedness facts
into compact balls and hence a proper metric space.  It is deliberately
separate from the pointed-GH extraction theorem, whose diagonal realization
requires additional compactness data.
-/

open Set Metric

namespace MorganTianLib

universe u

/-- **Math.** In a complete metric space, a totally bounded closed ball is
compact. -/
theorem isCompact_closedBall_of_complete_of_totallyBounded
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (x : X) (R : ℝ)
    (hball : TotallyBounded (closedBall x R)) :
    IsCompact (closedBall x R) := by
  exact hball.isCompact_of_isClosed isClosed_closedBall

/-- **Math.** Completeness together with total boundedness of every closed ball
implies properness. -/
theorem properSpace_of_complete_of_totallyBounded_closedBall
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hball : ∀ (x : X) (R : ℝ), TotallyBounded (closedBall x R)) :
    ProperSpace X := by
  refine ⟨fun x R => ?_⟩
  exact isCompact_closedBall_of_complete_of_totallyBounded x R (hball x R)

/-- **Math.** A complete metric space with uniform all-scale packing bounds is
proper.  The bound is allowed to depend on the centre and the two scales. -/
theorem properSpace_of_complete_of_uniform_packing_bound
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hpack : ∀ (x : X) (δ R : ℝ), 0 < δ →
      ∃ N : ℕ, ∀ n, n ∈ packingAdmissible x δ R → n ≤ N) :
    ProperSpace X := by
  apply properSpace_of_complete_of_totallyBounded_closedBall
  intro x R
  by_cases hR : 0 ≤ R
  · apply totallyBounded_closedBall_of_uniform_packing_bound x hR
    intro δ S hδ
    exact hpack x δ S hδ
  · rw [Metric.closedBall_of_neg (lt_of_not_ge hR)]
    exact totallyBounded_empty

/-- **Math.** If an isometric partial-limit map covers its compact exhaustion,
then the target inherits completeness from the source. -/
theorem completeSpace_of_partialLimit_isometry_of_imageCovers
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace X]
    {x : X} (V : CompactExhaustion X x) (f : X → Y)
    (hf : Isometry f) (hcover : PartialLimitImageCovers V f) :
    CompleteSpace Y := by
  obtain ⟨e, he⟩ :=
    partialLimit_isometryEquiv_of_isometry_of_imageCovers V f hf hcover
  exact (IsometryEquiv.completeSpace_iff e).mp inferInstance

/-- **Math.** An isometric partial-limit map with compact-buffer image coverage
transfers completeness in both directions.  This is the converse companion to
`completeSpace_of_partialLimit_isometry_of_imageCovers` and exposes the exact
metric content of the completion bridge. -/
theorem completeSpace_iff_of_partialLimit_isometry_of_imageCovers
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {x : X} (V : CompactExhaustion X x) (f : X → Y)
    (hf : Isometry f) (hcover : PartialLimitImageCovers V f) :
    CompleteSpace X ↔ CompleteSpace Y := by
  obtain ⟨e, he⟩ :=
    partialLimit_isometryEquiv_of_isometry_of_imageCovers V f hf hcover
  constructor
  · intro hX
    letI : CompleteSpace X := hX
    exact (IsometryEquiv.completeSpace_iff e).mp inferInstance
  · intro hY
    letI : CompleteSpace Y := hY
    exact (IsometryEquiv.completeSpace_iff e).mpr inferInstance

/-! A compact-buffer variant of the preceding bridge.  In geometric-limit
arguments the naturally available coverage is often by the compact closures of
the exhaustion stages, rather than by the open stages themselves.  We keep
that interface separate: it does not assert that a closure is open or silently
change `PartialLimitImageCovers`. -/

/-- **Math.** Image coverage by compact exhaustion buffers. -/
def PartialLimitClosureImageCovers
    {X Y : Type*} [TopologicalSpace X]
    {x : X} (V : CompactExhaustion X x) (f : X → Y) : Prop :=
  ∀ y : Y, ∃ k, y ∈ f '' closure (V.set k)

theorem partialLimit_surjective_of_closureImageCovers
    {X Y : Type*} [TopologicalSpace X] {x : X}
    (V : CompactExhaustion X x) (f : X → Y)
    (hcover : PartialLimitClosureImageCovers V f) :
    Function.Surjective f := by
  intro y
  obtain ⟨k, ⟨z, hz, rfl⟩⟩ := hcover y
  exact ⟨z, rfl⟩

theorem partialLimit_isometryEquiv_of_isometry_of_closureImageCovers
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {x : X}
    (V : CompactExhaustion X x) (f : X → Y)
    (hf : Isometry f)
    (hcover : PartialLimitClosureImageCovers V f) :
    ∃ e : X ≃ᵢ Y, (e : X → Y) = f := by
  have hsurj : Function.Surjective f :=
    partialLimit_surjective_of_closureImageCovers V f hcover
  refine ⟨IsometryEquiv.mk' f (Function.surjInv hsurj)
      (Function.surjInv_eq hsurj) hf, ?_⟩
  rfl

theorem completeSpace_iff_of_partialLimit_isometry_of_closureImageCovers
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {x : X} (V : CompactExhaustion X x) (f : X → Y)
    (hf : Isometry f) (hcover : PartialLimitClosureImageCovers V f) :
    CompleteSpace X ↔ CompleteSpace Y := by
  obtain ⟨e, he⟩ :=
    partialLimit_isometryEquiv_of_isometry_of_closureImageCovers V f hf hcover
  constructor
  · intro hX
    letI : CompleteSpace X := hX
    exact (IsometryEquiv.completeSpace_iff e).mp inferInstance
  · intro hY
    letI : CompleteSpace Y := hY
    exact (IsometryEquiv.completeSpace_iff e).mpr inferInstance

end MorganTianLib
