import Topping.RicciFlow.Existence.FlowIntervals

/-!
# Curvature-supremum and endpoint-filter bridges

These are the order/filter pieces used by the finite-time extension argument.
They keep the non-blow-up alternative honest: failure of a `Tendsto ... atTop`
assertion yields a frequently bounded sequence of times, not an (generally
false) eventual bound.  A separate consumer converts a genuine pointwise
supremum bound into `HasUniformCurvatureBoundBefore`.
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
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]

/-! ## Pointwise/supremum conversion -/

/-- A pointwise upper bound is an upper bound for the spatial curvature range. -/
theorem curvatureSup_le_of_pointwise_bound
    {g : ℝ → RiemannianMetric I M} {t C : ℝ}
    (hC : ∀ p : M, riemannNormAt (g t) p ≤ C) :
    curvatureSup g t ≤ C := by
  apply csSup_le
  · exact Set.range_nonempty (fun p : M => riemannNormAt (g t) p)
  · intro b hb
    rcases hb with ⟨p, rfl⟩
    exact hC p

/-- A supremum bound gives the corresponding pointwise bound.  The bound itself
supplies the `BddAbove` witness required by `le_csSup`; no continuity or
attainment of the supremum is assumed. -/
theorem pointwise_le_of_curvatureSup_le
    {g : ℝ → RiemannianMetric I M} {t C : ℝ}
    (hBdd : BddAbove (Set.range (fun q : M => riemannNormAt (g t) q)))
    (hC : curvatureSup g t ≤ C) (p : M) :
    riemannNormAt (g t) p ≤ C := by
  exact (le_csSup hBdd ⟨p, rfl⟩).trans hC

/-- A uniform bound on the spatial curvature supremum is exactly the pointwise
bound consumed by the singularity-extension infrastructure. -/
theorem hasUniformCurvatureBoundBefore_of_curvatureSup_bound
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Ico (0 : ℝ) T,
      BddAbove (Set.range (fun q : M => riemannNormAt (g t) q)) ∧
        curvatureSup g t ≤ C) :
    HasUniformCurvatureBoundBefore g T := by
  refine ⟨C, hC, ?_⟩
  intro t ht p
  exact pointwise_le_of_curvatureSup_le (hbound t ht).1 (hbound t ht).2 p

/-- **Math.** A uniform pointwise pre-endpoint curvature bound also supplies the
corresponding spatial-supremum bound.  The pointwise estimate itself provides
the `BddAbove` witness, so no separate boundedness hypothesis is needed. -/
theorem curvatureSup_bound_of_hasUniformCurvatureBoundBefore
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hRm : HasUniformCurvatureBoundBefore g T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Ico (0 : ℝ) T,
        BddAbove (Set.range (fun q : M => riemannNormAt (g t) q)) ∧
          curvatureSup g t ≤ C := by
  rcases hRm with ⟨C, hC, hpoint⟩
  refine ⟨C, hC, ?_⟩
  intro t ht
  refine ⟨?_, curvatureSup_le_of_pointwise_bound (hpoint t ht)⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact hpoint t ht p

/-! ## The honest non-blow-up alternative -/

/-- If the spatial curvature supremum does not tend to `+∞` at a positive
endpoint, then it is bounded by one fixed nonnegative constant frequently in
every left-hand neighbourhood of that endpoint.  This is the precise filter
statement available before the local maximum-principle propagation step. -/
theorem exists_frequently_curvatureSup_le_of_not_curvatureBlowsUpAt
    {g : ℝ → RiemannianMetric I M} {T : ℝ} (hT : 0 < T)
    (hnot : ¬ CurvatureBlowsUpAt g T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ᶠ t in 𝓝[Iio T] T, curvatureSup g t ≤ C := by
  let L : Filter ℝ := 𝓝[Iio T] T
  letI : NeBot L := nhdsWithin_Iio_neBot (α := ℝ) (b := T) le_rfl
  have hnot' : ¬ (∀ b : ℝ, ∀ᶠ t in L, b ≤ curvatureSup g t) := by
    intro h
    apply hnot
    exact Filter.tendsto_atTop.2 h
  obtain ⟨b, hb⟩ := not_forall.mp hnot'
  have hfreq : ∃ᶠ t in L, ¬ b ≤ curvatureSup g t :=
    (Filter.not_eventually).mp hb
  refine ⟨max b 0, le_max_right _ _, hfreq.mono ?_⟩
  intro t ht
  exact (le_of_lt (lt_of_not_ge ht)).trans (le_max_left _ _)

/-! ## Neighbourhood form for restart arguments -/

/-- The frequently bounded times can be chosen inside any admissible left-hand
neighbourhood and, because `T > 0`, inside the positive-time interval. -/
theorem exists_curvatureSup_le_in_nhdsWithin_of_not_curvatureBlowsUpAt
    {g : ℝ → RiemannianMetric I M} {T : ℝ} (hT : 0 < T)
    (hnot : ¬ CurvatureBlowsUpAt g T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ U ∈ 𝓝[Iio T] T, ∃ t ∈ U ∩ Ioo (0 : ℝ) T,
        curvatureSup g t ≤ C := by
  obtain ⟨C, hC, hfreq⟩ :=
    exists_frequently_curvatureSup_le_of_not_curvatureBlowsUpAt hT hnot
  refine ⟨C, hC, ?_⟩
  have hpositive : ∀ᶠ t in 𝓝[Iio T] T, t ∈ Ioi (0 : ℝ) := by
    exact (eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds
  intro U hU
  have hU' : ∃ᶠ t in 𝓝[Iio T] T,
      curvatureSup g t ≤ C ∧ t ∈ U ∧ t ∈ Ioo (0 : ℝ) T := by
    refine (hfreq.and_eventually ?_)
    filter_upwards [mem_of_superset hU (fun t ht => ht), hpositive,
      self_mem_nhdsWithin] with t ht hpos hlt
    exact ⟨ht, hpos, hlt⟩
  obtain ⟨t, htC, htU, htIoo⟩ := hU'.exists
  exact ⟨t, ⟨htU, htIoo⟩, htC⟩

#print axioms curvatureSup_le_of_pointwise_bound
#print axioms pointwise_le_of_curvatureSup_le
#print axioms hasUniformCurvatureBoundBefore_of_curvatureSup_bound
#print axioms curvatureSup_bound_of_hasUniformCurvatureBoundBefore
#print axioms exists_frequently_curvatureSup_le_of_not_curvatureBlowsUpAt
#print axioms exists_curvatureSup_le_in_nhdsWithin_of_not_curvatureBlowsUpAt

end Topping

end
