import LeeSmoothLib.Ch05.Sec05_30.Definition_5_30_extra_2
import LeeSmoothLib.Ch06.Sec06_38.Definition_6_38_extra_2
import LeeSmoothLib.Ch06.Sec06_38.Lemma_6_6
import LeeSmoothLib.Ch06.Sec06_39.Theorem_6_10.EuclideanStrictCore
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_2
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.HausdorffDimension

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ContDiff Manifold Topology

-- Domain sampling for this refine pass:
-- * source-facing set: `{y : N | IsCriticalValue I J F y}`;
-- * core/canonical owner: `has_measure_zero_in_manifold`;
-- * bridge/view: `has_measure_zero_in_manifold.extChartAt_volume_eq_zero`.

universe uE uE' uH uH' uM uN

section

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable [MeasurableSpace E'] [BorelSpace E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Helper for Theorem 6.10: a `C¹` map from a lower-dimensional finite-dimensional real vector
space into a higher-dimensional one has additive Haar null range. -/
private theorem measure_zero_range_of_contDiff_of_model_finrank_lt {f : E → E'}
    (hf : ContDiff ℝ 1 f) (μ : Measure E') [μ.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') :
    μ (Set.range f) = 0 := by
  -- First show that the range has Hausdorff dimension strictly smaller than the ambient dimension.
  have hdimRange :
      dimH (Set.range f) < Module.finrank ℝ E' :=
    hf.dimH_range_le.trans_lt <| Nat.cast_lt.2 hdim
  have hhausdorff :
      Measure.hausdorffMeasure (Module.finrank ℝ E' : ℝ) (Set.range f) = 0 := by
    -- The ambient Hausdorff measure vanishes on sets of strictly smaller Hausdorff dimension.
    simpa using hausdorffMeasure_of_dimH_lt hdimRange
  -- Any additive Haar measure on a finite-dimensional real vector space is a scalar multiple of the
  -- canonical Hausdorff measure in top dimension.
  rw [Measure.isAddLeftInvariant_eq_smul μ
      (Measure.hausdorffMeasure (Module.finrank ℝ E' : ℝ))]
  simp [hhausdorff]

/-- Helper for Theorem 6.10: every critical value is, by definition, a value in the range. -/
private theorem criticalValues_subset_range {F : M → N} :
    {y : N | IsCriticalValue I J F y} ⊆ Set.range F := by
  intro y hy
  -- Unpack a critical value into a critical point lying over it.
  rcases (isCriticalValue_iff_exists_critical_point F y).1 hy with
    ⟨p, rfl, -⟩
  exact ⟨p, rfl⟩

/-- Helper for Theorem 6.10: when the source model dimension is strictly smaller than the target
model dimension, every value in the range is critical. -/
private theorem range_subset_criticalValues_of_model_finrank_lt {F : M → N}
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') :
    Set.range F ⊆ {y : N | IsCriticalValue I J F y} := by
  intro y hy
  -- Rewrite a range point as `F p` and invoke the dimension obstruction on surjectivity.
  rcases hy with ⟨p, rfl⟩
  have hcritical : IsCriticalValue I J F (F p) := by
    rw [isCriticalValue_iff_exists_critical_point]
    exact ⟨p, rfl, isCriticalPoint_of_model_finrank_lt hdim p⟩
  exact hcritical

/-- Helper for Theorem 6.10: in the low-dimensional case, the critical values coincide with the
entire range. -/
private theorem criticalValues_eq_range_of_model_finrank_lt {F : M → N}
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') :
    {y : N | IsCriticalValue I J F y} = Set.range F := by
  -- Combine the easy inclusion from the definition with the dimension-forcing converse.
  exact Set.Subset.antisymm criticalValues_subset_range
    (range_subset_criticalValues_of_model_finrank_lt hdim)

/-- Helper for Theorem 6.10: in the low-dimensional case, Sard's theorem reduces to the
measure-zero statement for `Set.range F`. -/
private theorem criticalValues_hasMeasureZero_of_rangeHasMeasureZero {F : M → N}
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E')
    (hRange : has_measure_zero_in_manifold J (Set.range F)) :
    has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
  -- Rewrite the critical-value set as the full range, then reuse the range-nullity input.
  simpa [criticalValues_eq_range_of_model_finrank_lt hdim] using hRange

/-- Helper for Theorem 6.10: for a fixed target chart, the chart image of `Set.range F` has
measure zero when the source model dimension is strictly smaller than the target one. -/
private theorem chartRangeImage_hasMeasureZero_of_model_finrank_lt
    [SecondCountableTopology M] {F : M → N} (hF : ContMDiff I J ∞ F)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E')
    (μ : Measure E') (hμ : μ.IsAddHaarMeasure)
    {e : OpenPartialHomeomorph N H'} (he : e ∈ IsManifold.maximalAtlas J ∞ N) :
    μ (((e.extend J) '' (Set.range F ∩ e.source))) = 0 := by
  classical
  let s : Set M := F ⁻¹' e.source
  let V : s → Set s := fun p ↦ Subtype.val ⁻¹' (extChartAt I p.1).source
  -- Cover the relevant source locus by countably many source-chart domains.
  have hV_nhds : ∀ p : s, V p ∈ nhds p := by
    intro p
    exact preimage_coe_mem_nhds_subtype.2 <|
      mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds p.1)
  obtain ⟨t, ht_countable, ht_cover⟩ := LindelofSpace.elim_nhds_subcover V hV_nhds
  let sourceSet : s → Set M := fun p ↦ (extChartAt I p.1).source ∩ F ⁻¹' e.source
  let sourcePiece : s → Set E := fun p ↦ (extChartAt I p.1) '' sourceSet p
  let rep : s → E → E' := fun p ↦ e.extend J ∘ F ∘ (extChartAt I p.1).symm
  have hpiece_zero : ∀ p ∈ t, μ (rep p '' sourcePiece p) = 0 := by
    intro p hp
    have hsourceSet_open : IsOpen (sourceSet p) := by
      -- The source piece is cut out by the source chart and the open preimage `F ⁻¹' e.source`.
      exact (isOpen_extChartAt_source p.1).inter (e.open_source.preimage hF.continuous)
    have hsource_subset : sourceSet p ⊆ (chartAt H p.1).source := by
      intro x hx
      simpa [sourceSet, Set.mem_inter_iff, extChartAt_source] using hx.1
    have hmapsTo : Set.MapsTo F (sourceSet p) e.source := by
      intro x hx
      exact hx.2
    have hrep_contDiff : ContDiffOn ℝ ∞ (rep p) (sourcePiece p) := by
      -- Rewrite manifold smoothness of `F` into ordinary smoothness on this source chart piece.
      exact
        (contMDiffOn_iff_of_mem_maximalAtlas'
          ((show chartAt H p.1 ∈ IsManifold.maximalAtlas I ∞ M from
              IsManifold.chart_mem_maximalAtlas p.1))
          he hsource_subset hmapsTo).1 <|
          hF.contMDiffOn.mono (Set.subset_univ _)
    have hsourcePiece_eq :
        sourcePiece p = I '' ((chartAt H p.1) '' sourceSet p) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨x, hx, rfl⟩
        exact ⟨chartAt H p.1 x, ⟨x, hx, rfl⟩, rfl⟩
      · intro hz
        rcases hz with ⟨u, ⟨x, hx, hux⟩, huz⟩
        refine ⟨x, hx, ?_⟩
        calc
          (extChartAt I p.1) x = I ((chartAt H p.1) x) := rfl
          _ = I u := by rw [hux]
          _ = z := huz
    have hsourcePiece_subset_range : sourcePiece p ⊆ Set.range I := by
      intro y hy
      rcases hy with ⟨x, -, rfl⟩
      exact ⟨chartAt H p.1 x, rfl⟩
    have hlocLip :
        ∀ x ∈ sourcePiece p,
          ∃ C : NNReal, ∃ t : Set E, t ∈ nhdsWithin x (sourcePiece p) ∧
            LipschitzOnWith C (rep p) t := by
      intro x hx
      rcases hx with ⟨y, hy, hxy⟩
      have hchart_image_open : IsOpen ((chartAt H p.1) '' sourceSet p) := by
        exact
          (chartAt H p.1).isOpen_image_of_subset_source hsourceSet_open
            hsource_subset
      have hsourcePiece_nhds :
          sourcePiece p ∈ nhdsWithin ((extChartAt I p.1) y) (Set.range I) := by
        have hchart_nhds :
            (chartAt H p.1) '' sourceSet p ∈ nhds ((chartAt H p.1) y) := by
          exact hchart_image_open.mem_nhds ⟨y, hy, rfl⟩
        have himage_nhds :
            I '' ((chartAt H p.1) '' sourceSet p) ∈
              nhdsWithin (I ((chartAt H p.1) y)) (Set.range I) :=
          I.image_mem_nhdsWithin hchart_nhds
        rw [hsourcePiece_eq]
        simpa using himage_nhds
      have hrepWithin : ContDiffWithinAt ℝ 1 (rep p) (Set.range I) x := by
        -- Upgrade the chart piece to the convex ambient model range near the current point.
        have hrepWithinSource :
            ContDiffWithinAt ℝ 1 (rep p) (sourcePiece p) ((extChartAt I p.1) y) := by
          exact
            (hrep_contDiff ((extChartAt I p.1) y) ⟨y, hy, rfl⟩).of_le
              (show (1 : ℕ∞ω) ≤ ∞ by simp)
        rw [← hxy]
        exact hrepWithinSource.mono_of_mem_nhdsWithin hsourcePiece_nhds
      obtain ⟨C, u, hu, hLip⟩ := hrepWithin.exists_lipschitzOnWith (I.convex_range)
      have hsourcePiece_nhds' : sourcePiece p ∈ 𝓝[Set.range I] x := by
        rw [← hxy]
        exact hsourcePiece_nhds
      have hrestrict : 𝓝[Set.range I] x = 𝓝[sourcePiece p] x := by
        rw [nhdsWithin_restrict'' (Set.range I) hsourcePiece_nhds']
        congr
        exact Set.inter_eq_right.2 hsourcePiece_subset_range
      have hu' : u ∈ 𝓝[sourcePiece p] x := by
        rw [← hrestrict]
        exact hu
      exact ⟨C, u, hu', hLip⟩
    have hdimImage : dimH (rep p '' sourcePiece p) < Module.finrank ℝ E' := by
      -- Local Lipschitz control bounds the Hausdorff dimension of each chartwise image piece.
      calc
        dimH (rep p '' sourcePiece p) ≤ dimH (sourcePiece p) := by
          exact dimH_image_le_of_locally_lipschitzOn hlocLip
        _ ≤ dimH (Set.range I) := dimH_mono hsourcePiece_subset_range
        _ ≤ Module.finrank ℝ E := by
          rw [← Real.dimH_univ_eq_finrank E]
          exact dimH_mono (Set.subset_univ _)
        _ < Module.finrank ℝ E' := Nat.cast_lt.2 hdim
    have hhausdorff :
        Measure.hausdorffMeasure (Module.finrank ℝ E' : ℝ) (rep p '' sourcePiece p) = 0 := by
      -- Top-dimensional Hausdorff measure vanishes once the Hausdorff dimension is too small.
      simpa using hausdorffMeasure_of_dimH_lt hdimImage
    -- Compare volume to top-dimensional Hausdorff measure on the codomain model space.
    rw [Measure.isAddLeftInvariant_eq_smul μ
      (Measure.hausdorffMeasure (Module.finrank ℝ E' : ℝ))]
    simp [hhausdorff]
  have hsubset :
      (e.extend J) '' (Set.range F ∩ e.source) ⊆ ⋃ p ∈ t, rep p '' sourcePiece p := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy.1 with ⟨x, rfl⟩
    let xs : s := ⟨x, hy.2⟩
    have hxs_cover : xs ∈ ⋃ p ∈ t, V p := by
      rw [ht_cover]
      simp
    rcases Set.mem_iUnion₂.1 hxs_cover with ⟨p, hp, hxp⟩
    have hx_source : x ∈ (extChartAt I p.1).source := by
      simpa [V] using hxp
    refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
    refine ⟨(extChartAt I p.1) x, ?_, ?_⟩
    · refine ⟨x, ?_, rfl⟩
      exact ⟨hx_source, hy.2⟩
    · -- On the chosen chart piece, the representative agrees with the original chart image.
      change (e.extend J) (F ((extChartAt I p.1).symm ((extChartAt I p.1) x))) =
        (e.extend J) (F x)
      rw [(extChartAt I p.1).left_inv hx_source]
  -- The whole target-chart image is a countable union of the null source-chart pieces.
  exact
    measure_mono_null hsubset <|
      (measure_biUnion_null_iff ht_countable).2 hpiece_zero

/-- Helper for Theorem 6.10: when `Module.finrank ℝ E < Module.finrank ℝ E'`, it remains to prove
that the smooth image `Set.range F` has measure zero in `N`. -/
private theorem range_hasMeasureZero_inManifold_of_contMDiff_of_model_finrank_lt {F : M → N}
    [SecondCountableTopology M] (hF : ContMDiff I J ∞ F)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ E') :
    has_measure_zero_in_manifold J (Set.range F) := by
  -- Work directly with the owner definition of manifold measure zero.
  intro μ hμ e he
  exact
    chartRangeImage_hasMeasureZero_of_model_finrank_lt
      hF hdim μ hμ he

/-- Helper for Theorem 6.10: in equal dimensions, postcomposing a chart operator with the inverse
linear equivalence preserves surjectivity. -/
private theorem surjective_coordinateOperator_of_surjective_linearized
    (heq : Module.finrank ℝ E = Module.finrank ℝ E') {A : E →L[ℝ] E'}
    (hA :
      Function.Surjective
        ((ContinuousLinearEquiv.ofFinrankEq heq).symm.toContinuousLinearMap.comp A)) :
    Function.Surjective A := by
  let L : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq heq
  -- Apply surjectivity to the inverse-image of the requested target vector.
  intro z
  obtain ⟨w, hw⟩ := hA (L.symm z)
  refine ⟨w, ?_⟩
  apply L.symm.injective
  simpa [L, ContinuousLinearMap.comp_apply] using hw

/-- Helper for Theorem 6.10: surjectivity of the fixed-chart coordinate operator forces
surjectivity of the manifold derivative. -/
private theorem surjective_mfderiv_of_surjective_coordinateOperator {F : M → N}
    {x₀ x : M} {y₀ : N}
    (hx : x ∈ (extChartAt I x₀).source) (hy : F x ∈ (extChartAt J y₀).source)
    (hA :
      Function.Surjective
        ((mfderiv% (extChartAt J y₀) (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x)))) :
    Function.Surjective (mfderiv I J F x) := by
  -- Solve the target vector in chart coordinates, then cancel the two invertible chart
  -- derivatives on the outside of the coordinate operator.
  intro v
  obtain ⟨w, hw⟩ := hA ((mfderiv% (extChartAt J y₀) (F x)) v)
  refine ⟨(mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x)) w, ?_⟩
  apply (isInvertible_mfderiv_extChartAt hy).injective
  simpa [ContinuousLinearMap.comp_apply] using hw

/-- Helper for Theorem 6.10: a non-surjective endomorphism of a finite-dimensional real vector
space has zero determinant. -/
private theorem det_eq_zero_of_not_surjective_endomorphism {A : E →L[ℝ] E}
    (hA : ¬ Function.Surjective A) : A.det = 0 := by
  -- In finite dimension, non-surjectivity implies non-injectivity, so the kernel is nontrivial.
  have hker : A.ker ≠ ⊥ := by
    intro hker
    apply hA
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (show Module.finrank ℝ E = Module.finrank ℝ E by simp)).1 <|
        LinearMap.ker_eq_bot.1 hker
  simpa [ContinuousLinearMap.det] using
    (LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker

/-- Helper for Theorem 6.10: at a critical point, the equal-dimensional linearized coordinate
operator has zero determinant. -/
private theorem linearizedCoordinateOperator_det_eq_zero_of_isCriticalPoint {F : M → N}
    (heq : Module.finrank ℝ E = Module.finrank ℝ E') {x₀ x : M} {y₀ : N}
    (hx : x ∈ (extChartAt I x₀).source) (hy : F x ∈ (extChartAt J y₀).source)
    (hcrit : IsCriticalPoint I J F x) :
    let L : E' →L[ℝ] E := (ContinuousLinearEquiv.ofFinrankEq heq).symm
    ContinuousLinearMap.det
      (L.comp
        ((mfderiv% (extChartAt J y₀) (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x)))) = 0 := by
  let LEquiv : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq heq
  let L : E' →L[ℝ] E := LEquiv.symm
  let A : E →L[ℝ] E' :=
    (mfderiv% (extChartAt J y₀) (F x)) ∘L
      (mfderiv I J F x) ∘L
      (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
  let B : E →L[ℝ] E := L.comp A
  -- Route correction: isolate the finite-dimensional algebra from the chart derivative
  -- normalization, so the remaining equal-branch work is only the `HasFDerivWithinAt` assembly.
  have hnotSurj : ¬ Function.Surjective B := by
    intro hB
    have hA : Function.Surjective A := by
      exact surjective_coordinateOperator_of_surjective_linearized heq <| by
        simpa [A, B, L, LEquiv] using hB
    have hmfderiv : Function.Surjective (mfderiv I J F x) := by
      exact surjective_mfderiv_of_surjective_coordinateOperator hx hy <| by
        simpa [A] using hA
    exact
      ((isCriticalPoint_iff_not_isRegularPoint F x).1 hcrit) <|
        (isRegularPoint_iff_surjective_mfderiv F x).2 hmfderiv
  -- Apply the endomorphism determinant criterion after the linearization step.
  simpa [A, B, L, LEquiv] using det_eq_zero_of_not_surjective_endomorphism hnotSurj

/-- Helper for Theorem 6.10: a source-chart coordinate in the target comes from a point in the
corresponding chart source. -/
private theorem extChartAt_symm_mem_source_of_mem_target {x₀ : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    (extChartAt I x₀).symm z ∈ (extChartAt I x₀).source := by
  -- Unpack target membership by applying the inverse chart map.
  exact (extChartAt I x₀).map_target hz

/-- Helper for Theorem 6.10: applying a source chart after its inverse returns the original
coordinate point on the target. -/
private theorem extChartAt_apply_symm_of_mem_target {x₀ : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    (extChartAt I x₀) ((extChartAt I x₀).symm z) = z := by
  -- This is the standard right-inverse identity on the chart target.
  exact (extChartAt I x₀).right_inv hz

/-- Helper for Theorem 6.10: on a fixed source-chart piece, the linearized derivative vanishes in
determinant at each critical point. -/
private theorem linearizedDerivative_det_eq_zero_onSourcePiece {F : M → N}
    (heq : Module.finrank ℝ E = Module.finrank ℝ E') {x₀ x : M} {y₀ : N} {s : Set M}
    (hcrit : ∀ x ∈ s, IsCriticalPoint I J F x)
    (hs_source : s ⊆ (extChartAt I x₀).source)
    (hs_target : s ⊆ F ⁻¹' (extChartAt J y₀).source)
    (hx : x ∈ s) :
    ContinuousLinearMap.det
      (((ContinuousLinearEquiv.ofFinrankEq heq).symm : E' →L[ℝ] E).toContinuousLinearMap.comp
        ((mfderiv% (extChartAt J y₀) (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderiv[Set.range I] (extChartAt I x₀).symm ((extChartAt I x₀) x)))) = 0 := by
  -- This is exactly the previously isolated critical-point determinant criterion.
  exact
    linearizedCoordinateOperator_det_eq_zero_of_isCriticalPoint
      heq (hs_source hx) (hs_target hx) (hcrit x hx)

/-- Helper for Theorem 6.10: the fixed-chart coordinate representative has the expected ordinary
derivative on `Set.range I`. -/
private theorem coordinateRepresentative_hasFDerivWithinAt {F : M → N}
    (hF : ContMDiff I J ∞ F) {x₀ x : M} {y₀ : N}
    (hx : x ∈ (extChartAt I x₀).source) (hy : F x ∈ (extChartAt J y₀).source) :
    HasFDerivWithinAt
      (extChartAt J y₀ ∘ F ∘ (extChartAt I x₀).symm)
      ((mfderiv% (extChartAt J y₀) (F x)) ∘L
        (mfderiv I J F x) ∘L
        (mfderiv[Set.range I] (extChartAt I x₀).symm ((extChartAt I x₀) x)))
      (Set.range I) ((extChartAt I x₀) x) := by
  let φ := extChartAt I x₀
  let ψ := extChartAt J y₀
  have hφleft : (extChartAt I x₀).symm ((extChartAt I x₀) x) = x := by
    -- Normalize the source chart inverse on the chosen source-chart point once and for all.
    exact (extChartAt I x₀).left_inv hx
  have hx_target : φ x ∈ φ.target := by
    -- The source-chart point is inside the chart target by the chart self-map property.
    simpa [φ] using (extChartAt I x₀).map_source hx
  have hφdiff :
      MDifferentiableWithinAt 𝓘(ℝ, E) I φ.symm (Set.range I) (φ x) := by
    -- The preferred chart inverse is differentiable on the model-range chart target.
    simpa [φ] using mdifferentiableWithinAt_extChartAt_symm hx_target
  have hFdiff :
      MDifferentiableAt I J F x := by
    -- Smoothness of `F` gives the manifold derivative at the chosen point.
    exact hF.contMDiffAt.mdifferentiableAt (by simp)
  have hFdiff' :
      HasMFDerivAt I J F (φ.symm (φ x)) (mfderiv I J F x) := by
    -- Rewrite the base point so the chain rule sees the source chart inverse literally.
    rw [show φ.symm (φ x) = x by simpa [φ] using hφleft]
    exact hFdiff.hasMFDerivAt
  have hy_chart : F x ∈ (chartAt H' y₀).source := by
    -- `mdifferentiableAt_extChartAt` is stated with `chartAt`, so rewrite the source condition.
    simpa [extChartAt_source] using hy
  have hψdiff :
      MDifferentiableAt J 𝓘(ℝ, E') ψ (F x) := by
    -- The preferred target chart is differentiable on its source.
    simpa [ψ] using mdifferentiableAt_extChartAt hy_chart
  have hψdiff' :
      HasMFDerivAt J 𝓘(ℝ, E') ψ (F (φ.symm (φ x))) (mfderiv% ψ (F x)) := by
    -- Normalize the target base point along the source chart inverse.
    rw [show F (φ.symm (φ x)) = F x by simpa [φ] using congrArg F hφleft]
    exact hψdiff.hasMFDerivAt
  have hFcomp :
      HasMFDerivWithinAt 𝓘(ℝ, E) J (F ∘ φ.symm) (Set.range I) (φ x)
        ((mfderiv I J F x) ∘L (mfderiv[Set.range I] φ.symm (φ x))) := by
    -- First compose `F` with the preferred source chart inverse.
    exact hFdiff'.comp_hasMFDerivWithinAt (φ x) hφdiff.hasMFDerivWithinAt
  have hcoord :
      HasMFDerivWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E') (ψ ∘ F ∘ φ.symm) (Set.range I) (φ x)
        ((mfderiv% ψ (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderiv[Set.range I] φ.symm (φ x))) := by
    -- Route correction: normalize the chart representative before any later linearization.
    simpa [Function.comp] using hψdiff'.comp_hasMFDerivWithinAt (φ x) hFcomp
  -- Convert the manifold derivative of the coordinate representative to the ordinary one.
  simpa [φ, ψ] using hcoord.hasFDerivWithinAt

/-- Helper for Theorem 6.10: the equal-dimensional fixed-chart representative has the expected
linearized derivative on `Set.range I`. -/
private theorem linearizedCoordinateRepresentative_hasFDerivWithinAt {F : M → N}
    (hF : ContMDiff I J ∞ F) (heq : Module.finrank ℝ E = Module.finrank ℝ E') {x₀ x : M}
    {y₀ : N} (hx : x ∈ (extChartAt I x₀).source) (hy : F x ∈ (extChartAt J y₀).source) :
    let L : E' →L[ℝ] E := (ContinuousLinearEquiv.ofFinrankEq heq).symm
    HasFDerivWithinAt
      ((L : E' → E) ∘ extChartAt J y₀ ∘ F ∘ (extChartAt I x₀).symm)
      (L.comp
        ((mfderiv% (extChartAt J y₀) (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderiv[Set.range I] (extChartAt I x₀).symm ((extChartAt I x₀) x))))
      (Set.range I) ((extChartAt I x₀) x) := by
  let φ := extChartAt I x₀
  let ψ := extChartAt J y₀
  let LEquiv : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq heq
  let L : E' →L[ℝ] E := LEquiv.symm
  have hφleft : (extChartAt I x₀).symm ((extChartAt I x₀) x) = x := by
    -- Normalize the source chart inverse on the chosen source-chart point once and for all.
    exact (extChartAt I x₀).left_inv hx
  have hcoordF :
      HasFDerivWithinAt (ψ ∘ F ∘ φ.symm)
        ((mfderiv% ψ (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderiv[Set.range I] φ.symm (φ x)))
        (Set.range I) (φ x) := by
    -- Reuse the standalone coordinate representative derivative before linearizing the codomain.
    simpa [φ, ψ] using
      coordinateRepresentative_hasFDerivWithinAt hF hx hy
  have hL :
      HasFDerivAt ((L : E' → E)) L ((ψ ∘ F ∘ φ.symm) (φ x)) := by
    -- Postcomposition by the inverse linear equivalence is an ordinary linear derivative step.
    exact L.hasFDerivAt
  -- Finish by postcomposing the chart representative with the inverse linear equivalence.
  simpa [φ, ψ, L, LEquiv, Function.comp, ContinuousLinearMap.comp_apply, hφleft] using
    hL.comp_hasFDerivWithinAt (φ x) hcoordF

/-- Helper for Theorem 6.10: a manifold critical point maps to a non-surjective ordinary
coordinate derivative for the fixed-chart representative. -/
private theorem coordinateRepresentative_not_surjective_of_isCriticalPoint {F : M → N}
    (hF : ContMDiff I J ∞ F) {x₀ x : M} {y₀ : N}
    (hx : x ∈ (extChartAt I x₀).source) (hy : F x ∈ (extChartAt J y₀).source)
    (hcrit : IsCriticalPoint I J F x) :
    ¬ Function.Surjective
      (fderivWithin ℝ (extChartAt J y₀ ∘ F ∘ (extChartAt I x₀).symm)
        (Set.range I) ((extChartAt I x₀) x)) := by
  let φ := extChartAt I x₀
  let ψ := extChartAt J y₀
  have hmem : φ x ∈ Set.range I := by
    -- The preferred source-chart image always lies in the model range.
    exact ⟨chartAt H x₀ x, rfl⟩
  have hcoord :=
    coordinateRepresentative_hasFDerivWithinAt
      hF hx hy
  let _ : T2Space (TangentSpace 𝓘(ℝ, E') (ψ (F x))) := by
    change T2Space E'
    infer_instance
  have hformula :
      fderivWithin ℝ (ψ ∘ F ∘ φ.symm) (Set.range I) (φ x) =
        ((mfderiv% ψ (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderiv[Set.range I] φ.symm (φ x))) := by
    -- Identify the ordinary within-derivative with the already normalized coordinate operator.
    symm
    exact
      (I.uniqueDiffOn.uniqueDiffWithinAt hmem).eq
        hcoord hcoord.differentiableWithinAt.hasFDerivWithinAt
  intro hsurj
  have hcoordSurj :
      Function.Surjective
        ((mfderiv% ψ (F x)) ∘L
          (mfderiv I J F x) ∘L
          (mfderiv[Set.range I] φ.symm (φ x))) := by
    -- Rewrite the surjectivity hypothesis into the manifold-coordinate operator spelling.
    rw [← hformula]
    exact hsurj
  have hmfderiv : Function.Surjective (mfderiv I J F x) :=
    surjective_mfderiv_of_surjective_coordinateOperator
      hx hy hcoordSurj
  -- A critical point cannot have surjective manifold derivative.
  exact
    ((isCriticalPoint_iff_not_isRegularPoint F x).1 hcrit) <|
      (isRegularPoint_iff_surjective_mfderiv F x).2 hmfderiv

/-- Helper for Theorem 6.10: zero measure transports back across a continuous linear equivalence
from the pushed-forward additive Haar measure. -/
private theorem measure_zero_of_linearEquiv_preimage (L : E ≃L[ℝ] E') (μ : Measure E')
    {s : Set E'} (hs : (μ.map L.symm) (L.symm '' s) = 0) :
    μ s = 0 := by
  let eHomeo : E' ≃ₜ E := L.symm.toHomeomorph
  let e : E' ≃ᵐ E := eHomeo.toMeasurableEquiv
  -- Evaluate the pushed-forward measure on the image set using the measurable equivalence formula.
  rw [show (μ.map L.symm) (L.symm '' s) = (μ.map e) (e '' s) by rfl] at hs
  rw [e.map_apply] at hs
  simpa using hs

/-- Helper for Theorem 6.10: one fixed source-chart critical piece has additive Haar-null image
under a fixed target-chart representative in the equal-dimensional case. -/
private theorem chartPieceImage_measure_zero_of_model_finrank_eq {F : M → N}
    (hF : ContMDiff I J ∞ F) (heq : Module.finrank ℝ E = Module.finrank ℝ E')
    (μ : Measure E') [μ.IsAddHaarMeasure] {y₀ : N} {s : Set M} (p : s)
    (hs_crit : ∀ x ∈ s, IsCriticalPoint I J F x)
    (hs_target : s ⊆ F ⁻¹' (extChartAt J y₀).source) :
    let L : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq heq
    let μE : Measure E := Measure.map L.symm μ
    let φ := extChartAt I p.1
    let ψ := extChartAt J y₀
    let sourceSet : Set M := s ∩ φ.source
    let sourcePiece : Set E := φ '' sourceSet
    let rep : E → E' := ψ ∘ F ∘ φ.symm
    let linearizedRep : E → E := L.symm ∘ rep
    μ (rep '' sourcePiece) = 0 := by
  classical
  let L : E ≃L[ℝ] E' := ContinuousLinearEquiv.ofFinrankEq heq
  let LMap : E' →L[ℝ] E := L.symm
  let μE : Measure E := Measure.map L.symm μ
  let φ := extChartAt I p.1
  let ψ := extChartAt J y₀
  let sourceSet : Set M := s ∩ φ.source
  let sourcePiece : Set E := φ '' sourceSet
  let rep : E → E' := ψ ∘ F ∘ φ.symm
  let linearizedRep : E → E := L.symm ∘ rep
  let linearizedDeriv : E → E →L[ℝ] E := fun z ↦
    LMap.comp
      ((mfderiv% ψ (F (φ.symm z))) ∘L
        (mfderiv I J F (φ.symm z)) ∘L
        (mfderiv[Set.range I] φ.symm z))
  have hsourceSet_crit : ∀ x ∈ sourceSet, IsCriticalPoint I J F x := by
    intro x hx
    exact hs_crit x hx.1
  have hsourceSet_source : sourceSet ⊆ φ.source := by
    intro x hx
    exact hx.2
  have hsourceSet_target : sourceSet ⊆ F ⁻¹' ψ.source := by
    intro x hx
    exact hs_target hx.1
  have hsourcePiece_subset_range : sourcePiece ⊆ Set.range I := by
    intro z hz
    rcases hz with ⟨x, -, rfl⟩
    exact ⟨chartAt H p.1 x, rfl⟩
  have hlinearized_deriv :
      ∀ z ∈ sourcePiece, HasFDerivWithinAt linearizedRep (linearizedDeriv z) sourcePiece z := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hφleft : (extChartAt I p.1).symm ((extChartAt I p.1) x) = x := by
      -- Collapse the chart inverse on the concrete source-point representative of this chart piece.
      exact (extChartAt I p.1).left_inv hx.2
    have hformula :
        linearizedDeriv (φ x) =
          LMap.comp
            ((mfderiv% ψ (F x)) ∘L
              (mfderiv I J F x) ∘L
              (mfderiv[Set.range I] φ.symm (φ x))) := by
      -- Normalize the source chart inverse in the derivative formula itself.
      simpa [linearizedDeriv] using
        congrArg
          (fun u : M ↦
            LMap.comp
              ((mfderiv% ψ (F u)) ∘L
                (mfderiv I J F u) ∘L
                (mfderiv[Set.range I] φ.symm (φ x))))
          hφleft
    have hbridge :=
      linearizedCoordinateRepresentative_hasFDerivWithinAt
        hF heq hx.2 (hs_target hx.1)
    -- Restrict the chart derivative from `Set.range I` to the actual critical chart piece.
    have hbridge' :
        HasFDerivWithinAt linearizedRep
          (LMap.comp
            ((mfderiv% ψ (F x)) ∘L
              (mfderiv I J F x) ∘L
              (mfderiv[Set.range I] φ.symm (φ x))))
          sourcePiece (φ x) := by
      simpa [linearizedRep, rep, φ, ψ, L, LMap, Function.comp, hφleft] using
        hbridge.mono hsourcePiece_subset_range
    exact hbridge'.congr_fderiv hformula.symm
  have hlinearized_det :
      ∀ z ∈ sourcePiece, (linearizedDeriv z).det = 0 := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hφleft : (extChartAt I p.1).symm ((extChartAt I p.1) x) = x := by
      -- Use the same chart-inverse normalization before reading off the determinant criterion.
      exact (extChartAt I p.1).left_inv hx.2
    have hformula :
        linearizedDeriv (φ x) =
          LMap.comp
            ((mfderiv% ψ (F x)) ∘L
              (mfderiv I J F x) ∘L
              (mfderiv[Set.range I] φ.symm (φ x))) := by
      -- Normalize the source chart inverse in the determinant formula as well.
      simpa [linearizedDeriv] using
        congrArg
          (fun u : M ↦
            LMap.comp
              ((mfderiv% ψ (F u)) ∘L
                (mfderiv I J F u) ∘L
                (mfderiv[Set.range I] φ.symm (φ x))))
          hφleft
    -- The determinant vanishes because every point in the source piece is critical.
    rw [hformula]
    simpa [φ, ψ, L, LMap] using
      linearizedDerivative_det_eq_zero_onSourcePiece
        heq hsourceSet_crit hsourceSet_source hsourceSet_target hx
  have hlinearized_zero : μE (linearizedRep '' sourcePiece) = 0 := by
    -- Apply the equal-dimensional Jacobian null-image theorem to the linearized chart map.
    exact
      MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μE
        hlinearized_deriv hlinearized_det
  have hpreimage :
      L.symm '' (rep '' sourcePiece) = linearizedRep '' sourcePiece := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨w, hw, hzw⟩
      rcases hw with ⟨u, hu, rfl⟩
      refine ⟨u, hu, ?_⟩
      simpa [linearizedRep, rep, Function.comp] using hzw
    · intro hz
      rcases hz with ⟨u, hu, hzu⟩
      refine ⟨rep u, ⟨u, hu, rfl⟩, ?_⟩
      simpa [linearizedRep, rep, Function.comp] using hzu
  -- Transport the zero statement back across the inverse linear equivalence.
  have htransport : (μ.map L.symm) (L.symm '' (rep '' sourcePiece)) = 0 := by
    -- Rewrite the transported image into the linearized one before applying the measure bridge.
    rw [hpreimage]
    exact hlinearized_zero
  exact measure_zero_of_linearEquiv_preimage L μ htransport

/-- Helper for Theorem 6.10: in the equal model-dimension case, each preferred target-chart image
of the critical values has measure zero. -/
private theorem chartCriticalValues_hasMeasureZero_of_model_finrank_eq
    [SecondCountableTopology M] {F : M → N} (hF : ContMDiff I J ∞ F)
    (heq : Module.finrank ℝ E = Module.finrank ℝ E') (μ : Measure E') [μ.IsAddHaarMeasure]
    (y₀ : N) :
    μ ((extChartAt J y₀) '' ({y : N | IsCriticalValue I J F y} ∩ (extChartAt J y₀).source)) = 0 := by
  classical
  let ψ := extChartAt J y₀
  let s : Set M := {x : M | IsCriticalPoint I J F x ∧ F x ∈ ψ.source}
  let V : s → Set s := fun p ↦ Subtype.val ⁻¹' (extChartAt I p.1).source
  -- Cover the critical preimage of the preferred target chart by countably many source charts.
  have hV_nhds : ∀ p : s, V p ∈ nhds p := by
    intro p
    exact preimage_coe_mem_nhds_subtype.2 <|
      mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds p.1)
  obtain ⟨t, ht_countable, ht_cover⟩ := LindelofSpace.elim_nhds_subcover V hV_nhds
  let sourceSet : s → Set M := fun p ↦ s ∩ (extChartAt I p.1).source
  let sourcePiece : s → Set E := fun p ↦ (extChartAt I p.1) '' sourceSet p
  let rep : s → E → E' := fun p ↦ ψ ∘ F ∘ (extChartAt I p.1).symm
  have hs_crit : ∀ x ∈ s, IsCriticalPoint I J F x := by
    intro x hx
    exact hx.1
  have hs_target : s ⊆ F ⁻¹' ψ.source := by
    intro x hx
    exact hx.2
  have hpiece_zero : ∀ p ∈ t, μ (rep p '' sourcePiece p) = 0 := by
    intro p hp
    -- Reuse the standalone chart-piece nullity theorem instead of rebuilding the Jacobian proof.
    simpa [sourceSet, sourcePiece, rep, ψ] using
      chartPieceImage_measure_zero_of_model_finrank_eq hF heq μ p hs_crit hs_target
  have hsubset :
      ψ '' ({y : N | IsCriticalValue I J F y} ∩ ψ.source) ⊆ ⋃ p ∈ t, rep p '' sourcePiece p := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases (isCriticalValue_iff_exists_critical_point F y).1 hy.1 with ⟨x, rfl, hcrit⟩
    let xs : s := ⟨x, ⟨hcrit, hy.2⟩⟩
    have hxs_cover : xs ∈ ⋃ p ∈ t, V p := by
      rw [ht_cover]
      simp
    rcases Set.mem_iUnion₂.1 hxs_cover with ⟨p, hp, hxp⟩
    have hx_source : x ∈ (extChartAt I p.1).source := by
      simpa [V] using hxp
    refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
    refine ⟨(extChartAt I p.1) x, ?_, ?_⟩
    · refine ⟨x, ?_, rfl⟩
      exact ⟨xs.2, hx_source⟩
    · -- On each chosen chart piece, the representative agrees with the original target chart map.
      change ψ (F ((extChartAt I p.1).symm ((extChartAt I p.1) x))) = ψ (F x)
      rw [(extChartAt I p.1).left_inv hx_source]
  -- The preferred target-chart image is contained in a countable union of null source-chart pieces.
  exact
    measure_mono_null hsubset <|
      (measure_biUnion_null_iff ht_countable).2 hpiece_zero

/-- Helper for Theorem 6.10: the equal-dimension Sard branch is obtained by reducing to the
preferred-chart cover furnished by Lemma 6.6. -/
private theorem criticalValues_hasMeasureZero_of_model_finrank_eq {F : M → N}
    [SecondCountableTopology M] (hF : ContMDiff I J ∞ F)
    (heq : Module.finrank ℝ E = Module.finrank ℝ E') :
    has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
  intro μ hμ e he
  let _ : MeasureSpace E' := ⟨μ⟩
  let _ : (volume : Measure E').IsAddHaarMeasure := by
    simpa using hμ
  -- Upgrade the preferred-chart nullity statement to the manifold owner by covering the critical
  -- values with their own preferred target charts.
  have howner :
      has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
    refine
      has_measure_zero_in_manifold_of_chart_cover (fun y : N ↦ chartAt H' y) ?_ ?_ ?_
    · -- Each preferred chart belongs to the maximal atlas.
      intro y
      exact
        (show chartAt H' y ∈ IsManifold.maximalAtlas J ∞ N from
          IsManifold.chart_mem_maximalAtlas y)
    · -- Every critical value lies in the source of its own preferred chart.
      intro y hy
      exact Set.mem_iUnion.2 ⟨y, mem_chart_source H' y⟩
    · -- Apply the chartwise equal-dimension theorem on each preferred target chart.
      intro y
      simpa using
        chartCriticalValues_hasMeasureZero_of_model_finrank_eq hF heq volume y
  exact howner μ hμ e he

/-- Helper for Theorem 6.10: one fixed source-chart critical piece in the strict target-dimension
branch should be reduced to the Euclidean Sard core for the coordinate representative. -/
private theorem sourcePiece_subset_coordinateCriticalSet {F : M → N}
    (hF : ContMDiff I J ∞ F) {y₀ : N} {s : Set M} (p : s)
    (hs_crit : ∀ x ∈ s, IsCriticalPoint I J F x)
    (hs_target : s ⊆ F ⁻¹' (extChartAt J y₀).source) :
    let φ := extChartAt I p.1
    let ψ := extChartAt J y₀
    let sourceSet : Set M := s ∩ φ.source
    let sourcePiece : Set E := φ '' sourceSet
    let rep : E → E' := ψ ∘ F ∘ φ.symm
    sourcePiece ⊆
      {z ∈ Set.range I |
        ¬ Function.Surjective (fderivWithin ℝ rep (Set.range I) z)} := by
  let φ := extChartAt I p.1
  let ψ := extChartAt J y₀
  let sourceSet : Set M := s ∩ φ.source
  let sourcePiece : Set E := φ '' sourceSet
  let rep : E → E' := ψ ∘ F ∘ φ.symm
  -- Unfold the local abbreviations before introducing a point of the source piece.
  dsimp [sourcePiece, sourceSet, rep, φ, ψ]
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · -- Every point of the chosen source piece still lies in the ambient model range.
    exact ⟨chartAt H p.1 x, rfl⟩
  · -- Push manifold criticality to non-surjectivity of the coordinate derivative.
    simpa [rep, φ, ψ] using
      coordinateRepresentative_not_surjective_of_isCriticalPoint
        hF hx.2 (hs_target hx.1) (hs_crit x hx.1)

/-- Helper for Theorem 6.10: Euclidean Sard on an explicit marked subset should be stated in the
local `fderivWithin` form needed by the strict chart branch. -/
private theorem image_measure_zero_of_lindelof_nullNeighborhoods
    {f : E → E'} (μ : Measure E') {s : Set E}
    (hlocal : ∀ x ∈ s, ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0) :
    μ (f '' s) = 0 := by
  classical
  let u : s → Set E := fun x ↦ Classical.choose (hlocal x.1 x.2)
  let V : s → Set s := fun x ↦ Subtype.val ⁻¹' u x
  have hu_nhds : ∀ x : s, u x ∈ nhdsWithin x.1 s := by
    intro x
    -- Record the chosen source neighborhood as a neighborhood in the ambient source set.
    exact (Classical.choose_spec (hlocal x.1 x.2)).1
  have hu_zero : ∀ x : s, μ (f '' u x) = 0 := by
    intro x
    -- Record the chosen null-image statement on the same neighborhood.
    exact (Classical.choose_spec (hlocal x.1 x.2)).2
  have hV_nhds : ∀ x : s, V x ∈ nhds x := by
    intro x
    -- Convert the ambient within-neighborhood into an actual neighborhood in the subtype.
    exact preimage_coe_mem_nhds_subtype.2 (hu_nhds x)
  obtain ⟨t, ht_countable, ht_cover⟩ := LindelofSpace.elim_nhds_subcover V hV_nhds
  have hsubset : f '' s ⊆ ⋃ x ∈ t, f '' u x := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    let xs : s := ⟨x, hx⟩
    have hxs_cover : xs ∈ ⋃ p ∈ t, V p := by
      rw [ht_cover]
      simp
    rcases Set.mem_iUnion₂.1 hxs_cover with ⟨p, hp, hxp⟩
    refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
    refine ⟨x, ?_, rfl⟩
    -- Membership in the chosen subtype neighborhood says exactly that the source point lies in it.
    simpa [V] using hxp
  -- Assemble the pointwise null-image neighborhoods into a countable union.
  exact
    measure_mono_null hsubset <|
      (measure_biUnion_null_iff ht_countable).2 fun x hx ↦ hu_zero x

/-- Helper for Theorem 6.10: if the target space is subsingleton, every continuous linear map into
it is surjective. -/
private theorem surjective_continuousLinearMap_of_subsingletonTarget {A : E →L[ℝ] E'}
    [Subsingleton E'] :
    Function.Surjective A := by
  -- Any target vector equals the image of `0`, because all target points coincide.
  intro y
  refine ⟨0, ?_⟩
  exact Subsingleton.elim _ _

/-- Helper for Theorem 6.10: pointwise `C^∞`-smoothness on the marked subset supplies the explicit
within-derivative data needed by Jacobian-style image estimates. -/
private theorem hasFDerivWithinAt_of_contDiffWithinAt_on_markedSubset
    {t s : Set E} {f : E → E'}
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f t x) :
    ∀ x ∈ s, HasFDerivWithinAt f (fderivWithin ℝ f t x) t x := by
  intro x hx
  -- Downgrade smoothness to differentiability, then read off the canonical within-derivative.
  exact
    ((hsmooth x hx).differentiableWithinAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasFDerivWithinAt

/-- Helper for Theorem 6.10: postcomposing a linear map with a codomain linear equivalence
preserves the surjectivity failure used in the strict Euclidean Sard branch. -/
private theorem not_surjective_comp_codomainLinearEquiv_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E' ≃L[ℝ] F) {A : E →L[ℝ] E'} :
    ¬ Function.Surjective (L.toContinuousLinearMap.comp A) ↔ ¬ Function.Surjective A := by
  constructor
  · intro hcomp hA
    -- A surjective original map stays surjective after composition with a surjective codomain
    -- equivalence, contradicting the transported rank-drop hypothesis.
    exact hcomp (L.surjective.comp hA)
  · intro hA hcomp
    -- Recover surjectivity of the original map by solving the transported equation at `L y` and
    -- cancelling the codomain equivalence.
    apply hA
    intro y
    rcases hcomp (L y) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact L.injective hx

/-- Helper for Theorem 6.10: precomposing a linear map with a domain linear equivalence preserves
surjectivity failure. -/
private theorem not_surjective_comp_domainLinearEquiv_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F ≃L[ℝ] E) {A : E →L[ℝ] E'} :
    ¬ Function.Surjective (A.comp L.toContinuousLinearMap) ↔ ¬ Function.Surjective A := by
  constructor
  · intro hcomp hA
    -- A surjective original map stays surjective after precomposing with a surjective domain
    -- equivalence.
    exact hcomp (hA.comp L.surjective)
  · intro hA hcomp
    -- Any witness for the precomposed map gives a witness for the original map after applying the
    -- domain equivalence.
    apply hA
    intro y
    rcases hcomp y with ⟨x, hx⟩
    exact ⟨L x, hx⟩

/-- Helper for Theorem 6.10: conjugating a linear map by domain and codomain linear equivalences
preserves the surjectivity failure used in the strict Euclidean transport step. -/
private theorem not_surjective_conj_linearEquiv_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Ldom : F ≃L[ℝ] E) (Lcod : E' ≃L[ℝ] G) {A : E →L[ℝ] E'} :
    ¬ Function.Surjective
        (Lcod.toContinuousLinearMap.comp (A.comp Ldom.toContinuousLinearMap)) ↔
      ¬ Function.Surjective A := by
  constructor
  · intro hconj hA
    -- A surjective original map stays surjective after both transport equivalences.
    exact hconj <| Lcod.surjective.comp <| hA.comp Ldom.surjective
  · intro hA hconj
    -- Any witness for the transported map gives a witness for the original map after canceling
    -- both linear equivalences.
    apply hA
    intro y
    rcases hconj (Lcod y) with ⟨x, hx⟩
    exact ⟨Ldom x, Lcod.injective hx⟩

/-- Helper for Theorem 6.10: conjugating a marked-subset map by domain and codomain continuous
linear equivalences transports `fderivWithin` by the expected composition formula. -/
private theorem fderivWithin_conjContinuousLinearEquiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Ldom : F ≃L[ℝ] E) (Lcod : E' ≃L[ℝ] G) {s : Set E} {f : E → E'} {x : F}
    (hxs : UniqueDiffWithinAt ℝ (Ldom ⁻¹' s) x) :
    fderivWithin ℝ (Lcod ∘ f ∘ Ldom) (Ldom ⁻¹' s) x =
      Lcod.toContinuousLinearMap.comp
        ((fderivWithin ℝ f s (Ldom x)).comp Ldom.toContinuousLinearMap) := by
  -- First transport the derivative across the codomain equivalence, then across the domain
  -- equivalence. This keeps the strict-branch rank-drop proof in one spelling world.
  simpa [Function.comp] using
    (show fderivWithin ℝ (Lcod ∘ (f ∘ Ldom)) (Ldom ⁻¹' s) x =
        Lcod.toContinuousLinearMap.comp
          ((fderivWithin ℝ f s (Ldom x)).comp Ldom.toContinuousLinearMap) by
      rw [ContinuousLinearEquiv.comp_fderivWithin Lcod hxs]
      rw [Ldom.comp_right_fderivWithin hxs])

/-- Helper for Theorem 6.10: the transported `fderivWithin` in finite coordinates has
surjectivity failure exactly when the original marked-subset derivative does. -/
private theorem notSurjective_fderivWithin_conjContinuousLinearEquiv_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Ldom : F ≃L[ℝ] E) (Lcod : E' ≃L[ℝ] G) {s : Set E} {f : E → E'} {x : F}
    (hxs : UniqueDiffWithinAt ℝ (Ldom ⁻¹' s) x) :
    ¬ Function.Surjective
        (fderivWithin ℝ (Lcod ∘ f ∘ Ldom) (Ldom ⁻¹' s) x) ↔
      ¬ Function.Surjective (fderivWithin ℝ f s (Ldom x)) := by
  -- Rewrite the transported derivative to the explicit conjugation form, then reuse the linear
  -- algebra transport lemma already isolated above.
  rw [fderivWithin_conjContinuousLinearEquiv Ldom Lcod hxs]
  exact not_surjective_conj_linearEquiv_iff Ldom Lcod

/-- Helper for Theorem 6.10: an ambient neighborhood inside `t` whose marked-subset image is null
restricts to a null-image neighborhood inside the marked subset `s`. -/
private theorem exists_nullImageNeighborhood_within_markedSubset
    {t s : Set E} {f : E → E'} (μ : Measure E') (hst : s ⊆ t) {x : E} (hx : x ∈ s)
    {u : Set E} (hu : u ∈ nhdsWithin x t) (hzero : μ (f '' (u ∩ s)) = 0) :
    ∃ v ∈ nhdsWithin x s, μ (f '' v) = 0 := by
  refine ⟨u ∩ s, ?_, ?_⟩
  · -- Intersect the ambient neighborhood with the marked subset to get a within-neighborhood of
    -- `x` inside `s`.
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hu with ⟨w, hw, hwsub⟩
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
    refine ⟨w, hw, ?_⟩
    intro y hy
    refine ⟨?_, hy.2⟩
    apply hwsub
    exact ⟨hy.1, hst hy.2⟩
  · -- The chosen neighborhood already has exactly the marked-subset image whose nullity was
    -- produced by the ambient argument.
    simpa using hzero

/-- Helper for Theorem 6.10: to prove pointwise null neighborhoods inside `s`, it suffices to
build them first inside the ambient set `t`. -/
private theorem localNullImageNeighborhood_of_ambientInterNullImageNeighborhood
    {t s : Set E} {f : E → E'} (μ : Measure E') (hst : s ⊆ t)
    (hambient : ∀ x ∈ s, ∃ u ∈ nhdsWithin x t, μ (f '' (u ∩ s)) = 0) :
    ∀ x ∈ s, ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0 := by
  intro x hx
  rcases hambient x hx with ⟨u, hu, hzero⟩
  -- Shrink the ambient neighborhood returned by the Euclidean argument back to the marked set
  -- using the exact marked-subset image statement.
  exact exists_nullImageNeighborhood_within_markedSubset μ hst hx hu hzero

/-- Helper for Theorem 6.10: on a closed ball inside the model range, the strict Euclidean Sard
core should show that the image of the marked critical piece has additive Haar measure zero. -/
private theorem closedBallPiece_subset_modelRange
    {s : Set E} {x₀ : E} {r : ℝ} (hst : s ⊆ Set.range I) :
    s ∩ Metric.closedBall x₀ r ⊆ Set.range I := by
  intro x hx
  -- Restricting to the closed ball does not change the ambient model-range membership.
  exact hst hx.1

/-- Helper for Theorem 6.10: the pointwise smoothness hypothesis restricts unchanged to the
closed-ball piece used in the compact Euclidean Sard core. -/
private theorem contDiffWithinAt_on_closedBallPiece
    {s : Set E} {f : E → E'} {x₀ : E} {r : ℝ}
    (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range I) x) :
    ∀ x ∈ s ∩ Metric.closedBall x₀ r, ContDiffWithinAt ℝ ∞ f (Set.range I) x := by
  intro x hx
  -- The compact-ball theorem only needs the original smoothness hypothesis on the smaller piece.
  exact hsmooth x hx.1

/-- Helper for Theorem 6.10: the rank-drop hypothesis also restricts unchanged to the compact
closed-ball piece used by the Euclidean Sard core. -/
private theorem not_surjective_fderivWithin_on_closedBallPiece
    {s : Set E} {f : E → E'} {x₀ : E} {r : ℝ}
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)) :
    ∀ x ∈ s ∩ Metric.closedBall x₀ r,
      ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x) := by
  intro x hx
  -- The compact-ball theorem uses the same pointwise non-surjectivity on the restricted source.
  exact hcrit x hx.1

/-- Helper for Theorem 6.10: adjoining a nontrivial zero complement to the codomain and then
transporting back along a continuous linear equivalence produces an endomorphism with zero
determinant. -/
private theorem det_eq_zero_of_zeroComplementLift
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
    (e : E ≃L[ℝ] (E' × F)) (A : E →L[ℝ] E') :
    ContinuousLinearMap.det
      ((e.symm : E' × F →L[ℝ] E).toContinuousLinearMap.comp
        ((ContinuousLinearMap.inl ℝ E' F).comp A)) = 0 := by
  let B : E →L[ℝ] E :=
    (e.symm : E' × F →L[ℝ] E).toContinuousLinearMap.comp
      ((ContinuousLinearMap.inl ℝ E' F).comp A)
  have hnot : ¬ Function.Surjective B := by
    intro hB
    rcases exists_ne (0 : F) with ⟨z, hz⟩
    rcases hB (e.symm (0, z)) with ⟨x, hx⟩
    have hpair : (A x, (0 : F)) = (0, z) := by
      -- Apply the codomain equivalence once so the zero complement becomes visible.
      have hcongr := congrArg e hx
      simpa [B] using hcongr
    have : z = 0 := by
      -- The second coordinate of the lifted map is forced to vanish identically.
      simpa using (congrArg Prod.snd hpair).symm
    exact hz this
  have hker : B.ker ≠ ⊥ := by
    -- In finite dimension, a non-surjective endomorphism has nontrivial kernel.
    intro hker
    apply hnot
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (show Module.finrank ℝ E = Module.finrank ℝ E by simp)).1 <|
        LinearMap.ker_eq_bot.1 hker
  -- Convert the kernel obstruction into the determinant vanishing statement.
  simpa [B, ContinuousLinearMap.det] using
    (LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker

/-- Helper for Theorem 6.10: a positive local Hölder exponent on a subset of
`EuclideanSpace ℝ (Fin m)` forces additive Haar-null image once the resulting Hausdorff-dimension
bound lies strictly below the target Euclidean dimension. -/
private theorem measure_zero_image_of_locallyHolderOn_of_finrank_div_lt
    {m n : ℕ} {s : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.IsAddHaarMeasure]
    {r : NNReal} (hr : 0 < r)
    (hholder :
      ∀ x ∈ s, ∃ C : NNReal, ∃ t ∈ nhdsWithin x s, HolderOnWith C r f t)
    (hdim :
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ENNReal) / r <
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :
    μ (f '' s) = 0 := by
  have hsourceDim :
      dimH s ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := by
    -- The marked source sits in the ambient `m`-dimensional Euclidean model space.
    rw [← Real.dimH_univ_eq_finrank (EuclideanSpace ℝ (Fin m))]
    exact dimH_mono (Set.subset_univ _)
  have hdimImage :
      dimH (f '' s) < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    -- Route correction: record the generic local Hölder dimension drop once, so Step 3 only has
    -- to provide the neighborhood-level Hölder estimate.
    calc
      dimH (f '' s) ≤ dimH s / r :=
        dimH_image_le_of_locally_holder_on hr hholder
      _ ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ENNReal) / r := by
        simpa using ENNReal.div_le_div_right hsourceDim r
      _ < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := hdim
  have hhausdorff :
      Measure.hausdorffMeasure
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) (f '' s) = 0 := by
    -- Top-dimensional Hausdorff measure vanishes once the image dimension is too small.
    simpa using hausdorffMeasure_of_dimH_lt hdimImage
  -- Compare additive Haar measure to the canonical top-dimensional Hausdorff measure.
  rw [Measure.isAddLeftInvariant_eq_smul μ
    (Measure.hausdorffMeasure (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ))]
  rw [Measure.smul_apply, hhausdorff]
  simp

/-- Helper for Theorem 6.10: once the target Euclidean dimension is positive, the Step 3 Hölder
exponent `m + 1` forces the Hausdorff-dimension ratio `m / (m + 1)` to lie below the target
dimension. -/
private theorem finrankDivSucc_lt_targetFinrank_of_ne_zero
    {m n : ℕ} (hn : n ≠ 0) :
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) : ENNReal) / (m + 1 : NNReal) <
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
  have hratio_lt_one :
      ((m : ENNReal) / (m + 1 : NNReal)) < 1 := by
    -- Rewrite the ratio and compare `m` with `m + 1`.
    rw [ENNReal.div_lt_iff
      (Or.inl (by exact_mod_cast Nat.succ_ne_zero m))
      (Or.inl (by simp))]
    simpa [Nat.succ_eq_add_one, one_mul] using
      (show (m : ENNReal) < m + 1 by exact_mod_cast Nat.lt_succ_self m)
  have hone_le_target :
      (1 : ENNReal) ≤ n := by
    -- A positive target dimension is at least `1`.
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
  -- Combine the universal ratio bound with positivity of the target dimension.
  simpa using hratio_lt_one.trans_le hone_le_target

/-- Helper for Theorem 6.10: if the target model space has finrank `0`, then pointwise rank drop
forces the marked subset to be empty, so its image has additive Haar measure zero. -/
private theorem image_measureZero_of_zeroTargetFinrank_rankDrop
    {s : Set E} {f : E → E'} (μ : Measure E') [μ.IsAddHaarMeasure]
    (hzero : Module.finrank ℝ E' = 0)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)) :
    μ (f '' s) = 0 := by
  letI : Subsingleton E' := (Module.finrank_zero_iff.mp hzero)
  have hs_empty : s = ∅ := by
    ext x
    constructor
    · intro hx
      -- In a subsingleton target every within-derivative is surjective, contradicting rank drop.
      exact
        (hcrit x hx <|
          (surjective_continuousLinearMap_of_subsingletonTarget :
            Function.Surjective (fderivWithin ℝ f (Set.range I) x))).elim
    · simp
  -- Once the marked subset is empty, its image is empty as well.
  simp [hs_empty]

/-- Helper for Theorem 6.10: Lee's first branch begins on the marked locus where the
`within`-derivative is already nonzero. This coordinate-free shell is the generic owner-side
version of the eventual Step 1 witness piece. -/
private def firstOrderNonvanishingPiece
    (s : Set E) (f : E → E') : Set E :=
  {x | x ∈ s ∧ fderivWithin ℝ f (Set.range I) x ≠ 0}

/-- Helper for Theorem 6.10: Lee's first vanishing-order piece is the marked locus where the
first `within`-derivative vanishes. -/
private def criticalVanishingPieceOne
    (s : Set E) (f : E → E') : Set E :=
  {x | x ∈ s ∧ fderivWithin ℝ f (Set.range I) x = 0}

/-- Helper for Theorem 6.10: membership in the nonvanishing first-derivative piece is exactly the
source membership together with nonzero `within`-derivative. -/
private theorem mem_firstOrderNonvanishingPiece_iff
    {s : Set E} {f : E → E'} {x : E} :
    x ∈ firstOrderNonvanishingPiece (I := I) s f ↔
      x ∈ s ∧ fderivWithin ℝ f (Set.range I) x ≠ 0 := by
  -- The Step 1 shell is defined by adjoining first-derivative nonvanishing to source membership.
  rfl

/-- Helper for Theorem 6.10: membership in the first vanishing-order piece is exactly the source
membership together with vanishing `within`-derivative. -/
private theorem mem_criticalVanishingPieceOne_iff
    {s : Set E} {f : E → E'} {x : E} :
    x ∈ criticalVanishingPieceOne (I := I) s f ↔
      x ∈ s ∧ fderivWithin ℝ f (Set.range I) x = 0 := by
  -- This is just the definition of the first vanishing-order piece.
  rfl

/-- Helper for Theorem 6.10: every marked point lies either in the generic Step 1 shell or in the
first vanishing-order piece `C₁`. -/
private theorem markedSubset_subset_firstOrderNonvanishingPiece_union_criticalVanishingPieceOne
    {s : Set E} {f : E → E'} :
    s ⊆
      firstOrderNonvanishingPiece (I := I) s f ∪
        criticalVanishingPieceOne (I := I) s f := by
  intro x hx
  -- Split on whether the first `within`-derivative at `x` already vanishes.
  by_cases hderiv : fderivWithin ℝ f (Set.range I) x = 0
  · exact Or.inr <| (mem_criticalVanishingPieceOne_iff (I := I)).2 ⟨hx, hderiv⟩
  · exact Or.inl <| (mem_firstOrderNonvanishingPiece_iff (I := I)).2 ⟨hx, hderiv⟩

/-- Helper for Theorem 6.10: Lee's Step 2 branch is recorded by a scalar function whose zero set
contains the marked source locally and whose `within`-derivative is nonzero at the marked point. -/
private structure HigherOrderScalarWitness
    (s : Set E) (f : E → E') (x : E) where
  order : ℕ
  scalar : E → ℝ
  contDiff : ContDiffWithinAt ℝ ∞ scalar (Set.range I) x
  zero_at : scalar x = 0
  deriv_nonzero : fderivWithin ℝ scalar (Set.range I) x ≠ 0
  zero_on_source : ∃ u ∈ nhdsWithin x s, ∀ y ∈ u, scalar y = 0

/-- Helper for Theorem 6.10: the Step 2 witness piece consists of marked points carrying a chosen
higher-order scalar witness. -/
private def higherOrderWitnessPiece
    (s : Set E) (f : E → E') : Set E :=
  {x | x ∈ s ∧ Nonempty (HigherOrderScalarWitness (I := I) s f x)}

/-- Helper for Theorem 6.10: the residual Step 3 shell consists of marked points where the first
`within`-derivative vanishes and no higher-order witness has been chosen. -/
private def deepVanishingRemainderPiece
    (s : Set E) (f : E → E') : Set E :=
  {x | x ∈ s ∧
      fderivWithin ℝ f (Set.range I) x = 0 ∧
      ¬ Nonempty (HigherOrderScalarWitness (I := I) s f x)}

/-- Helper for Theorem 6.10: the Step 2 witness piece is a genuine subset of the marked source. -/
private theorem higherOrderWitnessPiece_subset
    {s : Set E} {f : E → E'} :
    higherOrderWitnessPiece (I := I) s f ⊆ s := by
  intro x hx
  -- The Step 2 shell is defined by adjoining witness data to source membership.
  exact hx.1

/-- Helper for Theorem 6.10: the residual Step 3 shell is also a genuine subset of the marked
source. -/
private theorem deepVanishingRemainderPiece_subset
    {s : Set E} {f : E → E'} :
    deepVanishingRemainderPiece (I := I) s f ⊆ s := by
  intro x hx
  -- The residual shell keeps the original source membership as its first component.
  exact hx.1

/-- Helper for Theorem 6.10: points in the residual Step 3 shell still satisfy the vanishing
first-derivative condition. -/
private theorem deepVanishingRemainderPiece_fderivWithin_eq_zero
    {s : Set E} {f : E → E'} {x : E}
    (hx : x ∈ deepVanishingRemainderPiece (I := I) s f) :
    fderivWithin ℝ f (Set.range I) x = 0 := by
  -- This is the derivative half of the residual shell definition.
  exact hx.2.1

/-- Helper for Theorem 6.10: points in the residual Step 3 shell carry no chosen higher-order
scalar witness. -/
private theorem deepVanishingRemainderPiece_noHigherOrderWitness
    {s : Set E} {f : E → E'} {x : E}
    (hx : x ∈ deepVanishingRemainderPiece (I := I) s f) :
    ¬ Nonempty (HigherOrderScalarWitness (I := I) s f x) := by
  -- This is the witness-absence half of the residual shell definition.
  exact hx.2.2

/-- Helper for Theorem 6.10: the residual Step 3 shell packages both the vanishing derivative and
the absence of any chosen higher-order witness. -/
private theorem deepVanishingRemainderPiece_data
    {s : Set E} {f : E → E'} {x : E}
    (hx : x ∈ deepVanishingRemainderPiece (I := I) s f) :
    fderivWithin ℝ f (Set.range I) x = 0 ∧
      ¬ Nonempty (HigherOrderScalarWitness (I := I) s f x) := by
  -- Bundle the residual data once so later Step 3 closures can consume one stable fact.
  exact
    ⟨deepVanishingRemainderPiece_fderivWithin_eq_zero (I := I) hx,
      deepVanishingRemainderPiece_noHigherOrderWitness (I := I) hx⟩

/-- Helper for Theorem 6.10: inside Lee's first vanishing-order piece `C₁`, the current shell
splits a point into the Step 2 higher-order witness branch or the residual Step 3 branch. -/
private theorem
    criticalVanishingPieceOne_subset_higherOrderWitnessPiece_union_deepVanishingRemainderPiece
    {s : Set E} {f : E → E'} :
    criticalVanishingPieceOne (I := I) s f ⊆
      higherOrderWitnessPiece (I := I) s f ∪
        deepVanishingRemainderPiece (I := I) s f := by
  intro x hx
  rcases (mem_criticalVanishingPieceOne_iff (I := I)).1 hx with ⟨hsx, hderiv⟩
  -- Route correction: once the first derivative vanishes, the honest next split is by whether a
  -- higher-order witness has already been chosen at `x`.
  by_cases hhigher : Nonempty (HigherOrderScalarWitness (I := I) s f x)
  · exact Or.inl ⟨hsx, hhigher⟩
  · exact Or.inr ⟨hsx, hderiv, hhigher⟩

/-- Helper for Theorem 6.10: every marked point lies either in the generic Step 1 shell, the Step
2 higher-order witness shell, or the residual Step 3 shell. -/
private theorem witnessPieces_cover
    {s : Set E} {f : E → E'} :
    s ⊆
      firstOrderNonvanishingPiece (I := I) s f ∪
        higherOrderWitnessPiece (I := I) s f ∪
          deepVanishingRemainderPiece (I := I) s f := by
  intro x hx
  -- First split off the nonvanishing first-derivative branch, then subdivide the vanishing
  -- branch by witness existence.
  rcases
      markedSubset_subset_firstOrderNonvanishingPiece_union_criticalVanishingPieceOne
        (I := I) (s := s) (f := f) hx with hfirst | hcrit
  · exact Or.inl <| Or.inl hfirst
  · rcases
      criticalVanishingPieceOne_subset_higherOrderWitnessPiece_union_deepVanishingRemainderPiece
        (I := I) (s := s) (f := f) hcrit with hhigher | hdeep
    · exact Or.inl <| Or.inr hhigher
    · exact Or.inr hdeep

/-- Helper for Theorem 6.10: once the three Lee witness branches provide null-image neighborhoods,
the branchwise data upgrades to the single local-null hypothesis consumed by Lindelof. -/
private theorem localNullNeighborhoods_of_witnessPieceLocalNullity
    {s : Set E} {f : E → E'} (μ : Measure E')
    (hfirst :
      ∀ x ∈ firstOrderNonvanishingPiece (I := I) s f,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0)
    (hhigher :
      ∀ x ∈ higherOrderWitnessPiece (I := I) s f,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0)
    (hdeep :
      ∀ x ∈ deepVanishingRemainderPiece (I := I) s f,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0) :
    ∀ x ∈ s, ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0 := by
  intro x hx
  -- Dispatch the marked point to the local-null theorem for the branch supplied by the witness
  -- trichotomy.
  rcases witnessPieces_cover (I := I) (s := s) (f := f) hx with hfront | hdeepx
  · rcases hfront with hfirstx | hhigherx
    · exact hfirst x hfirstx
    · exact hhigher x hhigherx
  · exact hdeep x hdeepx

/-- Helper for Theorem 6.10: the strict marked-subset owner reduces to the three Lee witness
branches once their local null-image statements are available. -/
private theorem image_measure_zero_of_witnessPieceLocalNullity
    {s : Set E} {f : E → E'} (μ : Measure E') [μ.IsAddHaarMeasure]
    (hfirst :
      ∀ x ∈ firstOrderNonvanishingPiece (I := I) s f,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0)
    (hhigher :
      ∀ x ∈ higherOrderWitnessPiece (I := I) s f,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0)
    (hdeep :
      ∀ x ∈ deepVanishingRemainderPiece (I := I) s f,
        ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0) :
    μ (f '' s) = 0 := by
  -- Package the branchwise local-null conclusions into the generic Lindelof assembly already
  -- available in this owner file.
  exact
    image_measure_zero_of_lindelof_nullNeighborhoods (f := f) μ <|
      localNullNeighborhoods_of_witnessPieceLocalNullity
        (I := I) (s := s) (f := f) μ hfirst hhigher hdeep

/-- Helper for Theorem 6.10: on a closed ball inside the model range, the strict Euclidean Sard
owner should imply the corresponding null-image statement on the restricted closed-ball piece. -/
private theorem euclideanCriticalImage_measureZero_of_modelRangeMarkedSubset
    {s : Set E} {f : E → E'} (μ : Measure E') [μ.IsAddHaarMeasure]
    (hst : s ⊆ Set.range I) (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range I) x)
    (hlt : Module.finrank ℝ E' < Module.finrank ℝ E)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)) :
    μ (f '' s) = 0 := by
  by_cases hzero : Module.finrank ℝ E' = 0
  · -- Eliminate the zero-dimensional target case locally before invoking the imported strict core.
    exact image_measureZero_of_zeroTargetFinrank_rankDrop μ hzero hcrit
  -- Route correction: the strict Euclidean induction has to live on an arbitrary marked subset of
  -- `Set.range I`; the closed-ball theorem below is only a restriction wrapper used by local
  -- neighborhood arguments, so the Lee Step 1/2/3 frontier is delegated to the theorem-local
  -- support file.
  exact
    euclideanCriticalImage_measureZero_of_modelRangeMarkedSubset_strictCore
      μ hst hsmooth hlt hcrit

/-- Helper for Theorem 6.10: on a closed ball inside the model range, the strict Euclidean Sard
core should show that the image of the marked critical piece has additive Haar measure zero. -/
private theorem euclideanCriticalImage_measureZero_onClosedBallPiece
    {s : Set E} {f : E → E'} (μ : Measure E') [μ.IsAddHaarMeasure] {x₀ : E} {r : ℝ}
    (hst : s ⊆ Set.range I) (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range I) x)
    (hlt : Module.finrank ℝ E' < Module.finrank ℝ E)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)) :
    μ (f '' (s ∩ Metric.closedBall x₀ r)) = 0 := by
  -- Route correction: the closed-ball theorem is only a restriction wrapper around the marked-
  -- subset owner, so all compact-piece bookkeeping should be discharged before the owner call.
  have hpiece_subset :
      s ∩ Metric.closedBall x₀ r ⊆ Set.range I :=
    closedBallPiece_subset_modelRange hst
  have hpiece_smooth :
      ∀ x ∈ s ∩ Metric.closedBall x₀ r, ContDiffWithinAt ℝ ∞ f (Set.range I) x :=
    contDiffWithinAt_on_closedBallPiece hsmooth
  have hpiece_rankDrop :
      ∀ x ∈ s ∩ Metric.closedBall x₀ r,
        ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x) :=
    not_surjective_fderivWithin_on_closedBallPiece hcrit
  -- Apply the marked-subset owner to the restricted source piece cut out by the closed ball.
  exact
    euclideanCriticalImage_measureZero_of_modelRangeMarkedSubset
      μ hpiece_subset hpiece_smooth hlt hpiece_rankDrop

/-- Helper for Theorem 6.10: once the Euclidean Sard core is specialized to `Set.range I`, each
point of the marked critical set gets a null-image neighborhood inside that marked set. -/
private theorem localNullImageNeighborhood_of_rankDrop
    {s : Set E} {f : E → E'} (μ : Measure E') [μ.IsAddHaarMeasure]
    (hst : s ⊆ Set.range I) (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range I) x)
    (hlt : Module.finrank ℝ E' < Module.finrank ℝ E)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)) :
    ∀ x ∈ s, ∃ u ∈ nhdsWithin x s, μ (f '' u) = 0 := by
  intro x hx
  let u : Set E := Metric.ball x 1 ∩ s
  have hu_nhds : u ∈ nhdsWithin x s := by
    -- Use a genuine metric ball in the ambient Euclidean space, then restrict it back to `s`.
    rw [Metric.mem_nhdsWithin_iff]
    exact ⟨1, zero_lt_one, by intro y hy; exact hy⟩
  have hu_subset : u ⊆ s ∩ Metric.closedBall x 1 := by
    intro y hy
    refine ⟨hy.2, ?_⟩
    exact Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.1 hy.1))
  have hclosed_zero : μ (f '' (s ∩ Metric.closedBall x 1)) = 0 := by
    -- Invoke the compact-ball Euclidean Sard core on the closed ball centered at the current point.
    exact
      euclideanCriticalImage_measureZero_onClosedBallPiece
        μ hst hsmooth hlt hcrit
  refine ⟨u, hu_nhds, ?_⟩
  -- The open-ball neighborhood image is a subset of the closed-ball image handled above.
  exact measure_mono_null (Set.image_mono hu_subset) hclosed_zero

/-- Helper for Theorem 6.10: the strict-dimension Euclidean Sard core on the model range is a
global image-nullity statement on a marked subset of the source. -/
private theorem strictEuclideanCriticalImage_measureZero_of_rankDrop
    {s : Set E} {f : E → E'} (μ : Measure E') [μ.IsAddHaarMeasure]
    (hst : s ⊆ Set.range I) (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range I) x)
    (hlt : Module.finrank ℝ E' < Module.finrank ℝ E)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)) :
    μ (f '' s) = 0 := by
  -- Route correction: the arbitrary marked-subset owner is now the strict Euclidean frontier, so
  -- this theorem is just the compatibility wrapper consumed by the chart-piece reduction.
  exact
    euclideanCriticalImage_measureZero_of_modelRangeMarkedSubset
      μ hst hsmooth hlt hcrit

/-- Helper for Theorem 6.10: Euclidean Sard on an explicit marked subset of `Set.range I` is
stated in the local `fderivWithin` form needed by the strict chart branch. -/
private theorem euclideanCriticalValues_measure_zero_of_contDiffWithinAt_subset
    {s : Set E} {f : E → E'} (μ : Measure E') [μ.IsAddHaarMeasure]
    (hst : s ⊆ Set.range I) (hsmooth : ∀ x ∈ s, ContDiffWithinAt ℝ ∞ f (Set.range I) x)
    (hlt : Module.finrank ℝ E' < Module.finrank ℝ E)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)) :
    μ (f '' s) = 0 := by
  -- Route correction: the strict branch now uses the global Euclidean core directly, so the
  -- Lindelof assembly is no longer the proof frontier.
  exact
    strictEuclideanCriticalImage_measureZero_of_rankDrop
      μ hst hsmooth hlt hcrit

/-- Helper for Theorem 6.10: one fixed source-chart critical piece in the strict target-dimension
branch is reduced to a Euclidean Sard theorem on the coordinate representative. -/
private theorem chartPieceImage_measure_zero_of_targetFinrank_lt_sourceFinrank {F : M → N}
    (hF : ContMDiff I J ∞ F) (hlt : Module.finrank ℝ E' < Module.finrank ℝ E)
    (μ : Measure E') [μ.IsAddHaarMeasure] {y₀ : N} {s : Set M} (p : s)
    (hs_crit : ∀ x ∈ s, IsCriticalPoint I J F x)
    (hs_target : s ⊆ F ⁻¹' (extChartAt J y₀).source) :
    let φ := extChartAt I p.1
    let ψ := extChartAt J y₀
    let sourceSet : Set M := s ∩ φ.source
    let sourcePiece : Set E := φ '' sourceSet
    let rep : E → E' := ψ ∘ F ∘ φ.symm
    μ (rep '' sourcePiece) = 0 := by
  let φ := extChartAt I p.1
  let ψ := extChartAt J y₀
  let sourceSet : Set M := s ∩ φ.source
  let sourcePiece : Set E := φ '' sourceSet
  let rep : E → E' := ψ ∘ F ∘ φ.symm
  have hcoordinateCritical :
      sourcePiece ⊆
        {z ∈ Set.range I | ¬ Function.Surjective (fderivWithin ℝ rep (Set.range I) z)} := by
    -- First move the whole chart piece into the ambient coordinate critical locus.
    simpa [φ, ψ, sourceSet, sourcePiece, rep] using
      sourcePiece_subset_coordinateCriticalSet hF p hs_crit hs_target
  have hsourcePiece_subset_range : sourcePiece ⊆ Set.range I := by
    -- The Euclidean core uses the ambient model range as the within-set.
    intro z hz
    exact (hcoordinateCritical hz).1
  have hsmooth :
      ∀ z ∈ sourcePiece, ContDiffWithinAt ℝ ∞ rep (Set.range I) z := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hx_chart : x ∈ (chartAt H p.1).source := by
      -- Rewrite the preferred source-chart membership into the `chartAt` spelling expected by
      -- the coordinate smoothness criterion.
      simpa [φ, extChartAt_source] using hx.2
    have hy_chart : F x ∈ (chartAt H' y₀).source := by
      -- The target-chart membership comes from the fixed preferred target chart on `s`.
      simpa [ψ, extChartAt_source] using hs_target hx.1
    rcases
        (contMDiffAt_iff_of_mem_source
          hx_chart hy_chart).1 (hF x) with
      ⟨-, hcoordSmooth⟩
    -- Route correction: take pointwise coordinate smoothness from `ContMDiffAt` first, then feed
    -- the Euclidean core only the local within-chart statement it actually needs.
    simpa [rep, φ, ψ] using hcoordSmooth
  have hrankDrop :
      ∀ z ∈ sourcePiece, ¬ Function.Surjective (fderivWithin ℝ rep (Set.range I) z) := by
    -- The bridge lemma already packaged the non-surjectivity conclusion on the whole chart piece.
    intro z hz
    exact (hcoordinateCritical hz).2
  -- Apply the Euclidean strict-dimension Sard core to the fixed coordinate representative.
  exact
    euclideanCriticalValues_measure_zero_of_contDiffWithinAt_subset
      μ hsourcePiece_subset_range hsmooth hlt hrankDrop

/-- Helper for Theorem 6.10: in the strict target-dimension case, each preferred target-chart image
of the critical values should be reduced to the Euclidean Sard core on a coordinate representative.
-/
private theorem chartCriticalValues_hasMeasureZero_of_targetFinrank_lt_sourceFinrank
    [SecondCountableTopology M] {F : M → N} (hF : ContMDiff I J ∞ F)
    (hlt : Module.finrank ℝ E' < Module.finrank ℝ E) (μ : Measure E') [μ.IsAddHaarMeasure]
    (y₀ : N) :
    μ
      ((extChartAt J y₀) ''
        ({y : N | IsCriticalValue I J F y} ∩ (extChartAt J y₀).source)) = 0 := by
  classical
  let ψ := extChartAt J y₀
  let s : Set M := {x : M | IsCriticalPoint I J F x ∧ F x ∈ ψ.source}
  let V : s → Set s := fun p ↦ Subtype.val ⁻¹' (extChartAt I p.1).source
  -- Reuse the equal-branch source-chart cover verbatim; only the per-piece nullity theorem changes.
  have hV_nhds : ∀ p : s, V p ∈ nhds p := by
    intro p
    exact preimage_coe_mem_nhds_subtype.2 <|
      mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds p.1)
  obtain ⟨t, ht_countable, ht_cover⟩ := LindelofSpace.elim_nhds_subcover V hV_nhds
  let sourceSet : s → Set M := fun p ↦ s ∩ (extChartAt I p.1).source
  let sourcePiece : s → Set E := fun p ↦ (extChartAt I p.1) '' sourceSet p
  let rep : s → E → E' := fun p ↦ ψ ∘ F ∘ (extChartAt I p.1).symm
  have hs_crit : ∀ x ∈ s, IsCriticalPoint I J F x := by
    intro x hx
    exact hx.1
  have hs_target : s ⊆ F ⁻¹' ψ.source := by
    intro x hx
    exact hx.2
  have hpiece_zero : ∀ p ∈ t, μ (rep p '' sourcePiece p) = 0 := by
    intro p hp
    -- The strict branch now waits only on the per-piece Euclidean Sard theorem.
    simpa [sourceSet, sourcePiece, rep, ψ] using
      chartPieceImage_measure_zero_of_targetFinrank_lt_sourceFinrank
        hF hlt μ p hs_crit hs_target
  have hsubset :
      ψ '' ({y : N | IsCriticalValue I J F y} ∩ ψ.source) ⊆ ⋃ p ∈ t, rep p '' sourcePiece p := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases (isCriticalValue_iff_exists_critical_point F y).1 hy.1 with ⟨x, rfl, hcrit⟩
    let xs : s := ⟨x, ⟨hcrit, hy.2⟩⟩
    have hxs_cover : xs ∈ ⋃ p ∈ t, V p := by
      rw [ht_cover]
      simp
    rcases Set.mem_iUnion₂.1 hxs_cover with ⟨p, hp, hxp⟩
    have hx_source : x ∈ (extChartAt I p.1).source := by
      simpa [V] using hxp
    refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
    refine ⟨(extChartAt I p.1) x, ?_, ?_⟩
    · refine ⟨x, ?_, rfl⟩
      exact ⟨xs.2, hx_source⟩
    · -- On each chosen chart piece, the representative agrees with the original target chart map.
      change ψ (F ((extChartAt I p.1).symm ((extChartAt I p.1) x))) = ψ (F x)
      rw [(extChartAt I p.1).left_inv hx_source]
  -- The strict branch now has the same countable-union closing argument as the equal branch.
  exact
    measure_mono_null hsubset <|
      (measure_biUnion_null_iff ht_countable).2 hpiece_zero

/-- Helper for Theorem 6.10: the strict target-dimension branch is reduced to the corresponding
chartwise Euclidean Sard statement. -/
private theorem criticalValues_hasMeasureZero_of_targetFinrank_lt_sourceFinrank {F : M → N}
    [SecondCountableTopology M] (hF : ContMDiff I J ∞ F)
    (hlt : Module.finrank ℝ E' < Module.finrank ℝ E) :
    has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
  intro μ hμ e he
  let _ : MeasureSpace E' := ⟨μ⟩
  let _ : (volume : Measure E').IsAddHaarMeasure := by
    simpa using hμ
  -- Route correction: use the preferred-chart cover owner, so the strict branch matches the
  -- equal-dimensional assembly shape and the Euclidean core only has to prove the preferred-chart
  -- volume statement.
  have howner :
      has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
    refine
      has_measure_zero_in_manifold_of_chart_cover (fun y : N ↦ chartAt H' y) ?_ ?_ ?_
    · intro y
      exact
        (show chartAt H' y ∈ IsManifold.maximalAtlas J ∞ N from
          IsManifold.chart_mem_maximalAtlas y)
    · intro y hy
      exact Set.mem_iUnion.2 ⟨y, mem_chart_source H' y⟩
    · intro y
      simpa using
        chartCriticalValues_hasMeasureZero_of_targetFinrank_lt_sourceFinrank
          hF hlt volume y
  exact howner μ hμ e he

/-- Helper for Theorem 6.10: once the low-dimensional range case is removed, the complementary
dimension regime is an immediate split between the equal-dimension Jacobian branch and the strict
target-dimension Sard branch. -/
private theorem criticalValues_hasMeasureZero_of_targetFinrank_le_sourceFinrank {F : M → N}
    [SecondCountableTopology M] (hF : ContMDiff I J ∞ F)
    (hle : Module.finrank ℝ E' ≤ Module.finrank ℝ E) :
    has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
  -- Split the remaining work by whether the model dimensions are equal or strictly ordered.
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · -- The equal-dimension case is the fixed-dimension Jacobian branch.
    exact criticalValues_hasMeasureZero_of_model_finrank_eq hF heq.symm
  · -- The strict target-dimension case is the genuine Euclidean Sard branch.
    exact criticalValues_hasMeasureZero_of_targetFinrank_lt_sourceFinrank hF hlt

/-- Generic model-space bridge for Sard's theorem. The source-facing Theorem 6.10 for Lee
manifolds with or without boundary is stated below via `SmoothManifoldWithBoundary`. -/
theorem critical_values_has_measure_zero_in_manifold_of_contMDiff {F : M → N}
    [T2Space M] [SecondCountableTopology M] [T2Space N] [SecondCountableTopology N]
    (hF : ContMDiff I J ∞ F) :
    has_measure_zero_in_manifold J {y : N | IsCriticalValue I J F y} := by
  -- Route correction: split first by the model-dimension relation, because the low-dimensional
  -- branch collapses immediately to range-nullity while the complementary branch is genuine Sard.
  by_cases hdim : Module.finrank ℝ E < Module.finrank ℝ E'
  · -- Reduce the low-dimensional branch to the already isolated range-nullity statement.
    exact
      criticalValues_hasMeasureZero_of_rangeHasMeasureZero hdim
        (range_hasMeasureZero_inManifold_of_contMDiff_of_model_finrank_lt hF hdim)
  · -- The complementary branch is exactly the chartwise Euclidean Sard frontier.
    exact
      criticalValues_hasMeasureZero_of_targetFinrank_le_sourceFinrank
        hF (Nat.le_of_not_gt hdim)

end

section

open Manifold

-- Verified local owner/API: `SmoothManifoldWithBoundary n` packages the canonical
-- `IsManifold (leeBoundaryModelWithCorners n) ∞` structure used throughout the repo for Lee's
-- "with or without boundary" statements.
variable {m n : ℕ}
variable {M : Type uM} [TopologicalSpace M] [SmoothManifoldWithBoundary m M]
variable {N : Type uN} [TopologicalSpace N] [SmoothManifoldWithBoundary n N]

/-- Theorem 6.10 (Sard's Theorem): if `F : M → N` is a smooth map between smooth manifolds with
or without boundary, then the set of critical values of `F` has measure zero in `N`. -/
theorem critical_values_has_measure_zero_in_manifold_of_contMDiff_smoothManifoldWithBoundary
    {F : M → N}
    (hF :
      ContMDiff (leeBoundaryModelWithCorners m) (leeBoundaryModelWithCorners n) ∞ F) :
    has_measure_zero_in_manifold
      (leeBoundaryModelWithCorners n)
      {y : N |
        IsCriticalValue (leeBoundaryModelWithCorners m) (leeBoundaryModelWithCorners n) F y} :=
  by
    -- Specialize the generic model-space Sard theorem to Lee's boundary models.
    simpa using
      (critical_values_has_measure_zero_in_manifold_of_contMDiff hF)

end

section

open Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable [MeasureSpace E'] [BorelSpace E'] [(volume : Measure E').IsAddHaarMeasure]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Preferred-chart bridge theorem derived from the generic model-space Sard owner
`critical_values_has_measure_zero_in_manifold_of_contMDiff`. -/
theorem critical_values_volume_extChartAt_eq_zero_of_contMDiff {F : M → N}
    [T2Space M] [SecondCountableTopology M] [T2Space N] [SecondCountableTopology N]
    (hF : ContMDiff I J ∞ F) (x : N) :
    volume ((extChartAt J x) '' ({y : N | IsCriticalValue I J F y} ∩ (extChartAt J x).source)) =
      0 := by
  exact
    has_measure_zero_in_manifold.extChartAt_volume_eq_zero
      J (critical_values_has_measure_zero_in_manifold_of_contMDiff hF) x

end
