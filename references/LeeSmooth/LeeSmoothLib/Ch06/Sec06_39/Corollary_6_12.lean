import LeeSmoothLib.Ch06.Sec06_39.Corollary_6_11
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open MeasureTheory
open scoped ContDiff Manifold

-- Domain sampling for this refine pass checked the Section 6.38 owner
-- `has_measure_zero_in_manifold`, Corollary 6.11's canonical reformulation on that owner, and
-- the chapter's owner-level `Manifold.IsImmersion.contMDiff` bridge.
-- Semantic search note: `lean_leansearch` surfaced the subtype-immersion API around `Subtype.val`,
-- and this file keeps the source-facing subset formulation on that owner.

universe uE uE' uH uH' uM

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M]
variable {S : Set M} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  [T2Space S] [SecondCountableTopology S]

/-- Corollary 6.12: if `S ⊆ M` is an immersed submanifold of a smooth manifold with or without
boundary and the model-space dimension of `S` is strictly smaller than that of `M`, then `S` has
measure zero in `M`. -/
theorem range_has_measure_zero_in_manifold_of_immersion_of_model_finrank_lt
    (hS : IsImmersion J I ∞ (Subtype.val : S → M))
    (hdim : Module.finrank ℝ E' < Module.finrank ℝ E) :
    has_measure_zero_in_manifold I S := by
  -- Reuse Corollary 6.11 for the inclusion `Subtype.val : S → M`.
  -- The immersion hypothesis supplies the required smoothness of the inclusion.
  simpa [Subtype.range_coe] using
    range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt
      (I := J) (J := I) (F := Subtype.val) hS.contMDiff hdim

end

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M]
variable {S : Set M} [TopologicalSpace S] [ChartedSpace H' S] [IsManifold J ∞ S]
  [T2Space S] [SecondCountableTopology S]

/-- Preferred-chart formulation of the immersed-submanifold measure-zero theorem. -/
theorem range_has_measure_zero_in_manifold_of_immersion_of_model_finrank_lt_chartwise
    (hS : IsImmersion J I ∞ (Subtype.val : S → M))
    (hdim : Module.finrank ℝ E' < Module.finrank ℝ E) (x : M) :
    volume ((extChartAt I x) '' (S ∩ (extChartAt I x).source)) = 0 := by
  -- Project the owner measure-zero statement to the preferred chart at `x`.
  exact
    has_measure_zero_in_manifold.extChartAt_volume_eq_zero I
      (range_has_measure_zero_in_manifold_of_immersion_of_model_finrank_lt hS hdim) x

end
