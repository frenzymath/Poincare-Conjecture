import PoincareLib.Ch01.RiemannianMeasure
import PoincareLib.Ch01.ExpChartDifferentiable

/-!
# Morgan–Tian Ch. 1, §1.4 — null sets for the Riemannian measure

Mathlib has **no** notion of a null set on a manifold: there is no `MeasureZero` predicate under
`Geometry/Manifold`, no chart-invariance lemma, and no Sard theorem beyond the equidimensional case
in `Jacobian.lean`. So the two facts every volume argument needs have to be built here:

* `riemannianMeasure_eq_zero_of_chartImage_null` — a subset of a single chart whose *coordinate
  image* is Lebesgue-null is `μ_g`-null. This is what makes "null" a chart-independent notion: the
  Riemannian measure is `√(det gᵢⱼ) · dx` in any chart, and a density cannot resurrect a null set.

* `riemannianMeasure_image_eq_zero_of_null` — the image of a Lebesgue-null set under a map
  `f : E → M` that is **differentiable read in charts** is `μ_g`-null. Downstream this is applied to
  `f = exp_p` (`riemannianMeasure_expMapGlobal_image_eq_zero`), which is exactly what turns nullity
  of the *cut vectors* in `T_pM` into nullity of the *cut locus* in `M`.

The proof of the second is mathlib's `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`
("a differentiable map sends null sets to null sets", between finite-dimensional spaces), applied
chart by chart along the countable atlas `chartCover` that `riemannianMeasure` is built from. It is
the pointwise differentiability of `exp_p` in an *arbitrary* chart — `ExpChartDifferentiable` — that
lets the chart be chosen to suit the atlas rather than the Jacobi machinery.

Note neither statement needs `f '' N` to be measurable. Measures in mathlib are outer measures, and
nullity is proved by exhibiting a measurable null superset, which the chart argument produces.
-/

open MeasureTheory Measure Set Filter Riemannian Riemannian.Geodesic
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

-- Diamond-free model-space block (see `ExpContinuity`): no standalone `[NormedSpace ℝ E]`.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-! ## Nullity is a chart-local, chart-independent notion -/

/-- **Math.** **A set with null coordinate image is null.** If `A` lies inside a single chart and its
image `extChartAt α '' A` is Lebesgue-null in `E`, then `μ_g A = 0`.

`A` need not be measurable: we produce a measurable null superset. Take a measurable
`Z ⊇ extChartAt α '' A` with `μ Z = 0`; then `Zhat = (extChartAt α)⁻¹(Z) ∩ source` is a measurable
superset of `A` inside the chart whose coordinate image is `Z ∩ target`, and
`riemannianMeasure_apply_chart` computes `μ_g Zhat` as an integral over that null set. -/
theorem riemannianMeasure_eq_zero_of_chartImage_null (g : RiemannianMetric I M) (α : M)
    {A : Set M} (hA : A ⊆ (extChartAt I α).source)
    (hnull : μ (extChartAt I α '' A) = 0) :
    riemannianMeasure (I := I) g μ A = 0 := by
  obtain ⟨Z, hZsub, hZmeas, hZ0⟩ := exists_measurable_superset_of_null hnull
  -- the measurable superset of `A` inside the chart source
  set Zhat : Set M := (extChartAt I α) ⁻¹' Z ∩ (extChartAt I α).source with hZhatdef
  have hsrc : MeasurableSet (extChartAt I α).source :=
    (isOpen_extChartAt_source (I := I) α).measurableSet
  have hZhatmeas : MeasurableSet Zhat := by
    have hcont : Continuous ((extChartAt I α).source.restrict (extChartAt I α)) :=
      (continuousOn_extChartAt (I := I) α).restrict
    have hsub : MeasurableSet
        (((extChartAt I α).source.restrict (extChartAt I α)) ⁻¹' Z) := hcont.measurable hZmeas
    have himg := hsrc.subtype_image hsub
    convert himg using 1
    ext x
    simp only [hZhatdef, mem_inter_iff, mem_preimage, mem_image, Subtype.exists, Set.restrict_apply]
    constructor
    · rintro ⟨hxZ, hxs⟩; exact ⟨x, hxs, hxZ, rfl⟩
    · rintro ⟨y, hys, hyZ, rfl⟩; exact ⟨hyZ, hys⟩
  have hAZhat : A ⊆ Zhat := fun x hx => ⟨hZsub ⟨x, hx, rfl⟩, hA hx⟩
  -- the coordinate image of `Zhat` is `Z ∩ target`, which is null
  have hcp : chartPreimage (I := I) α Zhat = Z ∩ (extChartAt I α).target := by
    ext y
    simp only [chartPreimage, hZhatdef, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨⟨hyZ, -⟩, hyt⟩
      rw [(extChartAt I α).right_inv hyt] at hyZ
      exact ⟨hyZ, hyt⟩
    · rintro ⟨hyZ, hyt⟩
      refine ⟨⟨?_, (extChartAt I α).map_target hyt⟩, hyt⟩
      rwa [(extChartAt I α).right_inv hyt]
  have hZhat0 : riemannianMeasure (I := I) g μ Zhat = 0 := by
    rw [riemannianMeasure_apply_chart μ g α hZhatmeas inter_subset_right, hcp]
    exact setLIntegral_measure_zero _ _ (measure_mono_null inter_subset_left hZ0)
  exact measure_mono_null hAZhat hZhat0

/-! ## Differentiable images of null sets -/

/-- **Math.** **A chart-differentiable map sends null sets to null sets.**

Let `f : E → M` be continuous and, read in *any* chart around `f v`, differentiable at `v`. Then
`μ_g (f '' N) = 0` for every Lebesgue-null `N ⊆ E`.

Chart by chart along the countable atlas of `riemannianMeasure`: on the piece of `f '' N` lying in
the `α`-chart, the coordinate image is contained in the image of `N ∩ f⁻¹(source α)` under the
`E → E` map `extChartAt α ∘ f`, which is differentiable there — so mathlib's
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` applies. -/
theorem riemannianMeasure_image_eq_zero_of_null (g : RiemannianMetric I M)
    {f : E → M} (hfcont : Continuous f)
    (hfdiff : ∀ (α : M) (v : E), f v ∈ (extChartAt I α).source →
      DifferentiableAt ℝ (fun w : E => extChartAt I α (f w)) v)
    {N : Set E} (hN : μ N = 0) :
    riemannianMeasure (I := I) g μ (f '' N) = 0 := by
  -- split `f '' N` along the countable atlas underlying `riemannianMeasure`
  have hcover : f '' N
      = ⋃ n : ℕ, (f '' N ∩ (extChartAt I (chartCover (I := I) (M := M) n)).source) := by
    rw [← inter_iUnion, iUnion_chartCover_source (I := I) (M := M), inter_univ]
  rw [hcover]
  refine measure_iUnion_null fun n => ?_
  set α : M := chartCover (I := I) (M := M) n with hα
  refine riemannianMeasure_eq_zero_of_chartImage_null μ g α inter_subset_right ?_
  -- the coordinate image sits inside the image of `N ∩ f⁻¹(source α)` under `extChartAt α ∘ f`
  set S : Set E := N ∩ f ⁻¹' (extChartAt I α).source with hS
  have hmono : extChartAt I α '' (f '' N ∩ (extChartAt I α).source)
      ⊆ (fun w : E => extChartAt I α (f w)) '' S := by
    rintro _ ⟨x, ⟨⟨v, hvN, rfl⟩, hxs⟩, rfl⟩
    exact ⟨v, ⟨hvN, hxs⟩, rfl⟩
  refine measure_mono_null hmono ?_
  -- and that image is null: the map is differentiable on `S`, and `S ⊆ N` is null
  refine MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ ?_ ?_
  · exact fun v hv => (hfdiff α v hv.2).differentiableWithinAt
  · exact measure_mono_null inter_subset_left hN

/-- **Math.** **`exp_p` sends null sets to null sets.** The instance of the previous theorem that
the cut locus needs: `exp_p` is continuous (`continuous_expMapGlobal`) and differentiable in every
chart (`differentiableAt_extChartAt_expMapGlobal`). -/
theorem riemannianMeasure_expMapGlobal_image_eq_zero (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) (p : M) {N : Set E} (hN : μ N = 0) :
    riemannianMeasure (I := I) g μ (expMapGlobal (I := I) g hg p '' N) = 0 :=
  riemannianMeasure_image_eq_zero_of_null μ g
    (continuous_expMapGlobal (I := I) g hg p)
    (fun α v hv => differentiableAt_extChartAt_expMapGlobal (I := I) g hg p α hv) hN

end PoincareLib

end
