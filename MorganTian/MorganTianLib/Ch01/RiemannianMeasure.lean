import OpenGALib.Riemannian.Geodesic.HopfRinow.MetricBridge
import MorganTianLib.Ch01.Metric
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Morgan–Tian Ch. 1, §1.4 — the Riemannian volume measure

Every volume statement in Morgan–Tian's Chapter 1 — `thm:bishop-gromov`,
`prop:injectivity-radius-volume`, `thm:volume-injectivity-radius` — is a statement about
`Vol B(p,r)`, the **Riemannian measure** of a metric ball. Until now that quantity could not
even be *stated* in this workspace: mathlib has no volume measure on a manifold (only
`Orientation.volumeForm` on an inner-product space), and nothing in OpenGALib/MorganTianLib
supplied one. The comparison estimates feeding Bishop–Gromov were all proved
(`ricci_curvature_comparison`, `bishop_gromov_ball`), but they live on the *tangent space*,
against an abstract density `ρ : E → ℝ`. This file closes that gap.

## What is built

The classical definition: in a chart `α`, the Riemannian measure is
`√(det gᵢⱼ) dx¹ ⋯ dxⁿ`. Two things have to be checked, and the second is the whole content:

* `chartVolumeDensity g α y = √(det G^α(x))` — the density read in the `α`-chart, where
  `G^α` is `Riemannian.Tensor.chartGramMatrix`, the Gram matrix of the chart coordinate
  frame, and `x = (extChartAt I α).symm y`. Its determinant is positive
  (`chartGramMatrix_det_pos`) on the chart.

* `chartMeasure g μ α` — the pushforward of `√(det G^α) · μ` from the chart image to `M`.

* **Chart-independence** (`chartMeasure_apply_eq`): two charts assign the *same* measure to a
  set contained in both. This is the well-definedness of the Riemannian measure and the only
  real theorem here. It rests on the `(0,2)`-tensor transformation law
  `G^β = Aᵀ G^α A` with `A = tangentCoordChange I β α x` (OpenGALib's
  `chartGramMatrix_change`), whose determinant form
  `det G^β = (det A)² · det G^α` (`chartGramMatrix_det_change`) is *exactly* the Jacobian
  factor that mathlib's change-of-variables formula
  (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) produces. The two cancel.

* `riemannianMeasure g μ` — the global measure, glued from a countable atlas by
  disjointifying the chart sources (`Measure.sum` over `disjointed`), and
  `riemannianMeasure_apply_chart`, which says it is computed by the density formula in
  **every** chart, not just the ones used to build it. That last theorem is the interface
  every downstream volume statement should use; the gluing choices are invisible through it.

## Why the sqrt-determinant route, and not a volume form

A volume form needs an orientation, which a general `M` need not have; the density
`√(det gᵢⱼ)` needs none, transforming by `|det A|` rather than `det A`. That absolute value
is precisely what mathlib's change-of-variables formula supplies, so the unoriented route is
also the shorter one in Lean.

## Conventions

`μ` is an arbitrary additive Haar measure on the model space `E` — the same parameterisation
`PolarIntegral.lean` and `BishopGromovBall.lean` already use, so the three compose. Rescaling
`μ` rescales `riemannianMeasure` by the same constant, which cancels in every *ratio*
(Bishop–Gromov is a ratio). To pin an absolute normalisation, instantiate
`μ := (Module.finBasis ℝ E).addHaar`, the Haar measure giving the chart coordinate frame unit
covolume — then `riemannianMeasure` is the honest `√(det gᵢⱼ) dx¹ ⋯ dxⁿ`.

`I` is boundaryless: chart targets are then open in `E`, so `fderivWithin (range I)` is an
honest `fderiv` and the density is integrated over an open set.

Blueprint: `thm:bishop-gromov`, `prop:injectivity-radius-volume`, `thm:volume-injectivity-radius`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open MeasureTheory Measure Set Filter Module Matrix Function
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]

/-! ## The chart volume density `√(det gᵢⱼ)` -/

/-- **Math.** The **Riemannian volume density in the `α`-chart**: the function on chart
coordinates `y ∈ E` given by `√(det gᵢⱼ(x))`, where `x = (extChartAt I α).symm y` is the point
of `M` with coordinates `y` and `gᵢⱼ` is the Gram matrix of the chart coordinate frame at `x`.

Off the chart target this is junk; every statement below restricts it to
`(extChartAt I α).target`. -/
def chartVolumeDensity (g : RiemannianMetric I M) (α : M) (y : E) : ℝ :=
  Real.sqrt ((Riemannian.Tensor.chartGramMatrix (I := I) g α ((extChartAt I α).symm y)).det)

theorem chartVolumeDensity_nonneg (g : RiemannianMetric I M) (α : M) (y : E) :
    0 ≤ chartVolumeDensity (I := I) g α y :=
  Real.sqrt_nonneg _

/-- **Math.** The density is positive at coordinates of points of the chart source: the Gram
matrix of a coordinate frame is positive definite. -/
theorem chartVolumeDensity_pos (g : RiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    0 < chartVolumeDensity (I := I) g α y := by
  refine Real.sqrt_pos.mpr (Riemannian.Tensor.chartGramMatrix_det_pos (I := I) g α ?_)
  rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I]
  exact (extChartAt I α).map_target hy

/-! ## The determinant transformation law

The `(0,2)`-tensor law `G^β = Aᵀ G^α A` (OpenGALib `chartGramMatrix_change`) in the only form
this file needs: `det G^β = (det A)² det G^α`, hence `√(det G^β) = |det A| · √(det G^α)`. -/

/-- **Math.** The Gram matrix in the `β`-chart is the congruence `Aᵀ G^α A` of the Gram matrix in
the `α`-chart by `A = tangentCoordChange I β α x`, read in the basis `finBasis ℝ E`. -/
theorem chartGramMatrix_eq_conjTranspose_mul (g : RiemannianMetric I M) (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) :
    Riemannian.Tensor.chartGramMatrix (I := I) g β x
      = (LinearMap.toMatrix (finBasis ℝ E) (finBasis ℝ E)
            (tangentCoordChange I β α x : E →ₗ[ℝ] E)).transpose
          * Riemannian.Tensor.chartGramMatrix (I := I) g α x
          * LinearMap.toMatrix (finBasis ℝ E) (finBasis ℝ E)
            (tangentCoordChange I β α x : E →ₗ[ℝ] E) := by
  ext i j
  rw [Riemannian.chartGramMatrix_change (I := I) g α β hxα hxβ i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, LinearMap.toMatrix_apply,
    ContinuousLinearMap.coe_coe, Riemannian.Geodesic.chartCoord_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Math.** The determinant form of the transformation law:
`det G^β(x) = (det A)² · det G^α(x)` with `A = tangentCoordChange I β α x`. -/
theorem chartGramMatrix_det_change (g : RiemannianMetric I M) (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) :
    (Riemannian.Tensor.chartGramMatrix (I := I) g β x).det
      = (LinearMap.det (tangentCoordChange I β α x : E →ₗ[ℝ] E)) ^ 2
          * (Riemannian.Tensor.chartGramMatrix (I := I) g α x).det := by
  rw [chartGramMatrix_eq_conjTranspose_mul (I := I) g α β hxα hxβ, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, ← LinearMap.det_toMatrix (finBasis ℝ E)]
  ring

/-- **Math.** The density form of the transformation law:
`√(det G^β(x)) = |det A| · √(det G^α(x))`. This is the Jacobian factor that mathlib's
change-of-variables formula produces, which is why the two cancel in `chartMeasure_apply_eq`. -/
theorem sqrt_chartGramMatrix_det_change (g : RiemannianMetric I M) (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) :
    Real.sqrt ((Riemannian.Tensor.chartGramMatrix (I := I) g β x).det)
      = |LinearMap.det (tangentCoordChange I β α x : E →ₗ[ℝ] E)|
          * Real.sqrt ((Riemannian.Tensor.chartGramMatrix (I := I) g α x).det) := by
  rw [chartGramMatrix_det_change (I := I) g α β hxα hxβ, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs]

/-! ## The chart measure -/

/-- **Math.** The coordinate image of `s` in the `α`-chart, written as a *preimage* so that its
measurability is immediate. For `s ⊆ (extChartAt I α).source` this is `extChartAt I α '' s`. -/
def chartPreimage (α : M) (s : Set M) : Set E :=
  (extChartAt I α).symm ⁻¹' s ∩ (extChartAt I α).target

theorem chartPreimage_subset_target (α : M) (s : Set M) :
    chartPreimage (I := I) α s ⊆ (extChartAt I α).target :=
  inter_subset_right

theorem measurableSet_chartPreimage (α : M) {s : Set M} (hs : MeasurableSet s) :
    MeasurableSet (chartPreimage (I := I) α s) := by
  have htgt : MeasurableSet (extChartAt I α).target :=
    (isOpen_extChartAt_target (I := I) α).measurableSet
  have hcont : Continuous ((extChartAt I α).target.restrict (extChartAt I α).symm) :=
    (continuousOn_extChartAt_symm (I := I) α).restrict
  have hsub : MeasurableSet
      (((extChartAt I α).target.restrict (extChartAt I α).symm) ⁻¹' s) :=
    hcont.measurable hs
  have himg := htgt.subtype_image hsub
  convert himg using 1
  ext y
  simp only [chartPreimage, mem_inter_iff, mem_preimage, mem_image, Subtype.exists,
    Set.restrict_apply]
  constructor
  · rintro ⟨hys, hyt⟩; exact ⟨y, hyt, hys, rfl⟩
  · rintro ⟨z, hzt, hzs, rfl⟩; exact ⟨hzs, hzt⟩

/-- **Math.** The **Riemannian measure read in the `α`-chart**: push the density
`√(det gᵢⱼ) · μ` forward from the chart image to `M`. Supported on `(extChartAt I α).source`. -/
def chartMeasure (g : RiemannianMetric I M) (μ : Measure E) (α : M) : Measure M :=
  Measure.map (extChartAt I α).symm
    ((μ.restrict (extChartAt I α).target).withDensity
      (fun y => ENNReal.ofReal (chartVolumeDensity (I := I) g α y)))

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Math.** The defining formula: the `α`-chart measure of a measurable set is the integral of
the density `√(det gᵢⱼ)` over its coordinate image. -/
theorem chartMeasure_apply (g : RiemannianMetric I M) (α : M) {s : Set M}
    (hs : MeasurableSet s) :
    chartMeasure (I := I) g μ α s
      = ∫⁻ y in chartPreimage (I := I) α s,
          ENNReal.ofReal (chartVolumeDensity (I := I) g α y) ∂μ := by
  have htgt : MeasurableSet (extChartAt I α).target :=
    (isOpen_extChartAt_target (I := I) α).measurableSet
  have hae : AEMeasurable (extChartAt I α).symm (μ.restrict (extChartAt I α).target) :=
    (continuousOn_extChartAt_symm (I := I) α).aemeasurable htgt
  have hae' : AEMeasurable (extChartAt I α).symm
      ((μ.restrict (extChartAt I α).target).withDensity
        (fun y => ENNReal.ofReal (chartVolumeDensity (I := I) g α y))) :=
    hae.mono' (withDensity_absolutelyContinuous _ _)
  rw [chartMeasure, Measure.map_apply_of_aemeasurable hae' hs, withDensity_apply' _ _,
    chartPreimage, ← Measure.restrict_restrict' htgt]

/-! ## Chart-independence: the Riemannian measure is well defined -/

/-- **Math.** **Well-definedness of the Riemannian measure.** Two charts assign the same measure
to a measurable set contained in both chart sources.

The proof is the change of variables `τ = extChartAt I α ∘ (extChartAt I β).symm` on the model
space. Mathlib's formula contributes a factor `|det (fderiv τ)| = |det (tangentCoordChange I β α)|`;
the Gram-determinant transformation law contributes exactly its reciprocal, and the two cancel. -/
theorem chartMeasure_apply_eq (g : RiemannianMetric I M) (α β : M) {s : Set M}
    (hs : MeasurableSet s) (hsα : s ⊆ (extChartAt I α).source)
    (hsβ : s ⊆ (extChartAt I β).source) :
    chartMeasure (I := I) g μ α s = chartMeasure (I := I) g μ β s := by
  classical
  rw [chartMeasure_apply μ g α hs, chartMeasure_apply μ g β hs]
  set τ : E → E := fun y => extChartAt I α ((extChartAt I β).symm y) with hτ
  have hmem : ∀ y ∈ chartPreimage (I := I) β s,
      (extChartAt I β).symm y ∈ s ∧ y ∈ (extChartAt I β).target := fun _ hy => ⟨hy.1, hy.2⟩
  -- `τ` carries the β-coordinate image onto the α-coordinate image
  have himg : τ '' chartPreimage (I := I) β s = chartPreimage (I := I) α s := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hys, hyt⟩ := hmem y hy
      have hli : (extChartAt I α).symm (τ y) = (extChartAt I β).symm y := by
        simp only [hτ]; exact (extChartAt I α).left_inv (hsα hys)
      refine ⟨?_, ?_⟩
      · show (extChartAt I α).symm (τ y) ∈ s
        rw [hli]; exact hys
      · show τ y ∈ (extChartAt I α).target
        simp only [hτ]; exact (extChartAt I α).map_source (hsα hys)
    · intro z hz
      have hzs : (extChartAt I α).symm z ∈ s := hz.1
      have hzt : z ∈ (extChartAt I α).target := hz.2
      refine ⟨(extChartAt I β) ((extChartAt I α).symm z), ⟨?_, ?_⟩, ?_⟩
      · show (extChartAt I β).symm ((extChartAt I β) ((extChartAt I α).symm z)) ∈ s
        rw [(extChartAt I β).left_inv (hsβ hzs)]; exact hzs
      · exact (extChartAt I β).map_source (hsβ hzs)
      · show extChartAt I α
            ((extChartAt I β).symm ((extChartAt I β) ((extChartAt I α).symm z))) = z
        rw [(extChartAt I β).left_inv (hsβ hzs), (extChartAt I α).right_inv hzt]
  -- `τ` is injective there
  have hinj : InjOn τ (chartPreimage (I := I) β s) := by
    intro y₁ hy₁ y₂ hy₂ hEq
    obtain ⟨hy₁s, hy₁t⟩ := hmem y₁ hy₁
    obtain ⟨hy₂s, hy₂t⟩ := hmem y₂ hy₂
    have h := congrArg (extChartAt I α).symm hEq
    simp only [hτ] at h
    rw [(extChartAt I α).left_inv (hsα hy₁s), (extChartAt I α).left_inv (hsα hy₂s)] at h
    rw [← (extChartAt I β).right_inv hy₁t, ← (extChartAt I β).right_inv hy₂t, h]
  -- its derivative is the tangent coordinate change
  have hderiv : ∀ y ∈ chartPreimage (I := I) β s,
      HasFDerivWithinAt τ (tangentCoordChange I β α ((extChartAt I β).symm y))
        (chartPreimage (I := I) β s) y := by
    intro y hy
    obtain ⟨hys, hyt⟩ := hmem y hy
    have hz : (extChartAt I β).symm y ∈
        (extChartAt I β).source ∩ (extChartAt I α).source := ⟨hsβ hys, hsα hys⟩
    have hd := hasFDerivWithinAt_tangentCoordChange (I := I) hz
    rw [(extChartAt I β).right_inv hyt, I.range_eq_univ] at hd
    exact (hasFDerivWithinAt_univ.mp hd).hasFDerivWithinAt
  rw [← himg,
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul μ
      (measurableSet_chartPreimage (I := I) β hs) hderiv hinj
      (fun z => ENNReal.ofReal (chartVolumeDensity (I := I) g α z))]
  refine setLIntegral_congr_fun (measurableSet_chartPreimage (I := I) β hs) ?_
  intro y hy
  obtain ⟨hys, hyt⟩ := hmem y hy
  have hxα : (extChartAt I β).symm y ∈ (chartAt H α).source := by
    rw [← extChartAt_source I]; exact hsα hys
  have hxβ : (extChartAt I β).symm y ∈ (chartAt H β).source := by
    rw [← extChartAt_source I]; exact hsβ hys
  have hτy : (extChartAt I α).symm (τ y) = (extChartAt I β).symm y := by
    simp only [hτ]; exact (extChartAt I α).left_inv (hsα hys)
  simp only [ContinuousLinearMap.det, chartVolumeDensity, hτy]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  exact congrArg ENNReal.ofReal
    (sqrt_chartGramMatrix_det_change (I := I) g α β hxα hxβ).symm

/-! ## The global Riemannian measure -/

variable [SecondCountableTopology M] [Nonempty M]

/-- **Math.** A countable family of chart centres whose chart sources cover `M`; it exists because
`M` is second countable. This is the countable atlas of the classical construction. -/
theorem exists_countable_chart_cover :
    ∃ c : ℕ → M, (⋃ n, (extChartAt I (c n)).source) = univ := by
  obtain ⟨S, hScount, hScover⟩ :=
    TopologicalSpace.countable_cover_nhds (f := fun x : M => (extChartAt I x).source)
      fun x => extChartAt_source_mem_nhds (I := I) x
  have hSne : S.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    simp only [hemp, mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at hScover
    exact absurd (hScover ▸ mem_univ (Classical.arbitrary M)) (by simp)
  obtain ⟨c, hc⟩ := hScount.exists_eq_range hSne
  refine ⟨c, ?_⟩
  rw [← hScover, hc, Set.biUnion_range]

/-- **Math.** The chosen countable atlas underlying `riemannianMeasure`. Nothing downstream should
depend on the choice: `riemannianMeasure_apply_chart` computes the measure in an *arbitrary*
chart. -/
def chartCover : ℕ → M :=
  Classical.choose (exists_countable_chart_cover (I := I) (M := M))

theorem iUnion_chartCover_source :
    (⋃ n, (extChartAt I (chartCover (I := I) (M := M) n)).source) = univ :=
  Classical.choose_spec (exists_countable_chart_cover (I := I) (M := M))

/-- **Math.** The disjointification of the chart sources of the chosen countable atlas: a
measurable partition of `M` whose `n`-th piece lies inside the `n`-th chart. -/
def chartPiece (n : ℕ) : Set M :=
  disjointed (fun k => (extChartAt I (chartCover (I := I) (M := M) k)).source) n

theorem chartPiece_subset (n : ℕ) :
    chartPiece (I := I) (M := M) n
      ⊆ (extChartAt I (chartCover (I := I) (M := M) n)).source :=
  disjointed_le _ n

theorem measurableSet_chartPiece (n : ℕ) :
    MeasurableSet (chartPiece (I := I) (M := M) n) :=
  MeasurableSet.disjointed
    (fun k => (isOpen_extChartAt_source (I := I)
      (chartCover (I := I) (M := M) k)).measurableSet) n

theorem pairwise_disjoint_chartPiece :
    Pairwise (Disjoint on (chartPiece (I := I) (M := M))) :=
  disjoint_disjointed _

theorem iUnion_chartPiece : (⋃ n, chartPiece (I := I) (M := M) n) = univ :=
  (iUnion_disjointed (f := fun k =>
    (extChartAt I (chartCover (I := I) (M := M) k)).source)).trans
    (iUnion_chartCover_source (I := I) (M := M))

/-- **Math.** The **Riemannian volume measure** `μ_g` of `(M, g)`: glue the chart measures along a
countable atlas, cutting each chart down to its piece of a measurable partition of `M`.

Blueprint: the measure underlying `\Vol` in `thm:bishop-gromov`,
`prop:injectivity-radius-volume`, `thm:volume-injectivity-radius`. -/
def riemannianMeasure (g : RiemannianMetric I M) (μ : Measure E) : Measure M :=
  Measure.sum fun n =>
    (chartMeasure (I := I) g μ (chartCover (I := I) (M := M) n)).restrict
      (chartPiece (I := I) (M := M) n)

/-- **Math.** The **interface theorem**: the Riemannian measure of a measurable set contained in
*any* chart is the integral of `√(det gᵢⱼ)` over its coordinate image in that chart. The atlas
chosen to build `riemannianMeasure` is invisible here — this is what makes the definition the
honest `√(det gᵢⱼ) dx¹ ⋯ dxⁿ`, and it is the interface every volume statement should use. -/
theorem riemannianMeasure_apply_chart (g : RiemannianMetric I M) (α : M) {s : Set M}
    (hs : MeasurableSet s) (hsα : s ⊆ (extChartAt I α).source) :
    riemannianMeasure (I := I) g μ s
      = ∫⁻ y in chartPreimage (I := I) α s,
          ENNReal.ofReal (chartVolumeDensity (I := I) g α y) ∂μ := by
  classical
  have hpiece : ∀ n, MeasurableSet (s ∩ chartPiece (I := I) (M := M) n) := fun n =>
    hs.inter (measurableSet_chartPiece (I := I) (M := M) n)
  have hdisj : Pairwise (Disjoint on fun n => s ∩ chartPiece (I := I) (M := M) n) :=
    fun _ _ hmn =>
      ((pairwise_disjoint_chartPiece (I := I) (M := M) hmn).mono
        inter_subset_right inter_subset_right)
  have hchart : ∀ n,
      (chartMeasure (I := I) g μ (chartCover (I := I) (M := M) n)).restrict
          (chartPiece (I := I) (M := M) n) s
        = chartMeasure (I := I) g μ α (s ∩ chartPiece (I := I) (M := M) n) := by
    intro n
    rw [Measure.restrict_apply hs]
    exact chartMeasure_apply_eq μ g (chartCover (I := I) (M := M) n) α (hpiece n)
      (fun _ hz => chartPiece_subset (I := I) (M := M) n hz.2) (fun _ hz => hsα hz.1)
  rw [riemannianMeasure, Measure.sum_apply _ hs]
  calc ∑' n, (chartMeasure (I := I) g μ (chartCover (I := I) (M := M) n)).restrict
          (chartPiece (I := I) (M := M) n) s
      = ∑' n, chartMeasure (I := I) g μ α (s ∩ chartPiece (I := I) (M := M) n) :=
        tsum_congr hchart
    _ = chartMeasure (I := I) g μ α (⋃ n, s ∩ chartPiece (I := I) (M := M) n) :=
        (measure_iUnion hdisj hpiece).symm
    _ = chartMeasure (I := I) g μ α s := by
        rw [← inter_iUnion, iUnion_chartPiece (I := I) (M := M), inter_univ]
    _ = _ := chartMeasure_apply μ g α hs

/-! ## Change of variables: the Riemannian Jacobian of a parameterisation -/

/-- **Math.** **Change of variables for the Riemannian measure.** Let `φ : E → M` parameterise a
measurable set `S ⊆ M` lying in a single chart `α`, injectively, with derivative `φ'` read in that
chart. Then `μ_g S` is the integral over the parameter domain of the **Riemannian Jacobian** of
`φ`: the chart Jacobian `|det φ'|` times the chart density `√(det gᵢⱼ)` at the image point.

Neither factor is chart-independent on its own; their product is — that is exactly the
cancellation of `chartMeasure_apply_eq`. With `φ = exp_p` and `S = B(p,r)` the product is the
density `ρ(v) = |det d(exp_p)_v|` that `BishopGromovBall.expBallVolume` integrates, so this is the
bridge from the comparison estimates to `Vol B(p,r)`.

Scope: `S` must lie in one chart. Both of the things this scope restriction used to cost are now
paid for elsewhere, and callers should reach for those rather than for this lemma directly:
* the same argument run over the `chartPiece` partition, for an `S` that leaves every chart, is
  `Ch01/RiemannianJacobian.lean` (`riemannianMeasure_image_eq_lintegral_jacobian`);
* nullity of the cut locus is `Ch01/CutLocusNull.lean` (`riemannianMeasure_cutLocus_eq_zero`). -/
theorem riemannianMeasure_eq_lintegral_jacobian (g : RiemannianMetric I M) (α : M)
    {φ : E → M} {φ' : E → E →L[ℝ] E} {U : Set E} {S : Set M}
    (hU : MeasurableSet U) (hS : MeasurableSet S) (hSα : S ⊆ (extChartAt I α).source)
    (hcover : chartPreimage (I := I) α S = (fun v => extChartAt I α (φ v)) '' U)
    (hinj : InjOn (fun v => extChartAt I α (φ v)) U)
    (hderiv : ∀ v ∈ U, HasFDerivWithinAt (fun w => extChartAt I α (φ w)) (φ' v) U v) :
    riemannianMeasure (I := I) g μ S
      = ∫⁻ v in U, ENNReal.ofReal (|(φ' v).det|
          * chartVolumeDensity (I := I) g α (extChartAt I α (φ v))) ∂μ := by
  rw [riemannianMeasure_apply_chart μ g α hS hSα, hcover,
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hU hderiv hinj
      (fun z => ENNReal.ofReal (chartVolumeDensity (I := I) g α z))]
  refine setLIntegral_congr_fun hU ?_
  intro v _
  exact (ENNReal.ofReal_mul (abs_nonneg ((φ' v).det))).symm

end MorganTianLib
