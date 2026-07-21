import MorganTianLib.Ch01.MeasureNull

/-!
# Morgan–Tian Ch. 1, §1.4 — change of variables for the Riemannian measure, globally

`Ch01/RiemannianMeasure.lean` proves the change-of-variables formula
`riemannianMeasure_eq_lintegral_jacobian` only for a set lying inside **one chart**, and its own
docstring names the two things standing between it and `thm:bishop-gromov` on a manifold:
nullity of the cut locus (now `Ch01/CutLocusNull.lean`) and "the same argument run over the
`chartPiece` partition". This file does the latter:

  `riemannianMeasure_image_eq_lintegral_jacobian` :
    `μ_g (φ '' U) = ∫⁻ v in U, ρ(v)` for `φ : E → M` injective on `U`,

with no constraint whatsoever on where `φ '' U` sits — it may leave every chart, as the image of a
large ball under `exp_p` does.

## The Riemannian Jacobian

The subtlety is that the integrand is **not** a chart-local quantity. Read in the chart `α`, the
factor produced by mathlib's change of variables is `|det d(x_α ∘ φ)_v|`, and the factor produced by
the Riemannian measure is `√(det gᵢⱼ)` at `φ(v)` — and *neither is chart-independent on its own*.
Their product is: under a change of chart the two pick up reciprocal powers of `|det A|`, `A` the
tangent coordinate change, and they cancel (this cancellation is exactly `chartMeasure_apply_eq`).

`HasRiemannianJacobianOn g φ U ρ` says that `ρ` is that product, computed in *any* chart around
`φ(v)`. It is a hypothesis rather than a definition precisely so that a caller may supply whichever
chart it can compute in — the comparison estimates of `PolarVolumeComparison` produce a chart `ζ`
they do not control — while the theorem below is free to read `ρ` in the chart the atlas hands it.

## The proof

Cut `U` along the pullback of the measurable partition `chartPiece` of `M`. Each piece `Uₙ` maps
into a single chart, so the one-chart theorem applies to it verbatim; the images are pairwise
disjoint because the `chartPiece`s are, so the measures add; and the integrals add because the `Uₙ`
partition `U`. No injectivity of `φ` beyond `U` is used, and the pieces need no injectivity argument
of their own — `InjOn φ U` restricts.
-/

open MeasureTheory Measure Set Filter Function Riemannian Riemannian.Geodesic
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

-- Diamond-free model-space block (see `ExpContinuity`): no standalone `[NormedSpace ℝ E]`.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Math.** **`ρ` is the Riemannian Jacobian of `φ` on `U`**: at every `v ∈ U` and in *every*
chart `α` around `φ(v)`, the map `φ` read in coordinates has a derivative `D` there and

  `ρ(v) = |det D| · √(det gᵢⱼ(φ v))`.

Neither factor is chart-independent; the product is. With `φ = exp_p` this is the density that
`BishopGromovBall.expBallVolume` integrates. -/
def HasRiemannianJacobianOn (g : RiemannianMetric I M) (φ : E → M) (U : Set E) (ρ : E → ℝ) :
    Prop :=
  ∀ α : M, ∀ v ∈ U, φ v ∈ (extChartAt I α).source →
    ∃ D : E →L[ℝ] E,
      HasFDerivWithinAt (fun w : E => extChartAt I α (φ w)) D U v ∧
      ρ v = |D.det| * chartVolumeDensity (I := I) g α (extChartAt I α (φ v))

/-- **Math.** **Change of variables for the Riemannian measure, with no chart hypothesis.**

If `φ : E → M` is continuous, injective on a measurable `U ⊆ E`, and has Riemannian Jacobian `ρ`
there, then

  `μ_g (φ '' U) = ∫⁻ v in U, ρ(v) dv`.

Blueprint: the bridge from the pointwise comparison estimates to `Vol B(p,r)` in
`thm:bishop-gromov`. -/
theorem riemannianMeasure_image_eq_lintegral_jacobian (g : RiemannianMetric I M)
    {φ : E → M} {U : Set E} {ρ : E → ℝ}
    (hU : MeasurableSet U) (hφcont : Continuous φ) (hinj : InjOn φ U)
    (hρ : HasRiemannianJacobianOn (I := I) g φ U ρ) :
    riemannianMeasure (I := I) g μ (φ '' U) = ∫⁻ v in U, ENNReal.ofReal (ρ v) ∂μ := by
  classical
  -- pull the measurable partition of `M` back to a measurable partition of `U`
  set P : ℕ → Set M := chartPiece (I := I) (M := M) with hP
  set α : ℕ → M := chartCover (I := I) (M := M) with hα
  set Un : ℕ → Set E := fun n => U ∩ φ ⁻¹' P n with hUn
  have hUnmeas : ∀ n, MeasurableSet (Un n) := fun n =>
    hU.inter (hφcont.measurable (measurableSet_chartPiece (I := I) (M := M) n))
  have hUnsub : ∀ n, Un n ⊆ U := fun n => inter_subset_left
  have hUndisj : Pairwise (Disjoint on Un) := fun m n hmn =>
    ((pairwise_disjoint_chartPiece (I := I) (M := M) hmn).preimage φ).mono
      inter_subset_right inter_subset_right
  have hUnUnion : (⋃ n, Un n) = U := by
    rw [hUn, ← inter_iUnion, ← preimage_iUnion, iUnion_chartPiece (I := I) (M := M),
      preimage_univ, inter_univ]
  -- the image pieces
  set S : ℕ → Set M := fun n => φ '' Un n with hS
  have hSsub : ∀ n, S n ⊆ (extChartAt I (α n)).source := by
    rintro n _ ⟨v, hv, rfl⟩
    exact chartPiece_subset (I := I) (M := M) n hv.2
  -- the coordinate image of the `n`-th piece
  set Y : ℕ → Set E := fun n => (fun w : E => extChartAt I (α n) (φ w)) '' Un n with hY
  -- injectivity of `φ` read in the chart, on each piece
  have hinjY : ∀ n, InjOn (fun w : E => extChartAt I (α n) (φ w)) (Un n) := by
    intro n v hv w hw hEq
    have hvs : φ v ∈ (extChartAt I (α n)).source := hSsub n ⟨v, hv, rfl⟩
    have hws : φ w ∈ (extChartAt I (α n)).source := hSsub n ⟨w, hw, rfl⟩
    exact hinj (hUnsub n hv) (hUnsub n hw)
      ((extChartAt I (α n)).injOn hvs hws hEq)
  -- the derivative of `φ` read in the chart, on each piece
  have hderivY : ∀ n, ∀ v ∈ Un n, ∃ D : E →L[ℝ] E,
      HasFDerivWithinAt (fun w : E => extChartAt I (α n) (φ w)) D (Un n) v ∧
      ρ v = |D.det| * chartVolumeDensity (I := I) g (α n) (extChartAt I (α n) (φ v)) := by
    intro n v hv
    obtain ⟨D, hD, hρv⟩ := hρ (α n) v (hUnsub n hv) (hSsub n ⟨v, hv, rfl⟩)
    exact ⟨D, hD.mono (hUnsub n), hρv⟩
  choose! D hD hρD using hderivY
  -- the coordinate image is measurable …
  have hYmeas : ∀ n, MeasurableSet (Y n) := fun n =>
    MeasureTheory.measurable_image_of_fderivWithin (hUnmeas n) (hD n) (hinjY n)
  -- … hence so is the image piece, being its chart preimage inside the source
  have hSeq : ∀ n, S n = (extChartAt I (α n)) ⁻¹' Y n ∩ (extChartAt I (α n)).source := by
    intro n
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv, rfl⟩, hSsub n ⟨v, hv, rfl⟩⟩
    · rintro ⟨⟨v, hv, hvx⟩, hxs⟩
      have hvs : φ v ∈ (extChartAt I (α n)).source := hSsub n ⟨v, hv, rfl⟩
      exact ⟨v, hv, (extChartAt I (α n)).injOn hvs hxs hvx⟩
  have hSmeas : ∀ n, MeasurableSet (S n) := by
    intro n
    rw [hSeq n]
    have hsrc : MeasurableSet (extChartAt I (α n)).source :=
      (isOpen_extChartAt_source (I := I) (α n)).measurableSet
    have hcont : Continuous ((extChartAt I (α n)).source.restrict (extChartAt I (α n))) :=
      (continuousOn_extChartAt (I := I) (α n)).restrict
    have hsub : MeasurableSet
        (((extChartAt I (α n)).source.restrict (extChartAt I (α n))) ⁻¹' Y n) :=
      hcont.measurable (hYmeas n)
    have himg := hsrc.subtype_image hsub
    convert himg using 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, Set.restrict_apply]
    constructor
    · rintro ⟨hxY, hxs⟩; exact ⟨x, hxs, hxY, rfl⟩
    · rintro ⟨y, hys, hyY, rfl⟩; exact ⟨hyY, hys⟩
  -- the chart preimage of the image piece is exactly its coordinate image
  have hcover : ∀ n, chartPreimage (I := I) (α n) (S n) = Y n := by
    intro n
    ext y
    simp only [chartPreimage, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨⟨v, hv, hvy⟩, hyt⟩
      refine ⟨v, hv, ?_⟩
      show (extChartAt I (α n)) (φ v) = y
      rw [hvy, (extChartAt I (α n)).right_inv hyt]
    · rintro ⟨v, hv, rfl⟩
      have hvs : φ v ∈ (extChartAt I (α n)).source := hSsub n ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv, ((extChartAt I (α n)).left_inv hvs).symm⟩,
        (extChartAt I (α n)).map_source hvs⟩
  -- the one-chart change of variables on each piece
  have hpiece : ∀ n, riemannianMeasure (I := I) g μ (S n)
      = ∫⁻ v in Un n, ENNReal.ofReal (ρ v) ∂μ := by
    intro n
    rw [riemannianMeasure_eq_lintegral_jacobian μ g (α n) (hUnmeas n) (hSmeas n) (hSsub n)
      (hcover n) (hinjY n) (hD n)]
    refine setLIntegral_congr_fun (hUnmeas n) ?_
    intro v hv
    show ENNReal.ofReal (|(D n v).det| * chartVolumeDensity (I := I) g (α n)
        (extChartAt I (α n) (φ v))) = ENNReal.ofReal (ρ v)
    rw [hρD n v hv]
  -- assemble: the pieces are disjoint upstairs and downstairs
  have hSdisj : Pairwise (Disjoint on S) := fun m n hmn =>
    (pairwise_disjoint_chartPiece (I := I) (M := M) hmn).mono
      (by rintro _ ⟨v, hv, rfl⟩; exact hv.2) (by rintro _ ⟨v, hv, rfl⟩; exact hv.2)
  have hSunion : (⋃ n, S n) = φ '' U := by
    rw [hS, ← image_iUnion, hUnUnion]
  calc riemannianMeasure (I := I) g μ (φ '' U)
      = riemannianMeasure (I := I) g μ (⋃ n, S n) := by rw [hSunion]
    _ = ∑' n, riemannianMeasure (I := I) g μ (S n) := measure_iUnion hSdisj hSmeas
    _ = ∑' n, ∫⁻ v in Un n, ENNReal.ofReal (ρ v) ∂μ := tsum_congr hpiece
    _ = ∫⁻ v in ⋃ n, Un n, ENNReal.ofReal (ρ v) ∂μ :=
        (lintegral_iUnion hUnmeas hUndisj _).symm
    _ = ∫⁻ v in U, ENNReal.ofReal (ρ v) ∂μ := by rw [hUnUnion]

end MorganTianLib

end
