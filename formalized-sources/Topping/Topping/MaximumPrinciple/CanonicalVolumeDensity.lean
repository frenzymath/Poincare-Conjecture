import MorganTianLib.Ch02.GreenIdentity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Topping.MaximumPrinciple.RiemannianMeasureSigmaFinite
import Topping.MaximumPrinciple.RelativeVolumeDensity
import Topping.MaximumPrinciple.VolumeDensityBridge

open scoped ContDiff Manifold Topology Bundle Matrix ENNReal NNReal
open Set Riemannian MeasureTheory Filter

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

set_option linter.unusedSectionVars false in
private theorem chart_zero_of_riemannianMeasure_zero
    (g h : RiemannianMetric I M) (μ : Measure E) [μ.IsAddHaarMeasure]
    (α : M) {s : Set M} (hs : MeasurableSet s)
    (hsα : s ⊆ (extChartAt I α).source)
    (hzero : MorganTianLib.riemannianMeasure (I := I) h μ s = 0) :
    MorganTianLib.riemannianMeasure (I := I) g μ s = 0 := by
  let T : Set E := (extChartAt I α).target
  let A : Set E := MorganTianLib.chartPreimage (I := I) α s
  let f : E → ENNReal := fun y ↦
    ENNReal.ofReal (MorganTianLib.chartVolumeDensity (I := I) h α y)
  have hT : MeasurableSet T := by
    exact (isOpen_extChartAt_target (I := I) α).measurableSet
  have hA : MeasurableSet A := by
    exact MorganTianLib.measurableSet_chartPreimage (I := I) α hs
  have hAT : A ⊆ T := by
    exact MorganTianLib.chartPreimage_subset_target (I := I) α s
  have hfcont : ContinuousOn f T := by
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (MorganTianLib.contDiffOn_chartVolumeDensity (I := I) h α).continuousOn
  have hfa : AEMeasurable f (μ.restrict T) :=
    hfcont.aemeasurable hT
  have hzero' : ∫⁻ y in A, f y ∂μ = 0 := by
    have hz := hzero
    rw [MorganTianLib.riemannianMeasure_apply_chart μ h α hs hsα] at hz
    exact hz
  have hfA : AEMeasurable f (μ.restrict A) := hfa.mono_set hAT
  have hzae : ∀ᵐ y ∂μ, y ∈ A → f y = 0 :=
    (setLIntegral_eq_zero_iff' hA hfA).mp hzero'
  have hfpos : ∀ y ∈ A, f y ≠ 0 := by
    intro y hy
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (MorganTianLib.chartVolumeDensity_pos (I := I) h α (hAT hy)))
  have hμA : μ A = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hzae] with y hy
    intro hyA
    exact (hfpos y hyA) (hy hyA)
  rw [MorganTianLib.riemannianMeasure_apply_chart μ g α hs hsα]
  exact setLIntegral_measure_zero _ _ hμA

set_option linter.unusedSectionVars false in
/-- **Math.** Riemannian measures built from two metrics and the same Haar base have
the same null sets in the direction needed for a fixed-reference density. -/
theorem riemannianMeasure_absolutelyContinuous
    (g h : RiemannianMetric I M) (μ : Measure E) [μ.IsAddHaarMeasure] :
    MorganTianLib.riemannianMeasure (I := I) g μ ≪
      MorganTianLib.riemannianMeasure (I := I) h μ := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hzero ↦ ?_)
  have hpiece : ∀ n, MeasurableSet
      (s ∩ MorganTianLib.chartPiece (I := I) (M := M) n) := fun n ↦
    hs.inter (MorganTianLib.measurableSet_chartPiece (I := I) (M := M) n)
  have hdisj : Pairwise (fun i j ↦ Disjoint
      (s ∩ MorganTianLib.chartPiece (I := I) (M := M) i)
      (s ∩ MorganTianLib.chartPiece (I := I) (M := M) j)) := fun _ _ hmn ↦
    ((MorganTianLib.pairwise_disjoint_chartPiece (I := I) (M := M) hmn).mono
      inter_subset_right inter_subset_right)
  have hzero_piece : ∀ n,
      MorganTianLib.riemannianMeasure (I := I) h μ
        (s ∩ MorganTianLib.chartPiece (I := I) (M := M) n) = 0 := fun n ↦
    measure_mono_null inter_subset_left hzero
  have hlocal : ∀ n,
      MorganTianLib.riemannianMeasure (I := I) g μ
        (s ∩ MorganTianLib.chartPiece (I := I) (M := M) n) = 0 := fun n ↦ by
    apply chart_zero_of_riemannianMeasure_zero g h μ
      (MorganTianLib.chartCover (I := I) (M := M) n) (hpiece n)
    · intro x hx
      exact MorganTianLib.chartPiece_subset (I := I) (M := M) n hx.2
    · exact hzero_piece n
  have hsunion : s = ⋃ n, s ∩ MorganTianLib.chartPiece (I := I) (M := M) n := by
    calc
      s = s ∩ (⋃ n, MorganTianLib.chartPiece (I := I) (M := M) n) := by
        rw [MorganTianLib.iUnion_chartPiece (I := I) (M := M), inter_univ]
      _ = ⋃ n, s ∩ MorganTianLib.chartPiece (I := I) (M := M) n :=
        inter_iUnion s (fun n ↦ MorganTianLib.chartPiece (I := I) (M := M) n)
  rw [hsunion, measure_iUnion hdisj hpiece]
  exact ENNReal.tsum_eq_zero.mpr hlocal

set_option linter.unusedSectionVars false in
/-- **Math.** The two canonical Riemannian measures with a common Haar base are
mutually absolutely continuous. -/
theorem riemannianMeasure_mutuallyAbsolutelyContinuous
    (g h : RiemannianMetric I M) (μ : Measure E) [μ.IsAddHaarMeasure] :
    MorganTianLib.riemannianMeasure (I := I) g μ ≪
      MorganTianLib.riemannianMeasure (I := I) h μ ∧
    MorganTianLib.riemannianMeasure (I := I) h μ ≪
      MorganTianLib.riemannianMeasure (I := I) g μ := by
  exact ⟨riemannianMeasure_absolutelyContinuous g h μ,
    riemannianMeasure_absolutelyContinuous h g μ⟩

set_option linter.unusedSectionVars false in
/-- **Math.** A canonical Riemannian measure is the Radon--Nikodym `withDensity`
of any other canonical Riemannian measure built from the same Haar base. -/
theorem riemannianMeasure_eq_withDensity_rnDeriv
    (g h : RiemannianMetric I M) (μ : Measure E) [μ.IsAddHaarMeasure] :
    (MorganTianLib.riemannianMeasure (I := I) g μ).withDensity
        ((MorganTianLib.riemannianMeasure (I := I) h μ).rnDeriv
          (MorganTianLib.riemannianMeasure (I := I) g μ)) =
      MorganTianLib.riemannianMeasure (I := I) h μ := by
  exact Measure.withDensity_rnDeriv_eq _ _
    (riemannianMeasure_absolutelyContinuous h g μ)

set_option linter.unusedSectionVars false in
/-- **Math.** The preceding Radon--Nikodym representation can be fed directly to
the weighted-density volume bridge using the `NNReal` truncation of the derivative. -/
theorem riemannianMeasure_eq_withDensity_rnDensity
    (g h : RiemannianMetric I M) (μ : Measure E) [μ.IsAddHaarMeasure] :
  (MorganTianLib.riemannianMeasure (I := I) g μ).withDensity
        (fun p ↦ (((MorganTianLib.riemannianMeasure (I := I) h μ).rnDeriv
          (MorganTianLib.riemannianMeasure (I := I) g μ) p).toNNReal : ENNReal)) =
      MorganTianLib.riemannianMeasure (I := I) h μ := by
  have htop : ∀ᵐ p ∂MorganTianLib.riemannianMeasure (I := I) g μ,
      (MorganTianLib.riemannianMeasure (I := I) h μ).rnDeriv
          (MorganTianLib.riemannianMeasure (I := I) g μ) p ≠ (∞ : ENNReal) :=
    Measure.rnDeriv_ne_top
      (MorganTianLib.riemannianMeasure (I := I) h μ)
      (MorganTianLib.riemannianMeasure (I := I) g μ)
  calc
    (MorganTianLib.riemannianMeasure (I := I) g μ).withDensity
          (fun p ↦ (((MorganTianLib.riemannianMeasure (I := I) h μ).rnDeriv
            (MorganTianLib.riemannianMeasure (I := I) g μ) p).toNNReal : ENNReal)) =
        (MorganTianLib.riemannianMeasure (I := I) g μ).withDensity
          ((MorganTianLib.riemannianMeasure (I := I) h μ).rnDeriv
            (MorganTianLib.riemannianMeasure (I := I) g μ)) := by
      exact withDensity_congr_ae <| htop.mono fun p hp ↦ ENNReal.coe_toNNReal hp
    _ = MorganTianLib.riemannianMeasure (I := I) h μ :=
      riemannianMeasure_eq_withDensity_rnDeriv g h μ

/-- **Math.** The `NNReal` Radon--Nikodym density of a metric family relative to a fixed
reference metric and Haar base. -/
def riemannianMeasure_rnDensity
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (μ : Measure E) : ℝ → M → NNReal := fun t p ↦
  ((MorganTianLib.riemannianMeasure (I := I) (g t) μ).rnDeriv
    (MorganTianLib.riemannianMeasure (I := I) g₀ μ) p).toNNReal

set_option linter.unusedSectionVars false in
/-- **Math.** The fixed-reference `NNReal` density is measurable at each time. -/
theorem measurable_riemannianMeasure_rnDensity
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (μ : Measure E) (t : ℝ) :
    Measurable (riemannianMeasure_rnDensity (I := I) g₀ g μ t) := by
  unfold riemannianMeasure_rnDensity
  exact (Measure.measurable_rnDeriv _ _).ennreal_toNNReal

set_option linter.unusedSectionVars false in
/-- **Math.** Every member of a metric family is represented by the fixed-reference
density, in the form consumed by the weighted-density bridge. -/
theorem riemannianMeasure_eq_withDensity_rnDensity_family
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∀ t, (MorganTianLib.riemannianMeasure (I := I) g₀ μ).withDensity
        (fun p ↦ (riemannianMeasure_rnDensity (I := I) g₀ g μ t p : ENNReal)) =
      MorganTianLib.riemannianMeasure (I := I) (g t) μ := by
  intro t
  exact riemannianMeasure_eq_withDensity_rnDensity g₀ (g t) μ

#print axioms Topping.riemannianMeasure_absolutelyContinuous
#print axioms Topping.riemannianMeasure_mutuallyAbsolutelyContinuous
#print axioms Topping.riemannianMeasure_eq_withDensity_rnDeriv
#print axioms Topping.riemannianMeasure_eq_withDensity_rnDensity
#print axioms Topping.measurable_riemannianMeasure_rnDensity
#print axioms Topping.riemannianMeasure_eq_withDensity_rnDensity_family

end Topping

end
