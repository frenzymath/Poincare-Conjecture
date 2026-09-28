import MorganTianLib.Ch01.RiemannianMeasure

/-!
# Morgan--Tian Ch. 1: global comparison of Riemannian measures

`RiemannianMeasure.lean` gives the coordinate formula on a set contained in a
single chart.  This file performs the countable-atlas step which is needed when
the measured set is not contained in one chart: split it by the canonical
`chartPiece` partition, compare the chart integrals piecewise, and sum.

The pointwise hypothesis is deliberately stated for every chart and every
coordinate in the preimage of the measured set.  Thus a caller can supply a
geometric chart-density estimate without making any choice of the atlas used
internally by `riemannianMeasure`.
-/

open MeasureTheory Measure Set Filter Function
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

/-- **Math.** Pointwise comparison of the coordinate volume densities in every chart
induces the corresponding comparison of the global Riemannian measures on an
arbitrary measurable set.  The proof explicitly sums over the disjoint chart
partition underlying `riemannianMeasure`; no global atlas comparison is hidden
in the hypotheses.

The constants are real and nonnegative so that the `ENNReal.ofReal` factors
represent the intended scalar inequalities. -/
theorem riemannianMeasure_global_chartDensity_comparison
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g₀ g₁ : RiemannianMetric I M} {s : Set M}
    (hs : MeasurableSet s)
    {Cminus Cplus : ℝ} (hCminus : 0 ≤ Cminus) (hCplus : 0 ≤ Cplus)
    (hpoint : ∀ (alpha : M) (y : E),
      y ∈ chartPreimage (I := I) alpha s →
        Cminus * chartVolumeDensity (I := I) g₀ alpha y ≤
            chartVolumeDensity (I := I) g₁ alpha y ∧
          chartVolumeDensity (I := I) g₁ alpha y ≤
            Cplus * chartVolumeDensity (I := I) g₀ alpha y) :
    ENNReal.ofReal Cminus * riemannianMeasure (I := I) g₀ mu s ≤
        riemannianMeasure (I := I) g₁ mu s ∧
      riemannianMeasure (I := I) g₁ mu s ≤
        ENNReal.ofReal Cplus * riemannianMeasure (I := I) g₀ mu s := by
  classical
  let P : ℕ → Set M := chartPiece (I := I) (M := M)
  let alpha : ℕ → M := chartCover (I := I) (M := M)
  let S : ℕ → Set M := fun n => s ∩ P n
  have hSmeas : ∀ n, MeasurableSet (S n) := by
    intro n
    exact hs.inter (measurableSet_chartPiece (I := I) (M := M) n)
  have hSsub : ∀ n, S n ⊆ (extChartAt I (alpha n)).source := by
    intro n x hx
    exact chartPiece_subset (I := I) (M := M) n hx.2
  have hSdisj : Pairwise (Disjoint on S) := by
    intro m n hmn
    exact (pairwise_disjoint_chartPiece (I := I) (M := M) hmn).mono
      inter_subset_right inter_subset_right
  have hSunion : (⋃ n, S n) = s := by
    dsimp [S]
    rw [← inter_iUnion, iUnion_chartPiece (I := I) (M := M), inter_univ]
  have hqsub (n : ℕ) :
      chartPreimage (I := I) (alpha n) (S n) ⊆
        chartPreimage (I := I) (alpha n) s := by
    intro y hy
    exact ⟨hy.1.1, hy.2⟩
  have hlow_term : ∀ n : ℕ,
      ENNReal.ofReal Cminus *
          ((chartMeasure (I := I) g₀ mu (alpha n)).restrict (P n)) s ≤
        ((chartMeasure (I := I) g₁ mu (alpha n)).restrict (P n)) s := by
    intro n
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
      chartMeasure_apply mu g₀ (alpha n) (hSmeas n),
      chartMeasure_apply mu g₁ (alpha n) (hSmeas n)]
    let q := chartPreimage (I := I) (alpha n) (S n)
    have hq : MeasurableSet q := measurableSet_chartPreimage (I := I) (alpha n) (hSmeas n)
    calc
      ENNReal.ofReal Cminus *
          (∫⁻ y in q, ENNReal.ofReal
            (chartVolumeDensity (I := I) g₀ (alpha n) y) ∂mu) =
        ∫⁻ y in q, ENNReal.ofReal Cminus * ENNReal.ofReal
            (chartVolumeDensity (I := I) g₀ (alpha n) y) ∂mu := by
          rw [← lintegral_const_mul' (μ := mu.restrict q) (ENNReal.ofReal Cminus)
            (f := fun y : E => ENNReal.ofReal
              (chartVolumeDensity (I := I) g₀ (alpha n) y)) ENNReal.ofReal_ne_top]
      _ = ∫⁻ y in q, ENNReal.ofReal
          (Cminus * chartVolumeDensity (I := I) g₀ (alpha n) y) ∂mu := by
        apply setLIntegral_congr_fun hq
        intro y hy
        change ENNReal.ofReal Cminus * ENNReal.ofReal
            (chartVolumeDensity (I := I) g₀ (alpha n) y) =
          ENNReal.ofReal
            (Cminus * chartVolumeDensity (I := I) g₀ (alpha n) y)
        exact (ENNReal.ofReal_mul hCminus).symm
      _ ≤ ∫⁻ y in q, ENNReal.ofReal
          (chartVolumeDensity (I := I) g₁ (alpha n) y) ∂mu := by
        apply setLIntegral_mono' hq
        intro y hy
        exact ENNReal.ofReal_le_ofReal
          ((hpoint (alpha n) y (hqsub n hy)).1)
  have hupp_term : ∀ n : ℕ,
      ((chartMeasure (I := I) g₁ mu (alpha n)).restrict (P n)) s ≤
        ENNReal.ofReal Cplus *
          ((chartMeasure (I := I) g₀ mu (alpha n)).restrict (P n)) s := by
    intro n
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
      chartMeasure_apply mu g₁ (alpha n) (hSmeas n),
      chartMeasure_apply mu g₀ (alpha n) (hSmeas n)]
    let q := chartPreimage (I := I) (alpha n) (S n)
    have hq : MeasurableSet q := measurableSet_chartPreimage (I := I) (alpha n) (hSmeas n)
    calc
      (∫⁻ y in q, ENNReal.ofReal
          (chartVolumeDensity (I := I) g₁ (alpha n) y) ∂mu) ≤
        ∫⁻ y in q, ENNReal.ofReal
          (Cplus * chartVolumeDensity (I := I) g₀ (alpha n) y) ∂mu := by
        apply setLIntegral_mono' hq
        intro y hy
        exact ENNReal.ofReal_le_ofReal
          ((hpoint (alpha n) y (hqsub n hy)).2)
      _ = ∫⁻ y in q, ENNReal.ofReal Cplus * ENNReal.ofReal
          (chartVolumeDensity (I := I) g₀ (alpha n) y) ∂mu := by
        apply setLIntegral_congr_fun hq
        intro y hy
        change ENNReal.ofReal
            (Cplus * chartVolumeDensity (I := I) g₀ (alpha n) y) =
          ENNReal.ofReal Cplus * ENNReal.ofReal
            (chartVolumeDensity (I := I) g₀ (alpha n) y)
        exact ENNReal.ofReal_mul hCplus
      _ = ENNReal.ofReal Cplus *
          (∫⁻ y in q, ENNReal.ofReal
            (chartVolumeDensity (I := I) g₀ (alpha n) y) ∂mu) := by
        rw [lintegral_const_mul' (μ := mu.restrict q) (ENNReal.ofReal Cplus)
          (f := fun y : E => ENNReal.ofReal
            (chartVolumeDensity (I := I) g₀ (alpha n) y)) ENNReal.ofReal_ne_top]
  have hsum₀ :
      riemannianMeasure (I := I) g₀ mu s =
        ∑' n, ((chartMeasure (I := I) g₀ mu (alpha n)).restrict (P n)) s := by
    simpa [riemannianMeasure, alpha, P] using
      (Measure.sum_apply
        (fun n =>
          (chartMeasure (I := I) g₀ mu
            (chartCover (I := I) (M := M) n)).restrict
              (chartPiece (I := I) (M := M) n)) hs)
  have hsum₁ :
      riemannianMeasure (I := I) g₁ mu s =
        ∑' n, ((chartMeasure (I := I) g₁ mu (alpha n)).restrict (P n)) s := by
    simpa [riemannianMeasure, alpha, P] using
      (Measure.sum_apply
        (fun n =>
          (chartMeasure (I := I) g₁ mu
            (chartCover (I := I) (M := M) n)).restrict
              (chartPiece (I := I) (M := M) n)) hs)
  constructor
  · rw [hsum₀]
    calc
      ENNReal.ofReal Cminus *
          (∑' n, ((chartMeasure (I := I) g₀ mu (alpha n)).restrict (P n)) s) =
        ∑' n, ENNReal.ofReal Cminus *
          ((chartMeasure (I := I) g₀ mu (alpha n)).restrict (P n)) s := by
            rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' n, ((chartMeasure (I := I) g₁ mu (alpha n)).restrict (P n)) s :=
        ENNReal.tsum_le_tsum hlow_term
      _ = riemannianMeasure (I := I) g₁ mu s := by
        exact hsum₁.symm
  · rw [hsum₁]
    calc
      ∑' n, ((chartMeasure (I := I) g₁ mu (alpha n)).restrict (P n)) s ≤
        ∑' n, ENNReal.ofReal Cplus *
          ((chartMeasure (I := I) g₀ mu (alpha n)).restrict (P n)) s :=
        ENNReal.tsum_le_tsum hupp_term
      _ = ENNReal.ofReal Cplus *
          (∑' n, ((chartMeasure (I := I) g₀ mu (alpha n)).restrict (P n)) s) := by
            rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal Cplus * riemannianMeasure (I := I) g₀ mu s := by
            rw [hsum₀]

end MorganTianLib

end

#print axioms MorganTianLib.riemannianMeasure_global_chartDensity_comparison
