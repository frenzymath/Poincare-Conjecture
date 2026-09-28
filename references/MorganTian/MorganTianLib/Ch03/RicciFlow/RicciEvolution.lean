import MorganTianLib.Ch03.RicciFlow.ScalarTraceEvolution

/-!
# The covariant Ricci evolution in fixed coordinates

This file lowers the upper index in the covariant derivative of the Ricci-flow
connection variation and identifies the result with the corrected second
covariant derivatives of the Ricci tensor.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian Riemannian.Tensor Filter

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

set_option maxHeartbeats 1600000 in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
private theorem lowered_covariantDerivativeConnectionVariation
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha : M)
    (r i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target)
    (hδ : ∀ a b c : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (chartChristoffelVariationOnE (I := I) g h t alpha a b c) y) :
    (∑ k, chartCovariantDerivativeConnectionVariationOnE
        (I := I) g h t alpha r i j k y *
      chartGramOnE (I := I) (g t) alpha k l y) =
      partialDeriv (E := E) r
          (fun z => ∑ k,
            chartChristoffelVariationOnE (I := I) g h t alpha i j k z *
              chartGramOnE (I := I) (g t) alpha k l z) y
        - ∑ s, chartChristoffel (I := I) (g t) alpha r l s y *
            ∑ k, chartChristoffelVariationOnE
              (I := I) g h t alpha i j k y *
              chartGramOnE (I := I) (g t) alpha k s y
        - ∑ s, chartChristoffel (I := I) (g t) alpha r i s y *
            ∑ k, chartChristoffelVariationOnE
              (I := I) g h t alpha s j k y *
              chartGramOnE (I := I) (g t) alpha k l y
        - ∑ s, chartChristoffel (I := I) (g t) alpha r j s y *
            ∑ k, chartChristoffelVariationOnE
              (I := I) g h t alpha i s k y *
              chartGramOnE (I := I) (g t) alpha k l y := by
  classical
  have htarget_mem : (extChartAt I alpha).target ∈ 𝓝 y :=
    (isOpen_extChartAt_target alpha).mem_nhds hy
  have hsource : (extChartAt I alpha).symm y ∈
      (extChartAt I alpha).source :=
    (extChartAt I alpha).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  have hbase : (extChartAt I alpha).symm y ∈
      (trivializationAt E (TangentSpace I) alpha).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hgram (a b : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ (chartGramOnE (I := I) (g t) alpha a b) y :=
    ((chartGramOnE_contDiffOn (I := I) (g t) alpha a b).contDiffAt
      htarget_mem).differentiableAt (by norm_num)
  have hmul (a b c : Fin (Module.finrank ℝ E)) :
      partialDeriv (E := E) r
          (fun z => chartChristoffelVariationOnE
            (I := I) g h t alpha a b c z *
            chartGramOnE (I := I) (g t) alpha c l z) y =
        partialDeriv (E := E)
            r (chartChristoffelVariationOnE
              (I := I) g h t alpha a b c) y *
            chartGramOnE (I := I) (g t) alpha c l y +
          chartChristoffelVariationOnE
            (I := I) g h t alpha a b c y *
            partialDeriv (E := E)
              r (chartGramOnE (I := I) (g t) alpha c l) y := by
    unfold partialDeriv
    rw [fderiv_fun_mul (hδ a b c) (hgram c l)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hsum :
      partialDeriv (E := E) r
          (fun z => ∑ k,
            chartChristoffelVariationOnE (I := I) g h t alpha i j k z *
              chartGramOnE (I := I) (g t) alpha k l z) y =
        ∑ k, (partialDeriv (E := E) r
              (chartChristoffelVariationOnE
                (I := I) g h t alpha i j k) y *
              chartGramOnE (I := I) (g t) alpha k l y +
            chartChristoffelVariationOnE
              (I := I) g h t alpha i j k y *
              partialDeriv (E := E)
                r (chartGramOnE (I := I) (g t) alpha k l) y) := by
    unfold partialDeriv
    rw [fderiv_fun_sum]
    · rw [sum_apply]
      exact Finset.sum_congr rfl fun k _ => hmul i j k
    · intro k hk
      exact (hδ i j k).mul (hgram k l)
  rw [hsum]
  unfold chartCovariantDerivativeConnectionVariationOnE
  have hcompat (a b c : Fin (Module.finrank ℝ E)) :
      partialDeriv (E := E) c (chartGramOnE (I := I) (g t) alpha a b) y =
        ∑ m, (chartGramOnE (I := I) (g t) alpha m b y *
            chartChristoffel (I := I) (g t) alpha c a m y +
          chartGramOnE (I := I) (g t) alpha a m y *
            chartChristoffel (I := I) (g t) alpha c b m y) :=
    partialDeriv_chartGramOnE_eq (I := I) (g t) alpha a b c y hbase
  have hswap :
      (∑ k, (∑ s, chartChristoffel (I := I) (g t) alpha r s k y *
          chartChristoffelVariationOnE
            (I := I) g h t alpha i j s y) *
        chartGramOnE (I := I) (g t) alpha k l y) =
        ∑ k, chartChristoffelVariationOnE
            (I := I) g h t alpha i j k y *
          ∑ s, chartGramOnE (I := I) (g t) alpha s l y *
            chartChristoffel (I := I) (g t) alpha r k s y := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc, mul_comm]
  have hi :
      (∑ k, (∑ s, chartChristoffel (I := I) (g t) alpha r i s y *
          chartChristoffelVariationOnE
            (I := I) g h t alpha s j k y) *
        chartGramOnE (I := I) (g t) alpha k l y) =
        ∑ k, ∑ s, chartChristoffel (I := I) (g t) alpha r i k y *
          chartChristoffelVariationOnE
            (I := I) g h t alpha k j s y *
            chartGramOnE (I := I) (g t) alpha s l y := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hj :
      (∑ k, (∑ s, chartChristoffel (I := I) (g t) alpha r j s y *
          chartChristoffelVariationOnE
            (I := I) g h t alpha i s k y) *
        chartGramOnE (I := I) (g t) alpha k l y) =
        ∑ k, ∑ s, chartChristoffel (I := I) (g t) alpha r j k y *
          chartChristoffelVariationOnE
            (I := I) g h t alpha i k s y *
            chartGramOnE (I := I) (g t) alpha s l y := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hmetric :
      (∑ k, chartChristoffelVariationOnE
          (I := I) g h t alpha i j k y *
        ∑ s, chartGramOnE (I := I) (g t) alpha k s y *
          chartChristoffel (I := I) (g t) alpha r l s y) =
        ∑ k, ∑ s, chartChristoffelVariationOnE
            (I := I) g h t alpha i j k y *
          chartChristoffel (I := I) (g t) alpha r l s y *
          chartGramOnE (I := I) (g t) alpha k s y := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hmetric2 :
      (∑ k, ∑ s, chartChristoffelVariationOnE
          (I := I) g h t alpha i j k y *
          chartChristoffel (I := I) (g t) alpha r l s y *
          chartGramOnE (I := I) (g t) alpha k s y) =
        ∑ s, chartChristoffel (I := I) (g t) alpha r l s y *
          ∑ k, chartChristoffelVariationOnE
            (I := I) g h t alpha i j k y *
            chartGramOnE (I := I) (g t) alpha k s y := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hcompat]
  simp only [add_mul, sub_mul, mul_add, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [hswap, hi, hj, hmetric, hmetric2]
  simp only [Finset.mul_sum]
  simp only [mul_assoc]
  ring_nf

private theorem lowered_chartChristoffelVariation_neg_two_ricci
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ k, chartChristoffelVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z)
        t alpha i j k y * chartGramOnE (I := I) (g t) alpha k l y) =
      - (chartCovRicciOnE (I := I) (g t) alpha i l j y +
          chartCovRicciOnE (I := I) (g t) alpha j l i y -
          chartCovRicciOnE (I := I) (g t) alpha l i j y) := by
  classical
  have hsource : (extChartAt I alpha).symm y ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hbase : (extChartAt I alpha).symm y ∈
      (trivializationAt E (TangentSpace I) alpha).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hGinvG (a : Fin (Module.finrank ℝ E)) :
      (∑ k, chartInvGramOnE (I := I) (g t) alpha a k y *
        chartGramOnE (I := I) (g t) alpha k l y) =
        if a = l then (1 : ℝ) else 0 := by
    have h :
        (∑ k, chartInvGramOnE (I := I) (g t) alpha a k y *
          chartGramOnE (I := I) (g t) alpha k l y) =
          (chartInvGramMatrix (I := I) (g t) alpha
            ((extChartAt I alpha).symm y) *
           chartGramMatrix (I := I) (g t) alpha
            ((extChartAt I alpha).symm y)) a l := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by
        rw [chartInvGramOnE_def, chartGramOnE_def]
    rw [h, chartInvGramMatrix_mul_chartGramMatrix
      (I := I) (g t) alpha hbase, Matrix.one_apply]
  let C : Fin (Module.finrank ℝ E) → ℝ := fun a =>
    chartCovRicciOnE (I := I) (g t) alpha i a j y +
      chartCovRicciOnE (I := I) (g t) alpha j a i y -
      chartCovRicciOnE (I := I) (g t) alpha a i j y
  simp_rw [chartChristoffelVariationOnE_neg_two_ricci_eq_covRicci
    g t alpha i j _ hy]
  change (∑ k, (-∑ a, chartInvGramOnE (I := I) (g t) alpha k a y * C a) *
      chartGramOnE (I := I) (g t) alpha k l y) = - C l
  calc
    (∑ k, (-∑ a, chartInvGramOnE (I := I) (g t) alpha k a y * C a) *
        chartGramOnE (I := I) (g t) alpha k l y) =
      - ∑ a, (∑ k, chartInvGramOnE (I := I) (g t) alpha a k y *
        chartGramOnE (I := I) (g t) alpha k l y) * C a := by
      simp only [neg_mul, Finset.sum_neg_distrib]
      congr 1
      calc
        (∑ k, (∑ a, chartInvGramOnE (I := I) (g t) alpha k a y * C a) *
            chartGramOnE (I := I) (g t) alpha k l y) =
          ∑ k, ∑ a, chartInvGramOnE (I := I) (g t) alpha k a y * C a *
            chartGramOnE (I := I) (g t) alpha k l y := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.sum_mul]
        _ = ∑ a, ∑ k, chartInvGramOnE (I := I) (g t) alpha a k y *
            chartGramOnE (I := I) (g t) alpha k l y * C a := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro k hk
              rw [chartInvGramOnE_symm (g t) alpha hy k a]
              ring
        _ = ∑ a, (∑ k, chartInvGramOnE (I := I) (g t) alpha a k y *
            chartGramOnE (I := I) (g t) alpha k l y) * C a := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.sum_mul]
    _ = - C l := by
      rw [Finset.sum_eq_single l]
      · rw [hGinvG]
        simp
      · intro b hb hbl
        rw [hGinvG]
        simp [hbl]
      · simp

/-- **Math.** The chart component of the corrected second covariant derivative
`(nabla^2_{r,a} Ric)_{bc}`: differentiate the `nabla Ric` component and subtract
the Christoffel action in the derivative slot and both Ricci tensor slots. -/
noncomputable def chartSecondCovRicciOnE
    (g : RiemannianMetric I M) (alpha : M)
    (r a b c : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) r (chartCovRicciOnE (I := I) g alpha a b c) y
    - ∑ s, chartChristoffel g alpha r a s y *
        chartCovRicciOnE g alpha s b c y
    - ∑ s, chartChristoffel g alpha r b s y *
        chartCovRicciOnE g alpha a s c y
    - ∑ s, chartChristoffel g alpha r c s y *
        chartCovRicciOnE g alpha a b s y

set_option maxHeartbeats 1600000 in
/-- **Math.** The lowered covariant derivative of the genuine Ricci-flow
connection variation is the three-term corrected Ricci Hessian combination
`-nabla^2_{r,i} Ric_{lj} - nabla^2_{r,j} Ric_{li}
+ nabla^2_{r,l} Ric_{ij}`. -/
theorem sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_mul_chartGram_eq
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (r i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ k, chartCovariantDerivativeConnectionVariationOnE
        (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z)
        t alpha r i j k y * chartGramOnE (I := I) (g t) alpha k l y) =
      -chartSecondCovRicciOnE (I := I) (g t) alpha r i l j y
        - chartSecondCovRicciOnE (I := I) (g t) alpha r j l i y
        + chartSecondCovRicciOnE (I := I) (g t) alpha r l i j y := by
  classical
  have htarget : (extChartAt I alpha).target ∈ 𝓝 y :=
    (isOpen_extChartAt_target alpha).mem_nhds hy
  have hdelta (a b c : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ
        (chartChristoffelVariationOnE (I := I) g
          (fun s p x z => -2 * ricciTensorAt (g s) p x z)
          t alpha a b c) y :=
    ((chartChristoffelVariationOnE_neg_two_ricci_contDiffOn
      g t alpha a b c).contDiffAt htarget).differentiableAt (by norm_num)
  have hC (a b c : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ
        (chartCovRicciOnE (I := I) (g t) alpha a b c) y :=
    ((chartCovRicciOnE_contDiffOn
      (I := I) (g t) alpha a b c).contDiffAt htarget).differentiableAt
        (by norm_num)
  have hpartial_add {u v : E → ℝ}
      (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
      partialDeriv (E := E) r (fun z => u z + v z) y =
        partialDeriv (E := E) r u y + partialDeriv (E := E) r v y := by
    unfold partialDeriv
    rw [fderiv_fun_add hu hv, add_apply]
  have hpartial_sub {u v : E → ℝ}
      (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
      partialDeriv (E := E) r (fun z => u z - v z) y =
        partialDeriv (E := E) r u y - partialDeriv (E := E) r v y := by
    unfold partialDeriv
    rw [fderiv_fun_sub hu hv, sub_apply]
  have hpartial_neg {u : E → ℝ} :
      partialDeriv (E := E) r (fun z => -u z) y =
        -partialDeriv (E := E) r u y := by
    unfold partialDeriv
    rw [show (fun z => -u z) = -u by rfl, fderiv_neg, neg_apply]
  let C₁ : E → ℝ :=
    chartCovRicciOnE (I := I) (g t) alpha i l j
  let C₂ : E → ℝ :=
    chartCovRicciOnE (I := I) (g t) alpha j l i
  let C₃ : E → ℝ :=
    chartCovRicciOnE (I := I) (g t) alpha l i j
  have hC₁ : DifferentiableAt ℝ C₁ y := hC i l j
  have hC₂ : DifferentiableAt ℝ C₂ y := hC j l i
  have hC₃ : DifferentiableAt ℝ C₃ y := hC l i j
  have hlowerNear :
      (fun z => ∑ k,
          chartChristoffelVariationOnE (I := I) g
              (fun s p x w => -2 * ricciTensorAt (g s) p x w)
              t alpha i j k z *
            chartGramOnE (I := I) (g t) alpha k l z) =ᶠ[𝓝 y]
        (fun z => -(C₁ z + C₂ z - C₃ z)) := by
    filter_upwards [htarget] with z hz
    exact lowered_chartChristoffelVariation_neg_two_ricci
      g t alpha i j l hz
  have hpartialLower := partialDeriv_congr_of_eventuallyEq hlowerNear r
  have hpartial :
      partialDeriv (E := E) r (fun z => -(C₁ z + C₂ z - C₃ z)) y =
        -(partialDeriv (E := E) r C₁ y + partialDeriv (E := E) r C₂ y -
          partialDeriv (E := E) r C₃ y) := by
    rw [hpartial_neg,
      hpartial_sub (u := fun z => C₁ z + C₂ z) (v := C₃)
        (hC₁.add hC₂) hC₃,
      hpartial_add hC₁ hC₂]
  have hsum_three (A B C : Fin (Module.finrank ℝ E) → ℝ) :
      (∑ x, (-A x - B x + C x)) =
        -(∑ x, A x) - ∑ x, B x + ∑ x, C x := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib]
  rw [lowered_covariantDerivativeConnectionVariation
    g (fun s p x z => -2 * ricciTensorAt (g s) p x z)
      t alpha r i j l hy hdelta]
  rw [hpartialLower, hpartial]
  simp_rw [lowered_chartChristoffelVariation_neg_two_ricci
    g t alpha _ _ _ hy]
  simp only [chartSecondCovRicciOnE, C₁, C₂, C₃]
  ring_nf
  simp_rw [hsum_three]
  ring

#print axioms
  MorganTianLib.sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_mul_chartGram_eq

end MorganTianLib

end
