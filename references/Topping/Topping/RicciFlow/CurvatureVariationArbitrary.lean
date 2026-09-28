import Topping.RicciFlow.CurvatureVariationIntrinsic

/-!
# Arbitrary-vector Ricci-flow curvature variation

The fixed-chart component producer is lifted to arbitrary tangent vectors by
the pointwise four-linear expansion.  The chart inverse is named explicitly
to keep dependent tangent-space rewrites transparent to Lean.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian Riemannian.Geodesic Filter

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The chart expression for Ricci-flow curvature variation agrees
with the intrinsic four-linear tensor on every four tangent vectors in a chart.
-/
theorem chartRiemannVariationAt_neg_two_ricci_eq_intrinsic
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha p : M)
    (x y z w : TangentSpace I p)
    (hp : p ∈ (chartAt H alpha).source) :
    chartRiemannVariationAt (I := I) g
        (fun s q u v => -2 * ricciTensorAt (g s) q u v)
        t alpha p x y z w =
      pointwiseValue (ricciFlowRiemannVariationIntrinsic (g t)) p
        ![x, y, z, w] := by
  classical
  let e : Fin (Module.finrank ℝ E) → TangentSpace I p :=
    fun i => Tensor.chartBasisVecFiber (I := I) alpha i p
  have hp' : p ∈ (extChartAt I alpha).source := by
    simpa only [extChartAt_source] using hp
  have hy : extChartAt I alpha p ∈ (extChartAt I alpha).target :=
    (extChartAt I alpha).map_source hp'
  set q : M := (extChartAt I alpha).symm (extChartAt I alpha p) with hq
  have hqp : q = p := by
    rw [hq]
    exact (extChartAt I alpha).left_inv hp'
  obtain ⟨X, hX, hbasis⟩ :=
    exists_chartFrame_chartRiemannBasisVariation_neg_two_ricci_eq_intrinsic
      g t alpha hy
  change (∀ i, ∀ᶠ r in 𝓝 q,
    X i r = Tensor.chartBasisVecFiber (I := I) alpha i r) at hX
  change (∀ i j k l,
    chartRiemannBasisVariation (I := I) g
      (fun s r u v => -2 * MorganTianLib.ricciTensorAt (g s) r u v)
      t alpha q i j k l =
      ricciTensorAt (g t) q
          (curvatureOperator (g t) (X i) (X j) (X l) q) (X k q)
        - ricciTensorAt (g t) q
          (curvatureOperator (g t) (X i) (X j) (X k) q) (X l q)
        - secondCovDerivAlong (g t).leviCivitaConnection (X j) (X k)
          (ricciTensorField (g t)) ![X i, X l] q
        + secondCovDerivAlong (g t).leviCivitaConnection (X i) (X k)
          (ricciTensorField (g t)) ![X j, X l] q
        - secondCovDerivAlong (g t).leviCivitaConnection (X i) (X l)
          (ricciTensorField (g t)) ![X j, X k] q
        + secondCovDerivAlong (g t).leviCivitaConnection (X j) (X l)
          (ricciTensorField (g t)) ![X i, X k] q) at hbasis
  rw [hqp] at hX hbasis
  have hXval (i : Fin (Module.finrank ℝ E)) :
      X i p = e i := (hX i).self_of_nhds
  have hA :=
    isPointwiseMultilinear_ricciFlowRiemannVariationIntrinsic (g t) p
  have heq (i j k l : Fin (Module.finrank ℝ E)) :
      chartRiemannBasisVariation (I := I) g
          (fun s r u v => -2 * MorganTianLib.ricciTensorAt (g s) r u v)
          t alpha p i j k l =
        pointwiseValue (ricciFlowRiemannVariationIntrinsic (g t)) p
          ![e i, e j, e k, e l] := by
    rw [hbasis i j k l]
    have hpoint :=
      pointwiseValue_eq hA.tensorial ![X i, X j, X k, X l]
    change pointwiseValue (ricciFlowRiemannVariationIntrinsic (g t)) p
        ![X i p, X j p, X k p, X l p] =
      ricciFlowRiemannVariationIntrinsic (g t) ![X i, X j, X k, X l] p at hpoint
    rw [hXval i, hXval j, hXval k, hXval l,
      ricciFlowRiemannVariationIntrinsic_apply] at hpoint
    exact hpoint.symm
  rw [pointwiseValue_eq_chartBasis_sum_four hA alpha x y z w hp]
  change
    (∑ i, chartTangentCoeff (I := I) alpha p i x *
      ∑ j, chartTangentCoeff (I := I) alpha p j y *
        ∑ k, chartTangentCoeff (I := I) alpha p k z *
          ∑ l, chartTangentCoeff (I := I) alpha p l w *
            chartRiemannBasisVariation (I := I) g
              (fun s q u v => -2 * ricciTensorAt (g s) q u v)
              t alpha p i j k l) =
      ∑ i, chartTangentCoeff (I := I) alpha p i x *
        ∑ j, chartTangentCoeff (I := I) alpha p j y *
          ∑ k, chartTangentCoeff (I := I) alpha p k z *
            ∑ l, chartTangentCoeff (I := I) alpha p l w *
              pointwiseValue (ricciFlowRiemannVariationIntrinsic (g t)) p
                ![e i, e j, e k, e l]
  have heq' (i j k l : Fin (Module.finrank ℝ E)) :
      chartRiemannBasisVariation (I := I) g
          (fun s r u v => -2 * ricciTensorAt (g s) r u v)
          t alpha p i j k l =
        pointwiseValue (ricciFlowRiemannVariationIntrinsic (g t)) p
          ![e i, e j, e k, e l] := by
    simpa only [mtRicciTensorAt_eq_ricciTensorAt] using heq i j k l
  simp_rw [heq']

/-- **Math.** A Ricci flow genuinely witnesses Topping's full intrinsic
first-variation formula for the Riemann tensor at every interior time. -/
theorem hasRiemannVariationOn_interior_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) :
    HasRiemannVariationOn g
      (fun s q (u v : TangentSpace I q) => -2 * ricciTensorAt (g s) q u v)
      (interior J) := by
  intro t ht X Y W Z p
  have hd :=
    hasDerivAt_riemannCurvatureAt_selfChart_of_isRicciFlowOn
      hflow p (X p) (Y p) (W p) (Z p) ht
  rw [chartRiemannVariationAt_neg_two_ricci_eq_intrinsic
    g t p p (X p) (Y p) (W p) (Z p) (mem_chart_source H p)] at hd
  have hpoint := pointwiseValue_eq
    (isPointwiseMultilinear_ricciFlowRiemannVariationIntrinsic
      (g t) p).tensorial ![X, Y, W, Z]
  change pointwiseValue (ricciFlowRiemannVariationIntrinsic (g t)) p
      ![X p, Y p, W p, Z p] =
    ricciFlowRiemannVariationIntrinsic (g t) ![X, Y, W, Z] p at hpoint
  rw [hpoint, ricciFlowRiemannVariationIntrinsic_apply] at hd
  have hsecond (A B C D : SmoothVectorField I M) :
      secondCovDerivAlong (g t).leviCivitaConnection A B
          (covTensorOfBilin
            (fun q (u v : TangentSpace I q) => -2 * ricciTensorAt (g t) q u v))
          (fun i => if i = 0 then C else D) p =
        -2 * secondCovDerivAlong (g t).leviCivitaConnection A B
          (ricciTensorField (g t)) ![C, D] p := by
    rw [covTensorOfBilin_neg_two_ricci,
      secondCovDerivAlong_const_mul (g t).leviCivitaConnection A B (-2)
        (hasSmoothComponents_ricciTensorField (g t))]
    congr 2
    funext i
    fin_cases i <;> simp
  simp only [hsecond]
  exact hd.hasDerivWithinAt.congr_deriv (by ring)

/-! The coordinate derivative is smooth on the full flow time set.  Extend the
interior identity across the boundary using the convex-time-set closure. -/

/-- **Math.** A Ricci flow witnesses Topping's arbitrary-vector Riemann
first-variation formula on its whole prescribed time set. -/
theorem hasRiemannVariationOn_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) :
    HasRiemannVariationOn g
      (fun s q (u v : TangentSpace I q) => -2 * ricciTensorAt (g s) q u v) J := by
  intro t ht X Y W Z p
  let f : ℝ → ℝ := fun s =>
    riemannCurvatureAt (g s) p (X p) (Y p) (W p) (Z p)
  let rhs : ℝ → ℝ := fun s =>
    chartRiemannVariationAt (I := I) g
      (fun u q a b => -2 * ricciTensorAt (g u) q a b)
      s p p (X p) (Y p) (W p) (Z p)
  have hf : ContDiffOn ℝ ∞ f J := by
    simpa only [f] using
      contDiffOn_riemannCurvatureAt_timeSlice_of_isSmoothMetricFamilyOn
        hflow.smooth p (X p) (Y p) (W p) (Z p)
  have hrhs : ContDiffOn ℝ ∞ rhs J := by
    simpa only [rhs] using
      contDiffOn_chartRiemannVariationAt_neg_two_ricci_timeSlice
        hflow.smooth p (X p) (Y p) (W p) (Z p)
  have hconv : Convex ℝ J := hflow.ordConnected.convex
  have hinterior : (interior J).Nonempty :=
    hconv.nontrivial_iff_nonempty_interior.mp hflow.nontrivial
  have hunique : UniqueDiffOn ℝ J := uniqueDiffOn_convex hconv hinterior
  have hclosure : J ⊆ closure (interior J) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hinterior]
    exact subset_closure
  have heqInterior : Set.EqOn (derivWithin f J) rhs (interior J) := by
    intro s hs
    have hderivAt :=
      hasDerivAt_riemannCurvatureAt_selfChart_of_isRicciFlowOn
        hflow p (X p) (Y p) (W p) (Z p) hs
    have hderivWithin : HasDerivWithinAt f (rhs s) J s := by
      simpa only [f, rhs] using hderivAt.hasDerivWithinAt
    exact hderivWithin.derivWithin
      (hunique.uniqueDiffWithinAt (interior_subset hs))
  have heq : Set.EqOn (derivWithin f J) rhs J :=
    heqInterior.of_subset_closure
      (hf.continuousOn_derivWithin hunique (by simp))
      hrhs.continuousOn interior_subset hclosure
  have hdiff : DifferentiableWithinAt ℝ f J t :=
    (hf t ht).differentiableWithinAt (by simp)
  have hderiv' : HasDerivWithinAt
      (fun s => riemannCurvatureAt (g s) p (X p) (Y p) (W p) (Z p))
      (chartRiemannVariationAt (I := I) g
        (fun u q a b => -2 * ricciTensorAt (g u) q a b)
        t p p (X p) (Y p) (W p) (Z p)) J t := by
    simpa only [f, rhs] using hdiff.hasDerivWithinAt.congr_deriv (heq ht)
  rw [chartRiemannVariationAt_neg_two_ricci_eq_intrinsic
    g t p p (X p) (Y p) (W p) (Z p) (mem_chart_source H p)] at hderiv'
  have hpoint := pointwiseValue_eq
    (isPointwiseMultilinear_ricciFlowRiemannVariationIntrinsic
      (g t) p).tensorial ![X, Y, W, Z]
  change pointwiseValue (ricciFlowRiemannVariationIntrinsic (g t)) p
      ![X p, Y p, W p, Z p] =
    ricciFlowRiemannVariationIntrinsic (g t) ![X, Y, W, Z] p at hpoint
  rw [hpoint, ricciFlowRiemannVariationIntrinsic_apply] at hderiv'
  have hsecond (A B C D : SmoothVectorField I M) :
      secondCovDerivAlong (g t).leviCivitaConnection A B
          (covTensorOfBilin
            (fun q (u v : TangentSpace I q) => -2 * ricciTensorAt (g t) q u v))
          (fun i => if i = 0 then C else D) p =
        -2 * secondCovDerivAlong (g t).leviCivitaConnection A B
          (ricciTensorField (g t)) ![C, D] p := by
    rw [covTensorOfBilin_neg_two_ricci,
      secondCovDerivAlong_const_mul (g t).leviCivitaConnection A B (-2)
        (hasSmoothComponents_ricciTensorField (g t))]
    congr 2
    funext i
    fin_cases i <;> simp
  simp only [hsecond]
  exact hderiv'.congr_deriv (by ring)

/-- **Math.** Every time set contained in the interior of a Ricci-flow domain
inherits the full Riemann first-variation formula, including within-derivatives
at endpoints of the smaller set. -/
theorem hasRiemannVariationOn_of_isRicciFlowOn_of_subset_interior
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) (hK : K ⊆ interior J) :
    HasRiemannVariationOn g
      (fun s q (u v : TangentSpace I q) => -2 * ricciTensorAt (g s) q u v) K := by
  intro t ht X Y W Z p
  exact (hasRiemannVariationOn_interior_of_isRicciFlowOn
    hflow t (hK ht) X Y W Z p).mono hK

/-- **Math.** On an open Ricci-flow domain, every contained target time set
inherits the full Riemann first-variation formula. -/
theorem hasRiemannVariationOn_of_isRicciFlowOn_of_isOpen
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) (hJ : IsOpen J) (hK : K ⊆ J) :
    HasRiemannVariationOn g
      (fun s q (u v : TangentSpace I q) => -2 * ricciTensorAt (g s) q u v) K := by
  apply hasRiemannVariationOn_of_isRicciFlowOn_of_subset_interior hflow
  simpa [hJ.interior_eq] using hK

#print axioms Topping.chartRiemannVariationAt_neg_two_ricci_eq_intrinsic
#print axioms Topping.hasRiemannVariationOn_interior_of_isRicciFlowOn
#print axioms Topping.hasRiemannVariationOn_of_isRicciFlowOn
#print axioms Topping.hasRiemannVariationOn_of_isRicciFlowOn_of_subset_interior

end Topping
