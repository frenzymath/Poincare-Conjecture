import MorganTianLib.Ch03.RicciFlow.ScalarTraceEvolution
import Topping.RicciFlow.ScalarEvolutionUnconditional

/-!
# Joint space-time smoothness of scalar curvature

The smooth-family structure used by Morgan--Tian is joint in space and time.
This file carries that regularity through the coordinate construction of
curvature and then reads the result back intrinsically.  Spatial derivatives
are taken inside an open chart target, so this regularity is available on the
whole prescribed time set, including its endpoints.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- A spatial derivative of a jointly smooth function remains jointly smooth
when the spatial domain is open; the time set need not be open. -/
private theorem contDiffOn_spatialFDeriv_apply
    {J : Set ℝ} {U : Set E} (hU : IsOpen U) {F : ℝ × E → ℝ}
    (hF : ContDiffOn ℝ ∞ F (J ×ˢ U)) (v : E) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => fderiv ℝ (fun y => F (z.1, y)) z.2 v)
      (J ×ˢ U) := by
  let S : Set (ℝ × E) := J ×ˢ U
  let P : (ℝ × E) → E → ℝ := fun z y => F (z.1, y)
  let gs : (ℝ × E) → E := fun z => z.2
  let ks : (ℝ × E) → E := fun _ => v
  have hP : ContDiffOn ℝ ∞ (Function.uncurry P) (S ×ˢ U) := by
    change ContDiffOn ℝ ∞
      (fun w : (ℝ × E) × E => F (w.1.1, w.2)) (S ×ˢ U)
    have hmap : ContDiffOn ℝ ∞
        (fun w : (ℝ × E) × E => (w.1.1, w.2)) (S ×ˢ U) :=
      contDiffOn_fst.fst.prodMk contDiffOn_snd
    have hmaps : MapsTo
        (fun w : (ℝ × E) × E => (w.1.1, w.2)) (S ×ˢ U) S := by
      rintro ⟨z, y⟩ ⟨hz, hy⟩
      exact ⟨hz.1, hy⟩
    exact hF.comp hmap hmaps
  intro z hz
  have hgs : ContDiffWithinAt ℝ ∞ gs S z := contDiffWithinAt_snd
  have hks : ContDiffWithinAt ℝ ∞ ks S z := contDiffWithinAt_const
  have hpartial := (hP (z, gs z) ⟨hz, hz.2⟩).fderivWithin_apply
    hgs hks hU.uniqueDiffOn
    (show (∞ : ℕ∞ω) + 1 ≤ ∞ from le_rfl) hz (by
      intro w hw
      exact hw.2)
  refine hpartial.congr_of_eventuallyEq_of_mem ?_ hz
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [fderivWithin_of_isOpen hU hw.2]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** A spatial derivative of a chart Gram coefficient remains jointly
smooth on the full time set.  Only the spatial chart target needs to be open. -/
theorem contDiffOn_partialDeriv_chartGramOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j r : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => partialDeriv (E := E) r
        (chartGramOnE (I := I) (g z.1) alpha i j) z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  simpa only [partialDeriv] using
    contDiffOn_spatialFDeriv_apply
      (E := E) (J := J)
      (isOpen_extChartAt_target (I := I) alpha)
      (MorganTianLib.contDiffOn_chartGramOnE_timeSpace hg alpha i j)
      ((Module.finBasis ℝ E) r)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** Christoffel symbols of a smooth metric family are jointly smooth
on the full prescribed time set. -/
theorem contDiffOn_chartChristoffel_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartChristoffel (I := I) (g z.1) alpha i j k z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  rw [show (fun z : ℝ × E =>
      chartChristoffel (I := I) (g z.1) alpha i j k z.2) =
      fun z => (1 / 2 : ℝ) * ∑ l,
        Tensor.chartInvGramMatrix (I := I) (g z.1) alpha
            ((extChartAt I alpha).symm z.2) k l *
          (partialDeriv (E := E) i
              (chartGramOnE (I := I) (g z.1) alpha l j) z.2 +
           partialDeriv (E := E) j
              (chartGramOnE (I := I) (g z.1) alpha l i) z.2 -
           partialDeriv (E := E) l
              (chartGramOnE (I := I) (g z.1) alpha i j) z.2) by
    funext z
    rw [chartChristoffel_def]]
  exact (contDiffOn_const (c := (1 / 2 : ℝ))).mul
    (ContDiffOn.sum fun l _ =>
      ContDiffOn.mul
        (MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace hg alpha k l)
        (((contDiffOn_partialDeriv_chartGramOnE_timeSpace hg alpha l j i).add
          (contDiffOn_partialDeriv_chartGramOnE_timeSpace hg alpha l i j)).sub
          (contDiffOn_partialDeriv_chartGramOnE_timeSpace hg alpha i j l)))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** A spatial derivative of a Christoffel coefficient remains jointly
smooth on the full prescribed time set. -/
theorem contDiffOn_partialDeriv_chartChristoffel_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k r : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => partialDeriv (E := E) r
        (chartChristoffel (I := I) (g z.1) alpha i j k) z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  simpa only [partialDeriv] using
    contDiffOn_spatialFDeriv_apply
      (E := E) (J := J)
      (isOpen_extChartAt_target (I := I) alpha)
      (contDiffOn_chartChristoffel_timeSpace hg alpha i j k)
      ((Module.finBasis ℝ E) r)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** Mixed-index coordinate curvature coefficients of a smooth metric
family are jointly smooth on the full prescribed time set. -/
theorem contDiffOn_chartCurvatureCoef_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => Riemannian.Jacobi.chartCurvatureCoef
        (I := I) (g z.1) alpha i j k l z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  have hGamma : ∀ a b c : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun z : ℝ × E => chartChristoffel (I := I) (g z.1) alpha a b c z.2)
        (J ×ˢ (extChartAt I alpha).target) :=
    fun a b c => contDiffOn_chartChristoffel_timeSpace hg alpha a b c
  have hpartial : ∀ a b c d : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun z : ℝ × E => partialDeriv (E := E) a
          (chartChristoffel (I := I) (g z.1) alpha b c d) z.2)
        (J ×ˢ (extChartAt I alpha).target) :=
    fun a b c d =>
      contDiffOn_partialDeriv_chartChristoffel_timeSpace hg alpha b c d a
  unfold Riemannian.Jacobi.chartCurvatureCoef
  refine ((hpartial j i k l).sub (hpartial i j k l)).add ?_
  exact ContDiffOn.sum fun s _ =>
    ((hGamma i k s).mul (hGamma j s l)).sub
      ((hGamma j k s).mul (hGamma i s l))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** Coordinate Ricci coefficients of a smooth metric family are
jointly smooth on the full prescribed time set. -/
theorem contDiffOn_chartRicciCoefOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => MorganTianLib.chartRicciCoefOnE
        (I := I) (g z.1) alpha j k z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  unfold MorganTianLib.chartRicciCoefOnE
  exact ContDiffOn.sum fun a _ =>
    contDiffOn_chartCurvatureCoef_timeSpace hg alpha j a k a

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** A fixed chart partial derivative of a Ricci coefficient remains
jointly smooth on the full prescribed time set. -/
theorem contDiffOn_partialDeriv_chartRicciCoefOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j r : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => partialDeriv (E := E) r
        (MorganTianLib.chartRicciCoefOnE (I := I) (g z.1) alpha i j) z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  simpa only [partialDeriv] using
    contDiffOn_spatialFDeriv_apply
      (E := E) (J := J)
      (isOpen_extChartAt_target (I := I) alpha)
      (contDiffOn_chartRicciCoefOnE_timeSpace hg alpha i j)
      ((Module.finBasis ℝ E) r)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** The coordinate covariant derivative of Ricci is jointly smooth
on the full prescribed time set. -/
theorem contDiffOn_chartCovRicciOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (r i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => MorganTianLib.chartCovRicciOnE
        (I := I) (g z.1) alpha r i j z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  unfold MorganTianLib.chartCovRicciOnE
  exact ((contDiffOn_partialDeriv_chartRicciCoefOnE_timeSpace
      hg alpha i j r).sub
    (ContDiffOn.sum fun s _ =>
      (contDiffOn_chartChristoffel_timeSpace hg alpha r i s).mul
        (contDiffOn_chartRicciCoefOnE_timeSpace hg alpha s j))).sub
    (ContDiffOn.sum fun s _ =>
      (contDiffOn_chartChristoffel_timeSpace hg alpha r j s).mul
        (contDiffOn_chartRicciCoefOnE_timeSpace hg alpha i s))

/-- **Math.** In a Ricci-flow direction, the fixed-chart metric variation is
jointly smooth on the full prescribed time set. -/
theorem contDiffOn_chartMetricVariationOnE_neg_two_ricci_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => MorganTianLib.chartMetricVariationOnE (I := I)
        (fun s p x w => -2 * MorganTianLib.ricciTensorAt (g s) p x w)
        z.1 alpha i j z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  have hrhs := (contDiffOn_const (c := (-2 : ℝ))).mul
    (contDiffOn_chartRicciCoefOnE_timeSpace hg alpha i j)
  exact hrhs.congr fun z hz =>
    MorganTianLib.chartMetricVariationOnE_neg_two_ricci
      g z.1 alpha i j hz.2

/-- **Math.** In a Ricci-flow direction, the Christoffel variation is jointly
smooth on the full prescribed time set. -/
theorem contDiffOn_chartChristoffelVariationOnE_neg_two_ricci_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => MorganTianLib.chartChristoffelVariationOnE
        (I := I) g
        (fun s p x w => -2 * MorganTianLib.ricciTensorAt (g s) p x w)
        z.1 alpha i j k z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  have hrhs : ContDiffOn ℝ ∞ (fun z : ℝ × E =>
      - ∑ l, chartInvGramOnE (I := I) (g z.1) alpha k l z.2 *
        (MorganTianLib.chartCovRicciOnE (I := I) (g z.1) alpha i l j z.2 +
          MorganTianLib.chartCovRicciOnE (I := I) (g z.1) alpha j l i z.2 -
          MorganTianLib.chartCovRicciOnE (I := I) (g z.1) alpha l i j z.2))
      (J ×ˢ (extChartAt I alpha).target) := by
    exact (ContDiffOn.sum fun l _ =>
      (MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace hg alpha k l).mul
        (((contDiffOn_chartCovRicciOnE_timeSpace hg alpha i l j).add
          (contDiffOn_chartCovRicciOnE_timeSpace hg alpha j l i)).sub
          (contDiffOn_chartCovRicciOnE_timeSpace hg alpha l i j))).neg
  exact hrhs.congr fun z hz =>
    MorganTianLib.chartChristoffelVariationOnE_neg_two_ricci_eq_covRicci
      g z.1 alpha i j k hz.2

/-- **Math.** A fixed spatial derivative of the Ricci-flow Christoffel
variation remains jointly smooth on the full prescribed time set. -/
theorem contDiffOn_partialDeriv_chartChristoffelVariationOnE_neg_two_ricci_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k r : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => partialDeriv (E := E) r
        (MorganTianLib.chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * MorganTianLib.ricciTensorAt (g s) p x w)
          z.1 alpha i j k) z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  simpa only [partialDeriv] using
    contDiffOn_spatialFDeriv_apply
      (E := E) (J := J)
      (isOpen_extChartAt_target (I := I) alpha)
      (contDiffOn_chartChristoffelVariationOnE_neg_two_ricci_timeSpace
        hg alpha i j k)
      ((Module.finBasis ℝ E) r)

/-- **Math.** The coordinate curvature variation in the Ricci-flow direction
is jointly smooth on the full prescribed time set. -/
theorem contDiffOn_chartCurvatureCoefVariationOnE_neg_two_ricci_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => MorganTianLib.chartCurvatureCoefVariationOnE
        (I := I) g
        (fun s p x w => -2 * MorganTianLib.ricciTensorAt (g s) p x w)
        z.1 alpha i j k l z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  unfold MorganTianLib.chartCurvatureCoefVariationOnE
  refine ((contDiffOn_partialDeriv_chartChristoffelVariationOnE_neg_two_ricci_timeSpace
    hg alpha i k l j).sub
    (contDiffOn_partialDeriv_chartChristoffelVariationOnE_neg_two_ricci_timeSpace
      hg alpha j k l i)).add ?_
  exact ContDiffOn.sum fun s _ =>
    (((contDiffOn_chartChristoffelVariationOnE_neg_two_ricci_timeSpace
        hg alpha i k s).mul
      (contDiffOn_chartChristoffel_timeSpace hg alpha j s l)).add
      ((contDiffOn_chartChristoffel_timeSpace hg alpha i k s).mul
        (contDiffOn_chartChristoffelVariationOnE_neg_two_ricci_timeSpace
          hg alpha j s l))).sub
    (((contDiffOn_chartChristoffelVariationOnE_neg_two_ricci_timeSpace
        hg alpha j k s).mul
      (contDiffOn_chartChristoffel_timeSpace hg alpha i s l)).add
      ((contDiffOn_chartChristoffel_timeSpace hg alpha j k s).mul
        (contDiffOn_chartChristoffelVariationOnE_neg_two_ricci_timeSpace
          hg alpha i s l)))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** The coordinate scalar curvature of a smooth metric family is
jointly smooth on the full prescribed time set. -/
theorem contDiffOn_chartScalarCurvatureOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => MorganTianLib.chartScalarCurvatureOnE
        (I := I) (g z.1) alpha z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  unfold MorganTianLib.chartScalarCurvatureOnE
  exact ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ =>
    (MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace hg alpha j k).mul
      (contDiffOn_chartRicciCoefOnE_timeSpace hg alpha j k)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** A fixed chart partial derivative of scalar curvature remains
jointly smooth on the full time set. -/
theorem contDiffOn_partialDeriv_chartScalarCurvatureOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (r : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => partialDeriv (E := E) r
        (MorganTianLib.chartScalarCurvatureOnE (I := I) (g z.1) alpha) z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  simpa only [partialDeriv] using
    contDiffOn_spatialFDeriv_apply
      (E := E) (J := J)
      (isOpen_extChartAt_target (I := I) alpha)
      (contDiffOn_chartScalarCurvatureOnE_timeSpace hg alpha)
      ((Module.finBasis ℝ E) r)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** Two fixed chart partial derivatives of scalar curvature remain
jointly smooth on the full time set. -/
theorem contDiffOn_secondPartialDeriv_chartScalarCurvatureOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => partialDeriv (E := E) j (fun y =>
        partialDeriv (E := E) k
          (MorganTianLib.chartScalarCurvatureOnE (I := I) (g z.1) alpha) y) z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  simpa only [partialDeriv] using
    contDiffOn_spatialFDeriv_apply
      (E := E) (J := J)
      (isOpen_extChartAt_target (I := I) alpha)
      (contDiffOn_partialDeriv_chartScalarCurvatureOnE_timeSpace hg alpha k)
      ((Module.finBasis ℝ E) j)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** The Christoffel-coordinate Laplacian of scalar curvature is
jointly smooth on the full time set. -/
theorem contDiffOn_chartScalarLaplacianOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => ∑ j, ∑ k,
        chartInvGramOnE (I := I) (g z.1) alpha j k z.2 *
          (partialDeriv (E := E) j (fun y => partialDeriv (E := E) k
              (MorganTianLib.chartScalarCurvatureOnE (I := I) (g z.1) alpha) y) z.2 -
            ∑ s, chartChristoffel (I := I) (g z.1) alpha j k s z.2 *
              partialDeriv (E := E) s
                (MorganTianLib.chartScalarCurvatureOnE (I := I) (g z.1) alpha) z.2))
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  refine ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_
  have hinv : ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartInvGramOnE (I := I) (g z.1) alpha j k z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
    simpa only [chartInvGramOnE_def] using
      MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace hg alpha j k
  exact hinv.mul
    ((contDiffOn_secondPartialDeriv_chartScalarCurvatureOnE_timeSpace
        hg alpha j k).sub
      (ContDiffOn.sum fun s _ =>
        (contDiffOn_chartChristoffel_timeSpace hg alpha j k s).mul
          (contDiffOn_partialDeriv_chartScalarCurvatureOnE_timeSpace
            hg alpha s)))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** The complete inverse-Gram contraction defining `|Ric|²` is
jointly smooth on the full time set. -/
theorem contDiffOn_chartRicciNormSqOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E =>
        MorganTianLib.chartRicciNormSqOnE (I := I) (g z.1) alpha z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  unfold MorganTianLib.chartRicciNormSqOnE
  exact ContDiffOn.sum fun j _ => ContDiffOn.sum fun d _ =>
    ContDiffOn.sum fun k _ => ContDiffOn.sum fun a _ =>
      (((MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace hg alpha j a).mul
        (contDiffOn_chartRicciCoefOnE_timeSpace hg alpha a d)).mul
        (MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace hg alpha d k)).mul
        (contDiffOn_chartRicciCoefOnE_timeSpace hg alpha j k)

/-- **Math.** Scalar curvature is jointly smooth in space and time on the whole
time set of every smooth metric family. -/
theorem scalarCurvature_contMDiffOn_of_isSmoothMetricFamilyOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ J) := by
  rintro z hz
  rcases z with ⟨p, t⟩
  have ht : t ∈ J := hz.2
  have hp : p ∈ (extChartAt I p).source := mem_extChartAt_source p
  have hpy : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hp
  let S : Set (ℝ × E) := J ×ˢ (extChartAt I p).target
  let D : Set (M × ℝ) := (extChartAt I p).source ×ˢ J
  have hcoord : ContDiffWithinAt ℝ ∞
      (fun w : ℝ × E => MorganTianLib.chartScalarCurvatureOnE
        (I := I) (g w.1) p w.2)
      S (t, extChartAt I p p) :=
    contDiffOn_chartScalarCurvatureOnE_timeSpace hg p
      (t, extChartAt I p p) ⟨ht, hpy⟩
  have hcoordM : ContMDiffWithinAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun w : ℝ × E => MorganTianLib.chartScalarCurvatureOnE
        (I := I) (g w.1) p w.2)
      S (t, extChartAt I p p) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hcoord.contMDiffWithinAt
  have hchart : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun w : M × ℝ => extChartAt I p w.1) (p, t) :=
    (contMDiffAt_extChartAt (I := I) (x := p)).comp (p, t) contMDiffAt_fst
  have hread : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun w : M × ℝ => (w.2, extChartAt I p w.1)) D (p, t) :=
    contMDiffWithinAt_snd.prodMk hchart.contMDiffWithinAt
  have hmaps : MapsTo
      (fun w : M × ℝ => (w.2, extChartAt I p w.1)) D S := by
    intro w hw
    exact ⟨hw.2, (extChartAt I p).map_source hw.1⟩
  have hcomp : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => MorganTianLib.chartScalarCurvatureOnE
        (I := I) (g w.2) p (extChartAt I p w.1)) D (p, t) :=
    ContMDiffWithinAt.comp
      (f := fun w : M × ℝ => (w.2, extChartAt I p w.1))
      (g := fun q : ℝ × E => MorganTianLib.chartScalarCurvatureOnE
        (I := I) (g q.1) p q.2) (p, t) hcoordM hread hmaps
  have hintrinsic : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun w : M × ℝ => scalarCurvatureAt (g w.2) w.1) D (p, t) := by
    refine hcomp.congr ?_ ?_
    · intro w hw
      have htarget : extChartAt I p w.1 ∈ (extChartAt I p).target :=
        (extChartAt I p).map_source hw.1
      have hchartScalar :=
        MorganTianLib.chartScalarCurvatureOnE_eq_scalarCurvatureAt
          (I := I) (g w.2) p htarget
          (isLeviCivita_leviCivitaConnection (g w.2))
      rw [(extChartAt I p).left_inv hw.1] at hchartScalar
      calc
        scalarCurvatureAt (g w.2) w.1 =
            MorganTianLib.scalarCurvatureAt (g w.2)
              (g w.2).leviCivitaConnection
              (isLeviCivita_leviCivitaConnection (g w.2)) w.1 :=
          scalarCurvatureAt_eq_scalarCurvatureAt (g w.2) w.1
        _ = MorganTianLib.chartScalarCurvatureOnE
              (I := I) (g w.2) p (extChartAt I p w.1) :=
          hchartScalar.symm
    · have hchartScalar :=
        MorganTianLib.chartScalarCurvatureOnE_eq_scalarCurvatureAt
          (I := I) (g t) p hpy
          (isLeviCivita_leviCivitaConnection (g t))
      rw [(extChartAt I p).left_inv hp] at hchartScalar
      calc
        scalarCurvatureAt (g t) p =
            MorganTianLib.scalarCurvatureAt (g t)
              (g t).leviCivitaConnection
              (isLeviCivita_leviCivitaConnection (g t)) p :=
          scalarCurvatureAt_eq_scalarCurvatureAt (g t) p
        _ = MorganTianLib.chartScalarCurvatureOnE
              (I := I) (g t) p (extChartAt I p p) :=
          hchartScalar.symm
  have hsets : D =ᶠ[𝓝 (p, t)] ((Set.univ : Set M) ×ˢ J) := by
    filter_upwards
      [((isOpen_extChartAt_source (I := I) p).prod isOpen_univ).mem_nhds
        ⟨hp, mem_univ t⟩] with w hw
    apply propext
    change (w.1 ∈ (extChartAt I p).source ∧ w.2 ∈ J) ↔
      (w.1 ∈ (Set.univ : Set M) ∧ w.2 ∈ J)
    constructor
    · intro h
      exact ⟨mem_univ _, h.2⟩
    · intro h
      exact ⟨hw.1, h.2⟩
  exact hintrinsic.congr_set hsets

/-- **Math.** The full-set regularity restricts to the interior time set. -/
theorem scalarCurvature_contMDiffOn_interior_of_isSmoothMetricFamilyOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ interior J) :=
  (scalarCurvature_contMDiffOn_of_isSmoothMetricFamilyOn hg).mono
    (Set.prod_mono Subset.rfl interior_subset)

/-- **Math.** A Morgan--Tian Ricci flow supplies the joint scalar-curvature regularity
needed by interior maximum-principle arguments. -/
theorem scalarCurvature_contMDiffOn_interior_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ interior J) :=
  scalarCurvature_contMDiffOn_interior_of_isSmoothMetricFamilyOn hflow.smooth

/-- **Math.** A Morgan--Tian Ricci flow supplies joint scalar-curvature
regularity on its whole prescribed time set, including endpoints. -/
theorem scalarCurvature_contMDiffOn_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ J) :=
  scalarCurvature_contMDiffOn_of_isSmoothMetricFamilyOn hflow.smooth

#print axioms Topping.scalarCurvature_contMDiffOn_of_isSmoothMetricFamilyOn
#print axioms Topping.scalarCurvature_contMDiffOn_interior_of_isSmoothMetricFamilyOn
#print axioms Topping.scalarCurvature_contMDiffOn_of_isRicciFlowOn
#print axioms Topping.scalarCurvature_contMDiffOn_interior_of_isRicciFlowOn

end Topping

end
