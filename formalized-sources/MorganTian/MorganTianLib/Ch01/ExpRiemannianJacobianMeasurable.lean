import MorganTianLib.Ch01.ExpRiemannianJacobian
import MorganTianLib.Ch01.MatrixCalculus
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Measurability of the exponential-map Riemannian Jacobian

This module supplies the measure-theoretic producer needed by the Bishop--Gromov
manifold bridge.  The global function is assembled from the measurable pullbacks
of the fixed chart pieces used by `riemannianMeasure`.
-/

open MeasureTheory Measure Set Filter Function Metric Riemannian Riemannian.Geodesic Module
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

/-! The chart density is continuous on the target of every fixed chart.  This is
the Ch01-local form of the smooth density theorem; keeping it here avoids a
back-edge from this Ch01 measure producer to the Ch02 Green identity file. -/
private theorem continuousOn_chartVolumeDensity_target (g : RiemannianMetric I M) (a : M) :
    ContinuousOn (chartVolumeDensity (I := I) g a) (extChartAt I a).target := by
  have hmat : ContDiffOn ℝ ∞
      (fun y : E => (fun i j => chartGramOnE (I := I) g a i j y))
      (extChartAt I a).target := by
    rw [contDiffOn_pi]
    intro i
    rw [contDiffOn_pi]
    intro j
    exact chartGramOnE_contDiffOn (I := I) g a i j
  have hdet : ContDiffOn ℝ ∞
      (fun y : E => Matrix.det (fun i j => chartGramOnE (I := I) g a i j y))
      (extChartAt I a).target :=
    (MorganTianLib.contDiff_det.of_le (show (∞ : WithTop ℕ∞) ≤ ⊤ from le_top)).contDiffOn.comp
      hmat (fun _ _ => mem_univ _)
  have hsqrt : ContDiffOn ℝ ∞
      (fun y : E => Real.sqrt (Matrix.det (fun i j =>
        chartGramOnE (I := I) g a i j y))) (extChartAt I a).target :=
    hdet.sqrt (fun y hy => by
    change (Riemannian.Tensor.chartGramMatrix (I := I) g a
      ((extChartAt I a).symm y)).det ≠ 0
    exact ne_of_gt (Riemannian.Tensor.chartGramMatrix_det_pos (I := I) g a (by
      rw [trivializationAt_baseSet_eq_chartAt_source,
        ← extChartAt_source_eq_chartAt_source (I := I)]
      exact (extChartAt I a).map_target hy)) )
  have hcd : ContDiffOn ℝ ∞ (chartVolumeDensity (I := I) g a)
      (extChartAt I a).target := by
    convert hsqrt using 1
    · funext y
      rfl
  exact hcd.continuousOn

/-! A fixed chart gives a globally defined (zero-extended) density pullback. -/
noncomputable def expChartDensityPullback (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p a : M) (v : E) : ℝ :=
  by
    classical
    exact if h : expMapGlobal (I := I) g hg p v ∈ (extChartAt I a).source then
      chartVolumeDensity (I := I) g a
        (extChartAt I a (expMapGlobal (I := I) g hg p v))
      else 0

theorem measurable_expChartDensityPullback (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) (p a : M) :
    Measurable (expChartDensityPullback (I := I) g hg p a) := by
  classical
  let S : Set E := (expMapGlobal (I := I) g hg p) ⁻¹' (extChartAt I a).source
  have hS : MeasurableSet S := by
    exact (isOpen_extChartAt_source (I := I) a).measurableSet.preimage
      (continuous_expMapGlobal (I := I) g hg p).measurable
  have hcoord : ContinuousOn
      (fun w : E => extChartAt I a
        (expMapGlobal (I := I) g hg p w)) S := by
    exact (continuousOn_extChartAt (I := I) a).comp
      (continuous_expMapGlobal (I := I) g hg p).continuousOn
      (fun _ hw => hw)
  have hden : ContinuousOn
      (fun w : E => chartVolumeDensity (I := I) g a
        (extChartAt I a (expMapGlobal (I := I) g hg p w))) S := by
    exact (continuousOn_chartVolumeDensity_target (I := I) g a).comp hcoord
      (fun _ hw => (extChartAt I a).map_source hw)
  have hm : Measurable
      (S.piecewise
        (fun w : E => chartVolumeDensity (I := I) g a
          (extChartAt I a (expMapGlobal (I := I) g hg p w)))
        (fun _ => 0)) :=
    hden.measurable_piecewise continuous_zero.continuousOn hS
  have heq : expChartDensityPullback (I := I) g hg p a =
      S.piecewise
        (fun w : E => chartVolumeDensity (I := I) g a
          (extChartAt I a (expMapGlobal (I := I) g hg p w)))
        (fun _ => 0) := by
    funext v
    by_cases hv : v ∈ S <;> simp [expChartDensityPullback, Set.piecewise, S]
  rw [heq]
  exact hm

/-! The coordinate Jacobian factor is measurable without restricting to a chart. -/
theorem measurable_abs_det_expChart (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) (p a : M) :
    Measurable (fun v : E =>
      |(fderiv ℝ (fun w : E => extChartAt I a
        (expMapGlobal (I := I) g hg p (w : TangentSpace I p))) v).det|) := by
  have hfd : Measurable (fderiv ℝ (fun w : E => extChartAt I a
      (expMapGlobal (I := I) g hg p (w : TangentSpace I p)))) :=
    measurable_fderiv ℝ _
  exact continuous_abs.measurable.comp
    (ContinuousLinearMap.continuous_det.measurable.comp hfd)

theorem measurable_expChartJacobian (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) (p a : M) :
    Measurable (fun v : E =>
      |(fderiv ℝ (fun w : E => extChartAt I a
        (expMapGlobal (I := I) g hg p (w : TangentSpace I p))) v).det|
        * expChartDensityPullback (I := I) g hg p a v) := by
  exact (measurable_abs_det_expChart (I := I) g hg p a).mul
    (measurable_expChartDensityPullback (I := I) g hg p a)

/-! The fixed-chart factors glue to a measurable global Jacobian. -/
theorem measurable_expRiemannianJacobian (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) (p : M) :
    Measurable (expRiemannianJacobian (I := I) g hg p) := by
  classical
  let phi : E → M := fun v => expMapGlobal (I := I) g hg p v
  let t : ℕ → Set E := fun n =>
    phi ⁻¹' chartPiece (I := I) (M := M) n
  let f : ℕ → E → ℝ := fun n v =>
    |(fderiv ℝ (fun w : E => extChartAt I (chartCover (I := I) (M := M) n)
      (phi w)) v).det|
      * expChartDensityPullback (I := I) g hg p
        (chartCover (I := I) (M := M) n) v
  have hphi : Measurable phi := by
    exact (continuous_expMapGlobal (I := I) g hg p).measurable
  have ht : ∀ n, MeasurableSet (t n) := by
    intro n
    dsimp [t]
    exact (measurableSet_chartPiece (I := I) (M := M) n).preimage hphi
  have hf : ∀ n, Measurable (f n) := by
    intro n
    dsimp [f, phi]
    exact measurable_expChartJacobian (I := I) g hg p
      (chartCover (I := I) (M := M) n)
  have hRJ : HasRiemannianJacobianOn (I := I) g phi Set.univ
      (expRiemannianJacobian (I := I) g hg p) := by
    simpa only [phi] using
      (hasRiemannianJacobianOn_expMapGlobal (I := I) g hg p Set.univ)
  have hpiece : ∀ n, EqOn (f n)
      (expRiemannianJacobian (I := I) g hg p) (t n) := by
    intro n v hv
    have hvpiece : phi v ∈ chartPiece (I := I) (M := M) n := by
      exact hv
    have hvsource : phi v ∈
        (extChartAt I (chartCover (I := I) (M := M) n)).source :=
      chartPiece_subset (I := I) (M := M) n hvpiece
    obtain ⟨D, hD, hρ⟩ :=
      hRJ (chartCover (I := I) (M := M) n) v (Set.mem_univ _) hvsource
    have hDAt : HasFDerivAt
        (fun w : E => extChartAt I (chartCover (I := I) (M := M) n)
          (phi w)) D v :=
      hD.hasFDerivAt univ_mem
    have hDfderiv : fderiv ℝ
        (fun w : E => extChartAt I (chartCover (I := I) (M := M) n)
          (phi w)) v = D :=
      hDAt.fderiv
    have hpull :
        expChartDensityPullback (I := I) g hg p
          (chartCover (I := I) (M := M) n) v =
        chartVolumeDensity (I := I) g (chartCover (I := I) (M := M) n)
          (extChartAt I (chartCover (I := I) (M := M) n)
            (expMapGlobal (I := I) g hg p v)) := by
      unfold expChartDensityPullback
      exact dif_pos hvsource
    calc
      f n v =
          |(fderiv ℝ (fun w : E => extChartAt I
            (chartCover (I := I) (M := M) n) (phi w)) v).det| *
            expChartDensityPullback (I := I) g hg p
              (chartCover (I := I) (M := M) n) v := by rfl
      _ = |D.det| *
            chartVolumeDensity (I := I) g (chartCover (I := I) (M := M) n)
              (extChartAt I (chartCover (I := I) (M := M) n)
                (expMapGlobal (I := I) g hg p v)) := by
          rw [hDfderiv, hpull]
      _ = expRiemannianJacobian (I := I) g hg p v := hρ.symm
  have hpair : Pairwise (fun i j => EqOn (f i) (f j) (t i ∩ t j)) := by
    intro i j hij v hv
    have hvi : phi v ∈ chartPiece (I := I) (M := M) i := by
      exact hv.1
    have hvj : phi v ∈ chartPiece (I := I) (M := M) j := by
      exact hv.2
    exact False.elim ((Set.disjoint_left.1
      (pairwise_disjoint_chartPiece (I := I) (M := M) hij)) hvi hvj)
  obtain ⟨F, hF, hFpiece⟩ := exists_measurable_piecewise t ht f hf hpair
  have htcover : (⋃ n, t n) = (Set.univ : Set E) := by
    dsimp [t]
    rw [← Set.preimage_iUnion, iUnion_chartPiece (I := I) (M := M),
      Set.preimage_univ]
  have hEq : F = expRiemannianJacobian (I := I) g hg p := by
    funext v
    have hv : v ∈ (⋃ n, t n) := by
      rw [htcover]
      exact Set.mem_univ _
    obtain ⟨n, hvn⟩ := Set.mem_iUnion.1 hv
    exact (hFpiece n hvn).trans (hpiece n hvn)
  rw [← hEq]
  exact hF

end MorganTianLib
