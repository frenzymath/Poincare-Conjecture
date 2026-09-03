import MorganTianLib.Ch01.Issue16Foundations
import MorganTianLib.Ch01.MatrixCalculus

/-!
# Continuity of the exponential-map Riemannian Jacobian

The canonical definition of `expRiemannianJacobian` reads the derivative in a
chart whose centre varies with the tangent vector.  Continuity is therefore not
visible directly from the definition.  Locally one may instead use a single
chart around the image of a fixed vector: chart invariance of the Riemannian
Jacobian identifies the resulting fixed-chart formula with the canonical one.

This supplies the neighbourhood-level regularity input needed to pass from the
pointwise normalization at the exponential origin to a small-ball integral
asymptotic in Bishop--Gromov.
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

/-- **Math.** The Riemannian volume density in a fixed chart is continuous on
the chart target. -/
theorem continuousOn_chartVolumeDensity_target_ch01
    (g : RiemannianMetric I M) (a : M) :
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
        exact (extChartAt I a).map_target hy)))
  have hcd : ContDiffOn ℝ ∞ (chartVolumeDensity (I := I) g a)
      (extChartAt I a).target := by
    convert hsqrt using 1
    · funext y
      rfl
  exact hcd.continuousOn

/-- **Math.** The Riemannian Jacobian density of the global exponential map is
continuous on the whole tangent space.  Near any vector it can be read in the
single preferred chart centred at that vector's image; smoothness of the
coordinate exponential and of the chart volume density then gives continuity.
-/
theorem continuous_expRiemannianJacobian
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    Continuous (expRiemannianJacobian (I := I) g hg p) := by
  rw [continuous_iff_continuousAt]
  intro v
  let phi : E → M := fun w => expMapGlobal (I := I) g hg p (w : TangentSpace I p)
  let a : M := phi v
  let F : E → E := fun w => extChartAt I a (phi w)
  let s : Set E := phi ⁻¹' (extChartAt I a).source
  have hphi : ContMDiff 𝓘(ℝ, E) I ∞ phi :=
    Riemannian.Exponential.contMDiff_expMapGlobal g hg p
  have hsopen : IsOpen s :=
    (isOpen_extChartAt_source (I := I) a).preimage hphi.continuous
  have hvs : v ∈ s := mem_extChartAt_source (I := I) a
  have hmaps : MapsTo phi s (chartAt H a).source := by
    intro w hw
    rw [← extChartAt_source (I := I)]
    exact hw
  have hF : ContDiffOn ℝ ∞ F s := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_extChartAt (I := I) (x := a)).comp hphi.contMDiffOn hmaps
  have hDf : ContinuousOn (fderiv ℝ F) s :=
    hF.continuousOn_fderiv_of_isOpen hsopen (by exact_mod_cast le_top)
  have hdet : ContinuousOn (fun w => |(fderiv ℝ F w).det|) s :=
    continuous_abs.comp_continuousOn
      (ContinuousLinearMap.continuous_det.comp_continuousOn hDf)
  have hden : ContinuousOn
      (fun w => chartVolumeDensity (I := I) g a (extChartAt I a (phi w))) s :=
    (continuousOn_chartVolumeDensity_target_ch01 (I := I) g a).comp hF.continuousOn
      (fun w hw => (extChartAt I a).map_source hw)
  have hfixed : ContinuousAt
      (fun w => |(fderiv ℝ F w).det| *
        chartVolumeDensity (I := I) g a (extChartAt I a (phi w))) v :=
    (hdet.mul hden).continuousAt (hsopen.mem_nhds hvs)
  have heq : EqOn (expRiemannianJacobian (I := I) g hg p)
      (fun w => |(fderiv ℝ F w).det| *
        chartVolumeDensity (I := I) g a (extChartAt I a (phi w))) s := by
    intro w hw
    obtain ⟨D, hD, hvalue⟩ :=
      hasRiemannianJacobianOn_expMapGlobal (I := I) g hg p univ
        a w (mem_univ w) hw
    have hD' : fderiv ℝ F w = D := (hD.hasFDerivAt univ_mem).fderiv
    change expRiemannianJacobian (I := I) g hg p w =
      |(fderiv ℝ F w).det| *
        chartVolumeDensity (I := I) g a (extChartAt I a (phi w))
    rw [hD']
    simpa [phi] using hvalue
  exact hfixed.congr_of_eventuallyEq
    (eventuallyEq_of_mem (hsopen.mem_nhds hvs) heq)

end MorganTianLib

end

#print axioms MorganTianLib.continuous_expRiemannianJacobian
