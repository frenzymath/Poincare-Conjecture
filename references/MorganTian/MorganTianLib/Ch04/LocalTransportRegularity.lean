import MorganTianLib.Ch04.RadialTensorTransport
import MorganTianLib.Ch04.AugmentedParallelFlow
import MorganTianLib.Ch04.LocalTransportODE
import DoCarmoLib.Riemannian.Geodesic.BumpExtension
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureVector

/-!
# Smooth dependence of canonical local Levi-Civita transport

The connection ODE is extended by a bump function in a chart. Rescaling the
initial chart direction lets its short-time smooth flow reach the endpoint.
The resulting operator is identified with the canonical endpoint transport.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem rescaled_segment_mem_closedBall (y₀ y : E) {a τ : ℝ}
    (ha : 0 ≤ a) (hτ : 0 < τ) (hy : y ∈ Metric.closedBall y₀ a)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) :
    y₀ + s • (τ⁻¹ • (y - y₀)) ∈ Metric.closedBall y₀ a := by
  have hnonneg : 0 ≤ s * τ⁻¹ := mul_nonneg hs.1 (inv_nonneg.mpr hτ.le)
  have hle : s * τ⁻¹ ≤ 1 := by
    simpa [hτ.ne'] using mul_le_mul_of_nonneg_right hs.2 (inv_nonneg.mpr hτ.le)
  have hmem := (convex_closedBall y₀ a) (Metric.mem_closedBall_self ha) hy
    (sub_nonneg.mpr hle) hnonneg (sub_add_cancel 1 (s * τ⁻¹))
  convert hmem using 1
  module

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] [I.Boundaryless] in
private theorem rescaled_localTransport_coordinates (p x : M) {a τ : ℝ}
    (ha : 0 < a) (hτ : 0 < τ)
    (hball : Metric.ball (extChartAt I p p) a ⊆ (extChartAt I p).target)
    (hx : extChartAt I p x ∈ Metric.ball (extChartAt I p p) a) (t : ℝ) :
    extChartAt I p (localTransportCurve (I := I) p x t) =
      extChartAt I p p + (τ * Real.smoothTransition t) •
        (τ⁻¹ • (extChartAt I p x - extChartAt I p p)) := by
  rw [extChartAt_localTransportCurve_of_mem_ball p x ha hball hx t]
  rw [smul_smul, mul_right_comm τ, mul_inv_cancel₀ hτ.ne', one_mul]
  module

private theorem exists_smooth_chartChristoffel_extension
    (g : RiemannianMetric I M) (p : M) :
    ∃ (Γ : E → E →L[ℝ] E →L[ℝ] E) (a : ℝ),
      0 < a ∧ Metric.closedBall (extChartAt I p p) a ⊆ (extChartAt I p).target ∧
      ContDiff ℝ ∞ Γ ∧ EqOn Γ (Jacobi.chartChristoffelBilin g p)
        (Metric.closedBall (extChartAt I p p) a) := by
  obtain ⟨Γ, a, ha, hball, hΓ, heq⟩ :=
    Riemannian.exists_contDiff_eqOn_closedBall_of_contDiffOn isOpen_interior
      (Jacobi.contDiffOn_chartChristoffelBilin g p)
      (mem_interior_iff_mem_nhds.mpr (extChartAt_target_mem_nhds (I := I) p))
  exact ⟨Γ, a, ha, hball.trans interior_subset, hΓ, heq⟩

/-- **Math.** In a neighborhood of the centre, the canonical Levi-Civita
endpoint maps have smooth operator-valued chart coordinates. The same
coordinate operator represents every restriction of the fixed chart-curve
family, independently of the proofs that its curves are admissible. -/
theorem exists_contDiffOn_localLeviCivitaTangentTransport_coordinates
    (g : RiemannianMetric I M) (p : M) :
    ∃ (ρ : ℝ) (Q : E → E →L[ℝ] E), 0 < ρ ∧
      Metric.ball (extChartAt I p p) ρ ⊆ (extChartAt I p).target ∧
      ContDiffOn ℝ ∞ Q (Metric.ball (extChartAt I p p) ρ) ∧
      ∀ (U : Set M)
        (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
          localTransportCurve (I := I) p x 0 = p ∧
          localTransportCurve (I := I) p x 1 = x)
        (x : U), extChartAt I p x ∈ Metric.ball (extChartAt I p p) ρ →
        letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
        ∀ v : E, tangentCoordChange I (x : M) p (x : M)
          (localLeviCivitaTangentTransport g p hC x v) = Q (extChartAt I p x) v := by
  obtain ⟨Γ, a, ha, hball, hΓ, hΓeq⟩ := exists_smooth_chartChristoffel_extension g p
  obtain ⟨r, T, P, hr, hT, hP, hPsmooth⟩ :=
    exists_smooth_local_parallelOperator Γ hΓ (extChartAt I p p)
  let τ : ℝ := T / 2
  have hτ : 0 < τ := half_pos hT
  have hτT : τ < T := half_lt_self hT
  have htime : Icc (0 : ℝ) τ ⊆ Ioo (-T) T := by
    intro s hs
    exact ⟨lt_of_lt_of_le (neg_neg_of_pos hT) hs.1, hs.2.trans_lt hτT⟩
  let D : E → E := fun y => τ⁻¹ • (y - extChartAt I p p)
  have hD : ContDiff ℝ ∞ D := contDiff_const.smul (contDiff_id.sub contDiff_const)
  have hD0 : D (extChartAt I p p) = 0 := by simp [D]
  have hO : IsOpen (Metric.ball (extChartAt I p p) a ∩ D ⁻¹' Metric.ball (0 : E) r) :=
    Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage hD.continuous)
  have hpO : extChartAt I p p ∈
      Metric.ball (extChartAt I p p) a ∩ D ⁻¹' Metric.ball (0 : E) r := by
    refine ⟨Metric.mem_ball_self ha, ?_⟩
    change D (extChartAt I p p) ∈ Metric.ball (0 : E) r
    rw [hD0]
    exact Metric.mem_ball_self hr
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hpO)
  let Q : E → E →L[ℝ] E := fun y => P (D y) τ
  have hτmem : τ ∈ Ioo (-T) T := htime (right_mem_Icc.mpr hτ.le)
  refine ⟨ρ, Q, hρ, ?_, ?_, ?_⟩
  · intro y hy
    exact hball (Metric.ball_subset_closedBall (hρsub hy).1)
  · exact hPsmooth.comp (hD.prodMk contDiff_const).contDiffOn
      (fun y hy => ⟨(hρsub hy).2, hτmem⟩)
  · intro U hC x hx
    have hxa : extChartAt I p x ∈ Metric.ball (extChartAt I p p) a := (hρsub hx).1
    have hDx : D (extChartAt I p x) ∈ Metric.ball (0 : E) r := (hρsub hx).2
    have hba : Metric.ball (extChartAt I p p) a ⊆ (extChartAt I p).target :=
      Metric.ball_subset_closedBall.trans hball
    apply localLeviCivitaTangentTransport_chart_eq_of_ode g p hC x hτ
      (D (extChartAt I p x)) (P (D (extChartAt I p x))) (hP _ hDx).1
    · intro t
      simpa only [extChartAt_source] using
        (localTransportCurve_mem_chartBall p x ha hba hxa t).1
    · exact rescaled_localTransport_coordinates p x ha hτ hba hxa
    · intro s hs
      have hmem : extChartAt I p p + s • D (extChartAt I p x) ∈
          Metric.closedBall (extChartAt I p p) a :=
        rescaled_segment_mem_closedBall _ _ ha.le hτ
          (Metric.ball_subset_closedBall hxa) hs
      have heq := hΓeq hmem
      have hder := (hP _ hDx).2 s (htime hs)
      rw [heq] at hder
      exact hder.hasDerivWithinAt

end MorganTianLib
