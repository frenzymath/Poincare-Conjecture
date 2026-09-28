import MorganTianLib.Ch04.ParallelTransportReparam

/-!
# Radial compatibility of local Levi-Civita transport

The raw affine chart ray carries one interval-parallel field with prescribed
initial tangent value. Every canonical smooth-transition curve to a point on
that ray is a reparameterization, so its actual endpoint transport evaluates
the same field at the radial parameter.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- **Math.** The affine chart ray, before applying a smooth time transition. -/
def chartRadialCurve (p x : M) (s : ℝ) : M :=
  (extChartAt I p).symm ((1 - s) • extChartAt I p p + s • extChartAt I p x)

@[simp]
theorem chartRadialCurve_zero (p x : M) : chartRadialCurve (I := I) p x 0 = p := by
  simp [chartRadialCurve]

private theorem chartRadialCoordinate_mem_ball (p x : M) {r : ℝ} (hr : 0 < r)
    (hx : extChartAt I p x ∈ Metric.ball (extChartAt I p p) r)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (1 - s) • extChartAt I p p + s • extChartAt I p x ∈
      Metric.ball (extChartAt I p p) r :=
  (convex_ball (extChartAt I p p) r) (Metric.mem_ball_self hr) hx
    (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel 1 s)

/-- **Math.** The raw radial segment lies in the chart used to define it. -/
theorem chartRadialCurve_mem_source (p x : M) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (extChartAt I p p) r ⊆ (extChartAt I p).target)
    (hx : extChartAt I p x ∈ Metric.ball (extChartAt I p p) r)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    chartRadialCurve (I := I) p x s ∈ (chartAt H p).source := by
  rw [← extChartAt_source I]
  exact (extChartAt I p).map_target (hball (chartRadialCoordinate_mem_ball p x hr hx hs))

/-- **Math.** Chart readback of the raw radial segment. -/
theorem extChartAt_chartRadialCurve (p x : M) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (extChartAt I p p) r ⊆ (extChartAt I p).target)
    (hx : extChartAt I p x ∈ Metric.ball (extChartAt I p p) r)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    extChartAt I p (chartRadialCurve (I := I) p x s) =
      (1 - s) • extChartAt I p p + s • extChartAt I p x :=
  (extChartAt I p).right_inv (hball (chartRadialCoordinate_mem_ball p x hr hx hs))

/-- **Math.** A canonical curve to a radial endpoint is a time change of the
original raw ray, with parameter `s * Real.smoothTransition t`. -/
theorem localTransportCurve_chartRadialCurve (p x : M) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (extChartAt I p p) r ⊆ (extChartAt I p).target)
    (hx : extChartAt I p x ∈ Metric.ball (extChartAt I p p) r)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    localTransportCurve (I := I) p (chartRadialCurve (I := I) p x s) t =
      chartRadialCurve (I := I) p x (s * Real.smoothTransition t) := by
  unfold localTransportCurve
  rw [extChartAt_chartRadialCurve p x hr hball hx hs]
  unfold chartRadialCurve
  congr 1
  simp only [smul_add, smul_smul, ← add_assoc, ← add_smul]
  have hcoeff : (1 - Real.smoothTransition t) + Real.smoothTransition t * (1 - s) =
      1 - s * Real.smoothTransition t := by ring
  rw [hcoeff, mul_comm (Real.smoothTransition t)]

variable [IsManifold I ∞ M]

/-- **Math.** The raw chart ray is smooth on the closed unit interval. -/
theorem contMDiffOn_chartRadialCurve (p x : M) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (extChartAt I p p) r ⊆ (extChartAt I p).target)
    (hx : extChartAt I p x ∈ Metric.ball (extChartAt I p p) r) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (chartRadialCurve (I := I) p x) (Icc (0 : ℝ) 1) := by
  have hcoord : ContDiff ℝ ∞ (fun s : ℝ =>
      (1 - s) • extChartAt I p p + s • extChartAt I p x) :=
    ((contDiff_const.sub contDiff_id).smul contDiff_const).add
      (contDiff_id.smul contDiff_const)
  exact (contMDiffOn_extChartAt_symm p).comp hcoord.contMDiff.contMDiffOn
    (fun s hs => hball (chartRadialCoordinate_mem_ball p x hr hx hs))

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

private theorem parallelTransportTangentBetween_apply_model
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) {p q : M}
    (hp : c a = p) (hq : c b = q) (v : E) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (parallelTransportTangentBetween g hab hc hp hq v : E) =
      parallelTransportTangentEquiv g hab hc v := by
  subst p q
  rfl

private theorem parallelTransportTangentEquiv_apply_congr_curve
    (g : RiemannianMetric I M) {c d : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    (hd : ContMDiff 𝓘(ℝ, ℝ) I 1 d) (hcd : c = d) (v : E) :
    (parallelTransportTangentEquiv g hab hc v : E) =
      parallelTransportTangentEquiv g hab hd v := by
  subst d
  rfl

/-- **Math.** One parallel field along the raw radial segment evaluates every
canonical endpoint transport on that segment. The field is produced by the
Levi-Civita linear ODE from its initial tangent value. -/
theorem exists_radial_parallel_localLeviCivitaTangentTransport
    (g : RiemannianMetric I M) (p x : M) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (extChartAt I p p) r ⊆ (extChartAt I p).target)
    (hx : extChartAt I p x ∈ Metric.ball (extChartAt I p p) r)
    {U : Set M}
    (hC : ∀ y ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p y) ∧
      localTransportCurve (I := I) p y 0 = p ∧
      localTransportCurve (I := I) p y 1 = y)
    (v : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ V : ∀ s, TangentSpace I (chartRadialCurve (I := I) p x s),
      IsParallelWithinSolOn (I := I) g p (chartRadialCurve (I := I) p x) V 0 1 ∧
      V 0 = v ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ hsU : chartRadialCurve (I := I) p x s ∈ U,
        localLeviCivitaTangentTransport g p hC ⟨chartRadialCurve (I := I) p x s, hsU⟩ v =
          V s := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsrc : ∀ s ∈ Icc (0 : ℝ) 1,
      chartRadialCurve (I := I) p x s ∈ (chartAt H p).source :=
    fun _ hs => chartRadialCurve_mem_source p x hr hball hx hs
  obtain ⟨V, hV, hVinit, _⟩ := Riemannian.exists_intrinsic_chart_parallelWithin
    (g := g) (by norm_num : (0 : ℝ) < 1)
    ((contMDiffOn_chartRadialCurve p x hr hball hx).of_le (by simp)) hsrc (v : E)
  have hV0 : V 0 = v := by
    simpa only [chartFieldRep, chartRadialCurve_zero,
      tangentCoordChange_self (mem_extChartAt_source p)] using hVinit
  refine ⟨V, hV, hV0, ?_⟩
  intro s hs hsU
  let f : ℝ → ℝ := fun t => s * Real.smoothTransition t
  have hf : ContDiff ℝ 1 f := contDiff_const.mul Real.smoothTransition.contDiff
  have hfrange : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t _
    exact ⟨mul_nonneg hs.1 (Real.smoothTransition.nonneg t),
      (mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one t) hs.1).trans
        (by simpa using hs.2)⟩
  have hcurve : chartRadialCurve (I := I) p x ∘ f =
      localTransportCurve (I := I) p (chartRadialCurve (I := I) p x s) := by
    funext t
    exact (localTransportCurve_chartRadialCurve p x hr hball hx hs t).symm
  have hcr : ContMDiff 𝓘(ℝ, ℝ) I 1 (chartRadialCurve (I := I) p x ∘ f) :=
    hcurve.symm ▸ (hC _ hsU).1
  have heval := parallelTransportTangentEquiv_reparam_apply_of_single_chart
    g p (by norm_num : (0 : ℝ) < 1) hcr hsrc hV hfrange
    (fun t _ => (hf.differentiable (by simp) t).hasDerivAt.hasDerivWithinAt)
  have hVf0 : V (f 0) = v :=
    (congrArg (fun t : ℝ => (V t : E)) (show f 0 = 0 by simp [f])).trans hV0
  have hVf1 : V (f 1) = V s :=
    congrArg (fun t : ℝ => (V t : E)) (show f 1 = s by simp [f])
  rw [hVf0, hVf1] at heval
  change parallelTransportTangentBetween g (by norm_num : (0 : ℝ) < 1)
    (hC _ hsU).1 (hC _ hsU).2.1 (hC _ hsU).2.2 v = V s
  rw [parallelTransportTangentBetween_apply_model]
  exact (parallelTransportTangentEquiv_apply_congr_curve g
    (by norm_num : (0 : ℝ) < 1) hcr (hC _ hsU).1 hcurve (v : E)).symm.trans heval

end MorganTianLib
