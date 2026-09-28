import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Local smooth curves for parallel transport

An open neighborhood of each point of a smooth boundaryless manifold can be
joined to that point by curves smooth on the whole real line. The construction
interpolates in a convex chart ball, using a smooth transition constant before
time zero and after time one.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter
open scoped Topology ContDiff Manifold

noncomputable section

namespace MorganTianLib

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H M]

/-- Chart interpolation with time constant outside the unit interval. -/
def localTransportCurve (p x : M) (t : ℝ) : M :=
  (extChartAt I p).symm ((1 - Real.smoothTransition t) • extChartAt I p p +
    Real.smoothTransition t • extChartAt I p x)

/-- The curve with both endpoints at its centre is constant. -/
@[simp]
theorem localTransportCurve_self (p : M) (t : ℝ) :
    localTransportCurve (I := I) p p t = p := by
  simp [localTransportCurve, ← add_smul]

private theorem localTransportCoordinate_mem_ball (p x : M) {r : ℝ} (hr : 0 < r)
    (hx : extChartAt I p x ∈ Metric.ball (extChartAt I p p) r) (t : ℝ) :
    (1 - Real.smoothTransition t) • extChartAt I p p +
      Real.smoothTransition t • extChartAt I p x ∈ Metric.ball (extChartAt I p p) r :=
  (convex_ball (extChartAt I p p) r) (Metric.mem_ball_self hr) hx
    (sub_nonneg.mpr (Real.smoothTransition.le_one t))
    (Real.smoothTransition.nonneg t) (sub_add_cancel 1 (Real.smoothTransition t))

/-- **Math.** In a chart ball contained in the chart target, the curve's chart
coordinates are precisely its defining affine interpolation. -/
theorem extChartAt_localTransportCurve_of_mem_ball (p x : M) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (extChartAt I p p) r ⊆ (extChartAt I p).target)
    (hx : extChartAt I p x ∈ Metric.ball (extChartAt I p p) r) (t : ℝ) :
    extChartAt I p (localTransportCurve (I := I) p x t) =
      (1 - Real.smoothTransition t) • extChartAt I p p +
        Real.smoothTransition t • extChartAt I p x :=
  (extChartAt I p).right_inv (hball (localTransportCoordinate_mem_ball p x hr hx t))

/-- **Math.** Every point on the interpolating curve remains in the same chart ball. -/
theorem localTransportCurve_mem_chartBall (p x : M) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (extChartAt I p p) r ⊆ (extChartAt I p).target)
    (hx : extChartAt I p x ∈ Metric.ball (extChartAt I p p) r) (t : ℝ) :
    localTransportCurve (I := I) p x t ∈ (extChartAt I p).source ∩
      (extChartAt I p) ⁻¹' Metric.ball (extChartAt I p p) r := by
  refine ⟨(extChartAt I p).map_target
    (hball (localTransportCoordinate_mem_ball p x hr hx t)), ?_⟩
  change extChartAt I p (localTransportCurve (I := I) p x t) ∈
    Metric.ball (extChartAt I p p) r
  rw [extChartAt_localTransportCurve_of_mem_ball p x hr hball hx t]
  exact localTransportCoordinate_mem_ball p x hr hx t

/-- **Math.** A curve to a point on a radial curve follows the same chart ray;
the two interpolation parameters multiply. -/
theorem localTransportCurve_nested (p x : M) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (extChartAt I p p) r ⊆ (extChartAt I p).target)
    (hx : extChartAt I p x ∈ Metric.ball (extChartAt I p p) r) (s t : ℝ) :
    localTransportCurve (I := I) p (localTransportCurve (I := I) p x s) t =
      (extChartAt I p).symm
        ((1 - Real.smoothTransition s * Real.smoothTransition t) • extChartAt I p p +
          (Real.smoothTransition s * Real.smoothTransition t) • extChartAt I p x) := by
  change (extChartAt I p).symm
    ((1 - Real.smoothTransition t) • extChartAt I p p +
      Real.smoothTransition t • extChartAt I p (localTransportCurve (I := I) p x s)) = _
  rw [extChartAt_localTransportCurve_of_mem_ball p x hr hball hx s]
  congr 1
  simp only [smul_add, smul_smul, ← add_assoc, ← add_smul]
  have hcoeff : (1 - Real.smoothTransition t) +
      Real.smoothTransition t * (1 - Real.smoothTransition s) =
        1 - Real.smoothTransition s * Real.smoothTransition t := by ring
  rw [hcoeff, mul_comm (Real.smoothTransition t)]

variable [I.Boundaryless] [IsManifold I ∞ M]

/-- **Math.** The explicit chart curves join a point to every point in an open
neighborhood, remain in that neighborhood, and depend smoothly on endpoint and time. -/
theorem exists_open_nhds_localTransportCurve (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      (∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I ∞ (localTransportCurve (I := I) p x) ∧
        localTransportCurve (I := I) p x 0 = p ∧
        localTransportCurve (I := I) p x 1 = x) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : M × ℝ => localTransportCurve (I := I) p q.1 q.2) (U ×ˢ univ) ∧
      (∀ x ∈ U, ∀ t : ℝ, extChartAt I p (localTransportCurve (I := I) p x t) =
        (1 - Real.smoothTransition t) • extChartAt I p p +
          Real.smoothTransition t • extChartAt I p x) ∧
      (∀ x ∈ U, ∀ t : ℝ, localTransportCurve (I := I) p x t ∈ U) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (extChartAt_target_mem_nhds (I := I) p)
  let U : Set M := (extChartAt I p).source ∩
    (extChartAt I p) ⁻¹' Metric.ball (extChartAt I p p) r
  have hUopen : IsOpen U := (continuousOn_extChartAt p).isOpen_inter_preimage
    (isOpen_extChartAt_source p) Metric.isOpen_ball
  have hpU : p ∈ U := ⟨mem_extChartAt_source p, Metric.mem_ball_self hr⟩
  let a : E × ℝ → E := fun q =>
    (1 - Real.smoothTransition q.2) • extChartAt I p p +
      Real.smoothTransition q.2 • q.1
  have ha_target (x : M) (hx : x ∈ U) (t : ℝ) :
      a (extChartAt I p x, t) ∈ (extChartAt I p).target := by
    exact hball (localTransportCoordinate_mem_ball p x hr hx.2 t)
  have ha : ContDiff ℝ ∞ a :=
    ((contDiff_const.sub (Real.smoothTransition.contDiff.comp contDiff_snd)).smul
      contDiff_const).add
        ((Real.smoothTransition.contDiff.comp contDiff_snd).smul contDiff_fst)
  refine ⟨U, hUopen, hpU, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨?_, ?_, ?_⟩
    · intro t
      exact ((contMDiffOn_extChartAt_symm p).contMDiffAt
        (extChartAt_target_mem_nhds' (ha_target x hx t))).comp t
          (ha.comp (contDiff_const.prodMk contDiff_id)).contMDiff.contMDiffAt
    · simp [localTransportCurve]
    · simpa [localTransportCurve] using (extChartAt I p).left_inv hx.1
  · intro q hq
    have hxsource : q.1 ∈ (chartAt H p).source := by
      simpa only [extChartAt_source] using hq.1.1
    have hcoord : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) ∞
        (fun q : M × ℝ => (extChartAt I p q.1, q.2)) q :=
      ((contMDiffAt_extChartAt' (I := I) hxsource).comp q
        contMDiffAt_fst).prodMk_space
        contMDiffAt_snd
    exact (((contMDiffOn_extChartAt_symm p).contMDiffAt
      (extChartAt_target_mem_nhds' (ha_target q.1 hq.1 q.2))).comp q
        (ha.comp_contMDiffAt hcoord)).contMDiffWithinAt
  · intro x hx t
    exact extChartAt_localTransportCurve_of_mem_ball p x hr hball hx.2 t
  · intro x hx t
    exact localTransportCurve_mem_chartBall p x hr hball hx.2 t

/-- **Math.** Every point has an open neighborhood whose points are joined to it
by globally smooth real-parameter curves. -/
theorem exists_open_nhds_contMDiff_curve (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U,
      ∃ c : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ c ∧ c 0 = p ∧ c 1 = x := by
  obtain ⟨U, hU, hp, hcurves, _⟩ := exists_open_nhds_localTransportCurve (I := I) p
  exact ⟨U, hU, hp, fun x hx => ⟨localTransportCurve (I := I) p x, hcurves x hx⟩⟩

end MorganTianLib
