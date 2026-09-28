import PetersenLib.Ch02.DirectionalDerivative
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-! # Functions with vanishing differential on a connected manifold are constant

If a real-valued function on a manifold has vanishing manifold derivative `mfderiv` at every
point, then it is locally constant (`PetersenLib.isLocallyConstant_of_mfderiv_eq_zero`); on a
preconnected manifold this forces the function to be (globally) constant
(`PetersenLib.apply_eq_of_mfderiv_eq_zero`).

## Design notes

The proof works chart by chart: around any point `a`, the extended chart
`e := extChartAt I a` has open target `e.target` (using `I.Boundaryless`), and the function
written in the chart, `f ∘ e.symm`, is differentiable on `e.target` with vanishing Fréchet
derivative there (this is where the manifold derivative hypothesis is used, via the chain rule
`mfderiv_comp` together with `mfderiv_eq_fderiv` for maps between vector spaces). Since a
small metric ball around `e a` inside `e.target` is convex, hence preconnected,
`IsOpen.exists_is_const_of_fderiv_eq_zero` shows `f ∘ e.symm` is constant on that ball, and
pulling back along `e` produces an open neighbourhood of `a` on which `f` is constant. Hence
`f` is locally constant, and `IsLocallyConstant.apply_eq_of_preconnectedSpace` finishes the job
on a preconnected manifold.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.1.1 (basic facts about the
differential of a function on a manifold).
-/

open Set Function
open scoped ContDiff Manifold Topology

noncomputable section
namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** A real function on a manifold whose manifold differential vanishes identically
is locally constant. -/
theorem isLocallyConstant_of_mfderiv_eq_zero {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ) f) (h : ∀ x, mfderiv I 𝓘(ℝ) f x = 0) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro a
  set e := extChartAt I a with he_def
  have htarget : IsOpen e.target := isOpen_extChartAt_target a
  have hmem : e a ∈ e.target := mem_extChartAt_target a
  have hrange : Set.range I = Set.univ := ModelWithCorners.Boundaryless.range_eq_univ
  -- `f` written in the chart `e` is differentiable on `e.target`, with vanishing derivative.
  have hfderiv : ∀ z ∈ e.target, DifferentiableAt ℝ (f ∘ e.symm) z ∧ fderiv ℝ (f ∘ e.symm) z = 0 := by
    intro z hz
    have hsymm : MDifferentiableAt (𝓘(ℝ, E)) I e.symm z := by
      have := mdifferentiableWithinAt_extChartAt_symm (x := a) hz
      rw [hrange, mdifferentiableWithinAt_univ] at this
      exact this
    have hf' : MDifferentiableAt I 𝓘(ℝ) f (e.symm z) := hf (e.symm z)
    have hcomp : MDifferentiableAt (𝓘(ℝ, E)) 𝓘(ℝ) (f ∘ e.symm) z := hf'.comp z hsymm
    have hmfderiv : mfderiv (𝓘(ℝ, E)) 𝓘(ℝ) (f ∘ e.symm) z
        = (mfderiv I 𝓘(ℝ) f (e.symm z)).comp (mfderiv (𝓘(ℝ, E)) I e.symm z) :=
      mfderiv_comp z hf' hsymm
    rw [h (e.symm z), ContinuousLinearMap.zero_comp] at hmfderiv
    refine ⟨hcomp.differentiableAt, ?_⟩
    rw [← mfderiv_eq_fderiv]
    exact hmfderiv
  have hdiffOn : DifferentiableOn ℝ (f ∘ e.symm) e.target := fun z hz => (hfderiv z hz).1.differentiableWithinAt
  have hderivOn : e.target.EqOn (fderiv ℝ (f ∘ e.symm)) 0 := fun z hz => (hfderiv z hz).2
  -- pick a small convex (hence preconnected) ball inside `e.target`
  obtain ⟨r, hr, hballsub⟩ := Metric.isOpen_iff.mp htarget (e a) hmem
  have hballconn : IsPreconnected (Metric.ball (e a) r) := (convex_ball (e a) r).isPreconnected
  have hballopen : IsOpen (Metric.ball (e a) r) := Metric.isOpen_ball
  obtain ⟨c, hc⟩ := hballopen.exists_is_const_of_fderiv_eq_zero
    hballconn (hdiffOn.mono hballsub) (hderivOn.mono hballsub)
  -- pull the constancy on the ball back through the chart to a neighbourhood of `a`
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e a) r, ?_, ?_, ?_⟩
  · exact isOpen_extChartAt_preimage' a Metric.isOpen_ball
  · exact ⟨mem_extChartAt_source a, Metric.mem_ball_self hr⟩
  · rintro b ⟨hb1, hb2⟩
    have hb : f b = (f ∘ e.symm) (e b) := by
      simp [Function.comp, PartialEquiv.left_inv e hb1]
    have ha : f a = (f ∘ e.symm) (e a) := by
      simp [Function.comp, PartialEquiv.left_inv e (mem_extChartAt_source a)]
    rw [hb, hc (e b) hb2, ha, hc (e a) (Metric.mem_ball_self hr)]

/-- **Math.** A real function on a preconnected manifold whose manifold differential
vanishes identically is constant. -/
theorem apply_eq_of_mfderiv_eq_zero [PreconnectedSpace M] {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ) f) (h : ∀ x, mfderiv I 𝓘(ℝ) f x = 0) (x y : M) :
    f x = f y :=
  (isLocallyConstant_of_mfderiv_eq_zero hf h).apply_eq_of_preconnectedSpace x y

end PetersenLib
