import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Vanishing differential forces constancy on a connected manifold

A real function on a manifold whose manifold differential vanishes at every point
is locally constant, and hence constant when the manifold is connected. This is
the step Topping's Chapter 2 uses silently when it concludes from Schur's identity
`(n-2)dλ = 0` that `λ` and the scalar curvature *are constant*: what the identity
gives is the vanishing of a differential, and constancy needs connectedness.

The argument is chart-local and standard. Around a point `a` the extended chart
`e` has open target (boundarylessness), the function read in the chart is
differentiable there with vanishing Fréchet derivative (chain rule plus
`mfderiv_eq_fderiv`), and a metric ball inside the target is convex, hence
preconnected — so mathlib's `IsOpen.exists_is_const_of_fderiv_eq_zero` makes the
chart representation constant on that ball. Pulling back through the chart gives a
neighbourhood of `a` on which the function is constant.

This duplicates `PetersenLib.isLocallyConstant_of_mfderiv_eq_zero`, which Topping
does not depend on; it needs nothing but mathlib, so it is carried here rather than
adding a project dependency. If Petersen ever becomes a Topping dependency this
module should be deleted in favour of it.
-/

open Set Function
open scoped ContDiff Manifold Topology

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** A real function on a manifold whose manifold differential vanishes
identically is locally constant. -/
theorem isLocallyConstant_of_mfderiv_eq_zero {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ) f) (h : ∀ x, mfderiv I 𝓘(ℝ) f x = 0) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro a
  set e := extChartAt I a with he_def
  have htarget : IsOpen e.target := isOpen_extChartAt_target a
  have hmem : e a ∈ e.target := mem_extChartAt_target a
  have hrange : Set.range I = Set.univ := ModelWithCorners.Boundaryless.range_eq_univ
  -- `f` read in the chart is differentiable on the target, with zero derivative.
  have hfderiv : ∀ z ∈ e.target,
      DifferentiableAt ℝ (f ∘ e.symm) z ∧ fderiv ℝ (f ∘ e.symm) z = 0 := by
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
  have hdiffOn : DifferentiableOn ℝ (f ∘ e.symm) e.target :=
    fun z hz => (hfderiv z hz).1.differentiableWithinAt
  have hderivOn : e.target.EqOn (fderiv ℝ (f ∘ e.symm)) 0 :=
    fun z hz => (hfderiv z hz).2
  -- A convex, hence preconnected, ball inside the chart target.
  obtain ⟨r, hr, hballsub⟩ := Metric.isOpen_iff.mp htarget (e a) hmem
  have hballconn : IsPreconnected (Metric.ball (e a) r) :=
    (convex_ball (e a) r).isPreconnected
  have hballopen : IsOpen (Metric.ball (e a) r) := Metric.isOpen_ball
  obtain ⟨c, hc⟩ := hballopen.exists_is_const_of_fderiv_eq_zero
    hballconn (hdiffOn.mono hballsub) (hderivOn.mono hballsub)
  -- Pull the constancy back through the chart.
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e a) r, ?_, ?_, ?_⟩
  · exact isOpen_extChartAt_preimage' a Metric.isOpen_ball
  · exact ⟨mem_extChartAt_source a, Metric.mem_ball_self hr⟩
  · rintro b ⟨hb1, hb2⟩
    have hb : f b = (f ∘ e.symm) (e b) := by
      simp [Function.comp, PartialEquiv.left_inv e hb1]
    have ha : f a = (f ∘ e.symm) (e a) := by
      simp [Function.comp, PartialEquiv.left_inv e (mem_extChartAt_source a)]
    rw [hb, hc (e b) hb2, ha, hc (e a) (Metric.mem_ball_self hr)]

/-- **Math.** A real function on a preconnected manifold whose manifold
differential vanishes identically is constant. -/
theorem apply_eq_of_mfderiv_eq_zero [PreconnectedSpace M] {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ) f) (h : ∀ x, mfderiv I 𝓘(ℝ) f x = 0) (x y : M) :
    f x = f y :=
  (isLocallyConstant_of_mfderiv_eq_zero hf h).apply_eq_of_preconnectedSpace x y

end Topping

end
