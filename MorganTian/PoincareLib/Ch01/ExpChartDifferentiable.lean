import PoincareLib.Ch01.ExpContinuity
import PoincareLib.Ch01.ExpDifferential

/-!
# Morgan–Tian Ch. 1, §1.4 — `exp_p` is differentiable read in *any* chart

`Ch01/ExpDifferential.lean` produces, for each `v ∈ T_pM`, *some* chart `ζ` around `exp_p(v)` in
which `exp_p` has a derivative at `v` (the chart is whichever one the Jacobi-transport chain hands
back). That is enough to talk about `d(exp_p)_v` up to conjugation, but it is *not* enough for the
measure theory: to prove that `exp_p` carries null sets to null sets we must read `exp_p` in a
*prescribed* chart — the one covering the piece of `M` we are integrating over — and know it is
differentiable there.

This file removes the chart from the statement:

  `differentiableAt_extChartAt_expMapGlobal` :
    for every `α : M` with `exp_p(v) ∈ (extChartAt I α).source`,
    `w ↦ extChartAt I α (exp_p w)` is differentiable at `v`.

The proof is the only thing it can be: transition maps are smooth. Writing `ζ` for the chart
supplied by `ExpDifferential`, near `v` we have

  `extChartAt α ∘ exp_p = (extChartAt α ∘ (extChartAt ζ).symm) ∘ (extChartAt ζ ∘ exp_p)`,

the outer factor being differentiable by `hasFDerivWithinAt_tangentCoordChange` (with
`range I = univ`, as `I` is boundaryless) and the inner one by `ExpDifferential`. The identity holds
only *near* `v` — one needs `exp_p w` to stay in the source of `ζ`, which continuity of `exp_p`
supplies — so the conclusion is transported along an `EventuallyEq`.
-/

open Set Riemannian Riemannian.Geodesic Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

-- NOTE: no standalone `[NormedSpace ℝ E]` here, for the reason spelled out in `ExpContinuity`:
-- declaring one alongside `[InnerProductSpace ℝ E]` creates a genuine instance diamond, and the
-- defeq check against `ExpContinuity`'s lemmas (whose `NormedSpace` is `InnerProductSpace.to…`)
-- then fails to terminate. Mirror that block exactly.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]

/-- **Math.** The extended chart transition `extChartAt α ∘ (extChartAt ζ).symm` is differentiable
at the `ζ`-coordinates of any point lying in both chart sources.

This is `hasFDerivWithinAt_tangentCoordChange` with the `range I = univ` of a boundaryless model
discharged; its derivative is the tangent coordinate change. -/
theorem differentiableAt_extChartAt_comp_symm (ζ α : M) {q : M}
    (hζ : q ∈ (extChartAt I ζ).source) (hα : q ∈ (extChartAt I α).source) :
    DifferentiableAt ℝ ((extChartAt I α) ∘ (extChartAt I ζ).symm) (extChartAt I ζ q) := by
  have hd := hasFDerivWithinAt_tangentCoordChange (I := I) (x := ζ) (y := α) (z := q) ⟨hζ, hα⟩
  rw [I.range_eq_univ] at hd
  exact (hasFDerivWithinAt_univ.mp hd).differentiableAt

/-- **Math.** **`exp_p` is differentiable at every `v`, read in every chart around `exp_p(v)`.**

No hypothesis beyond completeness: the exponential map of a complete Riemannian manifold is
differentiable everywhere on `T_pM` (indeed smooth, but differentiability is all the change of
variables needs), and the chart in which one reads it is immaterial. -/
theorem differentiableAt_extChartAt_expMapGlobal (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) (p : M) (α : M) {v : E}
    (hv : expMapGlobal (I := I) g hg p v ∈ (extChartAt I α).source) :
    DifferentiableAt ℝ (fun w : E => extChartAt I α (expMapGlobal (I := I) g hg p w)) v := by
  -- the chart `ζ` in which `ExpDifferential` gives a derivative at `v`
  obtain ⟨ζ, D, J, DJ, hζsrc, hD, -⟩ :=
    expDifferential_eq_jacobiField (I := I) g hg p v 0
  rw [← extChartAt_source (I := I) ζ] at hζsrc
  -- the inner factor: `exp_p` read in the chart `ζ`
  have hG : DifferentiableAt ℝ
      (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) v := hD.differentiableAt
  -- the outer factor: the chart transition, differentiable at the `ζ`-coordinates of `exp_p v`
  have hτ : DifferentiableAt ℝ ((extChartAt I α) ∘ (extChartAt I ζ).symm)
      (extChartAt I ζ (expMapGlobal (I := I) g hg p v)) :=
    differentiableAt_extChartAt_comp_symm (I := I) ζ α hζsrc hv
  have hcomp := hτ.comp v hG
  -- near `v` the composite is the chart-`α` reading of `exp_p`: `exp_p w` stays in the source of ζ
  refine hcomp.congr_of_eventuallyEq ?_
  have hopen : IsOpen {w : E | expMapGlobal (I := I) g hg p w ∈ (extChartAt I ζ).source} :=
    (isOpen_extChartAt_source (I := I) ζ).preimage (continuous_expMapGlobal (I := I) g hg p)
  have hmem : v ∈ {w : E | expMapGlobal (I := I) g hg p w ∈ (extChartAt I ζ).source} := hζsrc
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) fun w hw => ?_
  simp only [Function.comp_apply]
  rw [(extChartAt I ζ).left_inv hw]

end PoincareLib

end
