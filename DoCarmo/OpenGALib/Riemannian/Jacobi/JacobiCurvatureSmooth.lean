import OpenGALib.Riemannian.Jacobi.ChartCurvatureContraction
import OpenGALib.Riemannian.Geodesic.ODESmoothness

/-!
# `C^∞` regularity of the chart curvature operator along a smooth geodesic

`ChartCurvatureContraction.lean` builds the chart curvature contraction `t ↦ R(u̇(t), ·)u̇(t)`
(`chartCurvatureOp`) as an operator field along a coordinate curve `u`, and proves it is
**continuous** in `t` when `u` and `u̇` are continuous (`continuousOn_chartCurvatureOp`).  For the
fourth-order Taylor expansion of `|J(t)|²` (do Carmo Ch. 5, Prop. 2.7) the abstract analytic core
`norm_sq_jacobi_isLittleO_local` needs the coefficient operator `A(t)` to be `C^∞`, not merely
continuous.

This file provides that upgrade: along a curve `u` that is `C^∞` on an open time set `s` and stays
in the chart interior, `chartCurvatureOp g α u` is `C^∞` on `s`.  The pointwise curvature
coefficient `Rˡ_{ijk}` is already `C^∞` on the chart (`chartCurvatureCoef_contDiffOn`), and the
velocity coordinates `u̇ⁱ` are `C^∞` once `u` is (`u̇ = deriv u` is `C^∞` on the open `s`), so the
operator — a finite sum of products of these times constant elementary operators — is `C^∞`.

For the geodesic `t ↦ exp_p(t v)`, the chart reading `u = φ_p ∘ γ` is `C^∞` on the open time
interval where `γ` stays in the chart at `p`, by the `C^∞` smoothness of `exp_p` on a ball
(`exists_contDiffOn_infty_extChartAt_expMap_ball`); this lemma then supplies the `C^∞` frame
curvature `A(t)` for that instantiation.
-/

open Set
open scoped ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **`C^∞` smoothness of the chart curvature operator.** Along a coordinate curve `u`
that is `C^∞` on an open time set `s` and stays in the chart interior, the curvature contraction
`t ↦ R(u̇(t), ·)u̇(t)` (`chartCurvatureOp`) is `C^∞` in `t` on `s`.  This is the `C^∞` upgrade of
`continuousOn_chartCurvatureOp`, supplying the `ContDiffOn ℝ ∞ A` hypothesis of the Taylor core
`norm_sq_jacobi_isLittleO_local` (do Carmo Ch. 5, Prop. 2.7). -/
theorem contDiffOn_infty_chartCurvatureOp (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    {s : Set ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (hmem : ∀ t ∈ s, u t ∈ interior (extChartAt I α).target) :
    ContDiffOn ℝ ∞ (chartCurvatureOp (I := I) g α u) s := by
  -- `u̇ = deriv u` is `C^∞` on the open set `s`
  have hu' : ContDiffOn ℝ ∞ (deriv u) s := by
    have h : ContDiffOn ℝ ∞ (derivWithin u s) s := hu.derivWithin hs.uniqueDiffOn (by simp)
    rwa [contDiffOn_congr (fun x hx => (derivWithin_of_isOpen hs hx))] at h
  -- the velocity coordinate `t ↦ u̇ⁱ(t)` is `C^∞` (a `C^∞` linear functional of the `C^∞` `u̇`)
  have hvel : ∀ i : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun t => Geodesic.chartCoord (E := E) i (deriv u t)) s := fun i => by
    have := (Geodesic.chartCoordFunctional (E := E) i).contDiff.comp_contDiffOn hu'
    simpa only [Geodesic.chartCoordFunctional_apply] using this
  unfold chartCurvatureOp
  refine ContDiffOn.sum (fun l _ => ContDiffOn.sum (fun j _ => ?_))
  have hscalar : ContDiffOn ℝ ∞
      (fun t => ∑ i, ∑ k, chartCurvatureCoef (I := I) g α i j k l (u t)
        * Geodesic.chartCoord (E := E) i (deriv u t)
        * Geodesic.chartCoord (E := E) k (deriv u t)) s := by
    refine ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun k _ => ?_))
    have hcoef : ContDiffOn ℝ ∞ (fun t => chartCurvatureCoef (I := I) g α i j k l (u t)) s :=
      (chartCurvatureCoef_contDiffOn g α i j k l).comp hu hmem
    exact (hcoef.mul (hvel i)).mul (hvel k)
  exact hscalar.smul (contDiffOn_const
    (c := (Geodesic.chartCoordFunctional (E := E) j).smulRight (Module.finBasis ℝ E l)))

end Riemannian.Jacobi

end
