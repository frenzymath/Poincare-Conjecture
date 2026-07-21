/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Geodesic/FlowGeodesic.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Geodesic.EquationTransfer

set_option linter.unusedSectionVars false

/-!
# Coordinate spray solutions are intrinsic geodesics

A solution `ζ : ℝ → E × E` of the coordinate geodesic spray ODE
`ζ' = F_q(ζ)`, `F_q(x, w) = (w, -Γ_q(w, w)(x))` in the chart at `q : M`,
whose position component stays in the chart target, projects to a base curve

`sprayBase q ζ = τ ↦ (extChartAt I q).symm (ζ τ).1`

on `M`. This file shows that on any open set of times where the ODE holds the
base curve is continuous and satisfies the intrinsic (moving-foot) geodesic
equation — the bridge from Picard–Lindelöf flows (`UniformExistence.lean`) to
the intrinsic geodesic predicates `IsGeodesicOn`/`IsGeodesic` of
`Equation.lean`.

The proof route: the position component `u = (ζ ·).1` is the chart-`q` reading
of the base curve; the spray ODE says precisely that `u' = (ζ ·).2` and
`u'' = -Γ_q(u', u')(u)`, i.e. the base curve solves the second-order geodesic
ODE in the chart at `q` (`SolvesGeodesicODEAt`); the chart-independence
theorem (`SolvesGeodesicODEAt.hasGeodesicEquationAt`,
`EquationTransfer.lean`) then yields the intrinsic geodesic equation.

This replaces the chart-anchored witness route of `ChartFlow.lean` for all
*global* geodesic purposes (do Carmo Ch. 7): the output predicate is the
intrinsic one, meaningful beyond the chart at `q`.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-- **Math.** The base curve of a coordinate spray solution: the position
component of `ζ : ℝ → E × E`, pulled back to `M` through the chart at `q`. -/
def sprayBase (q : M) (ζ : ℝ → E × E) : ℝ → M :=
  fun τ => (extChartAt I q).symm (ζ τ).1

@[simp] lemma sprayBase_apply (q : M) (ζ : ℝ → E × E) (τ : ℝ) :
    sprayBase (I := I) q ζ τ = (extChartAt I q).symm (ζ τ).1 := rfl

section SprayBase

variable {g : RiemannianMetric I M} {q : M} {ζ : ℝ → E × E} {J : Set ℝ}

/-- **Math.** The base curve of a spray solution confined to the chart target
stays in the chart source at `q`. -/
theorem sprayBase_mem_chart_source
    (hmem : ∀ τ ∈ J, (ζ τ).1 ∈ (extChartAt I q).target) {τ : ℝ} (hτ : τ ∈ J) :
    sprayBase (I := I) q ζ τ ∈ (chartAt H q).source := by
  have := (extChartAt I q).map_target (hmem τ hτ)
  rwa [extChartAt_source] at this

/-- **Math.** The chart-`q` reading of the base curve recovers the position
component of the spray solution. -/
theorem chartReading_sprayBase
    (hmem : ∀ τ ∈ J, (ζ τ).1 ∈ (extChartAt I q).target) {τ : ℝ} (hτ : τ ∈ J) :
    chartReading (I := I) q (sprayBase (I := I) q ζ) τ = (ζ τ).1 :=
  (extChartAt I q).right_inv (hmem τ hτ)

/-- **Math.** The base curve of a (differentiable) spray solution is continuous on
the set where the ODE holds. -/
theorem continuousOn_sprayBase
    (hd : ∀ τ ∈ J, HasDerivAt ζ
      (geodesicSprayCoord (I := I) g q (ζ τ).1 (ζ τ).2) τ)
    (hmem : ∀ τ ∈ J, (ζ τ).1 ∈ (extChartAt I q).target) :
    ContinuousOn (sprayBase (I := I) q ζ) J := by
  have hpos : ContinuousOn (fun τ => (ζ τ).1) J := fun τ hτ =>
    ((hd τ hτ).continuousAt.continuousWithinAt).fst
  exact (continuousOn_extChartAt_symm q).comp hpos hmem

/-- **Math.** The chart-`q` reading of the base curve of a spray solution is
differentiable at every time of the (open) ODE set, with derivative the
velocity component of the solution: the spray ODE's first equation `x' = w`. -/
theorem hasDerivAt_chartReading_sprayBase (hJ : IsOpen J)
    (hd : ∀ τ ∈ J, HasDerivAt ζ
      (geodesicSprayCoord (I := I) g q (ζ τ).1 (ζ τ).2) τ)
    (hmem : ∀ τ ∈ J, (ζ τ).1 ∈ (extChartAt I q).target)
    {τ : ℝ} (hτ : τ ∈ J) :
    HasDerivAt (chartReading (I := I) q (sprayBase (I := I) q ζ)) ((ζ τ).2) τ := by
  -- the position component has derivative the velocity component: `x' = w`
  have hpos : HasDerivAt (fun τ' => (ζ τ').1) ((ζ τ).2) τ := by
    have h := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt τ (hd τ hτ)
    simpa using h
  -- the chart reading agrees with the position component near `τ`
  refine hpos.congr_of_eventuallyEq ?_
  filter_upwards [hJ.mem_nhds hτ] with τ' hτ'
  exact chartReading_sprayBase (I := I) hmem hτ'

/-- **Math.** **Spray solutions are intrinsic geodesics.** The base curve of a
coordinate spray solution on an open set of times, confined to the chart
target at `q`, satisfies the intrinsic (moving-foot) geodesic equation at
every time of the set (do Carmo Ch. 3, Definition 2.1 / the local existence
Theorem 2.2, in intrinsic form). -/
theorem isGeodesicOn_sprayBase (hJ : IsOpen J)
    (hd : ∀ τ ∈ J, HasDerivAt ζ
      (geodesicSprayCoord (I := I) g q (ζ τ).1 (ζ τ).2) τ)
    (hmem : ∀ τ ∈ J, (ζ τ).1 ∈ (extChartAt I q).target) :
    IsGeodesicOn (I := I) g (sprayBase (I := I) q ζ) J := by
  intro t ht
  have hcont : ContinuousAt (sprayBase (I := I) q ζ) t :=
    (continuousOn_sprayBase (I := I) hd hmem).continuousAt (hJ.mem_nhds ht)
  refine SolvesGeodesicODEAt.hasGeodesicEquationAt (α := q) ⟨?_, ?_⟩ hcont
    (sprayBase_mem_chart_source (I := I) hmem ht)
  · -- the chart reading is differentiable near `t`
    filter_upwards [hJ.mem_nhds ht] with τ hτ
    have h1 := hasDerivAt_chartReading_sprayBase (I := I) hJ hd hmem hτ
    exact h1.deriv ▸ h1
  · -- second derivative: the spray ODE's second equation `w' = -Γ_q(w, w)(x)`
    have hderiv_eq : deriv (chartReading (I := I) q (sprayBase (I := I) q ζ))
        =ᶠ[𝓝 t] fun τ => (ζ τ).2 := by
      filter_upwards [hJ.mem_nhds ht] with τ hτ
      exact (hasDerivAt_chartReading_sprayBase (I := I) hJ hd hmem hτ).deriv
    have hvel : HasDerivAt (fun τ => (ζ τ).2)
        (- chartChristoffelContraction (I := I) g q ((ζ t).2) ((ζ t).2) ((ζ t).1)) t := by
      have h := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t (hd t ht)
      simpa using h
    refine ⟨- chartChristoffelContraction (I := I) g q ((ζ t).2) ((ζ t).2) ((ζ t).1),
      hvel.congr_of_eventuallyEq hderiv_eq, ?_⟩
    rw [hderiv_eq.self_of_nhds, chartReading_sprayBase (I := I) hmem ht]
    exact neg_add_cancel _

end SprayBase

end Geodesic
end PetersenLib

end
