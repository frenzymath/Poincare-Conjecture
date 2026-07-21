import DoCarmoLib.Riemannian.Jacobi.FlowStepManifold
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Poincaré Ch. 1, §1.4 — translation-invariance of the geodesic equation

The flow-derivative gluing that computes `d(exp_p)_v`
(`cor:dc-ch5-2-5`) reads the geodesic `γ = γ_v` in
successive charts along `[0,1]`, and each within-chart geodesic-flow step runs
on its *own* internal clock starting at `0`. To glue a flow step *based at an
arbitrary time* `a` along `γ` — rather than only at `t = 0` — one compares the
flow's internal base geodesic (a `0`-clock curve) with the *time-shifted*
geodesic `σ ↦ γ (a + σ)`. This file supplies the missing ingredient: the
moving-foot geodesic equation is invariant under a constant time shift, so the
shifted curve is again an intrinsic geodesic.

* `HasGeodesicEquationAt.comp_const_add` — pointwise translation invariance:
  `HasGeodesicEquationAt g γ (c + σ)` gives `HasGeodesicEquationAt g (γ (c + ·)) σ`.
* `IsGeodesicOn.comp_const_add` — its set-relativised form: a geodesic on `s`
  becomes a geodesic on the preimage `{σ | c + σ ∈ s}` after the shift.

The chart-local curve of the shifted geodesic is the chart-local curve of `γ`
precomposed with `s ↦ c + s`; the derivative facts translate by the chain rule
(`deriv_comp_const_add`, `HasDerivAt.comp`), the neighbourhood filter by
`Tendsto.const_add`, and the Christoffel term is unchanged because the foot
`γ (c + σ)` and its chart reading are the same.

Blueprint: `cor:dc-ch5-2-5`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **Translation invariance of the geodesic equation.** If `γ`
satisfies the moving-foot geodesic equation at time `c + σ`, then the
time-shifted curve `s ↦ γ (c + s)` satisfies it at time `σ`. The chart-local
curve of the shifted geodesic is `chartLocalCurve γ (c + σ)` precomposed with
`s ↦ c + s`; velocity and acceleration transport by the chain rule (the shift
has derivative `1`), and the Christoffel corrector is unchanged since the foot
point `γ (c + σ)` and its chart reading do not move. -/
theorem HasGeodesicEquationAt.comp_const_add (g : RiemannianMetric I M) {γ : ℝ → M}
    {c σ : ℝ} (h : HasGeodesicEquationAt (I := I) g γ (c + σ)) :
    HasGeodesicEquationAt (I := I) g (fun s => γ (c + s)) σ := by
  obtain ⟨v, a, hv, hev, ha, hchr⟩ := h
  set φ : ℝ → E := chartLocalCurve (I := I) γ (c + σ) with hφdef
  -- the constant time shift is differentiable with derivative `1` at every point
  have hadd : ∀ x : ℝ, HasDerivAt (fun s : ℝ => c + s) 1 x := fun x => by
    simpa using (hasDerivAt_id x).const_add c
  -- the chart-local curve of the shifted geodesic is `φ` precomposed with `c + ·`
  have hshift : chartLocalCurve (I := I) (fun s => γ (c + s)) σ = fun s => φ (c + s) := by
    funext s
    simp only [hφdef, chartLocalCurve_def]
  -- its derivative is `deriv φ` precomposed with `c + ·`
  have hderivEq : deriv (chartLocalCurve (I := I) (fun s => γ (c + s)) σ)
      = fun s => deriv φ (c + s) := by
    rw [hshift]; funext s; exact deriv_comp_const_add φ c s
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · -- velocity: `HasDerivAt (chartLocalCurve γ̃ σ) v σ`
    rw [hshift]
    simpa using hv.scomp σ (hadd σ)
  · -- the ambient differentiability, pulled back along the shift
    have htend : Tendsto (fun s : ℝ => c + s) (𝓝 σ) (𝓝 (c + σ)) := by
      simpa using (continuous_const.add continuous_id).tendsto σ
    filter_upwards [htend.eventually hev] with s hs
    rw [hshift, deriv_comp_const_add]
    simpa using hs.scomp s (hadd s)
  · -- acceleration: `HasDerivAt (deriv (chartLocalCurve γ̃ σ)) a σ`
    rw [hderivEq]
    simpa using ha.scomp σ (hadd σ)
  · -- the Christoffel corrector is unchanged
    exact hchr

/-- **Math.** **Translation invariance of `IsGeodesicOn`.** A geodesic of `g` on
`s : Set ℝ` remains a geodesic after a constant time shift `c`, on the shifted
set `{σ | c + σ ∈ s}`. -/
theorem IsGeodesicOn.comp_const_add (g : RiemannianMetric I M) {γ : ℝ → M} {c : ℝ}
    {s : Set ℝ} (hgeo : IsGeodesicOn (I := I) g γ s) :
    IsGeodesicOn (I := I) g (fun σ => γ (c + σ)) {σ | c + σ ∈ s} :=
  fun σ hσ => HasGeodesicEquationAt.comp_const_add g (hgeo (c + σ) hσ)

end Riemannian.Jacobi

end
