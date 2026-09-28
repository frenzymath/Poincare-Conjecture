import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Global `C^∞` extension of a `ContDiffOn` field by a bump multiplier

The abstract `C^∞` dependence of an ODE flow on its initial condition
(`Riemannian.FlowDependence.contDiffAt_flow_of_picardResidual`) is stated for a field that is
`C^∞` **globally** on the whole Banach space, because its proof runs the `C^∞` Nemytskii /
superposition operator (`contDiff_superposition_infty`) over arbitrary curves. The geodesic spray,
however, is only `ContDiffOn ℝ ∞` on the chart region. This file bridges the gap with the classical
*multiply by a bump* extension: a field that is `C^∞` on an open set `U` is modified to a globally
`C^∞` field agreeing with it on a closed ball around any interior point.

* `exists_contDiff_eqOn_closedBall_of_contDiffOn` — given `F` with `ContDiffOn ℝ ∞ F U` on an open
  `U` and `z₀ ∈ U`, there are a radius `a > 0` with `closedBall z₀ a ⊆ U` and a globally `C^∞`
  field `F'` with `F' = F` on `closedBall z₀ a`.

`F'` is `ρ • F`, where `ρ` is a `ContDiffBump` centred at `z₀` equal to `1` on `closedBall z₀ a`
and with `tsupport ρ ⊆ U`. On `U` the product `ρ • F` is `C^∞`; off `tsupport ρ` it vanishes
identically, so it is `C^∞` there too, and the two open regions cover the space. Since the ODE
trajectories we care about stay inside `closedBall z₀ a`, the extended field has the *same flow* as
the original there, while being amenable to the global-smoothness machinery.
-/

open Metric Function Set
open scoped Topology ContDiff

namespace Riemannian

variable {G G' : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup G'] [NormedSpace ℝ G']

/-- **Math.** **Global `C^∞` extension of a locally `C^∞` field.** If `F` is `C^∞` on an open set
`U` and `z₀ ∈ U`, there are a radius `a > 0` with `closedBall z₀ a ⊆ U` and a globally `C^∞` field
`F'` agreeing with `F` on `closedBall z₀ a`. The extension is `ρ • F` for a bump `ρ` centred at
`z₀`, equal to `1` on `closedBall z₀ a` and supported inside `U`; it is `C^∞` because it equals the
`C^∞` product `ρ • F` on `U` and equals `0` off the (closed) support of `ρ`. -/
theorem exists_contDiff_eqOn_closedBall_of_contDiffOn
    {F : G → G'} {U : Set G} (hU : IsOpen U) (hFU : ContDiffOn ℝ ∞ F U)
    {z₀ : G} (hz₀ : z₀ ∈ U) :
    ∃ (F' : G → G') (a : ℝ), 0 < a ∧ closedBall z₀ a ⊆ U ∧
      ContDiff ℝ ∞ F' ∧ Set.EqOn F' F (closedBall z₀ a) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  set bump : ContDiffBump z₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩ with hbump
  -- `tsupport bump ⊆ ball z₀ ε ⊆ U`
  have htsupp : tsupport (⇑bump) ⊆ U := by
    intro x hx
    apply hball
    have h1 : tsupport (⇑bump) ⊆ closedBall z₀ bump.rOut := by
      rw [tsupport, bump.support_eq]; exact closure_ball_subset_closedBall
    have h2 : closedBall z₀ bump.rOut ⊆ ball z₀ ε := by
      apply closedBall_subset_ball; show ε / 2 < ε; linarith
    exact h2 (h1 hx)
  refine ⟨fun x => bump x • F x, ε / 4, by positivity, ?_, ?_, ?_⟩
  · exact subset_trans (by apply closedBall_subset_ball; linarith) hball
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · have hsmul : ContDiffOn ℝ ∞ (fun y => bump y • F y) U :=
        (bump.contDiff (n := ⊤)).contDiffOn.smul hFU
      exact hsmul.contDiffAt (hU.mem_nhds hx)
    · have hxts : x ∉ tsupport (⇑bump) := fun h => hx (htsupp h)
      have hev : (fun y => bump y • F y) =ᶠ[𝓝 x] (fun _ => (0 : G')) := by
        have hopen : (tsupport (⇑bump))ᶜ ∈ 𝓝 x :=
          (isClosed_tsupport _).isOpen_compl.mem_nhds hxts
        filter_upwards [hopen] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro x hx
    have hb1 : bump x = 1 := bump.one_of_mem_closedBall hx
    show bump x • F x = F x
    rw [hb1, one_smul]

end Riemannian
