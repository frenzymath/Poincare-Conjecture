import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Widening a single-chart time window

`thm:dc-ch8-2-1` (E. Cartan) is assembled in
`Jacobi/CartanExpNormTransferGeneral.lean` against an **outer** window `[a', b']` with
`a' < 0 < 1 < b'`: the variable-curvature Jacobi transfer needs its parallel frames to carry a
two-sided chart flatness certificate around the closed unit interval, so the hypothesis
"the geodesic stays in the source of a single chart" has to be available on `[a', b']`, not
just on `[0, 1]`.

This file supplies the purely topological half of that gap: a single-chart hypothesis on the
**compact** `[0, 1]` automatically widens to a slightly larger window, because the chart source
is open and the preimage of an open set under a continuous curve is open, so a compact subset of
it is thickenable inside it.

## Contents

* `exists_window_of_mem_chartAt_source` — the widening.

The statement is deliberately generic in the curve `γ` (only `Continuous γ` is used) and in the
manifold: `Jacobi/CartanExpNormTransferGeneral.lean` carries **two** hypotheses of this shape,
`hsrc` and `hsrcbar`, over different manifolds (`M`/`I`/`H` and `M'`/`I'`/`H'`), and one generic
declaration discharges both.  Nothing about geodesics, metrics, completeness or finite
dimensionality is used, and none is assumed.

Blueprint: infrastructure for `thm:dc-ch8-2-1`.
-/

open Set

namespace Riemannian.Jacobi

variable {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Math.** If a continuous curve `γ` stays in the source of the single chart `chartAt H α`
over the compact `[0, 1]`, then it still does over a strictly larger window `[a', b']` with
`a' < 0 < 1 < b'`.

The chart source is open and `γ` is continuous, so `O := γ ⁻¹' (chartAt H α).source` is an open
set containing the compact `[0, 1]`; hence some thickening `Metric.thickening δ (Icc 0 1)` still
fits inside `O`, and `[-(δ/2), 1 + δ/2]` lies in that thickening (project each `t` to the nearest
of `0`, `t`, `1`).

**This lemma only widens an existing hypothesis; it does not produce the chart.**  That such an
`α` exists at all — that the geodesic of `thm:dc-ch8-2-1` can be covered by a *single* chart — is
a genuinely open obligation, tracked at the blueprint node `lem:dc-ch8-2-1-single-chart`, and
nothing here bears on it: `α` and the `[0, 1]` hypothesis are both inputs. -/
theorem exists_window_of_mem_chartAt_source {γ : ℝ → M} (hγ : Continuous γ) (α : M)
    (hsrc : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ (chartAt H α).source) :
    ∃ a' b' : ℝ, a' < 0 ∧ (1 : ℝ) < b' ∧ ∀ t ∈ Set.Icc a' b', γ t ∈ (chartAt H α).source := by
  -- The curve's chart-source preimage is open, and contains the compact `[0, 1]`.
  have hOopen : IsOpen (γ ⁻¹' (chartAt H α).source) := (chartAt H α).open_source.preimage hγ
  have hIccO : Set.Icc (0 : ℝ) 1 ⊆ γ ⁻¹' (chartAt H α).source := hsrc
  obtain ⟨δ, hδ, hsub⟩ := isCompact_Icc.exists_thickening_subset_open hOopen hIccO
  refine ⟨-(δ / 2), 1 + δ / 2, by linarith, by linarith, fun t ht => ?_⟩
  obtain ⟨htl, htr⟩ := ht
  -- It suffices to place `t` in the `δ`-thickening of `[0, 1]`, via a nearest-point witness.
  refine hsub (Metric.mem_thickening_iff.mpr ?_)
  rcases le_total t 0 with h0 | h0
  · -- `t` sits to the left of `[0, 1]`: the witness is `0`, at distance `-t ≤ δ/2 < δ`.
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [Real.dist_eq, abs_of_nonpos (by linarith : t - 0 ≤ 0)]
    linarith
  · rcases le_total t 1 with h1 | h1
    · -- `t ∈ [0, 1]`: it is its own witness.
      exact ⟨t, ⟨h0, h1⟩, by simpa using hδ⟩
    · -- `t` sits to the right of `[0, 1]`: the witness is `1`, at distance `t - 1 ≤ δ/2 < δ`.
      refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      rw [Real.dist_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - 1)]
      linarith

end Riemannian.Jacobi
