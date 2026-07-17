/-
Copyright (c) 2026 Archon Horizon. All rights reserved.
Released under Apache 2.0 license.
-/
import PoincareLib.Ch01.GlobalExp
import PoincareLib.Ch01.ChartVariation
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Poincaré Ch. 1 — three prerequisites for the second-variation assembly

Three small, independent lemmas needed to assemble the second variation of energy along a
broken chart variation of a minimizing geodesic (blueprint node
`prop:minimal-geodesic-no-conjugate`, half 2).

* `globalGeodesic_zero_velocity` — the geodesic with zero initial velocity is the constant
  curve. This is the `globalGeodesic` analogue of `expMapGlobal_zero`
  (`Ch01/GlobalExp.lean`), obtained the same way but read off through the uniqueness lemma
  `globalGeodesic_eq` instead of through `expMapGlobal_eq_of_isGeodesic`.

* `exists_forall_mem_of_isCompact_of_continuous` — the tube lemma of `Ch01/ChartVariation.lean`
  (`exists_forall_mem_of_isOpen_of_continuous`), generalized from the hard-coded interval
  `Icc τ₀ τ₁` and the hard-coded map `chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁` to an arbitrary compact
  time-set `K` and an arbitrary continuous two-parameter map `u`. The assembly needs this more
  general form for the *enlarged* interval supplied by the partition's slack, on which the
  concrete `chartVariation` map is no longer literally the one in play.

* `exists_Icc_enlarged_subset` — an open set containing a compact interval `[c, d]` contains a
  slightly thickened interval `[c - ρ, d + ρ]`. Proved via Mathlib's thickening lemma
  `IsCompact.exists_thickening_subset_open` together with the elementary observation that every
  point of `[c - ρ, d + ρ]` is within `ρ` of its clamp `max c (min d x) ∈ [c, d]`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4, and the second-variation
assembly of `prop:minimal-geodesic-no-conjugate`.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

section

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **A geodesic with zero initial velocity is constant.** The global geodesic
`globalGeodesic g hg p 0` is the constant curve at `p`: the constant curve `fun _ => p` is
itself a geodesic (`isGeodesic_const`) with the right initial data, so by the uniqueness of the
global geodesic (`globalGeodesic_eq`) it *is* `globalGeodesic g hg p 0`. -/
theorem globalGeodesic_zero_velocity (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) :
    globalGeodesic (I := I) g hg p (0 : TangentSpace I p) = fun _ => p := by
  have hconst : IsGeodesic (I := I) g (fun _ : ℝ => p) := isGeodesic_const (I := I) g p
  have hcont : Continuous (fun _ : ℝ => p) := continuous_const
  have hv : HasDerivAt (fun t : ℝ => extChartAt I p ((fun _ : ℝ => p) t))
      ((0 : TangentSpace I p) : E) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (extChartAt I p p))
  exact (globalGeodesic_eq g hg hconst hcont rfl hv).symm

end

section

/-- **Math.** **Tube lemma over an arbitrary compact time set.** If a continuous two-parameter
map `u : ℝ × ℝ → E` sends `t ↦ u (0, t)` into an open set `U` for every `t` in a compact set
`K`, then it sends `t ↦ u (s, t)` into `U` for every `t ∈ K`, for all sufficiently small
variation parameters `s`. This is `exists_forall_mem_of_isOpen_of_continuous`
(`Ch01/ChartVariation.lean`) with `Icc τ₀ τ₁` generalized to an arbitrary compact `K` and
`chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁` generalized to an arbitrary continuous `u`; the proof is
verbatim the same, via `IsCompact.eventually_forall_of_forall_eventually` and
`Metric.eventually_nhds_iff`. -/
theorem exists_forall_mem_of_isCompact_of_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : ℝ × ℝ → E} {U : Set E} {K : Set ℝ}
    (hK : IsCompact K) (hU : IsOpen U) (hcont : Continuous u)
    (hmem : ∀ t ∈ K, u (0, t) ∈ U) :
    ∃ ε > 0, ∀ s ∈ Set.Ioo (-ε) ε, ∀ t ∈ K, u (s, t) ∈ U := by
  have key : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), ∀ t ∈ K, u (s, t) ∈ U := by
    refine hK.eventually_forall_of_forall_eventually (fun t ht => ?_)
    have hpre : u ⁻¹' U ∈ 𝓝 ((0 : ℝ), t) := (hU.preimage hcont).mem_nhds (hmem t ht)
    filter_upwards [hpre] with z hz using hz
  rw [Metric.eventually_nhds_iff] at key
  obtain ⟨ε, hε, hkey⟩ := key
  refine ⟨ε, hε, fun s hs t ht => ?_⟩
  refine hkey ?_ t ht
  rw [Real.dist_eq, sub_zero, abs_lt]
  exact ⟨hs.1, hs.2⟩

/-- **Math.** **An open set containing a closed interval contains a thickened one.** If
`[c, d] ⊆ V` with `V` open, then `[c - ρ, d + ρ] ⊆ V` for some `ρ > 0`. Proved by taking `ρ`
half of a Mathlib thickening radius (`IsCompact.exists_thickening_subset_open`) for
`[c, d] ⊆ V`, and observing that every `x ∈ [c - ρ, d + ρ]` is within `ρ` of its clamp
`max c (min d x) ∈ [c, d]`. -/
theorem exists_Icc_enlarged_subset {V : Set ℝ} {c d : ℝ} (hV : IsOpen V) (hcd : c ≤ d)
    (hsub : Set.Icc c d ⊆ V) :
    ∃ ρ > 0, Set.Icc (c - ρ) (d + ρ) ⊆ V := by
  have hK : IsCompact (Set.Icc c d) := isCompact_Icc
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hV hsub
  refine ⟨δ / 2, by linarith, fun x hx => hthick ?_⟩
  obtain ⟨hx1, hx2⟩ := hx
  rw [Metric.mem_thickening_iff]
  refine ⟨max c (min d x), ⟨le_max_left _ _, max_le hcd (min_le_left _ _)⟩, ?_⟩
  rcases lt_or_ge x c with hxc | hxc
  · have hmin : min d x = x := min_eq_right (hxc.le.trans hcd)
    have hmax : max c x = c := max_eq_left hxc.le
    rw [hmin, hmax, Real.dist_eq, abs_of_neg (by linarith : x - c < 0)]
    linarith
  · rcases le_or_gt x d with hxd | hxd
    · have hmin : min d x = x := min_eq_right hxd
      have hmax : max c x = x := max_eq_right hxc
      rw [hmin, hmax, dist_self]
      linarith
    · have hmin : min d x = d := min_eq_left hxd.le
      have hmax : max c d = d := max_eq_right hcd
      rw [hmin, hmax, Real.dist_eq, abs_of_pos (by linarith : x - d > 0)]
      linarith

end

end PoincareLib

end

#print axioms PoincareLib.globalGeodesic_zero_velocity
#print axioms PoincareLib.exists_forall_mem_of_isCompact_of_continuous
#print axioms PoincareLib.exists_Icc_enlarged_subset
