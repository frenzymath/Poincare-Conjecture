import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UnitInterval
import DoCarmoLib.Riemannian.Exponential.CInftyGlobal

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
open scoped ContDiff Manifold Topology

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

/-! ### A common finite chart partition for a pair of curves -/

variable {H' : Type*} [TopologicalSpace H']
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- **Math.** **Synchronized chart partition.** If two curves are continuous on `[0,1]`,
there is one monotone, eventually stationary partition of the parameter interval such that
each piece is contained in one chart source for the first curve and in one chart source for the
second curve.  The construction uses the open cover by *intersections* of the two pullbacks of
chart sources, so the two chart chains have common junction times.

This is the topological input needed before applying a one-chart Jacobi transfer piecewise.  It
does not assert that either whole curve lies in a single chart, and it does not by itself perform
the ODE-data matching at a junction. -/
theorem exists_pair_curve_chart_partition {γ : ℝ → M} {γ' : ℝ → M'}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγ' : ContinuousOn γ' (Icc (0 : ℝ) 1)) :
    ∃ (τ : ℕ → ℝ) (β : ℕ → M) (β' : ℕ → M') (n : ℕ),
      τ 0 = 0 ∧ (∀ m ≥ n, τ m = 1) ∧ Monotone τ ∧
      (∀ i, τ i ∈ Icc (0 : ℝ) 1) ∧
      (∀ i, ∀ t ∈ Icc (τ i) (τ (i + 1)),
        γ t ∈ (chartAt H (β i)).source ∧ γ' t ∈ (chartAt H' (β' i)).source) := by
  classical
  have hcont : Continuous fun s : unitInterval => γ (s : ℝ) := by
    rw [continuousOn_iff_continuous_restrict] at hγ
    exact hγ
  have hcont' : Continuous fun s : unitInterval => γ' (s : ℝ) := by
    rw [continuousOn_iff_continuous_restrict] at hγ'
    exact hγ'
  -- Intersect the two pullback covers so a single partition works on both sides.
  set c : M × M' → Set unitInterval := fun b =>
    (fun s : unitInterval => γ (s : ℝ)) ⁻¹' (chartAt H b.1).source ∩
      (fun s : unitInterval => γ' (s : ℝ)) ⁻¹' (chartAt H' b.2).source with hc
  have hcopen : ∀ b, IsOpen (c b) := by
    intro b
    exact (chartAt H b.1).open_source.preimage hcont |>.inter
      ((chartAt H' b.2).open_source.preimage hcont')
  have hccover : (univ : Set unitInterval) ⊆ ⋃ b, c b := by
    intro s _
    refine mem_iUnion.2 ⟨(γ (s : ℝ), γ' (s : ℝ)), ?_⟩
    exact ⟨mem_chart_source H (γ (s : ℝ)), mem_chart_source H' (γ' (s : ℝ))⟩
  obtain ⟨t, ht0, htmono, ⟨n, htn⟩, htsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcopen hccover
  choose b hβ using htsub
  refine ⟨(fun i => (t i : ℝ)), (fun i => (b i).1), (fun i => (b i).2), n, ?_, ?_, ?_, ?_, ?_⟩
  · show (t 0 : ℝ) = 0
    rw [ht0]
    simp
  · intro m hm
    show (t m : ℝ) = 1
    rw [htn m hm]
    simp
  · intro i j hij
    exact_mod_cast htmono hij
  · intro i
    exact (t i).2
  · intro i s hs
    have hs01 : s ∈ Icc (0 : ℝ) 1 :=
      ⟨le_trans (t i).2.1 hs.1, le_trans hs.2 (t (i + 1)).2.2⟩
    have hmem : (⟨s, hs01⟩ : unitInterval) ∈ Icc (t i) (t (i + 1)) :=
      ⟨hs.1, hs.2⟩
    have hpair := hβ i hmem
    exact hpair

end Riemannian.Jacobi

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M]

/-! ### A uniform single chart for short radial geodesics -/

/-- **Math.** **Uniform radial chart neighborhood.** On a complete Riemannian manifold, there is
an open neighborhood `W` of `0` in `T_pM` such that every radial geodesic `γ_w`, for `w ∈ W`,
stays in the source of the single chart `chartAt H p` throughout `[0,1]`.

This is the valid local form of the single-chart input in E. Cartan's theorem. It is uniform in
`w`, unlike `exists_window_of_mem_chartAt_source`, and follows by choosing a small ball whose
image under `exp_p` lies in the chart source. Radial homogeneity
`exp_p(t • w) = γ_w(t)` then keeps the whole segment in that ball. -/
theorem exists_radial_chart_neighborhood
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) :
    ∃ W : Set E, IsOpen W ∧ (0 : E) ∈ W ∧
      ∀ w ∈ W, ∀ t ∈ Icc (0 : ℝ) 1,
        globalGeodesic (I := I) g hg p w t ∈ (chartAt H p).source := by
  let F : E → M := fun w => expMapGlobal (I := I) g hg p w
  have hFcont : Continuous F := (contMDiff_expMapGlobal g hg p).continuous
  have hopen : IsOpen (F ⁻¹' (chartAt H p).source) :=
    (chartAt H p).open_source.preimage hFcont
  have hzero : (0 : E) ∈ F ⁻¹' (chartAt H p).source := by
    change expMapGlobal (I := I) g hg p (0 : TangentSpace I p) ∈ (chartAt H p).source
    rw [expMapGlobal_zero]
    exact mem_chart_source H p
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hopen) 0 hzero
  refine ⟨Metric.ball 0 ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
  intro w hw t ht
  rw [← expMapGlobal_smul (I := I) g hg p w t]
  apply hball
  rw [Metric.mem_ball, dist_zero_right] at hw ⊢
  calc
    ‖t • w‖ = |t| * ‖w‖ := norm_smul t w
    _ = t * ‖w‖ := by rw [abs_of_nonneg ht.1]
    _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg w)
    _ < ε := by simpa using hw

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [SigmaCompactSpace M']

/-- **Math.** **A common uniform radial chart neighborhood.** For two complete manifolds and a
continuous linear equivalence `i : T_pM → T_p'M'`, one open neighborhood of `0` works
simultaneously for `γ_w` in `M` and `γ_{i(w)}` in `M'`. The source uses `chartAt H p`, the
target uses `chartAt H' p'`.

The common neighborhood is the intersection of the source neighborhood with the pullback under
`i` of the target neighborhood. This is the uniform pair of single-chart hypotheses consumed by
the variable-curvature Cartan transfer. -/
theorem exists_pair_radial_chart_neighborhood
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    (p : M) (p' : M') (i : E ≃L[ℝ] E) :
    ∃ W : Set E, IsOpen W ∧ (0 : E) ∈ W ∧
      ∀ w ∈ W, ∀ t ∈ Icc (0 : ℝ) 1,
        globalGeodesic (I := I) g hg p w t ∈ (chartAt H p).source ∧
        globalGeodesic (I := I') g' hg' p' (i w) t ∈ (chartAt H' p').source := by
  obtain ⟨W, hWopen, hW0, hW⟩ := exists_radial_chart_neighborhood (I := I) g hg p
  obtain ⟨W', hW'open, hW'0, hW'⟩ := exists_radial_chart_neighborhood (I := I') g' hg' p'
  refine ⟨W ∩ (fun w : E => i w) ⁻¹' W', hWopen.inter (hW'open.preimage i.continuous),
    ⟨hW0, ?_⟩, ?_⟩
  · simpa using hW'0
  · rintro w ⟨hw, hw'⟩ t ht
    exact ⟨hW w hw t ht, hW' (i w) hw' t ht⟩

end Riemannian.Jacobi
