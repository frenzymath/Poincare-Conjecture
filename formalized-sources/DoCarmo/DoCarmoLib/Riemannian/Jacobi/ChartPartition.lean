import Mathlib.Topology.UnitInterval
import DoCarmoLib.Riemannian.Jacobi.JacobiManifold

/-!
# Poincaré Ch. 1, §1.4 — chart partition of a compact geodesic

The differential of the exponential map (`cor:dc-ch5-2-5`) is computed by
chaining one-chart geodesic-flow steps along the compact geodesic
`γ = γ_v : [0,1] → M`. The image `γ([0,1])` is compact, so it is covered by
finitely many chart sources, and `[0,1]` can be partitioned so that each piece
maps into a single chart. This file provides that partition, which the
flow-derivative gluing (`FlowStep`/`StateTransition`/`FlowGluing`) consumes:
each junction between consecutive pieces re-reads the flow state across a chart
change, each piece transports the variational pair inside its chart
(`IsJacobiFieldOn.variational_transport`).

* `exists_geodesic_chart_partition` — for a curve `γ` continuous on `[0,1]`,
  there is a monotone partition `0 = τ 0 ≤ τ 1 ≤ ⋯`, eventually constant at
  `1`, and charts `β : ℕ → M` such that `γ([τ i, τ (i+1)])` lies in the source
  of the chart at `β i` for every `i`.

The combinatorial engine is mathlib's
`exists_monotone_Icc_subset_open_cover_unitInterval`, applied to the open cover
of `unitInterval = [0,1]` by the preimages of the chart sources; the finite
subcover / Lebesgue-number content is discharged there.

Blueprint: `cor:dc-ch5-2-5`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set
open scoped Manifold Topology

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Math.** **Chart partition of a compact curve.** For a curve `γ` continuous
on `[0,1]`, there are a monotone real partition `τ : ℕ → ℝ` with `τ 0 = 0`,
eventually equal to `1`, taking values in `[0,1]`, and a choice of charts
`β : ℕ → M`, such that on every piece `[τ i, τ (i+1)]` the curve maps into the
source of the chart at `β i`.

The compactness is discharged by mathlib's
`exists_monotone_Icc_subset_open_cover_unitInterval` (Lebesgue number of the
open cover of `[0,1]` by preimages of chart sources). This is the finite chart
partition consumed by the flow-derivative gluing of `cor:dc-ch5-2-5`. -/
theorem exists_geodesic_chart_partition {γ : ℝ → M}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    ∃ (τ : ℕ → ℝ) (β : ℕ → M) (n : ℕ),
      τ 0 = 0 ∧ (∀ m ≥ n, τ m = 1) ∧ Monotone τ ∧
      (∀ i, τ i ∈ Icc (0 : ℝ) 1) ∧
      (∀ i, ∀ t ∈ Icc (τ i) (τ (i + 1)), γ t ∈ (chartAt H (β i)).source) := by
  classical
  -- the curve read on the unit interval subtype is continuous
  have hcont : Continuous fun s : unitInterval => γ (s : ℝ) := by
    rw [continuousOn_iff_continuous_restrict] at hγ
    exact hγ
  -- the open cover of `[0,1]` by preimages of chart sources, indexed by `M`
  set c : M → Set unitInterval := fun b =>
    (fun s : unitInterval => γ (s : ℝ)) ⁻¹' (chartAt H b).source with hc
  have hcopen : ∀ b, IsOpen (c b) := fun b =>
    (chartAt H b).open_source.preimage hcont
  have hccover : (univ : Set unitInterval) ⊆ ⋃ b, c b := by
    intro s _
    exact mem_iUnion.2 ⟨γ (s : ℝ), mem_chart_source H (γ (s : ℝ))⟩
  obtain ⟨t, ht0, htmono, ⟨n, htn⟩, htsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcopen hccover
  -- choose a chart index for each piece
  choose β hβ using htsub
  refine ⟨fun i => (t i : ℝ), β, n, ?_, ?_, ?_, ?_, ?_⟩
  · show (t 0 : ℝ) = 0; rw [ht0]; simp
  · intro m hm; show (t m : ℝ) = 1; rw [htn m hm]; simp
  · intro i j hij
    exact_mod_cast htmono hij
  · intro i; exact (t i).2
  · intro i s hs
    -- `s ∈ [τ i, τ (i+1)] ⊆ [0,1]`, so `s : unitInterval` lies in the piece
    have hs01 : s ∈ Icc (0 : ℝ) 1 :=
      ⟨le_trans (t i).2.1 hs.1, le_trans hs.2 (t (i + 1)).2.2⟩
    have hmem : (⟨s, hs01⟩ : unitInterval) ∈ Icc (t i) (t (i + 1)) := by
      constructor <;> [exact hs.1; exact hs.2]
    exact hβ i hmem

end Riemannian.Jacobi

end
