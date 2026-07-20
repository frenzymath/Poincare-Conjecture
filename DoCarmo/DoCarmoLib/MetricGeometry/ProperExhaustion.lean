import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Shared.Util.Attributes
/-!
# Properness via divergent compact exhaustions

do Carmo, *Riemannian Geometry*, Ch. 7, Theorem 2.8, b) ↔ e): a metric space
has the Heine–Borel property (closed bounded sets are compact, i.e. it is a
*proper* space) iff it admits a monotone exhaustion by compact sets `K n` such
that every sequence escaping all the `K n` diverges in distance from a fixed
base point. This is the purely metric-topological part of the Hopf–Rinow
circle of equivalences; no manifold structure is involved.
-/

open Metric Set Filter

namespace OpenGA

variable {α : Type*} [PseudoMetricSpace α]

/-- **Math.** do Carmo Ch. 7, Theorem 2.8, b) ↔ e). A pseudometric space is
**proper** (closed balls — equivalently closed bounded sets — are compact) iff
there is a monotone exhaustion `K 0 ⊆ K 1 ⊆ ⋯`, `⋃ n, K n = univ`, by compact
sets such that any sequence `q` with `q n ∉ K n` satisfies
`dist p (q n) → ∞`, for a fixed base point `p`. -/
theorem properSpace_iff_exists_compact_exhaustion (p : α) :
    ProperSpace α ↔
      ∃ K : ℕ → Set α, (∀ n, IsCompact (K n)) ∧ Monotone K ∧ (⋃ n, K n) = univ ∧
        ∀ q : ℕ → α, (∀ n, q n ∉ K n) →
          Tendsto (fun n ↦ dist p (q n)) atTop atTop := by
  constructor
  · intro hprop
    refine ⟨fun n ↦ closedBall p n, fun n ↦ isCompact_closedBall p n,
      fun m n hmn ↦ closedBall_subset_closedBall (by exact_mod_cast hmn), ?_, ?_⟩
    · rw [eq_univ_iff_forall]
      intro x
      obtain ⟨n, hn⟩ := exists_nat_ge (dist x p)
      exact mem_iUnion.mpr ⟨n, mem_closedBall.mpr hn⟩
    · intro q hq
      refine tendsto_atTop_mono (fun n ↦ ?_) tendsto_natCast_atTop_atTop
      have hn : ¬ dist (q n) p ≤ n := fun h ↦ hq n (mem_closedBall.mpr h)
      rw [dist_comm]
      exact (not_le.mp hn).le
  · rintro ⟨K, hKcomp, -, hKuniv, hKesc⟩
    -- every closed ball around the base point is contained in some `K n`
    have key : ∀ r : ℝ, ∃ n, closedBall p r ⊆ K n := by
      intro r
      by_contra hcon
      push Not at hcon
      choose q hq hq' using fun n ↦ Set.not_subset.mp (hcon n)
      obtain ⟨n, hn⟩ := ((hKesc q hq').eventually_gt_atTop r).exists
      exact absurd (mem_closedBall.mp (hq n)) (by rw [dist_comm]; exact not_le.mpr hn)
    refine ⟨fun x r ↦ ?_⟩
    obtain ⟨n, hn⟩ := key (dist p x + r)
    refine (hKcomp n).of_isClosed_subset isClosed_closedBall (fun z hz ↦ hn ?_)
    rw [mem_closedBall] at hz ⊢
    calc dist z p ≤ dist z x + dist x p := dist_triangle z x p
      _ ≤ r + dist x p := by linarith
      _ = dist p x + r := by rw [dist_comm]; ring

end OpenGA
