import MorganTianLib.Ch05.Packing
import Mathlib.Topology.MetricSpace.Infsep

/-!
# Morgan--Tian Chapter 5: finite nets from packing bounds

This module isolates the finite based-net consequence of the packing
construction.  It does not choose a limit, a common ambient, or any
compatibility data between radii; those remain separate pointed-GH assembly
obligations.
-/

open Set Metric

namespace MorganTianLib

universe u

/-- **Math.** A uniform packing bound on a based metric space produces a finite
based `delta`-net in every nonnegative closed ball.  The cardinal bound is
allowed one extra point for the distinguished base point, since the finite
cover returned by the packing argument need not contain it. -/
theorem exists_finite_isDeltaNet_closedBall_of_uniform_packing_bound
    {X : Type u} [MetricSpace X] (x : X) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ)
    (hpack : ∀ (δ' S : ℝ), 0 < δ' → ∃ N : ℕ,
      ∀ n, n ∈ packingAdmissible x δ' S → n ≤ N) :
    ∃ N : ℕ, ∃ L : Set (Metric.closedBall x R),
      L.Finite ∧ L.ncard ≤ N ∧
        IsDeltaNet δ
          (⟨x, Metric.mem_closedBall_self hR⟩ : Metric.closedBall x R) L := by
  obtain ⟨N, hN⟩ := hpack (δ / 2) (R + 1 + δ / 2) (by linarith)
  obtain ⟨L₀, hL₀fin, hL₀card, hL₀cover⟩ :=
    exists_finite_closedBall_cover_of_uniform_packing_bound_with_card
      x (R := R) (η := δ) hR hδ hN
  let xb : Metric.closedBall x R :=
    ⟨x, Metric.mem_closedBall_self hR⟩
  let L : Set (Metric.closedBall x R) := insert xb L₀
  have hLfin : L.Finite := by
    dsimp [L]
    exact hL₀fin.insert xb
  have hbase : xb ∈ L := by
    exact mem_insert xb L₀
  have hcover : ∀ y : Metric.closedBall x R, ∃ z ∈ L, dist y z < δ := by
    intro y
    have hy : y ∈ ⋃ z ∈ L₀, Metric.ball z δ :=
      hL₀cover (Set.mem_univ y)
    rcases Set.mem_iUnion₂.mp hy with ⟨z, hz, hyz⟩
    exact ⟨z, mem_insert_of_mem _ hz, hyz⟩
  have hcard : L.ncard ≤ N + 1 := by
    dsimp [L]
    exact (Set.ncard_insert_le xb L₀).trans
      (Nat.add_le_add_right hL₀card 1)
  letI : Fintype L := hLfin.fintype
  have hsep : ∃ ε > 0, ∀ ⦃u v : Metric.closedBall x R⦄,
      u ∈ L → v ∈ L → u ≠ v → ε ≤ dist u v := by
    by_cases hnontrivial : L.Nontrivial
    · obtain ⟨ε, hε, hsep⟩ :=
        Set.relatively_discrete_of_finite (s := L)
      obtain ⟨u, hu, v, hv, huv⟩ := hnontrivial
      have hεtop : ε ≠ ⊤ := by
        intro htop
        have hle : (⊤ : ENNReal) ≤ edist u v := by
          simpa only [htop] using hsep u hu v hv huv
        exact edist_ne_top u v (top_unique hle)
      have hεreal : 0 < ε.toReal :=
        ENNReal.toReal_pos hε.ne' hεtop
      refine ⟨ε.toReal, hεreal, ?_⟩
      intro u v hu hv huv
      have hle := hsep u hu v hv huv
      have hreal := ENNReal.toReal_mono (edist_ne_top u v) hle
      simpa [edist_dist] using hreal
    · have hsubsingleton : L.Subsingleton :=
        Set.not_nontrivial_iff.mp hnontrivial
      refine ⟨1, zero_lt_one, ?_⟩
      intro u v hu hv huv
      exact (huv (hsubsingleton hu hv)).elim
  refine ⟨N + 1, L, hLfin, hcard, ?_⟩
  exact ⟨hbase, hcover, hsep⟩

end MorganTianLib

#print axioms MorganTianLib.exists_finite_isDeltaNet_closedBall_of_uniform_packing_bound
