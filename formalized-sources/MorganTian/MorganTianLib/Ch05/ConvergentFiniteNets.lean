import MorganTianLib.Ch05.FinitePackingNets
import MorganTianLib.Ch05.Precompactness

/-!
# Morgan--Tian Chapter 5: finite nets along compact pointed limits

Pointed Gromov--Hausdorff convergence to a compact target gives an eventual
packing bound at every fixed scale.  This file turns that bound into explicit
finite based nets in the varying closed balls, with a cardinality independent
of the index.  No total-boundedness or compactness of the varying spaces is
assumed.
-/

open Set Filter Metric Topology

noncomputable section

namespace MorganTianLib

universe u

/-! ## A single-scale packing-to-net bridge -/

/-- **Math.** A packing bound at the scale and buffer needed by the maximal-net
construction produces a finite based net in a closed ball.  The extra point is
the distinguished basepoint, which need not occur in the finite cover returned
by the packing argument. -/
theorem exists_finite_isDeltaNet_closedBall_of_packing_bound
    {X : Type u} [MetricSpace X] (x : X) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) {N : ℕ}
    (hpack : ∀ n,
      n ∈ packingAdmissible x (δ / 2) (R + 1 + δ / 2) → n ≤ N) :
    ∃ L : Set (Metric.closedBall x R),
      L.Finite ∧ L.ncard ≤ N + 1 ∧
        IsDeltaNet δ
          (⟨x, Metric.mem_closedBall_self hR⟩ : Metric.closedBall x R) L := by
  obtain ⟨L₀, hL₀fin, hL₀card, hL₀cover⟩ :=
    exists_finite_closedBall_cover_of_uniform_packing_bound_with_card
      x hR hδ hpack
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
    · obtain ⟨ε, hε, hsep⟩ := Set.relatively_discrete_of_finite (s := L)
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
  refine ⟨L, hLfin, hcard, ?_⟩
  exact ⟨hbase, hcover, hsep⟩

/-! ## Eventual nets from pointed GH convergence -/

/-- **Math.** A sequence converging in pointed Gromov--Hausdorff distance to a
compact target admits, eventually, finite based δ-nets in every fixed closed
ball, with one cardinal bound independent of the sequence index. -/
theorem eventually_exists_finite_isDeltaNet_closedBall_of_pointedGHConverges_compact_target
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}} [CompactSpace Y.carrier]
    (hconv : PointedGHConverges X Y) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ᶠ k in atTop,
      ∃ L : Set (Metric.closedBall (X k).base R),
        L.Finite ∧ L.ncard ≤ N + 1 ∧
          IsDeltaNet δ
            (⟨(X k).base, Metric.mem_closedBall_self hR⟩ :
              Metric.closedBall (X k).base R) L := by
  obtain ⟨N, hN⟩ :=
    eventually_uniform_packing_bound_of_pointedGHConverges_compact_target
      hconv (δ := δ / 2) (R₀ := R + 1 + δ / 2)
      (by linarith) (by linarith)
  refine ⟨N, ?_⟩
  filter_upwards [hN] with k hk
  obtain ⟨L, hLfin, hLcard, hLnet⟩ :=
    exists_finite_isDeltaNet_closedBall_of_packing_bound
      (X k).base hR hδ hk
  exact ⟨L, hLfin, hLcard, hLnet⟩

end MorganTianLib

end

#print axioms MorganTianLib.exists_finite_isDeltaNet_closedBall_of_packing_bound
#print axioms MorganTianLib.eventually_exists_finite_isDeltaNet_closedBall_of_pointedGHConverges_compact_target
