import MorganTianLib.Ch05.Precompactness
import MorganTianLib.Ch05.StageMetricBridge
import MorganTianLib.Ch05.FinitePackingNets
import MorganTianLib.Ch05.RadialAmbientBridge

/-!
# Morgan--Tian Chapter 5: packing across a compatible compact assembly

Radial coverage lets a finite configuration in the completed common ambient be
represented in one compact stage.  This file makes the corresponding packing
transfer explicit: a finite packing in the completed ambient pulls back to a
packing in that stage, so uniform stage packing bounds become an ambient bound.
The final net statement then feeds this bound into the existing finite-net
producer.
-/

open Set Filter Metric

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-! ## Radius-uniform tail interfaces -/

/-- **Math.** A nonpositive-radius packing can only have zero centres.  This
elementary empty-ball case extends the compact-target packing estimate from
nonnegative radii to the all-real-radius interface used by the net producer. -/
theorem packing_bound_of_nonpositive_radius
    {X : Type*} [MetricSpace X] (x : X) {δ R : ℝ} (hR : R ≤ 0) :
    ∀ n, n ∈ packingAdmissible x δ R → n ≤ 0 := by
  intro n hn
  rcases hn with ⟨w⟩
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    let i : Fin n := ⟨0, hnpos⟩
    have hi : w.center i ∈ Metric.ball x R := w.center_mem i
    rw [Metric.ball_eq_empty.mpr hR] at hi
    exact False.elim hi

/-- **Math.** Pointed GH convergence to a compact target supplies an eventual
uniform packing bound at an arbitrary real radius.  For nonnegative radii this
is the compact-target precompactness theorem; for nonpositive radii the bound
is the empty-ball bound above. -/
theorem eventually_uniform_packing_bound_of_pointedGHConverges_compact_target_all_radii
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}} [CompactSpace Y.carrier]
    (hconv : PointedGHConverges X Y)
    {δ R : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ᶠ k in atTop,
      ∀ n, n ∈ packingAdmissible (X k).base δ R → n ≤ N := by
  by_cases hR : 0 ≤ R
  · exact eventually_uniform_packing_bound_of_pointedGHConverges_compact_target
      hconv hδ hR
  · refine ⟨0, Filter.Eventually.of_forall ?_⟩
    intro k n hn
    exact packing_bound_of_nonpositive_radius (X k).base
      (le_of_not_ge hR) n hn

/-- **Math.** Package the preceding fixed-radius adapter in the all-scale form
needed by eventual compact-stage assembly.  The cardinal bound may depend on
the chosen scale and radius, exactly as in the source precompactness estimate. -/
theorem eventually_uniform_packing_bounds_of_pointedGHConverges_compact_target
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}} [CompactSpace Y.carrier]
    (hconv : PointedGHConverges X Y) :
    ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ᶠ k in atTop,
      ∀ n, n ∈ packingAdmissible (X k).base δ R → n ≤ N := by
  intro δ R hδ
  exact eventually_uniform_packing_bound_of_pointedGHConverges_compact_target_all_radii
    hconv hδ

/-! ## Fixed-stage packing transfer -/

/-- **Math.** A specified compact stage containing the completed-limit ball can
pull a finite packing witness back along its isometric embedding.  Keeping the
stage index explicit is essential when the available packing and coverage
estimates hold only eventually along the exhaustion. -/
theorem exists_stage_packingWitness_of_completedLimit_packingWitness_at
    (S : CompatiblePointedCompactSystem.{u}) (k : ℕ)
    {δ R : ℝ} {n : ℕ}
    (hk : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding k))
    (w : PackingWitness S.completedLimit.base δ R n) :
    ∃ w' : PackingWitness (S.stage k).base δ R n,
      ∀ i, S.stageEmbedding k (w'.center i) = w.center i := by
  have hcenter_closed : ∀ i, w.center i ∈
      Metric.closedBall S.completedLimit.base R := by
    intro i
    exact Metric.mem_closedBall.mpr
      (le_of_lt (Metric.mem_ball.mp (w.center_mem i)))
  choose c hc using fun i => hk (hcenter_closed i)
  let c' : Fin n → (S.stage k).carrier := c
  have hc' (i : Fin n) : S.stageEmbedding k (c' i) = w.center i :=
    hc i
  have hcenter_mem : ∀ i, c' i ∈ Metric.ball (S.stage k).base R := by
    intro i
    rw [Metric.mem_ball]
    calc
      dist (c' i) (S.stage k).base =
          dist (S.stageEmbedding k (c' i)) S.completedLimit.base :=
        (S.dist_stageEmbedding_base k (c' i)).symm
      _ = dist (w.center i) S.completedLimit.base := by rw [hc' i]
      _ < R := Metric.mem_ball.mp (w.center_mem i)
  have hball_subset : ∀ i,
      Metric.ball (c' i) δ ⊆ Metric.ball (S.stage k).base R := by
    intro i z hz
    rw [Metric.mem_ball]
    have hz' : S.stageEmbedding k z ∈
        Metric.ball (S.stageEmbedding k (c' i)) δ := by
      rw [Metric.mem_ball]
      simpa [(S.stageEmbedding_isometry k).dist_eq] using
        (Metric.mem_ball.mp hz)
    have hbase' := w.ball_subset i (by simpa [hc' i] using hz')
    rw [Metric.mem_ball] at hbase'
    calc
      dist z (S.stage k).base =
          dist (S.stageEmbedding k z) S.completedLimit.base :=
        (S.dist_stageEmbedding_base k z).symm
      _ < R := hbase'
  have hdisjoint : Pairwise (fun i j =>
      Disjoint (Metric.ball (c' i) δ) (Metric.ball (c' j) δ)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hzi' : S.stageEmbedding k z ∈
        Metric.ball (w.center i) δ := by
      rw [Metric.mem_ball]
      rw [← hc' i]
      simpa [(S.stageEmbedding_isometry k).dist_eq] using
        (Metric.mem_ball.mp hzi)
    have hzj' : S.stageEmbedding k z ∈
        Metric.ball (w.center j) δ := by
      rw [Metric.mem_ball]
      rw [← hc' j]
      simpa [(S.stageEmbedding_isometry k).dist_eq] using
        (Metric.mem_ball.mp hzj)
    exact Set.disjoint_left.mp (w.pairwise_disjoint hij) hzi' hzj'
  exact ⟨⟨c', hcenter_mem, hball_subset, hdisjoint⟩, hc'⟩

/-- **Math.** Pull a finite packing witness in the completed common ambient back to a
single compact stage.  The stage is chosen by radial coverage, and the
stage-embedding metric bridge preserves the centre, containment, and
disjointness clauses exactly. -/
theorem exists_stage_packingWitness_of_completedLimit_packingWitness
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ k : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding k))
    {δ R : ℝ} {n : ℕ}
    (w : PackingWitness S.completedLimit.base δ R n) :
    ∃ k : ℕ, ∃ w' : PackingWitness (S.stage k).base δ R n,
      ∀ i, S.stageEmbedding k (w'.center i) = w.center i := by
  obtain ⟨k, hk⟩ := hcover R
  obtain ⟨w', hw'⟩ :=
    S.exists_stage_packingWitness_of_completedLimit_packingWitness_at k hk w
  exact ⟨k, w', hw'⟩

/-! ## Eventual packing transfer -/

/-- **Math.** Eventual cofinal coverage and eventual uniform packing bounds on
the compact stages transfer to a uniform packing bound in the completed common
ambient.  The proof synchronizes the two tails at one sufficiently late stage,
so no unjustified finite-prefix bound is introduced. -/
theorem exists_packing_bound_completedLimit_of_eventually_cofinal_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (hcover : ∀ᶠ k : ℕ in atTop,
      Metric.closedBall S.completedLimit.base (r k) ⊆
        Set.range (S.stageEmbedding k))
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ᶠ k : ℕ in atTop,
      ∀ n, n ∈ packingAdmissible (S.stage k).base δ R → n ≤ N) :
    ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ n,
      n ∈ packingAdmissible S.completedLimit.base δ R → n ≤ N := by
  intro δ R hδ
  obtain ⟨Npack, hNpack⟩ := hpack δ R hδ
  obtain ⟨Kpack, hNpackTail⟩ := eventually_atTop.1 hNpack
  obtain ⟨Ncov, hNcov⟩ := eventually_atTop.1 hcover
  have hevR : ∀ᶠ k : ℕ in atTop, R ≤ r k :=
    (Filter.tendsto_atTop.1 hr) R
  obtain ⟨Nr, hNr⟩ := eventually_atTop.1 hevR
  let k := max Kpack (max Ncov Nr)
  have hkpack : Kpack ≤ k := Nat.le_max_left _ _
  have hkcov : Ncov ≤ k :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hkr : Nr ≤ k :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hrad : R ≤ r k := hNr k hkr
  have hkcover : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding k) :=
    (Metric.closedBall_subset_closedBall hrad).trans (hNcov k hkcov)
  refine ⟨Npack, ?_⟩
  intro n hn
  rcases hn with ⟨w⟩
  obtain ⟨w', hw'⟩ :=
    S.exists_stage_packingWitness_of_completedLimit_packingWitness_at
      k hkcover w
  exact hNpackTail k hkpack n ⟨w'⟩

/-- **Math.** The coverage and packing tails may use a reindexed stage map.
If the selected stage index `m k` tends to infinity, one late radius index can
be chosen so that both the coverage statement and the stage packing estimate
hold at that selected stage.  This is the form suited to diagonal compact-ball
extractions whose limit stages are not numbered by the radius index itself. -/
theorem exists_packing_bound_completedLimit_of_eventually_cofinal_reindexed_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (r : ℕ → ℝ) (m : ℕ → ℕ)
    (hr : Tendsto r atTop atTop) (hm : Tendsto m atTop atTop)
    (hcover : ∀ᶠ k : ℕ in atTop,
      Metric.closedBall S.completedLimit.base (r k) ⊆
        Set.range (S.stageEmbedding (m k)))
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ᶠ j : ℕ in atTop,
      ∀ n, n ∈ packingAdmissible (S.stage j).base δ R → n ≤ N) :
    ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ n,
      n ∈ packingAdmissible S.completedLimit.base δ R → n ≤ N := by
  intro δ R hδ
  obtain ⟨Npack, hNpack⟩ := hpack δ R hδ
  obtain ⟨Kpack, hNpackTail⟩ := eventually_atTop.1 hNpack
  obtain ⟨Ncov, hNcov⟩ := eventually_atTop.1 hcover
  obtain ⟨Nr, hNr⟩ := eventually_atTop.1 ((Filter.tendsto_atTop.1 hr) R)
  obtain ⟨Nm, hNm⟩ :=
    eventually_atTop.1 ((Filter.tendsto_atTop.1 hm) Kpack)
  let k := max Ncov (max Nr Nm)
  have hkcov : Ncov ≤ k := Nat.le_max_left _ _
  have hkr : Nr ≤ k :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hkm : Nm ≤ k :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hrad : R ≤ r k := hNr k hkr
  have hkcover : Metric.closedBall S.completedLimit.base R ⊆
      Set.range (S.stageEmbedding (m k)) :=
    (Metric.closedBall_subset_closedBall hrad).trans (hNcov k hkcov)
  refine ⟨Npack, ?_⟩
  intro n hn
  rcases hn with ⟨w⟩
  obtain ⟨w', hw'⟩ :=
    S.exists_stage_packingWitness_of_completedLimit_packingWitness_at
      (m k) hkcover w
  exact hNpackTail (m k) (hNm k hkm) n ⟨w'⟩

/-- **Math.** The preceding eventual cofinal transfer specializes to natural
radii, the usual compact exhaustion indexing. -/
theorem exists_packing_bound_completedLimit_of_eventually_nat_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ᶠ k : ℕ in atTop,
      Metric.closedBall S.completedLimit.base (k : ℝ) ⊆
        Set.range (S.stageEmbedding k))
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ᶠ k : ℕ in atTop,
      ∀ n, n ∈ packingAdmissible (S.stage k).base δ R → n ≤ N) :
    ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ n,
      n ∈ packingAdmissible S.completedLimit.base δ R → n ≤ N := by
  simpa using
    (S.exists_packing_bound_completedLimit_of_eventually_cofinal_stage_coverage
      (r := fun k : ℕ => (k : ℝ)) tendsto_natCast_atTop_atTop hcover hpack)

/-- **Math.** Eventual cofinal coverage and eventual stage packing bounds also
produce finite based nets in each completed-limit closed ball.  This is the
finite-net interface consumed by the compact GH precompactness argument. -/
theorem exists_finite_isDeltaNet_completedLimit_closedBall_of_eventually_cofinal_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (hcover : ∀ᶠ k : ℕ in atTop,
      Metric.closedBall S.completedLimit.base (r k) ⊆
        Set.range (S.stageEmbedding k))
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ᶠ k : ℕ in atTop,
      ∀ n, n ∈ packingAdmissible (S.stage k).base δ R → n ≤ N)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∃ L : Set (Metric.closedBall S.completedLimit.base R),
      L.Finite ∧ L.ncard ≤ N ∧
        IsDeltaNet δ
          (⟨S.completedLimit.base,
            Metric.mem_closedBall_self hR⟩ :
            Metric.closedBall S.completedLimit.base R) L := by
  have hambient :=
    S.exists_packing_bound_completedLimit_of_eventually_cofinal_stage_coverage
      r hr hcover hpack
  exact exists_finite_isDeltaNet_closedBall_of_uniform_packing_bound
    S.completedLimit.base hR hδ hambient

/-- **Math.** If the compact stages converge in pointed GH distance to a compact
target, their eventual packing estimates combine with same-index cofinal
coverage to give a uniform packing bound in the completed ambient.  This is the
direct bridge from the compact-target precompactness producer to the common
ambient assembly; compact-limit compatibility and coverage remain hypotheses. -/
theorem exists_packing_bound_completedLimit_of_pointedGHConverges_compact_stage
    (S : CompatiblePointedCompactSystem.{u})
    {Y : FiniteDiameterBasedMetricSpace.{u}} [CompactSpace Y.carrier]
    (hconv : PointedGHConverges
      (fun k : ℕ =>
        (S.stage k).toFiniteDiameterBasedMetricSpace) Y)
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (hcover : ∀ᶠ k : ℕ in atTop,
      Metric.closedBall S.completedLimit.base (r k) ⊆
        Set.range (S.stageEmbedding k)) :
    ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ n,
      n ∈ packingAdmissible S.completedLimit.base δ R → n ≤ N := by
  intro δ R hδ
  have hpack : ∀ δ' R', 0 < δ' → ∃ N : ℕ, ∀ᶠ k : ℕ in atTop,
      ∀ n, n ∈ packingAdmissible (S.stage k).base δ' R' → n ≤ N := by
    intro δ' R' hδ'
    obtain ⟨N, hN⟩ :=
      eventually_uniform_packing_bounds_of_pointedGHConverges_compact_target
        hconv δ' R' hδ'
    refine ⟨N, ?_⟩
    filter_upwards [hN] with k hk
    intro n hn
    apply hk n
    exact hn
  exact
    (S.exists_packing_bound_completedLimit_of_eventually_cofinal_stage_coverage
      r hr hcover hpack) δ R hδ

/-- **Math.** Uniform packing bounds on all compact stages transfer to the completed
common ambient whenever the stage images satisfy radial closed-ball coverage.
This is the finite-configuration bridge needed before applying the ambient
packing-to-net and GH precompactness producers. -/
theorem exists_packing_bound_completedLimit_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ k : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding k))
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ k n,
      n ∈ packingAdmissible (S.stage k).base δ R → n ≤ N) :
    ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ n,
      n ∈ packingAdmissible S.completedLimit.base δ R → n ≤ N := by
  intro δ R hδ
  obtain ⟨N, hN⟩ := hpack δ R hδ
  refine ⟨N, ?_⟩
  intro n hn
  rcases hn with ⟨w⟩
  obtain ⟨k, w', hw'⟩ :=
    S.exists_stage_packingWitness_of_completedLimit_packingWitness
      hcover w
  exact hN k n ⟨w'⟩

/-- **Math.** A uniform stage-packing bound and radial coverage produce finite based
`delta`-nets in every completed-limit closed ball, with the same cardinal
control as the ambient packing bound. -/
theorem exists_finite_isDeltaNet_completedLimit_closedBall_of_stage_packing
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ k : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding k))
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ k n,
      n ∈ packingAdmissible (S.stage k).base δ R → n ≤ N)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∃ L : Set (Metric.closedBall S.completedLimit.base R),
      L.Finite ∧ L.ncard ≤ N ∧
        IsDeltaNet δ
          (⟨S.completedLimit.base,
            Metric.mem_closedBall_self hR⟩ :
            Metric.closedBall S.completedLimit.base R) L := by
  have hambient :=
    S.exists_packing_bound_completedLimit_of_radial_stage_coverage
      hcover hpack
  exact exists_finite_isDeltaNet_closedBall_of_uniform_packing_bound
    S.completedLimit.base hR hδ hambient

/-- **Math.** A commuting based ambient identification supplies the eventual
closed-ball coverage needed by the reindexed compact-stage packing transfer.
This exposes the direct consumer path while keeping the independent limit and
ambient-identification hypotheses explicit. -/
theorem exists_packing_bound_completedLimit_of_eventually_reindexed_ambient_isometry
    (S : CompatiblePointedCompactSystem.{u})
    (X : BasedMetricSpaceBundle.{u})
    (r : ℕ → ℝ) (m : ℕ → ℕ) (hr : ∀ n, 0 ≤ r n)
    (hrcofinal : Tendsto r atTop atTop) (hm : Tendsto m atTop atTop)
    (ambientEquiv : S.completedLimit.carrier ≃ᵢ X.carrier)
    (ambient_base : ambientEquiv S.completedLimit.base = X.base)
    (stageToBall : ∀ k,
      (S.stage (m k)).carrier ≃ᵢ (closedBallModel X (r k) (hr k)).carrier)
    (stageToBall_comm : ∀ᶠ k : ℕ in atTop,
      ∀ x : (S.stage (m k)).carrier,
        ambientEquiv (S.stageEmbedding (m k) x) = (stageToBall k x).1)
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ᶠ j : ℕ in atTop,
      ∀ n, n ∈ packingAdmissible (S.stage j).base δ R → n ≤ N) :
    ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ n,
      n ∈ packingAdmissible S.completedLimit.base δ R → n ≤ N := by
  have hcover :=
    S.eventually_closedBall_subset_range_of_eventually_reindexed_ambient_isometry
      X r m hr ambientEquiv ambient_base stageToBall stageToBall_comm
  exact
    S.exists_packing_bound_completedLimit_of_eventually_cofinal_reindexed_stage_coverage
      r m hrcofinal hm hcover hpack

end CompatiblePointedCompactSystem

end MorganTianLib

#print axioms MorganTianLib.CompatiblePointedCompactSystem.packing_bound_of_nonpositive_radius
#print axioms MorganTianLib.CompatiblePointedCompactSystem.eventually_uniform_packing_bound_of_pointedGHConverges_compact_target_all_radii
#print axioms MorganTianLib.CompatiblePointedCompactSystem.eventually_uniform_packing_bounds_of_pointedGHConverges_compact_target
#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_stage_packingWitness_of_completedLimit_packingWitness_at
#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_stage_packingWitness_of_completedLimit_packingWitness
#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_packing_bound_completedLimit_of_eventually_cofinal_stage_coverage
#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_packing_bound_completedLimit_of_eventually_cofinal_reindexed_stage_coverage
#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_packing_bound_completedLimit_of_eventually_nat_stage_coverage
#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_finite_isDeltaNet_completedLimit_closedBall_of_eventually_cofinal_stage_coverage
#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_packing_bound_completedLimit_of_pointedGHConverges_compact_stage
#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_packing_bound_completedLimit_of_radial_stage_coverage
#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_finite_isDeltaNet_completedLimit_closedBall_of_stage_packing
#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_packing_bound_completedLimit_of_eventually_reindexed_ambient_isometry
