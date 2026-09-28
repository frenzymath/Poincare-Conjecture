import MorganTianLib.Ch05.UnboundedAssembly
import MorganTianLib.Ch05.AdvanceCompactAssembly

/-!
# Morgan--Tian Chapter 5: packing bounds from unbounded pointed limits

This module records the fixed-radius converse needed by the unbounded
precompactness route.  A packing in an ambient space is first viewed in the
closed-ball subtype, where compact-target convergence supplies a uniform
cardinality bound.
-/

open Set Filter Metric

noncomputable section

namespace MorganTianLib

universe u

/-! ## Ambient-to-closed-ball transport -/

/-- **Math.** A finite packing in an ambient metric space can be regarded as a
packing in the corresponding closed-ball subtype.  The strict center and
containment conditions are unchanged by the subtype metric; the nonnegative
radius hypothesis supplies the subtype membership of each center and of the
distinguished base point. -/
def packingWitness_to_closedBall
    {X : Type*} [MetricSpace X] {x : X} {δ R : ℝ} {n : ℕ}
    (hR : 0 ≤ R) (w : PackingWitness x δ R n) :
    PackingWitness
      (⟨x, Metric.mem_closedBall_self hR⟩ : Metric.closedBall x R)
      δ R n := by
  let c : Fin n → Metric.closedBall x R := fun i =>
    ⟨w.center i, (Metric.mem_ball.mp (w.center_mem i)).le⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i
    rw [Metric.mem_ball]
    change dist (w.center i) x < R
    exact Metric.mem_ball.mp (w.center_mem i)
  · intro i z hz
    apply Metric.mem_ball.mpr
    apply w.ball_subset i
    apply Metric.mem_ball.mpr
    simpa only [c, Subtype.dist_eq] using (Metric.mem_ball.mp hz)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    apply Set.disjoint_left.mp (w.pairwise_disjoint hij)
    · apply Metric.mem_ball.mpr
      change dist (z : X) (w.center i) < δ
      simpa only [c, Subtype.dist_eq] using (Metric.mem_ball.mp hzi)
    · apply Metric.mem_ball.mpr
      simpa only [c, Subtype.dist_eq] using (Metric.mem_ball.mp hzj)

/-! The subtype transport is bidirectional up to a factor-two loss in scale.
The larger-carrier version is needed when a fixed target radius is compared
through a realization at a buffered radius.  In the reverse direction,
disjoint subtype `delta`-balls give `delta`-separated ambient centers, hence
disjoint ambient `(delta / 2)`-balls after adding the corresponding radial
buffer. -/

/-- **Math.** A packing witness in an ambient metric space embeds into any
larger closed-ball subtype without changing its scale or containing radius. -/
def packingWitness_to_closedBall_of_radius_le
    {X : Type*} [MetricSpace X] {x : X} {δ R T : ℝ} {n : ℕ}
    (hT : 0 ≤ T) (hRT : R ≤ T) (w : PackingWitness x δ R n) :
    PackingWitness
      (⟨x, Metric.mem_closedBall_self hT⟩ : Metric.closedBall x T)
      δ R n := by
  let c : Fin n → Metric.closedBall x T := fun i =>
    ⟨w.center i, (Metric.mem_ball.mp (w.center_mem i)).le.trans hRT⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · intro i
    rw [Metric.mem_ball]
    change dist (w.center i) x < R
    exact Metric.mem_ball.mp (w.center_mem i)
  · intro i z hz
    apply Metric.mem_ball.mpr
    apply w.ball_subset i
    apply Metric.mem_ball.mpr
    simpa only [c, Subtype.dist_eq] using (Metric.mem_ball.mp hz)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    apply Set.disjoint_left.mp (w.pairwise_disjoint hij)
    · apply Metric.mem_ball.mpr
      simpa only [c, Subtype.dist_eq] using (Metric.mem_ball.mp hzi)
    · apply Metric.mem_ball.mpr
      simpa only [c, Subtype.dist_eq] using (Metric.mem_ball.mp hzj)

/-- **Math.** A packing witness in a closed-ball subtype gives an ambient
packing witness after halving the scale and enlarging the containing radius by
that half-scale.  This loss is necessary for general metric spaces: subtype
balls only control possible intersections inside the closed ball. -/
def packingWitness_from_closedBall_halfScale
    {X : Type*} [MetricSpace X] {x : X} {δ R T : ℝ} {n : ℕ}
    (hT : 0 ≤ T) (hδ : 0 < δ)
    (w : PackingWitness
      (⟨x, Metric.mem_closedBall_self hT⟩ : Metric.closedBall x T)
      δ R n) : PackingWitness x (δ / 2) (R + δ / 2) n := by
  let c : Fin n → X := fun i => (w.center i : X)
  have hc : ∀ i, dist (c i) x + δ / 2 ≤ R + δ / 2 := by
    intro i
    have hi := Metric.mem_ball.mp (w.center_mem i)
    have hi' : dist (w.center i : X) x < R := by
      simpa only [Subtype.dist_eq] using hi
    change dist (w.center i : X) x + δ / 2 ≤ R + δ / 2
    linarith
  have hsep : ∀ ⦃i j : Fin n⦄, i ≠ j →
      2 * (δ / 2) ≤ dist (c i) (c j) := by
    intro i j hij
    have hsep' := w.center_separated hδ hij
    calc
      2 * (δ / 2) = δ := by ring
      _ ≤ dist (c i) (c j) := by
        simpa only [c, Subtype.dist_eq] using hsep'
  exact packingWitness_of_separated_centers x (by linarith) c hc hsep

/-- **Math.** An unbounded pointed-GH limit inherits all-scale packing bounds
from its approximating sequence.  For a requested target radius `R`, the
realization is taken at the buffered radius `R + 2 + δ / 8`; a source packing
is transported into that closed-ball subtype, while a target packing at `R` is
embedded into the same larger subtype.  Thus no properness or compactness of
the limit is assumed, and the source packing hypothesis remains explicit. -/
theorem exists_packing_bound_of_pointedGHConvergesUnbounded_source_packing
    {X : ℕ → BasedMetricSpaceBundle.{u}}
    {Y : BasedMetricSpaceBundle.{u}}
    [∀ k, LengthSpace (X k).carrier] [LengthSpace Y.carrier]
    (hconv : PointedGHConvergesUnbounded X Y)
    (hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ᶠ k in atTop,
      ∀ n, n ∈ packingAdmissible (X k).base δ R → n ≤ N) :
    ∀ δ R, 0 < δ → ∃ N : ℕ,
      ∀ n, n ∈ packingAdmissible Y.base δ R → n ≤ N := by
  intro δ R hδ
  by_cases hR : 0 ≤ R
  · let T : ℝ := R + 2 + δ / 8
    have hT : 0 ≤ T := by
      dsimp [T]
      linarith
    have hRT : R ≤ T := by
      dsimp [T]
      linarith
    have hTpos : 0 < T := by
      dsimp [T]
      linarith
    obtain ⟨N, hN⟩ := hpack (δ / 8 / 2) (T + δ / 8 / 2) (by linarith)
    have hclosed :
        PointedGHConverges
          (fun k => closedBallModel (X k) T hT)
          (closedBallModel Y T hT) :=
      (pointedGHConvergesUnbounded_iff_fixedRadius_closedBall X Y).mp
        hconv T hTpos
    let ε : ℝ := min (δ / 16) (1 / 2)
    have hε : 0 < ε := by
      dsimp [ε]
      exact lt_min (by linarith) (by norm_num)
    obtain ⟨Kdist, hKdist⟩ :=
      (Metric.tendsto_atTop.1 hclosed.2) ε hε
    obtain ⟨Kpack, hKpack⟩ := Filter.eventually_atTop.1 hN
    let k : ℕ := max Kdist Kpack
    have hKdist_le : Kdist ≤ k := Nat.le_max_left _ _
    have hKpack_le : Kpack ≤ k := Nat.le_max_right _ _
    have hdist :
        dist (pointedGHDistance
          (closedBallModel (X k) T hT)
          (closedBallModel Y T hT)) 0 < ε :=
      hKdist k hKdist_le
    have hgh : pointedGHDistance
        (closedBallModel (X k) T hT)
        (closedBallModel Y T hT) < ε := by
      simpa [Real.dist_eq, abs_of_nonneg
        (pointedGHDistance_nonneg _ _)] using hdist
    obtain ⟨Q, hQ⟩ := exists_pointedGHRealization_lt_add
      (closedBallModel (X k) T hT) (closedBallModel Y T hT) hε
    have hε_le_δ : ε ≤ δ / 16 := min_le_left _ _
    have hε_le_one : ε ≤ 1 / 2 := min_le_right _ _
    have htwice : 2 * ε ≤ min (δ / 8) 1 := by
      apply le_min
      · linarith
      · linarith
    have hHaus : pointedHausdorffDist Q < min (δ / 8) 1 := by
      calc
        pointedHausdorffDist Q <
            pointedGHDistance
              (closedBallModel (X k) T hT)
              (closedBallModel Y T hT) + ε := hQ
        _ < ε + ε := by linarith
        _ = 2 * ε := by ring
        _ ≤ min (δ / 8) 1 := htwice
    have hpack_sub : ∀ n,
        n ∈ packingAdmissible
          (closedBallModel (X k) T hT).base (δ / 8) T → n ≤ N := by
      intro n hn
      rcases hn with ⟨w⟩
      apply hKpack k hKpack_le n
      exact ⟨packingWitness_from_closedBall_halfScale hT (by linarith) w⟩
    obtain ⟨N', htarget_sub⟩ :=
      exists_packing_bound_of_pointedGHRealization_source_packing_at
        Q hδ hR ⟨N, hpack_sub⟩ hHaus
    refine ⟨N', ?_⟩
    intro n hn
    apply htarget_sub n
    rcases hn with ⟨w⟩
    exact ⟨packingWitness_to_closedBall_of_radius_le hT hRT w⟩
  · refine ⟨0, ?_⟩
    intro n hn
    exact CompatiblePointedCompactSystem.packing_bound_of_nonpositive_radius Y.base
      (le_of_not_ge hR) n hn

/-! ## The fixed-radius converse -/

/-- **Math.** If pointed GH convergence is unbounded and the target is a proper
length space, then every positive scale and every radius have an eventual
uniform source packing bound.  For positive radii, fixed-radius closed-ball
convergence and compactness of the target closed ball reduce the claim to the
compact-target packing producer.  Nonpositive radii are handled directly by
the empty-ball argument. -/
theorem eventually_uniform_packing_bound_of_pointedGHConvergesUnbounded_proper_target
    {X : ℕ → BasedMetricSpaceBundle.{u}}
    {Y : BasedMetricSpaceBundle.{u}}
    [∀ k, LengthSpace (X k).carrier]
    [LengthSpace Y.carrier] [ProperSpace Y.carrier]
    (hconv : PointedGHConvergesUnbounded X Y)
    {δ R : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ᶠ k in atTop,
      ∀ n, n ∈ packingAdmissible (X k).base δ R → n ≤ N := by
  by_cases hRpos : 0 < R
  · let hR : 0 ≤ R := hRpos.le
    have hclosed :
        PointedGHConverges
          (fun k => closedBallModel (X k) R hR)
          (closedBallModel Y R hR) :=
      (pointedGHConvergesUnbounded_iff_fixedRadius_closedBall X Y).mp
        hconv R hRpos
    letI : CompactSpace (closedBallModel Y R hR).carrier :=
      isCompact_iff_compactSpace.mp
        (ProperSpace.isCompact_closedBall Y.base R)
    obtain ⟨N, hN⟩ :=
      eventually_uniform_packing_bound_of_pointedGHConverges_compact_target
        hclosed hδ hR
    refine ⟨N, ?_⟩
    filter_upwards [hN] with k hk
    intro n hn
    rcases hn with ⟨w⟩
    apply hk n
    exact ⟨by
      have hw := packingWitness_to_closedBall hR w
      change PackingWitness (closedBallModel (X k) R hR).base δ R n at hw
      exact hw⟩
  · refine ⟨0, Filter.Eventually.of_forall ?_⟩
    intro k n hn
    exact CompatiblePointedCompactSystem.packing_bound_of_nonpositive_radius (X k).base
      (le_of_not_gt hRpos) n hn

#print axioms MorganTianLib.packingWitness_to_closedBall_of_radius_le
#print axioms MorganTianLib.packingWitness_from_closedBall_halfScale
#print axioms MorganTianLib.exists_packing_bound_of_pointedGHConvergesUnbounded_source_packing
#print axioms MorganTianLib.eventually_uniform_packing_bound_of_pointedGHConvergesUnbounded_proper_target

end MorganTianLib
