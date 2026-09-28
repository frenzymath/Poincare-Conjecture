import MorganTianLib.Ch05.TransitionExtractionOptimal

/-!
# Morgan--Tian Chapter 5: ambient radial coverage bridge

The compatible compact-stage construction provides a completed ambient before
the geometric identification with the intended limit space is established.
This module isolates the exact metric compatibility needed to recover radial
coverage from such an identification: a based ambient isometry, cofinal
closed-ball radii, and stage-to-ball identifications that commute with the
ambient map.
-/

open Set Filter Metric

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** A based isometry from the completed common ambient to a metric
space, together with compatible cofinal closed-ball stage models, yields the
radial closed-ball coverage required for properness.  The ambient identification
and its stage compatibility are explicit, so this theorem does not assert them
for independently extracted limits. -/
theorem radial_stage_coverage_of_ambient_isometry
    (S : CompatiblePointedCompactSystem.{u})
    (X : BasedMetricSpaceBundle.{u})
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hrcofinal : Tendsto r atTop atTop)
    (ambientEquiv : S.completedLimit.carrier ≃ᵢ X.carrier)
    (ambient_base : ambientEquiv S.completedLimit.base = X.base)
    (stageToBall : ∀ n,
      (S.stage n).carrier ≃ᵢ (closedBallModel X (r n) (hr n)).carrier)
    (stageToBall_comm : ∀ (n : ℕ) (x : (S.stage n).carrier),
      ambientEquiv (S.stageEmbedding n x) = (stageToBall n x).1) :
    ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n) := by
  intro R
  have hev : ∀ᶠ n : ℕ in atTop, R ≤ r n :=
    (Filter.tendsto_atTop.1 hrcofinal) R
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hev
  refine ⟨n, ?_⟩
  intro y hy
  have hyR : dist (ambientEquiv y) X.base ≤ R := by
    have hy' : dist y S.completedLimit.base ≤ R :=
      Metric.mem_closedBall.mp hy
    calc
      dist (ambientEquiv y) X.base =
          dist (ambientEquiv y) (ambientEquiv S.completedLimit.base) := by
            rw [ambient_base]
      _ = dist y S.completedLimit.base := ambientEquiv.dist_eq _ _
      _ ≤ R := hy'
  have hyRn : dist (ambientEquiv y) X.base ≤ r n :=
    hyR.trans (hn n le_rfl)
  let q : (closedBallModel X (r n) (hr n)).carrier :=
    ⟨ambientEquiv y, hyRn⟩
  obtain ⟨x, hx⟩ := (stageToBall n).surjective q
  refine ⟨x, ?_⟩
  apply ambientEquiv.injective
  calc
    ambientEquiv (S.stageEmbedding n x) = (stageToBall n x).1 :=
      stageToBall_comm n x
    _ = q.1 := congrArg Subtype.val hx
    _ = ambientEquiv y := rfl

/-- **Math.** Eventual commutation of reindexed stage-to-ball isometries with a
based ambient isometry gives the exact eventual closed-ball coverage needed by
the compact-stage packing transfer.  No cofinality assumption on the radius
sequence is needed for this pointwise tail statement. -/
theorem eventually_closedBall_subset_range_of_eventually_reindexed_ambient_isometry
    (S : CompatiblePointedCompactSystem.{u})
    (X : BasedMetricSpaceBundle.{u})
    (r : ℕ → ℝ) (m : ℕ → ℕ) (hr : ∀ n, 0 ≤ r n)
    (ambientEquiv : S.completedLimit.carrier ≃ᵢ X.carrier)
    (ambient_base : ambientEquiv S.completedLimit.base = X.base)
    (stageToBall : ∀ k,
      (S.stage (m k)).carrier ≃ᵢ (closedBallModel X (r k) (hr k)).carrier)
    (stageToBall_comm : ∀ᶠ k : ℕ in atTop,
      ∀ x : (S.stage (m k)).carrier,
        ambientEquiv (S.stageEmbedding (m k) x) = (stageToBall k x).1) :
    ∀ᶠ k : ℕ in atTop,
      Metric.closedBall S.completedLimit.base (r k) ⊆
        Set.range (S.stageEmbedding (m k)) := by
  filter_upwards [stageToBall_comm] with k hk
  intro y hy
  have hyR : dist (ambientEquiv y) X.base ≤ r k := by
    have hy' : dist y S.completedLimit.base ≤ r k :=
      Metric.mem_closedBall.mp hy
    calc
      dist (ambientEquiv y) X.base =
          dist (ambientEquiv y) (ambientEquiv S.completedLimit.base) := by
            rw [ambient_base]
      _ = dist y S.completedLimit.base := ambientEquiv.dist_eq _ _
      _ ≤ r k := hy'
  let q : (closedBallModel X (r k) (hr k)).carrier :=
    ⟨ambientEquiv y, hyR⟩
  obtain ⟨x, hx⟩ := (stageToBall k).surjective q
  refine ⟨x, ?_⟩
  apply ambientEquiv.injective
  calc
    ambientEquiv (S.stageEmbedding (m k) x) = (stageToBall k x).1 :=
      hk x
    _ = q.1 := congrArg Subtype.val hx
    _ = ambientEquiv y := rfl

/-- **Math.** The ambient-isometry radial-coverage argument remains valid when
the available closed-ball models and stage embeddings are indexed by an
eventual reindexing.  The cofinal radius tail and the eventual commutation tail
are synchronized at one late reindexed stage. -/
theorem radial_stage_coverage_of_eventually_reindexed_ambient_isometry
    (S : CompatiblePointedCompactSystem.{u})
    (X : BasedMetricSpaceBundle.{u})
    (r : ℕ → ℝ) (m : ℕ → ℕ) (hr : ∀ n, 0 ≤ r n)
    (hrcofinal : Tendsto r atTop atTop)
    (ambientEquiv : S.completedLimit.carrier ≃ᵢ X.carrier)
    (ambient_base : ambientEquiv S.completedLimit.base = X.base)
    (stageToBall : ∀ k,
      (S.stage (m k)).carrier ≃ᵢ (closedBallModel X (r k) (hr k)).carrier)
    (stageToBall_comm : ∀ᶠ k : ℕ in atTop,
      ∀ x : (S.stage (m k)).carrier,
        ambientEquiv (S.stageEmbedding (m k) x) = (stageToBall k x).1) :
    ∀ R : ℝ, ∃ k : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding (m k)) := by
  intro R
  have hev : ∀ᶠ k : ℕ in atTop, R ≤ r k :=
    (Filter.tendsto_atTop.1 hrcofinal) R
  obtain ⟨Nr, hNr⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨Ncomm, hNcomm⟩ :=
    Filter.eventually_atTop.1 stageToBall_comm
  let k := max Nr Ncomm
  have hNrk : Nr ≤ k := Nat.le_max_left _ _
  have hNcommk : Ncomm ≤ k := Nat.le_max_right _ _
  refine ⟨k, ?_⟩
  intro y hy
  have hyR : dist (ambientEquiv y) X.base ≤ R := by
    have hy' : dist y S.completedLimit.base ≤ R :=
      Metric.mem_closedBall.mp hy
    calc
      dist (ambientEquiv y) X.base =
          dist (ambientEquiv y) (ambientEquiv S.completedLimit.base) := by
            rw [ambient_base]
      _ = dist y S.completedLimit.base := ambientEquiv.dist_eq _ _
      _ ≤ R := hy'
  have hyRk : dist (ambientEquiv y) X.base ≤ r k :=
    hyR.trans (hNr k hNrk)
  let q : (closedBallModel X (r k) (hr k)).carrier :=
    ⟨ambientEquiv y, hyRk⟩
  obtain ⟨x, hx⟩ := (stageToBall k).surjective q
  refine ⟨x, ?_⟩
  apply ambientEquiv.injective
  calc
    ambientEquiv (S.stageEmbedding (m k) x) = (stageToBall k x).1 :=
      hNcomm k hNcommk x
    _ = q.1 := congrArg Subtype.val hx
    _ = ambientEquiv y := rfl

end CompatiblePointedCompactSystem

end MorganTianLib

#print axioms MorganTianLib.CompatiblePointedCompactSystem.radial_stage_coverage_of_ambient_isometry
#print axioms MorganTianLib.CompatiblePointedCompactSystem.eventually_closedBall_subset_range_of_eventually_reindexed_ambient_isometry
#print axioms MorganTianLib.CompatiblePointedCompactSystem.radial_stage_coverage_of_eventually_reindexed_ambient_isometry
