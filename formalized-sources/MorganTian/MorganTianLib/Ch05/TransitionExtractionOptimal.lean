import MorganTianLib.Ch05.CompatibleBallEmbedding

/-!
# Morgan--Tian Chapter 5: canonical compact-coupling transition extraction

The generic transition extractor keeps attainment of the pointed infimum as an
explicit hypothesis.  For compact stages, Mathlib's canonical Gromov--Hausdorff
coupling supplies that attainment whenever the marked points agree.  This file
records that concrete bridge, while leaving the marked-point agreement (and all
geometric hypotheses needed to prove it) visible.
-/

noncomputable section

namespace MorganTianLib

universe u

/-! Mathlib's canonical compact coupling is stated with typeclass arguments,
whereas `PointedCompactMetricSpace` stores those instances as fields.  This
predicate exposes the marked-point premise while installing the stored fields
locally, so it can be used for dependent stage families. -/

/-- **Math.** Canonical optimal-coupling embeddings agree on the distinguished
points. -/
def CanonicalBaseAgreement
    (X Y : PointedCompactMetricSpace.{u}) : Prop :=
  letI : MetricSpace X.carrier := X.metric
  letI : CompactSpace X.carrier := X.compact
  letI : Nonempty X.carrier := X.nonempty
  letI : MetricSpace Y.carrier := Y.metric
  letI : CompactSpace Y.carrier := Y.compact
  letI : Nonempty Y.carrier := Y.nonempty
  GromovHausdorff.optimalGHInjl X.carrier Y.carrier X.base =
    GromovHausdorff.optimalGHInjr X.carrier Y.carrier Y.base

/-- **Math.** A canonical marked-point agreement for two compact bundled spaces
produces an attained realization for the pointed finite-diameter distance. -/
theorem exists_attainment_of_canonical_base_agreement
    (X Y : PointedCompactMetricSpace.{u})
    (hbase : CanonicalBaseAgreement X Y) :
    ∃ R : PointedGHRealization
        X.toFiniteDiameterBasedMetricSpace
        Y.toFiniteDiameterBasedMetricSpace,
      pointedGHDistance X.toFiniteDiameterBasedMetricSpace
          Y.toFiniteDiameterBasedMetricSpace = pointedHausdorffDist R := by
  letI : MetricSpace X.carrier := X.metric
  letI : CompactSpace X.carrier := X.compact
  letI : Nonempty X.carrier := X.nonempty
  letI : MetricSpace Y.carrier := Y.metric
  letI : CompactSpace Y.carrier := Y.compact
  letI : Nonempty Y.carrier := Y.nonempty
  have hb :
      GromovHausdorff.optimalGHInjl X.carrier Y.carrier X.base =
        GromovHausdorff.optimalGHInjr X.carrier Y.carrier Y.base := by
    simpa [CanonicalBaseAgreement] using hbase
  exact @exists_pointedGHRealization_attaining_of_optimal_base_agreement
    X.toFiniteDiameterBasedMetricSpace
    Y.toFiniteDiameterBasedMetricSpace
    X.compact Y.compact hb

/-- **Math.** Any based isometry between finite-diameter metric spaces gives an
explicit pointed realization attaining the pointed distance.  The realization
uses the target as ambient and therefore has zero Hausdorff error. -/
theorem exists_attainment_of_based_isometry
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (e : X.carrier ≃ᵢ Y.carrier) (hbase : e X.base = Y.base) :
    ∃ R : PointedGHRealization X Y,
      pointedGHDistance X Y = pointedHausdorffDist R := by
  let R : PointedGHRealization X Y :=
    { ambient :=
        { carrier := Y.carrier
          metric := Y.metric
          base := Y.base }
      left := e
      right := id
      left_isometry := e.isometry
      right_isometry := isometry_id
      left_base := hbase
      right_base := rfl }
  have hR : pointedHausdorffDist R = 0 := by
    unfold pointedHausdorffDist
    rw [e.surjective.range_eq, Set.range_id]
    exact Metric.hausdorffDist_self_zero
  refine ⟨R, ?_⟩
  have hzero := pointedGHDistance_eq_zero_of_basedIsometry X Y e hbase
  rw [hzero, hR]

namespace CompatiblePointedCompactSystem

/-- **Math.** Canonical compact-coupling base agreement supplies the attainment
data required by `ofCommonLimits`, so independently extracted consecutive
compact limits yield a compatible pointed system.  The common source limits,
compactness, and marked-point agreement remain explicit; no transition or
radial-coverage hypothesis is hidden in the construction. -/
noncomputable def ofCommonLimits_of_optimal_base_agreement
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (hbase : ∀ n, CanonicalBaseAgreement (stage n) (inner n))
    (embed : ∀ n, (inner n).carrier → (stage (n + 1)).carrier)
    (embed_isometry : ∀ n, Isometry (embed n))
    (embed_base : ∀ n, embed n (inner n).base = (stage (n + 1)).base) :
    CompatiblePointedCompactSystem.{u} := by
  refine ofCommonLimits stage inner source hstage hinner ?_ embed
    embed_isometry embed_base
  intro n
  exact exists_attainment_of_canonical_base_agreement (stage n) (inner n)
    (hbase n)

/-! The nested closed-ball adapter is the common geometric use of the preceding
bridge.  It removes only the redundant attainment field; nested identifications
and the canonical marked-point agreement are still supplied by the caller. -/

/-- **Math.** For nested closed-ball models, canonical marked-point agreement at
each adjacent pair supplies the compact-coupling attainment required to extract
the transition system. -/
noncomputable def ofCommonLimits_of_nested_closedBall_optimal_base_agreement
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (hbase : ∀ n, CanonicalBaseAgreement (stage n) (inner n))
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hmono : ∀ n, r n ≤ r (n + 1))
    (inner_to_ball : ∀ n,
      (inner n).carrier ≃ᵢ (closedBallModel X (r n) (hr n)).carrier)
    (inner_to_ball_base : ∀ n,
      inner_to_ball n (inner n).base =
        (closedBallModel X (r n) (hr n)).base)
    (ball_to_stage : ∀ n,
      (closedBallModel X (r n) (hr n)).carrier ≃ᵢ (stage n).carrier)
    (ball_to_stage_base : ∀ n,
      ball_to_stage n (closedBallModel X (r n) (hr n)).base =
        (stage n).base) :
    CompatiblePointedCompactSystem.{u} := by
  refine ofCommonLimits_of_nested_closedBall_identifications
    (X := X) (stage := stage) (inner := inner) (source := source)
    (hstage := hstage) (hinner := hinner) (hattain := ?_)
    (r := r) (hr := hr) (hmono := hmono)
    (inner_to_ball := inner_to_ball)
    (inner_to_ball_base := inner_to_ball_base)
    (ball_to_stage := ball_to_stage)
    (ball_to_stage_base := ball_to_stage_base)
  intro n
  exact exists_attainment_of_canonical_base_agreement (stage n) (inner n)
    (hbase n)

/-! In the nested closed-ball situation, the two displayed identifications
already provide a based isometry between each pair of limits.  Consequently no
canonical-coupling base-agreement premise is needed: attainment follows from
the explicit zero-error realization induced by that based isometry. -/

/-- **Math.** Nested closed-ball identifications with compatible basepoints
directly extract the compatible transition system.  The attainment and
canonical-coupling premises are derived internally from the based isometry
between the two copies of each closed ball. -/
noncomputable def ofCommonLimits_of_nested_closedBall_identifications_of_based_models
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hmono : ∀ n, r n ≤ r (n + 1))
    (inner_to_ball : ∀ n,
      (inner n).carrier ≃ᵢ (closedBallModel X (r n) (hr n)).carrier)
    (inner_to_ball_base : ∀ n,
      inner_to_ball n (inner n).base =
        (closedBallModel X (r n) (hr n)).base)
    (ball_to_stage : ∀ n,
      (closedBallModel X (r n) (hr n)).carrier ≃ᵢ (stage n).carrier)
    (ball_to_stage_base : ∀ n,
      ball_to_stage n (closedBallModel X (r n) (hr n)).base =
        (stage n).base) :
    CompatiblePointedCompactSystem.{u} := by
  let e : ∀ n, (stage n).carrier ≃ᵢ (inner n).carrier := fun n =>
    (ball_to_stage n).symm.trans (inner_to_ball n).symm
  have hebase : ∀ n, e n (stage n).base = (inner n).base := by
    intro n
    have hs :
        (ball_to_stage n).symm (stage n).base =
          (closedBallModel X (r n) (hr n)).base := by
      apply (ball_to_stage n).injective
      simp [ball_to_stage_base n]
    have hi :
        (inner_to_ball n).symm (closedBallModel X (r n) (hr n)).base =
          (inner n).base := by
      apply (inner_to_ball n).injective
      simp [inner_to_ball_base n]
    change (inner_to_ball n).symm
        ((ball_to_stage n).symm (stage n).base) = (inner n).base
    rw [hs, hi]
  have hattain : ∀ n, ∃ R : PointedGHRealization
      (stage n).toFiniteDiameterBasedMetricSpace
      (inner n).toFiniteDiameterBasedMetricSpace,
      pointedGHDistance
          (stage n).toFiniteDiameterBasedMetricSpace
          (inner n).toFiniteDiameterBasedMetricSpace =
        pointedHausdorffDist R := by
    intro n
    exact exists_attainment_of_based_isometry (e n) (hebase n)
  exact ofCommonLimits_of_nested_closedBall_identifications
    (X := X) (stage := stage) (inner := inner) (source := source)
    (hstage := hstage) (hinner := hinner) (hattain := hattain)
    (r := r) (hr := hr) (hmono := hmono)
    (inner_to_ball := inner_to_ball)
    (inner_to_ball_base := inner_to_ball_base)
    (ball_to_stage := ball_to_stage)
    (ball_to_stage_base := ball_to_stage_base)

end CompatiblePointedCompactSystem

end MorganTianLib

#print axioms MorganTianLib.CompatiblePointedCompactSystem.ofCommonLimits_of_optimal_base_agreement
#print axioms MorganTianLib.CompatiblePointedCompactSystem.ofCommonLimits_of_nested_closedBall_optimal_base_agreement
#print axioms MorganTianLib.exists_attainment_of_canonical_base_agreement
#print axioms MorganTianLib.exists_attainment_of_based_isometry
#print axioms MorganTianLib.CompatiblePointedCompactSystem.ofCommonLimits_of_nested_closedBall_identifications_of_based_models
