import MorganTianLib.Ch05.CompatibleBallEmbedding
import MorganTianLib.Ch05.CrossRadiusLimitDistance

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

/-- **Math.** Same-radius compact closed-ball limits admit an attained pointed
Gromov--Hausdorff realization.  The based isometry comes from the common
closed-ball limit, and the realization is the explicit zero-error coupling. -/
theorem exists_attainment_of_sameRadius_closedBall_limits
    (X : ℕ -> BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (r : ℝ) (hr : 0 ≤ r)
    (L₁ L₂ : FiniteDiameterBasedMetricSpace.{u})
    [CompactSpace L₁.carrier] [CompactSpace L₂.carrier]
    (hconv₁ : PointedGHConverges
      (fun k => closedBallModel (X k) r hr) L₁)
    (hconv₂ : PointedGHConverges
      (fun k => closedBallModel (X k) r hr) L₂) :
    ∃ R : PointedGHRealization L₁ L₂,
      pointedGHDistance L₁ L₂ = pointedHausdorffDist R := by
  obtain ⟨e, hbase⟩ := exists_basedIsometry_of_sameRadius_closedBall_limits
    X r hr L₁ L₂ hconv₁ hconv₂
  exact exists_attainment_of_based_isometry e hbase

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
provide the transition embedding.  The compact common-limit constructor now
supplies the based isometries without requiring an explicit pointed-distance
attainment witness. -/

/-- **Math.** Nested closed-ball identifications with compatible basepoints
directly extract the compatible transition system.  The common-limit data and
compactness supply the stage identifications, while the nested models supply
the transition embedding; no attainment or canonical-coupling premise is
needed. -/
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
  let embed : ∀ n, (inner n).carrier → (stage (n + 1)).carrier := fun n =>
    (ball_to_stage (n + 1)) ∘
      (closedBallModelInclusion X (r n) (r (n + 1)) (hr n) (hr (n + 1))
        (hmono n)) ∘
      (inner_to_ball n)
  have hembed_isometry : ∀ n, Isometry (embed n) := by
    intro n
    exact (ball_to_stage (n + 1)).isometry.comp
      ((closedBallModelInclusion_isometry X (r n) (r (n + 1))
        (hr n) (hr (n + 1)) (hmono n)).comp (inner_to_ball n).isometry)
  have hembed_base : ∀ n,
      embed n (inner n).base = (stage (n + 1)).base := by
    intro n
    dsimp [embed]
    rw [inner_to_ball_base n]
    rw [closedBallModelInclusion_base X (r n) (r (n + 1))
      (hr n) (hr (n + 1)) (hmono n)]
    exact ball_to_stage_base (n + 1)
  exact ofCommonLimits_of_compact_limits stage inner source hstage hinner
    embed hembed_isometry hembed_base

end CompatiblePointedCompactSystem

end MorganTianLib

#print axioms MorganTianLib.CompatiblePointedCompactSystem.ofCommonLimits_of_optimal_base_agreement
#print axioms MorganTianLib.CompatiblePointedCompactSystem.ofCommonLimits_of_nested_closedBall_optimal_base_agreement
#print axioms MorganTianLib.exists_attainment_of_canonical_base_agreement
#print axioms MorganTianLib.exists_attainment_of_based_isometry
#print axioms MorganTianLib.CompatiblePointedCompactSystem.ofCommonLimits_of_nested_closedBall_identifications_of_based_models
