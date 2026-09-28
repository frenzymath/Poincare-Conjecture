import MorganTianLib.Ch05.PointedGH

/-!
# Morgan--Tian Chapter 5: ambient-universe independence of pointed GH distance

The source definition of pointed Gromov--Hausdorff distance allows the common
ambient metric space to live in an arbitrary larger universe. For two
finite-diameter source carriers in the same universe, this module defines the
ambient-level-parametrized infimum and proves that it agrees with the
fixed-universe distance in `PointedGH.lean`.

The key construction replaces any large ambient realization by the metric
separation quotient of the disjoint union of the two source carriers. The new
ambient lies in the source universe and has exactly the same Hausdorff error.
-/

open Set

noncomputable section

namespace MorganTianLib

universe u v

/-- **Math.** A pointed realization whose ambient carrier may live in the larger
universe `max u v`. -/
structure PointedGHRealizationIn
    (X Y : FiniteDiameterBasedMetricSpace.{u}) where
  ambient : BasedMetricSpaceBundle.{max u v}
  left : X.carrier -> ambient.carrier
  right : Y.carrier -> ambient.carrier
  left_isometry : Isometry left
  right_isometry : Isometry right
  left_base : left X.base = ambient.base
  right_base : right Y.base = ambient.base

namespace PointedGHRealizationIn

/-- **Math.** Lift a fixed-universe realization to an arbitrary larger ambient
universe. -/
noncomputable def ofFixed
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) :
    PointedGHRealizationIn.{u, v} X Y :=
  { ambient :=
      { carrier := ULift.{v, u} R.ambient.carrier
        metric := inferInstance
        base := ULift.up R.ambient.base }
    left := Function.comp ULift.up R.left
    right := Function.comp ULift.up R.right
    left_isometry := Isometry.of_dist_eq fun x y => by
      simp only [Function.comp_apply, ULift.dist_eq]
      exact R.left_isometry.dist_eq x y
    right_isometry := Isometry.of_dist_eq fun x y => by
      simp only [Function.comp_apply, ULift.dist_eq]
      exact R.right_isometry.dist_eq x y
    left_base := congrArg ULift.up R.left_base
    right_base := congrArg ULift.up R.right_base }

end PointedGHRealizationIn

/-- **Math.** Hausdorff distance between the two copies in a larger-universe pointed
realization. -/
noncomputable def pointedHausdorffDistIn
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) : Real :=
  @Metric.hausdorffDist R.ambient.carrier
    R.ambient.metric.toPseudoMetricSpace
    (Set.range R.left) (Set.range R.right)

/-- **Math.** Hausdorff errors realized in ambient carriers of universe `max u v`. -/
def pointedGHAdmissibleDistancesIn
    (X Y : FiniteDiameterBasedMetricSpace.{u}) : Set Real :=
  Set.range (fun R : PointedGHRealizationIn.{u, v} X Y =>
    pointedHausdorffDistIn R)

/-- **Math.** Pointed Gromov--Hausdorff distance computed using ambient carriers in
universe `max u v`. -/
noncomputable def pointedGHDistanceIn
    (X Y : FiniteDiameterBasedMetricSpace.{u}) : Real :=
  sInf (pointedGHAdmissibleDistancesIn.{u, v} X Y)

theorem pointedGHAdmissibleDistancesIn_nonempty
    (X Y : FiniteDiameterBasedMetricSpace.{u}) :
    (pointedGHAdmissibleDistancesIn.{u, v} X Y).Nonempty :=
  ⟨pointedHausdorffDistIn
      (PointedGHRealizationIn.ofFixed (basePointedGHRealization X Y)),
    PointedGHRealizationIn.ofFixed (basePointedGHRealization X Y), rfl⟩

theorem pointedGHAdmissibleDistancesIn_bddBelow
    (X Y : FiniteDiameterBasedMetricSpace.{u}) :
    BddBelow (pointedGHAdmissibleDistancesIn.{u, v} X Y) := by
  refine ⟨0, ?_⟩
  rintro d ⟨R, rfl⟩
  exact Metric.hausdorffDist_nonneg

/-- **Math.** Every larger-universe realization bounds the corresponding infimum. -/
theorem pointedGHDistanceIn_le_realization
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    pointedGHDistanceIn.{u, v} X Y <= pointedHausdorffDistIn R := by
  unfold pointedGHDistanceIn pointedGHAdmissibleDistancesIn
  exact csInf_le (pointedGHAdmissibleDistancesIn_bddBelow X Y) ⟨R, rfl⟩

/-- **Math.** Lifting a realization does not change its Hausdorff error. -/
theorem pointedHausdorffDistIn_ofFixed
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealization X Y) :
    pointedHausdorffDistIn (PointedGHRealizationIn.ofFixed R :
      PointedGHRealizationIn.{u, v} X Y) = pointedHausdorffDist R := by
  let e : R.ambient.carrier -> ULift.{v, u} R.ambient.carrier := ULift.up
  have he : Isometry e := Isometry.of_dist_eq fun x y => by
    exact ULift.dist_eq _ _
  change Metric.hausdorffDist (Set.range (Function.comp e R.left))
      (Set.range (Function.comp e R.right)) =
    Metric.hausdorffDist (Set.range R.left) (Set.range R.right)
  rw [Set.range_comp, Set.range_comp, Metric.hausdorffDist_image he]

private def PointedGHRealizationIn.sumMap
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    Sum X.carrier Y.carrier -> R.ambient.carrier
  | Sum.inl x => R.left x
  | Sum.inr y => R.right y

private abbrev pointedGHAmbientCompressionPseudoMetric
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    PseudoMetricSpace (Sum X.carrier Y.carrier) :=
  PseudoMetricSpace.induced R.sumMap R.ambient.metric.toPseudoMetricSpace

private def PointedGHAmbientCompression
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) : Type u :=
  @SeparationQuotient (Sum X.carrier Y.carrier)
    (pointedGHAmbientCompressionPseudoMetric R).toUniformSpace.toTopologicalSpace

private abbrev pointedGHAmbientCompressionMetricSpace
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    MetricSpace (PointedGHAmbientCompression R) :=
  inferInstanceAs <| MetricSpace <|
    @SeparationQuotient (Sum X.carrier Y.carrier)
      (pointedGHAmbientCompressionPseudoMetric R).toUniformSpace.toTopologicalSpace

attribute [local instance] pointedGHAmbientCompressionMetricSpace

private def PointedGHRealizationIn.compressionLeft
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    X.carrier -> PointedGHAmbientCompression R :=
  fun x => Quotient.mk'' (Sum.inl x)

private def PointedGHRealizationIn.compressionRight
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    Y.carrier -> PointedGHAmbientCompression R :=
  fun y => Quotient.mk'' (Sum.inr y)

private theorem PointedGHRealizationIn.compressionLeft_isometry
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    Isometry R.compressionLeft := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (R.left x) (R.left y) = dist x y
  exact R.left_isometry.dist_eq x y

private theorem PointedGHRealizationIn.compressionRight_isometry
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    Isometry R.compressionRight := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (R.right x) (R.right y) = dist x y
  exact R.right_isometry.dist_eq x y

private def PointedGHRealizationIn.compressionEmbedding
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    PointedGHAmbientCompression R -> R.ambient.carrier := by
  let i := pointedGHAmbientCompressionPseudoMetric R
  let _ := i.toUniformSpace.toTopologicalSpace
  exact SeparationQuotient.lift R.sumMap fun a b hab => by
    apply dist_eq_zero.mp
    change @dist (Sum X.carrier Y.carrier) i.toDist a b = 0
    exact Metric.inseparable_iff.mp hab

private theorem PointedGHRealizationIn.compressionEmbedding_isometry
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    Isometry R.compressionEmbedding := by
  apply Isometry.of_dist_eq
  intro a b
  induction a using Quotient.inductionOn' with
  | _ a =>
    induction b using Quotient.inductionOn' with
    | _ b => rfl

/-- **Math.** Compress a realization with an arbitrarily large ambient carrier to a
realization whose ambient carrier lies in the source universe. -/
noncomputable def PointedGHRealizationIn.toFixed
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    PointedGHRealization X Y :=
  { ambient :=
      { carrier := PointedGHAmbientCompression R
        metric := inferInstance
        base := R.compressionLeft X.base }
    left := R.compressionLeft
    right := R.compressionRight
    left_isometry := R.compressionLeft_isometry
    right_isometry := R.compressionRight_isometry
    left_base := rfl
    right_base := by
      let i := pointedGHAmbientCompressionPseudoMetric R
      let _ := i.toUniformSpace.toTopologicalSpace
      apply SeparationQuotient.mk_eq_mk.mpr
      apply Metric.inseparable_iff.mpr
      change dist (R.right Y.base) (R.left X.base) = 0
      rw [R.left_base, R.right_base, dist_self] }

private theorem PointedGHRealizationIn.compressionEmbedding_comp_left
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    Function.comp R.compressionEmbedding R.compressionLeft = R.left := by
  funext x
  rfl

private theorem PointedGHRealizationIn.compressionEmbedding_comp_right
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    Function.comp R.compressionEmbedding R.compressionRight = R.right := by
  funext y
  rfl

/-- **Math.** Compressing a realization preserves its Hausdorff error exactly. -/
theorem PointedGHRealizationIn.pointedHausdorffDist_toFixed
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    pointedHausdorffDist R.toFixed = pointedHausdorffDistIn R := by
  have h := Metric.hausdorffDist_image
    (s := Set.range R.compressionLeft)
    (t := Set.range R.compressionRight)
    R.compressionEmbedding_isometry
  change Metric.hausdorffDist (Set.range R.compressionLeft)
      (Set.range R.compressionRight) =
    Metric.hausdorffDist (Set.range R.left) (Set.range R.right)
  rw [<- h, <- Set.range_comp, <- Set.range_comp,
    R.compressionEmbedding_comp_left, R.compressionEmbedding_comp_right]

/-- **Math.** Allowing the common pointed ambient metric space to live in any larger
universe does not change the pointed Gromov--Hausdorff distance. -/
theorem pointedGHDistanceIn_eq_pointedGHDistance
    (X Y : FiniteDiameterBasedMetricSpace.{u}) :
    pointedGHDistanceIn.{u, v} X Y = pointedGHDistance X Y := by
  apply le_antisymm
  · unfold pointedGHDistance
    apply le_csInf (pointedGHAdmissibleDistances_nonempty X Y)
    rintro d ⟨R, rfl⟩
    exact (pointedGHDistanceIn_le_realization
      (PointedGHRealizationIn.ofFixed R : PointedGHRealizationIn.{u, v} X Y)).trans_eq
        (pointedHausdorffDistIn_ofFixed R)
  · unfold pointedGHDistanceIn
    apply le_csInf (pointedGHAdmissibleDistancesIn_nonempty X Y)
    rintro d ⟨R, rfl⟩
    exact (pointedGHDistance_le_realization R.toFixed).trans_eq
      R.pointedHausdorffDist_toFixed

/-- **Math.** Every realization in a larger ambient universe bounds the original
fixed-universe pointed Gromov--Hausdorff distance. -/
theorem pointedGHDistance_le_realizationIn
    {X Y : FiniteDiameterBasedMetricSpace.{u}}
    (R : PointedGHRealizationIn.{u, v} X Y) :
    pointedGHDistance X Y <= pointedHausdorffDistIn R := by
  rw [<- pointedGHDistanceIn_eq_pointedGHDistance]
  exact pointedGHDistanceIn_le_realization R

end MorganTianLib

end

#print axioms MorganTianLib.PointedGHRealizationIn.toFixed
#print axioms MorganTianLib.pointedGHDistanceIn_eq_pointedGHDistance
#print axioms MorganTianLib.pointedGHDistance_le_realizationIn
