import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Geometry.DistinctEndRays
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Geometry.ChordConeAnnulus

/-!
# Direct audits of actual ray distinction and compact chord-cone annuli

These audit derivations 153 and 154. The link still needs its actual
ray-data construction and packing proof before the generic annulus
factory can be used in the final M28 contradiction.
-/

set_option autoImplicit false

#print axioms PoincareMT.RiemannianMetric.exists_three_points_at_small_edist
#print axioms PoincareMT.M28.exists_point_off_intrinsic_metric_end_ray
#print axioms PoincareMT.M28.intrinsic_metric_rays_differ_near_end
#print axioms PoincareMT.M28.exists_two_distinct_selected_metric_end_rays
#print axioms PoincareMT.M28.chordConeDistance
#print axioms PoincareMT.M28.chordConeDistance_nonneg
#print axioms PoincareMT.M28.chordConeDistance_sq
#print axioms PoincareMT.M28.chordConeDistance_self
#print axioms PoincareMT.M28.chordConeDistance_comm
#print axioms PoincareMT.M28.abs_sub_le_chordConeDistance
#print axioms PoincareMT.M28.mul_le_chordConeDistance
#print axioms PoincareMT.M28.chordConeDistance_le_abs_sub_add_mul
#print axioms PoincareMT.M28.chordConeDistance_dilation_sq
#print axioms PoincareMT.M28.chordConeTriangle_completion
#print axioms PoincareMT.M28.chord_bound_completion
#print axioms PoincareMT.M28.ChordConeAnnulus
#print axioms PoincareMT.M28.chordConeAnnulusTopologicalSpace
#print axioms PoincareMT.M28.chordConeAnnulusMetric
#print axioms PoincareMT.M28.chordConeAnnulus_dist_eq
#print axioms PoincareMT.M28.chordConeAnnulus_compact
#print axioms PoincareMT.M28.chordConeAnnulus_radius_lipschitz
#print axioms PoincareMT.M28.chordConeAnnulus_local_radial_variation
