import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Limits.SelectedCylinderMetricRays
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Limits.SelectedSphereRadiusBarrier
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.IntrinsicGeometry.IntrinsicEndRayUniqueness
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Limits.SelectedSegmentRayLimits
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Angles.Geometry.MissingEndComparison
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Angles.Geometry.ChordDefectLimits

/-!
# Direct axiom checks for the actual recut rays

Morgan--Tian Claims 10.13-10.14, Corollary 10.15 and Lemmas 10.16/10.21,
pp. 256-259; M28 derivations 135, 138, 145, 147, 151 and 152a.
-/

set_option autoImplicit false

#print axioms PoincareMT.M28.exists_selected_cylinder_metric_rays
#print axioms PoincareMT.M28.completion_radius_le_endpoint_sum_of_metric_segment
#print axioms PoincareMT.M28.exists_selected_sphere_radius_barrier
#print axioms PoincareMT.M28.exists_intrinsic_segment_below_completion_radius_barrier
#print axioms PoincareMT.M28.exists_geodesic_eq_intrinsic_metric_ray_prefix
#print axioms PoincareMT.M28.intrinsic_metric_ray_regular
#print axioms PoincareMT.M28.intrinsic_end_ray_eq_after_interior
#print axioms PoincareMT.M28.exists_geodesic_eq_intrinsic_metric_segment_real
#print axioms PoincareMT.M28.exists_geodesic_eq_intrinsic_unit_metric_segment
#print axioms PoincareMT.M28.exists_smooth_intrinsic_segment_below_completion_radius_barrier
#print axioms PoincareMT.M28.selected_segment_tendsto_shortened_ray
#print axioms PoincareMT.M28.corresponding_side_lower_at_selected_end
#print axioms PoincareMT.M28.chordDefect
#print axioms PoincareMT.M28.chordDefect_bounds
#print axioms PoincareMT.M28.chordDefect_le_of_corresponding_side_lower
#print axioms PoincareMT.M28.exists_joint_chord_limit
#print axioms PoincareMT.M28.exists_chordDefect_limit_of_corresponding_side_lower
#print axioms PoincareMT.M28.chordDefect_le_joint_limit_of_corresponding_side_lower
#print axioms PoincareMT.M28.sqrt_chord_limit_bounds
#print axioms PoincareMT.M28.tendsto_rescaled_distance_of_chordDefect_limit
#print axioms PoincareMT.M28.tendsto_equal_radius_distance_of_chordDefect_limit
