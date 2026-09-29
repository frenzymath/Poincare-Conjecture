import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Limits.SelectedChordCompactness

/-!
# Direct audits of the actual compact chord-link construction

Morgan--Tian Proposition 10.29, pp. 262-263; M28 derivation 155.
-/

set_option autoImplicit false

#print axioms UniformSpace.Completion.radius_le_dist_of_precompact_ball
#print axioms UniformSpace.Completion.compactSpace_of_totallyBounded_univ
#print axioms Metric.totallyBounded_univ_of_finite_pair_collision
#print axioms PoincareMT.M28.neck_completion_radius_lower
#print axioms PoincareMT.M28.exists_completion_radius_threshold_for_cylinder_height
#print axioms PoincareMT.M28.cylinder_height_ge_threeQuarter_of_radius_barrier
#print axioms PoincareMT.M28.exists_inward_ray_crossing_selected_sphere
#print axioms PoincareMT.M28.exists_standardSphere_small_path_cover
#print axioms PoincareMT.M28.exists_central_sphere_packing_number
#print axioms PoincareMT.M28.exists_cofinal_selected_neck_sequence
#print axioms PoincareMT.M28.totallyBounded_selected_end_ray_chord
#print axioms PoincareMT.M28.exists_compact_selected_end_chord_link
