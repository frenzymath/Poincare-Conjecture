import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Limits.SelectedCurvatureAnnularEmbedding
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Limits.SelectedRayScalarSequence
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Limits.SelectedEndChordData

/-!
# Direct axiom checks for the actual annular and end assembly

Morgan--Tian Proposition 10.29 and Claim 10.31, pp. 262-265;
M28 derivations 158, 159b, 160 and 161c.
-/

set_option autoImplicit false

#print axioms PoincareMT.M28.chordConeDistance_mul
#print axioms PoincareMT.M28.metricEndRayAnnularPoint
#print axioms PoincareMT.M28.metricEndRayAnnularPoint_dist
#print axioms PoincareMT.M28.metricEndRay_annular_scaled_dist_le
#print axioms PoincareMT.M28.exists_finite_metricEndRay_annular_net
#print axioms PoincareMT.M28.eventually_metricEndRay_annular_distortion
#print axioms PoincareMT.M28.exists_selected_annular_approximation_maps
#print axioms Real.exists_strict_scalar_radius_subsequence
#print axioms PoincareMT.M28.exists_selected_ray_scalar_sequence_accuracy
#print axioms PoincareMT.M28.eventually_curvatureScale_radius_mem_Icc
#print axioms PoincareMT.M28.exists_curvatureScale_annular_limit
#print axioms PoincareMT.M28.SelectedCurvatureAnnularEmbeddingStatement
#print axioms PoincareMT.M28.exists_selected_curvatureScale_annular_embedding
#print axioms PoincareMT.M28.SelectedEndChordData
#print axioms PoincareMT.M28.exists_selected_end_chord_data
