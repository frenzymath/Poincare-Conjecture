import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Geometry.CenteredNeckRadiusFloor
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Limits.SelectedRayScalarRadius

/-!
# Direct audits of the quantitative scalar-radius estimates

These declarations implement the direct chord-defect route to
Morgan--Tian Claim 10.31, pp. 264-265; M28 derivation 157.
-/

set_option autoImplicit false

#print axioms PoincareMT.M28.exists_positive_rectangle_of_joint_limit
#print axioms PoincareMT.M28.half_mul_radius_sq_le_of_chord_lower
#print axioms PoincareMT.M28.scalar_radius_ratio_le_of_chord_lower
#print axioms PoincareMT.M28.centered_neck_scalar_radius_floor
#print axioms PoincareMT.M28.exists_centered_neck_radius_floor_accuracy
#print axioms PoincareMT.M28.exists_selected_ray_scalar_radius_upper
