import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.PositiveEnds.PositiveEndRecutModel
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.PositiveEnds.PositiveEndOrientation
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.NeckGeometry.NeckRecutScalarModel

/-! Direct axiom audits for the literal recut in MT Claim 10.8, p. 254. -/

set_option autoImplicit false

#print axioms PoincareMT.EpsilonNeck.closure_region_eq_coordinate_slab
#print axioms PoincareMT.EpsilonNeck.recut_positive_component
#print axioms PoincareMT.EpsilonNeck.exists_orientation_into_component
#print axioms PoincareMT.M28.exists_positive_recut_model
#print axioms PoincareMT.M28.exists_neck_recut_scalar_model_accuracy
