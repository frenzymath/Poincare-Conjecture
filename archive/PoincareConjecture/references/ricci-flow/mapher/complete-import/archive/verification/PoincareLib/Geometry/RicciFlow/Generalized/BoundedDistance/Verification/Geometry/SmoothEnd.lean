import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderComponentModel
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderMiddleModel

/-! Direct axiom audit for smooth end coordinates, MT Claim 10.8, p. 253. -/

set_option autoImplicit false

#print axioms PoincareMT.OpenCylinderModel.exists_isotopic_sphere_model
#print axioms PoincareMT.OpenCylinderModel.exists_model_of_interval_reparametrization
#print axioms PoincareMT.OpenCylinderModel.exists_reflected_model
#print axioms PoincareMT.OpenCylinderModel.exists_positive_tail_model
#print axioms PoincareMT.OpenCylinderModel.exists_oriented_model_of_component
#print axioms Poincare.unitIntervalReparam
#print axioms Poincare.unitIntervalReparam_properties
#print axioms Poincare.unitIntervalReparam_strictMonoOn
#print axioms PoincareMT.OpenCylinderModel.exists_midlevel_model
