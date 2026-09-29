import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderMiddleCrossing
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.InitialGeometry.SourceInitialGraphIsotopy

/-!
# Direct audits of the actual middle-sphere coordinate construction

Source: Morgan--Tian Claim 10.8, p. 254; M28 derivation 124.
-/

set_option autoImplicit false

#print axioms PoincareMT.OpenCylinderModel.exists_three_isotopic_sphere_coordinates
#print axioms PoincareMT.M28.cylinderSignedHeight_component_half
#print axioms PoincareMT.OpenCylinderModel.exists_middle_sphere_crossing_height
#print axioms PoincareMT.M28.SourceTubeData.initial_graph_isotopic_middle
