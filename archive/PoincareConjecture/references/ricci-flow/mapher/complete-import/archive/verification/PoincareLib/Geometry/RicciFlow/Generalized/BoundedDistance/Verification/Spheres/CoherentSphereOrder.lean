import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Spheres.CoherentSphereOrder
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Paths.PathCrossingDistance
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Geometry.SourceMatchingHighNeck

/-!
# Axiom checks for the coherent three-sphere order

Audit the fixed-coordinate pair adapter and the actual connected-set
sign argument for Morgan--Tian Claim 10.8; M28 derivation 123.
-/

set_option autoImplicit false

open PoincareMT.M28.CounterexampleNeckFamily

#print axioms PoincareMT.M28.cylinderSignedHeight_opposite_order
#print axioms PoincareMT.M28.cylinderSignedHeight_middle_signs
#print axioms PoincareMT.RiemannianMetric.edist_add_le_of_path_crossing
#print axioms exists_matching_high_neck_scalar_accuracy
#print axioms exists_matching_high_neck_compact_exclusion_accuracy
