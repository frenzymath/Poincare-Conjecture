import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Ends.SourceTubeIntersectingSlab

/-!
# Axiom checks for the intersecting-sphere source radius estimate

Source: Morgan--Tian Claim 10.8, p. 254; M28 derivation 124.
-/

set_option autoImplicit false

#print axioms PoincareMT.M28.SourceTubeData.intrinsicEDist_lt_of_initial_graph_intersection
#print axioms PoincareMT.M28.CounterexampleNeckFamily.tube_distance_lt_of_initial_graph_intersection
