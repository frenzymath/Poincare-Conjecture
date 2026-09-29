import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Ends.SourceTubeFreshSlab
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallFreshSlab
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.NeckGeometry.SourceFreshSphereIsotopy

/-!
# Axiom checks for whole fresh-slab tube containment

Audit the pre-exit remainder, initial-graph barrier and actual fresh
closed-slab producers for Morgan--Tian Claim 10.8; M28 derivation 115.
-/

set_option autoImplicit false

open PoincareMT.M28.SourceTubeData

#print axioms ContinuousOn.exists_prefix_in_remainder_of_exit
#print axioms short_path_mapsTo_of_terminal_avoidance
#print axioms exists_central_slab_competitor_in_tube
#print axioms exists_fresh_slab_competitor_in_tube
#print axioms fresh_three_quarter_slab_subset
#print axioms PoincareMT.M28.CounterexampleNeckFamily.exists_retained_fresh_slab_accuracy
#print axioms PoincareMT.M28.exists_source_fresh_sphere_isotopy_accuracy
