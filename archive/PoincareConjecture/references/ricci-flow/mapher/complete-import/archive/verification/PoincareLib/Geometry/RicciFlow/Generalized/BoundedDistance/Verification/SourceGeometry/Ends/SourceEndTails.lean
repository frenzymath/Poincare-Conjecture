import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Ends.SourceTubeEndTails
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Ends.SourceTubeSharpScalar
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Ends.SourceTubeTerminalScalar

/-!
# Axiom audit of retained source end-tail controls

The compact middle, literal end tails, sharp scalar and scale bounds,
and terminal-neck exclusion use the actual source data.
Morgan--Tian Claim 10.8, p. 254; M28 derivation 89.
-/

set_option autoImplicit false
-- This verification module intentionally prints kernel dependency reports.
set_option linter.hashCommand false

open PoincareMT.M28

#print axioms SourceTubeData.coreUnion
#print axioms SourceTubeData.coreUnion_compact_subset
#print axioms SourceTubeData.subset_coreUnion_end_tails
#print axioms SourceTubeData.frontier_subset_end_tail_closures
#print axioms SourceTubeData.node_last_readout

open CounterexampleNeckFamily

#print axioms exists_source_tube_sharp_scalar_accuracy
#print axioms exists_source_tube_fresh_scale_accuracy
#print axioms exists_source_terminal_neck_scalar_accuracy
#print axioms exists_source_terminal_neck_exclusion_accuracy
