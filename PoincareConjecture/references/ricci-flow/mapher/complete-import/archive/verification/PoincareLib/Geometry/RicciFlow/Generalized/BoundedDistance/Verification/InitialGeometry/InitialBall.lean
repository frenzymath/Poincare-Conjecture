import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Ends.SourceTubeLargeInitialBall
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.GeometryLimit

/-! Kernel audits for the actual initial pair and curvature-conditioned factory. -/

set_option autoImplicit false
-- Printing kernel dependencies is the purpose of this audit module.
set_option linter.hashCommand false

#print axioms PoincareMT.M28.intrinsic_ball_subset_first_two_necks
#print axioms PoincareMT.M28.exists_initial_pair_scalar_accuracy
#print axioms PoincareMT.M28.SourceTubeData.node_zero_readout
#print axioms PoincareMT.M28.SourceTubeData.tube_chain_readout
#print axioms PoincareMT.M28.SourceTubeData.initial_pair
#print axioms PoincareMT.M28.CounterexampleNeckFamily.tubeNodeScale_zero
#print axioms PoincareMT.M28.exists_source_tube_successor_accuracy
#print axioms PoincareMT.M28.exists_source_tube_large_initial_bound_accuracy
#print axioms PoincareMT.M28.exists_actual_source_tube_large_critical_radius_accuracy
#print axioms PoincareMT.M28.exists_uniform_regular_normal_charts
#print axioms PoincareMT.M28.exists_uniform_regular_normal_cover
#print axioms PoincareMT.M28.exists_regular_metric_limit_of_geometry
