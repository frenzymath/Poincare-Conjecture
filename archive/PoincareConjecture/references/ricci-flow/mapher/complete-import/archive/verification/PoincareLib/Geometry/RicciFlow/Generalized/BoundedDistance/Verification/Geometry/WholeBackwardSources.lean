import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Geometry.SourceWholeNeckBackwardPinching

/-!
# Direct audits of the original whole-neighborhood backward source flows

These declarations construct and estimate the original sources and their
fixed-domain pullbacks. They do not assert existence of the limiting flow.
-/

set_option autoImplicit false

namespace PoincareMT.M28.CounterexampleNeckFamily.WholeNeckBackwardData

#print axioms sourceIndex
#print axioms normalization
#print axioms normalization_pos
#print axioms half_window
#print axioms sourceFlow
#print axioms sourceFlow_metric_at_zero
#print axioms sourceFlow_metric_eq_restriction
#print axioms sourceFlow_physical_time_mem
#print axioms fixedDomain
#print axioms epsilon_pos
#print axioms center_mem_fixedDomain
#print axioms criticalMap
#print axioms criticalMap_localDiffeomorph
#print axioms originalMap
#print axioms originalMap_localDiffeomorph
#print axioms originalMap_in_core
#print axioms neckMap
#print axioms neckMap_localDiffeomorph
#print axioms fixedFlow
#print axioms fixedFlow_metric
#print axioms fixedFlow_curvatureTensorNorm
#print axioms fixedFlow_curvatureDerivativeNorm
#print axioms fixedFlow_metric_at_zero_original
#print axioms fixedFlow_metric_at_zero
#print axioms sourceIndex_strictMono
#print axioms normalization_tendsto_atTop
#print axioms originalPoint
#print axioms pinchingError
#print axioms pinchingError_tendsto_zero
#print axioms sourceFlow_plane_lower
#print axioms fixedFlow_plane_lower

end PoincareMT.M28.CounterexampleNeckFamily.WholeNeckBackwardData

namespace PoincareMT.M28.CounterexampleNeckFamily

#print axioms exists_whole_neck_backward_bounds_accuracy

end PoincareMT.M28.CounterexampleNeckFamily

namespace PoincareMT.M28

#print axioms GeneralizedStrongNeck.buffered_global_time_mem_backward
#print axioms GeneralizedStrongNeck.buffered_global_original_map
#print axioms GeneralizedStrongNeck.buffered_global_original_map_smooth
#print axioms GeneralizedStrongNeck.buffered_global_flow_metric_original
#print axioms GeneralizedStrongNeck.buffered_global_flow_scalar_original
#print axioms GeneralizedStrongNeck.buffered_global_flow_curvatureTensor_original
#print axioms GeneralizedStrongNeck.buffered_global_original_point
#print axioms GeneralizedStrongNeck.buffered_global_original_point_time_mem
#print axioms GeneralizedStrongNeck.buffered_global_flow_plane_lower
#print axioms GeneralizedStrongNeck.buffered_global_original_scalar_le_of_curvature_bound
#print axioms GeneralizedStrongNeck.buffered_global_original_negativePart_lt

end PoincareMT.M28
