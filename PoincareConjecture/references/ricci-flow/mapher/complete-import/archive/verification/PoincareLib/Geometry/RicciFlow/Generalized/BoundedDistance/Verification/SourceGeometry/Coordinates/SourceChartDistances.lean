import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Geometry.CanonicalFlowRestriction
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Geometry.FixedCoordinateTerminalCoefficients
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Geometry.CanonicalImageMetric
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Geometry.CanonicalImageDistanceLimit
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Geometry.SourceFinalChartDistanceLimit

/-!
# Direct audits of the actual source-chart distance limit

These declarations restrict the same actual backward flow, read its
source coefficients, and construct curvature-scale original-region
distance convergence. Source: Morgan--Tian pp. 263-265; M28 derivation159.
-/

set_option autoImplicit false

#print axioms PoincareMT.M28.canonicalFlowRestriction
#print axioms PoincareMT.M28.canonicalFlowRestriction_inner
#print axioms PoincareMT.M28.canonicalFlowRestriction_scalar
#print axioms PoincareMT.M28.canonicalFlowRestriction_nonnegative_iff
#print axioms PoincareMT.M28.FixedCoordinateFlowLimit.compact_pullbackCoefficients
#print axioms PoincareMT.M28.FixedCoordinateFlowLimit.compact_coefficient_bounds
#print axioms PoincareMT.M28.canonicalImageMetric
#print axioms PoincareMT.M28.canonicalImageMetric_inner
#print axioms PoincareMT.M28.canonicalImageMetric_originalOpen_edist
#print axioms PoincareMT.M28.exists_canonicalImageMetric_source_distance_limit
#print axioms
  PoincareMT.M28.CounterexampleNeckFamily.exists_source_final_chart_distance_limit_accuracy
