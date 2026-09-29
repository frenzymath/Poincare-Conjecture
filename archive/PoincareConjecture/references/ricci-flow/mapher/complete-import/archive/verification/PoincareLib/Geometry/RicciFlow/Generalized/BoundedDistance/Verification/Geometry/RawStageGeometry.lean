import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallRawStage
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Persistence.NeckGeometry.PartialDiffeomorphPullback
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallInitialGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallMetricIdentity

/-!
# Direct axiom audit of the actual raw-stage and neck geometry maps

The statements preserve the guarded source, raw image, actual coordinate
maps and target scalar scale for Proposition 10.7; M28 derivation 102.
-/

set_option autoImplicit false

open PoincareMT.M28 PoincareMT.M28.CounterexampleNeckFamily
open PoincareMT.Proofs.M28.NeckTransfer

#print axioms openSubtypePartialDiffeomorph
#print axioms openSubtypePartialDiffeomorph_source
#print axioms openSubtypePartialDiffeomorph_target
#print axioms openSubtypePartialDiffeomorph_apply
#print axioms regularRawStageDiffeomorph
#print axioms regularRawStageDiffeomorph_source
#print axioms regularRawStageDiffeomorph_apply
#print axioms regularRawStageDiffeomorph_target
#print axioms regularRawStageDiffeomorph_base
#print axioms pullbackNeckGeometry
#print axioms pullbackNeckGeometry_center
#print axioms pullbackNeckGeometry_coordinate_map
#print axioms pullbackNeckGeometry_carrier
#print axioms pullbackNeckGeometry_scale
#print axioms exists_retained_initial_geometry_accuracy
#print axioms intrinsicOpenMetric_pullbackCoefficients
#print axioms tubeCriticalMetric_pullbackCoefficients
