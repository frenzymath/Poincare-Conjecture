import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.CompactStageRegularity

/-!
# Axiom checks for compact-stage regular base components

Audit the actual inverse distance, compact buffer, and uniform stage
producers for Morgan--Tian Theorem 5.6; M28 derivation 122.
-/

set_option autoImplicit false

open PoincareMT.M28 PoincareMT.M28.RegularPointedMetricConvergence

#print axioms inverse_edist_le_intrinsicOpenMetric
#print axioms mem_regularPoints_of_compact_inverse_buffer
#print axioms exists_eventual_compact_stage_regularComponent
