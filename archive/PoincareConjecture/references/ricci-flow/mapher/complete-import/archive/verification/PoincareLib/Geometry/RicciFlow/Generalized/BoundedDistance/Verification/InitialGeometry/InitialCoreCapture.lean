import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallInitialCapture

/-!
# Axiom audit for capture of the actual initial neck core

The enlarged radius belongs to the same retained packet. Compact balls
through the actual nested open metrics place its entire first neck core
in one fixed stage of the retained limit. Morgan--Tian Proposition 10.7,
p. 253; M28 derivation 87.
-/

set_option autoImplicit false
-- This verification module intentionally prints kernel dependency reports.
set_option linter.hashCommand false

open PoincareMT.M28

#print axioms intrinsicOpenMetric_isCompact_closure_ball
#print axioms nested_intrinsicOpenMetric_isCompact_closure_ball

open CounterexampleNeckFamily

#print axioms exists_retained_criticalBall_large_radius_accuracy
#print axioms normalizedSlice_low_neck_ball_at
#print axioms normalizedSlice_low_neck_core_compact
#print axioms tubeCritical_initial_neck_core_regular
#print axioms tubeCritical_initial_neck_core_component
#print axioms exists_retained_initial_neck_capture_accuracy
