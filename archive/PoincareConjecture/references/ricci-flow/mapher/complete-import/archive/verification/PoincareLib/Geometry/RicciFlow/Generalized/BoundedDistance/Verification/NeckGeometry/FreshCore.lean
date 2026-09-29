import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallFreshCapture

/-! Direct axiom audits for the actual fresh-core capture (derivation 116). -/

set_option autoImplicit false

open PoincareMT.M28.CounterexampleNeckFamily

#print axioms normalizedSlice_fresh_core_compact
#print axioms tubeCritical_fresh_core_regular
#print axioms tubeCritical_fresh_core_component
#print axioms exists_retained_fresh_core_capture
#print axioms exists_retained_strong_neck_core_capture_accuracy
