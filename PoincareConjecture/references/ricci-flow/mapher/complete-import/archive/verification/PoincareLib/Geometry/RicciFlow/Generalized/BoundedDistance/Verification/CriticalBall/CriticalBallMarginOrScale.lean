import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.CriticalBall.CriticalBallMarginOrScale

/-! Kernel audit for the corrected critical-ball split. -/

set_option autoImplicit false
set_option linter.hashCommand false

open PoincareMT
open PoincareMT.M28
open PoincareMT.M28.CounterexampleNeckFamily

#print axioms PoincareMT.M28.CounterexampleNeckFamily.scalar_le_of_scale_lower_of_accuracy
#print axioms PoincareMT.M28.CounterexampleNeckFamily.small_scale_budget
#print axioms PoincareMT.M28.CounterexampleNeckFamily.moderate_witness_scalar_bound
#print axioms PoincareMT.M28.CounterexampleNeckFamily.hcurv_on_criticalBall_of_margin_or_scale
