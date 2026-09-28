import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.CriticalBall.CriticalBallSpine

/-! Kernel audit for the source-side critical-ball spine consumer. -/

set_option autoImplicit false
set_option linter.hashCommand false

open PoincareMT
open PoincareMT.M28
open PoincareMT.M28.CounterexampleNeckFamily

#print axioms PoincareMT.M28.CounterexampleNeckFamily.criticalBall_access_of_spine
