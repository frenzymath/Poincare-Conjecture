import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.CriticalBall.CriticalBallCurvature

/-! Kernel audit for the critical-ball curvature interface. -/

set_option autoImplicit false
set_option linter.hashCommand false

open PoincareMT
open PoincareMT.M28
open PoincareMT.M28.CounterexampleNeckFamily

#print axioms CounterexampleNeckFamily.eventually_scalar_le_on_critical_regularComponent
#print axioms PoincareMT.M28.CounterexampleNeckFamily.hcurv_on_criticalBall
