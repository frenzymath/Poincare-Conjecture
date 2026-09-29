import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.CriticalBall.CriticalBallFrontierReachability

/-! Kernel audit for the fixed-tube access implication and the retained
    critical-radius witness fact. -/

set_option autoImplicit false
set_option linter.hashCommand false

#print axioms PoincareMT.M28.CounterexampleNeckFamily.critical_radius_witnesses_eventually_near
#print axioms PoincareMT.M28.CounterexampleNeckFamily.tube_high_eventually_near
#print axioms PoincareMT.M28.CounterexampleNeckFamily.criticalBallFrontierMargin_of_access
