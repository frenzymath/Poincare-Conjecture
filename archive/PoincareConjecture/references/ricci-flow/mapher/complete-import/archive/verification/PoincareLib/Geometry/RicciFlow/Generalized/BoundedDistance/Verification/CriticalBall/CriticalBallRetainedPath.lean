import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.CriticalBall.CriticalBallRetainedPath

/-! Kernel audit for the retained-path transport into the normalized tube. -/

set_option autoImplicit false
set_option linter.hashCommand false

open PoincareMT
open PoincareMT.M28
open PoincareMT.M28.CounterexampleNeckFamily

#print axioms
  PoincareMT.M28.CounterexampleNeckFamily.exists_retained_path_minimizing_in_tube_accuracy
#print axioms
  PoincareMT.M28.CounterexampleNeckFamily.retained_path_base_distance_eq_length
