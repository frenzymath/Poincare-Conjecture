import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.NeckGeometry.NeckMinimizerSameLevel

/-! Kernel audit for whole-carrier same-level access along a regional minimum. -/

set_option autoImplicit false
set_option linter.hashCommand false

open PoincareMT
open PoincareMT.M28

#print axioms PoincareMT.M28.exists_neck_minimizer_same_level
