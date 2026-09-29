import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.NeckGeometry.NeckSlabMinimizer

/-! Kernel audits for actual fixed-level shortening and local A.9 tail minima. -/

set_option autoImplicit false
-- Printing kernel dependencies is the purpose of this audit module.
set_option linter.hashCommand false

#print axioms PoincareMT.M28.neckLevelShorteningEpsilon
#print axioms PoincareMT.M28.neckLevelShorteningEpsilon_pos
#print axioms PoincareMT.M28.mem_coordinate_sphere_iff
#print axioms PoincareMT.M28.exists_coordinate_sphere_shortcut
#print axioms PoincareMT.M28.exists_neck_level_excursion_replacement
#print axioms PoincareMT.M28.neckTailRegion
#print axioms PoincareMT.M28.neckTailCompactSet
#print axioms PoincareMT.M28.neckTailCompactSet_compact_subset
#print axioms PoincareMT.M28.mem_neckTailCompactSet_iff
#print axioms PoincareMT.M28.neck_tail_incoming_sphere
#print axioms PoincareMT.M28.exists_neck_tail_minimizer
