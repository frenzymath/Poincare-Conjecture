import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Geometry.SeparatingLimitCover

/-!
# Axiom checks for the connected limit cover

Audit the M25 separation-label and A.19 adapters for Morgan--Tian
Proposition 10.7, pp. 253-254; M28 derivation 121.
-/

set_option autoImplicit false

#print axioms PoincareMT.M28.exists_separating_cover_accuracy
#print axioms PoincareMT.M28.exists_limit_cover_tube_accuracy
