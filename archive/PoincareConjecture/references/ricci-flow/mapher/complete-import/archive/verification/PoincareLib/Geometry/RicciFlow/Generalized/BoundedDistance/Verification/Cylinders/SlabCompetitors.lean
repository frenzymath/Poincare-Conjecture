import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Geometry.ThreeQuarterSlabCompetitors

/-!
# Axiom checks for the original neck's closed-slab competitors

Audit the actual distance ceiling and the neck-valued C1 path producer
for Morgan--Tian Claim 10.8; M28 derivation 115.
-/

set_option autoImplicit false

#print axioms PoincareMT.EpsilonNeck.intrinsicEDist_lt_three_quarter_ceiling
#print axioms PoincareMT.EpsilonNeck.exists_three_quarter_slab_competitor
