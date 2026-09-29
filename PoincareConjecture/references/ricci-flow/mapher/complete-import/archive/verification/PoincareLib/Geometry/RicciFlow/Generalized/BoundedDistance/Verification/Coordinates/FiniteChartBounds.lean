import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.FiniteChartBounds
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Geometry.CoordinateComposition

/-!
# Direct axiom audit of the finite compact atlas inputs

These declarations supply the fixed chart regions and finite-order common
tail and actual coordinate identities for Morgan--Tian Proposition 10.7,
p. 253; M28 derivations 101 and 103.
-/

set_option autoImplicit false

#print axioms IsCompact.exists_finite_extChart_cover

open PoincareMT.M28.RegularPointedMetricConvergence

#print axioms exists_finite_stage_chart_cover
#print axioms exists_eventual_finite_chart_bounds
#print axioms eventually_finite_chart_jet_error
#print axioms PoincareMT.RiemannianMetric.pullbackCoefficients_comp
#print axioms PoincareMT.RiemannianMetric.pullbackCoefficients_eq_chart_pullback
