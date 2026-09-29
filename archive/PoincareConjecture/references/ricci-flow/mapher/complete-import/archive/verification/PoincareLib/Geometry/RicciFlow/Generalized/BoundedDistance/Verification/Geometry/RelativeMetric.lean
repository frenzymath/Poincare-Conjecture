import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.RelativeCompactMetric

/-!
# Axiom checks for actual compact relative metric control

Audit the bilinear, chart and intrinsic comparison producers for
Morgan--Tian Theorem 5.6; M28 derivations 116 and 118.
-/

set_option autoImplicit false

open PoincareMT.M28.RegularPointedMetricConvergence

#print axioms ContinuousLinearMap.relative_quadratic_bounds_of_norm_sub_le
#print axioms PoincareMT.RiemannianMetric.relative_inner_bounds_of_chart
#print axioms eventually_chart_relative_inner_bounds
#print axioms eventually_compact_relative_inner_bounds
