import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.UniformCompactScalar
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallCompactScalar

/-!
# Axiom checks for actual compact scalar control

Audit the uniform two-jet, chart and compact scalar producers for
Morgan--Tian Theorem 5.6 and Claim 10.8; M28 derivation 118.
-/

set_option autoImplicit false

open PoincareMT.M28.CounterexampleNeckFamily

#print axioms exists_eventual_compact_normalized_raw_scalar_bound

open PoincareMT.M28.RegularPointedMetricConvergence

#print axioms PoincareMT.M28.tendstoUniformlyOn_metricTwoJet_of_uniform_bilinear_jets
#print axioms PoincareMT.M28.tendstoUniformlyOn_jetScalarCurvature_of_metricTwoJet
#print axioms jetScalarCurvature_chart_eq_of_mem_exhaustion
#print axioms tendstoUniformlyOn_chart_scalarCurvature
#print axioms tendstoUniformlyOn_scalarCurvature
#print axioms exists_eventual_compact_scalar_bound
