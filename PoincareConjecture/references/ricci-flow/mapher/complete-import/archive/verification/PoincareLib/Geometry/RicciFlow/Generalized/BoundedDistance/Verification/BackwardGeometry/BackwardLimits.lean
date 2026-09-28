import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallBackwardProducer

/-!
# Axiom audit for actual local backward limits

The declarations implement the buffered original source family,
its mixed within-jet limits, and the actual Ricci-flow reconstruction
with the retained terminal metric in M28 derivation 76.
-/

set_option autoImplicit false
-- This verification module intentionally prints kernel dependency reports.
set_option linter.hashCommand false

open PoincareMT.M28

#print axioms PoincareMT.RiemannianMetric.pullbackCoefficients_eq_of_eventuallyEq
#print axioms backward_metric_comparison
#print axioms backward_pullback_ellipticity
#print axioms RegularPointedMetricConvergence.tendstoUniformlyOn_chart_coefficients
#print axioms RegularPointedMetricConvergence.exists_eventual_chart_jet_bound
#print axioms RegularPointedMetricConvergence.exists_eventual_chart_ellipticity

open CounterexampleNeckFamily

#print axioms tubeCritical_global_flow_terminal_coefficients
#print axioms CriticalBallBackwardChartData.mk
#print axioms exists_source_criticalBall_backward_chart_data_accuracy
#print axioms exists_source_criticalBall_backward_family_accuracy
#print axioms exists_source_criticalBall_backward_limit_accuracy

open CriticalBallBackwardChartData

#print axioms CriticalBallBackwardChartData.sourceIndex
#print axioms domain
#print axioms domain_open
#print axioms domain_nonempty
#print axioms sourceMap
#print axioms sourceMap_localDiffeomorph
#print axioms sourceMap_mem_ball
#print axioms sourceMap_mem_neck
#print axioms neckMap
#print axioms neckMap_localDiffeomorph
#print axioms parametrization
#print axioms parametrization_apply
#print axioms parametrization_smooth
#print axioms parametrization_invertible
#print axioms common_window
#print axioms sourceFlow
#print axioms terminal_coefficients
#print axioms testSet
#print axioms testSet_compact
#print axioms testSet_subset_domain
#print axioms terminal_jet_bounds
#print axioms terminal_ellipticity
#print axioms evolving_ellipticity
#print axioms mixed_jet_bounds
#print axioms limitDomain
#print axioms limitDomain_open
#print axioms limitDomain_convex
#print axioms limitDomain_nonempty
#print axioms limitDomain_subset_testSet
#print axioms limitDomain_subset_domain
#print axioms exists_backward_coefficient_limit
#print axioms limitNeckMap
#print axioms limitNeckMap_localDiffeomorph
#print axioms limitParametrization
#print axioms limitParametrization_eq
#print axioms limitParametrization_coefficients_eq
#print axioms BackwardChartLimit.mk
#print axioms exists_backward_limit
