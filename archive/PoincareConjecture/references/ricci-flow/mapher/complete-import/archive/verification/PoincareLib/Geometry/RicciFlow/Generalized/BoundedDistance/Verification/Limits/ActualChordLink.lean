import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Coordinates.MetricEndRayConeTriangle
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Coordinates.MetricEndRayEndpoint
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Limits.SelectedMetricEndRayData
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Angles.Limits.SelectedEndRayChordLimits

/-!
# Direct axiom checks for the actual chord-link producers

Morgan--Tian Lemmas 10.21-10.22 and Proposition 10.29, pp. 259-263;
M28 derivations 152, 152a, 152b and 152c.
-/

set_option autoImplicit false

#print axioms PoincareMT.M28.MetricEndRay
#print axioms PoincareMT.M28.MetricEndRay.inward
#print axioms PoincareMT.M28.MetricEndRay.inward_metric
#print axioms PoincareMT.M28.MetricEndRay.inward_radius
#print axioms PoincareMT.M28.MetricEndRay.continuousOn_point
#print axioms PoincareMT.M28.MetricEndRay.completion_triangle
#print axioms PoincareMT.M28.MetricEndRay.ofInward
#print axioms PoincareMT.M28.MetricEndRay.ofInward_endpoint
#print axioms PoincareMT.M28.MetricEndRay.SameEndGerm
#print axioms PoincareMT.M28.exists_selected_end_ray_chord_limits
#print axioms PoincareMT.M28.exists_metricEndRay_chord_pseudometric
#print axioms PoincareMT.M28.metricEndRay_chordConeTriangle
#print axioms PoincareMT.M28.MetricEndRay.dist_sq_le_of_chordDefect_le
#print axioms PoincareMT.M28.MetricEndRay.dist_le_chordConeDistance
#print axioms PoincareMT.M28.exists_selected_metricEndRay_at_point
#print axioms PoincareMT.M28.exists_two_distinct_selected_metricEndRay_data
