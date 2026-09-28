import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallRecutDiameter

/-! # Direct audits of actual source regularity, capture and recut diameter -/

set_option autoImplicit false

open PoincareMT.M28.CounterexampleNeckFamily

#print axioms exists_source_positive_bounded_regular_accuracy
#print axioms exists_retained_short_suffix_capture_accuracy
#print axioms exists_retained_positive_distance_bound_accuracy
#print axioms exists_retained_recut_diameter_accuracy
#print axioms PoincareMT.M28.exists_neck_region_center_connector
#print axioms PoincareMT.M28.intrinsicEDist_to_positive_component_le
#print axioms PoincareMT.M28.exists_intrinsicDiameter_bound_of_neck_recut
