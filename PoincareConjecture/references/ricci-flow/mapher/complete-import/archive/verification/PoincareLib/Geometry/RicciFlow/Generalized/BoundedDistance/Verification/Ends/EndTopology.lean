import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.InitialGeometry.SourceInitialSideNoncompact
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Limits.SelectedPositiveSection
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.PositiveEnds.PositiveAmbientComponent

/-! Direct audits for the actual initial-side exclusion and selected
ambient cylinder half in M28 derivations 94 and 120. -/

set_option autoImplicit false

#print axioms Poincare.not_isCompact_closure_of_open_height
#print axioms PoincareMT.M28.CounterexampleNeckFamily.not_isCompact_closure_retained_initial_side
#print axioms PoincareMT.M28.exists_high_selected_neck_inside_accuracy
#print axioms PoincareMT.M28.exists_neck_component_inside_of_compl_preconnected
#print axioms PoincareMT.M28.exists_positive_ambient_cylinder_half
