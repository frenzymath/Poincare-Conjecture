import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.NeckGeometry.NeckSlabRegularity

/-! Kernel audits for literal source-neck compact-ball regularity. -/

set_option autoImplicit false
-- Printing kernel dependencies is the purpose of this audit module.
set_option linter.hashCommand false

#print axioms PoincareMT.EpsilonNeck.ball_subset_centered_region
#print axioms PoincareMT.EpsilonNeck.precompact_ball_of_axial_margin
#print axioms PoincareMT.EpsilonNeck.mem_regularPoints_of_axial_margin
#print axioms PoincareMT.EpsilonNeck.central_sphere_subset_regularPoints
#print axioms PoincareMT.EpsilonNeck.mem_regularPoints_of_three_quarter
#print axioms PoincareMT.EpsilonNeck.mem_regularPoints_intrinsicOpenMetric_of_axial_margin
#print axioms PoincareMT.EpsilonNeck.mem_regularPoints_intrinsicOpenMetric_of_three_quarter
