import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.Geometry.OrdinaryNeckVolume

/-! Axiom audits for ordinary-neck volume at its actual scale (derivation 128). -/

set_option autoImplicit false

open PoincareMT.M28

#print axioms ordinary_neck_chart_speed_lower
#print axioms ordinary_neck_chart_density_lower
#print axioms ordinary_neck_center_chart_edist_le
#print axioms ordinary_neck_center_ball_volume_lower
