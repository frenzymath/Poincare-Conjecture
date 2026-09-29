import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallFreshNeck

/-! Axiom audits for varying-scale readout and actual positive-side necks (derivation 117). -/

set_option autoImplicit false

open PoincareMT.Proofs.M28.NeckTransfer PoincareMT.M28.CounterexampleNeckFamily

#print axioms NeckGeometryCore.norm_frozen_difference_jet_le_of_scale_error
#print axioms exists_retained_fresh_neck
#print axioms exists_retained_positive_limit_neck_accuracy
