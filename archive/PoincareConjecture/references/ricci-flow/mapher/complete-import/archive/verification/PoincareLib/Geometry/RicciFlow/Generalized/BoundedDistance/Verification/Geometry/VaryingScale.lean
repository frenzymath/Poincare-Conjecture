import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.NeckGeometry.SourceFreshCoefficients
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallFreshGeometry

/-! Axiom audits for varying-scale coefficients and captured geometry (derivation 117). -/

set_option autoImplicit false

open PoincareMT.Proofs.M28.FiniteHessian PoincareMT.M28.CounterexampleNeckFamily

#print axioms HasUniformJetBoundsAt.smul_family
#print axioms HasUniformJetBoundsAt.exists_scalar_error_tail
#print axioms normalizedSlice_fresh_coefficient_lower
#print axioms hasUniformJetBoundsAt_normalizedSlice_fresh_coefficients
#print axioms exists_retained_fresh_geometry
