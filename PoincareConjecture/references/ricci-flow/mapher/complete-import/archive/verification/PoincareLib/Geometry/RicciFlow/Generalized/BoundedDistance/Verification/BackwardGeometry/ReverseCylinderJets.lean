import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Persistence.NeckAnalysis.OrdinaryCoefficientJets
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.FiniteHessian.MetricJets
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderFiniteJets

/-!
# Direct axiom audit of reverse finite cylinder jets

These declarations implement the analytic conversion in Morgan--Tian
Proposition 9.79, pp. 232-234, and Proposition 10.7, p. 253.
See M28 derivations 90 and 100 for the finite-order and norm conventions.
-/

set_option autoImplicit false

#print axioms PoincareMT.Proofs.M28.FiniteHessian.HasUniformJetBoundsAt.add
#print axioms PoincareMT.Proofs.M28.FiniteHessian.HasUniformJetBoundsAt.sum
#print axioms PoincareMT.Proofs.M28.FiniteHessian.HasUniformJetBoundsAt.of_basis
#print axioms PoincareMT.Proofs.M28.FiniteHessian.HasUniformJetBoundsAt.fderiv
#print axioms PoincareMT.Proofs.M28.FiniteHessian.HasUniformJetBoundsAt.inverse_metric
#print axioms PoincareMT.Proofs.M28.FiniteHessian.hasUniformJetBoundsAt_christoffelBilinear
#print axioms PoincareMT.Proofs.M28.NeckAnalysis.cylinder_component_sq_le_jet_error
#print axioms PoincareMT.Proofs.M28.NeckAnalysis.cylinder_component_abs_le_of_jet_error_le_one

open PoincareMT.Proofs.M28.NeckAnalysis

#print axioms hasUniformZeroJetBoundsAt_roundCylinderIteratedDerivative
#print axioms hasUniformJetBoundsAt_fderiv_of_roundCylinderTensorDerivative
#print axioms hasUniformJetBoundsAt_of_roundCylinderJetError
#print axioms hasUniformJetBoundsAt_cylinder_error_of_close
#print axioms iteratedFDeriv_roundCylinderGram_axial
#print axioms exists_bound_roundCylinderGram_jets
#print axioms hasUniformJetBoundsAt_cylinder_coefficients_of_close
#print axioms PoincareMT.M28.tube.hasUniformJetBoundsAt_cylinderNeckCoefficients
