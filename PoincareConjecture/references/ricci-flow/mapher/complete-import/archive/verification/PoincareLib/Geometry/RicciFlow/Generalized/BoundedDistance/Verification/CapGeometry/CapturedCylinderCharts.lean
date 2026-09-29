import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Persistence.NeckGeometry.CapturedCylinderJets
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.FiniteHessian.PullbackTails

/-!
# Direct audit of actual captured charts and finite metric transition jets

These declarations implement the guarded map germs and quantitative
metric-to-Hessian step of Morgan--Tian Proposition 10.7; derivation 104.
-/

set_option autoImplicit false

open PoincareMT.Proofs.M28.NeckTransfer PoincareMT.Proofs.M28.FiniteHessian

#print axioms capturedCylinderMap
#print axioms capturedCylinderCoordinates
#print axioms capturedCylinderChartDomain
#print axioms cylinderNeckChart_mem_carrier
#print axioms capturedCylinderMap_mem_source
#print axioms contMDiffOn_capturedCylinderMap
#print axioms isOpen_capturedCylinderChartDomain
#print axioms zero_mem_capturedCylinderChartDomain
#print axioms contDiffOn_capturedCylinderCoordinates
#print axioms capturedCylinderCoordinates_source_coefficients
#print axioms capturedCylinderCoordinates_limit_coefficients
#print axioms hasUniformJetBoundsAt_fderiv_of_metric_pullback
#print axioms capturedCylinderCoordinates_atlas_regular
#print axioms hasUniformJetBoundsAt_capturedCylinderCoordinates_fderiv
#print axioms exists_bilinear_pullback_error_tail
