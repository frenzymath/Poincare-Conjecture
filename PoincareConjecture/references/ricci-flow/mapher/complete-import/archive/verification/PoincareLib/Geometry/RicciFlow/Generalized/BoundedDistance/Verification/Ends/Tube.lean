import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Ends.SourceTubeCertificate
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Local.Geometry.LocalReciprocalSign
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.CapGeometry.CapBoundaryEntryProducer
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Local.Geometry.LocalScaleComparison

/-!
# Source tube and orientation audits

Kernel dependencies for the finite source-cylinder construction of
Morgan--Tian Proposition A.19, pp. 507-508, and the Claim 10.4 entry and
orientation producers. The local gluing import closure excludes higher
milestone proofs.
-/

set_option autoImplicit false
-- These commands are the audit's intended output.
set_option linter.hashCommand false

#print axioms PoincareMT.BalancedNeckChain.exists_finite_openCylinderModel_threshold_m28
#print axioms PoincareMT.BalancedNeckChain.exists_finite_tubeCertificate_threshold_m28
#print axioms PoincareMT.M28.exists_source_tube_certificate_threshold
#print axioms PoincareMT.M28.exists_oriented_forward_reciprocal_sign
#print axioms PoincareMT.M28.exists_predecessor_entry_below_cap_graph
