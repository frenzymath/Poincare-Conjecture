import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Construction.RawFlow.Asymptotic.AsymptoticCertificate
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.MetricUniqueness.PartialUniqueness
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.RotationInvariance.RotationInvariance

/-!
# Axiom audit for the published lower uniqueness and end inputs

Morgan-Tian Theorem 12.5 and Proposition 12.7, pp. 295-299.
These are the actual imported producer endpoints used by M35.
-/

set_option autoImplicit false

-- This module intentionally audits the imported proof endpoints.
set_option linter.hashCommand false

#print axioms PoincareMT.RepairedStandardCapExistenceData.partial_metric_unique
#print axioms PoincareMT.M35.Uniqueness.rawMaximalAsymptoticProducer
#print axioms PoincareMT.M35.Uniqueness.rawPartialAsymptoticProducer
#print axioms PoincareMT.M34.partialStandardCapFlow_rotation_invariant
#print axioms PoincareMT.M34.partialStandardCapFlow_lifetime_le_one
