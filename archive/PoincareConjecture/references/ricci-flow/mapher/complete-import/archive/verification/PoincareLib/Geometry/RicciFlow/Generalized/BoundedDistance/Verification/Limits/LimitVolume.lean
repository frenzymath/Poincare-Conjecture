import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallLimitVolume

/-!
# Axiom checks for actual spatial-limit volume

Source: Morgan--Tian Theorem 5.6, pp. 85-87, and Proposition 10.7, p. 253;
M28 derivation 127.
-/

set_option autoImplicit false

#print axioms PoincareMT.M28.volumeMeasure_image_le_of_edist_le
#print axioms PoincareMT.M28.RegularPointedMetricConvergence.volumeMeasure_univ_le_of_source_bound
#print axioms PoincareMT.M28.CounterexampleNeckFamily.exists_criticalBall_limit_volume_bound
