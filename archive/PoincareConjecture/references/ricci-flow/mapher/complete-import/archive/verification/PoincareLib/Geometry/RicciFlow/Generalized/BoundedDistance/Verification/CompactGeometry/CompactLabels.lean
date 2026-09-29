import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallCompactLabels

/-!
# Axiom checks for uniform compact side labels

Audit the compact-envelope and actual source-label producers for
Morgan--Tian Proposition 10.7, pp. 253-254; M28 derivation 119.
-/

set_option autoImplicit false

#print axioms IsCompact.exists_connected_envelope_within
#print axioms IsCompact.eventually_component_mem_iff
#print axioms PoincareMT.M28.CounterexampleNeckFamily.eventually_initial_graph_labels_on_compact
