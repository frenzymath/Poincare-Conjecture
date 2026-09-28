import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Limits.SourceActualTube

/-! Kernel audits for the actual selected list, balanced chain and tube. -/

set_option autoImplicit false
-- Kernel dependency output is the intended content of this audit.
set_option linter.hashCommand false

#print axioms List.exists_consistent_lift
#print axioms PoincareMT.M28.source_edge_orientations_agree
#print axioms PoincareMT.M28.exists_source_oriented_list_accuracy
#print axioms PoincareMT.M28.SourceOrientedList.active
#print axioms PoincareMT.M28.SourceOrientedList.node
#print axioms PoincareMT.M28.SourceOrientedList.active_nonempty
#print axioms PoincareMT.M28.SourceOrientedList.toNat_lt_length
#print axioms PoincareMT.M28.SourceOrientedList.node_eq_getElem
#print axioms PoincareMT.M28.SourceOrientedList.node_mem
#print axioms PoincareMT.M28.SourceOrientedList.node_time_mem
#print axioms PoincareMT.M28.SourceOrientedList.node_provenance
#print axioms PoincareMT.M28.SourceOrientedList.node_epsilon
#print axioms PoincareMT.M28.SourceOrientedList.node_center
#print axioms PoincareMT.M28.SourceOrientedList.node_time_lt
#print axioms PoincareMT.M28.SourceOrientedList.node_edge
#print axioms PoincareMT.M28.SourceOrientedList.neckOfList_eq_node
#print axioms PoincareMT.M28.intrinsicEDist_self_of_mem
#print axioms PoincareMT.M28.SourceEdgeCommonOrientationPacket.center_ne_later_center
#print axioms PoincareMT.M28.exists_literal_source_balanced_chain_of_edge_packets
#print axioms PoincareMT.M28.exists_actual_source_balanced_chain_accuracy
#print axioms PoincareMT.M28.exists_actual_source_tube_accuracy
