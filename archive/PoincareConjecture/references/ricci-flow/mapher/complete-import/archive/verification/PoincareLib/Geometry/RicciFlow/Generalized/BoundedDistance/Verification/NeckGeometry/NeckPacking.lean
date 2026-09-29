import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.NeckGeometry.NeckCoverEnd

/-! Direct audits for actual neck-cover packing and proper-end scalar
divergence in M28 derivation 128. -/

set_option autoImplicit false

#print axioms PoincareMT.M28.exists_compact_bounded_scalar_neck_cover
#print axioms PoincareMT.M28.exists_scalar_gt_of_neck_cover_noncompact_closure
#print axioms Poincare.exists_height_tail_disjoint_compact
#print axioms PoincareMT.M28.scalar_diverges_on_proper_neck_cover_end
