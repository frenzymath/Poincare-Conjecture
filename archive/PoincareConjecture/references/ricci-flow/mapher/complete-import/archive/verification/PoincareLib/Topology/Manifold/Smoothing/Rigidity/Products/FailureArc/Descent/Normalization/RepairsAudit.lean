import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.PlanarPosition
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.RimHomotopy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Composition.RimHomotopy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Composition.Schedule
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Composition.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Cofaces
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Endpoint
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Components.OrdinaryGraph
import Lean.Util.CollectAxioms

/-! Recursive checks for the actual constructions in this directory. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``Geometry.OriginalPLTower.Step.exists_planar_annulus_position_data,
      ``Geometry.OriginalPLTower.MarkedSurfacePositionData.repairPairs_finite,
      ``Geometry.OriginalPLTower.MarkedSurfacePositionData.exists_original_marked_rim_homotopy,
      ``Geometry.OriginalPLTower.MarkedSurfacePositionData.nonempty_marked_interior_exception_repair,
      ``Geometry.OriginalPLTower.FiniteMarkedSurfaceRepairs.nonempty_projected_crossing,
      ``Geometry.OriginalPLTower.FiniteMarkedSurfaceRepairs.endpoint_properties,
      ``Geometry.OriginalPLTower.FiniteMarkedSurfaceRepairs.exists_original_essential_marked_rim,
      ``Geometry.OriginalPLTower.MarkedSurfacePositionData.assemble_finite_marked_repairs,
      ``Geometry.OriginalPLTower.MarkedSurfacePositionData.nonempty_finite_marked_annulus_repairs,
      ``Geometry.OriginalPLTower.MarkedSurfacePositionData.nonempty_marked_annulus_boundary_exception_repair,
      ``Geometry.OriginalPLTower.MarkedSurfacePositionData.exists_annulus_boundary_exception_repair,
      ``Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion.exists_crossed_change_support,
      ``Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion.exists_positive_carrier_crossing,
      ``Geometry.OriginalPLTower.Step.nonempty_planar_annulus_boundary_motion,
      ``Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion.endpoint_properties,
      ``Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion.exists_original_region_homotopy,
      ``Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion.compact_change_support,
      ``Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion.exists_moved_boundary_cofaces,
      ``PoincareMT.M76.Dehn.Annuli.exists_finite_proper_double_graph] do
    let axioms ← collectAxioms root
    let mut pending := #[root]
    let mut seen : NameSet := {}
    let mut admissions : NameSet := {}
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      let some info := env.checked.get.find? name
        | throwError "Cannot inspect {name}"
      if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
        admissions := admissions.insert name
      pending := pending ++ info.getUsedConstantsAsSet.toArray
    unless admissions.isEmpty && axioms.all standard.contains do
      throwError "{root}: admissions {admissions.toArray}; axioms {axioms}"
    logInfo m!"{root}: {seen.size} reachable declarations, no admissions, axioms {axioms}"
