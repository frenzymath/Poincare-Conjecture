import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Contacts.WholeCharts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryCharts.ProjectedBranches
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryCharts.ProjectedMarks
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.PositionData
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.PositionHomotopy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.ExceptionSchedule
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.PlanarSource
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.PlanarReparametrization
import Lean.Util.CollectAxioms

/-! Recursive checks for the actual constructions in this directory. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``Geometry.OriginalPLTower.Step.nonempty_markedSurfacePositionData,
      ``Geometry.OriginalPLTower.MarkedSurfacePositionData.exists_whole_projected_crossing,
      ``Geometry.OriginalPLTower.MarkedSurfacePositionData.exceptional_pairs_finite,
      ``Geometry.OriginalPLTower.Step.exists_original_annulus_boundary_double_branch_chart,
      ``Geometry.OriginalPLTower.Step.exists_open_boundary_mark_window,
      ``Geometry.OriginalPLTower.MarkedSurfacePositionData.exists_ambient_history,
      ``Geometry.OriginalPLTower.MarkedSurfacePositionData.exists_exception_schedule,
      ``PoincareMT.M76.Dehn.exists_planar_annulus_rim_complexes,
      ``PoincareMT.M76.Dehn.exists_marked_planar_annulus_reparametrization] do
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
