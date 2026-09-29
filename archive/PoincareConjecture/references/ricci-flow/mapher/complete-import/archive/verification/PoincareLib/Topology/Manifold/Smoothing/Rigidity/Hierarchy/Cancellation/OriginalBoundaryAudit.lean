import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.OriginalSpanningPair
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.OriginalCoordinatePair
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.SelectedSpanningPair
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.InstalledFrontierCovering
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.ChartRange
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Recognition.FiniteModelTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Recognition.OriginalCollar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.MinimalPhaseSquareMaps
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.FirstFrontierCoverings
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.OriginalFailureComponents
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.OriginalPeriodicProduct
import Lean.Util.CollectAxioms

/-! Recursive audit of original boundary recognition, annuli, and installed covering. -/

set_option autoImplicit false

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.PLDomain.exists_original_spanning_pair_of_incompressible_boundary,
    ``PoincareMT.M76.PLDomain.exists_original_coordinate_pair_of_incompressible_boundary,
    ``PoincareMT.M76.PLDomain.exists_original_coordinate_pair_with_finite_realization,
    ``PoincareMT.M76.exists_hamiltonZero_selected_component_spanning_pair,
    ``PoincareMT.M76.PLDomain.nonempty_sourceSquareMap_of_original_component_model,
    ``PoincareMT.M76.PLDomain.exists_square_maps_on_original_phase_collar,
    ``PoincareMT.M76.exists_hamiltonZero_minimal_phase_square_maps,
    ``PoincareMT.M76.exists_hamiltonZero_minimal_installed_phase_products,
    ``PoincareMT.M76.exists_hamiltonZero_rigidity_or_original_failure_components,
    ``PoincareMT.M76.not_hamiltonZero_boundary_failure_of_marked_product_data,
    ``PoincareMT.M76.isCoveringMap_hamiltonZero_frontier_of_installed_collar,
    ``PoincareMT.M76.isCoveringMap_hamiltonZero_first_frontiers_of_installed_products,
    ``PoincareMT.M76.ChartwisePLHomeomorph.of_range_source]
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut admissions : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Cannot inspect {name}"
    match info with
    | .axiomInfo _ =>
        unless standard.contains name do admissions := admissions.insert name
    | _ => pure ()
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
      admissions := admissions.insert name
    pending := pending ++ info.getUsedConstantsAsSet.toArray
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"{root}: {axioms}"
    unless axioms.all standard.contains do
      throwError "Nonstandard axioms in {root}"
  logInfo m!"Original boundary constructions: {seen.size} declarations; admissions: {admissions.toArray}"
  unless admissions.isEmpty do
    throwError "Original boundary constructions have an unproved dependency"
