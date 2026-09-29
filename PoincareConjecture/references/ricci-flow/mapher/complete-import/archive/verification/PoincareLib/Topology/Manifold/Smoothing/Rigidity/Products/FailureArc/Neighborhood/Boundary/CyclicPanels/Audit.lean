import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Sphere
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the constructed cyclic band and capped sphere. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.CyclicPanels.exists_original_panel_pasting,
      ``PoincareMT.M76.Dehn.Annuli.CyclicPanels.exists_original_cut_strip,
      ``PoincareMT.M76.Dehn.Annuli.CyclicPanels.cut_strip_fibers,
      ``PoincareMT.M76.Dehn.Annuli.CyclicPanels.exists_original_annulus_of_periodic_strip,
      ``PoincareMT.M76.Dehn.Annuli.CyclicPanels.exists_original_eight_panel_annulus,
      ``PoincareMT.M76.Dehn.Annuli.CyclicPanels.exists_original_disk_parameter_of_rim,
      ``PoincareMT.M76.Dehn.Annuli.CyclicPanels.exists_original_capped_annulus_disk,
      ``PoincareMT.M76.Dehn.Annuli.CyclicPanels.nonempty_original_sphere_of_annulus_and_disks,
      ``PoincareMT.M76.Dehn.Annuli.CyclicPanels.nonempty_original_sphere_of_eight_panels] do
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
