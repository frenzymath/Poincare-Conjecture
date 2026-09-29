import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.AnnulusChart
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.GraphChart
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.Compression
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.CompressionPL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.AnnulusFamily
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Reflection.PairChart
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Coordinates.TorusCrossingPatch
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Coordinates.CollarPatch
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Coordinates.CollaredPair
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.TranslationTrack
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.RimLift
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Translations.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.ClopenMotion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.TrackTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.ComponentModel
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.CollaredWindows
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.AnnularLift
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.OriginalModel
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.FromPLTorus
import Lean.Util.CollectAxioms

/-! Recursive admission checks for constructed local boundary coordinates. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.OriginalSurfacePairChart.frontier_iff_of_region_halfspace,
      ``PoincareMT.M76.exists_original_proper_annulus_boundary_chart,
      ``PoincareMT.M76.exists_original_boundary_pair_chart_of_graph,
      ``PoincareMT.M76.exists_common_collar_compression,
      ``PoincareMT.M76.chartwisePL_common_collar_compression,
      ``PoincareMT.M76.PLDomain.exists_original_common_collar_compression,
      ``PoincareMT.M76.continuousOn_commonCollarAttachment,
      ``PoincareMT.M76.PLDomain.exists_original_common_collared_annulus_family,
      ``PoincareMT.M76.exists_doubled_halfspace_open_chart,
      ``PoincareMT.M76.exists_original_boundary_pair_chart_of_halfbox,
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_original_coordinate_crossing_patch,
      ``PoincareMT.M76.exists_original_common_collar_patch,
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_original_collared_pair_with_lower_crossing_chart,
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_finitePL_translation_track,
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_finitePL_embedded_rim_lift,
      ``PoincareMT.M76.UpperTranslation.exists_small_translation_whole_family_charts,
      ``PoincareMT.M76.UpperExtension.exists_clopen_motion_extension,
      ``PoincareMT.M76.exists_finitePL_conjugate_track,
      ``PoincareMT.M76.exists_finitePL_component_in_collar_base,
      ``PoincareMT.M76.PeriodicSquare.exists_original_collared_pair_of_periodic_windows,
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_original_pair_with_translated_upper_rim,
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_finitePL_annulus_rim_lift,
      ``PoincareMT.M76.PLDomain.exists_original_boundary_torus_coordinates,
      ``PoincareMT.M76.PLDomain.exists_original_coordinates_of_PL_torus] do
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
