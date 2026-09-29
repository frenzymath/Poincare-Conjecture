import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Caps.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Checks
import PoincareLib.Topology.Manifold.Schoenflies.CapCore
import PoincareLib.Topology.Manifold.Schoenflies.Checks
import Lean.Util.CollectAxioms

/-! # Recursive audit of the four-model Schoenflies consumer closure -/

#print axioms Poincare.Manifold.SmoothDomain.exists_ball_neighborhood
#print axioms PoincareMT.CapCertificate.exists_euclidean_closed_core_ball_neighborhood

open Lean Elab Command in
run_cmd do
  for name in #[``Poincare.Manifold.SmoothDomain.exists_ball_neighborhood,
      ``PoincareMT.CapCertificate.exists_euclidean_closed_core_ball_neighborhood] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "Nonstandard axiom in Schoenflies consumer {name}: {axioms}"
