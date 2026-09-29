import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Caps.Adapter
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Caps.Replacement
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Leaves
import Lean.Util.CollectAxioms

/-! # Recursive audit of both terminal cap orientations -/

set_option autoImplicit false

namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview

#print axioms TerminalSaddleGeometry.toAccepted
#print axioms TerminalSaddleData.toAccepted
#print axioms saddle_cap_replacement_original
#print axioms Caps.reflectedGeometry
#print axioms Caps.exists_reflectedData
#print axioms Caps.conjugate_replacement
#print axioms Caps.saddle_cap_replacement
#print axioms saddle_cap_replacement_leaf

open Lean Elab Command in
run_cmd do
  for name in #[``Caps.reflectedGeometry, ``Caps.exists_reflectedData,
      ``Caps.conjugate_replacement, ``Caps.saddle_cap_replacement,
      ``saddle_cap_replacement_leaf] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "Nonstandard axiom in four-model cap producer {name}: {axioms}"

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
