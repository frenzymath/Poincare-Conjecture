import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Leaves
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Assembly
import Lean.Util.CollectAxioms

/-! # Recursive axiom audit of the four-model planar construction -/

#print axioms Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Planar.exists_original_or_reflected_planar_family
#print axioms Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Planar.exists_original_ends
#print axioms Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.reflectGeometry
#print axioms Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.reflectData
#print axioms Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Planar.exists_four_model_planar_family
#print axioms Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.saddle_planar_family_leaf

#print axioms Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.saddle_cap_replacement_leaf
#print axioms Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.exists_ball_neighborhood

open Lean Elab Command in
run_cmd do
  for name in #[
      ``Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Planar.exists_four_model_planar_family,
      ``Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.saddle_planar_family_leaf,
      ``Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.exists_ball_neighborhood] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "Nonstandard axiom in four-model saddle assembly {name}: {axioms}"
