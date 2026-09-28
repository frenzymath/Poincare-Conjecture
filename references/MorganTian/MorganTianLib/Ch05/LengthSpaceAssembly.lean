import MorganTianLib.Ch05.RadialFiniteConfiguration
import MorganTianLib.Ch05.ConnectedAssembly

/-!
# Morgan--Tian Chapter 5: length-space assembly

The completed inductive-limit ambient is a metric completion of compatible
compact stages.  Once radial coverage is supplied, every finite configuration
lies in one stage, so the stage length-space arcs can be pushed into the
completion.  This file records that metric-to-length bridge explicitly.
-/

open Set Metric Topology
open scoped unitInterval

noncomputable section

namespace MorganTianLib

universe u

private theorem eVariationOn_comp_isometry
    {α : Type*} {X Y : Type u} [LinearOrder α]
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (f : X → Y) (hf : Isometry f) (γ : α → X) :
    eVariationOn (f ∘ γ) Set.univ = eVariationOn γ Set.univ := by
  unfold eVariationOn
  apply iSup_congr
  intro p
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.comp_apply, Function.comp_apply]
  rw [hf.edist_eq]

namespace CompatiblePointedCompactSystem

/-- **Math.** Radial coverage and length-space stages make the completed common
ambient a length space.  Every pair of points is first captured in one compact
stage, then a distance-realizing stage path is pushed through the stage
isometric embedding into the completion. -/
theorem lengthSpace_completedLimit_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (hlength : ∀ n, LengthSpace (S.stage n).carrier) :
    LengthSpace S.completedLimit.carrier := by
  letI : ConnectedSpace S.completedLimit.carrier :=
    S.connectedSpace_completedLimit (fun n => (hlength n).toConnectedSpace)
  refine {
    exists_rectifiable_arc := ?_
  }
  intro x y
  obtain ⟨n, x', y', hx', hy'⟩ :=
    S.exists_common_stageEmbedding_eq_of_radial_stage_coverage hcover x y
  letI : LengthSpace (S.stage n).carrier := hlength n
  obtain ⟨γ, hγvar, hγdist⟩ :=
    LengthSpace.exists_path_realizing_dist (S.stage n).carrier x' y'
  let f : (S.stage n).carrier → S.completedLimit.carrier :=
    S.stageEmbedding n
  let γ' : Path x y :=
    (γ.map (S.stageEmbedding_isometry n).continuous).cast hx'.symm hy'.symm
  refine ⟨γ', ?_, ?_⟩
  · have hvar := hγvar
    have hcomp :
        BoundedVariationOn (f ∘ (γ : I → (S.stage n).carrier)) Set.univ := by
      exact (S.stageEmbedding_isometry n).lipschitz.lipschitzOnWith
        |>.comp_boundedVariationOn (mapsTo_univ _ _) hvar
    simpa [γ', f, Path.cast, Path.map, Path.map'] using hcomp
  · have heq := eVariationOn_comp_isometry f
      (S.stageEmbedding_isometry n) (γ : I → (S.stage n).carrier)
    have hdist :
        dist x y = dist x' y' := by
      rw [← hx', ← hy']
      exact (S.stageEmbedding_isometry n).dist_eq _ _
    rw [show (γ' : I → S.completedLimit.carrier) =
        f ∘ (γ : I → (S.stage n).carrier) by
          simp [γ', f, Path.cast, Path.map, Path.map']]
    rw [heq]
    rw [hγdist, hdist]

end CompatiblePointedCompactSystem

end MorganTianLib

end

#print axioms MorganTianLib.CompatiblePointedCompactSystem.lengthSpace_completedLimit_of_radial_stage_coverage
