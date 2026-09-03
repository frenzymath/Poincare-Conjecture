import MorganTianLib.Ch05.CompatibleBallLimits

/-!
# Morgan--Tian Chapter 5: connected assembly

Connected compact stages remain connected after assembly in the common completed
ambient: consecutive stage images meet at the common mapped basepoint, and their
dense union therefore has connected completion.
-/

open Set Metric Topology

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Connected compact stages assemble into a preconnected dense union
in the completed common ambient. -/
theorem isPreconnected_iUnion_range_stageEmbedding
    (S : CompatiblePointedCompactSystem.{u})
    (hconn : ∀ n, ConnectedSpace (S.stage n).carrier) :
    IsPreconnected (⋃ n : ℕ, Set.range (S.stageEmbedding n)) := by
  apply IsPreconnected.iUnion_of_chain
  · intro n
    letI : ConnectedSpace (S.stage n).carrier := hconn n
    exact (isConnected_range (S.stageEmbedding_isometry n).continuous).isPreconnected
  · intro n
    refine ⟨S.completedLimit.base, ?_, ?_⟩
    · exact ⟨(S.stage n).base, S.stageEmbedding_base n⟩
    · exact ⟨(S.stage (n + 1)).base, S.stageEmbedding_base (n + 1)⟩

/-- **Math.** If every compact stage is connected, then the completed common
ambient is connected. -/
theorem connectedSpace_completedLimit
    (S : CompatiblePointedCompactSystem.{u})
    (hconn : ∀ n, ConnectedSpace (S.stage n).carrier) :
    ConnectedSpace S.completedLimit.carrier := by
  rw [connectedSpace_iff_univ]
  let U : Set S.completedLimit.carrier :=
    ⋃ n : ℕ, Set.range (S.stageEmbedding n)
  have hUpre : IsPreconnected U := by
    exact S.isPreconnected_iUnion_range_stageEmbedding hconn
  have hUnonempty : U.Nonempty := by
    refine ⟨S.completedLimit.base, ?_⟩
    exact mem_iUnion.2 ⟨0, ⟨(S.stage 0).base, S.stageEmbedding_base 0⟩⟩
  have hU : IsConnected U := ⟨hUnonempty, hUpre⟩
  refine hU.subset_closure (s := U) (t := Set.univ) (subset_univ U) ?_
  rw [S.dense_iUnion_range_stageEmbedding.closure_eq]

end CompatiblePointedCompactSystem

end MorganTianLib

#print axioms MorganTianLib.CompatiblePointedCompactSystem.isPreconnected_iUnion_range_stageEmbedding
#print axioms MorganTianLib.CompatiblePointedCompactSystem.connectedSpace_completedLimit
