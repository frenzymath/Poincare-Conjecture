import MorganTianLib.Ch05.ClosedBallStageBridge

/-!
# Morgan--Tian Chapter 5: cross-radius stage embeddings

When two compact stages cover closed balls of different radii in the completed
common ambient, the canonical nested-ball inclusion can be transported through
the stage equivalences.  This gives an explicit based isometric embedding,
without treating an embedding of a smaller ball as an isomorphism onto the
larger ball.  Coverage and all radius inequalities remain visible hypotheses.
-/

open Set Metric

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** The canonical inclusion of two centered closed balls in the
completed common ambient. -/
def completedLimitClosedBallInclusion
    (S : CompatiblePointedCompactSystem.{u}) {r s : Real} (hrs : r <= s) :
    Metric.closedBall S.completedLimit.base r ->
      Metric.closedBall S.completedLimit.base s :=
  fun x => ⟨x, le_trans x.property hrs⟩

/-- **Math.** The centered closed-ball inclusion is an isometry. -/
theorem completedLimitClosedBallInclusion_isometry
    (S : CompatiblePointedCompactSystem.{u}) {r s : Real} (hrs : r <= s) :
    Isometry (S.completedLimitClosedBallInclusion hrs) := by
  intro x y
  rfl

/-- **Math.** The centered closed-ball inclusion preserves the marked point. -/
theorem completedLimitClosedBallInclusion_base
    (S : CompatiblePointedCompactSystem.{u}) {r s : Real}
    (hr : 0 <= r) (hs : 0 <= s) (hrs : r <= s) :
    S.completedLimitClosedBallInclusion hrs
        ⟨S.completedLimit.base, Metric.mem_closedBall_self hr⟩ =
      ⟨S.completedLimit.base, Metric.mem_closedBall_self hs⟩ := by
  apply Subtype.ext
  rfl

/-- **Math.** Transport the canonical nested closed-ball inclusion through two
covered compact stages.  The result is an isometric embedding from the
radius-`r` closed ball in stage `n` to the radius-`s` closed ball in stage `m`.
-/
noncomputable def crossRadiusClosedBallEmbedding
    (S : CompatiblePointedCompactSystem.{u})
    (n m : Nat) (r s : Real) (_hr : 0 <= r) (_hs : 0 <= s) (hrs : r <= s)
    (hcover_n : Metric.closedBall S.completedLimit.base r <=
      Set.range (S.stageEmbedding n))
    (hcover_m : Metric.closedBall S.completedLimit.base s <=
      Set.range (S.stageEmbedding m)) :
    Metric.closedBall (S.stage n).base r ->
      Metric.closedBall (S.stage m).base s :=
  (S.stageClosedBallEquiv_of_coverage m s hcover_m).symm ∘
    S.completedLimitClosedBallInclusion hrs ∘
      S.stageClosedBallEquiv_of_coverage n r hcover_n

/-- **Math.** The transported cross-radius map is an isometry. -/
theorem crossRadiusClosedBallEmbedding_isometry
    (S : CompatiblePointedCompactSystem.{u})
    (n m : Nat) (r s : Real) (hr : 0 <= r) (hs : 0 <= s) (hrs : r <= s)
    (hcover_n : Metric.closedBall S.completedLimit.base r <=
      Set.range (S.stageEmbedding n))
    (hcover_m : Metric.closedBall S.completedLimit.base s <=
      Set.range (S.stageEmbedding m)) :
    Isometry (S.crossRadiusClosedBallEmbedding n m r s hr hs hrs hcover_n
      hcover_m) := by
  exact (S.stageClosedBallEquiv_of_coverage m s hcover_m).symm.isometry.comp
    ((S.completedLimitClosedBallInclusion_isometry hrs).comp
      (S.stageClosedBallEquiv_of_coverage n r hcover_n).isometry)

/-- **Math.** The transported cross-radius map preserves the distinguished
closed-ball basepoints. -/
theorem crossRadiusClosedBallEmbedding_base
    (S : CompatiblePointedCompactSystem.{u})
    (n m : Nat) (r s : Real) (hr : 0 <= r) (hs : 0 <= s) (hrs : r <= s)
    (hcover_n : Metric.closedBall S.completedLimit.base r <=
      Set.range (S.stageEmbedding n))
    (hcover_m : Metric.closedBall S.completedLimit.base s <=
      Set.range (S.stageEmbedding m)) :
    S.crossRadiusClosedBallEmbedding n m r s hr hs hrs hcover_n hcover_m
        ⟨(S.stage n).base, Metric.mem_closedBall_self hr⟩ =
      ⟨(S.stage m).base, Metric.mem_closedBall_self hs⟩ := by
  let eₙ := S.stageClosedBallEquiv_of_coverage n r hcover_n
  let eₘ := S.stageClosedBallEquiv_of_coverage m s hcover_m
  let bᵣ : Metric.closedBall S.completedLimit.base r :=
    ⟨S.completedLimit.base, Metric.mem_closedBall_self hr⟩
  let bₛ : Metric.closedBall S.completedLimit.base s :=
    ⟨S.completedLimit.base, Metric.mem_closedBall_self hs⟩
  have heₙ : eₙ ⟨(S.stage n).base, Metric.mem_closedBall_self hr⟩ = bᵣ := by
    simpa [eₙ, bᵣ] using
      (S.stageClosedBallEquiv_of_coverage_base n r hr hcover_n)
  have hinc : S.completedLimitClosedBallInclusion hrs bᵣ = bₛ := by
    simpa [bᵣ, bₛ] using
      (S.completedLimitClosedBallInclusion_base hr hs hrs)
  have heₘ : eₘ.symm bₛ = ⟨(S.stage m).base,
      Metric.mem_closedBall_self hs⟩ := by
    apply eₘ.injective
    calc
      eₘ (eₘ.symm bₛ) = bₛ := eₘ.apply_symm_apply _
      _ = eₘ ⟨(S.stage m).base, Metric.mem_closedBall_self hs⟩ := by
        simpa [eₘ] using
          (S.stageClosedBallEquiv_of_coverage_base m s hs hcover_m).symm
  apply Subtype.ext
  have hsub :
      eₘ.symm
          (S.completedLimitClosedBallInclusion hrs
            (eₙ ⟨(S.stage n).base, Metric.mem_closedBall_self hr⟩)) =
        ⟨(S.stage m).base, Metric.mem_closedBall_self hs⟩ := by
    rw [heₙ, hinc, heₘ]
  have hval := congrArg Subtype.val hsub
  simpa [crossRadiusClosedBallEmbedding, eₙ, eₘ,
    completedLimitClosedBallInclusion, Function.comp_apply, bᵣ, bₛ] using hval

/-- **Math.** The cross-radius map commutes with the completed-limit stage
embeddings.  Thus it is the concrete finite-radius transition seen in the
common ambient, rather than merely an abstract isometric copy. -/
theorem crossRadiusClosedBallEmbedding_commutes
    (S : CompatiblePointedCompactSystem.{u})
    (n m : Nat) (r s : Real) (hr : 0 <= r) (hs : 0 <= s) (hrs : r <= s)
    (hcover_n : Metric.closedBall S.completedLimit.base r <=
      Set.range (S.stageEmbedding n))
    (hcover_m : Metric.closedBall S.completedLimit.base s <=
      Set.range (S.stageEmbedding m))
    (x : Metric.closedBall (S.stage n).base r) :
    S.stageEmbedding m
        (S.crossRadiusClosedBallEmbedding n m r s hr hs hrs hcover_n hcover_m x) =
      S.stageEmbedding n x := by
  let eₙ := S.stageClosedBallEquiv_of_coverage n r hcover_n
  let eₘ := S.stageClosedBallEquiv_of_coverage m s hcover_m
  let i := S.completedLimitClosedBallInclusion hrs
  have hcancel := eₘ.apply_symm_apply (i (eₙ x))
  have hval := congrArg Subtype.val hcancel
  exact hval

/-- **Math.** Cross-radius embeddings satisfy the expected three-radius
coherence law.  The equality is proved in the completed ambient, so proof
arguments for the coverage witnesses do not affect the resulting map. -/
theorem crossRadiusClosedBallEmbedding_comp
    (S : CompatiblePointedCompactSystem.{u})
    (n m l : Nat) (r s t : Real)
    (hr : 0 <= r) (hs : 0 <= s) (ht : 0 <= t)
    (hrs : r <= s) (hst : s <= t) (hrt : r <= t)
    (hcover_n : Metric.closedBall S.completedLimit.base r <=
      Set.range (S.stageEmbedding n))
    (hcover_m : Metric.closedBall S.completedLimit.base s <=
      Set.range (S.stageEmbedding m))
    (hcover_l : Metric.closedBall S.completedLimit.base t <=
      Set.range (S.stageEmbedding l)) :
    S.crossRadiusClosedBallEmbedding m l s t hs ht hst hcover_m hcover_l ∘
        S.crossRadiusClosedBallEmbedding n m r s hr hs hrs hcover_n hcover_m =
      S.crossRadiusClosedBallEmbedding n l r t hr ht hrt hcover_n hcover_l := by
  funext x
  apply Subtype.ext
  apply (S.stageEmbedding_isometry l).injective
  calc
    S.stageEmbedding l
        ((S.crossRadiusClosedBallEmbedding m l s t hs ht hst hcover_m hcover_l)
          (S.crossRadiusClosedBallEmbedding n m r s hr hs hrs hcover_n hcover_m x)) =
        S.stageEmbedding m
          (S.crossRadiusClosedBallEmbedding n m r s hr hs hrs hcover_n hcover_m x) :=
      S.crossRadiusClosedBallEmbedding_commutes m l s t hs ht hst hcover_m
        hcover_l _
    _ = S.stageEmbedding n x :=
      S.crossRadiusClosedBallEmbedding_commutes n m r s hr hs hrs hcover_n
        hcover_m x
    _ = S.stageEmbedding l
        (S.crossRadiusClosedBallEmbedding n l r t hr ht hrt hcover_n hcover_l x) :=
      (S.crossRadiusClosedBallEmbedding_commutes n l r t hr ht hrt hcover_n
        hcover_l x).symm

end CompatiblePointedCompactSystem

end MorganTianLib

#print axioms MorganTianLib.CompatiblePointedCompactSystem.completedLimitClosedBallInclusion_isometry
#print axioms MorganTianLib.CompatiblePointedCompactSystem.crossRadiusClosedBallEmbedding_isometry
#print axioms MorganTianLib.CompatiblePointedCompactSystem.crossRadiusClosedBallEmbedding_base
#print axioms MorganTianLib.CompatiblePointedCompactSystem.crossRadiusClosedBallEmbedding_commutes
#print axioms MorganTianLib.CompatiblePointedCompactSystem.crossRadiusClosedBallEmbedding_comp
