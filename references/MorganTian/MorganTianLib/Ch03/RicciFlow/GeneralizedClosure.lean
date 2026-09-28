import MorganTianLib.Ch03.RicciFlow.GeneralizedScaling
import MorganTianLib.Ch03.RicciFlow.GeneralizedEmbeddingClosure

/-!
# Morgan--Tian Ch. 3 - generalized embedding and scaling closure

The compatible-embedding structure stores an embedding only on its declared
source.  Consequently its continuity is a `ContinuousOn` fact on that source,
which is exactly what is needed to extend flow-line uniqueness from an open
slab to a closed slab.  The affine time change also acts by a homeomorphism of
the restricted source, so it preserves the embedding contract.
-/

open scoped ContDiff Manifold Topology
open Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

private def restrictIooForClosure
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t a b : ℝ}
    (e : S.CompatibleTimeSliceEmbedding n C t (Icc a b))
    (ht : t ∈ Ioo a b) :
    S.CompatibleTimeSliceEmbedding n C t (Ioo a b) := by
  let hsub : C ×ˢ Ioo a b ⊆ C ×ˢ Icc a b := by
    rintro ⟨x, s⟩ ⟨hx, hs⟩
    exact ⟨hx, ⟨le_of_lt hs.1, le_of_lt hs.2⟩⟩
  let incl : C ×ˢ Ioo a b → C ×ˢ Icc a b := Set.inclusion hsub
  let hincl : Topology.IsEmbedding incl := Topology.IsEmbedding.inclusion hsub
  have hemb :
      Topology.IsEmbedding (Set.restrict (C ×ˢ Ioo a b) e.toFun) := by
    have hc := e.toCompatibleEmbedding.isEmbedding.comp hincl
    convert hc using 1
    funext z
    rfl
  refine
    { toCompatibleEmbedding :=
        { toFun := e.toFun
          isEmbedding := hemb
          time_eq := ?_
          isIntegralCurveOn := ?_ }
      center_mem := ht
      source_subset := e.source_subset
      center_eq := e.center_eq }
  · intro z hz
    exact e.toCompatibleEmbedding.time_eq z (hsub hz)
  · intro x hx
    exact e.toCompatibleEmbedding.isIntegralCurveOn x hx |>.mono
      (by
        intro s hs
        exact ⟨le_of_lt hs.1, le_of_lt hs.2⟩)

private theorem continuousOn_compatibleEmbedding_toFun
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) :
    ContinuousOn e.toFun (C ×ˢ J) := by
  rw [continuousOn_iff_continuous_restrict]
  exact e.isEmbedding.continuous

/-- **Math.** Two compatible time-slice embeddings agree on a closed slab
when their central time is interior.  Continuity is required only on the
declared source and follows from the embedding fields themselves; no global
extension or closedness assumption on the spatial source is needed. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.eqOn_Icc_of_embedding
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t a b : ℝ}
    (e₁ e₂ : S.CompatibleTimeSliceEmbedding n C t (Icc a b))
    (hab : a < b) (ht : t ∈ Ioo a b) :
    Set.EqOn e₁.toFun e₂.toFun (C ×ˢ Icc a b) := by
  let e₁oo := restrictIooForClosure n e₁ ht
  let e₂oo := restrictIooForClosure n e₂ ht
  have hopen : Set.EqOn e₁.toFun e₂.toFun (C ×ˢ Ioo a b) := by
    exact GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.eqOn_Ioo
      n e₁oo e₂oo ht
  have hcont₁ : ContinuousOn e₁.toFun (C ×ˢ Icc a b) :=
    continuousOn_compatibleEmbedding_toFun n e₁.toCompatibleEmbedding
  have hcont₂ : ContinuousOn e₂.toFun (C ×ˢ Icc a b) :=
    continuousOn_compatibleEmbedding_toFun n e₂.toCompatibleEmbedding
  letI : T2Space N := S.t2Space
  apply Set.EqOn.of_subset_closure hopen hcont₁ hcont₂
  · intro z hz
    exact ⟨hz.1, ⟨le_of_lt hz.2.1, le_of_lt hz.2.2⟩⟩
  · intro z hz
    rw [closure_prod_eq]
    refine ⟨subset_closure hz.1, ?_⟩
    rw [closure_Ioo hab.ne]
    exact hz.2

/-- **Math.** Positive affine time reparameterization preserves the embedding
part of a compatible embedding on its reparameterized source. -/
theorem GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam_isEmbedding
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    Topology.IsEmbedding
      (Set.restrict
        (C ×ˢ (parabolicTimeOrderIso Q hQ a '' J))
        (e.affineTimeReparam n Q hQ a)) := by
  let o := parabolicTimeOrderIso Q hQ a
  let ho : (o '' J) ≃ₜ J := (o.toHomeomorph.image J).symm
  let hp : (C ×ˢ (o '' J)) ≃ₜ (C ×ˢ J) :=
    (Homeomorph.Set.prod C (o '' J)).trans
      ((Homeomorph.refl C).prodCongr ho) |>.trans
      (Homeomorph.Set.prod C J).symm
  have hcomp := e.isEmbedding.comp hp.isEmbedding
  convert hcomp using 1
  funext z
  rcases z with ⟨z, hz⟩
  rcases z with ⟨x, s⟩
  simp only [Set.restrict, Function.comp_apply, hp, Homeomorph.trans_apply,
    Homeomorph.Set.prod_apply]
  rfl

/-! ## Exact affine laws for the time range -/

/-- **Math.** Positive parabolic rescaling carries the time range to its
affine image. -/
theorem GeneralizedSpaceTime.range_scaledTime
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) :
    Set.range (S.scaledTime n Q) =
      parabolicTimeOrderIso Q hQ 0 '' Set.range S.time := by
  ext s
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨S.time x, ⟨x, rfl⟩, by simp [parabolicTimeOrderIso_apply]⟩
  · rintro ⟨t, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, by simp [parabolicTimeOrderIso_apply]⟩

/-- **Math.** Time translation carries the time range to its translated
affine image. -/
theorem GeneralizedSpaceTime.range_translatedTime
    (S : GeneralizedSpaceTime n (N := N)) (a : ℝ) :
    Set.range (S.translatedTime n a) =
      parabolicTimeOrderIso 1 zero_lt_one a '' Set.range S.time := by
  ext s
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨S.time x, ⟨x, rfl⟩, by simp [parabolicTimeOrderIso_apply]⟩
  · rintro ⟨t, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, by simp [parabolicTimeOrderIso_apply]⟩

/-- **Math.** The frontier of the rescaled time range is the affine image of
the original frontier. -/
theorem GeneralizedSpaceTime.frontier_range_scaledTime
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) :
    frontier (Set.range (S.scaledTime n Q)) =
      parabolicTimeOrderIso Q hQ 0 '' frontier (Set.range S.time) := by
  rw [S.range_scaledTime n Q hQ]
  change
    frontier ((parabolicTimeOrderIso Q hQ 0).toHomeomorph '' Set.range S.time) =
      (parabolicTimeOrderIso Q hQ 0).toHomeomorph '' frontier (Set.range S.time)
  exact ((parabolicTimeOrderIso Q hQ 0).toHomeomorph.image_frontier
    (Set.range S.time)).symm

/-- **Math.** The frontier of the translated time range is the translated
frontier of the original time range. -/
theorem GeneralizedSpaceTime.frontier_range_translatedTime
    (S : GeneralizedSpaceTime n (N := N)) (a : ℝ) :
    frontier (Set.range (S.translatedTime n a)) =
      parabolicTimeOrderIso 1 zero_lt_one a '' frontier (Set.range S.time) := by
  rw [S.range_translatedTime n a]
  change
    frontier ((parabolicTimeOrderIso 1 zero_lt_one a).toHomeomorph '' Set.range S.time) =
      (parabolicTimeOrderIso 1 zero_lt_one a).toHomeomorph '' frontier (Set.range S.time)
  exact ((parabolicTimeOrderIso 1 zero_lt_one a).toHomeomorph.image_frontier
    (Set.range S.time)).symm

/-- **Math.** Rescaling does not change which ambient points lie over the
frontier of the time range. -/
theorem GeneralizedSpaceTime.scaledTime_preimage_frontier_range
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) :
    S.scaledTime n Q ⁻¹' frontier (Set.range (S.scaledTime n Q)) =
      S.time ⁻¹' frontier (Set.range S.time) := by
  rw [S.frontier_range_scaledTime n Q hQ]
  ext x
  constructor
  · rintro ⟨u, hu, hux⟩
    have hval : u = S.time x := by
      apply (parabolicTimeOrderIso Q hQ 0).injective
      calc
        parabolicTimeOrderIso Q hQ 0 u = S.scaledTime n Q x := hux
        _ = parabolicTimeOrderIso Q hQ 0 (S.time x) := by
          simp [GeneralizedSpaceTime.scaledTime, parabolicTimeOrderIso_apply]
    simpa [hval] using hu
  · intro hx
    refine ⟨S.time x, hx, ?_⟩
    simp [parabolicTimeOrderIso_apply]

/-- **Math.** Translation does not change which ambient points lie over the
frontier of the time range. -/
theorem GeneralizedSpaceTime.translatedTime_preimage_frontier_range
    (S : GeneralizedSpaceTime n (N := N)) (a : ℝ) :
    S.translatedTime n a ⁻¹' frontier (Set.range (S.translatedTime n a)) =
      S.time ⁻¹' frontier (Set.range S.time) := by
  rw [S.frontier_range_translatedTime n a]
  ext x
  constructor
  · rintro ⟨u, hu, hux⟩
    have hval : u = S.time x := by
      apply (parabolicTimeOrderIso 1 zero_lt_one a).injective
      calc
        parabolicTimeOrderIso 1 zero_lt_one a u = S.translatedTime n a x := hux
        _ = parabolicTimeOrderIso 1 zero_lt_one a (S.time x) := by
          simp [GeneralizedSpaceTime.translatedTime, parabolicTimeOrderIso_apply]
    simpa [hval] using hu
  · intro hx
    refine ⟨S.time x, hx, ?_⟩
    simp [parabolicTimeOrderIso_apply]

end MorganTianLib

end
