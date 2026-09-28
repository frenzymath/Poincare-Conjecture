import HatcherLib.Ch1.CoveringSpaces

/-!
# Chapter 1: classification and uniqueness of covering spaces

The lifting criterion compares connected covering spaces by their induced
fundamental-group subgroups.  Mutual lifts preserving chosen basepoints are
inverse by uniqueness of lifts.  In particular, any two locally
path-connected simply connected covering spaces over the same base are
canonically isomorphic after choosing points in the same fiber.
-/

namespace HatcherLib

noncomputable section

universe u v w

variable {E : Type u} {F : Type v} {X : Type w}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
variable {p : E → X} {q : F → X} {e₀ : E} {f₀ : F}

/-- A basepoint-preserving isomorphism of two covering spaces over the same
base. -/
structure BasedCoveringEquiv (p : E → X) (q : F → X) (e₀ : E) (f₀ : F) where
  toHomeomorph : E ≃ₜ F
  map_basepoint : toHomeomorph e₀ = f₀
  commutes : q ∘ (toHomeomorph : E → F) = p

/-- A parser-visible alias for basepointed covering equivalences. -/
def basedCoveringEquivType (p : E → X) (q : F → X) (e₀ : E) (f₀ : F) :=
  BasedCoveringEquiv p q e₀ f₀

namespace BasedCoveringEquiv

instance : CoeFun (BasedCoveringEquiv p q e₀ f₀) fun _ ↦ E → F :=
  ⟨fun h ↦ h.toHomeomorph⟩

omit [TopologicalSpace X] in
@[simp] theorem apply_basepoint (h : BasedCoveringEquiv p q e₀ f₀) :
    h e₀ = f₀ :=
  h.map_basepoint

omit [TopologicalSpace X] in
theorem preserves_projection (h : BasedCoveringEquiv p q e₀ f₀) (e : E) :
    q (h e) = p e :=
  congrFun h.commutes e

omit [TopologicalSpace X] in
@[ext] theorem ext {h k : BasedCoveringEquiv p q e₀ f₀}
    (heq : h.toHomeomorph = k.toHomeomorph) : h = k := by
  cases h
  cases k
  cases heq
  rfl

/-- Reverse a basepointed equivalence of covering spaces. -/
def symm (h : BasedCoveringEquiv p q e₀ f₀) :
    BasedCoveringEquiv q p f₀ e₀ where
  toHomeomorph := h.toHomeomorph.symm
  map_basepoint := by
    apply h.toHomeomorph.injective
    simp [h.map_basepoint]
  commutes := by
    funext f
    obtain ⟨e, rfl⟩ := h.toHomeomorph.surjective f
    simpa using (h.preserves_projection e).symm

/-- Basepointed covering equivalences into a connected covering are uniquely
determined by their value at the basepoint. -/
theorem toHomeomorph_unique (covq : CoveringMap q) [PreconnectedSpace E]
    (h k : BasedCoveringEquiv p q e₀ f₀) :
    h.toHomeomorph = k.toHomeomorph := by
  apply Homeomorph.ext
  have heq : (h.toHomeomorph : E → F) = (k.toHomeomorph : E → F) :=
    covq.eq_of_comp_eq h.toHomeomorph.continuous k.toHomeomorph.continuous
      (h.commutes.trans k.commutes.symm) e₀
      (h.map_basepoint.trans k.map_basepoint.symm)
  exact congrFun heq

/-- There is at most one basepoint-preserving covering equivalence over a
connected source. -/
theorem unique (covq : CoveringMap q) [PreconnectedSpace E]
    (h k : BasedCoveringEquiv p q e₀ f₀) : h = k :=
  ext (toHomeomorph_unique covq h k)

end BasedCoveringEquiv

/-- Package two mutually compatible based lifts as an isomorphism of covering
spaces.  The inverse laws follow from uniqueness of lifts. -/
def basedCoveringEquivOfMutualLifts
    (covp : CoveringMap p) (covq : CoveringMap q)
    [PreconnectedSpace E] [PreconnectedSpace F]
    (forward : C(E, F)) (backward : C(F, E))
    (hforward₀ : forward e₀ = f₀) (hbackward₀ : backward f₀ = e₀)
    (hforward : q ∘ (forward : E → F) = p)
    (hbackward : p ∘ (backward : F → E) = q) :
    BasedCoveringEquiv p q e₀ f₀ := by
  have hleft : (backward : F → E) ∘ (forward : E → F) = id := by
    exact covp.eq_of_comp_eq
      (backward.continuous.comp forward.continuous) continuous_id
      (by
        funext e
        exact (congrFun hbackward (forward e)).trans (congrFun hforward e))
      e₀ ((congrArg backward hforward₀).trans hbackward₀)
  have hright : (forward : E → F) ∘ (backward : F → E) = id := by
    exact covq.eq_of_comp_eq
      (forward.continuous.comp backward.continuous) continuous_id
      (by
        funext f
        exact (congrFun hforward (backward f)).trans (congrFun hbackward f))
      f₀ ((congrArg forward hbackward₀).trans hforward₀)
  let equiv : E ≃ F :=
    { toFun := forward
      invFun := backward
      left_inv := congrFun hleft
      right_inv := congrFun hright }
  exact
    { toHomeomorph := Homeomorph.mk equiv forward.continuous backward.continuous
      map_basepoint := hforward₀
      commutes := hforward }

/-- The basepointed covering-space isomorphism criterion.  The two subgroup
inclusions are the lifting criteria in the two possible directions, with the
basepoint-change equalities displayed explicitly. -/
def basedCoveringEquivOfPiOneRanges
    (covp : CoveringMap p) (covq : CoveringMap q)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    (hbase : p e₀ = q f₀)
    (hforward :
      (FundamentalGroup.map ⟨p, covp.continuous⟩ e₀).range ≤
        (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ hbase.symm).range)
    (hbackward :
      (FundamentalGroup.map ⟨q, covq.continuous⟩ f₀).range ≤
        (FundamentalGroup.mapOfEq ⟨p, covp.continuous⟩ hbase).range) :
    BasedCoveringEquiv p q e₀ f₀ := by
  let forward_exists :=
    covq.existsUnique_continuousMap_lifts_of_range_le
      (f := (⟨p, covp.continuous⟩ : C(E, X)))
      (a₀ := e₀) (e₀ := f₀) hbase.symm hforward
  let backward_exists :=
    covp.existsUnique_continuousMap_lifts_of_range_le
      (f := (⟨q, covq.continuous⟩ : C(F, X)))
      (a₀ := f₀) (e₀ := e₀) hbase hbackward
  let forward := forward_exists.choose
  let backward := backward_exists.choose
  have ⟨hforward₀, hforward_lifts⟩ := forward_exists.choose_spec.1
  have ⟨hbackward₀, hbackward_lifts⟩ := backward_exists.choose_spec.1
  exact basedCoveringEquivOfMutualLifts covp covq forward backward
    hforward₀ hbackward₀ hforward_lifts hbackward_lifts

/-- Two path-connected, locally path-connected based covering spaces are
equivalent over the base exactly when their induced fundamental-group image
subgroups agree after transporting to the same basepoint. -/
theorem nonempty_basedCoveringEquiv_iff_piOneRanges_eq
    (covp : CoveringMap p) (covq : CoveringMap q)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    (hbase : p e₀ = q f₀) :
    Nonempty (BasedCoveringEquiv p q e₀ f₀) ↔
      (FundamentalGroup.map ⟨p, covp.continuous⟩ e₀).range =
        (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ hbase.symm).range := by
  constructor
  · rintro ⟨h⟩
    apply le_antisymm
    · exact piOne_range_le_of_lift (A := E) covq
        (f := (⟨p, covp.continuous⟩ : C(E, X)))
        (f' := (⟨h.toHomeomorph, h.toHomeomorph.continuous⟩ : C(E, F)))
        hbase.symm h.map_basepoint h.commutes
    · have hrange := piOne_mapOfEq_range_le_of_lift (A := F) covp
        (f := (⟨q, covq.continuous⟩ : C(F, X)))
        (f' := (⟨h.symm.toHomeomorph,
          h.symm.toHomeomorph.continuous⟩ : C(F, E))) hbase.symm rfl
        h.symm.map_basepoint h.symm.commutes
      simpa using hrange
  · intro hrange
    have hbackward :
        (FundamentalGroup.map ⟨q, covq.continuous⟩ f₀).range ≤
          (FundamentalGroup.mapOfEq ⟨p, covp.continuous⟩ hbase).range := by
      rintro z ⟨u, rfl⟩
      have hu : FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ hbase.symm u ∈
          (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ hbase.symm).range :=
        ⟨u, rfl⟩
      rw [← hrange] at hu
      obtain ⟨v, hv⟩ := hu
      refine ⟨v, ?_⟩
      have hv' := congrArg
        (FundamentalGroup.mapOfEq (ContinuousMap.id X) hbase) hv
      have hptransport :
          FundamentalGroup.mapOfEq (ContinuousMap.id X) hbase
              (FundamentalGroup.map ⟨p, covp.continuous⟩ e₀ v) =
            FundamentalGroup.mapOfEq ⟨p, covp.continuous⟩ hbase v :=
        DFunLike.congr_fun (fundamentalGroup_basepointTransport_comp_map
          (⟨p, covp.continuous⟩ : C(E, X)) hbase) v
      have hqtransport :
          FundamentalGroup.mapOfEq (ContinuousMap.id X) hbase
              (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ hbase.symm u) =
            FundamentalGroup.map ⟨q, covq.continuous⟩ f₀ u :=
        DFunLike.congr_fun (fundamentalGroup_basepointTransport_comp_mapOfEq_symm
          (⟨q, covq.continuous⟩ : C(F, X)) hbase) u
      rw [hptransport, hqtransport] at hv'
      exact hv'
    exact ⟨basedCoveringEquivOfPiOneRanges covp covq hbase hrange.le hbackward⟩

/-- A universal covering map over Hatcher's class of base spaces: the base is
path-connected and locally path-connected, the covering is onto, and the total
space is simply connected. -/
def IsUniversalCoveringMap (p : E → X) : Prop :=
  CoveringMap p ∧ Function.Surjective p ∧ PathConnectedSpace X ∧
    LocallyPathConnectedSpace X ∧ SimplyConnectedSpace E

/-- A `K(G,1)` space, presented together with a contractible universal cover.
The fundamental-group isomorphism may use any basepoint since the base is path
connected. -/
def IsKGOneSpace (G : Type u) (X : Type v) (E : Type w)
    [Group G] [TopologicalSpace X] [TopologicalSpace E] (p : E → X) : Prop :=
  PathConnectedSpace X ∧
    (∃ x₀ : X, Nonempty (FundamentalGroup X x₀ ≃* G)) ∧
    CoveringMap p ∧ Function.Surjective p ∧ ContractibleSpace E

namespace IsUniversalCoveringMap

theorem coveringMap (h : IsUniversalCoveringMap p) : CoveringMap p :=
  h.1

theorem surjective (h : IsUniversalCoveringMap p) : Function.Surjective p :=
  h.2.1

theorem pathConnectedSpace (h : IsUniversalCoveringMap p) : PathConnectedSpace X :=
  h.2.2.1

theorem locPathConnectedSpace (h : IsUniversalCoveringMap p) : LocallyPathConnectedSpace X :=
  h.2.2.2.1

theorem simplyConnectedSpace (h : IsUniversalCoveringMap p) : SimplyConnectedSpace E :=
  h.2.2.2.2

/-- The total space of a universal cover is locally path-connected because
the base is locally path-connected. -/
theorem totalLocPathConnectedSpace (h : IsUniversalCoveringMap p) :
    LocallyPathConnectedSpace E := by
  letI : LocallyPathConnectedSpace X := h.locPathConnectedSpace
  exact h.coveringMap.locPathConnectedSpace

/-- A universal cover admits a unique based continuous map to every other
covering over the same base. This is the based lifting part of “the universal
cover covers every connected cover”; it does not yet assert that the resulting
map is itself a covering map. -/
theorem existsUnique_mapToCover
    (hp : IsUniversalCoveringMap p)
    (covq : CoveringMap q) (hbase : p e₀ = q f₀) :
    ∃! lift : C(E, F), lift e₀ = f₀ ∧ q ∘ lift = p := by
  letI : LocallyPathConnectedSpace E := hp.totalLocPathConnectedSpace
  letI : SimplyConnectedSpace E := hp.simplyConnectedSpace
  exact covq.existsUnique_continuousMap_lifts
    (⟨p, hp.coveringMap.continuous⟩ : C(E, X)) e₀ f₀ hbase.symm

end IsUniversalCoveringMap

/-- Any two locally path-connected universal covers are uniquely isomorphic
after choosing basepoints in the same fiber. -/
def universalCoverBasedEquiv
    (covp : CoveringMap p) (covq : CoveringMap q)
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    [SimplyConnectedSpace F] [LocallyPathConnectedSpace F]
    (hbase : p e₀ = q f₀) : BasedCoveringEquiv p q e₀ f₀ := by
  let forward_exists :=
    covq.existsUnique_continuousMap_lifts
      (⟨p, covp.continuous⟩ : C(E, X)) e₀ f₀ hbase.symm
  let backward_exists :=
    covp.existsUnique_continuousMap_lifts
      (⟨q, covq.continuous⟩ : C(F, X)) f₀ e₀ hbase
  let forward := forward_exists.choose
  let backward := backward_exists.choose
  have ⟨hforward₀, hforward_lifts⟩ := forward_exists.choose_spec.1
  have ⟨hbackward₀, hbackward_lifts⟩ := backward_exists.choose_spec.1
  exact basedCoveringEquivOfMutualLifts covp covq forward backward
    hforward₀ hbackward₀ hforward_lifts hbackward_lifts

/-- Universal-cover uniqueness stated using `IsUniversalCoveringMap`. -/
def universalCoverBasedEquivOfIsUniversal
    (hp : IsUniversalCoveringMap p) (hq : IsUniversalCoveringMap q)
    (hbase : p e₀ = q f₀) : BasedCoveringEquiv p q e₀ f₀ := by
  letI : LocallyPathConnectedSpace E := hp.totalLocPathConnectedSpace
  letI : LocallyPathConnectedSpace F := hq.totalLocPathConnectedSpace
  letI : SimplyConnectedSpace E := hp.simplyConnectedSpace
  letI : SimplyConnectedSpace F := hq.simplyConnectedSpace
  exact universalCoverBasedEquiv hp.coveringMap hq.coveringMap hbase

/-- The basepointed isomorphism between two universal covers is unique. -/
theorem universalCoverBasedEquiv_eq
    (covp : CoveringMap p) (covq : CoveringMap q)
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    [SimplyConnectedSpace F] [LocallyPathConnectedSpace F]
    (hbase : p e₀ = q f₀) (h : BasedCoveringEquiv p q e₀ f₀) :
    h = universalCoverBasedEquiv covp covq hbase :=
  BasedCoveringEquiv.unique covq h _

end
end HatcherLib
