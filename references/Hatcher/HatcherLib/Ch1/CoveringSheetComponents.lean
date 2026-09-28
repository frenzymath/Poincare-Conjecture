import HatcherLib.Ch1.CoveringSheets
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Chapter 1: sheets as connected components

An evenly covered preimage is homeomorphic to a product `U x I` with `I`
discrete.  When `U` is connected, its sheets are exactly the connected
components of the preimage.  This file states the result for an explicit
covering trivialization, matching the witness contained in `IsEvenlyCovered`.
-/

open Set Function Topology TopologicalSpace

namespace HatcherLib

noncomputable section

universe u v w

variable {E : Type u} {X : Type v} {I : Type w}
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace I]

/-- The sheet indexed by `i` in a covering trivialization of `p` over `U`. -/
def trivializedSheet (p : E -> X) {U : Set X} {I : Type w} [TopologicalSpace I]
    (H : p ⁻¹' U ≃ₜ U × I) (i : I) : Set E :=
  (Subtype.val : (p ⁻¹' U) -> E) ''
    (H ⁻¹' ((Set.univ : Set U) ×ˢ ({i} : Set I)))

theorem trivializedSheet_subset_preimage (p : E -> X) {U : Set X} {I : Type w}
    [TopologicalSpace I] (H : p ⁻¹' U ≃ₜ U × I) (i : I) :
    trivializedSheet p H i ⊆ p ⁻¹' U := by
  rintro e ⟨z, hz, rfl⟩
  exact z.property

theorem trivializedSheet_isOpen (p : E -> X) {U : Set X} {I : Type w}
    [TopologicalSpace I] (hpre : IsOpen (p ⁻¹' U))
    [DiscreteTopology I] (H : p ⁻¹' U ≃ₜ U × I) (i : I) :
    IsOpen (trivializedSheet p H i) := by
  apply hpre.isOpenMap_subtype_val _
  exact H.isOpen_preimage.mpr (isOpen_univ.prod (isOpen_discrete _))

theorem trivializedSheet_isConnected (p : E -> X) {U : Set X} {I : Type w}
    [TopologicalSpace I] (hU : IsConnected U)
    (H : p ⁻¹' U ≃ₜ U × I) (i : I) :
    IsConnected (trivializedSheet p H i) := by
  letI : ConnectedSpace U := Subtype.connectedSpace hU
  let S : Set (p ⁻¹' U) :=
    H ⁻¹' ((Set.univ : Set U) ×ˢ ({i} : Set I))
  have hprod : IsConnected ((Set.univ : Set U) ×ˢ ({i} : Set I)) :=
    isConnected_univ.prod isConnected_singleton
  have hS : IsConnected S := H.isConnected_preimage.mpr hprod
  have hval : IsConnected ((Subtype.val : (p ⁻¹' U) -> E) '' S) :=
    hS.image _ continuous_subtype_val.continuousOn
  simpa [trivializedSheet, S] using hval

/-- Each fixed-coordinate slice of a covering trivialization is a sheet. -/
theorem trivializedSheet_isSheet (p : E -> X) {U : Set X} {I : Type w}
    [TopologicalSpace I] [DiscreteTopology I]
    (hpre : IsOpen (p ⁻¹' U))
    (H : p ⁻¹' U ≃ₜ U × I)
    (hH : ∀ z, (H z).1.1 = p z) (i : I) :
    IsSheet p U (trivializedSheet p H i) := by
  refine ⟨trivializedSheet_isOpen p hpre H i, ?_⟩
  let S : Set (p ⁻¹' U) :=
    H ⁻¹' ((Set.univ : Set U) ×ˢ ({i} : Set I))
  let hSU : S ≃ₜ ((Set.univ : Set U) ×ˢ ({i} : Set I)) := H.sets rfl
  let Uset : Set U := Set.univ
  let Iset : Set I := {i}
  let hprod0 : (Uset ×ˢ Iset) ≃ₜ (↑Uset × ↑Iset) :=
    Homeomorph.Set.prod Uset Iset
  let hprod1 : (Uset ×ˢ Iset) ≃ₜ U × ↑Iset :=
    hprod0.trans ((Homeomorph.Set.univ U).prodCongr (Homeomorph.refl Iset))
  let hprod : (Uset ×ˢ Iset) ≃ₜ U :=
    hprod1.trans (Homeomorph.prodUnique U Iset)
  let hval : S ≃ₜ trivializedSheet p H i :=
    (IsEmbedding.subtypeVal.homeomorphImage S).trans (Homeomorph.setCongr rfl)
  let e : trivializedSheet p H i ≃ₜ U := hval.symm.trans (hSU.trans hprod)
  refine ⟨e, ?_⟩
  intro v
  rcases v with ⟨v, ⟨z, hz, rfl⟩⟩
  change (e ⟨(z : E), ⟨z, hz, rfl⟩⟩ : X) = p z
  have hval_symm :
      hval.symm ⟨(z : E), ⟨z, hz, rfl⟩⟩ = (⟨z, hz⟩ : S) := by
    apply hval.injective
    rw [hval.apply_symm_apply]
    rfl
  rw [show e = hval.symm.trans (hSU.trans hprod) from rfl,
    Homeomorph.trans_apply, Homeomorph.trans_apply, hval_symm]
  simpa [hSU, S, hprod, hprod1, hprod0, Uset, Iset] using hH z

/-- Over a connected base, each fixed-coordinate sheet is the connected
component of any one of its points inside the evenly covered preimage. -/
theorem trivializedSheet_eq_connectedComponentIn (p : E -> X) {U : Set X}
    {I : Type w} [TopologicalSpace I] [DiscreteTopology I]
    (hU : IsConnected U) (H : p ⁻¹' U ≃ₜ U × I) (i : I)
    (z : trivializedSheet p H i) :
    connectedComponentIn (p ⁻¹' U) z = trivializedSheet p H i := by
  apply Set.Subset.antisymm
  · intro e he
    have hzW : (z : E) ∈ p ⁻¹' U :=
      trivializedSheet_subset_preimage p H i z.property
    rw [connectedComponentIn_eq_image hzW] at he
    rcases he with ⟨eW, heW, rfl⟩
    rcases z.property with ⟨zW, hzslice, hzval⟩
    have hzW_eq : zW = (⟨z, hzW⟩ : p ⁻¹' U) := by
      apply Subtype.ext
      exact hzval
    have hq : Continuous (fun w : p ⁻¹' U => (H w).2) :=
      continuous_snd.comp H.continuous
    have hqmem : (H eW).2 ∈ ({(H zW).2} : Set I) := by
      rw [← hq.image_connectedComponent_eq_singleton zW]
      refine ⟨eW, ?_, rfl⟩
      simpa [hzW_eq] using heW
    have hzsecond : (H zW).2 = i := hzslice.2
    refine ⟨eW, ?_, rfl⟩
    exact ⟨Set.mem_univ _, by simpa [hzsecond] using hqmem⟩
  · exact (trivializedSheet_isConnected p hU H i).2.subset_connectedComponentIn
      z.property (trivializedSheet_subset_preimage p H i)

/-- Every sheet over a connected trivializing neighborhood is one of the
fixed-coordinate slices. -/
theorem isSheet_eq_trivializedSheet (p : E -> X) {U : Set X} {I : Type w}
    [TopologicalSpace I] [DiscreteTopology I]
    (hU : IsConnected U) (H : p ⁻¹' U ≃ₜ U × I)
    (hH : ∀ z, (H z).1.1 = p z)
    {V : Set E} (hV : IsSheet p U V) (z0 : V) :
    V = trivializedSheet p H (H ⟨z0, hV.mapsTo z0.property⟩).2 := by
  have hVsub : V ⊆ p ⁻¹' U := fun _ hv => hV.mapsTo hv
  let j : V -> p ⁻¹' U := fun v => ⟨v, hVsub v.property⟩
  let q : V -> I := fun v => (H (j v)).2
  haveI : ConnectedSpace U := Subtype.connectedSpace hU
  haveI : ConnectedSpace V :=
    hV.homeomorph.symm.surjective.connectedSpace hV.homeomorph.symm.continuous
  have hq : Continuous q :=
    continuous_snd.comp (H.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hqconst (v : V) : q v = q z0 :=
    TotallyDisconnectedSpace.eq_of_continuous q hq v z0
  let i : I := q z0
  have hi : i = (H ⟨z0, hV.mapsTo z0.property⟩).2 := rfl
  apply Set.Subset.antisymm
  · intro v hv
    refine ⟨j ⟨v, hv⟩, ?_, rfl⟩
    exact ⟨Set.mem_univ _, by simpa [i, q, j] using hqconst ⟨v, hv⟩⟩
  · intro e he
    rcases he with ⟨eW, heW, rfl⟩
    let u : U := (H eW).1
    obtain ⟨v, hv⟩ := hV.homeomorph.surjective u
    have hfirst : (H eW).1 = (H (j v)).1 := by
      apply Subtype.ext
      calc
        (H eW).1.1 = (u : X) := rfl
        _ = (hV.homeomorph v : X) := congrArg (fun w : U => (w : X)) hv.symm
        _ = p (v : E) := hV.2.choose_spec v
        _ = (H (j v)).1.1 := (hH (j v)).symm
    have hsecond : (H eW).2 = (H (j v)).2 := by
      rw [heW.2, ← hi]
      exact (hqconst v).symm.trans rfl
    have hHeq : H eW = H (j v) := Prod.ext hfirst hsecond
    have heq : eW = j v := H.injective hHeq
    have heval : (eW : E) = (v : E) := by
      simpa [j] using congrArg Subtype.val heq
    rw [heval]
    exact v.property

/-- For a connected evenly covered open set, the sheets are exactly the
connected components of its preimage. -/
theorem isSheet_iff_connectedComponentIn (p : E -> X) {U : Set X} {I : Type w}
    [TopologicalSpace I] [DiscreteTopology I]
    (hU : IsConnected U) (H : p ⁻¹' U ≃ₜ U × I)
    (hH : ∀ z, (H z).1.1 = p z)
    {V : Set E} (hpre : IsOpen (p ⁻¹' U)) :
    IsSheet p U V ↔
      ∃ e : E, e ∈ V ∧ V = connectedComponentIn (p ⁻¹' U) e := by
  constructor
  · intro hV
    obtain ⟨u, hu⟩ := hU.nonempty
    let z0 : V := hV.homeomorph.symm ⟨u, hu⟩
    let i : I := (H ⟨z0, hV.mapsTo z0.property⟩).2
    refine ⟨z0, z0.property, ?_⟩
    have hcanon := isSheet_eq_trivializedSheet p hU H hH hV z0
    have hcomp := trivializedSheet_eq_connectedComponentIn p hU H i
      ⟨(z0 : E), ⟨⟨z0, hV.mapsTo z0.property⟩,
        by exact ⟨Set.mem_univ _, rfl⟩, rfl⟩⟩
    exact hcanon.trans hcomp.symm
  · rintro ⟨e, heV, hEq⟩
    have heW : e ∈ p ⁻¹' U := connectedComponentIn_subset _ _ (hEq ▸ heV)
    let i : I := (H ⟨e, heW⟩).2
    have heSheet : e ∈ trivializedSheet p H i := by
      exact ⟨⟨e, heW⟩, ⟨Set.mem_univ _, rfl⟩, rfl⟩
    have hcomp := trivializedSheet_eq_connectedComponentIn p hU H i ⟨e, heSheet⟩
    have hcomp' :
        connectedComponentIn (p ⁻¹' U) e = trivializedSheet p H i := by
      simpa using hcomp
    rw [hEq, hcomp']
    exact trivializedSheet_isSheet p hpre H hH i

end
end HatcherLib
