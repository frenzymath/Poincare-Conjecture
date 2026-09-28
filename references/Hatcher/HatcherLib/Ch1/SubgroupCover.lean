import HatcherLib.Ch1.GroupActions
import HatcherLib.Ch1.UniversalCoverConstruction

/-!
# Chapter 1: subgroup orbit maps

This module constructs intermediate covers by quotienting a universal cover by
an arbitrary subgroup of its deck group.  Uniform sheet-orbit trivializations
show that the descended map is a covering, and monodromy identifies its induced
fundamental-group subgroup.  Applying this to the path-class universal cover
realizes every subgroup of `PiOne`.
-/

namespace HatcherLib

noncomputable section

universe u v w

variable {E : Type u} {X : Type v}
  [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}

/-! ## The restricted deck action -/

instance subgroupDeckTransformationMulAction
    (S : Subgroup (DeckTransformationGroup p)) : MulAction S E :=
  MulAction.compHom E S.subtype

instance subgroupDeckTransformationContinuousConstSMul
    (S : Subgroup (DeckTransformationGroup p)) : ContinuousConstSMul S E where
  continuous_const_smul s := (s.1.1 : E ≃ₜ E).continuous

/-! ## The descended map -/

/-- The map from the quotient by a deck subgroup to the original base. -/
def subgroupOrbitMap (S : Subgroup (DeckTransformationGroup p)) :
    OrbitSpace S E → X :=
  Quotient.lift p (fun a b hab => by
    obtain ⟨s, hs⟩ :=
      MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hs]
    exact deckTransformation_preserves_projection s.1 b)

omit [TopologicalSpace X] in
@[simp] theorem subgroupOrbitMap_mk
    (S : Subgroup (DeckTransformationGroup p)) (e : E) :
    subgroupOrbitMap (p := p) S (orbitProjection S E e) = p e :=
  rfl

omit [TopologicalSpace X] in
theorem subgroupOrbitMap_comp_orbitProjection
    (S : Subgroup (DeckTransformationGroup p)) :
    subgroupOrbitMap (p := p) S ∘ orbitProjection S E = p := by
  funext e
  rfl

theorem subgroupOrbitMap_continuous (cov : CoveringMap p)
    (S : Subgroup (DeckTransformationGroup p)) :
    Continuous (subgroupOrbitMap (p := p) S) :=
  cov.continuous.quotient_lift (fun a b hab => by
    obtain ⟨s, hs⟩ :=
      MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hs]
    exact deckTransformation_preserves_projection s.1 b)

omit [TopologicalSpace X] in
theorem subgroupOrbitMap_surjective (hp : Function.Surjective p)
    (S : Subgroup (DeckTransformationGroup p)) :
    Function.Surjective (subgroupOrbitMap (p := p) S) := by
  intro x
  obtain ⟨e, rfl⟩ := hp x
  exact ⟨orbitProjection S E e, rfl⟩

/-! ## Consequences available before the sheet quotient is constructed -/

theorem subgroupOrbitProjection_isCoveringMap (cov : CoveringMap p)
    [PreconnectedSpace E] (S : Subgroup (DeckTransformationGroup p)) :
    CoveringMap (orbitProjection S E) := by
  apply orbitProjection_isCoveringMap
  exact subgroup_deckTransformationGroup_isCoveringSpaceAction cov S

theorem subgroupOrbitMap_isLocalHomeomorph (cov : CoveringMap p)
    [PreconnectedSpace E] (S : Subgroup (DeckTransformationGroup p)) :
    IsLocalHomeomorph (subgroupOrbitMap (p := p) S) := by
  let qcov := subgroupOrbitProjection_isCoveringMap cov S
  have hcomp : IsLocalHomeomorph
      (subgroupOrbitMap (p := p) S ∘ orbitProjection S E) := by
    rw [subgroupOrbitMap_comp_orbitProjection]
    exact cov.isLocalHomeomorph
  have hq : IsLocalHomeomorph (orbitProjection S E) :=
    qcov.isLocalHomeomorph
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  have hlocal := IsLocalHomeomorphOn.of_comp_right
    (s := (Set.univ : Set E))
    hcomp.isLocalHomeomorphOn hq.isLocalHomeomorphOn
  have hqsurj : Function.Surjective (orbitProjection S E) := by
    intro z
    obtain ⟨e, he⟩ := Quotient.mk''_surjective z
    refine ⟨e, ?_⟩
    simpa [orbitProjection] using he
  rw [Set.image_univ, hqsurj.range_eq] at hlocal
  exact hlocal

/-- A fiber of a local homeomorphism is discrete. -/
theorem IsLocalHomeomorph.discreteTopology_fiber
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} (hf : IsLocalHomeomorph f) (b : B) :
    DiscreteTopology (f ⁻¹' {b}) :=
  (isDiscrete_iff_discreteTopology (s := f ⁻¹' {b})).mp <|
    IsDiscrete.of_openPartialHomeomorph f Set.Subset.rfl fun a _ ↦ by
      obtain ⟨e, ha, he⟩ := hf a
      exact ⟨e, ha, he.symm⟩

/-- A deck transformation sends one whole sheet of a trivialization to another
once it does so at a single point of a preconnected base set. -/
private theorem deckTransformation_trivialization_symm_eq
    {F : Type w} [TopologicalSpace F] (cov : CoveringMap p)
    (t : Bundle.Trivialization F p) (hbase : IsPreconnected t.baseSet)
    (phi : DeckTransformationGroup p) {i j : F} {y₀ : X}
    (hy₀ : y₀ ∈ t.baseSet)
    (h₀ : phi • t.invFun (y₀, i) = t.invFun (y₀, j)) :
    ∀ y ∈ t.baseSet, phi • t.invFun (y, i) = t.invFun (y, j) := by
  have hsection (k : F) :
      ContinuousOn (fun y : X ↦ t.invFun (y, k)) t.baseSet := by
    exact t.continuousOn_invFun.comp
      (continuous_id.prodMk continuous_const).continuousOn fun y hy ↦ by
        rw [t.target_eq]
        exact ⟨hy, Set.mem_univ k⟩
  have hleft : ContinuousOn
      (fun y : X ↦ phi • t.invFun (y, i)) t.baseSet :=
    (phi.1 : E ≃ₜ E).continuous.comp_continuousOn (hsection i)
  have hcomp : t.baseSet.EqOn
      (p ∘ fun y : X ↦ phi • t.invFun (y, i))
      (p ∘ fun y : X ↦ t.invFun (y, j)) := by
    intro y hy
    simp only [Function.comp_apply]
    calc
      p (phi • t.invFun (y, i)) = p (t.invFun (y, i)) :=
        deckTransformation_preserves_projection (p := p) phi _
      _ = y := t.proj_symm_apply' hy
      _ = p (t.invFun (y, j)) := (t.proj_symm_apply' hy).symm
  exact cov.eqOn_of_comp_eqOn hbase hleft (hsection j) hcomp hy₀ h₀

/-- The sheet of a trivialization selected by a fiber coordinate. -/
private def trivializationSheet {F : Type w} [TopologicalSpace F]
    (t : Bundle.Trivialization F p) (i : F) : Set E :=
  t.source ∩ (Prod.snd ∘ t) ⁻¹' {i}

private theorem trivializationSheet_isOpen {F : Type w} [TopologicalSpace F]
    [DiscreteTopology F] (t : Bundle.Trivialization F p) (i : F) :
    IsOpen (trivializationSheet t i) :=
  t.continuousOn_toFun.isOpen_inter_preimage t.open_source
    (continuous_snd.isOpen_preimage _ (isOpen_discrete _))

private theorem trivializationSheet_injOn {F : Type w} [TopologicalSpace F]
    (t : Bundle.Trivialization F p) (i : F) :
    (trivializationSheet t i).InjOn p := by
  intro e he e' he' hp
  apply t.injOn he.1 he'.1
  apply Prod.ext
  · exact (t.coe_fst he.1).trans (hp.trans (t.coe_fst he'.1).symm)
  · exact he.2.trans he'.2.symm

private theorem trivializationSheet_surjOn {F : Type w} [TopologicalSpace F]
    (t : Bundle.Trivialization F p) (i : F) :
    (trivializationSheet t i).SurjOn p t.baseSet := by
  intro y hy
  have htarget : (y, i) ∈ t.target := by
    rw [t.target_eq]
    exact ⟨hy, Set.mem_univ i⟩
  refine ⟨t.invFun (y, i), ⟨t.map_target htarget, ?_⟩, ?_⟩
  · exact congrArg Prod.snd (t.apply_symm_apply htarget)
  · exact t.proj_symm_apply' hy

private theorem trivialization_invFun_mem_sheet
    {F : Type w} [TopologicalSpace F] (t : Bundle.Trivialization F p)
    {y : X} (hy : y ∈ t.baseSet) (i : F) :
    t.invFun (y, i) ∈ trivializationSheet t i := by
  have htarget : (y, i) ∈ t.target := by
    rw [t.target_eq]
    exact ⟨hy, Set.mem_univ i⟩
  exact ⟨t.map_target htarget, congrArg Prod.snd (t.apply_symm_apply htarget)⟩

private theorem trivialization_invFun_eq_of_mem_sheet
    {F : Type w} [TopologicalSpace F] (t : Bundle.Trivialization F p)
    {i : F} {e : E} (he : e ∈ trivializationSheet t i) :
    t.invFun (p e, i) = e := by
  rw [← he.2]
  exact t.symm_apply_mk_proj he.1

/-- Orbit equality between two trivialization sheets propagates across a
preconnected base set. -/
private theorem orbitProjection_eq_of_trivializationSheets
    {F : Type w} [TopologicalSpace F] (cov : CoveringMap p)
    (t : Bundle.Trivialization F p) (hbase : IsPreconnected t.baseSet)
    (S : Subgroup (DeckTransformationGroup p)) {i j : F} {e e' : E}
    (he : e ∈ trivializationSheet t i)
    (he' : e' ∈ trivializationSheet t j)
    (hq : orbitProjection S E e = orbitProjection S E e') :
    ∀ y ∈ t.baseSet,
      orbitProjection S E (t.invFun (y, i)) =
        orbitProjection S E (t.invFun (y, j)) := by
  obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp
    ((orbitProjection_eq_iff (G := S) (Y := E) e e').mp hq)
  change (s.1 : DeckTransformationGroup p) • e' = e at hs
  have hpe : p e = p e' := by
    calc
      p e = p ((s.1 : DeckTransformationGroup p) • e') := congrArg p hs.symm
      _ = p e' := deckTransformation_preserves_projection (p := p) s.1 e'
  have hpe'base : p e' ∈ t.baseSet := t.mem_source.mp he'.1
  have h₀ : (s.1 : DeckTransformationGroup p) • t.invFun (p e', j) =
      t.invFun (p e', i) := by
    calc
      (s.1 : DeckTransformationGroup p) • t.invFun (p e', j) =
          (s.1 : DeckTransformationGroup p) • e' := by
            rw [trivialization_invFun_eq_of_mem_sheet t he']
      _ = e := hs
      _ = t.invFun (p e, i) :=
        (trivialization_invFun_eq_of_mem_sheet t he).symm
      _ = t.invFun (p e', i) := by rw [hpe]
  have hall := deckTransformation_trivialization_symm_eq
    cov t hbase s.1 hpe'base h₀
  intro y hy
  calc
    orbitProjection S E (t.invFun (y, i)) =
        orbitProjection S E ((s.1 : DeckTransformationGroup p) •
          t.invFun (y, j)) := congrArg (orbitProjection S E) (hall y hy).symm
    _ = orbitProjection S E (t.invFun (y, j)) := orbitProjection_smul s _

/-- Quotienting a path-connected covering space by any subgroup of its deck
group gives an intermediate covering of the original base. -/
theorem subgroupOrbitMap_isCoveringMap (cov : CoveringMap p)
    (hp : Function.Surjective p) [PathConnectedSpace E]
    [LocallyPathConnectedSpace X] (S : Subgroup (DeckTransformationGroup p)) :
    CoveringMap (subgroupOrbitMap (p := p) S) := by
  let q : E → OrbitSpace S E := orbitProjection S E
  let r : OrbitSpace S E → X := subgroupOrbitMap (p := p) S
  have hqcov : CoveringMap q := subgroupOrbitProjection_isCoveringMap cov S
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨e, he⟩ := Quotient.mk''_surjective z
    refine ⟨e, ?_⟩
    simpa [q, orbitProjection] using he
  have hrlocal : IsLocalHomeomorph r :=
    subgroupOrbitMap_isLocalHomeomorph cov S
  have hrcont : Continuous r := subgroupOrbitMap_continuous cov S
  intro x
  letI : Nonempty (p ⁻¹' {x}) := by
    obtain ⟨e, he⟩ := hp x
    exact ⟨⟨e, he⟩⟩
  letI : DiscreteTopology (p ⁻¹' {x}) :=
    (cov x).discreteTopology_fiber
  let t₀ : Bundle.Trivialization (p ⁻¹' {x}) p := (cov x).toTrivialization
  obtain ⟨U, ⟨hUopen, hxU, hUPath⟩, hUsub⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp
      (t₀.open_baseSet.mem_nhds (cov x).mem_toTrivialization_baseSet)
  let t : Bundle.Trivialization (p ⁻¹' {x}) p := t₀.restrOpen U hUopen
  have htbase : t.baseSet = U := by
    change t₀.baseSet ∩ U = U
    exact Set.inter_eq_right.mpr hUsub
  have hxbase : x ∈ t.baseSet := htbase.symm ▸ hxU
  have htpre : IsPreconnected t.baseSet :=
    htbase ▸ hUPath.isConnected.isPreconnected
  let I := r ⁻¹' {x}
  letI : DiscreteTopology I :=
    HatcherLib.IsLocalHomeomorph.discreteTopology_fiber hrlocal x
  have hrsurj : Function.Surjective r := subgroupOrbitMap_surjective hp S
  letI : Nonempty I := by
    obtain ⟨z, hz⟩ := hrsurj x
    exact ⟨⟨z, hz⟩⟩
  let index (i : p ⁻¹' {x}) : I :=
    ⟨q (t.invFun (x, i)), by
      change r (q (t.invFun (x, i))) = x
      change p (t.invFun (x, i)) = x
      exact t.proj_symm_apply' hxbase⟩
  let W (b : I) : Set (OrbitSpace S E) :=
    ⋃ i : p ⁻¹' {x}, ⋃ _h : index i = b, q '' trivializationSheet t i
  have hWopen (b : I) : IsOpen (W b) := by
    dsimp only [W]
    apply isOpen_iUnion
    intro i
    apply isOpen_iUnion
    intro _hi
    exact hqcov.isOpenMap _ (trivializationSheet_isOpen t i)
  have hindex_surj : Function.Surjective index := by
    intro b
    obtain ⟨e, heq⟩ := hqsurj b.1
    have hpe : p e = x := by
      calc
        p e = r (q e) := rfl
        _ = r b.1 := congrArg r heq
        _ = x := b.2
    have hesource : e ∈ t.source := t.mem_source.mpr (hpe ▸ hxbase)
    let i : p ⁻¹' {x} := (t e).2
    have heSheet : e ∈ trivializationSheet t i := ⟨hesource, rfl⟩
    refine ⟨i, Subtype.ext ?_⟩
    change q (t.invFun (x, i)) = b.1
    rw [show t.invFun (x, i) = e by
      simpa only [i, hpe] using trivialization_invFun_eq_of_mem_sheet t heSheet]
    exact heq
  have hWsurj (b : I) : (W b).SurjOn r t.baseSet := by
    obtain ⟨i, hi⟩ := hindex_surj b
    intro y hy
    obtain ⟨e, he, hpe⟩ := trivializationSheet_surjOn t i hy
    refine ⟨q e, ?_, ?_⟩
    · exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, ⟨e, he, rfl⟩⟩⟩
    · change p e = y
      exact hpe
  have hWinj (b : I) : (W b).InjOn r := by
    intro z hz z' hz' hr
    rcases Set.mem_iUnion.mp hz with ⟨i, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hi, hz⟩
    rcases hz with ⟨e, he, hqe⟩
    rcases Set.mem_iUnion.mp hz' with ⟨j, hz'⟩
    rcases Set.mem_iUnion.mp hz' with ⟨hj, hz'⟩
    rcases hz' with ⟨e', he', hqe'⟩
    have href : q (t.invFun (x, i)) = q (t.invFun (x, j)) :=
      congrArg Subtype.val (hi.trans hj.symm)
    have hrefi := trivialization_invFun_mem_sheet t hxbase i
    have hrefj := trivialization_invFun_mem_sheet t hxbase j
    have hprop := orbitProjection_eq_of_trivializationSheets
      cov t htpre S hrefi hrefj href
    have hpe : p e = p e' := by
      calc
        p e = r (q e) := rfl
        _ = r z := congrArg r hqe
        _ = r z' := hr
        _ = r (q e') := congrArg r hqe'.symm
        _ = p e' := rfl
    have hpebase : p e ∈ t.baseSet := t.mem_source.mp he.1
    have hsections := hprop (p e) hpebase
    rw [← hqe, ← hqe']
    calc
      q e = q (t.invFun (p e, i)) :=
        congrArg q (trivialization_invFun_eq_of_mem_sheet t he).symm
      _ = q (t.invFun (p e, j)) := hsections
      _ = q (t.invFun (p e', j)) := by rw [hpe]
      _ = q e' := congrArg q (trivialization_invFun_eq_of_mem_sheet t he')
  have hWdisjoint : Pairwise fun b b' ↦ Disjoint (W b) (W b') := by
    intro b b' hne
    rw [Set.disjoint_left]
    intro z hz hz'
    rcases Set.mem_iUnion.mp hz with ⟨i, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hi, hz⟩
    rcases hz with ⟨e, he, hqe⟩
    rcases Set.mem_iUnion.mp hz' with ⟨j, hz'⟩
    rcases Set.mem_iUnion.mp hz' with ⟨hj, hz'⟩
    rcases hz' with ⟨e', he', hqe'⟩
    have hqee' : q e = q e' := hqe.trans hqe'.symm
    have href := orbitProjection_eq_of_trivializationSheets
      cov t htpre S he he' hqee' x hxbase
    apply hne
    calc
      b = index i := hi.symm
      _ = index j := Subtype.ext href
      _ = b' := hj
  have hopen_iff (b : I) {A : Set X} (hA : A ⊆ t.baseSet) :
      IsOpen A ↔ IsOpen (r ⁻¹' A ∩ W b) := by
    constructor
    · intro hAopen
      exact (hAopen.preimage hrcont).inter (hWopen b)
    · intro hopen
      have himage : r '' (r ⁻¹' A ∩ W b) = A := by
        apply Set.Subset.antisymm
        · rintro _ ⟨z, ⟨hzA, _hzW⟩, rfl⟩
          exact hzA
        · intro y hy
          obtain ⟨z, hzW, hrz⟩ := hWsurj b (hA hy)
          have hzA : r z ∈ A := hrz.symm ▸ hy
          exact ⟨z, ⟨hzA, hzW⟩, hrz⟩
      rw [← himage]
      exact hrlocal.isOpenMap _ hopen
  have hexhaustive : r ⁻¹' t.baseSet ⊆ ⋃ b, W b := by
    intro z hz
    obtain ⟨e, heq⟩ := hqsurj z
    have hpebase : p e ∈ t.baseSet := by
      change r z ∈ t.baseSet at hz
      have hpez : p e = r z := by
        calc
          p e = r (q e) := rfl
          _ = r z := congrArg r heq
      rw [hpez]
      exact hz
    have hesource : e ∈ t.source := t.mem_source.mpr hpebase
    let i : p ⁻¹' {x} := (t e).2
    have heSheet : e ∈ trivializationSheet t i := ⟨hesource, rfl⟩
    apply Set.mem_iUnion.2
    refine ⟨index i, ?_⟩
    exact Set.mem_iUnion.2 ⟨i,
      Set.mem_iUnion.2 ⟨rfl, ⟨e, heSheet, heq⟩⟩⟩
  let T : Bundle.Trivialization I r :=
    t.open_baseSet.trivializationDiscrete W t.baseSet hopen_iff hWinj hWsurj
      hWdisjoint hexhaustive
  have hxT : x ∈ T.baseSet := by
    change x ∈ t.baseSet
    exact hxbase
  exact (IsEvenlyCovered.of_trivialization hxT).to_isEvenlyCovered_preimage

/-- Monodromy for the intermediate orbit covering is obtained by projecting
monodromy in the original covering. -/
private theorem subgroupOrbitMap_monodromy
    (cov : CoveringMap p) (S : Subgroup (DeckTransformationGroup p))
    (covS : CoveringMap (subgroupOrbitMap (p := p) S))
    {x y : X} (gamma : Path.Homotopic.Quotient x y) (e : E) (he : p e = x) :
    covS.monodromy gamma
        ⟨orbitProjection S E e, by simpa using he⟩ =
      ⟨orbitProjection S E (cov.monodromy gamma ⟨e, he⟩).1, by
        change p (cov.monodromy gamma ⟨e, he⟩).1 = y
        exact (cov.monodromy gamma ⟨e, he⟩).2⟩ := by
  apply Subtype.ext
  induction gamma using Path.Homotopic.Quotient.ind with
  | mk gamma =>
      let Gamma : C(unitInterval, OrbitSpace S E) :=
        ⟨fun t ↦ orbitProjection S E (cov.liftPath gamma e (gamma.source.trans he.symm) t),
          orbitProjection_continuous.comp
            (cov.liftPath gamma e (gamma.source.trans he.symm)).continuous⟩
      have hGamma : Gamma = covS.liftPath gamma (orbitProjection S E e)
          (gamma.source.trans (by simpa using he.symm)) := by
        apply (covS.eq_liftPath_iff' (gamma.source.trans (by simpa using he.symm))).2
        constructor
        · funext t
          change p (cov.liftPath gamma e (gamma.source.trans he.symm) t) = gamma t
          exact congrFun (cov.liftPath_lifts gamma e (gamma.source.trans he.symm)) t
        · change orbitProjection S E
              (cov.liftPath gamma e (gamma.source.trans he.symm) 0) =
            orbitProjection S E e
          rw [cov.liftPath_zero]
      change covS.liftPath gamma (orbitProjection S E e)
          (gamma.source.trans (by simpa using he.symm)) 1 =
        orbitProjection S E
          (cov.liftPath gamma e (gamma.source.trans he.symm) 1)
      exact (congrArg (fun f ↦ f 1) hGamma).symm

/-- Normal-cover monodromy sends the chosen point to the endpoint of the
corresponding lifted `PiOne` loop. -/
theorem normalCoverPiOneDeckHom_smul_basepoint
    (h : IsNormalCovering p) [PathConnectedSpace E] (e₀ : E)
    (g : PiOne (p e₀)) :
    normalCoverPiOneDeckHom h e₀ g • e₀ =
      (coveringEndpoint h.1 e₀ g.unop).1 := by
  change normalCoverDeck h e₀ g.unop⁻¹ • e₀ =
    (coveringEndpoint h.1 e₀ g.unop).1
  rw [normalCoverDeck_apply]
  simp

/-- Every universal cover is normal. -/
theorem IsUniversalCoveringMap.isNormalCovering
    (hu : IsUniversalCoveringMap p) (e₀ : E) : IsNormalCovering p := by
  letI : PathConnectedSpace X := hu.pathConnectedSpace
  letI : LocallyPathConnectedSpace X := hu.locPathConnectedSpace
  letI : SimplyConnectedSpace E := hu.simplyConnectedSpace
  letI : PathConnectedSpace E := inferInstance
  apply (isNormalCovering_iff_piOneImageSubgroup_normal hu.coveringMap e₀).2
  rw [coveringPiOneImageSubgroup_eq_bot_of_simplyConnected]
  infer_instance

/-- For a universal cover, the subgroup induced by the intermediate orbit
cover is exactly the preimage of the chosen deck subgroup under monodromy. -/
theorem coveringPiOneImageSubgroup_subgroupOrbitMap
    (hu : IsUniversalCoveringMap p) (e₀ : E)
    (S : Subgroup (DeckTransformationGroup p)) :
    letI : PathConnectedSpace X := hu.pathConnectedSpace
    letI : LocallyPathConnectedSpace X := hu.locPathConnectedSpace
    letI : SimplyConnectedSpace E := hu.simplyConnectedSpace
    letI : PathConnectedSpace E := inferInstance
    let covS := subgroupOrbitMap_isCoveringMap hu.coveringMap hu.surjective S
    coveringPiOneImageSubgroup covS (orbitProjection S E e₀) =
      S.comap (normalCoverPiOneDeckHom
        (hu.isNormalCovering e₀) e₀) := by
  letI : PathConnectedSpace X := hu.pathConnectedSpace
  letI : LocallyPathConnectedSpace X := hu.locPathConnectedSpace
  letI : SimplyConnectedSpace E := hu.simplyConnectedSpace
  letI : PathConnectedSpace E := inferInstance
  let hnormal : IsNormalCovering p := hu.isNormalCovering e₀
  let cov : CoveringMap p := hnormal.1
  let covS := subgroupOrbitMap_isCoveringMap cov hu.surjective S
  apply Subgroup.ext
  intro g
  rw [coveringPiOneImageSubgroup_eq_op]
  change g.unop ∈ coveringImageSubgroup covS (orbitProjection S E e₀) ↔
    normalCoverPiOneDeckHom hnormal e₀ g ∈ S
  rw [mem_coveringImageSubgroup_iff_monodromy_fixed]
  rw [subgroupOrbitMap_monodromy cov S covS
    (FundamentalGroup.toPath g.unop) e₀ rfl]
  rw [Subtype.ext_iff]
  change orbitProjection S E (coveringEndpoint cov e₀ g.unop).1 =
      orbitProjection S E e₀ ↔ normalCoverPiOneDeckHom hnormal e₀ g ∈ S
  have hdeck : normalCoverPiOneDeckHom hnormal e₀ g • e₀ =
      (coveringEndpoint cov e₀ g.unop).1 := by
    exact normalCoverPiOneDeckHom_smul_basepoint hnormal e₀ g
  rw [← hdeck]
  constructor
  · intro hq
    obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp
      ((orbitProjection_eq_iff (G := S) (Y := E)
        (normalCoverPiOneDeckHom hnormal e₀ g • e₀) e₀).mp hq)
    change (s.1 : DeckTransformationGroup p) • e₀ =
      normalCoverPiOneDeckHom hnormal e₀ g • e₀ at hs
    have heq : (s.1 : DeckTransformationGroup p) =
        normalCoverPiOneDeckHom hnormal e₀ g :=
      deckTransformation_ext cov hs
    exact heq ▸ s.2
  · intro hg
    let s : S := ⟨normalCoverPiOneDeckHom hnormal e₀ g, hg⟩
    exact orbitProjection_smul s e₀

/-- The deck subgroup corresponding to a subgroup of the base fundamental
group under universal-cover monodromy. -/
noncomputable def universalCoverDeckSubgroup
    (hu : IsUniversalCoveringMap p) (e₀ : E)
    (H : Subgroup (PiOne (p e₀))) : Subgroup (DeckTransformationGroup p) := by
  letI : PathConnectedSpace X := hu.pathConnectedSpace
  letI : LocallyPathConnectedSpace X := hu.locPathConnectedSpace
  letI : SimplyConnectedSpace E := hu.simplyConnectedSpace
  letI : PathConnectedSpace E := inferInstance
  exact H.map (normalCoverPiOneDeckHom (hu.isNormalCovering e₀) e₀)

/-- The orbit cover attached to `H` induces exactly `H` on `PiOne`. -/
theorem coveringPiOneImageSubgroup_universalCoverDeckSubgroup
    (hu : IsUniversalCoveringMap p) (e₀ : E)
    (H : Subgroup (PiOne (p e₀))) :
    letI : PathConnectedSpace X := hu.pathConnectedSpace
    letI : LocallyPathConnectedSpace X := hu.locPathConnectedSpace
    letI : SimplyConnectedSpace E := hu.simplyConnectedSpace
    letI : PathConnectedSpace E := inferInstance
    let S := universalCoverDeckSubgroup hu e₀ H
    let covS := subgroupOrbitMap_isCoveringMap hu.coveringMap hu.surjective S
    coveringPiOneImageSubgroup covS (orbitProjection S E e₀) = H := by
  letI : PathConnectedSpace X := hu.pathConnectedSpace
  letI : LocallyPathConnectedSpace X := hu.locPathConnectedSpace
  letI : SimplyConnectedSpace E := hu.simplyConnectedSpace
  letI : PathConnectedSpace E := inferInstance
  let hnormal : IsNormalCovering p := hu.isNormalCovering e₀
  let phi := normalCoverPiOneDeckHom hnormal e₀
  have hker : phi.ker = ⊥ := by
    rw [normalCoverPiOneDeckHom_ker]
    exact coveringPiOneImageSubgroup_eq_bot_of_simplyConnected hu.coveringMap e₀
  have hphi : Function.Injective phi :=
    (MonoidHom.ker_eq_bot_iff phi).mp hker
  dsimp only
  rw [coveringPiOneImageSubgroup_subgroupOrbitMap (hu := hu) (e₀ := e₀)]
  change (H.map phi).comap phi = H
  exact Subgroup.comap_map_eq_self_of_injective hphi H

/-- Hatcher Proposition 1.36: every subgroup of the fundamental group is
realized by a path-connected covering space.  The displayed `let` bindings
give the covering, its total space, and its chosen basepoint explicitly. -/
theorem exists_coveringSpace_for_subgroup
    [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (hsemi : SemilocallySimplyConnected X) (x₀ : X)
    (H : Subgroup (PiOne x₀)) :
    letI : TopologicalSpace (UniversalCoverConstruction.Space x₀) :=
      UniversalCoverConstruction.universalCoverTopology hsemi
    letI : PathConnectedSpace (UniversalCoverConstruction.Space x₀) :=
      UniversalCoverConstruction.universalCover_pathConnectedSpace hsemi
    let p₀ : UniversalCoverConstruction.Space x₀ → X :=
      UniversalCoverConstruction.endpoint
    let e₀ : UniversalCoverConstruction.Space x₀ :=
      ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩
    let hu : IsUniversalCoveringMap p₀ :=
      UniversalCoverConstruction.universalCoverEndpoint_isUniversalCoveringMap hsemi
    let S := universalCoverDeckSubgroup hu e₀ H
    let pH := subgroupOrbitMap (p := p₀) S
    let eH := orbitProjection S (UniversalCoverConstruction.Space x₀) e₀
    let covH := subgroupOrbitMap_isCoveringMap hu.coveringMap hu.surjective S
    CoveringMap pH ∧ coveringPiOneImageSubgroup covH eH = H := by
  letI : TopologicalSpace (UniversalCoverConstruction.Space x₀) :=
    UniversalCoverConstruction.universalCoverTopology hsemi
  letI : PathConnectedSpace (UniversalCoverConstruction.Space x₀) :=
    UniversalCoverConstruction.universalCover_pathConnectedSpace hsemi
  let p₀ : UniversalCoverConstruction.Space x₀ → X :=
    UniversalCoverConstruction.endpoint
  let e₀ : UniversalCoverConstruction.Space x₀ :=
    ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩
  let hu : IsUniversalCoveringMap p₀ :=
    UniversalCoverConstruction.universalCoverEndpoint_isUniversalCoveringMap hsemi
  let S := universalCoverDeckSubgroup hu e₀ H
  let pH := subgroupOrbitMap (p := p₀) S
  let eH := orbitProjection S (UniversalCoverConstruction.Space x₀) e₀
  let covH := subgroupOrbitMap_isCoveringMap hu.coveringMap hu.surjective S
  exact ⟨covH, coveringPiOneImageSubgroup_universalCoverDeckSubgroup hu e₀ H⟩

omit [TopologicalSpace X] in
theorem subgroupOrbitSpace_pathConnectedSpace
    [PathConnectedSpace E] (S : Subgroup (DeckTransformationGroup p)) :
    PathConnectedSpace (OrbitSpace S E) := by
  infer_instance

end
end HatcherLib
