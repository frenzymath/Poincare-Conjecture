import HatcherLib.Ch1.CoveringIndex
import HatcherLib.Ch1.CoveringClassification
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Topology.Covering.Quotient

/-!
# Chapter 1: deck transformations and group actions

This file packages Hatcher's group-action language in terms of mathlib's
`MulAction` and orbit quotient.  The neighborhood condition for a covering
space action directly supplies the local trivializations for the quotient
map.  Deck transformations are realized as the subgroup of self-homeomorphisms
over the base.
-/

namespace HatcherLib

noncomputable section

universe u v w

/-! ## Actions and orbit spaces -/

/-- An action of a group on a space, represented as a homomorphism to its
self-homeomorphism group. -/
abbrev GroupAction (G : Type u) (Y : Type v) [Group G] [TopologicalSpace Y] :=
  G →* (Y ≃ₜ Y)

namespace GroupAction

variable {G : Type u} {Y : Type v} [Group G] [TopologicalSpace Y]

/-- The multiplicative action associated to an action by homeomorphisms. -/
@[reducible] protected def toMulAction (rho : GroupAction G Y) : MulAction G Y where
  smul g y := rho g y
  one_smul y := by
    change rho 1 y = y
    rw [rho.map_one]
    rfl
  mul_smul g h y := by
    change rho (g * h) y = rho g (rho h y)
    rw [rho.map_mul]
    rfl

/-- Every action by homeomorphisms is continuous in the space variable. -/
@[reducible] protected def toContinuousConstSMul (rho : GroupAction G Y) :
    letI := rho.toMulAction
    ContinuousConstSMul G Y := by
  letI := rho.toMulAction
  exact ⟨fun g ↦ (rho g).continuous⟩

end GroupAction

section AbstractAction

variable {G : Type u} {Y : Type v} [Group G] [MulAction G Y]

/-- An action is free when no nonidentity group element fixes a point. -/
def IsFreeAction (G : Type u) (Y : Type v) [Group G] [MulAction G Y] : Prop :=
  ∀ g : G, ∀ y : Y, g • y = y → g = 1

/-- Freeness is equivalent to cancellation in each orbit map. -/
theorem isFreeAction_iff_isCancelSMul :
    IsFreeAction G Y ↔ IsCancelSMul G Y :=
  isCancelSMul_iff_eq_one_of_smul_eq.symm

variable [TopologicalSpace Y]

/-- Hatcher's local-disjointness condition for a covering space action. -/
def IsCoveringSpaceAction (G : Type u) (Y : Type v)
    [Group G] [TopologicalSpace Y] [MulAction G Y] : Prop :=
  ∀ y : Y, ∃ U ∈ nhds y,
    ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1

/-- The local-disjointness condition implies that the action is free. -/
theorem IsCoveringSpaceAction.isFree (h : IsCoveringSpaceAction G Y) :
    IsFreeAction G Y := by
  intro g y hgy
  obtain ⟨U, hyU, hU⟩ := h y
  have hy : y ∈ U := mem_of_mem_nhds hyU
  apply hU g
  exact ⟨y, ⟨y, hy, hgy⟩, hy⟩

namespace GroupAction

/-- A group action by homeomorphisms is a covering space action when its
associated action satisfies the local-disjointness condition. -/
def IsCovering (ρ : GroupAction G Y) : Prop :=
  letI := ρ.toMulAction
  IsCoveringSpaceAction G Y

/-- A group action by homeomorphisms is free when only the identity fixes a
point. -/
def IsFree (ρ : GroupAction G Y) : Prop :=
  letI := ρ.toMulAction
  IsFreeAction G Y

omit [MulAction G Y] in
/-- Every covering space action by homeomorphisms is free. -/
theorem IsCovering.isFree {ρ : GroupAction G Y} (h : ρ.IsCovering) : ρ.IsFree := by
  letI := ρ.toMulAction
  exact IsCoveringSpaceAction.isFree h

end GroupAction

/-- The type of orbits of a group action.  Its topology is the quotient
topology inherited from `Y`. -/
abbrev OrbitSpace (G : Type u) (Y : Type v) [Group G] [MulAction G Y] :=
  MulAction.orbitRel.Quotient G Y

/-- The projection from a space to its orbit space. -/
def orbitProjection (G : Type u) (Y : Type v) [Group G] [MulAction G Y] :
    Y → OrbitSpace G Y :=
  Quotient.mk (MulAction.orbitRel G Y)

/-- The orbit projection is continuous. -/
theorem orbitProjection_continuous :
    Continuous (orbitProjection G Y) := by
  change Continuous
    (@Quotient.mk' Y (MulAction.orbitRel G Y) :
      Y → Quotient (MulAction.orbitRel G Y))
  exact continuous_quotient_mk'

omit [TopologicalSpace Y] in
/-- Two points have the same image in the orbit space exactly when they lie
in the same orbit. -/
theorem orbitProjection_eq_iff (y y' : Y) :
    orbitProjection G Y y = orbitProjection G Y y' ↔
      y ∈ MulAction.orbit G y' := by
  change (Quotient.mk'' y : OrbitSpace G Y) = Quotient.mk'' y' ↔ _
  exact Quotient.eq''.trans MulAction.orbitRel_apply

omit [TopologicalSpace Y] in
/-- The orbit projection is invariant under the action. -/
@[simp] theorem orbitProjection_smul (g : G) (y : Y) :
    orbitProjection G Y (g • y) = orbitProjection G Y y :=
  (orbitProjection_eq_iff (G := G) (Y := Y) (g • y) y).2
    (MulAction.mem_orbit_iff.2 ⟨g, rfl⟩)

/-- A covering space action makes the orbit projection a quotient covering
map. -/
theorem orbitProjection_isQuotientCoveringMap [ContinuousConstSMul G Y]
    (h : IsCoveringSpaceAction G Y) :
    IsQuotientCoveringMap (orbitProjection G Y) G where
  toIsQuotientMap := by
    change Topology.IsQuotientMap
      (@Quotient.mk' Y (MulAction.orbitRel G Y) :
        Y → Quotient (MulAction.orbitRel G Y))
    exact isQuotientMap_quotient_mk'
  toContinuousConstSMul := inferInstance
  apply_eq_iff_mem_orbit := fun {y y'} ↦
    orbitProjection_eq_iff (G := G) (Y := Y) y y'
  disjoint := h

/-- In particular, the orbit projection of a covering space action is a
covering map. -/
theorem orbitProjection_isCoveringMap [ContinuousConstSMul G Y]
    (h : IsCoveringSpaceAction G Y) :
    CoveringMap (orbitProjection G Y) :=
  (orbitProjection_isQuotientCoveringMap h).isCoveringMap

end AbstractAction

/-! ## A free action that is not a covering-space action -/

/-- The additive group of rationals acts on the real line by translations. -/
def rationalTranslationAction : GroupAction (Multiplicative ℚ) ℝ where
  toFun q := Homeomorph.addLeft ((q.toAdd : ℚ) : ℝ)
  map_one' := by
    ext x
    simp
  map_mul' q r := by
    ext x
    simp [add_assoc]

/-- Rational translation acts freely on the real line. -/
theorem rationalTranslationAction_isFree : rationalTranslationAction.IsFree := by
  letI := rationalTranslationAction.toMulAction
  intro q x h
  change ((q.toAdd : ℚ) : ℝ) + x = x at h
  have hq : ((q.toAdd : ℚ) : ℝ) = 0 := by linarith
  change q.toAdd = 0
  exact_mod_cast hq

/-- Freeness alone does not imply Hatcher's local-disjointness condition:
arbitrarily small nonzero rational translations overlap every neighborhood. -/
theorem rationalTranslationAction_not_isCovering :
    ¬ rationalTranslationAction.IsCovering := by
  intro h
  letI := rationalTranslationAction.toMulAction
  obtain ⟨U, hU, hdisj⟩ := h (0 : ℝ)
  rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, hball⟩
  obtain ⟨q : ℚ, hqpos, hqε⟩ := exists_pos_rat_lt hε
  have hqposR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have h0U : (0 : ℝ) ∈ U := mem_of_mem_nhds hU
  have hqU : (q : ℝ) ∈ U := hball (by
    rw [Metric.mem_ball]
    simpa [Real.dist_eq, abs_of_pos hqposR] using hqε)
  have hinter : (((Multiplicative.ofAdd q) • ·) '' U ∩ U).Nonempty := by
    refine ⟨(q : ℝ), ?_, hqU⟩
    refine ⟨0, h0U, ?_⟩
    change (((q : ℚ) : ℝ) + 0) = (q : ℝ)
    simp
  have hone := hdisj (Multiplicative.ofAdd q) hinter
  have hqzero : q = 0 := by
    change q = 0 at hone
    exact hone
  exact (ne_of_gt hqpos) hqzero

/-! ## Deck transformations -/

section DeckTransformations

variable {E : Type u} {X : Type v} [TopologicalSpace E]
variable {p : E → X}

/-- The deck transformation group of `p`, as the subgroup of
self-homeomorphisms preserving `p`. -/
def DeckTransformationGroup (p : E → X) : Subgroup (E ≃ₜ E) where
  carrier := {phi | p ∘ phi = p}
  one_mem' := rfl
  mul_mem' {phi psi} hphi hpsi := by
    ext e
    calc
      p ((phi * psi) e) = p (psi e) := by
        simpa using congrFun hphi (psi e)
      _ = p e := by
        simpa using congrFun hpsi e
  inv_mem' {phi} hphi := by
    ext e
    simpa using (congrFun hphi (phi⁻¹ e)).symm

/-- Membership in the deck group is preservation of the projection. -/
theorem mem_deckTransformationGroup_iff (phi : E ≃ₜ E) :
    phi ∈ DeckTransformationGroup p ↔ p ∘ phi = p :=
  Iff.rfl

/-- Deck transformations act on the total space by evaluation. -/
instance deckTransformationGroupMulAction :
    MulAction (DeckTransformationGroup p) E where
  smul phi e := (phi : E ≃ₜ E) e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Each deck transformation acts continuously. -/
instance deckTransformationGroupContinuousConstSMul :
    ContinuousConstSMul (DeckTransformationGroup p) E where
  continuous_const_smul phi := (phi : E ≃ₜ E).continuous

/-- The deck-group action is evaluation of the underlying homeomorphism. -/
@[simp] theorem deckTransformation_smul_def
    (phi : DeckTransformationGroup p) (e : E) :
    phi • e = (phi : E ≃ₜ E) e :=
  rfl

/-- A deck transformation preserves the projection pointwise. -/
theorem deckTransformation_preserves_projection
    (phi : DeckTransformationGroup p) (e : E) :
    p (phi • e) = p e := by
  simpa using congrFun phi.2 e

variable [TopologicalSpace X]

/-- Over a preconnected covering space, a deck transformation is determined
by its value at one point. -/
theorem deckTransformation_ext (cov : CoveringMap p) [PreconnectedSpace E]
    {phi psi : DeckTransformationGroup p} {e : E}
    (h : phi • e = psi • e) : phi = psi := by
  apply Subtype.ext
  apply Homeomorph.ext
  have hfun : (phi : E → E) = (psi : E → E) :=
    cov.eq_of_comp_eq (phi : E ≃ₜ E).continuous (psi : E ≃ₜ E).continuous
      (phi.2.trans psi.2.symm) e h
  exact congrFun hfun

/-- A covering map supplies the local-disjointness condition for its full deck
group.  The neighborhood is one sheet of an evenly covered neighborhood. -/
theorem deckTransformationGroup_isCoveringSpaceAction (cov : CoveringMap p)
    [PreconnectedSpace E] :
    IsCoveringSpaceAction (DeckTransformationGroup p) E := by
  intro e
  letI : Nonempty (p ⁻¹' {p e}) := ⟨⟨e, rfl⟩⟩
  let t := (cov (p e)).toTrivialization
  haveI : DiscreteTopology (p ⁻¹' {p e}) :=
    (cov (p e)).discreteTopology_fiber
  let U : Set E := t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e).2}
  have heU : e ∈ U := by
    exact ⟨t.mem_source.mpr (cov (p e)).mem_toTrivialization_baseSet, rfl⟩
  have hUo : IsOpen U := by
    exact t.continuousOn_toFun.isOpen_inter_preimage t.open_source
      (continuous_snd.isOpen_preimage _ (isOpen_discrete _))
  refine ⟨U, hUo.mem_nhds heU, ?_⟩
  intro phi hphi
  obtain ⟨z, ⟨y, hyU, rfl⟩, hzU⟩ := hphi
  have hp : p (phi • y) = p y := deckTransformation_preserves_projection phi y
  have ht : t y = t (phi • y) := by
    apply Prod.ext
    · calc
        (t y).1 = p y := t.coe_fst hyU.1
        _ = p (phi • y) := hp.symm
        _ = (t (phi • y)).1 := (t.coe_fst hzU.1).symm
    · exact hyU.2.trans hzU.2.symm
  have hyz : y = phi • y := t.injOn hyU.1 hzU.1 ht
  apply deckTransformation_ext cov (e := y)
  exact hyz.symm

/-- Restricting the deck action to a subgroup preserves the local-disjointness
condition.  Install the displayed action with `MulAction.compHom` at use sites. -/
theorem subgroup_deckTransformationGroup_isCoveringSpaceAction
    (cov : CoveringMap p) [PreconnectedSpace E]
    (S : Subgroup (DeckTransformationGroup p)) :
    letI : MulAction S E := MulAction.compHom E S.subtype
    IsCoveringSpaceAction S E := by
  letI : MulAction S E := MulAction.compHom E S.subtype
  intro e
  obtain ⟨U, heU, hU⟩ := deckTransformationGroup_isCoveringSpaceAction cov e
  refine ⟨U, heU, ?_⟩
  intro s hs
  apply Subtype.ext
  exact hU (s : DeckTransformationGroup p) hs

/-- The deck group of a preconnected covering acts freely. -/
theorem deckTransformationGroup_isFree (cov : CoveringMap p)
    [PreconnectedSpace E] :
    IsCancelSMul (DeckTransformationGroup p) E := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro phi e hphi
  exact deckTransformation_ext cov (hphi.trans (one_smul _ _).symm)

/-- A covering is normal when its deck group acts transitively on every
fiber. -/
def IsNormalCovering (p : E → X) : Prop :=
  CoveringMap p ∧ Function.Surjective p ∧
    ∀ ⦃e e' : E⦄, p e = p e' →
      ∃ phi : DeckTransformationGroup p, phi • e = e'

end DeckTransformations

/-! ## A normal cover as the quotient by its deck group -/

section NormalCoverOrbit

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}

/-- The projection of a normal cover descends to its deck-orbit space. -/
def normalCoverOrbitMap : OrbitSpace (DeckTransformationGroup p) E → X :=
  Quotient.lift p fun a b hab => by
    obtain ⟨phi, hphi⟩ :=
      MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hphi]
    exact deckTransformation_preserves_projection phi b

omit [TopologicalSpace X] in
/-- The descended orbit map agrees with the covering projection. -/
@[simp] theorem normalCoverOrbitMap_mk (e : E) :
    normalCoverOrbitMap (p := p)
        (orbitProjection (DeckTransformationGroup p) E e) = p e :=
  rfl

/-- The descended map from the deck-orbit space is continuous. -/
theorem normalCoverOrbitMap_continuous (cov : CoveringMap p) :
    Continuous (normalCoverOrbitMap (p := p)) :=
  cov.continuous.quotient_lift fun a b hab => by
    obtain ⟨phi, hphi⟩ :=
      MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hphi]
    exact deckTransformation_preserves_projection phi b

/-- For a normal covering, the descended map from the deck-orbit space is
bijective. -/
theorem normalCoverOrbitMap_bijective (h : IsNormalCovering p) :
    Function.Bijective (normalCoverOrbitMap (p := p)) := by
  constructor
  · intro a b hab
    induction a using Quotient.ind with
    | _ a =>
      induction b using Quotient.ind with
      | _ b =>
        apply (orbitProjection_eq_iff
          (G := DeckTransformationGroup p) (Y := E) a b).2
        obtain ⟨phi, hphi⟩ := h.2.2 hab
        exact MulAction.mem_orbit_iff.2 ⟨phi⁻¹, by
          rw [← hphi, inv_smul_smul]⟩
  · intro x
    obtain ⟨e, rfl⟩ := h.2.1 x
    exact ⟨orbitProjection (DeckTransformationGroup p) E e, rfl⟩

/-- The descended map from a normal covering is open. -/
theorem normalCoverOrbitMap_isOpenMap (h : IsNormalCovering p) :
    IsOpenMap (normalCoverOrbitMap (p := p)) := by
  intro V hV
  rw [show normalCoverOrbitMap (p := p) '' V =
      p '' (orbitProjection (DeckTransformationGroup p) E ⁻¹' V) by
    ext x
    constructor
    · rintro ⟨q, hqV, rfl⟩
      obtain ⟨e, rfl⟩ := Quotient.mk''_surjective q
      exact ⟨e, hqV, rfl⟩
    · rintro ⟨e, heV, rfl⟩
      exact ⟨orbitProjection (DeckTransformationGroup p) E e, heV, rfl⟩]
  exact h.1.isOpenMap _ (hV.preimage orbitProjection_continuous)

/-- A surjective normal covering identifies its base homeomorphically with the
orbit space of its deck-transformation action. -/
noncomputable def normalCoverOrbitHomeomorph (h : IsNormalCovering p) :
    OrbitSpace (DeckTransformationGroup p) E ≃ₜ X :=
  (Equiv.ofBijective (normalCoverOrbitMap (p := p))
    (normalCoverOrbitMap_bijective h)).toHomeomorphOfContinuousOpen
      (normalCoverOrbitMap_continuous h.1)
      (normalCoverOrbitMap_isOpenMap h)

end NormalCoverOrbit

/-! ## Deck transformations of an orbit covering -/

section OrbitDeckTransformations

variable {G : Type u} {Y : Type v}
  [Group G] [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]

/-- Each element of the acting group gives a deck transformation of the
orbit projection. -/
def actionToDeckTransformation :
    G →* DeckTransformationGroup (orbitProjection G Y) where
  toFun g := ⟨Homeomorph.smul g, by
    funext y
    exact orbitProjection_smul g y⟩
  map_one' := by
    apply Subtype.ext
    ext y
    exact one_smul G y
  map_mul' g h := by
    apply Subtype.ext
    ext y
    exact mul_smul g h y

/-- The induced deck transformation acts as the original group element. -/
@[simp] theorem actionToDeckTransformation_smul (g : G) (y : Y) :
    actionToDeckTransformation (Y := Y) g • y = g • y :=
  rfl

/-- The orbit covering of a covering space action is normal. -/
theorem orbitProjection_isNormalCovering
    (h : IsCoveringSpaceAction G Y) :
    IsNormalCovering (orbitProjection G Y) := by
  refine ⟨orbitProjection_isCoveringMap h, Quotient.mk''_surjective, ?_⟩
  intro y y' hyy'
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp
    ((orbitProjection_eq_iff (G := G) (Y := Y) y y').mp hyy')
  refine ⟨actionToDeckTransformation (Y := Y) g⁻¹, ?_⟩
  change g⁻¹ • y = y'
  rw [← hg, inv_smul_smul]

/-- A free action embeds in the deck group of its orbit projection. -/
theorem actionToDeckTransformation_injective [Nonempty Y]
    (h : IsFreeAction G Y) :
    Function.Injective (actionToDeckTransformation (G := G) (Y := Y)) := by
  intro g k hgk
  obtain ⟨y⟩ := ‹Nonempty Y›
  have hvalue := congrArg
    (fun phi : DeckTransformationGroup (orbitProjection G Y) ↦ phi • y) hgk
  have hgk_smul : g • y = k • y := by
    change (actionToDeckTransformation (Y := Y) g) • y =
      (actionToDeckTransformation (Y := Y) k) • y
    exact hvalue
  have hfix : (k⁻¹ * g) • y = y := by
    rw [mul_smul, hgk_smul, inv_smul_smul]
  exact (inv_mul_eq_one.mp (h (k⁻¹ * g) y hfix)).symm

/-- If the orbit covering is preconnected, every deck transformation comes
from the original action. -/
theorem actionToDeckTransformation_surjective [PreconnectedSpace Y] [Nonempty Y]
    (h : IsCoveringSpaceAction G Y) :
    Function.Surjective (actionToDeckTransformation (G := G) (Y := Y)) := by
  intro phi
  obtain ⟨y⟩ := ‹Nonempty Y›
  have heq :
      orbitProjection G Y (phi • y) = orbitProjection G Y y :=
    deckTransformation_preserves_projection phi y
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp
    ((orbitProjection_eq_iff (G := G) (Y := Y)
      (phi • y) y).mp heq)
  refine ⟨g, deckTransformation_ext (orbitProjection_isCoveringMap h) (e := y) ?_⟩
  change g • y = phi • y
  exact hg

/-- For a nonempty preconnected covering space action, the acting group is
the full deck transformation group of the orbit covering. -/
noncomputable def actionDeckTransformationMulEquiv
    [PreconnectedSpace Y] [Nonempty Y] (h : IsCoveringSpaceAction G Y) :
    G ≃* DeckTransformationGroup (orbitProjection G Y) :=
  MulEquiv.ofBijective (actionToDeckTransformation (G := G) (Y := Y))
    ⟨actionToDeckTransformation_injective h.isFree,
      actionToDeckTransformation_surjective h⟩

end OrbitDeckTransformations

/-! ## The deck group of a normal covering -/

section NormalCoverDeckGroup

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X} {e₀ e₁ : E}

/-- Deck transformations commute with monodromy on the covering fiber. -/
theorem deckTransformation_coveringEndpoint
    (cov : CoveringMap p) (phi : DeckTransformationGroup p)
    (g : FundamentalGroup X (p e₀)) :
    cov.monodromy (FundamentalGroup.toPath g)
        ⟨phi • e₀, by
          exact Set.mem_singleton_iff.mpr
            (deckTransformation_preserves_projection phi e₀)⟩ =
      ⟨phi • (coveringEndpoint cov e₀ g).1, by
        exact Set.mem_singleton_iff.mpr
          ((deckTransformation_preserves_projection phi
            (coveringEndpoint cov e₀ g).1).trans
              (Set.mem_singleton_iff.mp (coveringEndpoint cov e₀ g).2))⟩ := by
  apply Subtype.ext
  unfold coveringEndpoint
  obtain ⟨γ, hγ⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  rw [← hγ]
  change cov.liftPath γ (phi • e₀) _ 1 =
    phi • (cov.liftPath γ e₀ _ 1)
  let Γ : C(↑unitInterval, E) :=
    ⟨fun t => phi • cov.liftPath γ e₀ (by simp) t,
      (phi : E ≃ₜ E).continuous.comp
        (cov.liftPath γ e₀ (by simp)).continuous⟩
  have hΓ : Γ = cov.liftPath γ (phi • e₀) (by
      simpa using γ.source.trans
        (deckTransformation_preserves_projection phi e₀).symm) := by
    apply (cov.eq_liftPath_iff' _).2
    constructor
    · funext t
      change p (phi • cov.liftPath γ e₀ (by simp) t) = γ t
      rw [deckTransformation_preserves_projection (p := p)]
      exact congrFun (cov.liftPath_lifts γ e₀ (by simp)) t
    · change phi • cov.liftPath γ e₀ (by simp) 0 = phi • e₀
      rw [cov.liftPath_zero]
  exact (DFunLike.congr_fun hΓ 1).symm

/-- If a deck transformation sends the basepoint to the endpoint of `a`, it
sends the endpoint of `b` to the endpoint of `b * a`. -/
theorem deckTransformation_coveringEndpoint_mul
    (cov : CoveringMap p) (phi : DeckTransformationGroup p)
    (a b : FundamentalGroup X (p e₀))
    (ha : phi • e₀ = (coveringEndpoint cov e₀ a).1) :
    phi • (coveringEndpoint cov e₀ b).1 =
      (coveringEndpoint cov e₀ (b * a)).1 := by
  let zphi : p ⁻¹' {p e₀} :=
    ⟨phi • e₀, Set.mem_singleton_iff.mpr
      (deckTransformation_preserves_projection phi e₀)⟩
  have hzphi : zphi = coveringEndpoint cov e₀ a :=
    Subtype.ext ha
  have hdeck := deckTransformation_coveringEndpoint cov phi b
  have htrans := cov.monodromy_trans_apply
    (FundamentalGroup.toPath a) (FundamentalGroup.toPath b) ⟨e₀, rfl⟩
  calc
    phi • (coveringEndpoint cov e₀ b).1 =
        (cov.monodromy (FundamentalGroup.toPath b) zphi).1 := by
          exact congrArg Subtype.val hdeck.symm
    _ = (cov.monodromy (FundamentalGroup.toPath b)
          (coveringEndpoint cov e₀ a)).1 := by rw [hzphi]
    _ = (cov.monodromy
          ((FundamentalGroup.toPath a).trans (FundamentalGroup.toPath b))
          ⟨e₀, rfl⟩).1 := by
          exact congrArg Subtype.val htrans.symm
    _ = (coveringEndpoint cov e₀ (b * a)).1 := by
          rw [← covering_toPath_mul b a]
          rfl

/-! ## Basepoint transport for covering image subgroups -/

private theorem fundamentalGroup_changePath_apply_raw
    {x₀ x₁ : X} (eta : Path x₀ x₁) (gamma : Path x₀ x₀) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath eta
        (FundamentalGroup.fromPath (.mk gamma)) =
      FundamentalGroup.fromPath (.mk ((eta.symm.trans gamma).trans eta)) := by
  change ((CategoryTheory.Groupoid.isoEquivHom
      (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm
        (Path.Homotopic.Quotient.mk eta)).conj
      (Path.Homotopic.Quotient.mk gamma) =
    Path.Homotopic.Quotient.mk ((eta.symm.trans gamma).trans eta)
  rw [CategoryTheory.Iso.conj_apply]
  have hhom :
      ((CategoryTheory.Groupoid.isoEquivHom
        (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm
          (Path.Homotopic.Quotient.mk eta)).hom =
        Path.Homotopic.Quotient.mk eta := rfl
  have hinv :
      ((CategoryTheory.Groupoid.isoEquivHom
        (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm
          (Path.Homotopic.Quotient.mk eta)).inv =
        Path.Homotopic.Quotient.mk eta.symm := rfl
  rw [hhom, hinv, FundamentalGroupoid.comp_eq,
    FundamentalGroupoid.comp_eq,
    ← Path.Homotopic.Quotient.mk_trans,
    ← Path.Homotopic.Quotient.mk_trans]
  exact Quotient.sound (Path.Homotopic.trans_assoc eta.symm gamma eta).symm

/-! The following equality is the raw-group form of naturality of monodromy
under changing both the total-space and base-space basepoints. -/
theorem coveringImageSubgroup_basepointChange
    (cov : CoveringMap p) (e₀ e₁ : E) (eta : Path e₀ e₁)
    (hbase : p e₀ = p e₁) :
    (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ hbase.symm).range =
      ((coveringImageSubgroup cov e₀).map
        (FundamentalGroup.fundamentalGroupMulEquivOfPath
          (eta.map cov.continuous)).toMonoidHom).map
        (FundamentalGroup.mapOfEq (ContinuousMap.id X) hbase.symm) := by
  let sigma := FundamentalGroup.fundamentalGroupMulEquivOfPath eta
  let tau := FundamentalGroup.fundamentalGroupMulEquivOfPath
    (eta.map cov.continuous)
  let m₀ := FundamentalGroup.map ⟨p, cov.continuous⟩ e₀
  let m₁ := FundamentalGroup.map ⟨p, cov.continuous⟩ e₁
  let kappa := FundamentalGroup.mapOfEq (ContinuousMap.id X) hbase.symm
  have hcomp :
      kappa.comp (tau.toMonoidHom.comp m₀) =
        kappa.comp (m₁.comp sigma.toMonoidHom) := by
    ext u
    obtain ⟨gamma, rfl⟩ := Path.Homotopic.Quotient.mk_surjective
      (FundamentalGroup.toPath u)
    change kappa (tau (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (gamma.map cov.continuous)))) =
      kappa (m₁ (sigma (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk gamma))))
    rw [fundamentalGroup_changePath_apply_raw,
      fundamentalGroup_changePath_apply_raw]
    rw [FundamentalGroup.map_apply]
    rw [← Path.Homotopic.Quotient.mk_map]
    rw [Path.map_trans, Path.map_trans, Path.map_symm]
  have hkm₁ :
      kappa.comp m₁ =
        FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ hbase.symm :=
    fundamentalGroup_basepointTransport_comp_map
      (⟨p, cov.continuous⟩ : C(E, X)) hbase.symm
  have hsigma :
      sigma.toMonoidHom.range = (⊤ : Subgroup (FundamentalGroup E e₁)) :=
    MonoidHom.range_eq_top.mpr sigma.surjective
  have hmap : (sigma.toMonoidHom.range).map m₁ = m₁.range := by
    rw [hsigma]
    exact (MonoidHom.range_eq_map m₁).symm
  have hrange_sigma :
      (kappa.comp (m₁.comp sigma.toMonoidHom)).range =
        (kappa.comp m₁).range := by
    calc
      (kappa.comp (m₁.comp sigma.toMonoidHom)).range =
          (m₁.comp sigma.toMonoidHom).range.map kappa :=
        MonoidHom.range_comp kappa (m₁.comp sigma.toMonoidHom)
      _ = ((sigma.toMonoidHom.range).map m₁).map kappa := by
        rw [MonoidHom.range_comp]
      _ = (m₁.range).map kappa := by rw [hmap]
      _ = (kappa.comp m₁).range := (MonoidHom.range_comp kappa m₁).symm
  have hrange_nat :
      (kappa.comp (tau.toMonoidHom.comp m₀)).range =
        (kappa.comp m₁).range := by
    rw [hcomp]
    exact hrange_sigma
  calc
    (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ hbase.symm).range =
        (kappa.comp m₁).range := by rw [hkm₁]
    _ = (kappa.comp (tau.toMonoidHom.comp m₀)).range :=
      hrange_nat.symm
    _ = (m₀.range.map tau.toMonoidHom).map kappa := by
      calc
        (kappa.comp (tau.toMonoidHom.comp m₀)).range =
            (tau.toMonoidHom.comp m₀).range.map kappa :=
          MonoidHom.range_comp kappa (tau.toMonoidHom.comp m₀)
        _ = (m₀.range.map tau.toMonoidHom).map kappa := by
          rw [MonoidHom.range_comp]
    _ = ((coveringImageSubgroup cov e₀).map tau.toMonoidHom).map kappa := by
      rfl

private theorem fundamentalGroup_map_path_change_noeq
    (cov : CoveringMap p) (eta : Path e₀ e₁)
    (z : FundamentalGroup E e₀) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        (eta.map cov.continuous)
        (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀ z) =
      FundamentalGroup.map ⟨p, cov.continuous⟩ e₁
        (FundamentalGroup.fundamentalGroupMulEquivOfPath eta z) := by
  obtain ⟨gamma, rfl⟩ := Path.Homotopic.Quotient.mk_surjective
    (FundamentalGroup.toPath z)
  change FundamentalGroup.fundamentalGroupMulEquivOfPath
      (eta.map cov.continuous)
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (gamma.map cov.continuous))) =
    FundamentalGroup.map ⟨p, cov.continuous⟩ e₁
      (FundamentalGroup.fundamentalGroupMulEquivOfPath eta
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk gamma)))
  rw [fundamentalGroup_changePath_apply_raw,
    fundamentalGroup_changePath_apply_raw]
  rw [FundamentalGroup.map_apply]
  rw [← Path.Homotopic.Quotient.mk_map]
  rw [Path.map_trans, Path.map_trans, Path.map_symm]

/-- The image subgroups at two points joined by a path are carried into one
another by the corresponding fundamental-group basepoint equivalence. -/
theorem coveringImageSubgroup_pathChange
    (cov : CoveringMap p) (eta : Path e₀ e₁) :
    coveringImageSubgroup cov e₁ =
      (coveringImageSubgroup cov e₀).map
        (FundamentalGroup.fundamentalGroupMulEquivOfPath
          (eta.map cov.continuous)).toMonoidHom := by
  let sigma := FundamentalGroup.fundamentalGroupMulEquivOfPath eta
  let tau := FundamentalGroup.fundamentalGroupMulEquivOfPath
    (eta.map cov.continuous)
  let m₀ := FundamentalGroup.map ⟨p, cov.continuous⟩ e₀
  let m₁ := FundamentalGroup.map ⟨p, cov.continuous⟩ e₁
  have hnat : tau.toMonoidHom.comp m₀ = m₁.comp sigma.toMonoidHom := by
    ext z
    exact fundamentalGroup_map_path_change_noeq cov eta z
  have hsigma : sigma.toMonoidHom.range =
      (⊤ : Subgroup (FundamentalGroup E e₁)) :=
    MonoidHom.range_eq_top.mpr sigma.surjective
  have hmap : (sigma.toMonoidHom.range).map m₁ = m₁.range := by
    rw [hsigma]
    exact (MonoidHom.range_eq_map m₁).symm
  have hrange_sigma :
      (m₁.comp sigma.toMonoidHom).range = m₁.range := by
    calc
      (m₁.comp sigma.toMonoidHom).range =
          (sigma.toMonoidHom.range).map m₁ :=
        MonoidHom.range_comp m₁ sigma.toMonoidHom
      _ = m₁.range := hmap
  calc
    coveringImageSubgroup cov e₁ = m₁.range := rfl
    _ = (m₁.comp sigma.toMonoidHom).range := hrange_sigma.symm
    _ = (tau.toMonoidHom.comp m₀).range := by rw [hnat]
    _ = m₀.range.map tau.toMonoidHom :=
      MonoidHom.range_comp tau.toMonoidHom m₀
    _ = (coveringImageSubgroup cov e₀).map tau.toMonoidHom := by rfl

theorem coveringImageSubgroup_normal_iff_pathChange
    (cov : CoveringMap p) (eta : Path e₀ e₁) :
    (coveringImageSubgroup cov e₀).Normal ↔
      (coveringImageSubgroup cov e₁).Normal := by
  let tau := FundamentalGroup.fundamentalGroupMulEquivOfPath
    (eta.map cov.continuous)
  have hrange := coveringImageSubgroup_pathChange cov eta
  constructor
  · intro hnormal
    have hmap :
        ((coveringImageSubgroup cov e₀).map tau.toMonoidHom).Normal :=
      hnormal.map tau.toMonoidHom tau.surjective
    simpa only [hrange] using hmap
  · intro hnormal
    have hback :
        coveringImageSubgroup cov e₀ =
          (coveringImageSubgroup cov e₁).map tau.symm.toMonoidHom := by
      exact (Subgroup.map_symm_eq_iff_map_eq (e := tau)
        (K := coveringImageSubgroup cov e₀)).2 hrange.symm |>.symm
    have hmap :
        ((coveringImageSubgroup cov e₁).map tau.symm.toMonoidHom).Normal :=
      hnormal.map tau.symm.toMonoidHom tau.symm.surjective
    simpa only [hback] using hmap

private theorem quotient_comp_eqToHom_eq_cast {a b : X}
    (q : Path.Homotopic.Quotient a b) (h : a = b) :
    CategoryTheory.CategoryStruct.comp q
        (CategoryTheory.eqToHom
          (congrArg FundamentalGroupoid.mk h.symm)) = q.cast rfl h := by
  subst b
  simp

private theorem fundamentalGroup_loop_change_apply
    {x : X} (alpha : Path x x) (z : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath alpha z =
      MulAut.conj (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) z := by
  rw [MulAut.conj_apply]
  change ((CategoryTheory.Groupoid.isoEquivHom
      (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x)).symm
        (Path.Homotopic.Quotient.mk alpha)).conj z =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha) * z *
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha))⁻¹
  rw [CategoryTheory.Iso.conj_apply]
  rfl

private theorem fundamentalGroup_map_path_change
    (cov : CoveringMap p) (eta : Path e₀ e₁) (hbase : p e₀ = p e₁)
    (z : FundamentalGroup E e₀) :
    FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ hbase.symm
        (FundamentalGroup.fundamentalGroupMulEquivOfPath eta z) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((eta.map cov.continuous).cast rfl hbase)
        (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀ z) := by
  let P : C(E, X) := ⟨p, cov.continuous⟩
  let F := FundamentalGroupoid.map P
  let I : FundamentalGroupoid.mk e₀ ≅ FundamentalGroupoid.mk e₁ :=
    (CategoryTheory.Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.mk eta)
  let J : FundamentalGroupoid.mk (p e₁) ≅ FundamentalGroupoid.mk (p e₀) :=
    CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk hbase.symm)
  let alpha : Path (p e₀) (p e₀) :=
    (eta.map cov.continuous).cast rfl hbase
  let K : FundamentalGroupoid.mk (p e₀) ≅ FundamentalGroupoid.mk (p e₀) :=
    F.mapIso I ≪≫ J
  let Kalpha : FundamentalGroupoid.mk (p e₀) ≅ FundamentalGroupoid.mk (p e₀) :=
    (CategoryTheory.Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.mk alpha)
  have hK : K = Kalpha := by
    apply CategoryTheory.Iso.ext
    change CategoryTheory.CategoryStruct.comp (F.map I.hom) J.hom = Kalpha.hom
    change CategoryTheory.CategoryStruct.comp
        ((Path.Homotopic.Quotient.mk eta).map P) J.hom =
      Path.Homotopic.Quotient.mk alpha
    dsimp only [J, alpha, P]
    rw [← Path.Homotopic.Quotient.mk_map]
    exact quotient_comp_eqToHom_eq_cast
      (Path.Homotopic.Quotient.mk (eta.map cov.continuous)) hbase
  change J.conj (F.map (I.conj z)) = Kalpha.conj (F.map z)
  rw [F.map_conj]
  calc
    J.conj ((F.mapIso I).conj (F.map z)) =
        (F.mapIso I ≪≫ J).conj (F.map z) :=
      (CategoryTheory.Iso.trans_conj (F.mapIso I) J (F.map z)).symm
    _ = Kalpha.conj (F.map z) := by
      change K.conj (F.map z) = Kalpha.conj (F.map z)
      rw [hK]

private theorem fundamentalGroup_map_path_change_conj
    (cov : CoveringMap p) (eta : Path e₀ e₁) (hbase : p e₀ = p e₁)
    (z : FundamentalGroup E e₀) :
    FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ hbase.symm
        (FundamentalGroup.fundamentalGroupMulEquivOfPath eta z) =
      MulAut.conj
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk
            ((eta.map cov.continuous).cast rfl hbase)))
        (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀ z) := by
  rw [fundamentalGroup_map_path_change cov eta hbase z,
    fundamentalGroup_loop_change_apply]

/-- Changing the chosen point in a fiber conjugates the image subgroup by the
projected path between the chosen points. -/
theorem mapOfEq_range_eq_conj_map_range
    (cov : CoveringMap p) (eta : Path e₀ e₁) (hbase : p e₀ = p e₁) :
    (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ hbase.symm).range =
      Subgroup.map
        (MulAut.conj
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk
              ((eta.map cov.continuous).cast rfl hbase)))).toMonoidHom
        (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range := by
  ext y
  rw [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨z, rfl⟩
    let z' := (FundamentalGroup.fundamentalGroupMulEquivOfPath eta).symm z
    refine ⟨FundamentalGroup.map ⟨p, cov.continuous⟩ e₀ z', ?_, ?_⟩
    · exact ⟨z', rfl⟩
    · have hzeta : FundamentalGroup.fundamentalGroupMulEquivOfPath eta z' = z := by
        dsimp [z']
        exact (FundamentalGroup.fundamentalGroupMulEquivOfPath eta).apply_symm_apply z
      rw [← hzeta]
      exact (fundamentalGroup_map_path_change_conj cov eta hbase z').symm
  · rintro ⟨z, ⟨z', rfl⟩, rfl⟩
    refine ⟨FundamentalGroup.fundamentalGroupMulEquivOfPath eta z', ?_⟩
    exact fundamentalGroup_map_path_change_conj cov eta hbase z'

private theorem exists_path_to_coveringEndpoint_inv
    (cov : CoveringMap p) (e₀ : E)
    (g : FundamentalGroup X (p e₀)) :
    let e₁ := (coveringEndpoint cov e₀ g⁻¹).1
    ∃ hbase : p e₀ = p e₁, ∃ eta : Path e₀ e₁,
      FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk
            ((eta.map cov.continuous).cast rfl hbase)) = g⁻¹ := by
  let ep := coveringEndpoint cov e₀ g⁻¹
  let e₁ : E := ep.1
  have hbase : p e₀ = p e₁ :=
    (Set.mem_singleton_iff.mp ep.2).symm
  obtain ⟨gamma, hgamma⟩ := Path.Homotopic.Quotient.mk_surjective
    (FundamentalGroup.toPath (g⁻¹))
  let gammac : C(↑unitInterval, X) := ⟨gamma, gamma.continuous⟩
  have hgamma0 : gammac 0 = p e₀ := by simp [gammac]
  let Gamma : C(↑unitInterval, E) := cov.liftPath gammac e₀ hgamma0
  have hm :
      cov.monodromy (Path.Homotopic.Quotient.mk gamma) ⟨e₀, rfl⟩ =
        ⟨Gamma 1, (congrFun (cov.liftPath_lifts gammac e₀ hgamma0) 1).trans
          gamma.target⟩ := by
    unfold IsCoveringMap.monodromy
    rfl
  have hep :
      coveringEndpoint cov e₀ g⁻¹ =
        ⟨Gamma 1, (congrFun (cov.liftPath_lifts gammac e₀ hgamma0) 1).trans
          gamma.target⟩ := by
    unfold coveringEndpoint
    rw [← hgamma]
    exact hm
  have hGammaEnd : Gamma 1 = e₁ := by
    change Gamma 1 = ep.1
    exact (congrArg Subtype.val hep).symm
  let eta : Path e₀ e₁ :=
    Path.mk Gamma (cov.liftPath_zero gammac e₀ hgamma0) hGammaEnd
  refine ⟨hbase, eta, ?_⟩
  have hpath : ((eta.map cov.continuous).cast rfl hbase) = gamma := by
    apply Path.ext
    funext t
    change p (Gamma t) = gamma t
    exact congrFun (cov.liftPath_lifts gammac e₀ hgamma0) t
  rw [hpath]
  exact congrArg FundamentalGroup.fromPath hgamma

/-- The image subgroup at the endpoint of the lift of `g⁻¹` is the conjugate
of the original image subgroup by `g⁻¹`. -/
theorem coveringEndpoint_range_eq_conj_inv
    (cov : CoveringMap p) (e₀ : E)
    (g : FundamentalGroup X (p e₀)) :
    let e₁ := (coveringEndpoint cov e₀ g⁻¹).1
    ∃ hbase : p e₀ = p e₁,
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ hbase.symm).range =
        Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
          (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range := by
  dsimp
  obtain ⟨hbase, eta, halpha⟩ :=
    exists_path_to_coveringEndpoint_inv cov e₀ g
  refine ⟨hbase, ?_⟩
  rw [mapOfEq_range_eq_conj_map_range cov eta hbase, halpha]
  rfl

private theorem subgroup_map_conj_carrier_image
    {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    ((Subgroup.map (MulAut.conj g).toMonoidHom H : Subgroup G) : Set G) =
      (MulAut.conj g : G → G) '' (H : Set G) := by
  ext y
  change y ∈ Subgroup.map (MulAut.conj g).toMonoidHom H ↔
    y ∈ (MulAut.conj g : G → G) '' (H : Set G)
  rw [Subgroup.mem_map]
  rfl

private theorem mem_normalizer_iff_map_conj_eq
    {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    g ∈ Subgroup.normalizer (H : Set G) ↔
      Subgroup.map (MulAut.conj g).toMonoidHom H = H := by
  constructor
  · intro hg
    apply Subgroup.ext
    intro y
    change y ∈ ((Subgroup.map (MulAut.conj g).toMonoidHom H : Subgroup G) : Set G) ↔
      y ∈ (H : Set G)
    rw [subgroup_map_conj_carrier_image H g]
    exact Set.ext_iff.mp
      (Subgroup.mem_normalizer_iff_conj_image_eq.mp hg) y
  · intro hmap
    apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
    rw [← subgroup_map_conj_carrier_image H g, hmap]

/-- The deck transformation associated to a loop in a normal cover. The
inverse compensates for the multiplication convention on fundamental groups. -/
def normalCoverDeck (h : IsNormalCovering p) (e₀ : E)
    (g : FundamentalGroup X (p e₀)) : DeckTransformationGroup p :=
  Classical.choose (h.2.2
    (Set.mem_singleton_iff.mp (coveringEndpoint h.1 e₀ g⁻¹).2).symm)

@[simp] theorem normalCoverDeck_apply (h : IsNormalCovering p) (e₀ : E)
    (g : FundamentalGroup X (p e₀)) :
    normalCoverDeck h e₀ g • e₀ =
      (coveringEndpoint h.1 e₀ g⁻¹).1 :=
  Classical.choose_spec (h.2.2
    (Set.mem_singleton_iff.mp (coveringEndpoint h.1 e₀ g⁻¹).2).symm)

/-- Monodromy of a normal connected cover, viewed as a homomorphism to its
deck-transformation group. -/
def normalCoverDeckHom (h : IsNormalCovering p) [PreconnectedSpace E]
    (e₀ : E) :
    FundamentalGroup X (p e₀) →* DeckTransformationGroup p where
  toFun := normalCoverDeck h e₀
  map_one' := by
    apply deckTransformation_ext h.1 (e := e₀)
    rw [normalCoverDeck_apply]
    change (coveringEndpoint h.1 e₀
      (1 : FundamentalGroup X (p e₀))).1 = e₀
    have hfixed :=
      (mem_coveringImageSubgroup_iff_monodromy_fixed h.1
        (1 : FundamentalGroup X (p e₀))).1
        (coveringImageSubgroup h.1 e₀).one_mem
    exact congrArg Subtype.val hfixed
  map_mul' g k := by
    apply deckTransformation_ext h.1 (e := e₀)
    rw [normalCoverDeck_apply]
    change (coveringEndpoint h.1 e₀ (g * k)⁻¹).1 =
      (normalCoverDeck h e₀ g * normalCoverDeck h e₀ k) • e₀
    rw [mul_smul, normalCoverDeck_apply]
    rw [deckTransformation_coveringEndpoint_mul h.1
      (normalCoverDeck h e₀ g) g⁻¹ k⁻¹ (normalCoverDeck_apply h e₀ g)]
    rw [mul_inv_rev]

/-- For a path-connected covering, every point of the chosen fiber is the
endpoint of the lift of some loop. -/
theorem coveringEndpoint_surjective [PathConnectedSpace E]
    (cov : CoveringMap p) (e₀ : E) :
    Function.Surjective (coveringEndpoint cov e₀) := by
  intro z
  obtain ⟨q, hq⟩ := coveringEndpointQuotient_surjective cov e₀ z
  induction q using QuotientGroup.induction_on with
  | _ g => exact ⟨g, hq⟩

/-- Every deck transformation of a path-connected normal cover is induced by
a loop in the base. -/
theorem normalCoverDeckHom_surjective (h : IsNormalCovering p)
    [PathConnectedSpace E] (e₀ : E) :
    Function.Surjective (normalCoverDeckHom h e₀) := by
  intro phi
  let z : p ⁻¹' {p e₀} :=
    ⟨phi • e₀, Set.mem_singleton_iff.mpr
      (deckTransformation_preserves_projection phi e₀)⟩
  obtain ⟨g, hg⟩ := coveringEndpoint_surjective h.1 e₀ z
  refine ⟨g⁻¹, deckTransformation_ext h.1 (e := e₀) ?_⟩
  change normalCoverDeck h e₀ g⁻¹ • e₀ = phi • e₀
  rw [normalCoverDeck_apply, inv_inv]
  exact congrArg Subtype.val hg

/-- The kernel of normal-cover monodromy is precisely the subgroup induced by
the covering projection. -/
theorem normalCoverDeckHom_ker (h : IsNormalCovering p)
    [PathConnectedSpace E] (e₀ : E) :
    (normalCoverDeckHom h e₀).ker = coveringImageSubgroup h.1 e₀ := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    have hvalue := congrArg
      (fun phi : DeckTransformationGroup p => phi • e₀) hg
    change normalCoverDeck h e₀ g • e₀ = e₀ at hvalue
    rw [normalCoverDeck_apply] at hvalue
    have hfixed :
        h.1.monodromy (FundamentalGroup.toPath g⁻¹) ⟨e₀, rfl⟩ =
          ⟨e₀, rfl⟩ := Subtype.ext hvalue
    have hinv : g⁻¹ ∈ coveringImageSubgroup h.1 e₀ :=
      (mem_coveringImageSubgroup_iff_monodromy_fixed h.1 g⁻¹).2 hfixed
    simpa using (coveringImageSubgroup h.1 e₀).inv_mem hinv
  · intro hg
    have hinv : g⁻¹ ∈ coveringImageSubgroup h.1 e₀ :=
      (coveringImageSubgroup h.1 e₀).inv_mem hg
    have hfixed :=
      (mem_coveringImageSubgroup_iff_monodromy_fixed h.1 g⁻¹).1 hinv
    apply deckTransformation_ext h.1 (e := e₀)
    change normalCoverDeck h e₀ g • e₀ = e₀
    rw [normalCoverDeck_apply]
    exact congrArg Subtype.val hfixed

/-- The image subgroup of a path-connected normal cover is normal. -/
theorem normalCovering_imageSubgroup_normal (h : IsNormalCovering p)
    [PathConnectedSpace E] (e₀ : E) :
    (coveringImageSubgroup h.1 e₀).Normal := by
  rw [← normalCoverDeckHom_ker h e₀]
  infer_instance

/-- For a path-connected normal cover, the deck group is the quotient of the
base fundamental group by the induced subgroup. -/
noncomputable def normalCoverDeckGroupMulEquiv (h : IsNormalCovering p)
    [PathConnectedSpace E] (e₀ : E) :
    letI : (coveringImageSubgroup h.1 e₀).Normal :=
      normalCovering_imageSubgroup_normal h e₀
    (FundamentalGroup X (p e₀) ⧸ coveringImageSubgroup h.1 e₀) ≃*
      DeckTransformationGroup p := by
  let phi := normalCoverDeckHom h e₀
  letI : (coveringImageSubgroup h.1 e₀).Normal :=
    normalCovering_imageSubgroup_normal h e₀
  let e₁ : (FundamentalGroup X (p e₀) ⧸ phi.ker) ≃*
      DeckTransformationGroup p :=
    QuotientGroup.quotientKerEquivOfSurjective phi
      (normalCoverDeckHom_surjective h e₀)
  let e₀' :
      (FundamentalGroup X (p e₀) ⧸ coveringImageSubgroup h.1 e₀) ≃*
        (FundamentalGroup X (p e₀) ⧸ phi.ker) :=
    QuotientGroup.quotientMulEquivOfEq
      (normalCoverDeckHom_ker h e₀).symm
  exact e₀'.trans e₁

/-- Normal-cover monodromy in Hatcher's path-product convention. -/
def normalCoverPiOneDeckHom (h : IsNormalCovering p)
    [PathConnectedSpace E] (e₀ : E) :
    PiOne (p e₀) →* DeckTransformationGroup p :=
  (normalCoverDeckHom h e₀).comp
    (MulEquiv.inv' (FundamentalGroup X (p e₀))).symm.toMonoidHom

/-- Every deck transformation of a connected normal cover is induced by a
`PiOne` class. -/
theorem normalCoverPiOneDeckHom_surjective (h : IsNormalCovering p)
    [PathConnectedSpace E] (e₀ : E) :
    Function.Surjective (normalCoverPiOneDeckHom h e₀) :=
  (normalCoverDeckHom_surjective h e₀).comp
    (MulEquiv.inv' (FundamentalGroup X (p e₀))).symm.surjective

/-- The kernel of normal-cover monodromy in Hatcher's convention is the
induced `PiOne` subgroup. -/
theorem normalCoverPiOneDeckHom_ker (h : IsNormalCovering p)
    [PathConnectedSpace E] (e₀ : E) :
    (normalCoverPiOneDeckHom h e₀).ker =
      coveringPiOneImageSubgroup h.1 e₀ := by
  ext g
  change normalCoverDeckHom h e₀
      ((MulEquiv.inv' (FundamentalGroup X (p e₀))).symm g) = 1 ↔
    g ∈ coveringPiOneImageSubgroup h.1 e₀
  rw [← MonoidHom.mem_ker, normalCoverDeckHom_ker]
  change g.unop⁻¹ ∈ coveringImageSubgroup h.1 e₀ ↔ _
  rw [coveringPiOneImageSubgroup_eq_op]
  change g.unop⁻¹ ∈ coveringImageSubgroup h.1 e₀ ↔
    g.unop ∈ coveringImageSubgroup h.1 e₀
  exact (coveringImageSubgroup h.1 e₀).inv_mem_iff

/-- For a connected normal cover, the deck group is Hatcher's fundamental
group modulo the subgroup induced from upstairs. -/
noncomputable def normalCoverPiOneDeckGroupMulEquiv
    (h : IsNormalCovering p) [PathConnectedSpace E] (e₀ : E) :
    let H := coveringPiOneImageSubgroup h.1 e₀
    letI : H.Normal := by
      change (coveringPiOneImageSubgroup h.1 e₀).Normal
      rw [coveringPiOneImageSubgroup_eq_op, Subgroup.normal_op]
      exact normalCovering_imageSubgroup_normal h e₀
    (PiOne (p e₀) ⧸ H) ≃* DeckTransformationGroup p := by
  let H := coveringPiOneImageSubgroup h.1 e₀
  let phi := normalCoverPiOneDeckHom h e₀
  letI : H.Normal := by
    change (coveringPiOneImageSubgroup h.1 e₀).Normal
    rw [coveringPiOneImageSubgroup_eq_op, Subgroup.normal_op]
    exact normalCovering_imageSubgroup_normal h e₀
  let e₁ : (PiOne (p e₀) ⧸ phi.ker) ≃* DeckTransformationGroup p :=
    QuotientGroup.quotientKerEquivOfSurjective phi
      (normalCoverPiOneDeckHom_surjective h e₀)
  let e₀' : (PiOne (p e₀) ⧸ H) ≃* (PiOne (p e₀) ⧸ phi.ker) :=
    QuotientGroup.quotientMulEquivOfEq
      (normalCoverPiOneDeckHom_ker h e₀).symm
  exact e₀'.trans e₁

end NormalCoverDeckGroup

/-! ## The normalizer and the deck group -/

section NormalizerDeckGroup

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}

/-- The normalizer of the image subgroup of a covering, in the raw
mathlib fundamental group convention. -/
abbrev coveringNormalizer (cov : CoveringMap p) (e₀ : E) :
    Subgroup (FundamentalGroup X (p e₀)) :=
  Subgroup.normalizer (coveringImageSubgroup cov e₀ :
    Set (FundamentalGroup X (p e₀)))

/-- A loop class lies in the image-subgroup normalizer exactly when its lift
ends at a point obtainable by a deck transformation. -/
theorem mem_coveringNormalizer_iff_exists_deck
    (cov : CoveringMap p) [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ : E) (g : FundamentalGroup X (p e₀)) :
    g ∈ coveringNormalizer cov e₀ ↔
      ∃ phi : DeckTransformationGroup p,
        phi • e₀ = (coveringEndpoint cov e₀ g⁻¹).1 := by
  let H := coveringImageSubgroup cov e₀
  constructor
  · intro hg
    obtain ⟨hbase, hrange⟩ := coveringEndpoint_range_eq_conj_inv cov e₀ g
    have hg0 : g ∈ Subgroup.normalizer
        (coveringImageSubgroup cov e₀ : Set _) := hg
    have hginv0 : g⁻¹ ∈ Subgroup.normalizer
        (coveringImageSubgroup cov e₀ : Set _) :=
      Subgroup.inv_mem _ hg0
    have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set _) := by
      simpa [H] using hginv0
    have hmap : Subgroup.map (MulAut.conj g⁻¹).toMonoidHom H = H :=
      (mem_normalizer_iff_map_conj_eq H g⁻¹).mp hginv
    have hmap' : Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
        (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range =
          (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range := by
      change Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
          (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range =
        (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range at hmap
      exact hmap
    have hrange' :
        (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ hbase.symm).range =
          (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range := by
      rw [hrange, hmap']
    obtain ⟨hequiv⟩ :=
      (nonempty_basedCoveringEquiv_iff_piOneRanges_eq cov cov hbase).2
        hrange'.symm
    refine ⟨⟨hequiv.toHomeomorph, hequiv.commutes⟩, hequiv.map_basepoint⟩
  · rintro ⟨phi, hphi⟩
    obtain ⟨hbase, hrange⟩ := coveringEndpoint_range_eq_conj_inv cov e₀ g
    have hrange' :
        (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ hbase.symm).range =
          (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range := by
      have hequiv : BasedCoveringEquiv p p e₀
          (coveringEndpoint cov e₀ g⁻¹).1 := {
        toHomeomorph := phi
        map_basepoint := hphi
        commutes := phi.2
      }
      exact ((nonempty_basedCoveringEquiv_iff_piOneRanges_eq cov cov hbase).mp
        ⟨hequiv⟩).symm
    have hmap' : Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
        (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range =
          (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range := by
      rw [← hrange, hrange'.symm]
    have hmap : Subgroup.map (MulAut.conj g⁻¹).toMonoidHom H = H := by
      change Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
          (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range =
        (FundamentalGroup.map ⟨p, cov.continuous⟩ e₀).range
      exact hmap'
    have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set _) :=
      (mem_normalizer_iff_map_conj_eq H g⁻¹).mpr hmap
    simpa using (Subgroup.inv_mem _ hginv)

/-- The deck transformation induced by a normalizer element. -/
noncomputable def normalizerCoverDeck
    (cov : CoveringMap p) [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ : E) (g : coveringNormalizer cov e₀) :
    DeckTransformationGroup p :=
  Classical.choose
    ((mem_coveringNormalizer_iff_exists_deck cov e₀
      (g : FundamentalGroup X (p e₀))).mp g.property)

@[simp] theorem normalizerCoverDeck_apply
    (cov : CoveringMap p) [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ : E) (g : coveringNormalizer cov e₀) :
    normalizerCoverDeck cov e₀ g • e₀ =
      (coveringEndpoint cov e₀ (g : FundamentalGroup X (p e₀))⁻¹).1 :=
  Classical.choose_spec
    ((mem_coveringNormalizer_iff_exists_deck cov e₀
      (g : FundamentalGroup X (p e₀))).mp g.property)

/-- The normalizer-to-deck map is multiplicative. -/
def normalizerCoverDeckHom
    (cov : CoveringMap p) [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ : E) : coveringNormalizer cov e₀ →* DeckTransformationGroup p where
  toFun := normalizerCoverDeck cov e₀
  map_one' := by
    apply deckTransformation_ext cov (e := e₀)
    rw [normalizerCoverDeck_apply]
    change (coveringEndpoint cov e₀
      (1 : FundamentalGroup X (p e₀))).1 = e₀
    have hfixed :=
      (mem_coveringImageSubgroup_iff_monodromy_fixed cov
        (1 : FundamentalGroup X (p e₀))).1
        (coveringImageSubgroup cov e₀).one_mem
    exact congrArg Subtype.val hfixed
  map_mul' g k := by
    apply deckTransformation_ext cov (e := e₀)
    rw [normalizerCoverDeck_apply]
    change (coveringEndpoint cov e₀ ((g * k : coveringNormalizer cov e₀) :
      FundamentalGroup X (p e₀))⁻¹).1 =
      (normalizerCoverDeck cov e₀ g * normalizerCoverDeck cov e₀ k) • e₀
    rw [mul_smul, normalizerCoverDeck_apply]
    rw [deckTransformation_coveringEndpoint_mul cov
      (normalizerCoverDeck cov e₀ g)
      (g : FundamentalGroup X (p e₀))⁻¹
      (k : FundamentalGroup X (p e₀))⁻¹
      (normalizerCoverDeck_apply cov e₀ g)]
    change (coveringEndpoint cov e₀
      (((g : FundamentalGroup X (p e₀)) *
        (k : FundamentalGroup X (p e₀)))⁻¹)).1 =
      (coveringEndpoint cov e₀
        ((k : FundamentalGroup X (p e₀))⁻¹ *
          (g : FundamentalGroup X (p e₀))⁻¹)).1
    rw [mul_inv_rev]

/-- Every deck transformation is induced by a normalizer element. -/
theorem normalizerCoverDeckHom_surjective
    (cov : CoveringMap p) [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ : E) :
    Function.Surjective (normalizerCoverDeckHom cov e₀) := by
  intro phi
  let z : p ⁻¹' {p e₀} :=
    ⟨phi • e₀, Set.mem_singleton_iff.mpr
      (deckTransformation_preserves_projection phi e₀)⟩
  obtain ⟨g, hg⟩ := coveringEndpoint_surjective cov e₀ z
  have hnorm : g⁻¹ ∈ coveringNormalizer cov e₀ := by
    apply (mem_coveringNormalizer_iff_exists_deck cov e₀ (g⁻¹)).2
    refine ⟨phi, ?_⟩
    rw [inv_inv]
    exact congrArg Subtype.val hg.symm
  let n : coveringNormalizer cov e₀ := ⟨g⁻¹, hnorm⟩
  refine ⟨n, deckTransformation_ext cov (e := e₀) ?_⟩
  change normalizerCoverDeck cov e₀ n • e₀ = phi • e₀
  rw [normalizerCoverDeck_apply]
  rw [show (n : FundamentalGroup X (p e₀))⁻¹ = g by simp [n]]
  change (coveringEndpoint cov e₀ g).1 = (z : E)
  exact congrArg Subtype.val hg

/-- The kernel of the normalizer-to-deck map is the image subgroup, viewed as
a subgroup of the normalizer. -/
theorem normalizerCoverDeckHom_ker
    (cov : CoveringMap p) [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ : E) :
    (normalizerCoverDeckHom cov e₀).ker =
      (coveringImageSubgroup cov e₀).subgroupOf (coveringNormalizer cov e₀) := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    have hvalue := congrArg
      (fun phi : DeckTransformationGroup p => phi • e₀) hg
    change normalizerCoverDeck cov e₀ g • e₀ = e₀ at hvalue
    rw [normalizerCoverDeck_apply] at hvalue
    have hfixed :
        cov.monodromy (FundamentalGroup.toPath
          (g : FundamentalGroup X (p e₀))⁻¹) ⟨e₀, rfl⟩ =
          ⟨e₀, rfl⟩ := Subtype.ext hvalue
    have hinv : (g : FundamentalGroup X (p e₀))⁻¹ ∈
        coveringImageSubgroup cov e₀ :=
      (mem_coveringImageSubgroup_iff_monodromy_fixed cov
        (g : FundamentalGroup X (p e₀))⁻¹).2 hfixed
    have hraw : (g : FundamentalGroup X (p e₀)) ∈
        coveringImageSubgroup cov e₀ := by
      simpa using (coveringImageSubgroup cov e₀).inv_mem hinv
    exact hraw
  · intro hg
    have hinv : (g : FundamentalGroup X (p e₀))⁻¹ ∈
        coveringImageSubgroup cov e₀ :=
      (coveringImageSubgroup cov e₀).inv_mem hg
    have hfixed :=
      (mem_coveringImageSubgroup_iff_monodromy_fixed cov
        (g : FundamentalGroup X (p e₀))⁻¹).1 hinv
    apply deckTransformation_ext cov (e := e₀)
    change normalizerCoverDeck cov e₀ g • e₀ = e₀
    rw [normalizerCoverDeck_apply]
    exact congrArg Subtype.val hfixed

/-- The deck group is the quotient of the normalizer by the image subgroup. -/
noncomputable def normalizerCoverDeckGroupMulEquiv
    (cov : CoveringMap p) [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ : E) :
    let H := coveringImageSubgroup cov e₀
    let N := coveringNormalizer cov e₀
    (N ⧸ H.subgroupOf N) ≃* DeckTransformationGroup p := by
  let H := coveringImageSubgroup cov e₀
  let N := coveringNormalizer cov e₀
  let phi := normalizerCoverDeckHom cov e₀
  letI : (H.subgroupOf N).Normal := by infer_instance
  let e₁ : (N ⧸ phi.ker) ≃* DeckTransformationGroup p :=
    QuotientGroup.quotientKerEquivOfSurjective phi
      (normalizerCoverDeckHom_surjective cov e₀)
  let e₀' : (N ⧸ H.subgroupOf N) ≃* (N ⧸ phi.ker) :=
    QuotientGroup.quotientMulEquivOfEq
      (normalizerCoverDeckHom_ker cov e₀).symm
  exact e₀'.trans e₁

/-- The normalizer of a covering image subgroup in Hatcher's path-product
fundamental group. -/
abbrev coveringPiOneNormalizer (cov : CoveringMap p) (e₀ : E) :
    Subgroup (PiOne (p e₀)) :=
  Subgroup.normalizer (coveringPiOneImageSubgroup cov e₀)

/-- Inversion identifies the `PiOne` normalizer with the raw fundamental-group
normalizer used by mathlib. -/
def coveringPiOneNormalizerRawMulEquiv
    (cov : CoveringMap p) (e₀ : E) :
    coveringPiOneNormalizer cov e₀ ≃* coveringNormalizer cov e₀ where
  toFun g := ⟨g.1.unop⁻¹, by
    have hg : g.1 ∈ (coveringNormalizer cov e₀).op := by
      rw [Subgroup.op_normalizer, ← coveringPiOneImageSubgroup_eq_op]
      exact g.2
    exact (coveringNormalizer cov e₀).inv_mem hg⟩
  invFun g := ⟨MulOpposite.op (g.1⁻¹), by
    have hg : MulOpposite.op (g.1⁻¹) ∈
        (coveringNormalizer cov e₀).op :=
      (coveringNormalizer cov e₀).inv_mem g.2
    rw [Subgroup.op_normalizer, ← coveringPiOneImageSubgroup_eq_op] at hg
    exact hg⟩
  left_inv g := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simp
  map_mul' g k := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, MulOpposite.unop_mul] using
      mul_inv_rev k.1.unop g.1.unop

/-- The normalizer action on a connected cover, in Hatcher's fundamental-group
convention. -/
def normalizerPiOneCoverDeckHom
    (cov : CoveringMap p) [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ : E) :
    coveringPiOneNormalizer cov e₀ →* DeckTransformationGroup p :=
  (normalizerCoverDeckHom cov e₀).comp
    (coveringPiOneNormalizerRawMulEquiv cov e₀).toMonoidHom

/-- Every deck transformation comes from the `PiOne` normalizer. -/
theorem normalizerPiOneCoverDeckHom_surjective
    (cov : CoveringMap p) [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ : E) :
    Function.Surjective (normalizerPiOneCoverDeckHom cov e₀) :=
  (normalizerCoverDeckHom_surjective cov e₀).comp
    (coveringPiOneNormalizerRawMulEquiv cov e₀).surjective

/-- The kernel of the `PiOne` normalizer action is the image subgroup. -/
theorem normalizerPiOneCoverDeckHom_ker
    (cov : CoveringMap p) [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ : E) :
    (normalizerPiOneCoverDeckHom cov e₀).ker =
      (coveringPiOneImageSubgroup cov e₀).subgroupOf
        (coveringPiOneNormalizer cov e₀) := by
  ext g
  change normalizerCoverDeckHom cov e₀
      (coveringPiOneNormalizerRawMulEquiv cov e₀ g) = 1 ↔
    g.1 ∈ coveringPiOneImageSubgroup cov e₀
  rw [← MonoidHom.mem_ker, normalizerCoverDeckHom_ker]
  change g.1.unop⁻¹ ∈ coveringImageSubgroup cov e₀ ↔ _
  rw [coveringPiOneImageSubgroup_eq_op]
  change g.1.unop⁻¹ ∈ coveringImageSubgroup cov e₀ ↔
    g.1.unop ∈ coveringImageSubgroup cov e₀
  exact (coveringImageSubgroup cov e₀).inv_mem_iff

/-- In Hatcher's convention, the deck group is the quotient of the normalizer
of the induced subgroup by that subgroup. -/
noncomputable def normalizerPiOneCoverDeckGroupMulEquiv
    (cov : CoveringMap p) [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ : E) :
    let H := coveringPiOneImageSubgroup cov e₀
    let N := coveringPiOneNormalizer cov e₀
    (N ⧸ H.subgroupOf N) ≃* DeckTransformationGroup p := by
  let H := coveringPiOneImageSubgroup cov e₀
  let N := coveringPiOneNormalizer cov e₀
  let phi := normalizerPiOneCoverDeckHom cov e₀
  letI : (H.subgroupOf N).Normal := by infer_instance
  let e₁ : (N ⧸ phi.ker) ≃* DeckTransformationGroup p :=
    QuotientGroup.quotientKerEquivOfSurjective phi
      (normalizerPiOneCoverDeckHom_surjective cov e₀)
  let e₀' : (N ⧸ H.subgroupOf N) ≃* (N ⧸ phi.ker) :=
    QuotientGroup.quotientMulEquivOfEq
      (normalizerPiOneCoverDeckHom_ker cov e₀).symm
  exact e₀'.trans e₁

/-- The normalizer quotient theorem with the hypotheses used in Hatcher's
statement; local path-connectedness of the total space follows from the
covering map. -/
noncomputable def normalizerPiOneCoverDeckGroupMulEquivOfLocPathConnectedBase
    (cov : CoveringMap p) [PathConnectedSpace E] [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] (e₀ : E) :
    let H := coveringPiOneImageSubgroup cov e₀
    let N := coveringPiOneNormalizer cov e₀
    (N ⧸ H.subgroupOf N) ≃* DeckTransformationGroup p := by
  letI : LocallyPathConnectedSpace E := cov.locPathConnectedSpace
  exact normalizerPiOneCoverDeckGroupMulEquiv cov e₀

end NormalizerDeckGroup

/-! The normal-cover criterion can now be stated directly in terms of the
image subgroup.  The local path-connectedness instance on the total space is
transferred from the base by the covering map. -/
theorem isNormalCovering_iff_forall_imageSubgroup_normal
    {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : CoveringMap p) [PathConnectedSpace E]
    [PathConnectedSpace X] [LocallyPathConnectedSpace X] (e₀ : E) :
    IsNormalCovering p ↔
      ∀ e : E, (coveringImageSubgroup cov e).Normal := by
  letI : LocallyPathConnectedSpace E := cov.locPathConnectedSpace
  constructor
  · intro h e
    exact normalCovering_imageSubgroup_normal h e
  · intro hnormal
    refine ⟨cov, cov.surjective_of_pathConnectedSpace e₀, ?_⟩
    intro e e' hpe
    let z : p ⁻¹' {p e} :=
      ⟨e', Set.mem_singleton_iff.mpr hpe.symm⟩
    obtain ⟨g, hg⟩ := coveringEndpoint_surjective cov e z
    have hnorm_inv : g⁻¹ ∈ coveringNormalizer cov e := by
      change g⁻¹ ∈ Subgroup.normalizer
        (coveringImageSubgroup cov e : Set (FundamentalGroup X (p e)))
      rw [Subgroup.normalizer_eq_top_iff.mpr (hnormal e)]
      trivial
    obtain ⟨phi, hphi⟩ :=
      (mem_coveringNormalizer_iff_exists_deck cov e (g⁻¹)).1 hnorm_inv
    refine ⟨phi, ?_⟩
    have hphi' : phi • e = (coveringEndpoint cov e g).1 := by
      simpa using hphi
    simpa [z] using hphi'.trans (congrArg Subtype.val hg)

/-- For a path-connected covering of a path-connected, locally
path-connected base, normality is detected at one chosen point of the total
space. -/
theorem isNormalCovering_iff_imageSubgroup_normal
    {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : CoveringMap p) [PathConnectedSpace E]
    [PathConnectedSpace X] [LocallyPathConnectedSpace X] (e₀ : E) :
    IsNormalCovering p ↔ (coveringImageSubgroup cov e₀).Normal := by
  letI : LocallyPathConnectedSpace E := cov.locPathConnectedSpace
  constructor
  · intro h
    exact normalCovering_imageSubgroup_normal h e₀
  · intro hnormal
    apply (isNormalCovering_iff_forall_imageSubgroup_normal cov e₀).2
    intro e
    exact (coveringImageSubgroup_normal_iff_pathChange cov
      (PathConnectedSpace.somePath e₀ e)).1 hnormal

/-- The same normal-cover criterion in Hatcher's path-product (`PiOne`)
convention. -/
theorem isNormalCovering_iff_piOneImageSubgroup_normal
    {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : CoveringMap p) [PathConnectedSpace E]
    [PathConnectedSpace X] [LocallyPathConnectedSpace X] (e₀ : E) :
    IsNormalCovering p ↔ (coveringPiOneImageSubgroup cov e₀).Normal := by
  rw [coveringPiOneImageSubgroup_eq_op, Subgroup.normal_op]
  exact isNormalCovering_iff_imageSubgroup_normal cov e₀

/-- The deck-transformation group of a universal cover is Hatcher's
fundamental group of the base. -/
noncomputable def universalCoverPiOneDeckGroupMulEquiv
    {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hu : IsUniversalCoveringMap p) (e₀ : E) :
    PiOne (p e₀) ≃* DeckTransformationGroup p := by
  letI : PathConnectedSpace X := hu.pathConnectedSpace
  letI : LocallyPathConnectedSpace X := hu.locPathConnectedSpace
  letI : SimplyConnectedSpace E := hu.simplyConnectedSpace
  letI : PathConnectedSpace E := inferInstance
  let cov := hu.coveringMap
  have hnormal : IsNormalCovering p := by
    apply (isNormalCovering_iff_piOneImageSubgroup_normal cov e₀).2
    rw [coveringPiOneImageSubgroup_eq_bot_of_simplyConnected]
    infer_instance
  have hbot : coveringImageSubgroup cov e₀ = ⊥ :=
    coveringImageSubgroup_eq_bot_of_simplyConnected cov e₀
  let eBot :
      FundamentalGroup X (p e₀) ≃*
        (FundamentalGroup X (p e₀) ⧸
          (⊥ : Subgroup (FundamentalGroup X (p e₀)))) :=
    (QuotientGroup.quotientBot :
      (FundamentalGroup X (p e₀) ⧸
        (⊥ : Subgroup (FundamentalGroup X (p e₀)))) ≃*
          FundamentalGroup X (p e₀)).symm
  letI : (coveringImageSubgroup cov e₀).Normal :=
    normalCovering_imageSubgroup_normal hnormal e₀
  let eCast :
      (FundamentalGroup X (p e₀) ⧸
          (⊥ : Subgroup (FundamentalGroup X (p e₀)))) ≃*
        (FundamentalGroup X (p e₀) ⧸ coveringImageSubgroup cov e₀) :=
    QuotientGroup.quotientMulEquivOfEq hbot.symm
  exact (MulEquiv.inv' (FundamentalGroup X (p e₀))).symm |>.trans
    (eBot.trans (eCast.trans (normalCoverDeckGroupMulEquiv hnormal e₀)))

/-! ## Fundamental group of an orbit covering -/

section OrbitCoverFundamentalGroup

variable {G : Type u} {Y : Type v}
  [Group G] [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]

/-- For a path-connected, locally path-connected covering space action, the
acting group is the quotient of the orbit-space fundamental group by the image
of the fundamental group upstairs. -/
noncomputable def actionFundamentalGroupQuotientMulEquiv
    [PathConnectedSpace Y] [LocallyPathConnectedSpace Y]
    (h : IsCoveringSpaceAction G Y) (y₀ : Y) :
    let cov := orbitProjection_isNormalCovering h
    letI : (coveringImageSubgroup cov.1 y₀).Normal :=
      normalCovering_imageSubgroup_normal cov y₀
    G ≃* (FundamentalGroup (OrbitSpace G Y) (orbitProjection G Y y₀) ⧸
      coveringImageSubgroup cov.1 y₀) := by
  let cov := orbitProjection_isNormalCovering h
  letI : (coveringImageSubgroup cov.1 y₀).Normal :=
    normalCovering_imageSubgroup_normal cov y₀
  exact (actionDeckTransformationMulEquiv h).trans
    (normalCoverDeckGroupMulEquiv cov y₀).symm

end OrbitCoverFundamentalGroup

end
end HatcherLib
