import HatcherLib.Ch1.SubgroupCover

/-!
# Chapter 1: the classification theorem for based covering spaces

This module packages path-connected based covers of a fixed space and proves
the based form of Hatcher's covering-space classification theorem.  Equality
in the quotient is shown to mean an actual basepoint-preserving equivalence
over the base, rather than merely equality of an auxiliary invariant.
-/

namespace HatcherLib

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

private theorem monoidHom_range_op {G H : Type u} [Group G] [Group H]
    (m : G →* H) : (MonoidHom.op m).range = m.range.op := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    change m z.unop ∈ m.range
    exact ⟨z.unop, rfl⟩
  · intro hy
    change y.unop ∈ m.range at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨MulOpposite.op z, ?_⟩
    apply MulOpposite.unop_injective
    simpa using hz

/-- A path-connected covering of `X` equipped with a point over `x₀`.

The topology is stored explicitly so that covers with different total spaces
can occur in a single type. -/
structure BasedConnectedCover (X : Type u) [TopologicalSpace X] (x₀ : X) where
  Total : Type u
  topology : TopologicalSpace Total
  proj : Total → X
  point : Total
  point_proj : proj point = x₀
  covering : @CoveringMap Total X topology inferInstance proj
  pathConnected : @PathConnectedSpace Total topology

namespace BasedConnectedCover

instance (c : BasedConnectedCover X x₀) : TopologicalSpace c.Total :=
  c.topology

instance (c : BasedConnectedCover X x₀) : PathConnectedSpace c.Total :=
  c.pathConnected

instance (c : BasedConnectedCover X x₀) [LocallyPathConnectedSpace X] :
    LocallyPathConnectedSpace c.Total :=
  c.covering.locPathConnectedSpace

/-- The subgroup of `PiOne x₀` induced by a based connected cover. -/
def imageSubgroup (c : BasedConnectedCover X x₀) : Subgroup (PiOne x₀) :=
  (inducedPiOneOfEq ⟨c.proj, c.covering.continuous⟩ c.point_proj).range

/-- Two based connected covers induce the same subgroup exactly when they are
basepoint-preservingly equivalent over the base. -/
theorem imageSubgroup_eq_iff_nonempty_basedCoveringEquiv
    [LocallyPathConnectedSpace X] (c d : BasedConnectedCover X x₀) :
    imageSubgroup c = imageSubgroup d ↔
      Nonempty (BasedCoveringEquiv c.proj d.proj c.point d.point) := by
  rcases c with ⟨T, topT, p, e, hp, covp, pcT⟩
  rcases d with ⟨U, topU, q, f, hq, covq, pcU⟩
  dsimp only at hp hq ⊢
  letI : TopologicalSpace T := topT
  letI : PathConnectedSpace T := pcT
  letI : LocallyPathConnectedSpace T := covp.locPathConnectedSpace
  letI : TopologicalSpace U := topU
  letI : PathConnectedSpace U := pcU
  letI : LocallyPathConnectedSpace U := covq.locPathConnectedSpace
  subst x₀
  rw [nonempty_basedCoveringEquiv_iff_piOneRanges_eq covp covq hq.symm]
  simp only [imageSubgroup, fundamentalGroup_mapOfEq_rfl, inducedPiOneOfEq,
    monoidHom_range_op]
  exact Subgroup.op_injective.eq_iff

/-- The setoid whose classes are based isomorphism classes of connected
covering spaces.  The preceding theorem identifies this relation with
nonemptiness of `BasedCoveringEquiv`. -/
def isomorphismSetoid (X : Type u) [TopologicalSpace X] (x₀ : X) :
    Setoid (BasedConnectedCover X x₀) where
  r c d := imageSubgroup c = imageSubgroup d
  iseqv := {
    refl := fun _ ↦ rfl
    symm := fun h ↦ h.symm
    trans := fun h k ↦ h.trans k }

/-- Based isomorphism classes of path-connected covers of `(X, x₀)`. -/
abbrev IsomorphismClass (X : Type u) [TopologicalSpace X] (x₀ : X) :=
  Quotient (isomorphismSetoid X x₀)

/-- Send a based covering-space isomorphism class to its induced subgroup. -/
def classificationMap :
    IsomorphismClass X x₀ → Subgroup (PiOne x₀) :=
  Quotient.lift imageSubgroup (fun _ _ h ↦ h)

/-- Equality of representatives in the quotient is precisely existence of a
based covering equivalence. -/
theorem mk_eq_iff_nonempty_basedCoveringEquiv
    [LocallyPathConnectedSpace X] (c d : BasedConnectedCover X x₀) :
    Quotient.mk (isomorphismSetoid X x₀) c =
        Quotient.mk (isomorphismSetoid X x₀) d ↔
      Nonempty (BasedCoveringEquiv c.proj d.proj c.point d.point) := by
  rw [Quotient.eq]
  exact imageSubgroup_eq_iff_nonempty_basedCoveringEquiv c d

/-- The connected based cover constructed from a subgroup by quotienting the
path-class universal cover by the corresponding deck subgroup. -/
noncomputable def ofSubgroup
    [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (hsemi : SemilocallySimplyConnected X) (x₀ : X)
    (H : Subgroup (PiOne x₀)) : BasedConnectedCover X x₀ := by
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
  exact
    { Total := OrbitSpace S (UniversalCoverConstruction.Space x₀)
      topology := inferInstance
      proj := pH
      point := eH
      point_proj := rfl
      covering := covH
      pathConnected := subgroupOrbitSpace_pathConnectedSpace S }

/-- The subgroup cover constructed from `H` induces exactly `H`. -/
theorem imageSubgroup_ofSubgroup
    [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (hsemi : SemilocallySimplyConnected X) (x₀ : X)
    (H : Subgroup (PiOne x₀)) :
    imageSubgroup (ofSubgroup hsemi x₀ H) = H := by
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
  let hbase : pH eH = x₀ := rfl
  let f : C(OrbitSpace S (UniversalCoverConstruction.Space x₀), X) :=
    ⟨pH, covH.continuous⟩
  change (inducedPiOneOfEq f hbase).range = H
  have hmap : FundamentalGroup.mapOfEq f hbase =
      FundamentalGroup.map f eH := by
    have hb : hbase = (rfl : pH eH = pH eH) := Subsingleton.elim _ _
    rw [hb]
    exact fundamentalGroup_mapOfEq_rfl f eH
  unfold inducedPiOneOfEq
  calc
    (MonoidHom.op (FundamentalGroup.mapOfEq f hbase)).range =
        (MonoidHom.op (FundamentalGroup.map f eH)).range :=
      congrArg (fun m ↦ (MonoidHom.op m).range) hmap
    _ = H := coveringPiOneImageSubgroup_universalCoverDeckSubgroup hu e₀ H

/-- The classification map is injective: equal subgroups give based
isomorphic connected covers. -/
theorem classificationMap_injective :
    Function.Injective (classificationMap (X := X) (x₀ := x₀)) := by
  intro a b h
  refine Quotient.inductionOn₂ a b ?_ h
  intro c d hcd
  exact Quotient.sound hcd

/-- Every subgroup is represented by a based connected covering space. -/
theorem classificationMap_surjective
    [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (hsemi : SemilocallySimplyConnected X) (x₀ : X) :
    Function.Surjective (classificationMap (X := X) (x₀ := x₀)) := by
  intro H
  refine ⟨Quotient.mk (isomorphismSetoid X x₀) (ofSubgroup hsemi x₀ H), ?_⟩
  exact imageSubgroup_ofSubgroup hsemi x₀ H

/-- Hatcher Theorem 1.38, based form: based isomorphism classes of
path-connected covering spaces correspond bijectively to subgroups of the
fundamental group. -/
noncomputable def classificationEquiv
    [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (hsemi : SemilocallySimplyConnected X) (x₀ : X) :
    IsomorphismClass X x₀ ≃ Subgroup (PiOne x₀) :=
  Equiv.ofBijective classificationMap
    ⟨classificationMap_injective, classificationMap_surjective hsemi x₀⟩

end BasedConnectedCover

namespace IsUniversalCoveringMap

variable {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
variable {p : E → X} {q : F → X}

/-- A universal cover covers every path-connected cover of the same base.

This strengthens `existsUnique_mapToCover`: the unique based lift is itself a
covering map.  It is constructed by quotienting the universal cover by the
deck subgroup corresponding to the target cover, then using based covering
classification to identify that orbit cover with the target. -/
theorem existsUnique_coveringMapToCover
    (hu : IsUniversalCoveringMap p) (covq : CoveringMap q)
    [PathConnectedSpace F] (e₀ : E) (f₀ : F)
    (hbase : p e₀ = q f₀) :
    ∃! lift : C(E, F),
      lift e₀ = f₀ ∧ q ∘ (lift : E → F) = p ∧ CoveringMap lift := by
  letI : PathConnectedSpace X := hu.pathConnectedSpace
  letI : LocallyPathConnectedSpace X := hu.locPathConnectedSpace
  letI : SimplyConnectedSpace E := hu.simplyConnectedSpace
  letI : PathConnectedSpace E := inferInstance
  let cF : BasedConnectedCover X (p e₀) :=
    { Total := F
      topology := inferInstance
      proj := q
      point := f₀
      point_proj := hbase.symm
      covering := covq
      pathConnected := inferInstance }
  let H := cF.imageSubgroup
  let S := universalCoverDeckSubgroup hu e₀ H
  let pH := subgroupOrbitMap (p := p) S
  let eH := orbitProjection S E e₀
  let covH := subgroupOrbitMap_isCoveringMap hu.coveringMap hu.surjective S
  let cH : BasedConnectedCover X (p e₀) :=
    { Total := OrbitSpace S E
      topology := inferInstance
      proj := pH
      point := eH
      point_proj := rfl
      covering := covH
      pathConnected := subgroupOrbitSpace_pathConnectedSpace S }
  have hcH : cH.imageSubgroup = H := by
    let hbaseH : pH eH = p e₀ := rfl
    let f : C(OrbitSpace S E, X) := ⟨pH, covH.continuous⟩
    change (inducedPiOneOfEq f hbaseH).range = H
    have hmap : FundamentalGroup.mapOfEq f hbaseH =
        FundamentalGroup.map f eH := by
      have hb : hbaseH = (rfl : pH eH = pH eH) := Subsingleton.elim _ _
      rw [hb]
      exact fundamentalGroup_mapOfEq_rfl f eH
    unfold inducedPiOneOfEq
    calc
      (MonoidHom.op (FundamentalGroup.mapOfEq f hbaseH)).range =
          (MonoidHom.op (FundamentalGroup.map f eH)).range :=
        congrArg (fun m ↦ (MonoidHom.op m).range) hmap
      _ = H := coveringPiOneImageSubgroup_universalCoverDeckSubgroup hu e₀ H
  have hcF : cF.imageSubgroup = H := rfl
  obtain ⟨h⟩ :=
    (BasedConnectedCover.imageSubgroup_eq_iff_nonempty_basedCoveringEquiv cH cF).mp
      (hcH.trans hcF.symm)
  let lift : C(E, F) :=
    ⟨h.toHomeomorph ∘ orbitProjection S E,
      h.toHomeomorph.continuous.comp orbitProjection_continuous⟩
  have hlift₀ : lift e₀ = f₀ := by
    change h.toHomeomorph (orbitProjection S E e₀) = f₀
    exact h.map_basepoint
  have hlifts : q ∘ (lift : E → F) = p := by
    funext e
    change q (h.toHomeomorph (orbitProjection S E e)) = p e
    calc
      q (h.toHomeomorph (orbitProjection S E e)) =
          pH (orbitProjection S E e) := congrFun h.commutes _
      _ = p e := rfl
  have covLift : CoveringMap lift := by
    change IsCoveringMap (h.toHomeomorph ∘ orbitProjection S E)
    exact (subgroupOrbitProjection_isCoveringMap hu.coveringMap S).homeomorph_comp
      h.toHomeomorph
  refine ⟨lift, ⟨hlift₀, hlifts, covLift⟩, ?_⟩
  intro other hother
  exact (hu.existsUnique_mapToCover covq hbase).unique
    ⟨hother.1, hother.2.1⟩ ⟨hlift₀, hlifts⟩

end IsUniversalCoveringMap

end

end HatcherLib
