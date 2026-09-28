import HatcherLib.Ch1.GroupActions

/-!
# Chapter 1: unbased classification of connected covers

For path-connected, locally path-connected covering spaces, forgetting the
chosen point in the fiber changes equality of induced subgroups into
conjugacy.  The statement below uses mathlib's fundamental-group convention
(`FundamentalGroup`); the corresponding `PiOne` formulation is obtained by
applying `coveringPiOneImageSubgroup_eq_op`.
-/

namespace HatcherLib

noncomputable section

universe u v

variable {E : Type u} {F : Type u} {X : Type v}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
variable {p : E → X} {q : F → X}

/-- An unbased isomorphism of covering spaces over the same base. -/
structure CoveringEquiv (p : E → X) (q : F → X) where
  toHomeomorph : E ≃ₜ F
  commutes : q ∘ (toHomeomorph : E → F) = p

/-- A parser-visible alias for unbased covering equivalences. -/
def coveringEquivType (p : E → X) (q : F → X) :=
  CoveringEquiv p q

namespace CoveringEquiv

instance : CoeFun (CoveringEquiv p q) fun _ ↦ E → F :=
  ⟨fun h ↦ h.toHomeomorph⟩

/-- Reverse an unbased covering equivalence. -/
def symm (h : CoveringEquiv p q) : CoveringEquiv q p where
  toHomeomorph := h.toHomeomorph.symm
  commutes := by
    funext f
    obtain ⟨e, rfl⟩ := h.toHomeomorph.surjective f
    simpa using (congrFun h.commutes e).symm

end CoveringEquiv

/-! Equality of basepoint transports is easiest to use through this small
composition lemma.  Its proof is pointwise on loop representatives, so it
does not depend on proof-irrelevance simplification of `mapOfEq`. -/
private lemma mapOfEq_id_comp_mapOfEq
    (f : C(F, X)) {y : F} {a b : X} (h1 : f y = a) (h2 : a = b) :
    (FundamentalGroup.mapOfEq (ContinuousMap.id X) h2).comp
      (FundamentalGroup.mapOfEq f h1) =
      FundamentalGroup.mapOfEq f (h1.trans h2) := by
  ext u
  obtain ⟨γ, rfl⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath u)
  rw [MonoidHom.comp_apply, FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  rfl

/-!
Hatcher's unbased classification criterion.  The left side says that some
point of the first total space over the chosen basepoint of the second gives
a based covering equivalence.  The right side says that the two induced
subgroups, transported to `p e₀`, differ by conjugation.

The inverse on the conjugating element reflects the convention in
`coveringEndpoint_range_eq_conj_inv`: the endpoint of the lift of `g⁻¹`
has image subgroup conjugated by `g⁻¹`.
-/
theorem exists_fiber_point_basedCoveringEquiv_iff_conj
    (covp : CoveringMap p) (covq : CoveringMap q)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    (e₀ : E) (f₀ : F) (hbase : p e₀ = q f₀) :
    (∃ e₁ : E, p e₁ = q f₀ ∧
      Nonempty (BasedCoveringEquiv p q e₁ f₀)) ↔
    ∃ g : FundamentalGroup X (p e₀),
      (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ hbase.symm).range =
      Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
        (FundamentalGroup.map ⟨p, covp.continuous⟩ e₀).range := by
  constructor
  · rintro ⟨e₁, h₁, heq⟩
    let z : p ⁻¹' {p e₀} := ⟨e₁, h₁.trans hbase.symm⟩
    obtain ⟨a, ha⟩ := coveringEndpoint_surjective covp e₀ z
    obtain ⟨hendpoint, hconj⟩ :=
      coveringEndpoint_range_eq_conj_inv covp e₀ a⁻¹
    have haE : (coveringEndpoint covp e₀ a⁻¹⁻¹).1 = e₁ := by
      simpa only [inv_inv] using congrArg Subtype.val ha
    subst e₁
    have hcriterion :
        (FundamentalGroup.map ⟨p, covp.continuous⟩
          (coveringEndpoint covp e₀ a⁻¹⁻¹).1).range =
          (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ h₁.symm).range :=
      (nonempty_basedCoveringEquiv_iff_piOneRanges_eq covp covq h₁).mp heq
    have htransport :
        (FundamentalGroup.mapOfEq (ContinuousMap.id X) hendpoint.symm).comp
            (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ h₁.symm) =
          FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ hbase.symm := by
      rw [mapOfEq_id_comp_mapOfEq]
    have hPtransport :
        (FundamentalGroup.mapOfEq (ContinuousMap.id X) hendpoint.symm).comp
            (FundamentalGroup.map ⟨p, covp.continuous⟩
              (coveringEndpoint covp e₀ a⁻¹⁻¹).1) =
          FundamentalGroup.mapOfEq ⟨p, covp.continuous⟩ hendpoint.symm :=
      fundamentalGroup_basepointTransport_comp_map
        (⟨p, covp.continuous⟩ : C(E, X)) hendpoint.symm
    refine ⟨a⁻¹, ?_⟩
    have hmapped := congrArg
      (Subgroup.map
        (FundamentalGroup.mapOfEq (ContinuousMap.id X) hendpoint.symm))
      hcriterion
    rw [← MonoidHom.range_comp, ← MonoidHom.range_comp,
      hPtransport, htransport] at hmapped
    exact hmapped.symm.trans hconj
  · rintro ⟨g, hg⟩
    obtain ⟨hendpoint, hconj⟩ :=
      coveringEndpoint_range_eq_conj_inv covp e₀ g
    let e₁ := (coveringEndpoint covp e₀ g⁻¹).1
    have h₁ : p e₁ = q f₀ := hendpoint.symm.trans hbase
    have hcriterion :
        (FundamentalGroup.map ⟨p, covp.continuous⟩ e₁).range =
          (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ h₁.symm).range := by
      have htransport :
          (FundamentalGroup.mapOfEq (ContinuousMap.id X) hendpoint).comp
              (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ hbase.symm) =
            FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ h₁.symm := by
        rw [mapOfEq_id_comp_mapOfEq]
      have hPtransport :
          (FundamentalGroup.mapOfEq (ContinuousMap.id X) hendpoint).comp
              (FundamentalGroup.mapOfEq
                ⟨p, covp.continuous⟩ hendpoint.symm) =
            FundamentalGroup.map ⟨p, covp.continuous⟩ e₁ :=
        fundamentalGroup_basepointTransport_comp_mapOfEq_symm
          (⟨p, covp.continuous⟩ : C(E, X)) hendpoint
      have hmapped := congrArg
        (Subgroup.map
          (FundamentalGroup.mapOfEq (ContinuousMap.id X) hendpoint))
        (hconj.trans hg.symm)
      rw [← MonoidHom.range_comp, ← MonoidHom.range_comp,
        hPtransport, htransport] at hmapped
      exact hmapped
    exact ⟨e₁, h₁,
      (nonempty_basedCoveringEquiv_iff_piOneRanges_eq covp covq h₁).2
        hcriterion⟩

omit [TopologicalSpace X] in
/-- An unbased covering equivalence is the same as a based one after choosing
the preimage of the target basepoint. -/
theorem nonempty_coveringEquiv_iff_exists_fiber_point
    (f₀ : F) :
    Nonempty (CoveringEquiv p q) ↔
      ∃ e₁ : E, p e₁ = q f₀ ∧
        Nonempty (BasedCoveringEquiv p q e₁ f₀) := by
  constructor
  · rintro ⟨h⟩
    let e₁ := h.toHomeomorph.symm f₀
    have hbase : p e₁ = q f₀ := by
      have hproj := congrFun h.commutes e₁
      simpa [e₁] using hproj.symm
    refine ⟨e₁, hbase, ⟨?_⟩⟩
    exact
      { toHomeomorph := h.toHomeomorph
        map_basepoint := h.toHomeomorph.apply_symm_apply f₀
        commutes := h.commutes }
  · rintro ⟨e₁, _hbase, ⟨h⟩⟩
    exact ⟨{ toHomeomorph := h.toHomeomorph, commutes := h.commutes }⟩

/-- Hatcher's unbased isomorphism criterion: connected covering spaces are
isomorphic over the base exactly when their induced image subgroups are
conjugate.  Both subgroups are displayed in the raw mathlib fundamental group
at `p e₀`; the second is transported there along `hbase`. -/
theorem nonempty_coveringEquiv_iff_conj
    (covp : CoveringMap p) (covq : CoveringMap q)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    (e₀ : E) (f₀ : F) (hbase : p e₀ = q f₀) :
    Nonempty (CoveringEquiv p q) ↔
      ∃ g : FundamentalGroup X (p e₀),
        (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ hbase.symm).range =
        Subgroup.map (MulAut.conj g⁻¹).toMonoidHom
          (FundamentalGroup.map ⟨p, covp.continuous⟩ e₀).range :=
  (nonempty_coveringEquiv_iff_exists_fiber_point f₀).trans
    (exists_fiber_point_basedCoveringEquiv_iff_conj
      covp covq e₀ f₀ hbase)

end
end HatcherLib
