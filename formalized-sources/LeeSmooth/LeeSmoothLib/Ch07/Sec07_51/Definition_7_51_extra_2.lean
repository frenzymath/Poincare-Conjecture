import LeeSmoothLib.Ch07.Sec07_51.Theorem_7_35
-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` is unavailable in this environment; repository inspection verified that
-- `semidirect_product_lie_group_isomorphism` is the canonical local owner-level bridge for this
-- item.

open scoped Manifold ContDiff Pointwise

section

universe u𝕜 uE uHG uG uEN uHN uEH uHH

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable (I : ModelWithCorners 𝕜 E HG) [LieGroup I (∞ : ℕ∞ω) G]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable (I_N : ModelWithCorners 𝕜 EN HN) (I_H : ModelWithCorners 𝕜 EH HH)
variable (N H : Subgroup G)
variable [ChartedSpace HN N] [ChartedSpace HH H]
variable [LieGroup I_N (∞ : ℕ∞ω) N] [LieGroup I_H (∞ : ℕ∞ω) H]

/-- Definition 7.51-extra-2: under the hypotheses of Theorem 7.35, the ambient Lie group `G` is
the internal semidirect product of the subgroups `N` and `H`. -/
class IsInternalSemidirectProduct : Prop where
  /-- The subgroup inclusion `N ↪ G` is smooth for the chosen Lie-group structure on `N`. -/
  n_subtype_contMDiff : ContMDiff I_N I (∞ : ℕ∞ω) N.subtype
  /-- The subgroup inclusion `H ↪ G` is smooth for the chosen Lie-group structure on `H`. -/
  h_subtype_contMDiff : ContMDiff I_H I (∞ : ℕ∞ω) H.subtype
  /-- The subgroup `N` is closed in `G`. -/
  n_closed : IsClosed (N : Set G)
  /-- The subgroup `H` is closed in `G`. -/
  h_closed : IsClosed (H : Set G)
  /-- The subgroup `N` is normal in `G`. -/
  normal : N.Normal
  /-- The intersection of `N` and `H` is trivial, encoded by disjointness. -/
  disjoint : Disjoint N H
  /-- Every element of `G` is a product of an element of `N` and an element of `H`. -/
  mul_eq_univ : (N : Set G) * (H : Set G) = Set.univ

/-- The proposition of being an internal semidirect product is subsingleton. -/
instance isInternalSemidirectProduct_subsingleton :
    Subsingleton (IsInternalSemidirectProduct I I_N I_H N H) := inferInstance

/-- Helper for Definition 7.51-extra-2: the ambient conjugation formula
`(h, n) ↦ h * n * h⁻¹` is smooth. -/
theorem internalSemidirectProductAmbientConjugation_contMDiff
    (h : IsInternalSemidirectProduct I I_N I_H N H) :
    ContMDiff (I_H.prod I_N) I (∞ : ℕ∞ω)
      (fun p : H × N ↦ p.1.1 * p.2.1 * p.1.1⁻¹) := by
  -- Compose the smooth subgroup inclusions with the coordinate projections from `H × N`.
  have hHfst :
      ContMDiff (I_H.prod I_N) I (∞ : ℕ∞ω) (fun p : H × N ↦ p.1.1) :=
    h.h_subtype_contMDiff.comp contMDiff_fst
  have hNsnd :
      ContMDiff (I_H.prod I_N) I (∞ : ℕ∞ω) (fun p : H × N ↦ p.2.1) :=
    h.n_subtype_contMDiff.comp contMDiff_snd
  -- The ambient formula is built from multiplication in `G` and inversion of the `H` factor.
  simpa [mul_assoc] using (hHfst.mul hNsnd).mul hHfst.inv

/-- Helper for Definition 7.51-extra-2: ambient conjugation by an element of `H` preserves the
normal subgroup `N`. -/
theorem internalSemidirectProductConjugation_mem
    (h : IsInternalSemidirectProduct I I_N I_H N H) (p : H × N) :
    p.1.1 * p.2.1 * p.1.1⁻¹ ∈ N := by
  let _ : N.Normal := h.normal
  -- Rewrite the ambient conjugation formula back to the canonical `MulAut.conjNormal` action.
  simpa [MulAut.conjNormal_apply, mul_assoc] using
    (((MulAut.conjNormal.comp H.subtype) p.1 p.2 : N)).2

/-- Helper for Definition 7.51-extra-2: once `N ↪ G` is known to be a smooth embedding, the
conjugation action of `H` on `N` is smooth. -/
theorem internalSemidirectProductConjugationAction_contMDiff_ofIsSmoothEmbedding
    (h : IsInternalSemidirectProduct I I_N I_H N H)
    (hSubtype : Manifold.IsSmoothEmbedding I_N I (∞ : ℕ∞ω) N.subtype) :
    let _ : N.Normal := h.normal
    let θ : H →* MulAut N := MulAut.conjNormal.comp H.subtype
    ContMDiff (I_H.prod I_N) I_N (∞ : ℕ∞ω) (fun p : H × N ↦ θ p.1 p.2) := by
  let _ : N.Normal := h.normal
  let θ : H →* MulAut N := MulAut.conjNormal.comp H.subtype
  have hSubtypeMap :
      ContMDiff (I_H.prod I_N) I_N (∞ : ℕ∞ω)
        (fun p : H × N ↦
          (⟨p.1.1 * p.2.1 * p.1.1⁻¹, internalSemidirectProductConjugation_mem
            I I_N I_H N H h p⟩ : N)) :=
    Manifold.IsSmoothEmbedding.contMDiff_toSubtype_infty hSubtype
      (internalSemidirectProductAmbientConjugation_contMDiff I I_N I_H N H h)
      (internalSemidirectProductConjugation_mem I I_N I_H N H h)
  have hActionEq :
      (fun p : H × N ↦
        (⟨p.1.1 * p.2.1 * p.1.1⁻¹, internalSemidirectProductConjugation_mem
          I I_N I_H N H h p⟩ : N)) =
        fun p : H × N ↦ θ p.1 p.2 := by
    -- Compare the two subgroup-valued maps by their ambient coordinates.
    funext p
    apply Subtype.ext
    simp [θ, MulAut.conjNormal_apply, mul_assoc]
  -- Rewrite the codomain-restricted ambient formula to the canonical conjugation action.
  rw [hActionEq] at hSubtypeMap
  exact hSubtypeMap

/-- In an internal semidirect product, the induced conjugation action of `H` on `N` is smooth. -/
theorem internal_semidirect_product_conjugation_action_contMDiff
    (h : IsInternalSemidirectProduct I I_N I_H N H)
    (hN_subtype : Manifold.IsSmoothEmbedding I_N I (∞ : ℕ∞ω) N.subtype) :
    let _ : N.Normal := h.normal
    let θ : H →* MulAut N := MulAut.conjNormal.comp H.subtype
    ContMDiff (I_H.prod I_N) I_N (∞ : ℕ∞ω) (fun p : H × N ↦ θ p.1 p.2) := by
  -- The earlier helper already proves the subgroup-valued smoothness once the codomain lift
  -- through `N.subtype` is available as a smooth embedding.
  simpa using
    internalSemidirectProductConjugationAction_contMDiff_ofIsSmoothEmbedding
      I I_N I_H N H h hN_subtype

end

section

universe u𝕜 uE uHG uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable (I : ModelWithCorners 𝕜 E HG) [LieGroup I (∞ : ℕ∞ω) G]

local notation "LieSubgroupI" => @LieSubgroup 𝕜 _ E _ _ HG _ G _ _ _ I

variable (N H : LieSubgroupI)

/-- Theorem 7.35 applies to the bundled Lie-subgroup data, yielding the canonical Lie-group
isomorphism from the corresponding semidirect product onto `G`. -/
-- Route correction: expose Theorem 7.35 on its native bundled-owner surface instead of searching
-- for a nonexistent bridge from arbitrary subgroup models to `LieSubgroup`.
noncomputable def internal_semidirect_product_lie_group_isomorphism
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint N.carrier H.carrier)
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
    let _ :
        LieGroup
          ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
            (modelWithCornersSelf 𝕜 H.ModelSpace))
          (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
      semidirectProductLieGroup θ
        (lie_subgroup_conjugation_action_contMDiff
          I N H hN_closed hH_closed)
    LieGroupIsomorphism
      ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
        (modelWithCornersSelf 𝕜 H.ModelSpace))
      I (N.carrier × H.carrier) G :=
  semidirect_product_lie_group_isomorphism I N H hN_closed hH_closed hdisj hNH

@[simp] theorem internal_semidirect_product_lie_group_isomorphism_apply
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint N.carrier H.carrier)
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ)
    (p : N.carrier × H.carrier) :
    internal_semidirect_product_lie_group_isomorphism I N H hN_closed hH_closed hdisj hNH p =
      p.1.1 * p.2.1 := rfl

end
