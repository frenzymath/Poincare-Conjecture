import Mathlib.Topology.Algebra.OpenSubgroup
import LeeSmoothLib.Ch02.Sec02_09.Proposition_2_15
import LeeSmoothLib.Ch07.Sec07_46.Definition_7_46_extra_3
-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` identified `Subgroup.connectedComponentOfOne` as the
-- canonical owner of the identity component. The diffeomorphism clause is packaged below through
-- the source-facing left-translation map from Definition 7.46-extra-3.

open scoped LieGroup Manifold ContDiff

universe u𝕜 uE uH uG

section LieGroupIdentityComponent

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H] [LocallyConnectedSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [IsTopologicalGroup G] [LieGroup I ∞ G]

/-- Helper for Proposition 7.15: conjugation preserves the identity component of a Lie group. -/
lemma identityComponentConjMem {g x : G} (hx : x ∈ connectedComponent (1 : G)) :
    g * x * g⁻¹ ∈ connectedComponent (1 : G) := by
  -- Conjugation carries the connected component of `1` into the connected component of its image.
  have hsubset :=
    Continuous.image_connectedComponent_subset (IsTopologicalGroup.continuous_conj g) (1 : G)
  have himage : g * x * g⁻¹ ∈ (fun h : G => g * h * g⁻¹) '' connectedComponent (1 : G) :=
    ⟨x, hx, rfl⟩
  simpa using hsubset himage

/-- The identity component `Subgroup.connectedComponentOfOne G` of a Lie group is normal. -/
instance identityComponent_normal : (Subgroup.connectedComponentOfOne G).Normal where
  -- Normality follows from the conjugation-invariance of the identity component.
  conj_mem x hx g := identityComponentConjMem (g := g) (x := x) hx

/-- Helper: the carrier of `Subgroup.connectedComponentOfOne G` is connected. -/
theorem identityComponent_isConnected :
    IsConnected ((Subgroup.connectedComponentOfOne G : Set G)) := by
  -- This carrier is definitionally the connected component of `1`.
  change IsConnected (connectedComponent (1 : G))
  exact isConnected_connectedComponent

/-- The identity component `Subgroup.connectedComponentOfOne G` of a Lie group is open. -/
theorem identityComponent_isOpen {J : ModelWithCorners 𝕜 E H} [LieGroup J ∞ G] :
    IsOpen ((Subgroup.connectedComponentOfOne G : Set G)) := by
  -- A Lie group modeled on a locally connected chart space is locally connected.
  letI : LocallyConnectedSpace G := ChartedSpace.locallyConnectedSpace H G
  -- The carrier is definitionally the connected component of `1`.
  change IsOpen (connectedComponent (1 : G) : Set G)
  exact isOpen_connectedComponent

/-- A connected open subgroup of a Lie group is its identity component. -/
theorem connected_openSubgroup_eq_identityComponent (K : OpenSubgroup G)
    (hK_connected : IsConnected (K : Set G)) :
    K.toSubgroup = Subgroup.connectedComponentOfOne G := by
  -- Show each subgroup contains exactly the connected component of the identity.
  refine le_antisymm ?_ ?_
  · intro x hx
    exact hK_connected.subset_connectedComponent K.one_mem hx
  · intro x hx
    exact K.isClopen.connectedComponent_subset K.one_mem hx

section ConnectedComponentDiffeomorph

/-- Helper: each connected component of a Lie group is open. -/
theorem connectedComponent_isOpen {J : ModelWithCorners 𝕜 E H} [LieGroup J ∞ G] (g : G) :
    IsOpen (connectedComponent g : Set G) := by
  -- A Lie group modeled on a locally connected chart space is locally connected.
  letI : LocallyConnectedSpace G := ChartedSpace.locallyConnectedSpace H G
  exact isOpen_connectedComponent

/-- Helper for Proposition 7.15: the restricted image of left translation on the identity
component is the connected component of `g`. -/
lemma leftTranslationRestrictOpenImage_eq_connectedComponent (g : G) :
    (leftTranslationDiffeomorph (I := I) g).restrictOpenImage
        (⟨(Subgroup.connectedComponentOfOne G : Set G), identityComponent_isOpen (J := I)⟩ :
          TopologicalSpace.Opens G) =
      (⟨connectedComponent g, connectedComponent_isOpen (J := I) g⟩ : TopologicalSpace.Opens G) := by
  ext x
  -- Rewrite the open-image carrier as a range statement and prove both inclusions directly.
  change
    x ∈ Set.range
        (fun y :
          (⟨(Subgroup.connectedComponentOfOne G : Set G), identityComponent_isOpen (J := I)⟩ :
            TopologicalSpace.Opens G) ↦ leftTranslationDiffeomorph (I := I) g y) ↔
      x ∈ connectedComponent g
  constructor
  · rintro ⟨y, rfl⟩
    -- Left translation maps the identity component into the component of `g`.
    have hsubset :=
      Continuous.image_connectedComponent_subset (continuous_const_mul g) (1 : G)
    have hy :
        leftTranslationDiffeomorph (I := I) g y ∈
          (fun z : G => g * z) '' connectedComponent (1 : G) := by
      refine ⟨y, y.2, ?_⟩
      simp [leftTranslationDiffeomorph_apply]
    simpa [leftTranslationDiffeomorph_apply, mul_one] using hsubset hy
  · intro hx
    -- Translate back by `g⁻¹` to land in the identity component.
    have hsubset :=
      Continuous.image_connectedComponent_subset (continuous_const_mul g⁻¹) g
    have hx' : g⁻¹ * x ∈ connectedComponent (1 : G) := by
      have himage : g⁻¹ * x ∈ (fun z : G => g⁻¹ * z) '' connectedComponent g :=
        ⟨x, hx, rfl⟩
      simpa [mul_assoc] using hsubset himage
    refine ⟨⟨g⁻¹ * x, hx'⟩, ?_⟩
    simp [leftTranslationDiffeomorph_apply]

/-- Proposition 7.15. Let `G` be a Lie group and let `G₀` be its identity component. Then `G₀`
is a normal subgroup of `G`, `G₀` is the only connected open subgroup of `G`, and every connected
component of `G` is diffeomorphic to `G₀`. The preceding declarations record the normality,
openness, and uniqueness clauses; this theorem records the diffeomorphism clause. -/
theorem connectedComponent_diffeomorph_identityComponent (g : G) :
    let Cg : TopologicalSpace.Opens G := ⟨connectedComponent g,
      connectedComponent_isOpen (J := I) g⟩
    let G₀ : TopologicalSpace.Opens G := ⟨(Subgroup.connectedComponentOfOne G : Set G),
      identityComponent_isOpen (J := I)⟩
    Nonempty (Cg ≃ₘ⟮I, I⟯ G₀) := by
  let Cg : TopologicalSpace.Opens G := ⟨connectedComponent g, connectedComponent_isOpen (J := I) g⟩
  let G₀ : TopologicalSpace.Opens G := ⟨(Subgroup.connectedComponentOfOne G : Set G),
    identityComponent_isOpen (J := I)⟩
  change Nonempty (Cg ≃ₘ⟮I, I⟯ G₀)
  -- Restrict left translation to the identity component and identify its open image.
  have hImage :
      (leftTranslationDiffeomorph (I := I) g).restrictOpenImage G₀ = Cg := by
    simpa [Cg, G₀] using leftTranslationRestrictOpenImage_eq_connectedComponent (I := I) (g := g)
  let e : G₀ ≃ₘ⟮I, I⟯ Cg :=
    hImage ▸ (leftTranslationDiffeomorph (I := I) g).restrictOpen G₀
  exact ⟨e.symm⟩

/-- Helper: the connected component of `g` is the image of the identity component under left
translation by `g`. -/
theorem connectedComponent_eq_leftTranslation_image_identityComponent (g : G) :
    connectedComponent g = 𝑳 I g '' (connectedComponent (1 : G) : Set G) := by
  ext x
  constructor
  · intro hx
    -- Translate `x` back to the identity component, then translate forward again.
    have hsubset :=
      Continuous.image_connectedComponent_subset (continuous_const_mul g⁻¹) g
    have hx' : g⁻¹ * x ∈ connectedComponent (1 : G) := by
      have himage : g⁻¹ * x ∈ (fun z : G => g⁻¹ * z) '' connectedComponent g :=
        ⟨x, hx, rfl⟩
      simpa [mul_assoc] using hsubset himage
    refine ⟨g⁻¹ * x, hx', ?_⟩
    simp
  · rintro ⟨y, hy, rfl⟩
    -- Left translation carries the identity component into the component of `g`.
    have hsubset :=
      Continuous.image_connectedComponent_subset (continuous_const_mul g) (1 : G)
    have hy' : g * y ∈ (fun z : G => g * z) '' connectedComponent (1 : G) :=
      ⟨y, hy, rfl⟩
    simpa [mul_one] using hsubset hy'

end ConnectedComponentDiffeomorph

end LieGroupIdentityComponent
