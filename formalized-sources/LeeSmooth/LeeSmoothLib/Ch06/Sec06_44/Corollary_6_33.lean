import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import LeeSmoothLib.Ch01.Sec01.Example_1_3
import LeeSmoothLib.Ch04.Sec04_21.Proposition_4_1
import LeeSmoothLib.Ch04.Sec04_25.Theorem_4_26
import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5
import LeeSmoothLib.Ch05.Sec05_31.Definition_5_31_extra_1
import LeeSmoothLib.Ch05.Sec05_31.Proposition_5_21
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
open scoped ContDiff Manifold
open Manifold Set

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search note: `lean_leansearch` surfaced only generic immersion/local-diffeomorphism
-- lemmas, so the repair below follows the source metadata and the local `Theorem_6_32` API.

section LocalGraphs

universe uEM uEN uHM uHN uM uN

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {IM : ModelWithCorners ℝ EM HM} [IsManifold IM ∞ M]
variable {IN : ModelWithCorners ℝ EN HN} [IsManifold IN ∞ N]

/-- Helper for Corollary 6.33: the restriction of the first projection `M × N → M` to an
immersed submanifold of `M × N`. -/
def graphFirstProjection
    (S : ImmersedSubmanifold (IM.prod IN) (M × N)) : S → M :=
  fun x ↦ (S.inclusion x).1

/-- Helper for Corollary 6.33: the restriction of the second projection `M × N → N` to an
immersed submanifold of `M × N`. -/
def graphSecondProjection
    (S : ImmersedSubmanifold (IM.prod IN) (M × N)) : S → N :=
  fun x ↦ (S.inclusion x).2

/-- Helper for Corollary 6.33: the canonical vertical-slice parametrization `N → M × N`,
`y ↦ (p, y)`. -/
def verticalSliceMap (p : M) : N → M × N :=
  fun y ↦ (p, y)

/-- Helper for Corollary 6.33: the transversality predicate used in Theorem 6.32. -/
def verticalSliceMeetsTransverselyAt
    (S : ImmersedSubmanifold (IM.prod IN) (M × N)) (x : S) : Prop :=
  (mfderiv IN (IM.prod IN) (verticalSliceMap ((S.inclusion x).1)) ((S.inclusion x).2)).range ⊔
    (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) (IM.prod IN) S.inclusion x).range = ⊤

omit [FiniteDimensional ℝ EM] [FiniteDimensional ℝ EN] in
/-- Helper for Corollary 6.33: the restricted first projection of an immersed submanifold is
smooth. -/
lemma graphFirstProjection_contMDiff
    (S : ImmersedSubmanifold (IM.prod IN) (M × N)) :
    ContMDiff (modelWithCornersSelf ℝ S.ModelSpace) IM ∞ (graphFirstProjection S) := by
  -- View the restricted projection as `Prod.fst ∘ S.inclusion`.
  simpa [graphFirstProjection, Function.comp] using
    (contMDiff_fst.comp (ImmersedSubmanifold.inclusion_isImmersion_smooth S).contMDiff)

omit [FiniteDimensional ℝ EM] [FiniteDimensional ℝ EN] in
/-- Helper for Corollary 6.33: the restricted second projection of an immersed submanifold is
smooth. -/
lemma graphSecondProjection_contMDiff
    (S : ImmersedSubmanifold (IM.prod IN) (M × N)) :
    ContMDiff (modelWithCornersSelf ℝ S.ModelSpace) IN ∞ (graphSecondProjection S) := by
  -- The same normalization identifies the restricted second projection with
  -- `Prod.snd ∘ S.inclusion`.
  simpa [graphSecondProjection, Function.comp] using
    (contMDiff_snd.comp (ImmersedSubmanifold.inclusion_isImmersion_smooth S).contMDiff)

/-- Helper for Corollary 6.33: a linear map into a product has range spanning the whole product
with the vertical factor if and only if its first-factor projection is surjective. -/
lemma range_inr_sup_range_iff_surjective_fst_comp
    {V X Y : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (A : V →ₗ[ℝ] X × Y) :
    (LinearMap.inr ℝ X Y).range ⊔ A.range = ⊤ ↔
      Function.Surjective ((LinearMap.fst ℝ X Y).comp A) := by
  constructor
  · intro h u
    -- Decompose `(u, 0)` into a vertical correction term plus a point in the image of `A`.
    have huTop : (u, (0 : Y)) ∈ (⊤ : Submodule ℝ (X × Y)) := by
      trivial
    have hu : (u, (0 : Y)) ∈ (LinearMap.inr ℝ X Y).range ⊔ A.range := by
      rw [h]
      exact huTop
    rcases Submodule.mem_sup.mp hu with ⟨a, ha, b, hb, hab⟩
    rcases LinearMap.mem_range.mp ha with ⟨y, rfl⟩
    rcases LinearMap.mem_range.mp hb with ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    have hfst := congrArg Prod.fst hab
    simpa [LinearMap.comp_apply, LinearMap.inr_apply] using hfst
  · intro h
    -- Surjectivity of the horizontal projection lets us absorb any missing first coordinate into
    -- the image of `A`, leaving only a vertical term.
    rw [eq_top_iff]
    intro w _
    rcases h w.1 with ⟨z, hz⟩
    refine Submodule.mem_sup.mpr ?_
    refine ⟨LinearMap.inr ℝ X Y (w.2 - (A z).2), ?_, A z, ?_, ?_⟩
    · exact LinearMap.mem_range_self _ _
    · exact LinearMap.mem_range_self _ _
    · ext
      · simpa [LinearMap.comp_apply] using hz
      · simp [LinearMap.inr_apply]

/-- Helper for Corollary 6.33: the previous range criterion is unchanged for continuous linear
maps. -/
lemma range_inr_sup_range_iff_surjective_fst_comp_continuousLinear
    {V X Y : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : V →L[ℝ] X × Y) :
    (ContinuousLinearMap.inr ℝ X Y).range ⊔ A.range = ⊤ ↔
      Function.Surjective ((ContinuousLinearMap.fst ℝ X Y).comp A) := by
  -- Freeze the coercion from continuous linear maps to linear maps once.
  simpa using
    (range_inr_sup_range_iff_surjective_fst_comp A.toLinearMap :
      (LinearMap.inr ℝ X Y).range ⊔ A.toLinearMap.range = ⊤ ↔
        Function.Surjective ((LinearMap.fst ℝ X Y).comp A.toLinearMap))

omit [FiniteDimensional ℝ EM] [FiniteDimensional ℝ EN] in
/-- Helper for Corollary 6.33: the derivative of the restricted first projection is the first
factor projection after the derivative of the inclusion. -/
lemma graphFirstProjection_mfderiv_eq_fst_comp
    (S : ImmersedSubmanifold (IM.prod IN) (M × N)) (x : S) :
    mfderiv (modelWithCornersSelf ℝ S.ModelSpace) IM (graphFirstProjection S) x =
      (ContinuousLinearMap.fst ℝ
        (TangentSpace IM (graphFirstProjection S x))
        (TangentSpace IN (graphSecondProjection S x))).comp
        (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) (IM.prod IN) S.inclusion x) := by
  -- Read the restricted first projection as `Prod.fst ∘ S.inclusion` and differentiate once.
  have hg := ((contMDiff_fst.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasMFDerivAt :
    HasMFDerivAt (IM.prod IN) IM Prod.fst (S.inclusion x)
      (mfderiv (IM.prod IN) IM Prod.fst (S.inclusion x)))
  have hf :
      HasMFDerivAt (modelWithCornersSelf ℝ S.ModelSpace) (IM.prod IN) S.inclusion x
        (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) (IM.prod IN) S.inclusion x) :=
    (((ImmersedSubmanifold.inclusion_isImmersion_smooth S).contMDiff.mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)).hasMFDerivAt)
  simpa [graphFirstProjection, graphSecondProjection, Function.comp] using
    (HasMFDerivAt.comp x hg hf).mfderiv

omit [FiniteDimensional ℝ EM] [FiniteDimensional ℝ EN] [IsManifold IM ∞ M] [IsManifold IN ∞ N] in
/-- Helper for Corollary 6.33: the derivative of the vertical slice map is the canonical inclusion
of the second factor. -/
lemma verticalSliceMap_mfderiv
    (p : M) (q : N) :
    mfderiv IN (IM.prod IN) (verticalSliceMap p) q =
      ContinuousLinearMap.inr ℝ (TangentSpace IM p) (TangentSpace IN q) := by
  -- The vertical slice is the product of the constant map `p` and the identity on `N`.
  simpa [verticalSliceMap] using
    (mfderiv_prod_right :
      mfderiv IN (IM.prod IN) (fun y : N ↦ (p, y)) q =
        ContinuousLinearMap.inr ℝ (TangentSpace IM p) (TangentSpace IN q))

omit [FiniteDimensional ℝ EM] [FiniteDimensional ℝ EN] in
/-- Helper for Corollary 6.33: vertical-slice transversality at `x` is equivalent to surjectivity
of the derivative of the restricted first projection at `x`. -/
lemma verticalSliceMeetsTransverselyAt_iff_surjective_graphFirstProjectionMfderiv
    (S : ImmersedSubmanifold (IM.prod IN) (M × N)) (x : S) :
    verticalSliceMeetsTransverselyAt S x ↔
      Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) IM (graphFirstProjection S) x) := by
  -- Normalize both derivatives into maps on the product tangent space, then apply the linear
  -- algebra range criterion.
  rw [verticalSliceMeetsTransverselyAt, verticalSliceMap_mfderiv]
  rw [graphFirstProjection_mfderiv_eq_fst_comp]
  let _ : NormedAddCommGroup (TangentSpace (modelWithCornersSelf ℝ S.ModelSpace) x) :=
    inferInstanceAs (NormedAddCommGroup S.ModelSpace)
  let _ : NormedSpace ℝ (TangentSpace (modelWithCornersSelf ℝ S.ModelSpace) x) :=
    inferInstanceAs (NormedSpace ℝ S.ModelSpace)
  exact range_inr_sup_range_iff_surjective_fst_comp_continuousLinear
    (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) (IM.prod IN) S.inclusion x)

omit [IsManifold IM ∞ M] [IsManifold IN ∞ N] in
/-- Helper for Corollary 6.33: an immersed submanifold of a finite-dimensional product manifold
has finite-dimensional model space as soon as it has one point. -/
lemma finiteDimensionalModelSpaceOfPoint
    (S : ImmersedSubmanifold (IM.prod IN) (M × N)) (x : S) :
    FiniteDimensional ℝ S.ModelSpace := by
  let hImm := S.inclusion_isImmersion.isImmersionAt x
  -- The immersion normal form identifies `S.ModelSpace × hImm.complement` with the ambient
  -- product model space, so that product is finite-dimensional.
  let _ : FiniteDimensional ℝ (S.ModelSpace × hImm.complement) :=
    FiniteDimensional.of_injective hImm.equiv.toLinearMap hImm.equiv.injective
  -- Projecting to the first factor then shows `S.ModelSpace` itself is finite-dimensional.
  exact
    FiniteDimensional.of_injective
      (ContinuousLinearMap.inl ℝ S.ModelSpace hImm.complement).toLinearMap
      LinearMap.inl_injective

/-- A neighborhood of `x` in an immersed submanifold is identified by the inclusion map with the
graph of a smooth map defined on an open neighborhood of the first coordinate of `S.inclusion x`.
-/
def isLocalGraphAt
    (S : ImmersedSubmanifold (IM.prod IN) (M × N))
    (x : S) : Prop :=
  ∃ U : TopologicalSpace.Opens M, (S.inclusion x).1 ∈ (U : Set M) ∧
    ∃ V : TopologicalSpace.Opens S, x ∈ (V : Set S) ∧
      ∃ f : U → N,
        ContMDiff IM IN ∞ f ∧
          Set.range (fun y : V ↦ S.inclusion y.1) = Set.range (fun u : U ↦ ((u : M), f u))

/-- Helper for Corollary 6.33: near `x`, each nearby vertical slice over `M` meets `S` in at most
one point. Equivalently, the restricted first projection is locally injective near `x`. -/
def hasLocallyUniqueVerticalSliceAt
    (S : ImmersedSubmanifold (IM.prod IN) (M × N))
    (x : S) : Prop :=
  ∃ U : TopologicalSpace.Opens M, (S.inclusion x).1 ∈ (U : Set M) ∧
    ∃ V : TopologicalSpace.Opens S, x ∈ (V : Set S) ∧
      ∀ y ∈ (V : Set S), ∀ z ∈ (V : Set S),
        graphFirstProjection S y = graphFirstProjection S z → y = z

omit [FiniteDimensional ℝ EM] [FiniteDimensional ℝ EN] in
/-- Helper for Corollary 6.33: a smooth local section of `graphFirstProjection S` through `x`,
together with local uniqueness of vertical slices, packages a neighborhood of `x` in `S` as the
graph of a smooth map over a neighborhood of `graphFirstProjection S x`. -/
lemma isLocalGraphAt_of_localSection_and_uniqueSlices
    (S : ImmersedSubmanifold (IM.prod IN) (M × N))
    (x : S)
    (U₀ : TopologicalSpace.Opens M)
    (hxU₀ : graphFirstProjection S x ∈ (U₀ : Set M))
    (σ : U₀ → S)
    (hσSmooth : ContMDiff IM (modelWithCornersSelf ℝ S.ModelSpace) ∞ σ)
    (hσ_eq : ∀ u : U₀, graphFirstProjection S (σ u) = u)
    (hσx : σ ⟨graphFirstProjection S x, hxU₀⟩ = x)
    (hunique : hasLocallyUniqueVerticalSliceAt S x) :
    isLocalGraphAt S x := by
  obtain ⟨_, _, V₁, hxV₁, hinjV₁⟩ := hunique
  let W : TopologicalSpace.Opens U₀ :=
    TopologicalSpace.Opens.comap ⟨σ, hσSmooth.continuous⟩ V₁
  have hxW : ⟨graphFirstProjection S x, hxU₀⟩ ∈ (W : Set U₀) := by
    -- Shrink the base so the chosen section remains inside the uniqueness neighborhood `V₁`.
    simpa [W, hσx] using hxV₁
  let U₂ : TopologicalSpace.Opens M := by
    refine ⟨Subtype.val '' (W : Set U₀), ?_⟩
    exact U₀.2.isOpenMap_subtype_val _ W.2
  have hU₂_le_U₀ : U₂ ≤ U₀ :=
    Subtype.coe_image_subset (U₀ : Set M) (W : Set U₀)
  have hxU₂ : graphFirstProjection S x ∈ (U₂ : Set M) := by
    refine ⟨⟨graphFirstProjection S x, hxU₀⟩, hxW, rfl⟩
  let U : TopologicalSpace.Opens M := U₂
  have hU_le_U₀ : U ≤ U₀ := hU₂_le_U₀
  have hxU : graphFirstProjection S x ∈ (U : Set M) := hxU₂
  let σU : U → S := fun u ↦ σ (TopologicalSpace.Opens.inclusion hU_le_U₀ u)
  have hσUSmooth :
      ContMDiff IM (modelWithCornersSelf ℝ S.ModelSpace) ∞ σU := by
    have hInclusion : ContMDiff IM IM ∞ (TopologicalSpace.Opens.inclusion hU_le_U₀) :=
      contMDiff_inclusion hU_le_U₀
    -- Restrict the local section to the final base neighborhood.
    simpa [σU, Function.comp] using
      hσSmooth.comp hInclusion
  have hσU_eq : ∀ u : U, graphFirstProjection S (σU u) = u := by
    intro u
    -- On the shrunken neighborhood, the section still inverts the first projection.
    simpa [σU] using hσ_eq (TopologicalSpace.Opens.inclusion hU_le_U₀ u)
  have hmemW_of_memU₂ : ∀ u : U₂, TopologicalSpace.Opens.inclusion hU₂_le_U₀ u ∈ (W : Set U₀) := by
    intro u
    rcases u.2 with ⟨w, hw, hwu⟩
    have hEq : TopologicalSpace.Opens.inclusion hU₂_le_U₀ u = w := by
      apply Subtype.ext
      simpa using hwu.symm
    exact hEq.symm ▸ hw
  have hσU_mem : ∀ u : U, σU u ∈ (V₁ : Set S) := by
    intro u
    -- Membership in the `U₂` image remembers exactly that the section lands in `V₁`.
    have hWmem :
        TopologicalSpace.Opens.inclusion hU₂_le_U₀ u ∈ (W : Set U₀) :=
      hmemW_of_memU₂ u
    simpa [W, σU] using hWmem
  let f : U → N := fun u ↦ graphSecondProjection S (σU u)
  have hf : ContMDiff IM IN ∞ f := by
    -- The graphing map is the second projection of the smooth local section.
    simpa [f, Function.comp] using (graphSecondProjection_contMDiff S).comp hσUSmooth
  have hσU_graph : ∀ u : U, S.inclusion (σU u) = ((u : M), f u) := by
    intro u
    -- A section point is determined by its first coordinate and the chosen second projection.
    apply Prod.ext
    · simpa [graphFirstProjection] using hσU_eq u
    · rfl
  let V : TopologicalSpace.Opens S :=
    V₁ ⊓ TopologicalSpace.Opens.comap
      ⟨graphFirstProjection S, (graphFirstProjection_contMDiff S).continuous⟩ U
  have hxV : x ∈ (V : Set S) := by
    exact ⟨hxV₁, hxU⟩
  have hRange :
      Set.range (fun y : V ↦ S.inclusion y.1) = Set.range (fun u : U ↦ ((u : M), f u)) := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz with ⟨y, rfl⟩
      let u : U := ⟨graphFirstProjection S y.1, y.2.2⟩
      have hyEq : y.1 = σU u := by
        apply hinjV₁ y.1 y.2.1 (σU u) (hσU_mem u)
        simpa [u] using (hσU_eq u).symm
      refine ⟨u, ?_⟩
      simpa [hyEq] using (hσU_graph u).symm
    · intro z hz
      rcases hz with ⟨u, rfl⟩
      have hσUV : σU u ∈ (V : Set S) := by
        refine ⟨hσU_mem u, ?_⟩
        change graphFirstProjection S (σU u) ∈ (U : Set M)
        simpa using hσU_eq u ▸ u.2
      refine ⟨⟨σU u, hσUV⟩, hσU_graph u⟩
  exact ⟨U, hxU, V, hxV, f, hf, hRange⟩

/-- Corollary 6.33 (Local Characterization of Graphs). Suppose `M` and `N` are smooth manifolds,
`S ⊆ M × N` is an immersed submanifold, and `x : S` maps to `(p, q)`. If `S` intersects the
submanifold `{p} × N` transversely at `(p, q)`, then there exist a neighborhood `U` of `p` in
`M` and a neighborhood `V` of `x` in `S` such that `V` is the graph of a smooth map `f : U → N`.
-/
theorem exists_local_graph_of_immersedSubmanifold_of_verticalSliceMeetsTransverselyAt
    (S : ImmersedSubmanifold (IM.prod IN) (M × N))
    (x : S)
    (htrans : verticalSliceMeetsTransverselyAt S x) :
    isLocalGraphAt S x := sorry

end LocalGraphs
