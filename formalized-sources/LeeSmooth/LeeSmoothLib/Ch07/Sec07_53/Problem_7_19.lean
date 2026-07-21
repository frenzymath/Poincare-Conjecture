import LeeSmoothLib.Ch07.Sec07_47.Definition_7_47_extra_1
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch07.Sec07_49.Definition_7_49_extra_1
import LeeSmoothLib.Ch05.Sec05_28.Proposition_5_3
import LeeSmoothLib.Ch05.Sec05_31.Proposition_5_18
import LeeSmoothLib.Ch05.Sec05_32.Theorem_5_29
import LeeSmoothLib.Ch07.Sec07_46.Definition_7_46_extra_3
import LeeSmoothLib.Ch07.Sec07_46.Proposition_7_1
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_11
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_16
import LeeSmoothLib.Ch07.Sec07_51.Exercise_7_31
import LeeSmoothLib.Ch07.Sec07_49.Theorem_7_21
-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall via `lean_leansearch` only surfaced generic kernel/group results; local Chapter 7
-- owners fix the semidirect-product and smooth-kernel API used below.

open scoped Manifold ContDiff Pointwise

noncomputable section

section

universe u𝕜 uEG uHG uG uEN uHN uN uEH uHH uH

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [FiniteDimensional 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [FiniteDimensional 𝕜 EN]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [FiniteDimensional 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I_G : ModelWithCorners 𝕜 EG HG}
variable {I_N : ModelWithCorners 𝕜 EN HN}
variable {I_H : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {N : Type uN} [Group N] [TopologicalSpace N] [ChartedSpace HN N]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [LieGroup I_G ∞ G] [LieGroup I_N ∞ N] [LieGroup I_H ∞ H]

local notation "SemidirectProductLieIso" =>
  @LieGroupIsomorphicToSemidirectProduct
    𝕜 inferInstance
    EN inferInstance inferInstance
    HN inferInstance
    N inferInstance inferInstance inferInstance
    EH inferInstance inferInstance
    HH inferInstance
    H inferInstance inferInstance inferInstance
    EG inferInstance inferInstance
    HG inferInstance
    G inferInstance inferInstance inferInstance
    I_N I_H I_G
    inferInstance inferInstance

/-- Helper for Problem 7-19: `KernelLieStructure φ` is the canonical Lie-group structure on
`ker φ` furnished by Proposition 7.16. -/
abbrev KernelLieStructure
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H) :=
  ContMDiffMonoidMorphism.kerLieSubgroupStructure φ

/-- Helper for Problem 7-19: `KernelLieGroupIsomorphism φ` is the type of Lie-group
isomorphisms from the canonical Lie-group structure on `ker φ` from Proposition 7.16 onto `N`.
-/
abbrev KernelLieGroupIsomorphism
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H) :=
  let W := KernelLieStructure φ
  let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
  let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
  let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instIsManifoldKer
  let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instLieGroupKer
  LieGroupIsomorphism
    (modelWithCornersSelf 𝕜 W.ModelSpace)
    I_N
    φ.toMonoidHom.ker
    N

/-- Helper for Problem 7-19: the kernel subtype inclusion coming from Proposition 7.16 is a
smooth embedding for the canonical kernel Lie-group structure. -/
lemma kernelSubtype_isSmoothEmbedding
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H) :
    let W := KernelLieStructure φ
    let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
    let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
    let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
      W.instIsManifoldKer
    let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
      W.instLieGroupKer
    Manifold.IsSmoothEmbedding
      (modelWithCornersSelf 𝕜 W.ModelSpace)
      I_G
      ∞
      (Subtype.val : φ.toMonoidHom.ker → G) := by
  let W := KernelLieStructure φ
  let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
  let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
  let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instIsManifoldKer
  let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instLieGroupKer
  let hEmb :=
    (ContMDiffMonoidMorphism.kerEmbeddedSubmanifold φ).hEmb
  let hSubtype := hEmb.isSmoothEmbedding_subtype_val
  -- Reuse the embedded-submanifold witness from Proposition 7.16 and lower the order to `∞`.
  exact isSmoothEmbedding_of_le (by simp) hSubtype

/-- Helper for Problem 7-19: the canonical inclusion `φ.toMonoidHom.ker → G` is smooth for the
kernel Lie-group structure from Proposition 7.16. -/
lemma kernelSubtype_contMDiff
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H) :
    let W := KernelLieStructure φ
    let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
    let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
    let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
      W.instIsManifoldKer
    let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
      W.instLieGroupKer
    ContMDiff
      (modelWithCornersSelf 𝕜 W.ModelSpace)
      I_G
      ∞
      (Subtype.val : φ.toMonoidHom.ker → G) := by
  let W := KernelLieStructure φ
  let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
  let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
  let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instIsManifoldKer
  let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instLieGroupKer
  -- The kernel inclusion is smooth because the embedded kernel inclusion is a smooth immersion.
  exact (kernelSubtype_isSmoothEmbedding φ).isImmersion.contMDiff

/-- Helper for Problem 7-19: the literal codomain restriction to `ker φ` is exactly the
kernel-valued map `x ↦ ⟨F x, hFker x⟩`. -/
private theorem kernelCodRestrict_eq
    {M : Type*} {F : M → G}
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H)
    (hFker : ∀ x, F x ∈ φ.toMonoidHom.ker) :
    (Set.codRestrict F (φ.toMonoidHom.ker : Set G) hFker : M → φ.toMonoidHom.ker) =
      fun x ↦ (⟨F x, hFker x⟩ : φ.toMonoidHom.ker) := rfl

/-- Helper for Problem 7-19: an ambient `C^∞` map into `G` whose image lies in `ker φ` is
`C^∞` as a map to the canonical kernel Lie-group structure from Proposition 7.16. -/
private theorem contMDiff_toKernelSubtype_infty
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H)
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
    {L : ModelWithCorners 𝕜 E' H'} [IsManifold L ∞ M]
    {F : M → G}
    (hF : ContMDiff L I_G ∞ F)
    (hFker : ∀ x, F x ∈ φ.toMonoidHom.ker) :
    let W := KernelLieStructure φ
    let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
    let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
    let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
      W.instIsManifoldKer
    ContMDiff
      L
      (modelWithCornersSelf 𝕜 W.ModelSpace)
      ∞
      (fun x ↦ (⟨F x, hFker x⟩ : φ.toMonoidHom.ker)) := by
  let W := KernelLieStructure φ
  let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
  let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
  let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instIsManifoldKer
  let S : Set G := φ.toMonoidHom.ker
  letI : TopologicalSpace S := W.instTopologicalSpaceKer
  letI : ChartedSpace W.ModelSpace S := W.instChartedSpaceKer
  letI : IsManifold
      (modelWithCornersSelf 𝕜 W.ModelSpace)
      ∞
      S := W.instIsManifoldKer
  have hEmb :
      Manifold.IsSmoothEmbedding
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        I_G
        ∞
        (Subtype.val : S → G) := by
    change
      Manifold.IsSmoothEmbedding
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        I_G
        ∞
        (Subtype.val : φ.toMonoidHom.ker → G)
    exact W.subtype_val_isSmoothEmbeddingKer
  have hCod :
      ContMDiff
        L
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        ∞
        (Set.codRestrict F S (fun x ↦ by simpa [S] using hFker x)) := by
    exact
      @Manifold.IsSmoothEmbedding.contMDiff_toSubtype_infty
        𝕜 inferInstance
        EG inferInstance inferInstance
        HG inferInstance
        I_G
        G inferInstance inferInstance inferInstance inferInstance
        W.ModelSpace inferInstance inferInstance
        W.ModelSpace inferInstance
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        S W.instChartedSpaceKer W.instIsManifoldKer
        hEmb
        E' inferInstance inferInstance
        H' inferInstance
        M inferInstance inferInstance
        L inferInstance
        F
        hF
        (fun x ↦ by simpa [S] using hFker x)
  simpa [S, kernelCodRestrict_eq] using hCod

/-- Helper for Problem 7-19: the semidirect-product quotient map `(n, h) ↦ h` is a smooth
group homomorphism for the source-side `semidirectProductGroup θ` model. -/
private lemma semidirectProductSecondProjection_map_mul
    (θ : H →* MulAut N)
    (a b : N × H) :
    ((semidirectProductGroup θ).mul a b).2 = a.2 * b.2 := by
  -- The second coordinate of the semidirect-product multiplication is the ordinary product in `H`.
  simpa [semidirectProductGroup_mul_eq]

/-- Helper for Problem 7-19: the canonical second projection of `N ⋊ H` is a smooth Lie-group
homomorphism. -/
noncomputable def semidirectProductSecondProjectionMorphism
    (θ : H →* MulAut N)
    (hθ : ContMDiff (I_H.prod I_N) I_N ∞ (fun p : H × N ↦ θ p.1 p.2)) :
    let _ : Group (N × H) := semidirectProductGroup θ
    let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
    ContMDiffMonoidMorphism (I_N.prod I_H) I_H ∞ (N × H) H :=
  let _ : Group (N × H) := semidirectProductGroup θ
  let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
  { toMonoidHom :=
      { toFun := Prod.snd
        map_one' := by
          -- The semidirect-product identity has second coordinate `1`.
          simpa [semidirectProductGroup_one_eq]
        map_mul' := fun a b ↦ semidirectProductSecondProjection_map_mul θ a b }
    contMDiff_toFun := by
      -- The projection to the `H`-factor is smooth on the product manifold.
      simpa using contMDiff_snd }

/-- Helper for Problem 7-19: the unit section `h ↦ (1, h)` is multiplicative for the
semidirect-product source group law. -/
private lemma semidirectProductUnitSection_map_mul
    (θ : H →* MulAut N)
    (a b : H) :
    let _ : Group (N × H) := semidirectProductGroup θ
    (((1 : N), a * b) : N × H) = (1, a) * (1, b) := by
  let _ : Group (N × H) := semidirectProductGroup θ
  -- The first coordinate stays `1` because every automorphism fixes the identity.
  ext <;> simp [semidirectProductGroup_mul_eq]

/-- Helper for Problem 7-19: the canonical section `h ↦ (1, h)` is a smooth Lie-group
homomorphism into `N ⋊ H`. -/
noncomputable def semidirectProductUnitSectionMorphism
    (θ : H →* MulAut N)
    (hθ : ContMDiff (I_H.prod I_N) I_N ∞ (fun p : H × N ↦ θ p.1 p.2)) :
    let _ : Group (N × H) := semidirectProductGroup θ
    let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
    ContMDiffMonoidMorphism I_H (I_N.prod I_H) ∞ H (N × H) :=
  let _ : Group (N × H) := semidirectProductGroup θ
  let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
  { toMonoidHom :=
      { toFun := fun h ↦ (1, h)
        map_one' := by
          -- The section sends the identity of `H` to the identity of `N ⋊ H`.
          simpa [semidirectProductGroup_one_eq]
        map_mul' := fun a b ↦ semidirectProductUnitSection_map_mul θ a b }
    contMDiff_toFun := by
      -- Smoothness is the product of the constant identity map on `N` with the identity on `H`.
      simpa using contMDiff_const.prodMk contMDiff_id }

/-- Helper for Problem 7-19: the canonical projection of `N ⋊ H` and the canonical unit section
split each other on the nose. -/
private lemma semidirectProductProjection_unitSection_leftInverse
    (θ : H →* MulAut N)
    (hθ : ContMDiff (I_H.prod I_N) I_N ∞ (fun p : H × N ↦ θ p.1 p.2)) :
    let _ : Group (N × H) := semidirectProductGroup θ
    let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
    Function.LeftInverse
      (semidirectProductSecondProjectionMorphism θ hθ)
      (semidirectProductUnitSectionMorphism θ hθ) := by
  let _ : Group (N × H) := semidirectProductGroup θ
  let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
  change
    ∀ h : H,
      semidirectProductSecondProjectionMorphism θ hθ
        (semidirectProductUnitSectionMorphism θ hθ h) = h
  intro h
  rfl

/-- Helper for Problem 7-19: a Lie-group isomorphism from the semidirect product `N ⋊ H` onto
`G` yields the split homomorphisms `φ : G → H` and `ψ : H → G`, and it identifies `ker φ` with
the image of the unit slice `n ↦ ΦG (n, 1)`. -/
private lemma semidirectUnitSlice_range_eq_kernel
    (θ : H →* MulAut N)
    (hθ : ContMDiff (I_H.prod I_N) I_N ∞ (fun p : H × N ↦ θ p.1 p.2))
    (ΦG :
      let _ : Group (N × H) := semidirectProductGroup θ
      let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
      LieGroupIsomorphism (I_N.prod I_H) I_G (N × H) G) :
    let _ : Group (N × H) := semidirectProductGroup θ
    let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
    let φ : ContMDiffMonoidMorphism I_G I_H ∞ G H :=
      { toMonoidHom :=
          { toFun := fun g ↦ (ΦG.symm g).2
            map_one' := by simp
            map_mul' := by
              intro g h
              rw [ΦG.symm.map_mul]
              exact semidirectProductSecondProjection_map_mul θ (ΦG.symm g) (ΦG.symm h) }
        contMDiff_toFun := by
          exact contMDiff_snd.comp ΦG.symm.contMDiff_toFun }
    Set.range (fun n : N ↦ ΦG (n, (1 : H))) = (φ.toMonoidHom.ker : Set G) := by
  let _ : Group (N × H) := semidirectProductGroup θ
  let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
  let φ : ContMDiffMonoidMorphism I_G I_H ∞ G H :=
    { toMonoidHom :=
        { toFun := fun g ↦ (ΦG.symm g).2
          map_one' := by simp
          map_mul' := by
            intro g h
            rw [ΦG.symm.map_mul]
            exact semidirectProductSecondProjection_map_mul θ (ΦG.symm g) (ΦG.symm h) }
      contMDiff_toFun := by
        exact contMDiff_snd.comp ΦG.symm.contMDiff_toFun }
  ext g
  constructor
  · rintro ⟨n, rfl⟩
    -- The unit slice lands in the kernel because the inverse has second coordinate `1`.
    change φ (ΦG (n, (1 : H))) = 1
    calc
      φ (ΦG (n, (1 : H))) = (ΦG.symm (ΦG (n, (1 : H)))).2 := rfl
      _ = (((n : N), (1 : H)) : N × H).2 := by
        exact congrArg Prod.snd (ΦG.left_inv ((n : N), (1 : H)))
      _ = 1 := rfl
  · intro hg
    have hsecond : (ΦG.symm g).2 = 1 := by
      simpa [φ] using hg
    refine ⟨(ΦG.symm g).1, ?_⟩
    -- Kernel elements have source coordinates `(n, 1)`, so they come from the unit slice.
    calc
      ΦG ((ΦG.symm g).1, (1 : H)) = ΦG ((ΦG.symm g).1, (ΦG.symm g).2) := by rw [hsecond]
      _ = ΦG (ΦG.symm g) := rfl
      _ = g := ΦG.right_inv g

/-- Helper for Problem 7-19: a Lie-group isomorphism from the semidirect product `N ⋊ H` onto
`G` yields the split homomorphisms `φ : G → H` and `ψ : H → G`, and it identifies `ker φ` with
`N` by the first coordinate of the inverse isomorphism. -/
private theorem kernelCoordinateLieIsoOfExplicitSection
    (θ : H →* MulAut N)
    (hθ : ContMDiff (I_H.prod I_N) I_N ∞ (fun p : H × N ↦ θ p.1 p.2))
    (ΦG :
      let _ : Group (N × H) := semidirectProductGroup θ
      let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
      LieGroupIsomorphism (I_N.prod I_H) I_G (N × H) G) :
    let _ : Group (N × H) := semidirectProductGroup θ
    let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
    let φ : ContMDiffMonoidMorphism I_G I_H ∞ G H :=
      { toMonoidHom :=
          { toFun := fun g ↦ (ΦG.symm g).2
            map_one' := by simp
            map_mul' := by
              intro g h
              rw [ΦG.symm.map_mul]
              exact semidirectProductSecondProjection_map_mul θ (ΦG.symm g) (ΦG.symm h) }
        contMDiff_toFun := by
          exact contMDiff_snd.comp ΦG.symm.contMDiff_toFun }
    ∃ _ :
      let W := KernelLieStructure φ
      let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
      let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
      let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
        W.instIsManifoldKer
      let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
        W.instLieGroupKer
      LieGroupIsomorphism
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        I_N
        φ.toMonoidHom.ker
        N, True := by
  let _ : Mul (N × H) := (semidirectProductGroup θ).toMulOneClass.toMul
  let _ : One (N × H) := (semidirectProductGroup θ).toMulOneClass.toOne
  let _ : Inv (N × H) := (semidirectProductGroup θ).toInv
  let _ : Group (N × H) := semidirectProductGroup θ
  let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
  let φ : ContMDiffMonoidMorphism I_G I_H ∞ G H :=
    { toMonoidHom :=
        { toFun := fun g ↦ (ΦG.symm g).2
          map_one' := by simp
          map_mul' := by
            intro g h
            rw [ΦG.symm.map_mul]
            exact semidirectProductSecondProjection_map_mul θ (ΦG.symm g) (ΦG.symm h) }
      contMDiff_toFun := by
        exact contMDiff_snd.comp ΦG.symm.contMDiff_toFun }
  let W := KernelLieStructure φ
  let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
  let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
  let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instIsManifoldKer
  let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instLieGroupKer
  let F : φ.toMonoidHom.ker → N := fun k ↦ (ΦG.symm k.1).1
  have hFinv_mem : ∀ n : N, ΦG (n, (1 : H)) ∈ φ.toMonoidHom.ker := by
    intro n
    -- The unit slice lands in `ker φ` because `φ` reads the second semidirect coordinate.
    change φ (ΦG (n, (1 : H))) = 1
    calc
      φ (ΦG (n, (1 : H))) = (ΦG.symm (ΦG (n, (1 : H)))).2 := rfl
      _ = (((n : N), (1 : H)) : N × H).2 := by
        exact congrArg Prod.snd (ΦG.left_inv ((n : N), (1 : H)))
      _ = 1 := rfl
  let Finv : N → φ.toMonoidHom.ker := fun n ↦ ⟨ΦG (n, (1 : H)), hFinv_mem n⟩
  have hF_mul : ∀ k l : φ.toMonoidHom.ker, F (k * l) = F k * F l := by
    intro k l
    have hkKer : φ k.1 = 1 := k.2
    have hk : (ΦG.symm k.1).2 = 1 := by
      simpa [φ] using hkKer
    have hlKer : φ l.1 = 1 := l.2
    have hl : (ΦG.symm l.1).2 = 1 := by
      simpa [φ] using hlKer
    -- Kernel elements have trivial `H`-coordinate, so the first coordinate multiplies directly.
    calc
      F (k * l) = (ΦG.symm (k.1 * l.1)).1 := rfl
      _ = (((ΦG.symm k.1) * (ΦG.symm l.1) : N × H)).1 := by
        exact congrArg Prod.fst (ΦG.symm.map_mul k.1 l.1)
      _ = (ΦG.symm k.1).1 * (ΦG.symm l.1).1 := by
        rcases hkg : ΦG.symm k.1 with ⟨kN, kH⟩
        rcases hlg : ΦG.symm l.1 with ⟨lN, lH⟩
        rw [hkg] at hk
        rw [hlg] at hl
        change (kN * θ kH lN, kH * lH).1 = kN * lN
        have hk' : kH = 1 := by simpa using hk
        rw [hk']
        simp
      _ = F k * F l := rfl
  have hF_smooth :
      ContMDiff
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        I_N
        ∞
        F := by
    have hCoords :
        ContMDiff
          (modelWithCornersSelf 𝕜 W.ModelSpace)
          (I_N.prod I_H)
          ∞
          (fun k : φ.toMonoidHom.ker ↦ ΦG.symm k.1) := by
      -- Read semidirect coordinates by composing the kernel inclusion with `ΦG.symm`.
      exact ΦG.symm.contMDiff_toFun.comp (kernelSubtype_contMDiff φ)
    -- The desired kernel-coordinate map is the first projection of those semidirect coordinates.
    simpa [F] using contMDiff_fst.comp hCoords
  have hFinv_smooth :
      ContMDiff
        I_N
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        ∞
        Finv := by
    have hAmbient :
        ContMDiff I_N I_G ∞ (fun n : N ↦ ΦG (n, (1 : H))) := by
      -- Build the unit slice in `N × H`, then transport it into `G` by `ΦG`.
      exact ΦG.contMDiff_toFun.comp (contMDiff_id.prodMk contMDiff_const)
    have hSubtype :
        ContMDiff
          I_N
          (modelWithCornersSelf 𝕜 W.ModelSpace)
          ∞
          (fun n : N ↦ (⟨ΦG (n, (1 : H)), hFinv_mem n⟩ : φ.toMonoidHom.ker)) := by
      exact contMDiff_toKernelSubtype_infty φ hAmbient hFinv_mem
    simpa [Finv] using hSubtype
  have hLeft : ∀ k : φ.toMonoidHom.ker, Finv (F k) = k := by
    intro k
    have hkKer : φ k.1 = 1 := k.2
    have hk : (ΦG.symm k.1).2 = 1 := by
      simpa [φ] using hkKer
    -- Kernel elements have semidirect coordinates `(n, 1)`, so the explicit inverse recovers `k`.
    apply Subtype.ext
    calc
      ΦG ((ΦG.symm k.1).1, (1 : H))
          = ΦG ((ΦG.symm k.1).1, (ΦG.symm k.1).2) := by rw [hk]
      _ = ΦG (ΦG.symm k.1) := rfl
      _ = k.1 := ΦG.right_inv k.1
  have hRight : ∀ n : N, F (Finv n) = n := by
    intro n
    -- Applying `ΦG.symm` to the unit slice immediately reads back the first coordinate.
    calc
      F (Finv n) = (ΦG.symm (ΦG (n, (1 : H)))).1 := rfl
      _ = (((n : N), (1 : H)) : N × H).1 := by
        exact congrArg Prod.fst (ΦG.left_inv ((n : N), (1 : H)))
      _ = n := rfl
  let eKer :
      LieGroupIsomorphism
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        I_N
        φ.toMonoidHom.ker
        N :=
    { toDiffeomorph :=
        { toFun := F
          invFun := Finv
          left_inv := hLeft
          right_inv := hRight
          contMDiff_toFun := hF_smooth
          contMDiff_invFun := hFinv_smooth }
      map_mul' := hF_mul }
  exact ⟨eKer, trivial⟩

/-- Helper for Problem 7-19: a Lie-group isomorphism from the semidirect product `N ⋊ H` onto
`G` yields the split homomorphisms `φ : G → H` and `ψ : H → G`, and it identifies `ker φ` with
`N` by the first coordinate of the inverse isomorphism. -/
lemma semidirectProductSplitWitness
    (θ : H →* MulAut N)
    (hθ : ContMDiff (I_H.prod I_N) I_N ∞ (fun p : H × N ↦ θ p.1 p.2))
    (ΦG :
      let _ : Group (N × H) := semidirectProductGroup θ
      let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
      LieGroupIsomorphism (I_N.prod I_H) I_G (N × H) G) :
    let _ : Group (N × H) := semidirectProductGroup θ
    let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
    ∃ φ : ContMDiffMonoidMorphism I_G I_H ∞ G H,
      ∃ ψ : ContMDiffMonoidMorphism I_H I_G ∞ H G,
        ∃ _ :
          let W := KernelLieStructure φ
          let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
          let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
          let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
            W.instIsManifoldKer
          let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
            W.instLieGroupKer
          LieGroupIsomorphism
            (modelWithCornersSelf 𝕜 W.ModelSpace)
            I_N
            φ.toMonoidHom.ker
            N, Function.LeftInverse φ ψ := by
  let _ : Group (N × H) := semidirectProductGroup θ
  let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
  let φ : ContMDiffMonoidMorphism I_G I_H ∞ G H :=
    { toMonoidHom :=
        { toFun := fun g ↦ (ΦG.symm g).2
          map_one' := by simp
          map_mul' := by
            intro g h
            -- Rewrite through multiplicativity of `ΦG.symm`, then read off the second coordinate.
            rw [ΦG.symm.map_mul]
            exact semidirectProductSecondProjection_map_mul θ (ΦG.symm g) (ΦG.symm h) }
      contMDiff_toFun := by
        exact contMDiff_snd.comp ΦG.symm.contMDiff_toFun }
  let ψ : ContMDiffMonoidMorphism I_H I_G ∞ H G :=
    { toMonoidHom :=
        { toFun := fun h ↦ ΦG (1, h)
          map_one' := by
            calc
              ΦG (1, (1 : H)) = ΦG (1 : N × H) := by rfl
              _ = 1 := ΦG.map_one
          map_mul' := by
            intro h₁ h₂
            -- Rewrite the target product back to the source multiplication of the two section values.
            calc
              ΦG (1, h₁ * h₂) =
                  ΦG ((semidirectProductGroup θ).mul ((1 : N), h₁) ((1 : N), h₂)) := by
                simp [semidirectProductGroup_mul_eq]
              _ = ΦG (1, h₁) * ΦG (1, h₂) := by
                exact ΦG.map_mul ((1 : N), h₁) ((1 : N), h₂) }
      contMDiff_toFun := by
        exact ΦG.contMDiff_toFun.comp (contMDiff_const.prodMk contMDiff_id) }
  have hsplit : Function.LeftInverse φ ψ := by
    intro h
    -- The section `ψ` is the unit section in `N ⋊ H`, transported across `ΦG`.
    calc
      (ΦG.symm (ΦG (1, h))).2 = (((1 : N), h) : N × H).2 := by
        exact congrArg Prod.snd (ΦG.left_inv ((1 : N), h))
      _ = h := rfl
  rcases (by
      simpa [φ] using
        kernelCoordinateLieIsoOfExplicitSection θ hθ ΦG :
      ∃ _ :
        let W := KernelLieStructure φ
        let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
        let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
        let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
          W.instIsManifoldKer
        let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
          W.instLieGroupKer
        LieGroupIsomorphism
          (modelWithCornersSelf 𝕜 W.ModelSpace)
          I_N
          φ.toMonoidHom.ker
          N, True) with ⟨e, -⟩
  exact ⟨φ, ψ, e, hsplit⟩

/-- Helper for Problem 7-19: the split residual `g * (ψ (φ g))⁻¹` always lies in `ker φ`. -/
lemma splitResidual_mem_ker
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H)
    (ψ : ContMDiffMonoidMorphism I_H I_G ∞ H G)
    (hsplit : Function.LeftInverse φ ψ) (g : G) :
    g * (ψ (φ g))⁻¹ ∈ φ.toMonoidHom.ker := by
  -- Apply `φ` and simplify the resulting product using the splitting identity.
  change φ (g * (ψ (φ g))⁻¹) = 1
  calc
    φ (g * (ψ (φ g))⁻¹) = φ g * (φ (ψ (φ g)))⁻¹ := by simp
    _ = 1 := by
      rw [hsplit (φ g)]
      simp

/-- Helper for Problem 7-19: every `g : G` factors as its kernel residual times the chosen split
section value `ψ (φ g)`. -/
lemma splitResidual_mul_section
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H)
    (ψ : ContMDiffMonoidMorphism I_H I_G ∞ H G)
    (g : G) :
    (g * (ψ (φ g))⁻¹) * ψ (φ g) = g := by
  -- This is the standard cancellation identity for the split residual.
  simp [mul_assoc]

/-- Helper for Problem 7-19: conjugating a kernel element by the split section stays in
`ker φ`. -/
lemma splitConjugate_mem_ker
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H)
    (ψ : ContMDiffMonoidMorphism I_H I_G ∞ H G)
    (hsplit : Function.LeftInverse φ ψ)
    (h : H) (k : φ.toMonoidHom.ker) :
    ψ h * k.1 * (ψ h)⁻¹ ∈ φ.toMonoidHom.ker := by
  -- Apply `φ` to the conjugate and use that `k` is already in the kernel.
  change φ (ψ h * k.1 * (ψ h)⁻¹) = 1
  calc
    φ (ψ h * k.1 * (ψ h)⁻¹) = φ (ψ h) * (φ k.1 * (φ (ψ h))⁻¹) := by
      simp [mul_assoc]
    _ = h * (1 * h⁻¹) := by
      simpa [hsplit h] using congrArg (fun x ↦ h * (x * h⁻¹)) k.2
    _ = 1 := by simp

/-- Helper for Problem 7-19: conjugation by the split section `ψ h` restricts to a kernel
automorphism. -/
private noncomputable def splitKernelConjugationMulAut
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H)
    (ψ : ContMDiffMonoidMorphism I_H I_G ∞ H G)
    (hsplit : Function.LeftInverse φ ψ)
    (h : H) :
    MulAut φ.toMonoidHom.ker where
  toEquiv :=
    { toFun := fun k ↦
        ⟨ψ h * k.1 * (ψ h)⁻¹, splitConjugate_mem_ker φ ψ hsplit h k⟩
      invFun := fun k ↦
        ⟨(ψ h)⁻¹ * k.1 * ψ h, by
          -- Conjugation by `ψ h⁻¹` is the inverse kernel map.
          simpa using splitConjugate_mem_ker φ ψ hsplit h⁻¹ k⟩
      left_inv := by
        intro k
        -- The inverse conjugation cancels the forward conjugation on the kernel.
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := by
        intro k
        -- The same cancellation proves the right inverse identity.
        apply Subtype.ext
        simp [mul_assoc]
    }
  map_mul' := by
    intro k l
    -- Conjugation is multiplicative on the kernel because ambient multiplication is.
    apply Subtype.ext
    simp [mul_assoc]

/-- Helper for Problem 7-19: kernel conjugation by the split section is smooth as a map into the
canonical kernel carrier. -/
private theorem splitKernelConjugationKernelSmooth
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H)
    (ψ : ContMDiffMonoidMorphism I_H I_G ∞ H G)
    (hsplit : Function.LeftInverse φ ψ) :
    let W := KernelLieStructure φ
    let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
    let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
    let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
      W.instIsManifoldKer
    let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
      W.instLieGroupKer
    ContMDiff
      (I_H.prod (modelWithCornersSelf 𝕜 W.ModelSpace))
      (modelWithCornersSelf 𝕜 W.ModelSpace)
      ∞
      (fun p : H × φ.toMonoidHom.ker ↦ splitKernelConjugationMulAut φ ψ hsplit p.1 p.2) := by
  let W := KernelLieStructure φ
  let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
  let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
  let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instIsManifoldKer
  let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instLieGroupKer
  let ambient : H × φ.toMonoidHom.ker → G := fun p ↦ ψ p.1 * (p.2 : G) * (ψ p.1)⁻¹
  have hAmbient :
      ContMDiff
        (I_H.prod (modelWithCornersSelf 𝕜 W.ModelSpace))
        I_G
        ∞
        ambient := by
    have hSection :
        ContMDiff
          (I_H.prod (modelWithCornersSelf 𝕜 W.ModelSpace))
          I_G
          ∞
          (fun p : H × φ.toMonoidHom.ker ↦ ψ p.1) := by
      -- Pull the split section `ψ` back along the first projection.
      exact ψ.contMDiff_toFun.comp contMDiff_fst
    have hKernel :
        ContMDiff
          (I_H.prod (modelWithCornersSelf 𝕜 W.ModelSpace))
          I_G
          ∞
          (fun p : H × φ.toMonoidHom.ker ↦ (p.2 : G)) := by
      -- Read the kernel factor through the canonical subtype inclusion.
      simpa using
        (kernelSubtype_contMDiff φ).comp
          (contMDiff_snd :
            ContMDiff
              (I_H.prod (modelWithCornersSelf 𝕜 W.ModelSpace))
              (modelWithCornersSelf 𝕜 W.ModelSpace)
              ∞
              fun p : H × φ.toMonoidHom.ker ↦ p.2)
    -- The ambient conjugation formula is smooth before codomain restriction.
    simpa [ambient, mul_assoc] using hSection.mul (hKernel.mul hSection.inv)
  have hMem : ∀ p : H × φ.toMonoidHom.ker, ambient p ∈ φ.toMonoidHom.ker := by
    intro p
    exact splitConjugate_mem_ker φ ψ hsplit p.1 p.2
  have hSubtype :
      ContMDiff
        (I_H.prod (modelWithCornersSelf 𝕜 W.ModelSpace))
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        ∞
        (fun p : H × φ.toMonoidHom.ker ↦
          (⟨ambient p, hMem p⟩ : φ.toMonoidHom.ker)) := by
    exact contMDiff_toKernelSubtype_infty φ hAmbient hMem
  simpa [ambient, splitKernelConjugationMulAut] using hSubtype

/-- Helper for Problem 7-19: transporting the kernel conjugation action across `e : ker φ ≃ N`
gives the smooth `H`-action used in the converse semidirect-product construction. -/
private theorem transportedSplitActionSmooth
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H)
    (ψ : ContMDiffMonoidMorphism I_H I_G ∞ H G)
    (hsplit : Function.LeftInverse φ ψ)
    (e :
      let W := KernelLieStructure φ
      let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
      let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
      let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
        W.instIsManifoldKer
      let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
        W.instLieGroupKer
      LieGroupIsomorphism
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        I_N
        φ.toMonoidHom.ker
        N) :
    let W := KernelLieStructure φ
    let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
    let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
    let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
      W.instIsManifoldKer
    let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
      W.instLieGroupKer
    ContMDiff (I_H.prod I_N) I_N ∞
      (fun p : H × N ↦ e (splitKernelConjugationMulAut φ ψ hsplit p.1 (e.symm p.2))) := by
  let W := KernelLieStructure φ
  let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
  let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
  let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instIsManifoldKer
  let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instLieGroupKer
  have hInput :
      ContMDiff
        (I_H.prod I_N)
        (I_H.prod (modelWithCornersSelf 𝕜 W.ModelSpace))
        ∞
        (fun p : H × N ↦ (p.1, e.symm p.2)) := by
    -- Pair the identity map on `H` with the inverse kernel-coordinate diffeomorphism on `N`.
    let hSymm := e.symm.contMDiff_toFun
    exact contMDiff_fst.prodMk (hSymm.comp contMDiff_snd)
  have hKernel :
      ContMDiff
        (I_H.prod I_N)
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        ∞
        (fun p : H × N ↦ splitKernelConjugationMulAut φ ψ hsplit p.1 (e.symm p.2)) := by
    -- Feed the kernel-side smooth action with the transported pair `(h, e.symm n)`.
    simpa [Function.comp] using (splitKernelConjugationKernelSmooth φ ψ hsplit).comp hInput
  -- Postcompose the kernel-side action with the Lie-group isomorphism `e : ker φ ≃ N`.
  let hE := e.contMDiff_toFun
  exact hE.comp hKernel

/-- Helper for Problem 7-19: a split pair `φ, ψ` together with a kernel Lie-group isomorphism
`e : ker φ ≃ N` yields an explicit semidirect-product Lie-group isomorphism onto `G`. -/
private theorem splitSemidirectProductWitness
    (φ : ContMDiffMonoidMorphism I_G I_H ∞ G H)
    (ψ : ContMDiffMonoidMorphism I_H I_G ∞ H G)
    (hsplit : Function.LeftInverse φ ψ)
    (e :
      let W := KernelLieStructure φ
      let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
      let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
      let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
        W.instIsManifoldKer
      let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
        W.instLieGroupKer
      LieGroupIsomorphism
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        I_N
        φ.toMonoidHom.ker
        N) :
    SemidirectProductLieIso := by
  let W := KernelLieStructure φ
  let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
  let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
  let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instIsManifoldKer
  let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
    W.instLieGroupKer
  let eMul : φ.toMonoidHom.ker ≃* N := e.toMulEquiv
  let eMulSymm : N ≃* φ.toMonoidHom.ker := eMul.symm
  let θ : H →* MulAut N :=
    { toFun := fun h ↦
        (eMulSymm.trans
          (splitKernelConjugationMulAut φ ψ hsplit h)).trans eMul
      map_one' := by
        ext n
        -- The transported conjugation action is trivial at the identity of `H`.
        simp [eMul, eMulSymm, splitKernelConjugationMulAut]
      map_mul' := by
        intro h₁ h₂
        ext n
        -- Conjugation by `ψ (h₁ h₂)` factors as the composition of the two conjugations.
        simp [eMul, eMulSymm, splitKernelConjugationMulAut, mul_assoc] }
  let _ : Mul (N × H) := (semidirectProductGroup θ).toMulOneClass.toMul
  let _ : One (N × H) := (semidirectProductGroup θ).toMulOneClass.toOne
  let _ : Inv (N × H) := (semidirectProductGroup θ).toInv
  have hθ :
      ContMDiff (I_H.prod I_N) I_N ∞
        (fun p : H × N ↦ θ p.1 p.2) := by
    -- Transport the smooth kernel conjugation action through the kernel-coordinate isomorphism.
    simpa [θ] using transportedSplitActionSmooth φ ψ hsplit e
  let _ : Group (N × H) := semidirectProductGroup θ
  let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
  let Ffun : N × H → G := fun p ↦ ((e.symm p.1 : φ.toMonoidHom.ker) : G) * ψ p.2
  let Finv : G → N × H := fun g ↦
    (e ⟨g * (ψ (φ g))⁻¹, splitResidual_mem_ker φ ψ hsplit g⟩, φ g)
  have hKernelValue : ∀ n : N, φ (((e.symm n : φ.toMonoidHom.ker) : G)) = 1 := by
    intro n
    exact (e.symm n).2
  have hForward_mul : ∀ a b : N × H, Ffun (a * b) = Ffun a * Ffun b := by
    intro a b
    -- Normalize the semidirect multiplication and expand the transported conjugation action.
    have hAction :
        (((e.symm ((θ a.2) b.1) : φ.toMonoidHom.ker) : G)) =
          ψ a.2 * (((e.symm b.1 : φ.toMonoidHom.ker) : G)) * (ψ a.2)⁻¹ := by
      let k := splitKernelConjugationMulAut φ ψ hsplit a.2 (e.symm b.1)
      have hk :
          e.symm ((θ a.2) b.1) = k := by
        change e.symm (e k) = k
        exact e.left_inv k
      simpa [θ, k, splitKernelConjugationMulAut] using
        congrArg
          (fun x : φ.toMonoidHom.ker ↦ ((x : φ.toMonoidHom.ker) : G))
          hk
    have hMap :
        (((e.symm (a.1 * (θ a.2) b.1) : φ.toMonoidHom.ker) : G)) =
          (((e.symm a.1 : φ.toMonoidHom.ker) : G)) *
            (((e.symm ((θ a.2) b.1) : φ.toMonoidHom.ker) : G)) := by
      exact
        congrArg
          (fun x : φ.toMonoidHom.ker ↦ ((x : φ.toMonoidHom.ker) : G))
          (e.symm.map_mul a.1 ((θ a.2) b.1))
    calc
      Ffun (a * b)
          = (((e.symm a.1 : φ.toMonoidHom.ker) : G) * ψ a.2) *
              (((e.symm b.1 : φ.toMonoidHom.ker) : G) * ψ b.2) := by
          have hψ : ψ (a.2 * b.2) = ψ a.2 * ψ b.2 := by
            exact ψ.map_mul a.2 b.2
          change
            (((e.symm (a.1 * (θ a.2) b.1) : φ.toMonoidHom.ker) : G) *
                ψ (a.2 * b.2)) =
              (((e.symm a.1 : φ.toMonoidHom.ker) : G) * ψ a.2) *
                (((e.symm b.1 : φ.toMonoidHom.ker) : G) * ψ b.2)
          simpa [hψ, hMap, hAction, mul_assoc]
      _ = Ffun a * Ffun b := by simp [Ffun, mul_assoc]
  have hForward_smooth :
      ContMDiff (I_N.prod I_H) I_G ∞ Ffun := by
    have hKernel :
        ContMDiff
          (I_N.prod I_H)
          I_G
          ∞
          (fun p : N × H ↦ ((e.symm p.1 : φ.toMonoidHom.ker) : G)) := by
      let hSymm := e.symm.contMDiff_toFun
      -- The kernel coordinate is smooth after composing `e.symm` with the kernel inclusion.
      simpa using
        (kernelSubtype_contMDiff φ).comp
          (hSymm.comp
            (contMDiff_fst :
              ContMDiff (I_N.prod I_H) I_N ∞ fun p : N × H ↦ p.1))
    have hSection :
        ContMDiff
          (I_N.prod I_H)
          I_G
          ∞
          (fun p : N × H ↦ ψ p.2) := by
      -- The split section contributes the smooth `H`-factor.
      exact ψ.contMDiff_toFun.comp contMDiff_snd
    -- The forward witness is the product of the kernel factor and the split section.
    simpa [Ffun] using hKernel.mul hSection
  have hResidual_ambient :
      ContMDiff I_G I_G ∞ (fun g : G ↦ g * (ψ (φ g))⁻¹) := by
    have hSection :
        ContMDiff I_G I_G ∞ (fun g : G ↦ ψ (φ g)) := by
      -- The chosen section is smooth after precomposing with `φ`.
      exact ψ.contMDiff_toFun.comp φ.contMDiff_toFun
    -- The ambient residual is a smooth product with the inverse split section.
    simpa using contMDiff_id.mul hSection.inv
  have hResidual_subtype :
      ContMDiff
        I_G
        (modelWithCornersSelf 𝕜 W.ModelSpace)
        ∞
        (fun g : G ↦
          (⟨g * (ψ (φ g))⁻¹, splitResidual_mem_ker φ ψ hsplit g⟩ :
            φ.toMonoidHom.ker)) := by
    exact
      contMDiff_toKernelSubtype_infty
        φ
        hResidual_ambient
        (fun g ↦ splitResidual_mem_ker φ ψ hsplit g)
  have hInverse_smooth :
      ContMDiff I_G (I_N.prod I_H) ∞ Finv := by
    have hFirst :
        ContMDiff I_G I_N ∞
          (fun g : G ↦ e ⟨g * (ψ (φ g))⁻¹, splitResidual_mem_ker φ ψ hsplit g⟩) := by
      -- Postcompose the smooth kernel residual with the kernel-coordinate Lie-group isomorphism.
      exact e.contMDiff_toFun.comp hResidual_subtype
    -- Pair the transported residual with the original quotient map `φ`.
    simpa [Finv] using hFirst.prodMk φ.contMDiff_toFun
  have hForward_rightInv : ∀ g : G, Ffun (Finv g) = g := by
    intro g
    -- Evaluating the forward map on the explicit inverse collapses to the residual factorization.
    have hFirst :
        (((e.symm (e ⟨g * (ψ (φ g))⁻¹, splitResidual_mem_ker φ ψ hsplit g⟩) :
            φ.toMonoidHom.ker) : G)) =
          ((⟨g * (ψ (φ g))⁻¹, splitResidual_mem_ker φ ψ hsplit g⟩ :
            φ.toMonoidHom.ker) : G) := by
      exact
        congrArg
          (fun x : φ.toMonoidHom.ker ↦ ((x : φ.toMonoidHom.ker) : G))
          (e.left_inv ⟨g * (ψ (φ g))⁻¹, splitResidual_mem_ker φ ψ hsplit g⟩)
    calc
      Ffun (Finv g)
          = (((e.symm (e ⟨g * (ψ (φ g))⁻¹, splitResidual_mem_ker φ ψ hsplit g⟩) :
                φ.toMonoidHom.ker) : G) * ψ (φ g)) := rfl
      _ = ((⟨g * (ψ (φ g))⁻¹, splitResidual_mem_ker φ ψ hsplit g⟩ :
            φ.toMonoidHom.ker) : G) * ψ (φ g) := by
        rw [hFirst]
      _ = g := splitResidual_mul_section φ ψ g
  have hForward_second : ∀ p : N × H, φ (Ffun p) = p.2 := by
    intro p
    -- The kernel coordinate contributes nothing to `φ`, so only the split section remains.
    simp [Ffun, hKernelValue, hsplit p.2]
  have hForward_leftInv : ∀ p : N × H, Finv (Ffun p) = p := by
    intro p
    ext
    · have hResidual_eq :
          (⟨Ffun p * (ψ (φ (Ffun p)))⁻¹,
              splitResidual_mem_ker φ ψ hsplit (Ffun p)⟩ :
            φ.toMonoidHom.ker) =
            e.symm p.1 := by
        -- After computing `φ (Ffun p)`, the residual simplifies to the kernel coordinate itself.
        apply Subtype.ext
        calc
          Ffun p * (ψ (φ (Ffun p)))⁻¹
              = Ffun p * (ψ p.2)⁻¹ := by rw [hForward_second p]
          _ = (((e.symm p.1 : φ.toMonoidHom.ker) : G) * ψ p.2) * (ψ p.2)⁻¹ := by rfl
          _ = ((e.symm p.1 : φ.toMonoidHom.ker) : G) := by simp [mul_assoc]
      calc
        e ⟨Ffun p * (ψ (φ (Ffun p)))⁻¹,
            splitResidual_mem_ker φ ψ hsplit (Ffun p)⟩
            = e (e.symm p.1) := by rw [hResidual_eq]
        _ = p.1 := e.right_inv p.1
    · exact hForward_second p
  let Φ :
      LieGroupIsomorphism (I_N.prod I_H) I_G (N × H) G :=
    { toDiffeomorph :=
        { toFun := Ffun
          invFun := Finv
          left_inv := hForward_leftInv
          right_inv := hForward_rightInv
          contMDiff_toFun := hForward_smooth
          contMDiff_invFun := hInverse_smooth }
      map_mul' := hForward_mul }
  exact ⟨θ, hθ, ⟨Φ⟩⟩

/-- Problem 7-19: for finite-dimensional Lie groups `G`, `N`, and `H`, `G` is isomorphic to a
semidirect product `N ⋊ H` if and only if
there are Lie group homomorphisms `φ : G → H` and `ψ : H → G` with `φ ∘ ψ = id_H`, and the
kernel of `φ`, with the canonical smooth Lie-group structure furnished by Proposition 7.16, is
Lie-group-isomorphic to `N`. -/
theorem lie_group_isomorphic_to_semidirect_product_iff_exists_split_lie_homs :
    SemidirectProductLieIso ↔
      ∃ φ : ContMDiffMonoidMorphism I_G I_H ∞ G H,
        ∃ ψ : ContMDiffMonoidMorphism I_H I_G ∞ H G,
          ∃ _ :
            let W := KernelLieStructure φ
            let _ : TopologicalSpace φ.toMonoidHom.ker := W.instTopologicalSpaceKer
            let _ : ChartedSpace W.ModelSpace φ.toMonoidHom.ker := W.instChartedSpaceKer
            let _ : IsManifold (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
              W.instIsManifoldKer
            let _ : LieGroup (modelWithCornersSelf 𝕜 W.ModelSpace) ∞ φ.toMonoidHom.ker :=
              W.instLieGroupKer
            LieGroupIsomorphism
              (modelWithCornersSelf 𝕜 W.ModelSpace)
              I_N
              φ.toMonoidHom.ker
              N, Function.LeftInverse φ ψ := by
  constructor
  · rintro ⟨θ, hθ, ⟨ΦG⟩⟩
    -- The forward implication is the explicit extraction lemma proved just above.
    exact semidirectProductSplitWitness θ hθ ΦG
  · rintro ⟨φ, ψ, e, hsplit⟩
    -- Transport kernel conjugation across `e`, then package the explicit inverse pair.
    exact splitSemidirectProductWitness φ ψ hsplit e

end
