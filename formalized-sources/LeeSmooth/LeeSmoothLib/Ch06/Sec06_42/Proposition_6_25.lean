import LeeSmoothLib.Ch04.Sec04_25.Proposition_4_28
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch04.Sec04_25.Theorem_4_26
import LeeSmoothLib.Ch03.Sec03_14.Proposition_3_10
import LeeSmoothLib.Ch01.Sec01.Definition_1_extra_1
import LeeSmoothLib.Ch05.Sec05_29.Theorem_5_8
import LeeSmoothLib.Ch05.Sec05_32.Definition_5_32_extra_2
import LeeSmoothLib.Ch05.Sec05_32.Corollary_5_30
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_38
import LeeSmoothLib.Ch05.Sec05_36.Proposition_5_49
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import LeeSmoothLib.Ch06.Sec06_42.Definition_6_42_extra_2
-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped ContDiff Manifold NormalBundle

noncomputable section

section TubularNeighborhoodRetraction

variable {n m : ℕ}
variable {M : Set (EuclideanSpace ℝ (Fin n))}
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
variable [IsManifold (𝓡 m) ∞ M]
variable [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
variable [IsManifold (𝓡 n) ∞ (NM[n, m; M])]

-- Domain sampling pass: Proposition 6.25 lives in the embedded-submanifold / normal-bundle
-- domain. The relevant upstream owner declarations checked before refinement are
-- `NM[n, m; M]` and `π_NM[n, m; M]` from `Definition_6_42_extra_1`,
-- `NormalBundle.endpointMap`,
-- `NormalBundle.TubularNeighborhood`,
-- and `Manifold.IsSmoothSubmersion`.
-- The owner abstraction is `NormalBundle.TubularNeighborhood`; the retraction and inclusion are
-- derived maps on that owner, not primitive data of a second public wrapper.

namespace NormalBundle

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper for Proposition 6.25: in any bundle trivialization, freezing the fiber coordinate
produces a local section whose trivialization coordinate is constant near the chosen base point. -/
lemma frozenTrivializationSection_contMDiffAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : M → Type*}
    [TopologicalSpace (Bundle.TotalSpace F E)]
    [∀ x : M, TopologicalSpace (E x)]
    [∀ x : M, Zero (E x)]
    (e :
      Bundle.Trivialization
        F
        (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → M))
    {x : M} (hx : x ∈ e.baseSet) (v0 : F) :
    ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞
      (fun y : M ↦
        (e (Bundle.TotalSpace.mk' F y (e.symm y v0))).2) x := by
  -- Route correction: the earlier version hard-coded `EuclideanSpace ℝ (Fin n)` as the fiber
  -- model, but the proof only uses that the trivialization sends the constructed section to the
  -- constant coordinate `v0`.
  refine (contMDiffAt_const : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞
    (fun _ : M ↦ v0) x).congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  simpa using congrArg Prod.snd (e.apply_mk_symm hy v0)

/-- Helper for Proposition 6.25: the ambient first coordinate of
`normal_bundle_toProd n m M` is the base-point map `NM[n, m; M] → ℝ^n`, and it is smooth for the
chosen compatible smooth structure. -/
lemma piNM_baseAmbient_contMDiff [CompatibleSmoothStructure n m M] :
    ContMDiff (𝓡 n) (𝓡 n) ∞
      (fun p : NM[n, m; M] ↦ ((π_NM[n, m; M] p : M) : EuclideanSpace ℝ (Fin n))) := by
  -- Compose the smooth embedding into product coordinates with the first projection.
  simpa only [normal_bundle_toProd_fst] using
    (contMDiff_fst.comp
      (NormalBundle.isSmoothEmbedding_normal_bundle_toProd
        (n := n) (m := m) (M := M)).isImmersion.contMDiff)

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper for Proposition 6.25: the embedded inclusion `Subtype.val : M → ℝ^n` is a smooth
embedding at `C^∞` regularity. -/
lemma subtypeVal_isSmoothEmbedding :
    IsSmoothEmbedding
      (𝓡 m)
      (𝓡 n)
      ∞
      (Subtype.val : M → EuclideanSpace ℝ (Fin n)) := by
  -- Lower the embedded-submanifold owner theorem to the `C^∞` regularity used in this file.
  exact isSmoothEmbedding_of_le (by simp) IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper for Proposition 6.25: the ambient inclusion of the embedded submanifold `M ⊆ ℝ^n` is a
smooth map. -/
lemma subtype_val_contMDiff :
    ContMDiff (𝓡 m) (𝓡 n) ∞ (Subtype.val : M → EuclideanSpace ℝ (Fin n)) := by
  let hSubtypeEmbedding :
      IsSmoothEmbedding
        (𝓡 m)
        (𝓡 n)
        ∞
        (Subtype.val : M → EuclideanSpace ℝ (Fin n)) :=
    subtypeVal_isSmoothEmbedding (n := n) (m := m) (M := M)
  -- Smooth embeddings are immersions, so their underlying maps are smooth.
  exact hSubtypeEmbedding.isImmersion.contMDiff

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper for Proposition 6.25: the embedded inclusion `Subtype.val : M → ℝ^n` admits the
standard local immersion normal form around each point of `M`. -/
lemma subtypeVal_localInclusionForm (x : M) :
    ∃ _ :
      LocalNormalFormAPI.LocalCoordinateNormalFormAt
        (Subtype.val : M → EuclideanSpace ℝ (Fin n))
        x
        (LocalNormalFormAPI.rank_normal_form m n m),
      True := by
  -- Reuse the local immersion normal form of the embedded inclusion directly.
  simpa using
    LocalNormalFormAPI.smooth_immersion_local_inclusion_form
      (m := m)
      (n := n)
      (F := (Subtype.val : M → EuclideanSpace ℝ (Fin n)))
      (hF := (subtypeVal_isSmoothEmbedding (n := n) (m := m) (M := M)).isImmersion)
      x

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper for Proposition 6.25: the dimension of the embedded submanifold cannot exceed the
ambient Euclidean dimension. -/
lemma embeddedSubmanifoldDimensionLe (x : M) :
    m ≤ n := by
  let hEmb :
      IsSmoothEmbedding
        (𝓡 m)
        (𝓡 n)
        ∞
        (Subtype.val : M → EuclideanSpace ℝ (Fin n)) :=
    subtypeVal_isSmoothEmbedding (n := n) (m := m) (M := M)
  let hCont :
      ContMDiff
        (𝓡 m)
        (𝓡 n)
        ∞
        (Subtype.val : M → EuclideanSpace ℝ (Fin n)) :=
    hEmb.isImmersion.contMDiff
  have hInj :
      Function.Injective
        (mfderiv (𝓡 m) (𝓡 n) (Subtype.val : M → EuclideanSpace ℝ (Fin n)) x) := by
    -- An immersion has injective manifold derivative at every point.
    exact ((Manifold.is_immersion_iff_forall_injective_mfderiv hCont).1 hEmb.isImmersion) x
  let _ : FiniteDimensional ℝ (TangentSpace (𝓡 n) ((x : M) : EuclideanSpace ℝ (Fin n))) :=
    FiniteDimensional.of_injective
      (NormedSpace.fromTangentSpace ((x : M) : EuclideanSpace ℝ (Fin n))).toLinearMap
      (NormedSpace.fromTangentSpace ((x : M) : EuclideanSpace ℝ (Fin n))).injective
  have hle :
      Module.finrank ℝ (TangentSpace (𝓡 m) x) ≤
        Module.finrank ℝ (TangentSpace (𝓡 n) ((x : M) : EuclideanSpace ℝ (Fin n))) := by
    -- Compare the tangent-space dimensions through the injective derivative of the inclusion.
    simpa using
      LinearMap.finrank_le_finrank_of_injective
        (f := (mfderiv (𝓡 m) (𝓡 n)
          (Subtype.val : M → EuclideanSpace ℝ (Fin n)) x).toLinearMap)
        hInj
  -- The tangent spaces of the source and ambient Euclidean manifolds have dimensions `m` and `n`.
  simpa [tangentSpace_finrank_eq_of_n_dimensional_manifold x,
    tangentSpace_finrank_eq_of_n_dimensional_manifold
      (p := ((x : M) : EuclideanSpace ℝ (Fin n)))] using hle

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper for Proposition 6.25: the ambient base-point map of the normal bundle already lands in
the embedded submanifold `M`. -/
lemma piNM_baseAmbient_mem (p : NM[n, m; M]) :
    ((π_NM[n, m; M] p : M) : EuclideanSpace ℝ (Fin n)) ∈ M := by
  -- Forgetting the subtype proof of `π_NM p` still lands in the underlying set `M`.
  exact (π_NM[n, m; M] p).property

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper for Proposition 6.25: codomain-restricting the ambient base-point map back to `M`
recovers the normal-bundle projection `π_NM`. -/
lemma piNM_codRestrict_baseAmbient :
    Set.codRestrict
      (fun p : NM[n, m; M] ↦ ((π_NM[n, m; M] p : M) : EuclideanSpace ℝ (Fin n)))
      M
      piNM_baseAmbient_mem
      =
      (π_NM[n, m; M] : NM[n, m; M] → M) := by
  -- Both functions are definitionally the same subtype-valued map.
  funext p
  rfl

/-- Helper for Proposition 6.25: lowering the differentiability order preserves immersions while
keeping the same local chart normal forms. -/
lemma isImmersion_of_le
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) N]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
    {J : ModelWithCorners 𝕜 E' H'} [IsManifold J (⊤ : WithTop ℕ∞) P]
    {n m : WithTop ℕ∞} {f : N → P} (hmn : m ≤ n)
    (hf : IsImmersion I J n f) :
    IsImmersion I J m f := by
  -- Reuse the same complement and the same local chart presentation at the lower smoothness level.
  let hComp := hf.complement
  let hCompImm := hf.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I) (M := N) hmn) hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := J) (M := P) hmn) hx.codChart_mem_maximalAtlas

/-- Helper for Proposition 6.25: a chart in the maximal atlas of `ℝ^n` is smooth on its source. -/
lemma contMDiffOn_chartOfMemMaximalAtlas
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞)
      (EuclideanSpace ℝ (Fin n))) :
    ContMDiffOn (𝓡 n) (𝓡 n) (⊤ : WithTop ℕ∞) e e.source := by
  -- Compare `e` against the identity chart on the Euclidean model and use that the chart
  -- expression on `e.source` is literally the identity.
  refine
    (contMDiffOn_iff_of_mem_maximalAtlas'
      (I := 𝓡 n) (I' := 𝓡 n) (e := e) (e' := OpenPartialHomeomorph.refl _)
      he
      (by
        simpa using
          (StructureGroupoid.id_mem_maximalAtlas
            (G := contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)) :
            OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)) ∈
              StructureGroupoid.maximalAtlas
                (EuclideanSpace ℝ (Fin n))
                (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n))))
      (by intro x hx; exact hx)
      (by intro x hx; simpa using e.map_source hx)).2 ?_
  -- On the image of the source, the coordinate expression is the identity map.
  refine
    (contDiffOn_id :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin n) ↦ x) ((e.extend (𝓡 n)) '' e.source)).congr ?_
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  simp [Function.comp, e.left_inv hx]

/-- Helper for Proposition 6.25: the inverse branch of a maximal-atlas chart on `ℝ^n` is smooth
on the target patch. -/
lemma contMDiffOn_symm_chartOfMemMaximalAtlas
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞)
      (EuclideanSpace ℝ (Fin n))) :
    ContMDiffOn (𝓡 n) (𝓡 n) (⊤ : WithTop ℕ∞) e.symm e.target := by
  -- Symmetrically, compare `e.symm` against the identity chart on the Euclidean model.
  refine
    (contMDiffOn_iff_of_mem_maximalAtlas'
      (I := 𝓡 n) (I' := 𝓡 n) (e := OpenPartialHomeomorph.refl _) (e' := e)
      (by
        simpa using
          (StructureGroupoid.id_mem_maximalAtlas
            (G := contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n)) :
            OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)) ∈
              StructureGroupoid.maximalAtlas
                (EuclideanSpace ℝ (Fin n))
                (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 n))))
      he
      (by intro x hx; simp)
      (by intro x hx; simpa using e.symm.map_source hx)).2 ?_
  -- On the target patch, the chart followed by its inverse is the identity map.
  refine
    (contDiffOn_id :
      ContDiffOn ℝ (⊤ : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin n) ↦ x)
        ((OpenPartialHomeomorph.refl _).extend (𝓡 n) '' e.target)).congr ?_
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  simp [Function.comp, e.right_inv hx]

/-- Helper for Proposition 6.25: a maximal-atlas chart of `ℝ^n` is differentiable on its source,
and its inverse branch is differentiable on the target. -/
lemma maximalAtlasChart_mdifferentiable
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞)
      (EuclideanSpace ℝ (Fin n))) :
    e.MDifferentiable (𝓡 n) (𝓡 n) := by
  constructor
  · intro x hx
    -- Upgrade the source-local smoothness of the chart to differentiability.
    exact
      (contMDiffOn_chartOfMemMaximalAtlas (n := n) he x hx).mdifferentiableWithinAt
        (by simp)
  · intro y hy
    -- Do the same for the inverse branch on the target patch.
    exact
      (contMDiffOn_symm_chartOfMemMaximalAtlas (n := n) he y hy).mdifferentiableWithinAt
        (by simp)

/-- Helper for Proposition 6.25: the derivative of a maximal-atlas chart of `ℝ^n` is surjective
at every point of its source. -/
lemma maximalAtlasChart_mfderiv_surjective
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞)
      (EuclideanSpace ℝ (Fin n))) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    Function.Surjective (mfderiv (𝓡 n) (𝓡 n) e x) := by
  -- Maximal-atlas charts are differentiable local diffeomorphisms, so their derivatives are
  -- automatically bijective on the source.
  exact (maximalAtlasChart_mdifferentiable (n := n) he).mfderiv_surjective hx

/-- Helper for Proposition 6.25: a chart in the `C^∞` maximal atlas of `ℝ^n` is smooth on its
source. -/
lemma contMDiffOn_chartOfMemMaximalAtlasInfty
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞
      (EuclideanSpace ℝ (Fin n))) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := by
  -- Compare `e` with the identity chart in the same `C^∞` groupoid.
  refine
    (contMDiffOn_iff_of_mem_maximalAtlas'
      (I := 𝓡 n) (I' := 𝓡 n) (e := e) (e' := OpenPartialHomeomorph.refl _)
      he
      (by
        simpa using
          (StructureGroupoid.id_mem_maximalAtlas
            (G := contDiffGroupoid (∞ : ℕ∞ω) (𝓡 n)) :
            OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)) ∈
              StructureGroupoid.maximalAtlas
                (EuclideanSpace ℝ (Fin n))
                (contDiffGroupoid (∞ : ℕ∞ω) (𝓡 n))))
      (by intro x hx; exact hx)
      (by intro x hx; simpa using e.map_source hx)).2 ?_
  -- In Euclidean coordinates the chart expression is literally the identity.
  refine
    (contDiffOn_id :
      ContDiffOn ℝ (∞ : ℕ∞ω)
        (fun x : EuclideanSpace ℝ (Fin n) ↦ x) ((e.extend (𝓡 n)) '' e.source)).congr ?_
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  simp [Function.comp, e.left_inv hx]

/-- Helper for Proposition 6.25: the inverse branch of a `C^∞` maximal-atlas chart on `ℝ^n` is
smooth on its target. -/
lemma contMDiffOn_symm_chartOfMemMaximalAtlasInfty
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞
      (EuclideanSpace ℝ (Fin n))) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := by
  -- Compare the inverse branch with the identity chart in the same `C^∞` atlas.
  refine
    (contMDiffOn_iff_of_mem_maximalAtlas'
      (I := 𝓡 n) (I' := 𝓡 n) (e := OpenPartialHomeomorph.refl _) (e' := e)
      (by
        simpa using
          (StructureGroupoid.id_mem_maximalAtlas
            (G := contDiffGroupoid (∞ : ℕ∞ω) (𝓡 n)) :
            OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)) ∈
              StructureGroupoid.maximalAtlas
                (EuclideanSpace ℝ (Fin n))
                (contDiffGroupoid (∞ : ℕ∞ω) (𝓡 n))))
      he
      (by intro x hx; simp)
      (by intro x hx; simpa using e.symm.map_source hx)).2 ?_
  -- In Euclidean coordinates the inverse chart expression is also the identity.
  refine
    (contDiffOn_id :
      ContDiffOn ℝ (∞ : ℕ∞ω)
        (fun x : EuclideanSpace ℝ (Fin n) ↦ x)
        ((OpenPartialHomeomorph.refl _).extend (𝓡 n) '' e.target)).congr ?_
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  simp [Function.comp, e.right_inv hx]

/-- Helper for Proposition 6.25: a `C^∞` maximal-atlas chart of `ℝ^n` is differentiable on its
source and so is its inverse branch on the target. -/
lemma maximalAtlasChart_mdifferentiableInfty
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞
      (EuclideanSpace ℝ (Fin n))) :
    e.MDifferentiable (𝓡 n) (𝓡 n) := by
  constructor
  · intro x hx
    -- Upgrade source-local smoothness of the chart to differentiability.
    exact
      (contMDiffOn_chartOfMemMaximalAtlasInfty (n := n) he x hx).mdifferentiableWithinAt
        (by simp)
  · intro y hy
    -- Apply the same argument to the inverse chart branch on the target.
    exact
      (contMDiffOn_symm_chartOfMemMaximalAtlasInfty (n := n) he y hy).mdifferentiableWithinAt
        (by simp)

/-- Helper for Proposition 6.25: the derivative of a `C^∞` maximal-atlas chart of `ℝ^n` is
surjective at each source point. -/
lemma maximalAtlasChart_mfderiv_surjectiveInfty
    {e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞
      (EuclideanSpace ℝ (Fin n))) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    Function.Surjective (mfderiv (𝓡 n) (𝓡 n) e x) := by
  -- A `C^∞` maximal-atlas chart is a differentiable local diffeomorphism on its source.
  exact (maximalAtlasChart_mdifferentiableInfty (n := n) he).mfderiv_surjective hx

/-- Helper for Proposition 6.25: projection to the tail coordinates of the Euclidean slice model
`ℝ^n = ℝ^m × ℝ^(n-m)`. -/
def sliceTailProjection (hmn : m ≤ n) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - m)) :=
  fun x ↦ WithLp.toLp 2 fun i : Fin (n - m) ↦ x (euclidean_slice_tail_coordinate hmn i)

/-- Helper for Proposition 6.25: reinserting a tail vector with zero head coordinates gives a
right inverse to `sliceTailProjection`. -/
def sliceZeroPrefixInclusion (hmn : m ≤ n) :
    EuclideanSpace ℝ (Fin (n - m)) → EuclideanSpace ℝ (Fin n) :=
  fun y ↦
    WithLp.toLp 2 <|
      (Fin.append (fun _ : Fin m ↦ (0 : ℝ)) y) ∘ Fin.cast (Nat.add_sub_of_le hmn).symm

/-- Helper for Proposition 6.25: the zero-prefix inclusion is a right inverse to the tail
projection. -/
lemma sliceTailProjection_zeroPrefixInclusion
    (hmn : m ≤ n) (y : EuclideanSpace ℝ (Fin (n - m))) :
    sliceTailProjection (n := n) (m := m) hmn
        (sliceZeroPrefixInclusion (n := n) (m := m) hmn y) = y := by
  -- Rewrite the transported tail index back to `Fin.natAdd`, then `Fin.append_right` applies.
  ext i
  change
    (Fin.append (fun _ : Fin m ↦ (0 : ℝ)) y)
        (Fin.cast (Nat.add_sub_of_le hmn).symm
          (Fin.cast (Nat.add_sub_of_le hmn) (i.natAdd m))) = y i
  rw [(Fin.leftInverse_cast (Nat.add_sub_of_le hmn)) (i.natAdd m)]
  simp

/-- Helper for Proposition 6.25: the Euclidean tail projection is a smooth submersion. -/
lemma sliceTailProjection_isSmoothSubmersion (hmn : m ≤ n) :
    IsSmoothSubmersion (𝓡 n) (𝓡 (n - m))
      (sliceTailProjection (n := n) (m := m) hmn) := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - m)) :=
    { toFun := sliceTailProjection (n := n) (m := m) hmn
      map_add' := by
        intro x y
        ext i
        simp [sliceTailProjection]
      map_smul' := by
        intro c x
        ext i
        simp [sliceTailProjection]
      cont := by
        have hcoord :
            Continuous fun x : EuclideanSpace ℝ (Fin n) =>
              fun i : Fin (n - m) ↦ x (euclidean_slice_tail_coordinate hmn i) :=
          continuous_pi fun i ↦
            PiLp.continuous_apply (p := 2) (β := fun _ : Fin n ↦ ℝ)
              (euclidean_slice_tail_coordinate hmn i)
        simpa [sliceTailProjection] using
          (PiLp.continuous_toLp 2 (fun _ : Fin (n - m) ↦ ℝ)).comp hcoord }
  refine ⟨?_, ?_⟩
  · -- A continuous linear map between Euclidean spaces is smooth.
    simpa [L] using (L.contMDiff :
      ContMDiff (𝓡 n) (𝓡 (n - m)) ∞ L)
  · intro x
    -- The manifold derivative is the ordinary derivative of the fixed linear map.
    rw [mfderiv_eq_fderiv]
    have hderiv :
        fderiv ℝ (sliceTailProjection (n := n) (m := m) hmn) x = L := by
      simpa [L, sliceTailProjection] using (L.hasFDerivAt (x := x)).fderiv
    rw [hderiv]
    change Function.Surjective L
    intro y
    refine ⟨sliceZeroPrefixInclusion (n := n) (m := m) hmn y, ?_⟩
    simpa [L] using sliceTailProjection_zeroPrefixInclusion (n := n) (m := m) hmn y

/-- Helper for Proposition 6.25: on the zero-tail Euclidean slice inside an ambient ball,
projecting to the first `m` coordinates stays inside the corresponding source ball. -/
private theorem zeroTailProjection_memBall
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hmn : m ≤ n) {ε : ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hzBall : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)
    (hz : z ∈ Set.euclideanSlice U m hmn (fun _ : Fin (n - m) ↦ (0 : ℝ))) :
    euclidean_slice_projection hmn z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε := by
  rw [Metric.mem_ball, dist_eq_norm] at hzBall ⊢
  have hnorm_sq :
      ‖euclidean_slice_projection hmn z‖ ^ 2 = ‖z‖ ^ 2 := by
    have hslice :
        euclidean_slice_inclusion hmn (fun _ : Fin (n - m) ↦ (0 : ℝ))
            (euclidean_slice_projection hmn z) = z :=
      euclidean_slice_inclusion_projection hmn (fun _ : Fin (n - m) ↦ (0 : ℝ)) hz
    let zProj := euclidean_slice_projection hmn z
    let a : Fin n → ℝ := fun i ↦
      (euclidean_slice_inclusion hmn (fun _ : Fin (n - m) ↦ (0 : ℝ)) zProj).ofLp i ^ 2
    let f : Fin (m + (n - m)) → ℝ := fun i ↦ a ((finCongr (Nat.add_sub_of_le hmn)) i)
    have hinclude_sq :
        ‖euclidean_slice_inclusion hmn (fun _ : Fin (n - m) ↦ (0 : ℝ))
            zProj‖ ^ 2 =
          ‖zProj‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      calc
        ∑ i : Fin n, a i
            = ∑ i : Fin (m + (n - m)), f i := by
              simpa [a, f] using
                (Equiv.sum_comp (finCongr (Nat.add_sub_of_le hmn)) (g := a)).symm
        _ =
              (∑ i : Fin m,
                (euclidean_slice_inclusion hmn (fun _ : Fin (n - m) ↦ (0 : ℝ)) zProj).ofLp
                  (Fin.castLE hmn i) ^ 2) +
                ∑ i : Fin (n - m),
                  (euclidean_slice_inclusion hmn (fun _ : Fin (n - m) ↦ (0 : ℝ)) zProj).ofLp
                    (euclidean_slice_tail_coordinate hmn i) ^ 2 := by
              simpa [a, f, cast_first_coordinates, euclidean_slice_tail_coordinate] using
                (Fin.sum_univ_add (f := f))
        _ =
              (∑ i : Fin m, zProj.ofLp i ^ 2) +
                ∑ i : Fin (n - m), (0 : ℝ) ^ 2 := by
              congr 1
              · refine Finset.sum_congr rfl ?_
                intro i hi
                simp [zProj, euclidean_slice_inclusion_first]
              · refine Finset.sum_congr rfl ?_
                intro i hi
                simp [euclidean_slice_inclusion_tail]
        _ = ∑ i : Fin m, zProj.ofLp i ^ 2 := by simp
    calc
      ‖euclidean_slice_projection hmn z‖ ^ 2 =
          ‖euclidean_slice_inclusion hmn (fun _ : Fin (n - m) ↦ (0 : ℝ)) zProj‖ ^ 2 := by
            simpa [zProj] using hinclude_sq.symm
      _ = ‖z‖ ^ 2 := by
            simp [zProj, hslice]
  have hnorm :
      ‖euclidean_slice_projection hmn z‖ = ‖z‖ := by
    nlinarith [hnorm_sq, norm_nonneg (euclidean_slice_projection hmn z), norm_nonneg z]
  simpa [hnorm] using hzBall

/-- Helper for Proposition 6.25: express the manifold derivative of an ambient Euclidean map in
fixed Euclidean source and target coordinates. -/
def fixedModelMfderiv {k : ℕ}
    (Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k)) (x : M) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  (NormedSpace.fromTangentSpace (Φ x)).toContinuousLinearMap ∘L
    mfderiv (𝓡 n) (𝓡 k) Φ (x : EuclideanSpace ℝ (Fin n)) ∘L
    ((NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap)

/-- Helper for Proposition 6.25: on the ambient Euclidean model, `fixedModelMfderiv` is the
ordinary Fréchet derivative written in the fixed coordinates used later in the file. -/
lemma fixedModelMfderiv_eq_fderivOnModel {k : ℕ}
    (Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k)) (x : M) :
    fixedModelMfderiv (n := n) (M := M) Φ x = fderiv ℝ Φ (x : EuclideanSpace ℝ (Fin n)) := by
  -- On Euclidean model spaces, the `fromTangentSpace` identifications are definitionally the
  -- identity, so `mfderiv_eq_fderiv` gives the whole normalization.
  rw [fixedModelMfderiv, mfderiv_eq_fderiv]
  rfl

/-- Helper for Proposition 6.25: a Euclidean vector orthogonal to the kernel of a linear map comes
from the range of the adjoint. -/
lemma exists_eq_adjoint_of_mem_orthogonalKer {k : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ A.kerᗮ) :
    ∃ c : EuclideanSpace ℝ (Fin k), LinearMap.adjoint A c = v := by
  -- In finite-dimensional inner-product spaces, the orthogonal complement of the kernel is the
  -- range of the adjoint.
  rw [LinearMap.orthogonal_ker] at hv
  rcases hv with ⟨c, rfl⟩
  exact ⟨c, rfl⟩

/-- Helper for Proposition 6.25: evaluating the adjoint of a continuous linear map at a fixed
vector is itself a continuous linear operation on the operator space. -/
noncomputable def adjointApplyContinuousLinearMap
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (a : F) : (E →L[ℝ] F) →L[ℝ] E :=
  (ContinuousLinearMap.apply ℝ E a).comp
    (ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Helper for Proposition 6.25: `adjointApplyContinuousLinearMap` evaluates the continuous-linear
adjoint at the chosen fixed vector. -/
lemma adjointApplyContinuousLinearMap_apply
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (a : F) (A : E →L[ℝ] F) :
    adjointApplyContinuousLinearMap a A = A.adjoint a :=
  rfl

/-- Helper for Proposition 6.25: at `C^∞`, codomain-restricting a smooth map along a smooth
embedding stays continuous because the subtype carries the induced topology. -/
private theorem smoothEmbedding_continuousCodRestrictInfty
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace 𝕜 EA]
    {HA : Type*} [TopologicalSpace HA]
    {A : Type*} [TopologicalSpace A] [ChartedSpace HA A]
    {I : ModelWithCorners 𝕜 EA HA} [IsManifold I ∞ A]
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type*} [TopologicalSpace HS]
    {S : Set A} [ChartedSpace HS S]
    {J : ModelWithCorners 𝕜 ES HS} [IsManifold J ∞ S]
    (hS : IsSmoothEmbedding J I ∞ (Subtype.val : S → A))
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
    {HN : Type*} [TopologicalSpace HN]
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {K : ModelWithCorners 𝕜 EN HN} [IsManifold K ∞ N]
    {F : N → A} (hF : ContMDiff K I ∞ F) (hFS : ∀ x, F x ∈ S) :
    Continuous (Set.codRestrict F S hFS) := by
  -- Continuity into the subtype is equivalent to continuity after composing with the inclusion.
  refine hS.isEmbedding.isInducing.continuous_iff.2 ?_
  simpa [Function.comp] using hF.continuous

/-- Helper for Proposition 6.25: in immersion charts for a smooth embedding, the codomain-
restricted chart expression is recovered by projecting the ambient chart expression. -/
private theorem smoothEmbedding_writtenInChartsCodRestrictEqOnInfty
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace 𝕜 EA]
    {HA : Type*} [TopologicalSpace HA]
    {A : Type*} [TopologicalSpace A] [ChartedSpace HA A]
    {I : ModelWithCorners 𝕜 EA HA}
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type*} [TopologicalSpace HS]
    {S : Set A} [ChartedSpace HS S]
    {J : ModelWithCorners 𝕜 ES HS}
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
    {HN : Type*} [TopologicalSpace HN]
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {F : N → A} (hFS : ∀ x, F x ∈ S) {y : S}
    (hImm : IsImmersionAt J I ∞ (Subtype.val : S → A) y) :
    Set.EqOn ((hImm.domChart.extend J) ∘ Set.codRestrict F S hFS)
      ((fun v ↦ (hImm.equiv.symm v).1) ∘ ((hImm.codChart.extend I) ∘ F))
      ((Set.codRestrict F S hFS) ⁻¹' hImm.domChart.source) := by
  -- Apply the immersion normal form to the codomain-restricted point and project to the subtype
  -- coordinates.
  intro z hz
  have hz_target :
      hImm.domChart.extend J (Set.codRestrict F S hFS z) ∈ (hImm.domChart.extend J).target :=
    (hImm.domChart.extend J).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using hz
  simpa [Function.comp, OpenPartialHomeomorph.extend_coe, hImm.domChart.left_inv hz] using
    (congrArg (fun v ↦ Prod.fst (hImm.equiv.symm v)) (hImm.writtenInCharts hz_target)).symm

/-- Helper for Proposition 6.25: a `C^∞` ambient map whose image lies in a smoothly embedded
subtype is `C^∞` as a map to that subtype at each point. -/
private theorem smoothEmbedding_contMDiffAtCodRestrictInfty
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace 𝕜 EA]
    {HA : Type*} [TopologicalSpace HA]
    {A : Type*} [TopologicalSpace A] [ChartedSpace HA A]
    {I : ModelWithCorners 𝕜 EA HA} [IsManifold I ∞ A]
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type*} [TopologicalSpace HS]
    {S : Set A} [ChartedSpace HS S]
    {J : ModelWithCorners 𝕜 ES HS} [IsManifold J ∞ S]
    (hS : IsSmoothEmbedding J I ∞ (Subtype.val : S → A))
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
    {HN : Type*} [TopologicalSpace HN]
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {K : ModelWithCorners 𝕜 EN HN} [IsManifold K ∞ N]
    {F : N → A} (hF : ContMDiff K I ∞ F) (hFS : ∀ x, F x ∈ S) (x : N) :
    ContMDiffAt K J ∞ (Set.codRestrict F S hFS) x := by
  let fS : N → S := Set.codRestrict F S hFS
  let y : S := fS x
  let hImm : IsImmersionAt J I ∞ (Subtype.val : S → A) y := hS.isImmersion.isImmersionAt y
  let e : OpenPartialHomeomorph N HN := chartAt HN x
  let x' : EN := e.extend K x
  have hcont : ContinuousAt fS x :=
    (smoothEmbedding_continuousCodRestrictInfty hS hF hFS).continuousAt
  have hx : x ∈ e.source := mem_chart_source HN x
  have hy : fS x ∈ hImm.domChart.source := hImm.mem_domChart_source
  have hy' : F x ∈ hImm.codChart.source := hImm.mem_codChart_source
  have hchartSubtype :
      ContMDiffWithinAt K J ∞ fS Set.univ x ↔
        ContinuousWithinAt fS Set.univ x ∧
          ContDiffWithinAt 𝕜 ∞
            ((hImm.domChart.extend J) ∘ fS ∘ (e.extend K).symm) (Set.range K) x' := by
    simpa [fS, e, x', Set.preimage_univ, Set.univ_inter] using
      (@contMDiffWithinAt_iff_of_mem_maximalAtlas
        𝕜 _ EN _ _ HN _ K N _ _ ES _ _ HS _ J S _ _ e hImm.domChart fS Set.univ ∞ _ _ x)
        (IsManifold.chart_mem_maximalAtlas x) hImm.domChart_mem_maximalAtlas hx hy
  -- Move the pointwise goal to the chart pair given by the immersion normal form.
  rw [ContMDiffAt, hchartSubtype, continuousWithinAt_univ]
  refine ⟨hcont, ?_⟩
  have hchartAmbient :
      ContMDiffWithinAt K I ∞ F Set.univ x ↔
        ContinuousWithinAt F Set.univ x ∧
          ContDiffWithinAt 𝕜 ∞
            ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) (Set.range K) x' := by
    simpa [e, x', Set.preimage_univ, Set.univ_inter] using
      (@contMDiffWithinAt_iff_of_mem_maximalAtlas
        𝕜 _ EN _ _ HN _ K N _ _ EA _ _ HA _ I A _ _ e hImm.codChart F Set.univ ∞ _ _ x)
        (IsManifold.chart_mem_maximalAtlas x) hImm.codChart_mem_maximalAtlas hx hy'
  have hambient :
      ContDiffWithinAt 𝕜 ∞ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) (Set.range K) x' := by
    -- Rewrite ambient smoothness in the chart pair `(e, hImm.codChart)`.
    exact (hchartAmbient.1 hF.contMDiffAt.contMDiffWithinAt).2
  let eSymm := hImm.equiv.symm
  have hsymm : ContDiff 𝕜 ∞ eSymm := by
    simpa [eSymm] using eSymm.contDiff
  have hproj :
      ContDiff 𝕜 ∞ (fun v ↦ (eSymm v).1) := by
    simpa [eSymm] using contDiff_fst.comp hsymm
  have hprojWithin :
      ContDiffWithinAt 𝕜 ∞ (fun v ↦ (eSymm v).1) Set.univ
        (((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) x') :=
    hproj.contDiffWithinAt
  have hcomp :
      ContDiffWithinAt 𝕜 ∞
        ((fun v ↦ (eSymm v).1) ∘ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm))
        (Set.range K) x' := by
    -- Postcompose the ambient chart expression with the smooth projection onto the subtype
    -- coordinates coming from the immersion normal form.
    exact hprojWithin.comp x' hambient (by intro z hz; simp)
  have hsource_mem : fS ⁻¹' hImm.domChart.source ∈ nhds x := by
    -- Pull back the immersion-chart neighborhood through the codomain-restricted map.
    exact hcont.preimage_mem_nhds (hImm.domChart.open_source.mem_nhds hy)
  have hset_mem :
      (e.extend K).symm ⁻¹' (fS ⁻¹' hImm.domChart.source) ∈ nhdsWithin x' (Set.range K) := by
    -- Transport that neighborhood through the source chart.
    simpa [e, x', nhdsWithin_univ] using
      e.extend_preimage_mem_nhdsWithin (I := K) (s := Set.univ) (t := fS ⁻¹' hImm.domChart.source)
        hx (by simpa [nhdsWithin_univ] using hsource_mem)
  have heq :
      ((hImm.domChart.extend J) ∘ fS ∘ (e.extend K).symm)
        =ᶠ[nhdsWithin x' (Set.range K)]
          ((fun v ↦ (eSymm v).1) ∘
            ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm)) := by
    -- On that chart neighborhood the restricted and projected ambient expressions agree.
    refine Filter.eventuallyEq_of_mem hset_mem ?_
    intro z hz
    have hchartEq :
        Set.EqOn ((hImm.domChart.extend J) ∘ Set.codRestrict F S hFS)
          ((fun v ↦ (eSymm v).1) ∘ ((hImm.codChart.extend I) ∘ F))
          ((Set.codRestrict F S hFS) ⁻¹' hImm.domChart.source) :=
      smoothEmbedding_writtenInChartsCodRestrictEqOnInfty
        (EA := EA) (HA := HA) (A := A) (I := I)
        (ES := ES) (HS := HS) (S := S) (J := J)
        (EN := EN) (HN := HN) (N := N) (F := F) (hFS := hFS) (hImm := hImm)
    simpa [Function.comp, eSymm] using hchartEq hz
  have hx'_target : x' ∈ (e.extend K).target := (e.extend K).map_source <| by
    simpa [OpenPartialHomeomorph.extend_source] using hx
  have hx'_range : x' ∈ Set.range K :=
    e.extend_target_subset_range hx'_target
  exact hcomp.congr_of_eventuallyEq_of_mem heq hx'_range

/-- Helper for Proposition 6.25: a `C^∞` ambient map whose image lies in a smoothly embedded
subtype is `C^∞` as a map to that subtype. -/
private theorem smoothEmbedding_contMDiffCodRestrictInfty
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace 𝕜 EA]
    {HA : Type*} [TopologicalSpace HA]
    {A : Type*} [TopologicalSpace A] [ChartedSpace HA A]
    {I : ModelWithCorners 𝕜 EA HA} [IsManifold I ∞ A]
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type*} [TopologicalSpace HS]
    {S : Set A} [ChartedSpace HS S]
    {J : ModelWithCorners 𝕜 ES HS} [IsManifold J ∞ S]
    (hS : IsSmoothEmbedding J I ∞ (Subtype.val : S → A))
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
    {HN : Type*} [TopologicalSpace HN]
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    {K : ModelWithCorners 𝕜 EN HN} [IsManifold K ∞ N]
    {F : N → A} (hF : ContMDiff K I ∞ F) (hFS : ∀ x, F x ∈ S) :
    ContMDiff K J ∞ (Set.codRestrict F S hFS) := by
  -- Verify the codomain-restricted map pointwise with the chart-level subtype bridge.
  intro x
  exact smoothEmbedding_contMDiffAtCodRestrictInfty hS hF hFS x

/-- Helper: the canonical projection `π_NM[n, m; M]` from the normal bundle to its base manifold
is smooth. -/
lemma piNM_contMDiff [CompatibleSmoothStructure n m M] :
    ContMDiff (𝓡 n) (𝓡 m) ∞ (π_NM[n, m; M] : NM[n, m; M] → M) := by
  have hSubtypeEmbedding :
      IsSmoothEmbedding
        (𝓡 m)
        (𝓡 n)
        ∞
        (Subtype.val : M → EuclideanSpace ℝ (Fin n)) := by
    -- Lower the embedded-submanifold owner theorem from `ω` to the `C^∞` regularity used here.
    exact isSmoothEmbedding_of_le (by simp) IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val
  -- Restrict the already smooth ambient base-point map back to the embedded manifold `M`.
  simpa [piNM_codRestrict_baseAmbient] using
    (smoothEmbedding_contMDiffCodRestrictInfty
      (I := 𝓡 n) (J := 𝓡 m) hSubtypeEmbedding
      piNM_baseAmbient_contMDiff piNM_baseAmbient_mem)

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper for Proposition 6.25: a chosen bundle trivialization through `p` already supplies the
point-set local right-inverse data for the bundle projection near `p.proj`. -/
lemma localSectionThrough_data_of_trivialization
    {F : Type*} {E : M → Type*}
    [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)]
    [∀ x : M, TopologicalSpace (E x)]
    [∀ x : M, Zero (E x)]
    (e :
      Bundle.Trivialization
        F
        (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → M))
    {p : Bundle.TotalSpace F E} (hp : p.proj ∈ e.baseSet) :
    ∃ U : TopologicalSpace.Opens M, ∃ hpU : p.proj ∈ U, ∃ σ : U → Bundle.TotalSpace F E,
      (∀ x : U, Bundle.TotalSpace.proj (σ x) = x) ∧ σ ⟨p.proj, hpU⟩ = p := by
  let U : TopologicalSpace.Opens M := ⟨e.baseSet, e.open_baseSet⟩
  let v0 : F := (e p).2
  let σ : U → Bundle.TotalSpace F E := fun x ↦
    Bundle.TotalSpace.mk' F x (e.symm x v0)
  refine ⟨U, hp, σ, ?_, ?_⟩
  · intro x
    -- The constructed section is a total-space point over `x` by definition.
    rfl
  · -- At the original base point, the frozen-coordinate section recovers the chosen point `p`.
    rcases p with ⟨b, y⟩
    simpa [σ, U, v0] using e.symm_apply_apply_mk hp y

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
  [IsManifold (𝓡 n) ∞ (NM[n, m; M])] in
/-- Helper for Proposition 6.25: the canonical trivialization through `p.proj` packages the same
point-set local-section data for the projection of any fiber bundle. -/
lemma bundleProjection_localSectionThrough_data
    {F : Type*} {E : M → Type*}
    [TopologicalSpace F]
    [TopologicalSpace (Bundle.TotalSpace F E)]
    [∀ x : M, TopologicalSpace (E x)]
    [∀ x : M, Zero (E x)]
    [FiberBundle F E]
    (p : Bundle.TotalSpace F E) :
    ∃ U : TopologicalSpace.Opens M, ∃ hpU : p.proj ∈ U, ∃ σ : U → Bundle.TotalSpace F E,
      (∀ x : U, Bundle.TotalSpace.proj (σ x) = x) ∧ σ ⟨p.proj, hpU⟩ = p := by
  let e := trivializationAt F E p.proj
  have hp : p.proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.proj
  -- The canonical trivialization at `p.proj` is enough for the point-set section data.
  exact localSectionThrough_data_of_trivialization (e := e) hp

/-- Helper for Proposition 6.25: once a normal-bundle trivialization identifies its frozen fiber
coordinate with `normal_bundle_vector`, the resulting local section has smooth ambient product
coordinates. -/
lemma normalBundleToProd_comp_localSectionThrough_of_trivialization_contMDiff
    (e :
      Bundle.Trivialization
        (EuclideanSpace ℝ (Fin n))
        (Bundle.TotalSpace.proj : NM[n, m; M] → M))
    {p : NM[n, m; M]} (hp : π_NM[n, m; M] p ∈ e.baseSet)
    (hcoord :
      ∀ x ∈ e.baseSet, ∀ v : EuclideanSpace ℝ (Fin n),
        normal_bundle_vector n m M
            (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x (e.symm x v)) = v) :
    ∃ U : TopologicalSpace.Opens M, ∃ hpU : π_NM[n, m; M] p ∈ U, ∃ σ : U → NM[n, m; M],
      ContMDiff (𝓡 m) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M ∘ σ) ∧
        (∀ x : U, π_NM[n, m; M] (σ x) = x) ∧
        σ ⟨π_NM[n, m; M] p, hpU⟩ = p := by
  let U : TopologicalSpace.Opens M := ⟨e.baseSet, e.open_baseSet⟩
  let v0 : EuclideanSpace ℝ (Fin n) := (e p).2
  let σ : U → NM[n, m; M] := fun x ↦
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x (e.symm x v0)
  have hbase :
      ContMDiff (𝓡 m) (𝓡 n) ∞
        (fun x : U ↦ ((x : M) : EuclideanSpace ℝ (Fin n))) := by
    -- The first product coordinate is just the ambient inclusion of the open subset `U ⊆ M`.
    simpa [Function.comp] using
      subtype_val_contMDiff.comp
        (contMDiff_subtype_val : ContMDiff (𝓡 m) (𝓡 m) ∞ (Subtype.val : U → M))
  have hσ :
      normal_bundle_toProd n m M ∘ σ =
        fun x : U ↦ (((x : M) : EuclideanSpace ℝ (Fin n)), v0) := by
    -- The chosen trivialization freezes the second coordinate at `v0`, so the product coordinates
    -- of the section are `(x, v0)`.
    funext x
    change
      (((x : M) : EuclideanSpace ℝ (Fin n)),
        normal_bundle_vector n m M
          (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x (e.symm x v0))) =
        (((x : M) : EuclideanSpace ℝ (Fin n)), v0)
    rw [hcoord x x.property v0]
  have hsmooth :
      ContMDiff (𝓡 m) ((𝓡 n).prod (𝓡 n)) ∞
        (fun x : U ↦ (((x : M) : EuclideanSpace ℝ (Fin n)), v0)) := by
    -- Smoothness splits into the ambient inclusion in the first factor and the constant second
    -- factor.
    exact hbase.prodMk (contMDiff_const : ContMDiff (𝓡 m) (𝓡 n) ∞ (fun _ : U ↦ v0))
  refine ⟨U, hp, σ, ?_, ?_, ?_⟩
  · -- Rewrite to the explicit pair form and reuse the product smoothness calculation.
    rw [hσ]
    exact hsmooth
  · intro x
    -- The frozen-coordinate section is a genuine right inverse to the bundle projection.
    rfl
  · -- At the chosen base point, the frozen-coordinate section recovers the original point `p`.
    rcases p with ⟨b, y⟩
    simpa [σ, U, v0] using e.symm_apply_apply_mk hp y

/-- Helper for Proposition 6.25: a smooth ambient normal vector field on an open set of `M`
packages to a local section of `π_NM[n, m; M]` with the same ambient product coordinates. -/
lemma localSectionThrough_of_ambientNormalField
    (p : NM[n, m; M])
    {U : TopologicalSpace.Opens M}
    {hpU : π_NM[n, m; M] p ∈ U}
    {η : U → EuclideanSpace ℝ (Fin n)}
    (hηsmooth : ContMDiff (𝓡 m) (𝓡 n) ∞ η)
    (hηnormal :
      ∀ x : U,
        (((NormedSpace.fromTangentSpace
            ((x : M) : EuclideanSpace ℝ (Fin n))).symm (η x)) :
          TangentSpace (𝓡 n) (((x : M) : EuclideanSpace ℝ (Fin n)))) ∈
            N[n, m; M; (x : M)])
    (hηp : η ⟨π_NM[n, m; M] p, hpU⟩ = normal_bundle_vector n m M p) :
    ∃ σ : U → NM[n, m; M],
      ContMDiff (𝓡 m) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M ∘ σ) ∧
        (∀ x : U, π_NM[n, m; M] (σ x) = x) ∧
        σ ⟨π_NM[n, m; M] p, hpU⟩ = p := by
  let σ : U → NM[n, m; M] := fun x ↦
    Bundle.TotalSpace.mk x.1
      ⟨(NormedSpace.fromTangentSpace ((x : M) : EuclideanSpace ℝ (Fin n))).symm (η x),
        hηnormal x⟩
  have hσcoords :
      normal_bundle_toProd n m M ∘ σ =
        fun x : U ↦ (((x : M) : EuclideanSpace ℝ (Fin n)), η x) := by
    -- The packaged section keeps the base point and records the chosen ambient normal vector.
    funext x
    ext <;> simp [σ, normal_bundle_toProd, normal_bundle_vector]
  have hbase :
      ContMDiff (𝓡 m) (𝓡 n) ∞
        (fun x : U ↦ ((x : M) : EuclideanSpace ℝ (Fin n))) := by
    -- The first product coordinate is the ambient inclusion of the open subset `U ⊆ M`.
    simpa [Function.comp] using
      subtype_val_contMDiff.comp
        (contMDiff_subtype_val : ContMDiff (𝓡 m) (𝓡 m) ∞ (Subtype.val : U → M))
  have hsmooth :
      ContMDiff (𝓡 m) ((𝓡 n).prod (𝓡 n)) ∞
        (fun x : U ↦ (((x : M) : EuclideanSpace ℝ (Fin n)), η x)) := by
    -- Smoothness is the product of the ambient inclusion and the chosen ambient normal field.
    exact hbase.prodMk hηsmooth
  refine ⟨σ, ?_, ?_, ?_⟩
  · -- Rewrite to the explicit product coordinates and use the smooth pair map.
    rw [hσcoords]
    exact hsmooth
  · intro x
    -- By construction, the packaged point lies over the original base point `x`.
    rfl
  · rcases p with ⟨b, v⟩
    have hv :
        ⟨(NormedSpace.fromTangentSpace (b : EuclideanSpace ℝ (Fin n))).symm (η ⟨b, hpU⟩),
          hηnormal ⟨b, hpU⟩⟩ = v := by
      -- The fiber coordinate is recovered by inverting the ambient Euclidean identification.
      apply Subtype.ext
      change (NormedSpace.fromTangentSpace (b : EuclideanSpace ℝ (Fin n))).symm (η ⟨b, hpU⟩) = v.1
      apply (NormedSpace.fromTangentSpace (b : EuclideanSpace ℝ (Fin n))).injective
      simpa [normal_bundle_vector] using hηp
    -- At the chosen base point, the packaged section returns the original normal-bundle point.
    exact congrArg (Bundle.TotalSpace.mk b) hv

/-- Helper for Proposition 6.25: restricting a local defining map to its open source gives an
ordinary smooth map on the corresponding open subtype. -/
lemma localDefiningMap_contMDiffOnOpenSource
    {k : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k)}
    (hDef : IsLocalDefiningMapOn (𝓡 n) (𝓡 k) M U Φ) :
    let Uo : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨U, hDef.isOpen_source⟩
    ContMDiff (𝓡 n) (𝓡 k) ∞ (fun u : Uo ↦ Φ u.1) := by
  let Uo : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨U, hDef.isOpen_source⟩
  change ContMDiff (𝓡 n) (𝓡 k) ∞ (fun u : Uo ↦ Φ u.1)
  intro x
  -- Open-source smoothness upgrades from `ContMDiffOn` to an ordinary smooth map on the subtype.
  have hxWithin : ContMDiffWithinAt (𝓡 n) (𝓡 k) ∞ Φ U x.1 :=
    hDef.smoothOn x.1 x.2
  have hxAt : ContMDiffAt (𝓡 n) (𝓡 k) ∞ Φ x.1 :=
    hxWithin.contMDiffAt (Uo.2.mem_nhds x.2)
  exact contMDiffAt_subtype_iff.2 hxAt

/-- Helper for Proposition 6.25: on a Euclidean slice, the fixed-tail equations are exactly the
single vector equation cut out by `sliceTailProjection`. -/
lemma mem_euclideanSlice_iff_sliceTailProjection_eq
    (hmn : m ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {c : Fin (n - m) → ℝ}
    {y : EuclideanSpace ℝ (Fin n)}
    (hyU : y ∈ U) :
    y ∈ Set.euclideanSlice U m hmn c ↔
      sliceTailProjection (n := n) (m := m) hmn y = WithLp.toLp 2 c := by
  constructor
  · intro hy
    -- The Euclidean-slice membership data is already the coordinatewise tail-equality statement.
    ext i
    exact hy.2 i
  · intro hy
    -- Conversely, the vector equality recovers the tail-coordinate equations one coordinate at a time.
    refine ⟨hyU, ?_⟩
    intro i
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (n - m)) ↦ z i) hy
    simpa [sliceTailProjection] using hi

/-- Helper for Proposition 6.25: on the chosen slice chart around `x₀`, membership in `M` is
equivalent to the fixed tail-coordinate equation for the slice-tail composite. -/
lemma sliceTailComposite_mem_iff_eq_constants
    (x0 : M)
    (hSlice : Set.SatisfiesLocalSliceCondition n M m)
    (hmn : m ≤ n) :
    let e := slice_condition_ambient_chart (S := M) hSlice x0
    let cVec := WithLp.toLp 2 (slice_condition_tail_constants (S := M) hSlice x0 hmn)
    let Φ := sliceTailProjection (n := n) (m := m) hmn ∘ e
    ∀ q : EuclideanSpace ℝ (Fin n), q ∈ e.source → (q ∈ M ↔ Φ q = cVec) := by
  classical
  let e := slice_condition_ambient_chart (S := M) hSlice x0
  let cVec := WithLp.toLp 2 (slice_condition_tail_constants (S := M) hSlice x0 hmn)
  let Φ := sliceTailProjection (n := n) (m := m) hmn ∘ e
  change ∀ q : EuclideanSpace ℝ (Fin n), q ∈ e.source → (q ∈ M ↔ Φ q = cVec)
  intro q hqSource
  refine ⟨?_, ?_⟩
  · intro hqM
    -- Points of `M` in the chart source map into the distinguished Euclidean slice.
    have hSliceEq :
        e '' (M ∩ e.source) =
          Set.euclideanSlice e.target m hmn
            (slice_condition_tail_constants (S := M) hSlice x0 hmn) := by
      simpa [e] using slice_condition_ambient_chart_image_eq_slice (S := M) hSlice x0 hmn
    have heqSlice : e q ∈ Set.euclideanSlice e.target m hmn
        (slice_condition_tail_constants (S := M) hSlice x0 hmn) := by
      rw [← hSliceEq]
      exact ⟨q, ⟨hqM, hqSource⟩, rfl⟩
    have heTarget : e q ∈ e.target := e.map_source hqSource
    exact (mem_euclideanSlice_iff_sliceTailProjection_eq (n := n) (m := m) hmn heTarget).1 heqSlice
  · intro hqEq
    -- If the tail coordinates agree with the fixed constants, invert the chart-image description.
    have heTarget : e q ∈ e.target := e.map_source hqSource
    have heqSlice : e q ∈ Set.euclideanSlice e.target m hmn
        (slice_condition_tail_constants (S := M) hSlice x0 hmn) := by
      exact (mem_euclideanSlice_iff_sliceTailProjection_eq (n := n) (m := m) hmn heTarget).2 hqEq
    have hSliceEq :
        e '' (M ∩ e.source) =
          Set.euclideanSlice e.target m hmn
            (slice_condition_tail_constants (S := M) hSlice x0 hmn) := by
      simpa [e] using slice_condition_ambient_chart_image_eq_slice (S := M) hSlice x0 hmn
    have heImage : e q ∈ e '' (M ∩ e.source) := by
      rw [hSliceEq]
      exact heqSlice
    rcases heImage with ⟨y, ⟨hyM, hySource⟩, hyEq⟩
    -- Injectivity of the chart on its source identifies the ambient point with that source witness.
    have hyq : y = q := by
      calc
        y = e.symm (e y) := (e.left_inv hySource).symm
        _ = e.symm (e q) := by rw [hyEq]
        _ = q := e.left_inv hqSource
    simpa [hyq] using hyM

/-- Helper for Proposition 6.25: the slice-tail composite is a local defining map on the chosen
ambient chart source. -/
lemma sliceTailComposite_mfderiv_surjective
    (x0 : M)
    (hSlice : Set.SatisfiesLocalSliceCondition n M m)
    (hmn : m ≤ n)
    (p : EuclideanSpace ℝ (Fin n))
    (hpSource :
      p ∈ (slice_condition_ambient_chart (S := M) hSlice x0).source) :
    Function.Surjective
      (mfderiv
        (𝓡 n)
        (𝓡 (n - m))
        (sliceTailProjection (n := n) (m := m) hmn ∘
          slice_condition_ambient_chart (S := M) hSlice x0)
        p) := by
  let e := slice_condition_ambient_chart (S := M) hSlice x0
  have hChartAt :
      MDifferentiableAt (𝓡 n) (𝓡 n) e p := by
    exact
      (maximalAtlasChart_mdifferentiable
        (n := n)
        (slice_condition_ambient_chart_mem_maximalAtlas (S := M) hSlice x0)).mdifferentiableAt
        hpSource
  have hProjAt :
      MDifferentiableAt (𝓡 n) (𝓡 (n - m))
        (sliceTailProjection (n := n) (m := m) hmn) (e p) := by
    exact ((sliceTailProjection_isSmoothSubmersion (n := n) (m := m) hmn).1.mdifferentiable
      (by simp)) (e p)
  have hComp :
      mfderiv
          (𝓡 n)
          (𝓡 (n - m))
          (sliceTailProjection (n := n) (m := m) hmn ∘ e)
          p =
        (mfderiv (𝓡 n) (𝓡 (n - m))
            (sliceTailProjection (n := n) (m := m) hmn) (e p)).comp
          (mfderiv (𝓡 n) (𝓡 n) e p) := by
    simpa [Function.comp] using mfderiv_comp p hProjAt hChartAt
  rw [show
      sliceTailProjection (n := n) (m := m) hmn ∘ e =
        sliceTailProjection (n := n) (m := m) hmn ∘
          slice_condition_ambient_chart (S := M) hSlice x0 by
      rfl] at hComp
  rw [hComp]
  have hProjSurj :
      Function.Surjective
        (mfderiv (𝓡 n) (𝓡 (n - m))
          (sliceTailProjection (n := n) (m := m) hmn) (e p)) :=
    (sliceTailProjection_isSmoothSubmersion (n := n) (m := m) hmn).2 (e p)
  have hChartSurj :
      Function.Surjective (mfderiv (𝓡 n) (𝓡 n) e p) :=
    maximalAtlasChart_mfderiv_surjective
      (n := n)
      (slice_condition_ambient_chart_mem_maximalAtlas (S := M) hSlice x0)
      hpSource
  simpa using hProjSurj.comp hChartSurj

/-- Helper for Proposition 6.25: the slice-tail composite is a local defining map on the chosen
ambient chart source. -/
lemma sliceTailCompositeIsLocalDefiningMapOn
    (x0 : M)
    (hSlice : Set.SatisfiesLocalSliceCondition n M m)
    (hmn : m ≤ n) :
    let e := slice_condition_ambient_chart (S := M) hSlice x0
    let Φ := sliceTailProjection (n := n) (m := m) hmn ∘ e
    IsLocalDefiningMapOn (𝓡 n) (𝓡 (n - m)) M e.source Φ := by
  classical
  let e := slice_condition_ambient_chart (S := M) hSlice x0
  let Φ := sliceTailProjection (n := n) (m := m) hmn ∘ e
  refine
    { isOpen_source := e.open_source
      smoothOn := ?_
      mem_iff_eq := ?_
      surjective_mfderiv := ?_ }
  · -- Smoothness comes from the ambient chart followed by the global smooth submersion
    -- `sliceTailProjection`.
    exact
      (sliceTailProjection_isSmoothSubmersion (n := n) (m := m) hmn).1.comp_contMDiffOn
        ((contMDiffOn_chartOfMemMaximalAtlas
          (n := n)
          (slice_condition_ambient_chart_mem_maximalAtlas (S := M) hSlice x0)).of_le
            (by simp))
  · intro p q hpM hpSource hqSource
    -- Normalize both membership tests to the same fixed tail-constant equation.
    have hpEq :
        Φ p = WithLp.toLp 2 (slice_condition_tail_constants (S := M) hSlice x0 hmn) :=
      (sliceTailComposite_mem_iff_eq_constants (n := n) (m := m) x0 hSlice hmn p hpSource).1 hpM
    constructor
    · intro hqM
      have hqEq :
          Φ q = WithLp.toLp 2 (slice_condition_tail_constants (S := M) hSlice x0 hmn) :=
        (sliceTailComposite_mem_iff_eq_constants (n := n) (m := m) x0 hSlice hmn q hqSource).1 hqM
      calc
        Φ q = WithLp.toLp 2 (slice_condition_tail_constants (S := M) hSlice x0 hmn) := hqEq
        _ = Φ p := hpEq.symm
    · intro hqEq
      have hqConst :
          Φ q = WithLp.toLp 2 (slice_condition_tail_constants (S := M) hSlice x0 hmn) := by
        calc
          Φ q = Φ p := hqEq
          _ = WithLp.toLp 2 (slice_condition_tail_constants (S := M) hSlice x0 hmn) := hpEq
      exact
        (sliceTailComposite_mem_iff_eq_constants (n := n) (m := m) x0 hSlice hmn q hqSource).2
          hqConst
  · intro p hpSource
    -- The chain rule reduces surjectivity to the chart derivative and the tail projection.
    simpa [Φ, e] using
      sliceTailComposite_mfderiv_surjective
        (n := n) (m := m) x0 hSlice hmn p hpSource

/-- Helper for Proposition 6.25: an open subset of the embedded submanifold is the pullback of an
ambient open subset of `ℝ^n`. -/
private theorem subtypeOpen_eq_preimage_ambientOpen
    {U : Set M} (hU : IsOpen U) :
    ∃ W : Set (EuclideanSpace ℝ (Fin n)), IsOpen W ∧ U = {y : M | y.1 ∈ W} := by
  -- Open sets in the subtype topology are exactly preimages of ambient open sets along
  -- `Subtype.val : M → ℝ^n`.
  rcases Topology.IsInducing.subtypeVal.isOpen_iff.mp hU with ⟨W, hWOpen, hW_eq⟩
  exact ⟨W, hWOpen, hW_eq.symm⟩

/-- Helper for Proposition 6.25: the local inclusion normal form around `x₀` contains a common
Euclidean ball about the origin in both source and target coordinates. -/
private theorem localInclusionFormCommonBallRadius
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m)) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε ⊆ hNF.domChart.target ∧
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ hNF.codChart.target := by
  have hdom_zero_mem : (0 : EuclideanSpace ℝ (Fin m)) ∈ hNF.domChart.target := by
    -- The centered source chart sends `x₀` to the origin.
    simpa [hNF.domChart_centered.2] using hNF.domChart.map_source hNF.domChart_centered.1
  have hcod_zero_mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ hNF.codChart.target := by
    -- The centered ambient chart sends `x₀` to the origin as well.
    simpa [hNF.codChart_centered.2] using hNF.codChart.map_source hNF.codChart_centered.1
  obtain ⟨εdom, hεdom_pos, hεdom_sub⟩ :=
    Metric.mem_nhds_iff.mp (hNF.domChart.open_target.mem_nhds hdom_zero_mem)
  obtain ⟨εcod, hεcod_pos, hεcod_sub⟩ :=
    Metric.mem_nhds_iff.mp (hNF.codChart.open_target.mem_nhds hcod_zero_mem)
  refine ⟨min εdom εcod, lt_min hεdom_pos hεcod_pos, ?_, ?_⟩
  · -- The smaller common ball still lies in the source-chart target.
    exact (Metric.ball_subset_ball (min_le_left _ _)).trans hεdom_sub
  · -- The same common radius also lies in the ambient chart target.
    exact (Metric.ball_subset_ball (min_le_right _ _)).trans hεcod_sub

/-- Helper for Proposition 6.25: the source-coordinate ball cut out by the local inclusion normal
form is an open patch of the embedded submanifold. -/
private def localInclusionFormSourceBall
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m))
    (ε : ℝ) : Set M :=
  hNF.domChart.symm '' Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε

/-- Helper for Proposition 6.25: the target-coordinate ball cut out by the local inclusion normal
form is an ambient open patch of `ℝ^n`. -/
private def localInclusionFormTargetBall
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m))
    (ε : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  hNF.codChart.symm '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε

/-- Helper for Proposition 6.25: shrinking the ambient normal-form chart to an open patch and a
common target ball gives the restricted chart used in the local defining-map proof. -/
private def localInclusionFormRestrictedChart
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m))
    (ε : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  hNF.codChart.restr (W ∩ localInclusionFormTargetBall hNF ε)

/-- Helper for Proposition 6.25: the source-coordinate ball of the local inclusion normal form is
open in the embedded submanifold. -/
private theorem localInclusionFormSourceBallOpen
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m))
    {ε : ℝ}
    (hεdom_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε ⊆ hNF.domChart.target) :
    IsOpen (localInclusionFormSourceBall hNF ε) := by
  -- The inverse source chart is open on any target subset contained in its target.
  simpa [localInclusionFormSourceBall, Set.inter_eq_right.2 hεdom_ball] using
    hNF.domChart.symm.isOpen_image_source_inter
      (Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε))

/-- Helper for Proposition 6.25: the target-coordinate ball of the local inclusion normal form is
open in the ambient Euclidean space. -/
private theorem localInclusionFormTargetBallOpen
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m))
    {ε : ℝ}
    (hεcod_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ hNF.codChart.target) :
    IsOpen (localInclusionFormTargetBall hNF ε) := by
  -- The inverse ambient chart is open on any target subset contained in its target.
  simpa [localInclusionFormTargetBall, Set.inter_eq_right.2 hεcod_ball] using
    hNF.codChart.symm.isOpen_image_source_inter
      (Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε))

/-- Helper for Proposition 6.25: the restricted ambient chart used in the local normal-form proof
has the expected source formula. -/
private theorem localInclusionFormRestrictedChart_source
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m))
    {ε : ℝ} {W : Set (EuclideanSpace ℝ (Fin n))} (hWOpen : IsOpen W)
    (hεcod_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ hNF.codChart.target) :
    (localInclusionFormRestrictedChart hNF ε W).source =
      hNF.codChart.source ∩ (W ∩ localInclusionFormTargetBall hNF ε) := by
  have hV0_open : IsOpen (localInclusionFormTargetBall hNF ε) :=
    localInclusionFormTargetBallOpen hNF hεcod_ball
  -- Unfold the restriction once to record the shrunken source used later.
  simpa [localInclusionFormRestrictedChart] using
    hNF.codChart.restr_source' (W ∩ localInclusionFormTargetBall hNF ε)
      (hWOpen.inter hV0_open)

/-- Helper for Proposition 6.25: the restricted ambient chart used in the local normal-form proof
has the expected target formula. -/
private theorem localInclusionFormRestrictedChart_target
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m))
    {ε : ℝ} {W : Set (EuclideanSpace ℝ (Fin n))} (hWOpen : IsOpen W)
    (hεcod_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ hNF.codChart.target) :
    (localInclusionFormRestrictedChart hNF ε W).target =
      hNF.codChart.target ∩
        hNF.codChart.symm ⁻¹' (W ∩ localInclusionFormTargetBall hNF ε) := by
  have hV0_open : IsOpen (localInclusionFormTargetBall hNF ε) :=
    localInclusionFormTargetBallOpen hNF hεcod_ball
  have hPatchOpen : IsOpen (W ∩ localInclusionFormTargetBall hNF ε) :=
    hWOpen.inter hV0_open
  -- Unfold the restriction target once so later rewrites see the ambient patch explicitly.
  simp [localInclusionFormRestrictedChart, PartialEquiv.restr_target, hPatchOpen.interior_eq]

/-- Helper for Proposition 6.25: after restricting the ambient chart in a local inclusion normal
form to an ambient patch matching the domain-chart source, the restricted source is exactly the
corresponding ambient patch of `M`. -/
private theorem localInclusionForm_sourceImage_eq_restrictedPatch
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m))
    {W : Set (EuclideanSpace ℝ (Fin n))} (hWOpen : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : M | y.1 ∈ W}) :
    Subtype.val '' hNF.domChart.source = M ∩ (hNF.codChart.restr W).source := by
  -- Expanding the restricted source shows that both sides record the same ambient patch of `M`.
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨z, hz, rfl⟩
    have hzW : z.1 ∈ W := by
      simpa [hW_eq] using hz
    have hzCod : z.1 ∈ hNF.codChart.source := by
      exact LocalNormalFormAPI.LocalCoordinateNormalFormAt.mapsTo_source hNF hz
    refine ⟨z.2, ?_⟩
    rw [hNF.codChart.restr_source' W hWOpen]
    exact ⟨hzCod, hzW⟩
  · rintro ⟨hyM, hyRestr⟩
    rw [hNF.codChart.restr_source' W hWOpen] at hyRestr
    let yM : M := ⟨y, hyM⟩
    have hyDom : yM ∈ hNF.domChart.source := by
      simpa [hW_eq] using hyRestr.2
    exact ⟨yM, hyDom, rfl⟩

/-- Helper for Proposition 6.25: after restricting a local inclusion normal form to an ambient
patch, the ambient image of `M` on that patch is exactly the zero-tail Euclidean slice once the
projected head coordinates stay in the source-chart target. -/
private theorem localInclusionForm_image_eq_zeroSlice_of_projection_memTarget
    (hmn : m ≤ n)
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m))
    {W : Set (EuclideanSpace ℝ (Fin n))} (hWOpen : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : M | y.1 ∈ W})
    (hproj :
      ∀ {z : EuclideanSpace ℝ (Fin n)},
        z ∈ Set.euclideanSlice (hNF.codChart.restr W).target m hmn
            (fun _ : Fin (n - m) ↦ (0 : ℝ)) →
          euclidean_slice_projection hmn z ∈ hNF.domChart.target) :
    (hNF.codChart.restr W) '' (M ∩ (hNF.codChart.restr W).source) =
      Set.euclideanSlice (hNF.codChart.restr W).target m hmn
        (fun _ : Fin (n - m) ↦ (0 : ℝ)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have hyImage :
        y ∈ Subtype.val '' hNF.domChart.source := by
      rw [localInclusionForm_sourceImage_eq_restrictedPatch (hNF := hNF) hWOpen hW_eq]
      exact hy
    rcases hyImage with ⟨yM, hyDom, rfl⟩
    refine ⟨?_, ?_⟩
    · -- The restricted ambient chart lands in its own target on source points.
      exact (hNF.codChart.restr W).map_source hy.2
    · -- The local inclusion normal form forces all tail coordinates to vanish on points of `M`.
      intro i
      have hyTarget : hNF.domChart yM ∈ hNF.domChart.target :=
        hNF.domChart.map_source hyDom
      have hyLeftInv : hNF.domChart.symm (hNF.domChart yM) = yM := by
        exact hNF.domChart.left_inv hyDom
      have hcoord :
          (hNF.codChart.restr W) yM.1 =
            LocalNormalFormAPI.rank_normal_form m n m (hNF.domChart yM) := by
        simpa [Function.comp, hyLeftInv] using hNF.eqOn hyTarget
      simpa [hcoord, rank_normal_form_self_eq_euclidean_slice_inclusion_zero hmn] using
        (euclidean_slice_inclusion_tail hmn
          (fun _ : Fin (n - m) ↦ (0 : ℝ))
          (hNF.domChart yM) i)
  · intro z hz
    let yM : M := hNF.domChart.symm (euclidean_slice_projection hmn z)
    have hyTarget : euclidean_slice_projection hmn z ∈ hNF.domChart.target := hproj hz
    have hyDom : yM ∈ hNF.domChart.source := by
      simpa [yM] using hNF.domChart.symm.map_source hyTarget
    have hySource : yM.1 ∈ (hNF.codChart.restr W).source := by
      have hyImage :
          yM.1 ∈ Subtype.val '' hNF.domChart.source := ⟨yM, hyDom, rfl⟩
      rw [localInclusionForm_sourceImage_eq_restrictedPatch (hNF := hNF) hWOpen hW_eq] at hyImage
      exact hyImage.2
    have hyCoord :
        (hNF.codChart.restr W) yM.1 = z := by
      calc
        (hNF.codChart.restr W) yM.1 =
            LocalNormalFormAPI.rank_normal_form m n m
              (euclidean_slice_projection hmn z) := by
              simpa [Function.comp, yM] using hNF.eqOn hyTarget
        _ = z := by
          rw [rank_normal_form_self_eq_euclidean_slice_inclusion_zero hmn]
          exact
            euclidean_slice_inclusion_projection hmn
              (fun _ : Fin (n - m) ↦ (0 : ℝ)) hz
    exact ⟨yM.1, ⟨yM.2, hySource⟩, hyCoord⟩

/-- Helper for Proposition 6.25: after shrinking the local inclusion normal form to a common
coordinate ball, the restricted ambient chart sends `M` exactly onto the zero-tail Euclidean
slice. -/
private theorem localInclusionFormRestrictedImageEqZeroSlice
    (hmn : m ≤ n)
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m))
    {ε : ℝ}
    (hεdom_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε ⊆ hNF.domChart.target)
    (hεcod_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ hNF.codChart.target)
    {W : Set (EuclideanSpace ℝ (Fin n))} (hWOpen : IsOpen W)
    (hW_eq : localInclusionFormSourceBall hNF ε = {y : M | y.1 ∈ W}) :
    (localInclusionFormRestrictedChart hNF ε W) '' (M ∩
        (localInclusionFormRestrictedChart hNF ε W).source) =
      Set.euclideanSlice
        (localInclusionFormRestrictedChart hNF ε W).target
        m hmn (fun _ : Fin (n - m) ↦ (0 : ℝ)) := by
  let U0 : Set M := localInclusionFormSourceBall hNF ε
  let V0 : Set (EuclideanSpace ℝ (Fin n)) := localInclusionFormTargetBall hNF ε
  let e := localInclusionFormRestrictedChart hNF ε W
  ext z
  constructor
  · intro hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases hy with ⟨hyM, hyRestr⟩
    have hyRestr_e : y ∈ e.source := hyRestr
    rw [localInclusionFormRestrictedChart_source (hNF := hNF) hWOpen hεcod_ball] at hyRestr
    let yS : M := ⟨y, hyM⟩
    have hyU0 : yS ∈ U0 := by
      -- The ambient patch `W` was chosen to cut out the source-ball patch in `M`.
      simpa [U0, hW_eq, yS] using hyRestr.2.1
    rcases hyU0 with ⟨u, huBall, huSymm⟩
    have huTarget : u ∈ hNF.domChart.target := hεdom_ball huBall
    have hyDom : yS ∈ hNF.domChart.source := by
      -- The inverse source chart sends a target coordinate back into the domain patch.
      simpa [yS, huSymm] using hNF.domChart.symm.map_source huTarget
    have hyCodSource : y ∈ hNF.codChart.source := hNF.mapsTo_source hyDom
    have hcoord :
        hNF.codChart y =
          LocalNormalFormAPI.rank_normal_form m n m u := by
      -- Collapse the local inclusion normal form at the chosen source coordinate `u`.
      simpa [Function.comp, yS, huSymm] using hNF.eqOn huTarget
    refine ⟨e.map_source hyRestr_e, ?_⟩
    -- The local normal form forces all tail coordinates of the restricted image to vanish.
    simpa [e, localInclusionFormRestrictedChart, hcoord,
      rank_normal_form_self_eq_euclidean_slice_inclusion_zero hmn] using
      (euclidean_slice_inclusion_tail hmn
        (fun _ : Fin (n - m) ↦ (0 : ℝ)) u)
  · intro hz
    let y0 := hNF.codChart.symm z
    have hzTargetData :
        z ∈ hNF.codChart.target ∩
          hNF.codChart.symm ⁻¹' (W ∩ V0) := by
      -- Rewrite the restricted target back to the original chart target plus the restricted
      -- source condition.
      simpa [e, V0] using
        (show z ∈
          hNF.codChart.target ∩
            hNF.codChart.symm ⁻¹' (W ∩ localInclusionFormTargetBall hNF ε) from by
              rw [← localInclusionFormRestrictedChart_target (hNF := hNF) hWOpen hεcod_ball]
              exact hz.1)
    have hzCodTarget : z ∈ hNF.codChart.target := hzTargetData.1
    have hy0WV0 : y0 ∈ W ∩ V0 := hzTargetData.2
    have hzBall : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε := by
      -- Because `y0` lies in the target-ball patch `V0`, the coordinate `z` is one of the chosen
      -- ambient ball points.
      rcases hy0WV0.2 with ⟨w, hwBall, hwSymm⟩
      have hwTarget : w ∈ hNF.codChart.target := hεcod_ball hwBall
      have hzw : z = w := by
        calc
          z = hNF.codChart y0 := by
                simpa [y0] using (hNF.codChart.right_inv hzCodTarget).symm
          _ = hNF.codChart (hNF.codChart.symm w) := by
                simpa [y0] using congrArg hNF.codChart hwSymm.symm
          _ = w := hNF.codChart.right_inv hwTarget
      simpa [hzw] using hwBall
    have huBall :
        euclidean_slice_projection hmn z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε :=
      zeroTailProjection_memBall (n := n) (m := m) hmn hzBall hz
    let yS : M := hNF.domChart.symm (euclidean_slice_projection hmn z)
    have hyTarget : euclidean_slice_projection hmn z ∈ hNF.domChart.target :=
      hεdom_ball huBall
    have hyDom : yS ∈ hNF.domChart.source := by
      -- The projected point lies in the source-chart target, so its inverse lies back in the
      -- embedded submanifold patch.
      exact hNF.domChart.symm.map_source hyTarget
    have hyCodSource : yS.1 ∈ hNF.codChart.source := hNF.mapsTo_source hyDom
    have hyW : yS.1 ∈ W := by
      have hyU0 : yS ∈ U0 := by
        refine ⟨euclidean_slice_projection hmn z, huBall, rfl⟩
      -- Translate source-ball membership back to the ambient open patch `W`.
      simpa [U0, hW_eq, yS] using hyU0
    have hyCoord : hNF.codChart yS.1 = z := by
      -- Project a zero-tail point and reinsert it through the local inclusion normal form.
      calc
        hNF.codChart yS.1 =
            LocalNormalFormAPI.rank_normal_form m n m
              (euclidean_slice_projection hmn z) := by
              simpa [Function.comp, yS] using hNF.eqOn hyTarget
        _ = z := by
          rw [rank_normal_form_self_eq_euclidean_slice_inclusion_zero hmn]
          exact
            euclidean_slice_inclusion_projection hmn
              (fun _ : Fin (n - m) ↦ (0 : ℝ)) hz
    have hyV0 : yS.1 ∈ V0 := by
      -- The reconstructed point has coordinate `z`, which lies in the ambient target ball.
      refine ⟨z, hzBall, ?_⟩
      simpa [V0, hyCoord] using hNF.codChart.left_inv hyCodSource
    have hyRestr : yS.1 ∈ e.source := by
      -- Expand the restricted source to record the ambient patch and target-ball conditions.
      rw [localInclusionFormRestrictedChart_source (hNF := hNF) hWOpen hεcod_ball]
      exact ⟨hyCodSource, ⟨hyW, hyV0⟩⟩
    refine ⟨yS.1, ⟨yS.2, hyRestr⟩, ?_⟩
    -- The reconstructed point maps back to `z` under the restricted ambient chart.
    simpa [e, localInclusionFormRestrictedChart] using hyCoord

/-- Helper for Proposition 6.25: on the restricted local inclusion chart, membership in `M` is
equivalent to vanishing of the tail-coordinate defining map. -/
private theorem localInclusionFormRestricted_mem_iff_sliceTailProjection_eq_zero
    (hmn : m ≤ n)
    {x0 : M}
    (hNF : LocalNormalFormAPI.LocalCoordinateNormalFormAt
      (Subtype.val : M → EuclideanSpace ℝ (Fin n))
      x0
      (LocalNormalFormAPI.rank_normal_form m n m))
    {ε : ℝ}
    (hεdom_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin m)) ε ⊆ hNF.domChart.target)
    (hεcod_ball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ hNF.codChart.target)
    {W : Set (EuclideanSpace ℝ (Fin n))} (hWOpen : IsOpen W)
    (hW_eq : localInclusionFormSourceBall hNF ε = {y : M | y.1 ∈ W}) :
    let e := localInclusionFormRestrictedChart hNF ε W
    let Φ := sliceTailProjection (n := n) (m := m) hmn ∘ e
    ∀ q : EuclideanSpace ℝ (Fin n), q ∈ e.source → (q ∈ M ↔ Φ q = 0) := by
  let e := localInclusionFormRestrictedChart hNF ε W
  let Φ := sliceTailProjection (n := n) (m := m) hmn ∘ e
  change ∀ q : EuclideanSpace ℝ (Fin n), q ∈ e.source → (q ∈ M ↔ Φ q = 0)
  have hImageEq :
      e '' (M ∩ e.source) =
        Set.euclideanSlice e.target m hmn (fun _ : Fin (n - m) ↦ (0 : ℝ)) :=
    localInclusionFormRestrictedImageEqZeroSlice
      (n := n) (m := m) hmn hNF hεdom_ball hεcod_ball hWOpen hW_eq
  intro q hqSource
  refine ⟨?_, ?_⟩
  · intro hqM
    have heSlice :
        e q ∈ Set.euclideanSlice e.target m hmn (fun _ : Fin (n - m) ↦ (0 : ℝ)) := by
      rw [← hImageEq]
      exact ⟨q, ⟨hqM, hqSource⟩, rfl⟩
    -- Membership in the zero-tail slice is equivalent to vanishing of the tail projection.
    simpa [Φ] using
      (mem_euclideanSlice_iff_sliceTailProjection_eq (n := n) (m := m) hmn
        (e.map_source hqSource)).1 heSlice
  · intro hqEq
    have heSlice :
        e q ∈ Set.euclideanSlice e.target m hmn (fun _ : Fin (n - m) ↦ (0 : ℝ)) := by
      exact
        (mem_euclideanSlice_iff_sliceTailProjection_eq (n := n) (m := m) hmn
          (e.map_source hqSource)).2 (by simpa [Φ] using hqEq)
    rw [← hImageEq] at heSlice
    rcases heSlice with ⟨y, ⟨hyM, hySource⟩, hyEq⟩
    have hyq : y = q := by
      -- The restricted chart is injective on its source, so equal coordinates identify the point.
      calc
        y = e.symm (e y) := (e.left_inv hySource).symm
        _ = e.symm (e q) := by rw [hyEq]
        _ = q := e.left_inv hqSource
    simpa [hyq] using hyM

/-- Helper for Proposition 6.25: around each base point of `M`, the embedded inclusion is cut out
by a local defining map on an ambient open patch of `ℝ^n`. -/
private theorem embeddedSubmanifoldLocalDefiningMapAt_of_topManifold
    [IsManifold (𝓡 m) (⊤ : WithTop ℕ∞) M] (x0 : M) :
    ∃ hmn : m ≤ n,
      ∃ U : Set (EuclideanSpace ℝ (Fin n)),
        ∃ Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - m)),
          ((x0 : M) : EuclideanSpace ℝ (Fin n)) ∈ U ∧
            Φ ((x0 : M) : EuclideanSpace ℝ (Fin n)) = 0 ∧
              IsLocalDefiningMapOn (𝓡 n) (𝓡 (n - m)) M U Φ := by
  let hEmb : IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M := inferInstance
  let tm : TopologicalManifold m M := topologicalManifoldOfChartedSpace m M
  let hs : IsManifold (𝓡 m) (⊤ : WithTop ℕ∞) M := inferInstance
  letI : TopologicalManifold m M := tm
  letI : IsManifold (𝓡 m) (⊤ : WithTop ℕ∞) M := hs
  have hSlice : Set.SatisfiesLocalSliceCondition n M m := by
    -- Theorem 5.8 turns the top-order embedded-submanifold owner into the needed slice chart.
    exact
      (local_slice_criterion_for_embedded_submanifold
        (M := EuclideanSpace ℝ (Fin n)) (n := n) (k := m) M).2
        ⟨tm, hs, hEmb⟩
  let hmn : m ≤ n := embeddedSubmanifoldDimensionLe (n := n) (m := m) (M := M) x0
  let e := slice_condition_ambient_chart (S := M) hSlice x0
  let Φ0 := sliceTailProjection (n := n) (m := m) hmn ∘ e
  let c := Φ0 ((x0 : M) : EuclideanSpace ℝ (Fin n))
  let Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - m)) :=
    fun q ↦ Φ0 q + (-c)
  have hx0U : ((x0 : M) : EuclideanSpace ℝ (Fin n)) ∈ e.source := by
    -- The slice chart from Theorem 5.8 is centered at `x0`.
    simpa [e] using slice_condition_ambient_chart_mem_source (S := M) hSlice x0
  have hΦx0 : Φ ((x0 : M) : EuclideanSpace ℝ (Fin n)) = 0 := by
    -- Center the defining map by subtracting its value at the base point.
    simp [Φ, c]
  have hDef0 : IsLocalDefiningMapOn (𝓡 n) (𝓡 (n - m)) M e.source Φ0 := by
    -- The unshifted slice-tail composite is already a local defining map on the slice chart.
    simpa [e, Φ0] using
      sliceTailCompositeIsLocalDefiningMapOn (n := n) (m := m) x0 hSlice hmn
  have hDef : IsLocalDefiningMapOn (𝓡 n) (𝓡 (n - m)) M e.source Φ := by
    refine
      { isOpen_source := hDef0.isOpen_source
        smoothOn := ?_
        mem_iff_eq := ?_
        surjective_mfderiv := ?_ }
    · -- Adding a constant vector preserves smoothness on the same open source.
      simpa [Φ] using hDef0.smoothOn.add
        (contMDiffOn_const : ContMDiffOn (𝓡 n) (𝓡 (n - m)) ∞
          (fun _ : EuclideanSpace ℝ (Fin n) ↦ -c) e.source)
    · intro p q hpM hpSource hqSource
      -- Equality of the shifted map is equivalent to equality of the original slice-tail map.
      simpa [Φ, add_assoc] using hDef0.mem_iff_eq hpM hpSource hqSource
    · intro p hpSource
      have hΦ0ContMDiffAt : ContMDiffAt (𝓡 n) (𝓡 (n - m)) ∞ Φ0 p :=
        (hDef0.smoothOn p hpSource).contMDiffAt (hDef0.isOpen_source.mem_nhds hpSource)
      have hΦ0DiffAt : MDiffAt Φ0 p :=
        hΦ0ContMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
      have hconstDiffAt : MDiffAt (fun _ : EuclideanSpace ℝ (Fin n) ↦ -c) p :=
        mdifferentiableAt_const
      have hmfderiv :
          mfderiv (𝓡 n) (𝓡 (n - m)) Φ p =
            mfderiv (𝓡 n) (𝓡 (n - m)) Φ0 p := by
        -- The derivative is unchanged by the constant codomain translation.
        change
          mfderiv (𝓡 n) (𝓡 (n - m)) (Φ0 + fun _ : EuclideanSpace ℝ (Fin n) ↦ -c) p =
            mfderiv (𝓡 n) (𝓡 (n - m)) Φ0 p
        rw [mfderiv_add hΦ0DiffAt hconstDiffAt, mfderiv_const]
        exact add_zero _
      rw [hmfderiv]
      exact hDef0.surjective_mfderiv hpSource
  exact ⟨hmn, e.source, Φ, hx0U, hΦx0, hDef⟩

/-- Helper for Proposition 6.25: around each base point of `M`, the embedded inclusion is cut out
by a local defining map on an ambient open patch of `ℝ^n`. -/
lemma embeddedSubmanifoldLocalDefiningMapAt (x0 : M) :
    ∃ hmn : m ≤ n,
      ∃ U : Set (EuclideanSpace ℝ (Fin n)),
        ∃ Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - m)),
          ((x0 : M) : EuclideanSpace ℝ (Fin n)) ∈ U ∧
            Φ ((x0 : M) : EuclideanSpace ℝ (Fin n)) = 0 ∧
              IsLocalDefiningMapOn (𝓡 n) (𝓡 (n - m)) M U Φ := by
  rcases subtypeVal_localInclusionForm (n := n) (m := m) (M := M) x0 with ⟨hNF, -⟩
  let hmn : m ≤ n := embeddedSubmanifoldDimensionLe (n := n) (m := m) (M := M) x0
  rcases localInclusionFormCommonBallRadius (n := n) (m := m) hNF with
    ⟨ε, hε_pos, hεdom_ball, hεcod_ball⟩
  let U0 : Set M := localInclusionFormSourceBall hNF ε
  have hU0_open : IsOpen U0 := localInclusionFormSourceBallOpen hNF hεdom_ball
  rcases subtypeOpen_eq_preimage_ambientOpen (U := U0) hU0_open with
    ⟨W, hWOpen, hW_eq⟩
  let e := localInclusionFormRestrictedChart hNF ε W
  let Φ := sliceTailProjection (n := n) (m := m) hmn ∘ e
  have hV0_open : IsOpen (localInclusionFormTargetBall hNF ε) :=
    localInclusionFormTargetBallOpen hNF hεcod_ball
  have heMax :
      e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n)) := by
    -- Restrict the ambient normal-form chart to the smaller patch used for the defining map.
    change hNF.codChart.restr (W ∩ localInclusionFormTargetBall hNF ε) ∈
      IsManifold.maximalAtlas (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
    exact restr_mem_maximalAtlas
      (contDiffGroupoid (∞ : ℕ∞ω) (𝓡 n)) hNF.codChart_mem_maximalAtlas
      (hWOpen.inter hV0_open)
  have hx0U0 : x0 ∈ U0 := by
    -- The centered source chart sends `x₀` to `0`, so `x₀` lies in the source coordinate ball.
    refine ⟨0, ?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using hε_pos
    · simpa [U0, localInclusionFormSourceBall, hNF.domChart_centered.2] using
        hNF.domChart.left_inv hNF.domChart_centered.1
  have hx0V0 :
      ((x0 : M) : EuclideanSpace ℝ (Fin n)) ∈ localInclusionFormTargetBall hNF ε := by
    -- The centered ambient chart also sends `x₀` to `0`, so the target-ball patch contains it.
    refine ⟨0, ?_, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using hε_pos
    · simpa [localInclusionFormTargetBall, hNF.codChart_centered.2] using
        hNF.codChart.left_inv hNF.codChart_centered.1
  have hx0W : ((x0 : M) : EuclideanSpace ℝ (Fin n)) ∈ W := by
    -- The ambient patch `W` was chosen to cut out the source-ball patch `U₀`.
    simpa [U0, hW_eq] using hx0U0
  have hx0U : ((x0 : M) : EuclideanSpace ℝ (Fin n)) ∈ e.source := by
    -- Expand the restricted source and record the source-chart, ambient-patch, and target-ball
    -- conditions at `x₀`.
    rw [localInclusionFormRestrictedChart_source (hNF := hNF) hWOpen hεcod_ball]
    exact ⟨hNF.codChart_centered.1, ⟨hx0W, hx0V0⟩⟩
  have hΦx0 : Φ ((x0 : M) : EuclideanSpace ℝ (Fin n)) = 0 := by
    -- In the centered local inclusion form, the tail coordinates of `x₀` already vanish.
    simpa [Φ, e, localInclusionFormRestrictedChart, hNF.codChart_centered.2]
      using (show sliceTailProjection (n := n) (m := m) hmn (0 : EuclideanSpace ℝ (Fin n)) = 0 by
        ext i
        simp [sliceTailProjection])
  have hMemIff :
      ∀ q : EuclideanSpace ℝ (Fin n), q ∈ e.source → (q ∈ M ↔ Φ q = 0) :=
    localInclusionFormRestricted_mem_iff_sliceTailProjection_eq_zero
      (n := n) (m := m) hmn hNF hεdom_ball hεcod_ball hWOpen hW_eq
  have hDef : IsLocalDefiningMapOn (𝓡 n) (𝓡 (n - m)) M e.source Φ := by
    refine
      { isOpen_source := e.open_source
        smoothOn := ?_
        mem_iff_eq := ?_
        surjective_mfderiv := ?_ }
    · -- Compose the restricted ambient chart with the global tail projection.
      exact
        (sliceTailProjection_isSmoothSubmersion (n := n) (m := m) hmn).1.comp_contMDiffOn
          (contMDiffOn_chartOfMemMaximalAtlasInfty (n := n) heMax)
    · intro p q hpM hpSource hqSource
      have hpEq : Φ p = 0 := (hMemIff p hpSource).1 hpM
      constructor
      · intro hqM
        have hqEq : Φ q = 0 := (hMemIff q hqSource).1 hqM
        calc
          Φ q = 0 := hqEq
          _ = Φ p := hpEq.symm
      · intro hqEq
        have hqZero : Φ q = 0 := by
          calc
            Φ q = Φ p := hqEq
            _ = 0 := hpEq
        exact (hMemIff q hqSource).2 hqZero
    · intro p hpSource
      have hChartAt :
          MDifferentiableAt (𝓡 n) (𝓡 n) e p := by
        exact (maximalAtlasChart_mdifferentiableInfty (n := n) heMax).mdifferentiableAt hpSource
      have hProjAt :
          MDifferentiableAt (𝓡 n) (𝓡 (n - m))
            (sliceTailProjection (n := n) (m := m) hmn) (e p) := by
        exact ((sliceTailProjection_isSmoothSubmersion (n := n) (m := m) hmn).1.mdifferentiable
          (by simp : (∞ : ℕ∞ω) ≠ 0)) (e p)
      have hComp :
          mfderiv (𝓡 n) (𝓡 (n - m)) Φ p =
            (mfderiv (𝓡 n) (𝓡 (n - m))
                (sliceTailProjection (n := n) (m := m) hmn) (e p)).comp
              (mfderiv (𝓡 n) (𝓡 n) e p) := by
        simpa [Φ, Function.comp] using mfderiv_comp p hProjAt hChartAt
      rw [hComp]
      -- The derivative is the composition of the chart derivative with the surjective tail
      -- projection derivative.
      exact
        ((sliceTailProjection_isSmoothSubmersion (n := n) (m := m) hmn).2 (e p)).comp
          (maximalAtlasChart_mfderiv_surjectiveInfty (n := n) heMax hpSource)
  exact ⟨hmn, e.source, Φ, hx0U, hΦx0, hDef⟩

/-- Helper for Proposition 6.25: pulling an ambient open subset of `ℝ^n` back along
`Subtype.val : M → ℝ^n` gives an open patch of the embedded submanifold `M`. -/
def ambientOpenPatchInSubmanifold
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) : TopologicalSpace.Opens M :=
  ⟨((Subtype.val : M → EuclideanSpace ℝ (Fin n)) ⁻¹' U), hU.preimage continuous_subtype_val⟩

/-- Helper for Proposition 6.25: the ambient source of the chosen slice chart cuts out an open
patch of `M`. -/
lemma isOpen_preimage_sliceChartSource
    (x0 : M) (hSlice : Set.SatisfiesLocalSliceCondition n M m) :
    IsOpen
      ((((↑) : M → EuclideanSpace ℝ (Fin n)) ⁻¹'
        (slice_condition_ambient_chart (S := M) hSlice x0).source)) := by
  -- Pull back the ambient chart source along the subtype inclusion `M ↪ ℝ^n`.
  simpa [Set.preimage, Function.comp] using
    (slice_condition_ambient_chart (S := M) hSlice x0).open_source.preimage
      continuous_subtype_val

/-- Helper for Proposition 6.25: the ambient source of the chosen slice chart, viewed as an open
subset of the embedded submanifold `M`. -/
def sliceChartSourcePatch
    (x0 : M) (hSlice : Set.SatisfiesLocalSliceCondition n M m) :
    TopologicalSpace.Opens M :=
  ⟨(((↑) : M → EuclideanSpace ℝ (Fin n)) ⁻¹'
      (slice_condition_ambient_chart (S := M) hSlice x0).source),
    isOpen_preimage_sliceChartSource (n := n) (m := m) (M := M) x0 hSlice⟩

/-- Helper for Proposition 6.25: the chosen base point lies in the slice-chart source patch of
`M`. -/
lemma basepoint_mem_sliceChartSourcePatch
    (x0 : M) (hSlice : Set.SatisfiesLocalSliceCondition n M m) :
    x0 ∈ sliceChartSourcePatch (n := n) (m := m) (M := M) x0 hSlice := by
  -- The ambient slice chart is centered at `x0`, so its source contains `x0`.
  simpa [sliceChartSourcePatch] using
    slice_condition_ambient_chart_mem_source (S := M) hSlice x0

/-- Helper for Proposition 6.25: the ambient inclusion `M ↪ ℝ^n`, restricted to the slice-chart
source patch, is smooth. -/
lemma sliceChartSourcePatchAmbientInclusion_contMDiff
    (x0 : M) (hSlice : Set.SatisfiesLocalSliceCondition n M m) :
    ContMDiff (𝓡 m) (𝓡 n) ∞
      (fun x : sliceChartSourcePatch (n := n) (m := m) (M := M) x0 hSlice ↦
        ((x : M) : EuclideanSpace ℝ (Fin n))) := by
  -- Restrict the already smooth ambient inclusion of `M` to the open slice-chart source patch.
  simpa [sliceChartSourcePatch, Function.comp] using
    subtype_val_contMDiff.comp
      (contMDiff_subtype_val :
        ContMDiff (𝓡 m) (𝓡 m) ∞
          (Subtype.val :
            sliceChartSourcePatch (n := n) (m := m) (M := M) x0 hSlice → M))

/-- Helper for Proposition 6.25: the slice-chart source patch is nonempty because it contains the
chosen base point. -/
lemma sliceChartSourcePatch_nonempty
    (x0 : M) (hSlice : Set.SatisfiesLocalSliceCondition n M m) :
    (sliceChartSourcePatch (n := n) (m := m) (M := M) x0 hSlice : Set M).Nonempty := by
  -- The base point lies in the patch by construction of the chosen ambient slice chart.
  exact ⟨x0, basepoint_mem_sliceChartSourcePatch (n := n) (m := m) (M := M) x0 hSlice⟩

/-- Helper for Proposition 6.25: the derivative field of the slice-tail composite is smooth on the
open source patch of the slice chart. -/
lemma sliceTailDerivativeField_contMDiff
    (x0 : M)
    (hSlice : Set.SatisfiesLocalSliceCondition n M m)
    (hmn : m ≤ n) :
    let e := slice_condition_ambient_chart (S := M) hSlice x0
    let Φ := sliceTailProjection (n := n) (m := m) hmn ∘ e
    let V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨e.source, e.open_source⟩
    ContMDiff
      (𝓡 n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - m)))
      ∞
      (fun x : V ↦ fderiv ℝ Φ x.1) := by
  classical
  let e := slice_condition_ambient_chart (S := M) hSlice x0
  let Φ := sliceTailProjection (n := n) (m := m) hmn ∘ e
  let V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨e.source, e.open_source⟩
  change
    ContMDiff
      (𝓡 n)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - m)))
      ∞
      (fun x : V ↦ fderiv ℝ Φ x.1)
  intro x
  have hx' := (contMDiffAt_subtype_iff
      (I := 𝓡 n)
      (I' := 𝓘(ℝ,
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - m))))
      (U := V)
      (f := fun y : EuclideanSpace ℝ (Fin n) ↦ fderiv ℝ Φ y)
      (x := x)).2 <| by
        rw [contMDiffAt_iff_contDiffAt]
        have hΦAtManifold :
            ContMDiffAt (𝓡 n) (𝓡 (n - m)) ∞ Φ x.1 := by
          -- Upgrade the local-defining-map smoothness on the open source to an ordinary smooth point.
          exact
            ((sliceTailCompositeIsLocalDefiningMapOn (n := n) (m := m) x0 hSlice hmn).smoothOn
              x.1 x.2).contMDiffAt (e.open_source.mem_nhds x.2)
        have hΦAt :
            ContDiffAt ℝ ∞ Φ x.1 := by
          -- In Euclidean model spaces, manifold smoothness and ordinary smoothness coincide.
          rw [← contMDiffAt_iff_contDiffAt]
          exact hΦAtManifold
        let F :
            EuclideanSpace ℝ (Fin n) →
              EuclideanSpace ℝ (Fin n) →
                EuclideanSpace ℝ (Fin (n - m)) :=
          fun _ y ↦ Φ y
        have hF :
            ContDiffAt ℝ ∞ (Function.uncurry F) (x.1, x.1) := by
          -- Regard `Φ` as a constant family in the base variable and differentiate in the second slot.
          simpa [F, Function.comp] using hΦAt.comp (x.1, x.1) contDiffAt_snd
        -- `ContDiffAt.fderiv` yields the smooth operator-valued derivative field in fixed coordinates.
        simpa [F] using
          (ContDiffAt.fderiv
            (x₀ := x.1)
            (f := F)
            (g := fun y : EuclideanSpace ℝ (Fin n) ↦ y)
            hF
            contDiffAt_id
            (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞))
  simpa using hx'

/-- Helper for Proposition 6.25: restricting the slice-tail derivative field from the ambient
chart source to the slice-chart source patch of `M` preserves smoothness. -/
lemma sliceTailDerivativeField_onPatch_contMDiff
    (x0 : M)
    (hSlice : Set.SatisfiesLocalSliceCondition n M m)
    (hmn : m ≤ n) :
    let e := slice_condition_ambient_chart (S := M) hSlice x0
    let Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - m)) :=
      sliceTailProjection (n := n) (m := m) hmn ∘ e
    ContMDiff
      (𝓡 m)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - m)))
      ∞
      (fun x : sliceChartSourcePatch (n := n) (m := m) (M := M) x0 hSlice ↦
        fderiv ℝ Φ ((x : M) : EuclideanSpace ℝ (Fin n))) := by
  classical
  let e := slice_condition_ambient_chart (S := M) hSlice x0
  let Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - m)) :=
    sliceTailProjection (n := n) (m := m) hmn ∘ e
  let V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨e.source, e.open_source⟩
  let ιV :
      sliceChartSourcePatch (n := n) (m := m) (M := M) x0 hSlice → V :=
    Set.codRestrict
      (fun x : sliceChartSourcePatch (n := n) (m := m) (M := M) x0 hSlice ↦
        ((x : M) : EuclideanSpace ℝ (Fin n)))
      V
      (fun x ↦ x.2)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) V := inferInstance
  let _ : IsManifold (𝓡 n) ∞ V := inferInstance
  have hOpenEmbedding :
      IsSmoothEmbedding (𝓡 n) (𝓡 n) ∞ (Subtype.val : V → EuclideanSpace ℝ (Fin n)) := by
    -- The source `V` is an open subset of `ℝ^n`, so its inclusion is a smooth embedding.
    simpa using (Manifold.IsSmoothEmbedding.of_opens V)
  have hιV :
      ContMDiff
        (𝓡 m)
        (𝓡 n)
        ∞
        ιV := by
    -- First regard the patch inclusion as an ambient map to `ℝ^n`, then codomain-restrict it to
    -- the open source `V`.
    exact
      smoothEmbedding_contMDiffCodRestrictInfty
        (I := 𝓡 n) (J := 𝓡 n) hOpenEmbedding
        (F := fun x : sliceChartSourcePatch (n := n) (m := m) (M := M) x0 hSlice ↦
          ((x : M) : EuclideanSpace ℝ (Fin n)))
        (sliceChartSourcePatchAmbientInclusion_contMDiff
          (n := n) (m := m) (M := M) x0 hSlice)
        (fun x ↦ x.2)
  -- Compose the ambient derivative field on `V` with the smooth inclusion of the slice patch.
  simpa [ιV, V, e, Φ, Function.comp] using
    (sliceTailDerivativeField_contMDiff (n := n) (m := m) (M := M) x0 hSlice hmn).comp hιV

/-- Helper for Proposition 6.25: the derivative field of a local defining map is smooth on the
corresponding open patch of the embedded submanifold `M`. -/
lemma localDefiningMapDerivativeField_onPatch_contMDiff
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - m))}
    (hDef : IsLocalDefiningMapOn (𝓡 n) (𝓡 (n - m)) M U Φ) :
    ContMDiff
      (𝓡 m)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - m)))
      ∞
      (fun x :
        ambientOpenPatchInSubmanifold (n := n) (M := M) U hDef.isOpen_source ↦
          fderiv ℝ Φ ((x : M) : EuclideanSpace ℝ (Fin n))) := by
  let P : TopologicalSpace.Opens M :=
    ambientOpenPatchInSubmanifold (n := n) (M := M) U hDef.isOpen_source
  let Uo : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) := ⟨U, hDef.isOpen_source⟩
  let ιU : P → Uo :=
    Set.codRestrict
      (fun x : P ↦ ((x : M) : EuclideanSpace ℝ (Fin n)))
      Uo
      (fun x ↦ by
        change (((x : P) : M) : EuclideanSpace ℝ (Fin n)) ∈ U
        exact x.2)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) Uo := inferInstance
  let _ : IsManifold (𝓡 n) ∞ Uo := inferInstance
  have hOpenEmbedding :
      IsSmoothEmbedding (𝓡 n) (𝓡 n) ∞
        (Subtype.val : Uo → EuclideanSpace ℝ (Fin n)) := by
    -- The ambient open source of a local defining map is an open subset of `ℝ^n`.
    simpa using (Manifold.IsSmoothEmbedding.of_opens Uo)
  have hιU :
      ContMDiff
        (𝓡 m)
        (𝓡 n)
        ∞
        ιU := by
    -- Codomain-restrict the ambient inclusion of `M` to the ambient open source `U`.
    exact
      smoothEmbedding_contMDiffCodRestrictInfty
        (I := 𝓡 n) (J := 𝓡 n) hOpenEmbedding
        (F := fun x : P ↦ ((x : M) : EuclideanSpace ℝ (Fin n)))
        (subtype_val_contMDiff.comp
          (contMDiff_subtype_val : ContMDiff (𝓡 m) (𝓡 m) ∞ (Subtype.val : P → M)))
        (fun x ↦ by
          change (((x : P) : M) : EuclideanSpace ℝ (Fin n)) ∈ U
          exact x.2)
  have hAmbient :
      ContMDiff
        (𝓡 n)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - m)))
        ∞
        (fun x : Uo ↦ fderiv ℝ Φ x.1) := by
    intro x
    have hx' := (contMDiffAt_subtype_iff
        (I := 𝓡 n)
        (I' := 𝓘(ℝ,
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - m))))
        (U := Uo)
        (f := fun y : EuclideanSpace ℝ (Fin n) ↦ fderiv ℝ Φ y)
        (x := x)).2 <| by
          rw [contMDiffAt_iff_contDiffAt]
          have hΦAtManifold :
              ContMDiffAt (𝓡 n) (𝓡 (n - m)) ∞ Φ x.1 := by
            -- The ambient source is open, so smoothness on it upgrades to smoothness at the point.
            exact (hDef.smoothOn x.1 x.2).contMDiffAt (Uo.2.mem_nhds x.2)
          have hΦAt :
              ContDiffAt ℝ ∞ Φ x.1 := by
            -- Euclidean manifold smoothness and ordinary smoothness agree.
            rw [← contMDiffAt_iff_contDiffAt]
            exact hΦAtManifold
          let F :
              EuclideanSpace ℝ (Fin n) →
                EuclideanSpace ℝ (Fin n) →
                  EuclideanSpace ℝ (Fin (n - m)) :=
            fun _ y ↦ Φ y
          have hF :
              ContDiffAt ℝ ∞ (Function.uncurry F) (x.1, x.1) := by
            -- Regard `Φ` as constant in the first variable and differentiate in the second slot.
            simpa [F, Function.comp] using hΦAt.comp (x.1, x.1) contDiffAt_snd
          -- `ContDiffAt.fderiv` produces the smooth derivative field in fixed Euclidean
          -- coordinates.
          simpa [F] using
            (ContDiffAt.fderiv
              (x₀ := x.1)
              (f := F)
              (g := fun y : EuclideanSpace ℝ (Fin n) ↦ y)
              hF
              contDiffAt_id
              (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞))
    simpa using hx'
  -- Restrict the ambient derivative field to the open patch of `M`.
  simpa [P, Uo, ιU, ambientOpenPatchInSubmanifold, Function.comp] using hAmbient.comp hιU

/-- Helper for Proposition 6.25: on the open patch cut out by a local defining map, a Euclidean
vector lies in the normal space exactly when it is orthogonal to the kernel of the Euclidean
derivative of that defining map. -/
lemma normalSpace_iff_mem_orthogonalKer_localDefiningMap
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - m))}
    (hDef : IsLocalDefiningMapOn (𝓡 n) (𝓡 (n - m)) M U Φ)
    (x :
      ambientOpenPatchInSubmanifold (n := n) (M := M) U hDef.isOpen_source)
    (v : EuclideanSpace ℝ (Fin n)) :
    (((NormedSpace.fromTangentSpace
        ((x : M) : EuclideanSpace ℝ (Fin n))).symm v) :
      TangentSpace (𝓡 n) (((x : M) : EuclideanSpace ℝ (Fin n)))) ∈
        N[n, m; M; (x : M)] ↔
      v ∈ ((fderiv ℝ Φ ((x : M) : EuclideanSpace ℝ (Fin n))).toLinearMap.ker)ᗮ := by
  let e :
      TangentSpace (𝓡 n) (((x : M) : EuclideanSpace ℝ (Fin n))) ≃L[ℝ]
        EuclideanSpace ℝ (Fin n) :=
    NormedSpace.fromTangentSpace
      (((x : M) : EuclideanSpace ℝ (Fin n)))
  have hSubtype :
      IsSmoothEmbedding
        (𝓡 m)
        (𝓡 n)
        ∞
        (Subtype.val : M → EuclideanSpace ℝ (Fin n)) :=
    subtypeVal_isSmoothEmbedding (n := n) (m := m) (M := M)
  have hTangent :
      T[𝓡 m; (x : M)] =
        (mfderiv
          (𝓡 n)
          (𝓡 (n - m))
          Φ
          (((x : M) : EuclideanSpace ℝ (Fin n)))).ker := by
    simpa using
      tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn
        hSubtype hDef (x : M) x.2
  constructor
  · intro hv
    rw [Submodule.mem_orthogonal']
    intro z hz
    have hz0 :
        fderiv ℝ Φ (((x : M) : EuclideanSpace ℝ (Fin n))) z = 0 :=
      LinearMap.mem_ker.mp hz
    have hzTangent :
        (e.symm z :
          TangentSpace (𝓡 n) (((x : M) : EuclideanSpace ℝ (Fin n)))) ∈
            T[𝓡 m; (x : M)] := by
      rw [hTangent]
      apply LinearMap.mem_ker.2
      have hzFixed :
          fixedModelMfderiv (n := n) (M := M) Φ (x : M) z = 0 := by
        -- Compare the Euclideanized manifold derivative with the ordinary Fréchet derivative.
        have hEq :=
          congrArg
            (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n - m)) ↦ A z)
            (fixedModelMfderiv_eq_fderivOnModel
              (n := n) (M := M) (k := n - m) Φ (x : M))
        simpa [hz0] using hEq
      exact
        (NormedSpace.fromTangentSpace
          (Φ (((x : M) : EuclideanSpace ℝ (Fin n))))).injective <| by
            simpa [fixedModelMfderiv] using hzFixed
    -- Apply the normal-space orthogonality criterion to the pulled-back kernel vector.
    exact
      (mem_normal_space_iff (n := n) (m := m) (M := M) (x := (x : M))
        (((NormedSpace.fromTangentSpace
          (((x : M) : EuclideanSpace ℝ (Fin n)))).symm v) :
          TangentSpace (𝓡 n) (((x : M) : EuclideanSpace ℝ (Fin n))))).1 hv
        (e.symm z) hzTangent
  · intro hv
    rw [mem_normal_space_iff]
    intro w hw
    have hw0 :
        mfderiv
          (𝓡 n)
          (𝓡 (n - m))
          Φ
          (((x : M) : EuclideanSpace ℝ (Fin n))) w = 0 := by
      rw [hTangent] at hw
      exact LinearMap.mem_ker.mp hw
    have hwKer :
        e w ∈ ((fderiv ℝ Φ (((x : M) : EuclideanSpace ℝ (Fin n)))).toLinearMap.ker) := by
      apply LinearMap.mem_ker.2
      have hw0' :
          fderiv ℝ Φ (((x : M) : EuclideanSpace ℝ (Fin n))) w = 0 := by
        simpa [mfderiv_eq_fderiv] using hw0
      have hwFixed :
          fixedModelMfderiv (n := n) (M := M) Φ (x : M) (e w) = 0 := by
        -- The fixed-model derivative sends the Euclidean representative of a tangent-kernel vector
        -- to zero because the manifold derivative already vanishes on `w`.
        simpa [fixedModelMfderiv, e.symm_apply_apply, hw0']
      -- Compare the Euclidean derivative with the fixed-model derivative at the same vector.
      rw [← fixedModelMfderiv_eq_fderivOnModel (n := n) (M := M) (k := n - m) Φ (x : M)]
      exact hwFixed
    -- The Euclidean derivative kernel is orthogonal to `v`, hence so is every tangent vector.
    rw [Submodule.mem_orthogonal'] at hv
    exact hv (e w) hwKer

/-- Helper for Proposition 6.25: applying the adjoint of the Euclidean derivative of a local
defining map produces a normal vector field on the corresponding open patch of `M`. -/
lemma ambientAdjointField_mem_normalSpace_of_localDefiningMap
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n - m))}
    (hDef : IsLocalDefiningMapOn (𝓡 n) (𝓡 (n - m)) M U Φ)
    (x :
      ambientOpenPatchInSubmanifold (n := n) (M := M) U hDef.isOpen_source)
    (c : EuclideanSpace ℝ (Fin (n - m))) :
    (((NormedSpace.fromTangentSpace
        ((x : M) : EuclideanSpace ℝ (Fin n))).symm
        (adjointApplyContinuousLinearMap c
          (fderiv ℝ Φ ((x : M) : EuclideanSpace ℝ (Fin n))))) :
      TangentSpace (𝓡 n) (((x : M) : EuclideanSpace ℝ (Fin n)))) ∈
        N[n, m; M; (x : M)] := by
  -- The adjoint image lies in the orthogonal complement of the derivative kernel, so the local
  -- defining-map normal-space criterion applies directly.
  refine
    (normalSpace_iff_mem_orthogonalKer_localDefiningMap
      (n := n) (m := m) (M := M) hDef x
      (adjointApplyContinuousLinearMap c
        (fderiv ℝ Φ ((x : M) : EuclideanSpace ℝ (Fin n))))).2 ?_
  simpa [adjointApplyContinuousLinearMap_apply] using
    show
      adjointApplyContinuousLinearMap c
          (fderiv ℝ Φ ((x : M) : EuclideanSpace ℝ (Fin n))) ∈
        (fderiv ℝ Φ ((x : M) : EuclideanSpace ℝ (Fin n))).kerᗮ by
      rw [ContinuousLinearMap.orthogonal_ker]
      exact subset_closure ⟨c, by simp [adjointApplyContinuousLinearMap_apply]⟩

/-- Helper for Proposition 6.25: a local defining map through `π_NM p` produces a local section of
the normal-bundle projection through `p` with smooth ambient product coordinates. -/
lemma piNM_hasProductSmoothLocalSectionThrough_of_localDefiningMap
    (p : NM[n, m; M]) :
    ∃ U : TopologicalSpace.Opens M, ∃ hpU : π_NM[n, m; M] p ∈ U, ∃ σ : U → NM[n, m; M],
      ContMDiff (𝓡 m) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M ∘ σ) ∧
        (∀ x : U, π_NM[n, m; M] (σ x) = x) ∧
        σ ⟨π_NM[n, m; M] p, hpU⟩ = p := by
  rcases
      embeddedSubmanifoldLocalDefiningMapAt
        (n := n) (m := m) (M := M) (π_NM[n, m; M] p) with
    ⟨hmn, U, Φ, hpU, hΦp, hDef⟩
  let Uo : TopologicalSpace.Opens M :=
    ambientOpenPatchInSubmanifold (n := n) (M := M) U hDef.isOpen_source
  let xU : Uo := ⟨π_NM[n, m; M] p, hpU⟩
  have hpNormal :
      (((NormedSpace.fromTangentSpace
          (((π_NM[n, m; M] p : M) : EuclideanSpace ℝ (Fin n)))).symm
          (normal_bundle_vector n m M p)) :
        TangentSpace (𝓡 n) (((π_NM[n, m; M] p : M) : EuclideanSpace ℝ (Fin n)))) ∈
          N[n, m; M; π_NM[n, m; M] p] := by
    -- The fiber component of `p` is already a vector in the normal space over its base point.
    simpa [normal_bundle_vector] using
      normal_bundle_vector_mem (n := n) (m := m) (M := M) p
  have hpKer :
      normal_bundle_vector n m M p ∈
        ((fderiv ℝ Φ
          (((π_NM[n, m; M] p : M) : EuclideanSpace ℝ (Fin n)))).toLinearMap.ker)ᗮ := by
    -- Convert the normal-bundle fiber condition into the orthogonal-kernel criterion provided by
    -- the local defining map through `π_NM p`.
    exact
      (normalSpace_iff_mem_orthogonalKer_localDefiningMap
        (n := n) (m := m) (M := M) hDef xU
        (normal_bundle_vector n m M p)).1 hpNormal
  rcases
      exists_eq_adjoint_of_mem_orthogonalKer
        (k := n - m) hpKer with
    ⟨c0, hc0⟩
  let η : Uo → EuclideanSpace ℝ (Fin n) := fun x ↦
    adjointApplyContinuousLinearMap c0
      (fderiv ℝ Φ ((x : M) : EuclideanSpace ℝ (Fin n)))
  have hηsmooth : ContMDiff (𝓡 m) (𝓡 n) ∞ η := by
    -- The adjoint-evaluation operator is continuous linear, so composing it with the smooth
    -- derivative field of the local defining map keeps the field smooth.
    simpa [η, Function.comp] using
      (adjointApplyContinuousLinearMap c0).contMDiff.comp
        (localDefiningMapDerivativeField_onPatch_contMDiff
          (n := n) (m := m) (M := M) hDef)
  have hηnormal :
      ∀ x : Uo,
        (((NormedSpace.fromTangentSpace
            ((x : M) : EuclideanSpace ℝ (Fin n))).symm (η x)) :
          TangentSpace (𝓡 n) (((x : M) : EuclideanSpace ℝ (Fin n)))) ∈
            N[n, m; M; (x : M)] := by
    intro x
    -- Each adjoint derivative value lands in the normal space by the local defining-map
    -- orthogonal-kernel characterization.
    exact
      ambientAdjointField_mem_normalSpace_of_localDefiningMap
        (n := n) (m := m) (M := M) hDef x c0
  have hηp : η xU = normal_bundle_vector n m M p := by
    -- At the base point `π_NM p`, the chosen adjoint coefficient recovers the original normal
    -- vector of `p`.
    simpa [η, xU, adjointApplyContinuousLinearMap_apply] using hc0
  rcases
      localSectionThrough_of_ambientNormalField
        (n := n) (m := m) (M := M) p
        (U := Uo) (hpU := xU.property) hηsmooth hηnormal hηp with
    ⟨σ, hσsmooth, hproj, hσp⟩
  exact ⟨Uo, xU.property, σ, hσsmooth, hproj, hσp⟩

/-- Helper for Proposition 6.25: a point of the normal bundle lies on a local section of
`π_NM[n, m; M]` whose ambient product coordinates are smooth near the chosen base point. -/
lemma piNM_hasProductSmoothLocalSectionThrough
    (p : NM[n, m; M]) :
    ∃ U : TopologicalSpace.Opens M, ∃ hpU : π_NM[n, m; M] p ∈ U, ∃ σ : U → NM[n, m; M],
      ContMDiff (𝓡 m) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M ∘ σ) ∧
        (∀ x : U, π_NM[n, m; M] (σ x) = x) ∧
        σ ⟨π_NM[n, m; M] p, hpU⟩ = p := by
  -- Route correction: the proof now goes through the local defining map at `π_NM p`, avoiding the
  -- blocked global slice-condition owner entirely.
  simpa using
    piNM_hasProductSmoothLocalSectionThrough_of_localDefiningMap
      (n := n) (m := m) (M := M) p

/-- Helper for Proposition 6.25: smoothness of `normal_bundle_toProd n m M ∘ σ` reflects back to
smoothness of `σ` for the chosen compatible smooth structure on `NM[n, m; M]`. -/
lemma contMDiff_of_contMDiffToProd [CompatibleSmoothStructure n m M]
    {U : TopologicalSpace.Opens M} {σ : U → NM[n, m; M]}
    (hσ :
      ContMDiff (𝓡 m) ((𝓡 n).prod (𝓡 n)) ∞ (normal_bundle_toProd n m M ∘ σ)) :
    ContMDiff (𝓡 m) (𝓡 n) ∞ σ := by
  have hEmbed :
      Manifold.IsSmoothEmbedding
        (𝓡 n)
        ((𝓡 n).prod (𝓡 n))
        (∞ : ℕ∞ω)
        (normal_bundle_toProd n m M) := by
    simpa using isSmoothEmbedding_normal_bundle_toProd (n := n) (m := m) (M := M)
  rcases smooth_embedding_range_has_induced_manifold_structure hEmbed with ⟨csR, hcsR⟩
  have hRange :
      ∃ hs : IsManifold (𝓡 n) (∞ : ℕ∞ω) (Set.range (normal_bundle_toProd n m M)),
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n))
            (Set.range (normal_bundle_toProd n m M)) := csR
        let _ : IsManifold (𝓡 n) (∞ : ℕ∞ω) (Set.range (normal_bundle_toProd n m M)) := hs
        Manifold.IsSmoothEmbedding
            (𝓡 n)
            ((𝓡 n).prod (𝓡 n))
            (∞ : ℕ∞ω)
            (Subtype.val : Set.range (normal_bundle_toProd n m M) →
              EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∧
          ∃ Φ : NM[n, m; M] ≃ₘ⟮𝓡 n, 𝓡 n⟯ Set.range (normal_bundle_toProd n m M),
            ∀ x, (Φ x : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =
              normal_bundle_toProd n m M x := by
    simpa [IsInducedImageManifoldStructure] using hcsR
  rcases hRange with ⟨hsR, hSubtypeR, Φ, hΦ⟩
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n))
      (Set.range (normal_bundle_toProd n m M)) := csR
  let _ : IsManifold (𝓡 n) ∞ (Set.range (normal_bundle_toProd n m M)) := hsR
  let γ : U → Set.range (normal_bundle_toProd n m M) :=
    Set.codRestrict (normal_bundle_toProd n m M ∘ σ) _ fun x ↦ ⟨σ x, rfl⟩
  have hγ :
      ContMDiff (𝓡 m) (𝓡 n) ∞ γ := by
    -- Move the ambient product smoothness to the embedded range of `normal_bundle_toProd`.
    simpa [γ] using
      (smoothEmbedding_contMDiffCodRestrictInfty
        (I := ((𝓡 n).prod (𝓡 n))) (J := 𝓡 n)
        hSubtypeR hσ (fun x ↦ ⟨σ x, rfl⟩))
  have hσeq : σ = Φ.symm ∘ γ := by
    funext x
    apply Φ.injective
    apply Subtype.ext
    simpa [γ, Function.comp] using hΦ (σ x)
  -- Pull the range-valued smooth map back to `NM[n, m; M]` through the embedding diffeomorphism.
  simpa [Function.comp, hσeq] using Φ.symm.contMDiff.comp hγ

/-- Helper: a point of the normal bundle lies on a smooth local section of `π_NM[n, m; M]`. -/
lemma piNM_hasSmoothLocalSectionThrough [CompatibleSmoothStructure n m M] (p : NM[n, m; M]) :
    ∃ U : TopologicalSpace.Opens M, ∃ hpU : π_NM[n, m; M] p ∈ U, ∃ σ : U → NM[n, m; M],
      Manifold.IsSmoothLocalSection (𝓡 n) (𝓡 m) (π_NM[n, m; M] : NM[n, m; M] → M) U σ ∧
        σ ⟨π_NM[n, m; M] p, hpU⟩ = p := by
  -- Route correction: first build the local section in ambient product coordinates, then reflect
  -- that smoothness through `normal_bundle_toProd`.
  obtain ⟨U, hpU, σ, hσ, hproj, hσp⟩ := piNM_hasProductSmoothLocalSectionThrough (p := p)
  have hσsmooth : ContMDiff (𝓡 m) (𝓡 n) ∞ σ := contMDiff_of_contMDiffToProd hσ
  -- `Manifold.IsSmoothLocalSection` is exactly smoothness together with the section equation.
  exact ⟨U, hpU, σ, ⟨hσsmooth, hproj⟩, hσp⟩

/-- Helper: the canonical projection `π_NM[n, m; M]` is a smooth submersion. -/
theorem piNM_isSmoothSubmersion [CompatibleSmoothStructure n m M] :
    IsSmoothSubmersion (𝓡 n) (𝓡 m) (π_NM[n, m; M] : NM[n, m; M] → M) := by
  -- The local-section criterion converts the bundle-section package into the submersion property.
  refine ⟨piNM_contMDiff, ?_⟩
  exact
    (Manifold.smooth_submersion_iff_exists_smooth_local_section_through_every_point
      piNM_contMDiff).2
      piNM_hasSmoothLocalSectionThrough

end NormalBundle

namespace NormalBundle.TubularNeighborhood

/-- The canonical map associated to a tubular neighborhood is the normal-bundle projection
transported across the inverse of the endpoint diffeomorphism. -/
def retraction (T : TubularNeighborhood n m M) : T.neighborhood → M := fun y ↦
  π_NM[n, m; M] (T.endpointDiffeomorph.symm y)

/-
The helper layer works with the local normal-bundle manifold structure already present in the
section context.
-/
/-- The canonical tubular retraction is given pointwise by the normal-bundle projection composed
with the inverse endpoint diffeomorphism. -/
@[simp] theorem retraction_apply (T : TubularNeighborhood n m M) (y : T.neighborhood) :
    T.retraction y = π_NM[n, m; M] (T.endpointDiffeomorph.symm y) :=
  rfl

/-- Helper for Proposition 6.25: after forgetting the subtype proof, the tubular retraction is a
smooth ambient Euclidean map under the compatible normal-bundle smooth structure. -/
lemma retraction_baseAmbient_contMDiff
    [CompatibleSmoothStructure n m M]
    (T : TubularNeighborhood n m M) :
    ContMDiff (𝓡 n) (𝓡 n) ∞
      (fun y : T.neighborhood ↦ ((T.retraction y : M) : EuclideanSpace ℝ (Fin n))) := by
  have hSymmAmbient :
      ContMDiff (𝓡 n) (𝓡 n) ∞
        (fun y : T.neighborhood ↦ ((T.endpointDiffeomorph.symm y : T.tube) : NM[n, m; M])) := by
    -- Forgetting the open-subtype proof turns the inverse endpoint diffeomorphism into an ambient
    -- normal-bundle map.
    change ContMDiff (𝓡 n) (𝓡 n) ∞ (Subtype.val ∘ T.endpointDiffeomorph.symm)
    simpa [Function.comp] using
      (contMDiff_subtype_val : ContMDiff (𝓡 n) (𝓡 n) ∞ (Subtype.val : T.tube → NM[n, m; M])).comp
        T.endpointDiffeomorph.contMDiff_invFun
  -- Compose the smooth ambient base-point coordinate with the inverse endpoint diffeomorphism.
  simpa [retraction_apply] using
    piNM_baseAmbient_contMDiff.comp hSymmAmbient

/-- Helper: the zero normal vector over `x` lies in the chosen tube. -/
lemma zeroVector_mem_tube (T : TubularNeighborhood n m M) (x : M) :
    Bundle.TotalSpace.mk x (0 : N[n, m; M; x]) ∈ (T.tube : Set (NM[n, m; M])) := by
  -- Rewrite the tube by its radius-slice description and use positivity of the radius function.
  rw [T.tube_eq]
  simpa [normal_bundle_vector] using T.δ_pos x

/-- Helper: the inverse endpoint diffeomorphism sends a base point of `M` to the zero vector over
that point. -/
lemma endpointDiffeomorph_symm_inclusion_eq_zeroVector (T : TubularNeighborhood n m M) (x : M) :
    T.endpointDiffeomorph.symm (Set.inclusion T.contains_base x) =
      ⟨Bundle.TotalSpace.mk x (0 : N[n, m; M; x]), zeroVector_mem_tube T x⟩ := by
  -- Compare the two candidate preimages after applying the endpoint diffeomorphism.
  apply T.endpointDiffeomorph.injective
  change
    T.endpointDiffeomorph (T.endpointDiffeomorph.symm (Set.inclusion T.contains_base x)) =
      T.endpointDiffeomorph ⟨Bundle.TotalSpace.mk x (0 : N[n, m; M; x]), zeroVector_mem_tube T x⟩
  rw [T.endpointDiffeomorph.apply_symm_apply]
  -- The endpoint map fixes the zero section, so both points are the same base point in `T`.
  ext
  rw [T.endpointDiffeomorph_eq]
  simp [NormalBundle.endpointMap, normal_bundle_vector]

/-- Helper: the canonical map associated to a tubular neighborhood is a retraction of the canonical
subset inclusion `M ↪ T.neighborhood`. -/
theorem retraction_leftInverse (T : TubularNeighborhood n m M) :
    Function.LeftInverse T.retraction (Set.inclusion T.contains_base) := by
  intro x
  -- Project the identified zero-vector preimage back to the original base point.
  have hzero :
      (T.endpointDiffeomorph.symm (Set.inclusion T.contains_base x) : NM[n, m; M]) =
        Bundle.TotalSpace.mk x (0 : N[n, m; M; x]) := by
    exact congrArg Subtype.val (endpointDiffeomorph_symm_inclusion_eq_zeroVector T x)
  simpa [retraction_apply] using congrArg Bundle.TotalSpace.proj hzero

/-- Helper for Proposition 6.25: the inclusion of the open tube into the ambient normal bundle is a
local diffeomorphism. -/
theorem tubeInclusion_isLocalDiffeomorph (T : TubularNeighborhood n m M) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ ((↑) : T.tube → NM[n, m; M]) := by
  -- The open-tube inclusion is an immersion, and both source and target use the same `n`-model.
  exact
    is_local_diffeomorph_of_is_immersion_of_eq_dim
      rfl
      (Manifold.IsSmoothEmbedding.of_opens T.tube).isImmersion

/-- Helper: the normal-bundle projection remains a smooth submersion after restricting its domain
to the open tube of a tubular neighborhood. -/
theorem tubeProjection_isSmoothSubmersion [CompatibleSmoothStructure n m M]
    (T : TubularNeighborhood n m M) :
    IsSmoothSubmersion (𝓡 n) (𝓡 m) (fun p : T.tube ↦ π_NM[n, m; M] p) := by
  -- Restricting the source along an open inclusion preserves the submersion property.
  simpa [Function.comp] using
    (Manifold.IsSmoothSubmersion.comp_isLocalDiffeomorph
      NormalBundle.piNM_isSmoothSubmersion
      (tubeInclusion_isLocalDiffeomorph T))

/-- Helper: the canonical map associated to a tubular neighborhood is a smooth submersion. -/
theorem retraction_isSmoothSubmersion [CompatibleSmoothStructure n m M]
    (T : TubularNeighborhood n m M) :
    IsSmoothSubmersion (𝓡 n) (𝓡 m) T.retraction := by
  -- Transport the restricted smooth-submersion property across the inverse endpoint diffeomorphism.
  have h_symm : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ T.endpointDiffeomorph.symm := by
    simpa using Diffeomorph.isLocalDiffeomorph T.endpointDiffeomorph.symm
  simpa [retraction_apply, Function.comp] using
    (Manifold.IsSmoothSubmersion.comp_isLocalDiffeomorph
      (NormalBundle.TubularNeighborhood.tubeProjection_isSmoothSubmersion
        (n := n) (m := m) (M := M) T)
      h_symm)

end NormalBundle.TubularNeighborhood

end TubularNeighborhoodRetraction

section TubularNeighborhoodRetractionCanonical

variable {n m : ℕ}
variable {M : Set (EuclideanSpace ℝ (Fin n))}
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
variable [IsManifold (𝓡 m) ∞ M]
variable [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
variable [IsManifold (𝓡 n) ∞ (NM[n, m; M])]

-- Semantic recall note: `lean_leansearch` only surfaced generic bundle-projection smoothness
-- results. The helper lemmas therefore remain polymorphic in `CompatibleSmoothStructure`, while a
-- tubular neighborhood itself supplies the needed compatibility witness via
-- `T.compatibleSmoothStructure`.
/-- Proposition 6.25. Let `M ⊆ ℝ^n` be an embedded submanifold. If `T` is any tubular
neighborhood of `M`, there exists a smooth map `r : T.neighborhood → M` that is both a retraction
and a smooth submersion. -/
theorem tubular_neighborhood_exists_retraction_and_smooth_submersion
    : ∀ T : NormalBundle.TubularNeighborhood n m M,
      ∃ r : T.neighborhood → M,
        Function.LeftInverse r (Set.inclusion T.contains_base) ∧
          IsSmoothSubmersion (𝓡 n) (𝓡 m) r := by
  intro T
  let _ : NormalBundle.CompatibleSmoothStructure n m M := T.compatibleSmoothStructure
  -- Package the canonical tubular retraction together with its two defining properties.
  refine ⟨T.retraction, NormalBundle.TubularNeighborhood.retraction_leftInverse T, ?_⟩
  simpa using NormalBundle.TubularNeighborhood.retraction_isSmoothSubmersion T

/-- Helper for Proposition 6.25: any tubular neighborhood comes with a canonical retraction that is
both a retraction and a smooth submersion. -/
theorem tubular_neighborhood_has_retraction_and_smooth_submersion
    : ∀ T : NormalBundle.TubularNeighborhood n m M,
      Function.LeftInverse T.retraction (Set.inclusion T.contains_base) ∧
        IsSmoothSubmersion (𝓡 n) (𝓡 m) T.retraction := by
  intro T
  let _ : NormalBundle.CompatibleSmoothStructure n m M := T.compatibleSmoothStructure
  -- Reuse the canonical tubular retraction supplied by the neighborhood data.
  exact ⟨NormalBundle.TubularNeighborhood.retraction_leftInverse T,
    NormalBundle.TubularNeighborhood.retraction_isSmoothSubmersion T⟩

end TubularNeighborhoodRetractionCanonical

end
