import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import LeeSmoothLib.Ch01.Sec01.Definition_1_extra_1
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_25.Theorem_4_29
import LeeSmoothLib.Ch05.Sec05_31.Definition_5_31_extra_1
import LeeSmoothLib.Ch05.Sec05_28.Proposition_5_2
import LeeSmoothLib.Ch05.Sec05_31.Proposition_5_18
import LeeSmoothLib.Ch05.Sec05_31.Proposition_5_21
import LeeSmoothLib.Ch05.Sec05_33.Theorem_5_32
import LeeSmoothLib.Ch05.Sec05_33.Theorem_5_31
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch05.Sec05_36.Proposition_5_49
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold Set

-- Semantic search note: `lean_leansearch` surfaced only general graph/projection lemmas, while
-- the current-repository precedent `Corollary_6_33` already states the local graph criterion on
-- `Manifold.ImmersedSubmanifold`, so this file uses that owner directly.

section GlobalCharacterizationOfGraphs

universe uEM uEN uHM uHN uM uN

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {I : ModelWithCorners ℝ EM HM} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ EN HN} [IsManifold J ∞ N]

/-- The restriction of the first projection `π_M : M × N → M` to an immersed submanifold of
`M × N`. -/
def graphFirstProjection
    (S : ImmersedSubmanifold (I.prod J) (M × N)) : S → M :=
  fun x ↦ (S.inclusion x).1

/-- The restriction of the second projection `π_N : M × N → N` to an immersed submanifold of
`M × N`. -/
def graphSecondProjection
    (S : ImmersedSubmanifold (I.prod J) (M × N)) : S → N :=
  fun x ↦ (S.inclusion x).2

/-- The canonical vertical-slice parametrization `N → M × N`, `y ↦ (p, y)`. -/
def verticalSliceMap (p : M) : N → M × N :=
  fun y ↦ (p, y)

/-- Helper for Theorem 6.32: the ambient graph parametrization `p ↦ (p, f p)`. -/
def ambientGraphMap (f : M → N) : M → M × N :=
  fun p ↦ (p, f p)

/-- An immersed submanifold of `M × N` is the graph of a smooth map `f : M → N` when the
underlying ambient subset of `S` is exactly the graph of `f`, and the graph parametrization
gives a smooth identification of `M` with `S`. -/
def IsGraphOfMap
    (S : ImmersedSubmanifold (I.prod J) (M × N)) (f : M → N) : Prop :=
  ContMDiff I J ∞ f ∧
    S.carrier = Set.range (fun p : M ↦ (p, f p)) ∧
      ∃ ψ : M → S,
        ContMDiff I (modelWithCornersSelf ℝ S.ModelSpace) ∞ ψ ∧
          Function.LeftInverse ψ (graphFirstProjection S) ∧
          Function.RightInverse ψ (graphFirstProjection S) ∧
            ∀ p : M, S.inclusion (ψ p) = ambientGraphMap f p

/-- An immersed submanifold of `M × N` is the graph of some smooth map `f : M → N` in the source
sense that its ambient carrier is the graph of `f`. -/
def IsGraphOfSmoothMap
    (S : ImmersedSubmanifold (I.prod J) (M × N)) : Prop :=
  ∃ f : M → N, IsGraphOfMap S f

/-- The restricted first projection `π_M|_S : S → M` is a diffeomorphism onto `M`. -/
def FirstProjectionRestrictionIsDiffeomorph
    (S : ImmersedSubmanifold (I.prod J) (M × N)) : Prop :=
  ContMDiff (modelWithCornersSelf ℝ S.ModelSpace) I ∞ (graphFirstProjection S) ∧
    ∃ ψ : M → S,
      ContMDiff I (modelWithCornersSelf ℝ S.ModelSpace) ∞ ψ ∧
        Function.LeftInverse ψ (graphFirstProjection S) ∧
        Function.RightInverse ψ (graphFirstProjection S)

/-- The vertical slice `{p} × N` meets the immersed submanifold `S` transversely at `x`. -/
def verticalSliceMeetsTransverselyAt
    (S : ImmersedSubmanifold (I.prod J) (M × N)) (x : S) : Prop :=
  (mfderiv J (I.prod J) (verticalSliceMap ((S.inclusion x).1)) ((S.inclusion x).2)).range ⊔
    (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) (I.prod J) S.inclusion x).range = ⊤

/-- Every vertical slice `{p} × N` meets `S` in exactly one point, and every such intersection is
transverse. -/
def HasUniqueTransverseVerticalSliceIntersections
    (S : ImmersedSubmanifold (I.prod J) (M × N)) : Prop :=
  ∀ p : M,
    (∃! x : S, graphFirstProjection S x = p) ∧
      ∀ x : S, graphFirstProjection S x = p → verticalSliceMeetsTransverselyAt S x

/-- A chosen inverse to the restricted first projection `π_M|_S : S → M` coming from a
`FirstProjectionRestrictionIsDiffeomorph` witness. The companion theorems record the smoothness
and inverse properties of this chosen map. -/
noncomputable def restrictedFirstProjectionInverse
    (S : ImmersedSubmanifold (I.prod J) (M × N))
    (h : FirstProjectionRestrictionIsDiffeomorph S) : M → S :=
  Classical.choose h.2

/-- The chosen inverse to `π_M|_S` is smooth. -/
theorem restrictedFirstProjectionInverse_contMDiff
    (S : ImmersedSubmanifold (I.prod J) (M × N))
    (h : FirstProjectionRestrictionIsDiffeomorph S) :
    ContMDiff I (modelWithCornersSelf ℝ S.ModelSpace) ∞
      (restrictedFirstProjectionInverse S h) := by
  -- Read the smoothness field directly from the witness chosen out of `h`.
  simpa [restrictedFirstProjectionInverse] using (Classical.choose_spec h.2).1

/-- The chosen inverse to `π_M|_S` is a left inverse to the restricted first projection. -/
theorem restrictedFirstProjectionInverse_leftInverse
    (S : ImmersedSubmanifold (I.prod J) (M × N))
    (h : FirstProjectionRestrictionIsDiffeomorph S) :
    Function.LeftInverse (restrictedFirstProjectionInverse S h) (graphFirstProjection S) := by
  -- The chosen inverse carries the left-inverse law recorded in the witness.
  simpa [restrictedFirstProjectionInverse] using (Classical.choose_spec h.2).2.1

/-- The chosen inverse to `π_M|_S` is a right inverse to the restricted first projection. -/
theorem restrictedFirstProjectionInverse_rightInverse
    (S : ImmersedSubmanifold (I.prod J) (M × N))
    (h : FirstProjectionRestrictionIsDiffeomorph S) :
    Function.RightInverse (restrictedFirstProjectionInverse S h) (graphFirstProjection S) := by
  -- The same witness also records the right-inverse law.
  simpa [restrictedFirstProjectionInverse] using (Classical.choose_spec h.2).2.2

/-- The canonical map `M → N` obtained from the inverse of `π_M|_S` when that restricted first
projection is a diffeomorphism. -/
noncomputable def graphingMapOfRestrictedFirstProjection
    (S : ImmersedSubmanifold (I.prod J) (M × N))
    (h : FirstProjectionRestrictionIsDiffeomorph S) : M → N :=
  graphSecondProjection S ∘ restrictedFirstProjectionInverse S h

/-- Helper for Theorem 6.32: the restricted first projection of an immersed submanifold is
smooth. -/
theorem graphFirstProjection_contMDiff
    (S : ImmersedSubmanifold (I.prod J) (M × N)) :
    ContMDiff (modelWithCornersSelf ℝ S.ModelSpace) I ∞ (graphFirstProjection S) := by
  -- Route correction: view the restricted first projection as `Prod.fst ∘ S.inclusion` and read
  -- smoothness from the ambient projection together with the immersed-submanifold inclusion.
  simpa [graphFirstProjection, Function.comp] using
    (contMDiff_fst.comp (ImmersedSubmanifold.inclusion_isImmersion_smooth S).contMDiff)

/-- Helper for Theorem 6.32: the restricted second projection of an immersed submanifold is
smooth. -/
theorem graphSecondProjection_contMDiff
    (S : ImmersedSubmanifold (I.prod J) (M × N)) :
    ContMDiff (modelWithCornersSelf ℝ S.ModelSpace) J ∞ (graphSecondProjection S) := by
  -- The same normalization identifies the restricted second projection with
  -- `Prod.snd ∘ S.inclusion`.
  simpa [graphSecondProjection, Function.comp] using
    (contMDiff_snd.comp (ImmersedSubmanifold.inclusion_isImmersion_smooth S).contMDiff)

/-- Helper for Theorem 6.32: the derivative of the restricted first projection is the first-factor
projection after the derivative of the inclusion. -/
theorem graphFirstProjection_mfderiv_eq_fst_comp
    (S : ImmersedSubmanifold (I.prod J) (M × N)) (x : S) :
    mfderiv (modelWithCornersSelf ℝ S.ModelSpace) I (graphFirstProjection S) x =
      (ContinuousLinearMap.fst ℝ
        (TangentSpace I (graphFirstProjection S x))
        (TangentSpace J (graphSecondProjection S x))).comp
        (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) (I.prod J) S.inclusion x) := by
  -- Freeze the chain-rule normal form once so later transversality proofs only rewrite through it.
  have hg := ((contMDiff_fst.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).hasMFDerivAt :
    HasMFDerivAt (I.prod J) I Prod.fst (S.inclusion x)
      (mfderiv (I.prod J) I Prod.fst (S.inclusion x)))
  have hf :
      HasMFDerivAt (modelWithCornersSelf ℝ S.ModelSpace) (I.prod J) S.inclusion x
        (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) (I.prod J) S.inclusion x) :=
    (((ImmersedSubmanifold.inclusion_isImmersion_smooth S).contMDiff.mdifferentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)).hasMFDerivAt)
  simpa [graphFirstProjection, graphSecondProjection, Function.comp] using
    (HasMFDerivAt.comp x hg hf).mfderiv

/-- Helper for Theorem 6.32: a smooth inverse to the restricted first projection packages the
canonical graph structure. -/
theorem graphingMapOfRestrictedFirstProjection_contMDiff
    (S : ImmersedSubmanifold (I.prod J) (M × N))
    (h : FirstProjectionRestrictionIsDiffeomorph S) :
    ContMDiff I J ∞ (graphingMapOfRestrictedFirstProjection S h) := by
  -- The canonical graphing map is the second projection after the chosen smooth inverse.
  simpa [graphingMapOfRestrictedFirstProjection, Function.comp] using
    (graphSecondProjection_contMDiff S).comp
      (restrictedFirstProjectionInverse_contMDiff S h)

/-- Helper for Theorem 6.32: a smooth inverse to the restricted first projection packages the
canonical graph structure. -/
theorem isGraphOfMap_of_firstProjectionRestrictionIsDiffeomorph
    (S : ImmersedSubmanifold (I.prod J) (M × N))
    (h : FirstProjectionRestrictionIsDiffeomorph S) :
    IsGraphOfMap S (graphingMapOfRestrictedFirstProjection S h) := by
  refine ⟨graphingMapOfRestrictedFirstProjection_contMDiff S h, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro z hz
      rcases hz with ⟨x, rfl⟩
      -- Every point of `S` is reconstructed from its first coordinate using the chosen inverse.
      refine ⟨graphFirstProjection S x, ?_⟩
      calc
        (graphFirstProjection S x,
            graphingMapOfRestrictedFirstProjection S h (graphFirstProjection S x)) =
            S.inclusion
              (restrictedFirstProjectionInverse S h (graphFirstProjection S x)) := by
                apply Prod.ext
                · simpa [graphFirstProjection] using
                    (restrictedFirstProjectionInverse_rightInverse S h
                      (graphFirstProjection S x)).symm
                · rfl
        _ = S.inclusion x := by
          rw [restrictedFirstProjectionInverse_leftInverse S h x]
    · intro z hz
      rcases hz with ⟨p, rfl⟩
      -- Conversely the canonical graph point is literally the inclusion of the chosen inverse.
      refine ⟨restrictedFirstProjectionInverse S h p, ?_⟩
      apply Prod.ext
      · simpa [graphFirstProjection] using restrictedFirstProjectionInverse_rightInverse S h p
      · rfl
  refine ⟨restrictedFirstProjectionInverse S h, restrictedFirstProjectionInverse_contMDiff S h,
    restrictedFirstProjectionInverse_leftInverse S h,
    restrictedFirstProjectionInverse_rightInverse S h, ?_⟩
  intro p
  apply Prod.ext
  · simpa [graphFirstProjection] using restrictedFirstProjectionInverse_rightInverse S h p
  · rfl

/-- Helper for Theorem 6.32: the ambient graph parametrization is smooth whenever `f` is. -/
theorem ambientGraphMap_contMDiff {f : M → N} (hf : ContMDiff I J ∞ f) :
    ContMDiff I (I.prod J) ∞ (ambientGraphMap f) := by
  -- The ambient graph map is the product of the identity on `M` with the smooth map `f`.
  simpa [ambientGraphMap] using contMDiff_id.prodMk hf

/-- Helper for Theorem 6.32: the ambient graph parametrization is a topological embedding. -/
theorem ambientGraphMap_isEmbedding {f : M → N} (hf : ContMDiff I J ∞ f) :
    Topology.IsEmbedding (ambientGraphMap f) := by
  -- The first projection is a continuous left inverse to the graph map.
  have hLeft : Function.LeftInverse Prod.fst (ambientGraphMap f) := by
    intro p
    rfl
  exact hLeft.isEmbedding continuous_fst ((continuous_id).prodMk hf.continuous)

/-- Helper for Theorem 6.32: the ambient graph parametrization is a smooth immersion. -/
theorem ambientGraphMap_isImmersion {f : M → N} (hf : ContMDiff I J ∞ f) :
    IsImmersion I (I.prod J) ∞ (ambientGraphMap f) := by
  have hΓ_cont : ContMDiff I (I.prod J) ∞ (ambientGraphMap f) :=
    ambientGraphMap_contMDiff hf
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hΓ_cont).2 ?_
  intro p u w huw
  have hDeriv :
      mfderiv I (I.prod J) (ambientGraphMap f) p =
        (mfderiv I I (fun x : M ↦ x) p).prod (mfderiv I J f p) := by
    -- The graph derivative is the product of the identity derivative and the derivative of `f`.
    simpa [ambientGraphMap] using
      (mfderiv_prodMk mdifferentiableAt_id
        (hf.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)) :
        mfderiv I (I.prod J) (fun x : M ↦ ((fun y : M ↦ y) x, f x)) p =
          (mfderiv I I (fun x : M ↦ x) p).prod (mfderiv I J f p))
  have hFirst :
      ((mfderiv I (I.prod J) (ambientGraphMap f) p) u).1 =
        ((mfderiv I (I.prod J) (ambientGraphMap f) p) w).1 := by
    exact congrArg Prod.fst huw
  -- The first component of the product derivative is exactly the identity tangent map.
  have hId :
      (mfderiv I I (fun x : M ↦ x) p) u =
        (mfderiv I I (fun x : M ↦ x) p) w := by
    simpa [hDeriv] using hFirst
  have hId' :
      (mfderiv I I (@id M) p) u =
        (mfderiv I I (@id M) p) w := by
    simpa only using hId
  simpa [mfderiv_id] using hId'

/-- Helper for Theorem 6.32: the ambient graph parametrization is a smooth embedding. -/
theorem ambientGraphMap_isSmoothEmbedding {f : M → N} (hf : ContMDiff I J ∞ f) :
    Manifold.IsSmoothEmbedding I (I.prod J) ∞ (ambientGraphMap f) := by
  -- Package the already-proved immersion and embedding parts into the owner predicate.
  exact ⟨ambientGraphMap_isImmersion hf, ambientGraphMap_isEmbedding hf⟩

/-- Helper for Theorem 6.32: the carrier of `S` is the range of the ambient graph parametrization
for the graphing map `f`. -/
theorem carrier_eq_range_ambientGraphMap
    (S : ImmersedSubmanifold (I.prod J) (M × N)) {f : M → N}
    (hgraph : IsGraphOfMap S f) :
    S.carrier = Set.range (ambientGraphMap f) := by
  -- This is just the graph condition rewritten with the canonical ambient graph-map helper.
  simpa [ambientGraphMap] using hgraph.2.1

/-- Helper for Theorem 6.32: in the graph case, the immersed-submanifold inclusion factors through
the canonical ambient graph map and the restricted first projection. -/
theorem inclusion_eq_ambientGraphMap_comp_graphFirstProjection
    (S : ImmersedSubmanifold (I.prod J) (M × N)) {f : M → N}
    (hgraph : IsGraphOfMap S f) :
    S.inclusion = ambientGraphMap f ∘ graphFirstProjection S := by
  funext x
  -- Any point of `S` lies on the ambient graph of `f`, so its two coordinates are determined by
  -- the first projection and the graph equation.
  have hx : S.inclusion x ∈ Set.range (ambientGraphMap f) := by
    rw [← carrier_eq_range_ambientGraphMap S hgraph]
    exact ⟨x, rfl⟩
  rcases hx with ⟨p, hp⟩
  have hpFst : p = graphFirstProjection S x := by
    simpa [graphFirstProjection] using congrArg Prod.fst hp
  subst p
  exact hp.symm

/-- Helper for Theorem 6.32: in the graph case, the derivative of the restricted first projection
is injective because differentiating the inclusion factorization recovers the already-immersive
ambient inclusion. -/
theorem graphFirstProjection_mfderiv_injective_of_isGraphOfMap
    (S : ImmersedSubmanifold (I.prod J) (M × N)) {f : M → N}
    (hgraph : IsGraphOfMap S f) (x : S) [FiniteDimensional ℝ S.ModelSpace] :
    Function.Injective
      (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) I (graphFirstProjection S) x) := by
  have hInclInj :
      Function.Injective
        (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) (I.prod J) S.inclusion x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv
      (ImmersedSubmanifold.inclusion_isImmersion_smooth S).contMDiff).1
      (ImmersedSubmanifold.inclusion_isImmersion_smooth S) x
  have hGraphProjDiff :
      MDifferentiableAt (modelWithCornersSelf ℝ S.ModelSpace) I (graphFirstProjection S) x :=
    (graphFirstProjection_contMDiff S).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hAmbientGraphDiff :
      MDifferentiableAt I (I.prod J) (ambientGraphMap f) (graphFirstProjection S x) :=
    (ambientGraphMap_contMDiff hgraph.1).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hcomp :
      mfderiv (modelWithCornersSelf ℝ S.ModelSpace) (I.prod J) S.inclusion x =
        (mfderiv I (I.prod J) (ambientGraphMap f) (graphFirstProjection S x)).comp
          (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) I (graphFirstProjection S) x) := by
    -- Differentiate the normalized factorization `S.inclusion = ambientGraphMap f ∘ π_M|_S`.
    rw [inclusion_eq_ambientGraphMap_comp_graphFirstProjection S hgraph]
    simpa [Function.comp] using
      (mfderiv_comp x hAmbientGraphDiff hGraphProjDiff)
  intro u v huv
  -- Apply injectivity of the inclusion derivative after rewriting it through
  -- the graph factorization.
  apply hInclInj
  rw [hcomp]
  change
    (mfderiv I (I.prod J) (ambientGraphMap f) (graphFirstProjection S x))
        ((mfderiv (modelWithCornersSelf ℝ S.ModelSpace) I (graphFirstProjection S) x) u) =
      (mfderiv I (I.prod J) (ambientGraphMap f) (graphFirstProjection S x))
        ((mfderiv (modelWithCornersSelf ℝ S.ModelSpace) I (graphFirstProjection S) x) v)
  rw [huv]

-- Theorem 6.32 (1) is proved just below after isolating the converse `(a) → (b)` direction.
/-- Helper for Theorem 6.32: if an immersed submanifold is the graph of a smooth map, then the
restricted first projection has the expected point-set inverse; the only remaining work is to
transport smoothness of that inverse through the graph identification. -/
  theorem firstProjectionRestrictionIsDiffeomorph_of_isGraphOfMap
    [BoundarylessManifold I M]
    (S : ImmersedSubmanifold (I.prod J) (M × N)) {f : M → N}
    (hgraph : IsGraphOfMap S f) :
    FirstProjectionRestrictionIsDiffeomorph S := by
  rcases hgraph.2.2 with ⟨ψ, hψ_contMDiff, hψ_left, hψ_right, hψ_graph⟩
  -- The graph witness already records the smooth inverse and the two inverse laws for `π_M|_S`.
  exact ⟨graphFirstProjection_contMDiff S, ψ, hψ_contMDiff, hψ_left, hψ_right⟩

/-- Theorem 6.32 (1) (Global Characterization of Graphs): if `S` is an immersed submanifold of
`M × N`, then condition `(a)` that `S` is the graph of a smooth map `f : M → N` is equivalent to
condition `(b)` that the restricted first projection `π_M|_S : S → M` is a diffeomorphism. -/
theorem graphCondition_iff_restrictedFirstProjection_diffeomorph
    [BoundarylessManifold I M]
    (S : ImmersedSubmanifold (I.prod J) (M × N)) :
    IsGraphOfSmoothMap S ↔
      FirstProjectionRestrictionIsDiffeomorph S := by
  constructor
  · rintro ⟨f, hgraph⟩
    -- The graph case is exactly the helper proved above.
    exact firstProjectionRestrictionIsDiffeomorph_of_isGraphOfMap S hgraph
  · intro h
    -- Conversely, the canonical inverse to `π_M|_S` produces the graphing map.
    exact ⟨graphingMapOfRestrictedFirstProjection S h,
      isGraphOfMap_of_firstProjectionRestrictionIsDiffeomorph S h⟩

/-- Helper for Theorem 6.32: in a product target, adding the vertical-direction range already
spans the whole space exactly when the first-coordinate projection is surjective. -/
theorem range_inr_sup_range_iff_surjective_fst_comp
    {V X Y : Type*}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (A : V →ₗ[ℝ] X × Y) :
    (LinearMap.inr ℝ X Y).range ⊔ A.range = ⊤ ↔
      Function.Surjective ((LinearMap.fst ℝ X Y).comp A) := by
  constructor
  · intro h u
    -- Decompose `(u, 0)` into a vertical piece and a point in the range of `A`.
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
    -- Surjectivity of the first projection lets us absorb the missing horizontal component into
    -- the image of `A`, leaving only a vertical correction term.
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

/-- Helper for Theorem 6.32: the previous range/surjectivity criterion is unchanged when the map
`A` is viewed as a continuous linear map. -/
  theorem range_inr_sup_range_iff_surjective_fst_comp_continuousLinear
    {V X Y : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : V →L[ℝ] X × Y) :
    (ContinuousLinearMap.inr ℝ X Y).range ⊔ A.range = ⊤ ↔
      Function.Surjective ((ContinuousLinearMap.fst ℝ X Y).comp A) := by
  -- This bridge freezes the coercion from continuous linear maps to linear maps once.
  simpa using
    (range_inr_sup_range_iff_surjective_fst_comp A.toLinearMap :
      (LinearMap.inr ℝ X Y).range ⊔ A.toLinearMap.range = ⊤ ↔
        Function.Surjective ((LinearMap.fst ℝ X Y).comp A.toLinearMap))

/-- Helper for Theorem 6.32: the derivative of the vertical slice map is the canonical inclusion
of the second factor. -/
theorem verticalSliceMap_mfderiv
    (p : M) (q : N) :
    mfderiv J (I.prod J) (verticalSliceMap p) q =
      ContinuousLinearMap.inr ℝ (TangentSpace I p) (TangentSpace J q) := by
  -- The vertical slice is the product of the constant map `p` and the identity on `N`.
  simpa [verticalSliceMap] using
    (mfderiv_prod_right :
      mfderiv J (I.prod J) (fun y : N ↦ (p, y)) q =
        ContinuousLinearMap.inr ℝ (TangentSpace I p) (TangentSpace J q))

/-- Helper for Theorem 6.32: vertical-slice transversality at `x` is exactly surjectivity of the
derivative of the restricted first projection at `x`. -/
theorem verticalSliceMeetsTransverselyAt_iff_surjective_graphFirstProjectionMfderiv
    (S : ImmersedSubmanifold (I.prod J) (M × N)) (x : S) :
    verticalSliceMeetsTransverselyAt S x ↔
      Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) I (graphFirstProjection S) x) := by
  -- Route correction: normalize the two derivatives, then apply the linear-algebra criterion in
  -- the product tangent space.
  rw [verticalSliceMeetsTransverselyAt, verticalSliceMap_mfderiv]
  rw [graphFirstProjection_mfderiv_eq_fst_comp]
  let _ : NormedAddCommGroup (TangentSpace (modelWithCornersSelf ℝ S.ModelSpace) x) :=
    inferInstanceAs (NormedAddCommGroup S.ModelSpace)
  let _ : NormedSpace ℝ (TangentSpace (modelWithCornersSelf ℝ S.ModelSpace) x) :=
    inferInstanceAs (NormedSpace ℝ S.ModelSpace)
  exact range_inr_sup_range_iff_surjective_fst_comp_continuousLinear
    (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) (I.prod J) S.inclusion x)

/-- Helper for Theorem 6.32: an immersed submanifold of a finite-dimensional product manifold has
finite-dimensional model space as soon as it has one point. -/
theorem finiteDimensionalModelSpaceOfPoint
    (S : ImmersedSubmanifold (I.prod J) (M × N)) (x : S) :
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

/-- Helper for Theorem 6.32: once every vertical slice meets `S` uniquely and transversely, the
restricted first projection is a smooth submersion. -/
theorem graphFirstProjection_isSmoothSubmersion_of_uniqueTransverseVerticalSlices
    (S : ImmersedSubmanifold (I.prod J) (M × N))
    [FiniteDimensional ℝ S.ModelSpace]
    (hS : HasUniqueTransverseVerticalSliceIntersections S) :
    Manifold.IsSmoothSubmersion (modelWithCornersSelf ℝ S.ModelSpace) I
      (graphFirstProjection S) := by
  -- Pointwise vertical-slice transversality exactly says the restricted first projection has
  -- surjective derivative everywhere.
  refine
    (Manifold.is_smooth_submersion_iff_forall_surjective_mfderiv
      (graphFirstProjection_contMDiff S)).2 ?_
  intro x
  exact
    (verticalSliceMeetsTransverselyAt_iff_surjective_graphFirstProjectionMfderiv S x).1
      ((hS (graphFirstProjection S x)).2 x rfl)

/-- Helper for Theorem 6.32: a global smooth inverse to the restricted first projection gives a
unique transverse intersection with every vertical slice. -/
theorem hasUniqueTransverseVerticalSliceIntersections_of_restrictedFirstProjectionDiffeomorph
    (S : ImmersedSubmanifold (I.prod J) (M × N))
    (h : FirstProjectionRestrictionIsDiffeomorph S) :
    HasUniqueTransverseVerticalSliceIntersections S := by
  intro p
  refine ⟨?_, ?_⟩
  · refine ⟨restrictedFirstProjectionInverse S h p, ?_, ?_⟩
    · -- The chosen inverse hits the unique point of the fiber over `p`.
      simpa [graphFirstProjection] using
        (restrictedFirstProjectionInverse_rightInverse S h p)
    · intro x hx
      -- Any other point in the same fiber equals the chosen inverse by the left-inverse law.
      calc
        x = restrictedFirstProjectionInverse S h (graphFirstProjection S x) := by
          symm
          exact restrictedFirstProjectionInverse_leftInverse S h x
        _ = restrictedFirstProjectionInverse S h p := by rw [hx]
  · intro x hx
    have hxeq : x = restrictedFirstProjectionInverse S h p := by
      calc
        x = restrictedFirstProjectionInverse S h (graphFirstProjection S x) := by
          symm
          exact restrictedFirstProjectionInverse_leftInverse S h x
        _ = restrictedFirstProjectionInverse S h p := by rw [hx]
    subst x
    have hcomp :
        graphFirstProjection S ∘ restrictedFirstProjectionInverse S h = id := by
      funext q
      exact restrictedFirstProjectionInverse_rightInverse S h q
    have hmfderiv :
        mfderiv I I (graphFirstProjection S ∘ restrictedFirstProjectionInverse S h) p =
          (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) I (graphFirstProjection S)
            (restrictedFirstProjectionInverse S h p)).comp
            (mfderiv I (modelWithCornersSelf ℝ S.ModelSpace)
              (restrictedFirstProjectionInverse S h) p) := by
      -- Differentiate the right-inverse identity at `p`.
      have hg :
          HasMFDerivAt (modelWithCornersSelf ℝ S.ModelSpace) I (graphFirstProjection S)
            (restrictedFirstProjectionInverse S h p)
            (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) I (graphFirstProjection S)
              (restrictedFirstProjectionInverse S h p)) :=
        (((graphFirstProjection_contMDiff S).mdifferentiableAt
          (by simp : (∞ : ℕ∞ω) ≠ 0)).hasMFDerivAt)
      have hf :
          HasMFDerivAt I (modelWithCornersSelf ℝ S.ModelSpace)
            (restrictedFirstProjectionInverse S h) p
            (mfderiv I (modelWithCornersSelf ℝ S.ModelSpace)
              (restrictedFirstProjectionInverse S h) p) :=
        (((restrictedFirstProjectionInverse_contMDiff S h).mdifferentiableAt
          (by simp : (∞ : ℕ∞ω) ≠ 0)).hasMFDerivAt)
      simpa using
        (HasMFDerivAt.comp p hg hf).mfderiv
    rw [hcomp, mfderiv_id] at hmfderiv
    have hsurj :
        Function.Surjective
          (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) I (graphFirstProjection S)
            (restrictedFirstProjectionInverse S h p)) := by
      intro v
      refine ⟨(mfderiv I (modelWithCornersSelf ℝ S.ModelSpace)
          (restrictedFirstProjectionInverse S h) p) v, ?_⟩
      have happly := congrArg (fun L ↦ L v) hmfderiv
      simpa [ContinuousLinearMap.comp_apply] using happly.symm
    exact
      (verticalSliceMeetsTransverselyAt_iff_surjective_graphFirstProjectionMfderiv S
        (restrictedFirstProjectionInverse S h p)).2 hsurj

/-- Helper for Theorem 6.32: unique transverse intersections with all vertical slices reconstruct a
smooth inverse to the restricted first projection. -/
theorem firstProjectionRestrictionIsDiffeomorph_of_uniqueTransverseVerticalSlices
    (S : ImmersedSubmanifold (I.prod J) (M × N))
    (h : HasUniqueTransverseVerticalSliceIntersections S) :
    FirstProjectionRestrictionIsDiffeomorph S := by
  classical
  let ψ : M → S := fun p ↦ Classical.choose (ExistsUnique.exists ((h p).1))
  have hψ_right : Function.RightInverse ψ (graphFirstProjection S) := by
    intro p
    -- The chosen point in the `p`-fiber has first projection equal to `p`.
    exact Classical.choose_spec (ExistsUnique.exists ((h p).1))
  have hψ_left : Function.LeftInverse ψ (graphFirstProjection S) := by
    intro x
    -- Uniqueness in the fiber over `graphFirstProjection S x` identifies `x` with the chosen point.
    rcases (h (graphFirstProjection S x)).1 with ⟨x₀, hx₀, hxuniq⟩
    have hψx : ψ (graphFirstProjection S x) = x₀ := by
      exact hxuniq _ (by simpa [ψ] using hψ_right (graphFirstProjection S x))
    have hx : x = x₀ := hxuniq _ rfl
    calc
      ψ (graphFirstProjection S x) = x₀ := hψx
      _ = x := hx.symm
  by_cases hM : IsEmpty M
  · letI : IsEmpty M := hM
    letI : IsEmpty S := ⟨fun x ↦ isEmptyElim (graphFirstProjection S x)⟩
    let ψEmpty : M → S := fun p ↦ False.elim (isEmptyElim p)
    refine ⟨graphFirstProjection_contMDiff S, ψEmpty, ?_, ?_, ?_⟩
    · -- A map into the empty codomain is automatically smooth.
      exact contMDiff_of_subsingleton
    · intro x
      exact False.elim (isEmptyElim x)
    · intro p
      exact False.elim (isEmptyElim p)
  · have hM_nonempty : Nonempty M := not_isEmpty_iff.mp hM
    let p₀ : M := Classical.choice hM_nonempty
    haveI : FiniteDimensional ℝ S.ModelSpace :=
      finiteDimensionalModelSpaceOfPoint S (ψ p₀)
    have hSubm :
        Manifold.IsSmoothSubmersion (modelWithCornersSelf ℝ S.ModelSpace) I
          (graphFirstProjection S) :=
      graphFirstProjection_isSmoothSubmersion_of_uniqueTransverseVerticalSlices S h
    have hSurj : Function.Surjective (graphFirstProjection S) := by
      intro p
      exact ⟨ψ p, hψ_right p⟩
    have hcomp : ψ ∘ graphFirstProjection S = id := by
      funext x
      exact hψ_left x
    have hψ_contMDiff :
        ContMDiff I (modelWithCornersSelf ℝ S.ModelSpace) ∞ ψ := by
      -- The chosen section is smooth because its composition with the smooth
      -- submersion is the identity.
      exact
        (Manifold.contMDiff_iff_comp_of_surjective_smooth_submersion hSubm hSurj).2 <|
          by simpa [hcomp, Function.comp] using
            (contMDiff_id :
              ContMDiff (modelWithCornersSelf ℝ S.ModelSpace)
                (modelWithCornersSelf ℝ S.ModelSpace) ∞ (id : S → S))
    refine ⟨graphFirstProjection_contMDiff S, ψ, hψ_contMDiff, hψ_left, hψ_right⟩

/-- Theorem 6.32 (2) (Global Characterization of Graphs): if `S` is an immersed submanifold of
`M × N`, then condition `(b)` that `π_M|_S : S → M` is a diffeomorphism is equivalent to
condition `(c)` that every vertical slice `{p} × N` intersects `S` transversely in exactly one
point. -/
theorem restrictedFirstProjection_diffeomorph_iff_uniqueTransverseVerticalSlices
    [BoundarylessManifold I M]
    (S : ImmersedSubmanifold (I.prod J) (M × N)) :
    FirstProjectionRestrictionIsDiffeomorph S ↔
      HasUniqueTransverseVerticalSliceIntersections S := by
  constructor
  · intro h
    -- One direction is already isolated as the transversality helper.
    exact hasUniqueTransverseVerticalSliceIntersections_of_restrictedFirstProjectionDiffeomorph
      S h
  · intro h
    -- The converse reconstructs the global inverse from the unique transverse slices.
    exact firstProjectionRestrictionIsDiffeomorph_of_uniqueTransverseVerticalSlices S h

/-- Theorem 6.32 (3) (Global Characterization of Graphs): if the restricted first projection
`π_M|_S : S → M` is a diffeomorphism, then `S` is the graph of the canonical smooth map
`π_N ∘ (π_M|_S)⁻¹ : M → N`. -/
theorem graphingMap_eq_secondProjection_comp_restrictedFirstProjectionInverse
    [BoundarylessManifold I M]
    (S : ImmersedSubmanifold (I.prod J) (M × N))
    (h : FirstProjectionRestrictionIsDiffeomorph S) :
    IsGraphOfMap S (graphingMapOfRestrictedFirstProjection S h) := by
  -- The final clause is exactly the canonical-graph helper for a restricted-projection inverse.
  simpa using isGraphOfMap_of_firstProjectionRestrictionIsDiffeomorph S h

end GlobalCharacterizationOfGraphs
