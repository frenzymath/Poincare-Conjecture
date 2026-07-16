import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorField.Pullback
import LeeSmoothLib.Ch03.Sec03_14.Proposition_3_9
import LeeSmoothLib.Ch02.Sec02_11.Definition_2_11_extra_2
import LeeSmoothLib.Ch05.Sec05_32.Definition_5_32_extra_2
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_2
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch05.Sec05_34.Lemma_5_34
import LeeSmoothLib.Ch08.Sec08_54.Lemma_8_6
import LeeSmoothLib.Ch08.Sec08_57.Definition_8_57_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Domain sampling for this item:
-- * source-facing vector fields on the submanifold `S` are expressed intrinsically as bundled
--   smooth sections `Cₛ^∞⟮J; E', TangentSpace J⟯`;
-- * ambient neighborhood and global extensions use the canonical bundled smooth-section owner on
--   the corresponding open submanifold of `M`;
-- * the restriction equalities are encoded by `VectorField.f_related` for the relevant subtype
--   inclusions, matching Lee's `X = Y|_S` wording without using the broken auxiliary
--   `VectorField.Along` layer.
-- Semantic recall note: `lean_leansearch` only surfaced generic section-extension lemmas, so the
-- source-facing global criterion is stated directly for intrinsic vector fields on `S`.

universe uE uE' uH uH' uM

noncomputable section

section

open Topology VectorField

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'}
  [IsManifold I (∞ : ℕ∞ω) M]
  {S : Set M} [ChartedSpace H' S] [IsManifold J (∞ : ℕ∞ω) S]

local notation "SmoothAmbientVectorField" => Cₛ^∞⟮I; E, TangentSpace I⟯
local notation "SmoothSubmanifoldVectorField" =>
  Cₛ^∞⟮J; E', fun p : S ↦ TangentSpace J p⟯

private noncomputable abbrev immersionProjection {p : S}
    (hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p) :
    E →L[ℝ] E' :=
  (ContinuousLinearMap.fst ℝ E' hImm.complement).comp
    (hImm.equiv.symm).toContinuousLinearMap

/-- Push an intrinsic vector field on `S` into the ambient tangent bundle
along the subtype inclusion. -/
def ambientSubtypePushforwardField
    (X : SmoothSubmanifoldVectorField) :
    ∀ p : S, TangentSpace I (p : M) :=
  fun p ↦ mfderiv J I (Subtype.val : S → M) p (X p)

/-- The ambient pushforward of a smooth intrinsic vector field is a
smooth section of the ambient tangent bundle along the embedded inclusion. -/
lemma ambientSubtypePushforwardField_contMDiff
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) :
    ContMDiff J I.tangent (∞ : ℕ∞ω)
      (fun p : S ↦
        (⟨(p : M), ambientSubtypePushforwardField X p⟩ : TangentBundle I M)) := by
  -- View the pushed-forward field as the tangent map of the smooth inclusion applied to the
  -- smooth section `T% X`.
  have hInclContMDiff : ContMDiff J I (∞ : ℕ∞ω) (Subtype.val : S → M) :=
    hS.isImmersion.contMDiff
  have hTangent :
      ContMDiff J I.tangent (∞ : ℕ∞ω)
        (tangentMap J I (Subtype.val : S → M) ∘ (T% fun p : S ↦ X p)) := by
    exact
      (hInclContMDiff.contMDiff_tangentMap (by simp)).comp X.contMDiff
  simpa [ambientSubtypePushforwardField, Function.comp, tangentMap] using hTangent

/-- Codomain-restricting the subtype inclusion to an ambient open
neighborhood of `S` preserves smoothness. -/
lemma subtypeValToNeighborhood_contMDiff
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    {U : TopologicalSpace.Opens M} (hSU : (S : Set M) ⊆ U) :
    ContMDiff J I (∞ : ℕ∞ω) (fun p : S ↦ (⟨(p : M), hSU p.2⟩ : U)) := by
  -- Restrict the already smooth subtype inclusion to the chosen ambient open neighborhood.
  have hcomp :
      ContMDiff J I (∞ : ℕ∞ω)
        (Subtype.val ∘ fun p : S ↦ (⟨(p : M), hSU p.2⟩ : U)) := by
    convert hS.isImmersion.contMDiff using 1
  exact
    (ContMDiff.subtypeVal_comp_iff U
      (fun p : S ↦ (⟨(p : M), hSU p.2⟩ : U))).mp hcomp

/-- Helper for Problem 8-15: ambient smoothness on `V ⊆ M` restricts along the open inclusion
`U ↪ M` to a smooth ambient tangent-bundle map on the open subtype. -/
lemma ambientLocalFieldRestrictSmoothAmbientMap
    {U : TopologicalSpace.Opens M} {Xloc : ∀ y : M, TangentSpace I y} {V : Set M}
    (hXloc : ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% Xloc) V) :
    ContMDiffOn I I.tangent (∞ : ℕ∞ω) (fun y : U ↦ T% Xloc y.1) (Subtype.val ⁻¹' V) := by
  -- Compose the ambient tangent-bundle section with the open-subtype inclusion.
  exact
    hXloc.comp
      ((contMDiff_subtype_val : ContMDiff I I (∞ : ℕ∞ω) (Subtype.val : U → M)).contMDiffOn)
      (by
        intro y hy
        exact hy)

/-- Helper for Problem 8-15: pushing the pullback of an ambient vector field along an open
inclusion recovers the original ambient tangent-bundle section. -/
lemma subtypeValMfderivInverseApply
    (U : TopologicalSpace.Opens M)
    (p : U) (w : TangentSpace I (p : M)) :
    mfderiv I I (Subtype.val : U → M) p
      ((mfderiv I I (Subtype.val : U → M) p).inverse w) = w := by
  -- The derivative of the open inclusion is invertible, so applying it cancels `.inverse`.
  simpa using
    (mfderiv_open_subset_inclusion_isInvertible U p).self_apply_inverse w

/-- Helper for Problem 8-15: pushing the pullback of an ambient vector field along an open
inclusion recovers the original ambient tangent-bundle section. -/
lemma tangentMapSubtypeValPullbackEq
    (U : TopologicalSpace.Opens M)
    (X : ∀ p : M, TangentSpace I p)
    (p : U) :
    tangentMap I I (Subtype.val : U → M)
      (T% (VectorField.mpullback I I (Subtype.val : U → M) X) p) =
      T% X p.1 := by
  -- Expand the pullback formula once and cancel the derivative of the open inclusion.
  simpa [tangentMap, VectorField.mpullback_apply, Bundle.TotalSpace.mk_inj] using
    subtypeValMfderivInverseApply U p (X p.1)

/-- Helper for Problem 8-15: restricting an ambient smooth local vector field to an ambient open
subtype yields a smooth local vector field on that open subtype. -/
lemma ambientLocalFieldRestrictSmoothOnOpenSubtype
    {U : TopologicalSpace.Opens M} {Xloc : ∀ y : M, TangentSpace I y} {V : Set M}
    (hXloc : ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% Xloc) V) :
    let g : ∀ y : U, TangentSpace I y :=
      VectorField.mpullback I I (Subtype.val : U → M) Xloc
    ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% g) (Subtype.val ⁻¹' V) := by
  let g : ∀ y : U, TangentSpace I y :=
    VectorField.mpullback I I (Subtype.val : U → M) Xloc
  -- Route correction: keep the field in pullback normal form on the open subtype and postpone the
  -- ambient identification to the final `f_related` packaging step.
  simpa [g] using
    hXloc.mpullback_vectorField_preimage
      (contMDiff_subtype_val : ContMDiff I I (∞ : ℕ∞ω) (Subtype.val : U → M))
      (by
        intro p hp
        simpa using mfderiv_open_subset_inclusion_isInvertible U p)
      (by simp)

/-- Pointwise smooth ambient extensions of the prescribed ambient tangent
vectors along `S` glue to a smooth vector field on an open neighborhood of `S`. -/
lemma exists_local_vectorField_extension_of_pointwiseLocalAmbientExtension
    [T2Space M] [SigmaCompactSpace M]
    (X : ∀ p : S, TangentSpace I (p : M))
    (hX : ∀ p : S, ContMDiffVectorFieldLocalExtension X p) :
    ∃ U : TopologicalSpace.Opens M, ∃ hSU : (S : Set M) ⊆ U,
      ∃ Y : Cₛ^∞⟮I; E, fun p : U ↦ TangentSpace I p⟯,
        ∀ p : S,
          Y ⟨(p : M), hSU p.2⟩ =
            (mfderiv I I (Subtype.val : U → M) ⟨(p : M), hSU p.2⟩).inverse (X p) := by
  classical
  letI : SecondCountableTopology H := I.secondCountableTopology
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let Uset : Set M := ⋃ p : S, (hX p).V
  let U : TopologicalSpace.Opens M := ⟨Uset, isOpen_iUnion fun p ↦ (hX p).isOpen_V⟩
  letI : SecondCountableTopology U := inferInstance
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  letI : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  letI : IsManifold I (∞ : ℕ∞ω) U := inferInstance
  have hSU : (S : Set M) ⊆ U := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, (hX ⟨x, hx⟩).mem_V⟩
  let t : ∀ x : U, Set (TangentSpace I x) := fun x ↦
    if hx : ((x : U) : M) ∈ S then
      {(mfderiv I I (Subtype.val : U → M) x).inverse (X ⟨((x : U) : M), hx⟩)}
    else Set.univ
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    by_cases hx : ((x : U) : M) ∈ S
    · have hxConv :
          Convex ℝ
            ({(mfderiv I I (Subtype.val : U → M) x).inverse (X ⟨((x : U) : M), hx⟩)} :
              Set (TangentSpace I x)) :=
        convex_singleton ((mfderiv I I (Subtype.val : U → M) x).inverse (X ⟨((x : U) : M), hx⟩))
      simpa [t, hx] using hxConv
    · simpa [t, hx] using (convex_univ : Convex ℝ (Set.univ : Set (TangentSpace I x)))
  have hloc :
      ∀ x : U, ∃ W ∈ nhds x, ∃ g : ∀ y : U, TangentSpace I y,
        ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% g) W ∧
          ∀ y ∈ W, g y ∈ t y := by
    intro x
    rcases Set.mem_iUnion.1 x.2 with ⟨p, hxVp⟩
    let data := hX p
    let W : Set U := Subtype.val ⁻¹' data.V
    let g : ∀ y : U, TangentSpace I y :=
      VectorField.mpullback I I (Subtype.val : U → M) data.Xloc
    refine ⟨W, ?_, g, ?_, ?_⟩
    · -- Use the ambient extension neighborhood of the chosen covering point as a neighborhood
      -- inside the open subtype `U`.
      exact (data.isOpen_V.preimage continuous_subtype_val).mem_nhds hxVp
    · -- Restrict the ambient local field to the open subtype by reinterpreting the same section
      -- inclusion `U ↪ M`.
      simpa [g] using
        ambientLocalFieldRestrictSmoothOnOpenSubtype data.contMDiffOn
    · intro y hyW
      by_cases hyS : ((y : U) : M) ∈ S
      · have hyEqLoc : data.Xloc y = X ⟨(y : M), hyS⟩ :=
          data.eq_source ⟨(y : M), hyS⟩ hyW
        -- On the source patch, the pulled-back local field is the inverse transport of the
        -- prescribed ambient vector through the open inclusion derivative.
        simpa [g, t, hyS, VectorField.mpullback_apply, hyEqLoc]
      · simp [g, t, hyS]
  -- Globalize the compatible local ambient extensions over the open neighborhood they cover.
  obtain ⟨Y, hY⟩ :
      ∃ Y : Cₛ^∞⟮I; E, fun p : U ↦ TangentSpace I p⟯, ∀ x : U, Y x ∈ t x := by
    simpa [t] using
      exists_contMDiffSection_forall_mem_convex_of_local I (TangentSpace I) t ht hloc
  refine ⟨U, hSU, Y, ?_⟩
  intro p
  have hpS : ((⟨(p : M), hSU p.2⟩ : U) : M) ∈ S := p.2
  simpa [t, hpS] using hY ⟨(p : M), hSU p.2⟩

/-- Once the pointwise local ambient extension problem is solved, the
closed-subset extension lemma upgrades proper embeddedness to a global extension theorem. -/
lemma properlyEmbedded_vectorField_globalExtension_of_pointwiseLocalAmbientExtension
    [T2Space M] [SigmaCompactSpace M]
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (hProper : S.IsProperlyEmbedded)
    (X : SmoothSubmanifoldVectorField)
    (hX :
      ∀ p : S,
        ContMDiffVectorFieldLocalExtension
          (ambientSubtypePushforwardField X : ∀ p : S, TangentSpace I (p : M)) p) :
    ∃ Z : SmoothAmbientVectorField,
      VectorField.f_related (Subtype.val : S → M) X Z := by
  have hClosed : IsClosed S := hProper.isClosed
  obtain ⟨Z, hZ⟩ :=
    exists_supported_contMDiff_vectorField_extension_of_isClosed
      hClosed isOpen_univ
      (by
        intro x hx
        simp)
      (ambientSubtypePushforwardField X) hX
  refine ⟨⟨Z, hZ.contMDiff⟩, ?_⟩
  refine ⟨hS.isImmersion.contMDiff, ?_⟩
  intro p
  -- The closed-subset extension agrees with the ambient pushforward field along `S`.
  simpa [ambientSubtypePushforwardField] using (hZ.eq_source p).symm

/-- Helper for Problem 8-15: a smooth Euclidean coordinate map on a set contained in one
tangent-bundle trivialization base reconstructs a smooth ambient local vector field. -/
lemma ambientFieldFromTrivializationCoordinates_contMDiffOn
    (p : M) {V : Set M} (hV_open : IsOpen V) {χ : M → E}
    (hχ : ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V)
    (hV_base : V ⊆ (trivializationAt E (TangentSpace I) p).baseSet) :
    let Xloc : ∀ y : M, TangentSpace I y :=
      fun y ↦ (trivializationAt E (TangentSpace I) p).symm y (χ y)
    ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% Xloc) V := by
  let τ := trivializationAt E (TangentSpace I) p
  let Xloc : ∀ y : M, TangentSpace I y := fun y ↦ τ.symm y (χ y)
  have hcoord :
      ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω)
        (fun y ↦ (τ ⟨y, Xloc y⟩).2) V := by
    -- The chosen trivialization reads the rebuilt field back as the original coordinate map `χ`.
    refine hχ.congr ?_
    intro y hy
    simpa [τ, Xloc] using congrArg Prod.snd (τ.apply_mk_symm (hV_base hy) (χ y))
  -- Convert smoothness of the trivialized coordinate back to smoothness of the tangent-bundle
  -- section on the same ambient patch.
  exact
    (Bundle.Trivialization.contMDiffOn_section_iff τ hV_open hV_base).2 hcoord

/-- Helper for Problem 8-15: if tangent-bundle trivialization coordinates match a prescribed
ambient tangent section along `S`, then the rebuilt ambient field agrees with that section on `S`.
-/
lemma ambientFieldFromTrivializationCoordinates_eq_source
    (p : M) {V : Set M} {χ : M → E}
    {X : ∀ q : S, TangentSpace I (q : M)}
    (hV_base : V ⊆ (trivializationAt E (TangentSpace I) p).baseSet)
    (hχ :
      ∀ q : S, (q : M) ∈ V →
        χ q = (trivializationAt E (TangentSpace I) p ⟨(q : M), X q⟩).2) :
    let Xloc : ∀ y : M, TangentSpace I y :=
      fun y ↦ (trivializationAt E (TangentSpace I) p).symm y (χ y)
    ∀ q : S, (q : M) ∈ V → Xloc q = X q := by
  let τ := trivializationAt E (TangentSpace I) p
  let Xloc : ∀ y : M, TangentSpace I y := fun y ↦ τ.symm y (χ y)
  dsimp only
  intro q hqV
  have hqBase : (q : M) ∈ τ.baseSet := hV_base hqV
  have hpair :
      Bundle.TotalSpace.mk' E (q : M) (Xloc q) =
        Bundle.TotalSpace.mk' E (q : M) (X q) := by
    -- Rewrite both fields through the same trivialization coordinates and then cancel `τ.symm`.
    calc
      Bundle.TotalSpace.mk' E (q : M) (Xloc q)
          = τ.toOpenPartialHomeomorph.symm ((q : M), χ q) := by
              simpa [Xloc] using τ.mk_symm hqBase (χ q)
      _ = τ.toOpenPartialHomeomorph.symm ((q : M), (τ ⟨(q : M), X q⟩).2) := by
              rw [hχ q hqV]
      _ = Bundle.TotalSpace.mk' E (q : M) (τ.symm (q : M) (τ ⟨(q : M), X q⟩).2) := by
              simpa using (τ.mk_symm hqBase ((τ ⟨(q : M), X q⟩).2)).symm
      _ = Bundle.TotalSpace.mk' E (q : M) (X q) := by
              congr
              exact τ.symm_apply_apply_mk hqBase (X q)
  simpa [τ, Xloc] using congrArg Bundle.TotalSpace.snd hpair

/-- Helper for Problem 8-15: on the pullback of the ambient tangent-bundle trivialization base set
to `S`, the pushed-forward intrinsic field has smooth ambient trivialization coordinates. -/
lemma ambientPushforwardTrivializationCoordinates_contMDiffOn
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) (p : S) :
    let τ := trivializationAt E (TangentSpace I) (p : M)
    let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
    ContMDiffOn J 𝓘(ℝ, E) (∞ : ℕ∞ω)
      (fun q : S ↦ (τ ⟨(q : M), ambientSubtypePushforwardField X q⟩).2) U := by
  let τ := trivializationAt E (TangentSpace I) (p : M)
  let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
  let fS : S → TangentBundle I M :=
    fun q ↦ ⟨(q : M), ambientSubtypePushforwardField X q⟩
  have hSection :
      ContMDiffOn J I.tangent (∞ : ℕ∞ω) fS U := by
    -- Restrict the globally smooth ambient pushed-forward field to the trivialization base set.
    simpa [fS] using
      (ambientSubtypePushforwardField_contMDiff hS X).contMDiffOn
  have hMaps : Set.MapsTo fS U τ.source := by
    intro q hq
    -- The trivialization source is exactly the pullback of its base set to the total space.
    simpa [fS, U, τ] using hq
  -- Read the smooth tangent-bundle section in the chosen ambient trivialization coordinates.
  exact ((τ.contMDiffOn_iff hMaps).mp hSection).2

/-- Helper for Problem 8-15: once a smooth local section `σ : M → S` fixes the embedded
submanifold near `p` and lands in the source-side trivialization domain, composing the source
coordinate map with `σ` yields the required ambient coordinate extension. -/
lemma ambientCoordinateExtensionOfLocalSection
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) (p : S)
    {V : Set M}
    {σ : M → S}
    (hσ : ContMDiffOn I J (∞ : ℕ∞ω) σ V)
    (hσ_mem :
      ∀ x ∈ V, ((σ x : S) : M) ∈ (trivializationAt E (TangentSpace I) (p : M)).baseSet)
    (hσ_eq : ∀ q : S, (q : M) ∈ V → σ q = q) :
    ∃ χ : M → E,
      ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V ∧
        ∀ q : S, (q : M) ∈ V →
          χ q =
            (trivializationAt E (TangentSpace I) (p : M)
              ⟨(q : M), ambientSubtypePushforwardField X q⟩).2 := by
  let τ := trivializationAt E (TangentSpace I) (p : M)
  let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
  let ψ : S → E := fun q ↦ (τ ⟨(q : M), ambientSubtypePushforwardField X q⟩).2
  have hψ :
      ContMDiffOn J 𝓘(ℝ, E) (∞ : ℕ∞ω) ψ U := by
    -- The intrinsic pushed-forward field is already smooth in these source-side coordinates.
    simpa [τ, U, ψ] using ambientPushforwardTrivializationCoordinates_contMDiffOn hS X p
  have hσ_maps : Set.MapsTo σ V U := by
    -- The local section is assumed to stay inside the trivialization domain used for `ψ`.
    intro x hx
    simpa [U] using hσ_mem x hx
  refine ⟨ψ ∘ σ, ?_, ?_⟩
  · -- Compose the smooth source coordinate map with the smooth local section.
    simpa [Function.comp, ψ] using hψ.comp hσ hσ_maps
  · intro q hqV
    -- On points of `S`, the local section is the identity, so the composed coordinates agree with
    -- the original pushed-forward field coordinates.
    rw [Function.comp, hσ_eq q hqV]

/-- Helper for Problem 8-15: if the projected immersion coordinates stay in the source chart
target on `V`, the standard projected chart formula defines a smooth `S`-valued local section
there. -/
lemma immersionProjectedLocalSection_contMDiffOn
    {p : S}
    (hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p)
    {V : Set M}
    (hV_cod : V ⊆ hImm.codChart.source)
    (hV_target :
      let π : E →L[ℝ] E' := immersionProjection hImm
      ∀ x ∈ V, π ((hImm.codChart.extend I) x) ∈ (hImm.domChart.extend J).target) :
    let π : E →L[ℝ] E' := immersionProjection hImm
    let σ : M → S := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
    ContMDiffOn I J (∞ : ℕ∞ω) σ V := by
  let π : E →L[ℝ] E' := immersionProjection hImm
  let σ : M → S := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
  have hdomChart_mem :
      hImm.domChart ∈ IsManifold.maximalAtlas J (∞ : ℕ∞ω) S :=
    IsManifold.maximalAtlas_subset_of_le
      (show (∞ : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp) hImm.domChart_mem_maximalAtlas
  have hdomChartSymm :
      ContMDiffOn 𝓘(ℝ, E') J (∞ : ℕ∞ω) (hImm.domChart.extend J).symm
        (hImm.domChart.extend J).target := by
    -- Rewrite the source chart inverse on its natural extended target.
    convert contMDiffOn_extend_symm hdomChart_mem using 2
    simpa [Set.inter_comm] using (J.image_eq hImm.domChart.target).symm
  have hcodChart_mem :
      hImm.codChart ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M :=
    IsManifold.maximalAtlas_subset_of_le
      (show (∞ : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp) hImm.codChart_mem_maximalAtlas
  have hcodExt :
      ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) (hImm.codChart.extend I) V := by
    -- Restrict the ambient codomain chart extension to the chosen ambient patch.
    exact (contMDiffOn_extend hcodChart_mem).mono hV_cod
  have hproj :
      ContMDiffOn I 𝓘(ℝ, E') (∞ : ℕ∞ω) (π ∘ (hImm.codChart.extend I)) V := by
    -- Postcompose the ambient chart coordinates with the fixed immersion projection.
    simpa [Function.comp] using π.contDiff.contMDiff.comp_contMDiffOn hcodExt
  have hmaps :
      Set.MapsTo (π ∘ (hImm.codChart.extend I)) V (hImm.domChart.extend J).target := by
    intro x hx
    simpa [π, Function.comp] using hV_target x hx
  -- Compose the smooth projected ambient coordinates with the smooth inverse source chart.
  simpa [σ, π, Function.comp] using hdomChartSymm.comp hproj hmaps

/-- Helper for Problem 8-15: on source points whose ambient image lies in the chosen patch, the
projected chart local section is the identity. -/
lemma immersionProjectedLocalSection_eqSelf
    {p q : S}
    (hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E →L[ℝ] E' := immersionProjection hImm
    let σ : M → S := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
    σ q = q := by
  let π : E →L[ℝ] E' := immersionProjection hImm
  let σ : M → S := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
  have hq_proj :
      π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q :=
    immersionProjectionEqDomainCoordinates hImm hq
  -- Normalize the projected immersion coordinates back to the intrinsic source chart coordinate.
  calc
    σ q = (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) q)) := rfl
    _ = (hImm.domChart.extend J).symm ((hImm.domChart.extend J) q) := by rw [hq_proj]
    _ = q := by
      exact hImm.domChart.extend_left_inv hq

/-- Helper for Problem 8-15: after rewriting the pushed-forward field in one ambient tangent
trivialization, the resulting source-chart coordinate representative is smooth on the part of the
source chart target where that trivialization is defined. -/
lemma sourceCoordinateRepresentative_contMDiffOn
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) (p : S) :
    let τ := trivializationAt E (TangentSpace I) (p : M)
    let hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p :=
      hS.isImmersion.isImmersionAt p
    let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
    let ψcoord : E' → E := fun z ↦
      (τ
        ⟨(((hImm.domChart.extend J).symm z : S) : M),
          ambientSubtypePushforwardField X ((hImm.domChart.extend J).symm z)⟩).2
    let T : Set E' := (hImm.domChart.extend J).target ∩ ((hImm.domChart.extend J).symm ⁻¹' U)
    ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E) (∞ : ℕ∞ω) ψcoord T := by
  let τ := trivializationAt E (TangentSpace I) (p : M)
  let hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p :=
    hS.isImmersion.isImmersionAt p
  let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
  let ψ : S → E := fun q ↦ (τ ⟨(q : M), ambientSubtypePushforwardField X q⟩).2
  let ψcoord : E' → E := fun z ↦
    (τ
      ⟨(((hImm.domChart.extend J).symm z : S) : M),
        ambientSubtypePushforwardField X ((hImm.domChart.extend J).symm z)⟩).2
  let T : Set E' := (hImm.domChart.extend J).target ∩ ((hImm.domChart.extend J).symm ⁻¹' U)
  have hψ :
      ContMDiffOn J 𝓘(ℝ, E) (∞ : ℕ∞ω) ψ U := by
    -- The pushed-forward field already has smooth ambient trivialization coordinates on the source
    -- patch where the tangent-bundle trivialization is defined.
    simpa [τ, U, ψ] using ambientPushforwardTrivializationCoordinates_contMDiffOn hS X p
  have hdomChart_mem :
      hImm.domChart ∈ IsManifold.maximalAtlas J (∞ : ℕ∞ω) S :=
    IsManifold.maximalAtlas_subset_of_le
      (show (∞ : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp) hImm.domChart_mem_maximalAtlas
  have hdomChartSymm :
      ContMDiffOn 𝓘(ℝ, E') J (∞ : ℕ∞ω) (hImm.domChart.extend J).symm
        (hImm.domChart.extend J).target := by
    -- Rewrite the inverse source chart onto its natural extended target once and compose there.
    convert contMDiffOn_extend_symm hdomChart_mem using 2
    simpa [Set.inter_comm] using (J.image_eq hImm.domChart.target).symm
  have hdomChartSymmT :
      ContMDiffOn 𝓘(ℝ, E') J (∞ : ℕ∞ω) (hImm.domChart.extend J).symm T := by
    exact hdomChartSymm.mono fun _ hz ↦ hz.1
  have hmaps : T ⊆ (hImm.domChart.extend J).symm ⁻¹' U := by
    intro z hz
    exact hz.2
  -- Pull the source-side coordinate map back along the smooth inverse source chart.
  change
    ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E) (∞ : ℕ∞ω)
      (ψ ∘ (hImm.domChart.extend J).symm) T
  exact hψ.comp hdomChartSymmT hmaps

/-- Helper for Problem 8-15: the source-chart coordinate representative should be handled through
the local-extension owner `Function.IsSmoothOn`, not just by within-set smoothness on `T`. -/
lemma sourceCoordinateRepresentative_isSmoothOn
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) (p : S) :
    let τ := trivializationAt E (TangentSpace I) (p : M)
    let hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p :=
      hS.isImmersion.isImmersionAt p
    let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
    let ψcoord : E' → E := fun z ↦
      (τ
        ⟨(((hImm.domChart.extend J).symm z : S) : M),
          ambientSubtypePushforwardField X ((hImm.domChart.extend J).symm z)⟩).2
    let T : Set E' := (hImm.domChart.extend J).target ∩ ((hImm.domChart.extend J).symm ⁻¹' U)
    (fun z : T ↦ ψcoord z).IsSmoothOn (𝓘(ℝ, E')) 𝓘(ℝ, E) := by
  -- Route correction: the forward proof needs an ambient-open extension of the chart
  -- representative near each point of `T`, not another `ContMDiffOn` proof on `T` itself.
  -- The naive choice `Ω := T` fails in the boundary case because `T` is generally not open in `E'`.
  -- TODO: construct a boundary-compatible local Euclidean extension of `ψcoord` off `range J`
  -- near each `z : T`, then package it with `Function.isSmoothOn_iff_exists_local_extension`.
  sorry

/-- Helper for Problem 8-15: in one ambient tangent-bundle trivialization around `p`, the
pushed-forward intrinsic field should admit a smooth ambient coordinate extension.

This isolates the remaining forward blocker to a single coordinate-extension datum. -/
lemma embeddedPointwiseLocalAmbientCoordinateExtension
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) (p : S) :
    ∃ V : Set M,
      IsOpen V ∧
        (p : M) ∈ V ∧
          V ⊆ (trivializationAt E (TangentSpace I) (p : M)).baseSet ∧
            ∃ χ : M → E,
              ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V ∧
                ∀ q : S, (q : M) ∈ V →
                  χ q =
                    (trivializationAt E (TangentSpace I) (p : M)
                      ⟨(q : M), ambientSubtypePushforwardField X q⟩).2 := by
  let τ := trivializationAt E (TangentSpace I) (p : M)
  let hImm : Manifold.IsImmersionAt J I (∞ : ℕ∞ω) (Subtype.val : S → M) p :=
    hS.isImmersion.isImmersionAt p
  let π : E →L[ℝ] E' := immersionProjection hImm
  let U : Set S := {q : S | (q : M) ∈ τ.baseSet}
  let ψ : S → E := fun q ↦ (τ ⟨(q : M), ambientSubtypePushforwardField X q⟩).2
  let ψcoord : E' → E := ψ ∘ (hImm.domChart.extend J).symm
  let T : Set E' := (hImm.domChart.extend J).target ∩ ((hImm.domChart.extend J).symm ⁻¹' U)
  let z0 : E' := (hImm.domChart.extend J) p
  have hpτ : (p : M) ∈ τ.baseSet := FiberBundle.mem_baseSet_trivializationAt' (p : M)
  have hpSource : p ∈ (hImm.domChart.extend J).source := by
    simpa [hImm.domChart.extend_source] using hImm.mem_domChart_source
  have hpT : z0 ∈ T := by
    refine ⟨(hImm.domChart.extend J).map_source hpSource, ?_⟩
    change (hImm.domChart.extend J).symm ((hImm.domChart.extend J) p) ∈ U
    rw [hImm.domChart.extend_left_inv hImm.mem_domChart_source]
    exact hpτ
  have hψcoord :
      ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E) (∞ : ℕ∞ω) ψcoord T := by
    -- The chart-side representative is already smooth on the source chart target; only the
    -- off-target Euclidean extension step remains.
    simpa only [τ, hImm, U, ψ, ψcoord, T, Function.comp] using
      sourceCoordinateRepresentative_contMDiffOn hS X p
  have hψcoordSmoothOn :
      (fun z : T ↦ ψcoord z).IsSmoothOn (𝓘(ℝ, E')) 𝓘(ℝ, E) := by
    -- Route correction: use the source-facing local-extension owner on `T`, then extract the
    -- ambient-open Euclidean extension data needed below.
    simpa only [τ, hImm, U, ψcoord, T] using
      sourceCoordinateRepresentative_isSmoothOn hS X p
  have hExtend :
      ∃ Ω : Set E', IsOpen Ω ∧ z0 ∈ Ω ∧
        ∃ ψext : E' → E,
          ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, E) (∞ : ℕ∞ω) ψext Ω ∧
            ∀ z, z ∈ Ω → z ∈ T → ψext z = ψcoord z := by
    rw [Function.isSmoothOn_iff_exists_local_extension] at hψcoordSmoothOn
    rcases hψcoordSmoothOn ⟨z0, hpT⟩ with ⟨Ω, hΩ_open, hz0Ω, ψext, hψext, hψext_eq⟩
    refine ⟨Ω, hΩ_open, hz0Ω, ψext, hψext, ?_⟩
    intro z hzΩ hzT
    exact hψext_eq ⟨z, hzT⟩ hzΩ
  rcases hExtend with ⟨Ω, hΩ_open, hz0Ω, ψext, hψext, hψext_eq⟩
  have hSubtypeVal : IsInducing (Subtype.val : S → M) := IsInducing.subtypeVal
  have hOpenSource :
      ∃ W : Set M, IsOpen W ∧ Subtype.val ⁻¹' W = hImm.domChart.source := by
    exact hSubtypeVal.isOpen_iff.mp hImm.domChart.open_source
  rcases hOpenSource with ⟨W, hW_open, hW_eq⟩
  let V : Set M :=
    τ.baseSet ∩ (W ∩ (hImm.codChart.source ∩ (hImm.codChart.extend I) ⁻¹' (π ⁻¹' Ω)))
  let χ : M → E := fun x ↦ ψext (π ((hImm.codChart.extend I) x))
  have hπΩ_open : IsOpen (π ⁻¹' Ω) := hΩ_open.preimage π.continuous
  have hcodPatch_open :
      IsOpen (hImm.codChart.source ∩ (hImm.codChart.extend I) ⁻¹' (π ⁻¹' Ω)) := by
    simpa using hImm.codChart.isOpen_extend_preimage hπΩ_open
  have hV_open : IsOpen V := by
    simpa [V] using τ.open_baseSet.inter (hW_open.inter hcodPatch_open)
  have hpW : (p : M) ∈ W := by
    have hpPre : p ∈ Subtype.val ⁻¹' W := by
      rw [hW_eq]
      exact hImm.mem_domChart_source
    exact hpPre
  have hp_proj : π ((hImm.codChart.extend I) p) = z0 := by
    dsimp [z0]
    simpa [π] using immersionProjectionEqDomainCoordinates hImm hImm.mem_domChart_source
  have hpV : (p : M) ∈ V := by
    refine ⟨hpτ, hpW, hImm.mem_codChart_source, ?_⟩
    simpa [Function.comp] using hp_proj.symm ▸ hz0Ω
  have hV_base : V ⊆ τ.baseSet := by
    intro x hx
    exact hx.1
  have hV_cod : V ⊆ hImm.codChart.source := by
    intro x hx
    exact hx.2.2.1
  have hχ :
      ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V := by
    have hcodChart_mem :
        hImm.codChart ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M :=
      IsManifold.maximalAtlas_subset_of_le
        (show (∞ : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp) hImm.codChart_mem_maximalAtlas
    have hcodExt :
        ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) (hImm.codChart.extend I) V := by
      -- Restrict the ambient codomain chart extension to the final ambient patch.
      exact (contMDiffOn_extend hcodChart_mem).mono hV_cod
    have hproj :
        ContMDiffOn I 𝓘(ℝ, E') (∞ : ℕ∞ω) (π ∘ (hImm.codChart.extend I)) V := by
      -- Postcompose the ambient chart coordinates with the fixed immersion projection.
      simpa [Function.comp] using π.contDiff.contMDiff.comp_contMDiffOn hcodExt
    have hmaps : Set.MapsTo (π ∘ (hImm.codChart.extend I)) V Ω := by
      intro x hx
      exact hx.2.2.2
    -- Compose the ambient codomain chart with the Euclidean extension built near `z0`.
    simpa [χ, Function.comp] using hψext.comp hproj hmaps
  refine ⟨V, hV_open, hpV, hV_base, χ, hχ, ?_⟩
  intro q hqV
  have hqτ : (q : M) ∈ τ.baseSet := hqV.1
  have hqW : (q : M) ∈ W := hqV.2.1
  have hqΩ : π ((hImm.codChart.extend I) q) ∈ Ω := hqV.2.2.2
  have hqDom : q ∈ hImm.domChart.source := by
    have hqPre : q ∈ Subtype.val ⁻¹' W := hqW
    rw [hW_eq] at hqPre
    exact hqPre
  have hq_proj : π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q := by
    simpa [π] using immersionProjectionEqDomainCoordinates hImm hqDom
  have hqSource : q ∈ (hImm.domChart.extend J).source := by
    simpa [hImm.domChart.extend_source] using hqDom
  have hqT : π ((hImm.codChart.extend I) q) ∈ T := by
    refine ⟨?_, ?_⟩
    · rw [hq_proj]
      exact (hImm.domChart.extend J).map_source hqSource
    · change (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) q)) ∈ U
      rw [hq_proj]
      rw [hImm.domChart.extend_left_inv hqDom]
      exact hqτ
  -- On source points, the ambient codomain chart projects back to the intrinsic source chart, so
  -- the Euclidean extension agrees with the original tangent-trivialization coordinates.
  calc
    χ q = ψcoord (π ((hImm.codChart.extend I) q)) := hψext_eq _ hqΩ hqT
    _ = ψcoord ((hImm.domChart.extend J) q) := by rw [hq_proj]
    _ = ψ q := by
      unfold ψcoord
      simp only [Function.comp_apply]
      rw [hImm.domChart.extend_left_inv hqDom]
    _ =
        (trivializationAt E (TangentSpace I) (p : M)
          ⟨(q : M), ambientSubtypePushforwardField X q⟩).2 := rfl

/-- Problem 8-15 (1). EXTENSION LEMMA FOR VECTOR FIELDS ON SUBMANIFOLDS: Suppose `M` is a smooth
manifold and `S ⊆ M` is an embedded smooth submanifold, with or without boundary. Given
`X ∈ 𝓧(S)`, there is a smooth vector field `Y` on a neighborhood of `S` in `M` such that
`X = Y|_S`. In Lean, the restriction equality is encoded by `VectorField.f_related` for the
inclusion `S ↪ U` into the chosen open neighborhood `U`. -/
theorem exists_local_vectorField_extension_of_isSmoothEmbedding
    [T2Space M] [SigmaCompactSpace M]
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (X : SmoothSubmanifoldVectorField) :
    ∃ U : TopologicalSpace.Opens M, ∃ hSU : (S : Set M) ⊆ U,
      ∃ Y : Cₛ^∞⟮I; E, fun p : U ↦ TangentSpace I p⟯,
        VectorField.f_related (fun p : S ↦ (⟨(p : M), hSU p.2⟩ : U)) X Y := by
  classical
  have hPointwise :
      ∀ p : S,
        ContMDiffVectorFieldLocalExtension
          (ambientSubtypePushforwardField X : ∀ p : S, TangentSpace I (p : M)) p := by
    intro p
    let V := Classical.choose (embeddedPointwiseLocalAmbientCoordinateExtension hS X p)
    have hVspec :=
      Classical.choose_spec (embeddedPointwiseLocalAmbientCoordinateExtension hS X p)
    have hV_open : IsOpen V := hVspec.1
    have hpV : (p : M) ∈ V := hVspec.2.1
    have hVbaseAndCoord := hVspec.2.2
    have hV_base :
        V ⊆ (trivializationAt E (TangentSpace I) (p : M)).baseSet := hVbaseAndCoord.1
    let χ := Classical.choose hVbaseAndCoord.2
    have hχspec := Classical.choose_spec hVbaseAndCoord.2
    have hχ : ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V := hχspec.1
    have hχ_eq :
        ∀ q : S, (q : M) ∈ V →
          χ q =
            (trivializationAt E (TangentSpace I) (p : M)
              ⟨(q : M), ambientSubtypePushforwardField X q⟩).2 := hχspec.2
    let τ := trivializationAt E (TangentSpace I) (p : M)
    let Xloc : ∀ y : M, TangentSpace I y := fun y ↦ τ.symm y (χ y)
    refine
      { V := V
        isOpen_V := hV_open
        mem_V := hpV
        Xloc := Xloc
        contMDiffOn := ?_
        eq_source := ?_ }
    · -- Rebuild the ambient field from its smooth trivialization coordinates on the chosen patch.
      simpa [τ, Xloc] using
        ambientFieldFromTrivializationCoordinates_contMDiffOn (p : M) hV_open hχ hV_base
    · intro q hqV
      -- On the submanifold patch, the rebuilt ambient field matches the prescribed pushforward.
      simpa [τ, Xloc] using
        (ambientFieldFromTrivializationCoordinates_eq_source (p : M) hV_base hχ_eq) q hqV
  obtain ⟨U, hSU, Y, hY⟩ :=
    exists_local_vectorField_extension_of_pointwiseLocalAmbientExtension
      (ambientSubtypePushforwardField X) hPointwise
  refine ⟨U, hSU, Y, ?_⟩
  refine ⟨subtypeValToNeighborhood_contMDiff hS hSU, ?_⟩
  intro p
  let f : S → U := fun q : S ↦ (⟨(q : M), hSU q.2⟩ : U)
  have hf :
      MDifferentiableAt J I f p := by
    -- The codomain-restricted inclusion is smooth, hence differentiable at `p`.
    exact (subtypeValToNeighborhood_contMDiff hS hSU).mdifferentiableAt (by simp)
  have hsub :
      MDifferentiableAt I I (Subtype.val : U → M) (f p) := by
    -- The open-subset inclusion is smooth at every point of `U`.
    exact
      (contMDiff_subtype_val : ContMDiff I I (∞ : ℕ∞ω) (Subtype.val : U → M)).mdifferentiableAt
        (by simp)
  -- Rewrite the target by the pullback normal form produced in the neighborhood gluing lemma.
  rw [hY p]
  rw [eq_comm, (mfderiv_open_subset_inclusion_isInvertible U (f p)).inverse_apply_eq]
  -- Differentiating `Subtype.val ∘ f = Subtype.val` recovers the ambient pushforward field.
  simpa [f, ambientSubtypePushforwardField, Function.comp] using
    (mfderiv_comp_apply p hsub hf (X p))

section GlobalExtension

variable [T2Space M] [SigmaCompactSpace M]

/-- Helper for Problem 8-15: nonproper embeddedness yields a point of the ambient closure that does
not lie on the submanifold itself. -/
lemma notProperlyEmbedded_exists_closure_witness
    (hNotProper : ¬ S.IsProperlyEmbedded) :
    ∃ r : M, r ∈ closure (S : Set M) ∧ r ∉ (S : Set M) := by
  classical
  have hNotClosed : ¬ IsClosed (S : Set M) := by
    -- In a Hausdorff ambient manifold, proper embeddedness is equivalent to closedness.
    intro hClosed
    exact hNotProper (Set.isProperlyEmbedded_iff_isClosed.2 hClosed)
  by_contra hNoWitness
  apply hNotClosed
  rw [← closure_eq_iff_isClosed]
  refine subset_antisymm ?_ subset_closure
  intro x hxClosure
  by_contra hxS
  exact hNoWitness ⟨x, hxClosure, hxS⟩

/-- Helper for Problem 8-15: if the embedded submanifold is not properly embedded, one can choose
an intrinsic smooth vector field with no global ambient extension. -/
lemma notProperlyEmbedded_exists_nonextendableVectorField
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (hpos : 0 < Module.finrank ℝ E')
    (hNotProper : ¬ S.IsProperlyEmbedded) :
    ∃ X : SmoothSubmanifoldVectorField,
      ¬ ∃ Z : SmoothAmbientVectorField,
        VectorField.f_related (Subtype.val : S → M) X Z := by
  rcases notProperlyEmbedded_exists_closure_witness hNotProper with ⟨r, hrClosure, hrNotMem⟩
  -- Route correction: the converse should now reduce the scalar obstruction from Problem 5-18 to
  -- a vector-field obstruction on one source chart patch with a fixed coordinate direction.
  -- The closure witness `r` is the point where the punctured ambient scalar obstruction will be
  -- localized before converting it into a vector-field obstruction.
  -- TODO: extract a nonextendable scalar on an accumulating patch, multiply it by a chart-supported
  -- intrinsic unit field, and show any ambient extension would induce a forbidden scalar
  -- extension.
  sorry

/-- Helper for Problem 8-15: if the embedded submanifold `S` is properly embedded, then every
intrinsic smooth vector field on `S` extends to a globally defined smooth ambient vector field on
`M`. This packages the forward implication for intrinsic vector fields obtained by combining the
local extension theorem from part (1) with the global closed-subset extension lemma. -/
theorem exists_global_vectorField_extension_of_isProperlyEmbedded
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (hProper : S.IsProperlyEmbedded)
    (X : SmoothSubmanifoldVectorField) :
    ∃ Z : SmoothAmbientVectorField,
      VectorField.f_related (Subtype.val : S → M) X Z := by
  classical
  have hPointwise :
      ∀ p : S,
        ContMDiffVectorFieldLocalExtension
          (ambientSubtypePushforwardField X : ∀ p : S, TangentSpace I (p : M)) p := by
    intro p
    let V := Classical.choose (embeddedPointwiseLocalAmbientCoordinateExtension hS X p)
    have hVspec :=
      Classical.choose_spec (embeddedPointwiseLocalAmbientCoordinateExtension hS X p)
    have hV_open : IsOpen V := hVspec.1
    have hpV : (p : M) ∈ V := hVspec.2.1
    have hVbaseAndCoord := hVspec.2.2
    have hV_base :
        V ⊆ (trivializationAt E (TangentSpace I) (p : M)).baseSet := hVbaseAndCoord.1
    let χ := Classical.choose hVbaseAndCoord.2
    have hχspec := Classical.choose_spec hVbaseAndCoord.2
    have hχ : ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) χ V := hχspec.1
    have hχ_eq :
        ∀ q : S, (q : M) ∈ V →
          χ q =
            (trivializationAt E (TangentSpace I) (p : M)
              ⟨(q : M), ambientSubtypePushforwardField X q⟩).2 := hχspec.2
    let τ := trivializationAt E (TangentSpace I) (p : M)
    let Xloc : ∀ y : M, TangentSpace I y := fun y ↦ τ.symm y (χ y)
    refine
      { V := V
        isOpen_V := hV_open
        mem_V := hpV
        Xloc := Xloc
        contMDiffOn := ?_
        eq_source := ?_ }
    · -- Rebuild the ambient field from the chosen smooth coordinate representative.
      simpa [τ, Xloc] using
        ambientFieldFromTrivializationCoordinates_contMDiffOn (p : M) hV_open hχ hV_base
    · intro q hqV
      -- The rebuilt field agrees with the pushed-forward source field on the submanifold patch.
      simpa [τ, Xloc] using
        (ambientFieldFromTrivializationCoordinates_eq_source (p : M) hV_base hχ_eq) q hqV
  exact
    properlyEmbedded_vectorField_globalExtension_of_pointwiseLocalAmbientExtension
      hS hProper X hPointwise

/-- Problem 8-15 (2). EXTENSION LEMMA FOR VECTOR FIELDS ON SUBMANIFOLDS: every smooth vector field
defined on a neighborhood of the embedded submanifold `S` in `M` whose restriction to `S` is an
intrinsic smooth vector field on `S` extends to a globally defined smooth ambient vector field on
`M` if and only if `S` is properly embedded. In Lean, the neighborhood field lives on an open
subtype `U`, and the extension condition is encoded by `VectorField.f_related` for the inclusion
`U ↪ M`. -/
theorem exists_global_vectorField_extension_iff_isProperlyEmbedded
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M)) :
    (∀ (U : TopologicalSpace.Opens M) (hSU : (S : Set M) ⊆ U)
        (Y : Cₛ^∞⟮I; E, fun p : U ↦ TangentSpace I p⟯),
        (∃ X : SmoothSubmanifoldVectorField,
          VectorField.f_related (fun p : S ↦ (⟨(p : M), hSU p.2⟩ : U)) X Y) →
        ∃ Z : SmoothAmbientVectorField,
          VectorField.f_related (Subtype.val : U → M) Y Z) ↔
      S.IsProperlyEmbedded := sorry

/-- Companion for Problem 8-15 (2): if one strengthens the textbook sentence to quantify directly
over intrinsic vector fields on `S`, the converse needs the positive-dimensional hypothesis
`hpos`. In dimension `0`, every intrinsic vector field is zero, so this stronger criterion does
not characterize proper embeddedness. -/
theorem exists_global_vectorField_extension_iff_isProperlyEmbedded_of_posDim
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    (hpos : 0 < Module.finrank ℝ E') :
    (∀ X : SmoothSubmanifoldVectorField,
      ∃ Z : SmoothAmbientVectorField,
        VectorField.f_related (Subtype.val : S → M) X Z) ↔
      S.IsProperlyEmbedded := sorry

end GlobalExtension

end
