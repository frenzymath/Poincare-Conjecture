import LeeSmoothLib.Ch06.Sec06_44.Definition_6_44_extra_1
import Mathlib.LinearAlgebra.Dimension.RankNullity
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch05.Sec05_32.Corollary_5_30
import LeeSmoothLib.Ch05.Sec05_33.Theorem_5_31
import LeeSmoothLib.Ch06.Sec06_44.Theorem_6_30
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold Set

/-- Helper for Problem 6-10: if `A.range ⊔ S = ⊤`, then the quotient map modulo `S` composed with
`A` is surjective, so rank-nullity computes the dimension of `S.comap A`. -/
lemma finrank_comap_add_finrank_quotient_of_range_sup_eq_top
    {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (A : V →ₗ[ℝ] W) (S : Submodule ℝ W) (hAS : A.range ⊔ S = ⊤) :
    Module.finrank ℝ (S.comap A) + Module.finrank ℝ (W ⧸ S) = Module.finrank ℝ V := by
  -- Surjectivity follows by writing any ambient vector as a sum of an `A.range` part and an
  -- `S`-part, then observing that the latter vanishes in the quotient.
  have hsurj : Function.Surjective (S.mkQ.comp A) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro w
    have hw : w ∈ A.range ⊔ S := by
      simpa [hAS]
    rcases Submodule.mem_sup.1 hw with ⟨w₁, hw₁, w₂, hw₂, rfl⟩
    rcases hw₁ with ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    exact (Submodule.Quotient.eq S).2 <| by
      simpa using hw₂
  have hrange : (S.mkQ.comp A).range = ⊤ :=
    LinearMap.range_eq_top.2 hsurj
  -- Rank-nullity for the quotient map identifies the kernel with `S.comap A`.
  have hker :
      (S.mkQ.comp A).ker = S.comap A := by
    ext v
    simp [LinearMap.mem_ker, LinearMap.comp_apply]
  have hnullity := LinearMap.finrank_range_add_finrank_ker (S.mkQ.comp A)
  rw [hrange, hker, finrank_top] at hnullity
  simpa [add_comm] using hnullity

-- Domain sampling:
-- * owner predicates: `IsTransverseToSubmanifold`, `SubmanifoldsIntersectTransversely`
-- * source-facing owner data: `IsEmbeddedSubmanifold`
-- * tangent-space API: `T[J; p]`

section EmbeddedSubmanifoldTangentHelpers

universe uE uH uM uE' uH' uE'' uH''

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S] [IsEmbeddedSubmanifold I J S]
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [FiniteDimensional ℝ E'']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {J' : ModelWithCorners ℝ E'' H''}
variable [ChartedSpace H'' S] [IsManifold J' ∞ S] [IsEmbeddedSubmanifold I J' S]

/-- Helper for Problem 6-10: a smooth ambient map whose image lies in an embedded submanifold is
manifold-differentiable at each point as a map into that subtype. -/
lemma mdifferentiableAt_toSubtype_of_isEmbeddedSubmanifold
    {G : Type*} [TopologicalSpace G] {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    {K : ModelWithCorners ℝ E'' G} [IsManifold K ∞ N]
    {F : N → M} (hF : ContMDiff K I ∞ F) (hFS : ∀ x, F x ∈ S) (x : N) :
    MDifferentiableAt K J (Set.codRestrict F S hFS) x := by
  -- Route correction: the failed shortcut through Corollary 5.30 demands a stronger codomain-
  -- restriction regularity level than the ambient `C^∞` context here provides. The remaining task
  -- is a direct pointwise chart proof of differentiability for the codomain-restricted map.
  let fS : N → S := Set.codRestrict F S hFS
  let y : S := fS x
  let hImm : IsImmersionAt J I ⊤ (Subtype.val : S → M) y :=
    IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val.isImmersion.isImmersionAt y
  let e : OpenPartialHomeomorph N G := chartAt G x
  let x' : E'' := e.extend K x
  have hdom :
      hImm.domChart ∈ IsManifold.maximalAtlas J 1 S :=
    IsManifold.maximalAtlas_subset_of_le
      (I := J) (M := S) (m := 1) (n := ⊤) (by simp) hImm.domChart_mem_maximalAtlas
  have hcod :
      hImm.codChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le
      (I := I) (M := M) (m := 1) (n := ⊤) (by simp) hImm.codChart_mem_maximalAtlas
  have hcont : ContinuousAt fS x := (hF.continuous.continuousAt.codRestrict hFS)
  have hx : x ∈ e.source := mem_chart_source G x
  have hy : fS x ∈ hImm.domChart.source := hImm.mem_domChart_source
  have hy' : F x ∈ hImm.codChart.source := hImm.mem_codChart_source
  rw [← mdifferentiableWithinAt_univ,
    mdifferentiableWithinAt_iff_of_mem_maximalAtlas
      (s := Set.univ) (e := e) (e' := hImm.domChart)
      (IsManifold.chart_mem_maximalAtlas x) hdom hx hy,
    continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
  refine ⟨hcont, ?_⟩
  have hFwithin : MDifferentiableWithinAt K I F Set.univ x := by
    exact (hF.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)).mdifferentiableWithinAt
  have hambient :
      DifferentiableWithinAt ℝ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm)
        (Set.range K) x' := by
    -- Rewrite ambient manifold differentiability into the chosen source/target charts.
    rw [mdifferentiableWithinAt_iff_of_mem_maximalAtlas
      (s := Set.univ) (e := e) (e' := hImm.codChart)
      (IsManifold.chart_mem_maximalAtlas x) hcod hx hy',
      continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter] at hFwithin
    simpa [x'] using hFwithin.2
  have hproj :
      Differentiable ℝ (fun v ↦ (hImm.equiv.symm v).1) := by
    simpa using
      (contDiff_fst.comp hImm.equiv.symm.contDiff).differentiable
        (by simp : (⊤ : ℕ∞ω) ≠ 0)
  have hprojWithin :
      DifferentiableWithinAt ℝ (fun v ↦ (hImm.equiv.symm v).1) Set.univ
        (((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) x') :=
    (hproj _).differentiableWithinAt
  have hcomp :
      DifferentiableWithinAt ℝ
        ((fun v ↦ (hImm.equiv.symm v).1) ∘ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm))
        (Set.range K) x' := by
    -- Postcompose the ambient chart expression with the projection onto the `S`-coordinates of
    -- the immersion normal form.
    exact hprojWithin.comp x' hambient (by intro z hz; simp)
  have hsource_mem : fS ⁻¹' hImm.domChart.source ∈ nhds x := by
    -- Continuity of the codomain-restricted map pulls back the immersion-chart neighborhood.
    have : hImm.domChart.source ∈ nhds (fS x) :=
      hImm.domChart.open_source.mem_nhds hy
    exact hcont.preimage_mem_nhds this
  have hset_mem :
      (e.extend K).symm ⁻¹' (fS ⁻¹' hImm.domChart.source) ∈ nhdsWithin x' (Set.range K) := by
    -- Transport that neighborhood through the source chart on `N`.
    simpa [e, x', nhdsWithin_univ] using
      e.extend_preimage_mem_nhdsWithin (I := K) (s := Set.univ) (t := fS ⁻¹' hImm.domChart.source)
        hx (by simpa [nhdsWithin_univ] using hsource_mem)
  have heq :
      ((hImm.domChart.extend J) ∘ fS ∘ (e.extend K).symm)
        =ᶠ[nhdsWithin x' (Set.range K)]
          ((fun v ↦ (hImm.equiv.symm v).1) ∘
            ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm)) := by
    -- On the neighborhood where the restricted map lands in the immersion chart domain, the two
    -- chart expressions agree by the written-in-charts normal form.
    refine Filter.eventuallyEq_of_mem hset_mem ?_
    intro z hz
    have hz_source : fS ((e.extend K).symm z) ∈ hImm.domChart.source := by
      simpa using hz
    have hz_extend_source : fS ((e.extend K).symm z) ∈ (hImm.domChart.extend J).source := by
      simpa [OpenPartialHomeomorph.extend_source] using hz_source
    have hz_target :
        hImm.domChart.extend J (fS ((e.extend K).symm z)) ∈ (hImm.domChart.extend J).target :=
      (hImm.domChart.extend J).map_source hz_extend_source
    have hwritten :=
      (congrArg (fun v => Prod.fst (hImm.equiv.symm v)) (hImm.writtenInCharts hz_target)).symm
    have hwritten' :
        hImm.domChart.extend J (fS ((e.extend K).symm z)) =
          (hImm.equiv.symm
            ((hImm.codChart.extend I)
              (↑(hImm.domChart.symm (hImm.domChart (fS ((e.extend K).symm z)))) : M))).1 := by
      simpa [Function.comp, OpenPartialHomeomorph.extend_coe, hImm.domChart.left_inv hz_source] using
        hwritten
    have hwritten'' :
        hImm.domChart.extend J (fS ((e.extend K).symm z)) =
          (hImm.equiv.symm ((hImm.codChart.extend I) (F ((e.extend K).symm z)))).1 := by
      calc
        hImm.domChart.extend J (fS ((e.extend K).symm z))
            = (hImm.equiv.symm
                ((hImm.codChart.extend I)
                  (↑(hImm.domChart.symm (hImm.domChart (fS ((e.extend K).symm z)))) : M))).1 := by
                    exact hwritten'
        _ = (hImm.equiv.symm ((hImm.codChart.extend I) (F ((e.extend K).symm z)))).1 := by
              rw [hImm.domChart.left_inv hz_source]
              rfl
    simpa [Function.comp, fS, OpenPartialHomeomorph.extend_coe] using hwritten''
  have hx'_target : x' ∈ (e.extend K).target := (e.extend K).map_source <| by
    simpa [OpenPartialHomeomorph.extend_source] using hx
  have hx'_range : x' ∈ Set.range K :=
    e.extend_target_subset_range hx'_target
  exact hcomp.congr_of_eventuallyEq_of_mem heq hx'_range

/-- Helper for Problem 6-10: two embedded submanifold structures on the same subtype determine the
same ambient tangent submodule at each point. -/
lemma sameCarrierTangentSpace_eq_of_embeddedStructures (p : S) :
    (T[J; p] : Submodule ℝ (TangentSpace I (p : M))) = T[J'; p] := by
  let g : S → S := Set.codRestrict (Subtype.val : S → M) S (fun x => x.2)
  have hsubJ : MDifferentiableAt J I (Subtype.val : S → M) p :=
    (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
      (I := I) (JS := J) (S := S)).mdifferentiableAt (by simp)
  have hsubJ' : MDifferentiableAt J' I (Subtype.val : S → M) p :=
    (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
      (I := I) (JS := J') (S := S)).mdifferentiableAt (by simp)
  have hdiffJJ' : MDifferentiableAt J J' g p := by
    -- Differentiate the carrier identity from the `J`-structure into the `J'`-structure.
    simpa [g] using
      mdifferentiableAt_toSubtype_of_isEmbeddedSubmanifold
        (I := I) (J := J') (K := J)
        (F := (Subtype.val : S → M))
        (subtypeVal_contMDiff_of_isEmbeddedSubmanifold (I := I) (JS := J) (S := S))
        (fun x => x.2) p
  have hdiffJ'J : MDifferentiableAt J' J g p := by
    -- The same carrier identity is differentiable in the opposite direction as well.
    simpa [g] using
      mdifferentiableAt_toSubtype_of_isEmbeddedSubmanifold
        (I := I) (J := J) (K := J')
        (F := (Subtype.val : S → M))
        (subtypeVal_contMDiff_of_isEmbeddedSubmanifold (I := I) (JS := J') (S := S))
        (fun x => x.2) p
  have hle : (T[J; p] : Submodule ℝ (TangentSpace I (p : M))) ≤ T[J'; p] := by
    rw [show T[J; p] = (mfderiv J I (Subtype.val : S → M) p).range by rfl,
      show T[J'; p] = (mfderiv J' I (Subtype.val : S → M) p).range by rfl]
    have hcomp :
        mfderiv J I (Subtype.val : S → M) p =
          (mfderiv J' I (Subtype.val : S → M) p).comp (mfderiv J J' g p) := by
      -- The inclusion factors through the carrier identity into the `J'`-structure.
      simpa [g, Function.comp] using
        (mfderiv_comp (x := p) (g := (Subtype.val : S → M)) (f := g) hsubJ' hdiffJJ')
    rw [hcomp]
    exact LinearMap.range_comp_le_range _ _
  have hge : T[J'; p] ≤ (T[J; p] : Submodule ℝ (TangentSpace I (p : M))) := by
    rw [show T[J'; p] = (mfderiv J' I (Subtype.val : S → M) p).range by rfl,
      show T[J; p] = (mfderiv J I (Subtype.val : S → M) p).range by rfl]
    have hcomp :
        mfderiv J' I (Subtype.val : S → M) p =
          (mfderiv J I (Subtype.val : S → M) p).comp (mfderiv J' J g p) := by
      -- Reversing the carrier identity gives the opposite tangent inclusion.
      simpa [g, Function.comp] using
        (mfderiv_comp (x := p) (g := (Subtype.val : S → M)) (f := g) hsubJ hdiffJ'J)
    rw [hcomp]
    exact LinearMap.range_comp_le_range _ _
  exact le_antisymm hle hge

/-- Helper for Problem 6-10: the codimension of an embedded submanifold equals the dimension of
the quotient of the ambient tangent space by the tangent submodule at any point. -/
lemma tangentQuotientFinrank_eq_codimension (p : S) :
    Module.finrank ℝ ((TangentSpace I (p : M)) ⧸ T[J; p]) =
      (inferInstance : IsEmbeddedSubmanifold I J S).codimension := by
  let _ : FiniteDimensional ℝ (TangentSpace I (p : M)) := by
    simpa using (inferInstance : FiniteDimensional ℝ E)
  let _ : FiniteDimensional ℝ (TangentSpace J p) := by
    simpa using (inferInstance : FiniteDimensional ℝ E')
  let hEmbedded : IsEmbeddedSubmanifold I J S := inferInstance
  let hSubtypeEmbeddingInf : Manifold.IsSmoothEmbedding J I ∞ (Subtype.val : S → M) :=
    isSmoothEmbedding_of_le
      (I := I) (I' := J) (M := M) (N := S) (m := ∞) (n := ⊤) (by simp)
      hEmbedded.isSmoothEmbedding_subtype_val
  have hinj :
      Function.Injective (mfderiv J I (Subtype.val : S → M) p) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv
      (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
        (I := I) (JS := J) (S := S))).1
      hSubtypeEmbeddingInf.isImmersion p
  have hrange :
      Module.finrank ℝ (T[J; p] : Submodule ℝ (TangentSpace I (p : M))) =
        Module.finrank ℝ (TangentSpace J p) := by
    -- The inclusion derivative is injective, so its range has the same dimension as the
    -- submanifold tangent space.
    change Module.finrank ℝ ((mfderiv J I (Subtype.val : S → M) p).toLinearMap.range) =
      Module.finrank ℝ (TangentSpace J p)
    have hnullity := LinearMap.finrank_range_add_finrank_ker
      (mfderiv J I (Subtype.val : S → M) p).toLinearMap
    have hker :
        (mfderiv J I (Subtype.val : S → M) p).toLinearMap.ker = ⊥ :=
      LinearMap.ker_eq_bot.2 hinj
    rw [hker, finrank_bot, add_zero] at hnullity
    exact hnullity
  have hquot := Submodule.finrank_quotient_add_finrank
    (T[J; p] : Submodule ℝ (TangentSpace I (p : M)))
  rw [hrange,
    show Module.finrank ℝ (TangentSpace I (p : M)) = Module.finrank ℝ E by rfl,
    show Module.finrank ℝ (TangentSpace J p) = Module.finrank ℝ E' by rfl] at hquot
  simpa [IsEmbeddedSubmanifold.codimension_eq_finrank_sub
    (I := I) (J := J) (S := S) (hS := inferInstance)] using
    Nat.eq_sub_of_add_eq hquot

/-- Helper for Problem 6-10: embedded submanifold structures on the same nonempty carrier have the
same codimension. -/
lemma sameCarrierCodimension_eq_of_embeddedStructures (p : S) :
    (inferInstance : IsEmbeddedSubmanifold I J S).codimension =
      (inferInstance : IsEmbeddedSubmanifold I J' S).codimension := by
  -- Compare both codimensions with the common quotient of the ambient tangent space at `p`.
  calc
    (inferInstance : IsEmbeddedSubmanifold I J S).codimension
      = Module.finrank ℝ ((TangentSpace I (p : M)) ⧸ T[J; p]) := by
          symm
          exact tangentQuotientFinrank_eq_codimension (I := I) (J := J) (S := S) p
    _ = Module.finrank ℝ ((TangentSpace I (p : M)) ⧸ T[J'; p]) := by
          rw [sameCarrierTangentSpace_eq_of_embeddedStructures
            (I := I) (J := J) (J' := J') (S := S) p]
    _ = (inferInstance : IsEmbeddedSubmanifold I J' S).codimension := by
          exact tangentQuotientFinrank_eq_codimension (I := I) (J := J') (S := S) p

end EmbeddedSubmanifoldTangentHelpers

section TransversePreimageTangentSpace

universe uE uF uE' uE'' uH uG uH' uH'' uM uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [FiniteDimensional ℝ E'']
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [TopologicalSpace G]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {K : ModelWithCorners ℝ F G} [IsManifold K ∞ N]
variable {JX : ModelWithCorners ℝ E' H'} {X : Set M}
variable [ChartedSpace H' X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold I JX X]

/-- Helper for Problem 6-10: every tangent vector to the chosen preimage submanifold maps under
`dfₚ` into the tangent space of the target submanifold. -/
lemma preimageTangentSpace_le_comap
    {f : N → M} {JW : ModelWithCorners ℝ E'' H''}
    [ChartedSpace H'' (f ⁻¹' X)] [IsManifold JW ∞ (f ⁻¹' X)]
    [IsEmbeddedSubmanifold K JW (f ⁻¹' X)]
    (hF : ContMDiff K I ∞ f)
    (p : f ⁻¹' X) :
    let x : X := ⟨f p, p.2⟩
    T[JW; p] ≤ (T[JX; x]).comap (mfderiv K I f p).toLinearMap := by
  dsimp
  let g : f ⁻¹' X → X := Set.codRestrict (fun y : f ⁻¹' X ↦ f y) X (fun y ↦ y.2)
  let x : X := ⟨f p, p.2⟩
  have hsubPre : MDifferentiableAt JW K (Subtype.val : f ⁻¹' X → N) p :=
    (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
      (I := K) (JS := JW) (S := f ⁻¹' X)).mdifferentiableAt (by simp)
  have hsubX : MDifferentiableAt JX I (Subtype.val : X → M) x :=
    (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
      (I := I) (JS := JX) (S := X)).mdifferentiableAt (by simp)
  have hFpre : ContMDiff JW I ∞ (fun y : f ⁻¹' X ↦ f y) := by
    -- Restrict the ambient smooth map to the chosen preimage submanifold.
    simpa [Function.comp] using
      hF.comp
        (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
          (I := K) (JS := JW) (S := f ⁻¹' X))
  have hgdiff : MDifferentiableAt JW JX g p := by
    -- Differentiate the codomain-restricted preimage map at the chosen point.
    simpa [g] using
      mdifferentiableAt_toSubtype_of_isEmbeddedSubmanifold
        (I := I) (J := JX) (K := JW) (S := X)
        (F := fun y : f ⁻¹' X ↦ f y) hFpre (fun y ↦ y.2) p
  rw [show T[JW; p] = (mfderiv JW K (Subtype.val : f ⁻¹' X → N) p).range by rfl]
  intro v hv
  rcases LinearMap.mem_range.1 hv with ⟨u, rfl⟩
  change (mfderiv K I f p) ((mfderiv JW K (Subtype.val : f ⁻¹' X → N) p) u) ∈ T[JX; x]
  rw [show T[JX; x] = (mfderiv JX I (Subtype.val : X → M) x).range by rfl]
  refine LinearMap.mem_range.2 ⟨mfderiv JW JX g p u, ?_⟩
  have hfg : f ∘ (Subtype.val : f ⁻¹' X → N) = (Subtype.val : X → M) ∘ g := by
    funext y
    rfl
  have hcomp :
      (mfderiv K I f p).comp
          (mfderiv JW K (Subtype.val : f ⁻¹' X → N) p) =
        (mfderiv JX I (Subtype.val : X → M) x).comp (mfderiv JW JX g p) := by
    -- Differentiate the ambient factorization of `f` through the codomain-restricted map `g`.
    have hleft :
        (mfderiv K I f p).comp
            (mfderiv JW K (Subtype.val : f ⁻¹' X → N) p) =
          mfderiv JW I (f ∘ (Subtype.val : f ⁻¹' X → N)) p := by
      symm
      simpa [Function.comp] using
        (mfderiv_comp (x := p) (g := f)
          (f := (Subtype.val : f ⁻¹' X → N))
          (hF.mdifferentiableAt (by simp)) hsubPre)
    have hmid :
        mfderiv JW I (f ∘ (Subtype.val : f ⁻¹' X → N)) p =
          mfderiv JW I ((Subtype.val : X → M) ∘ g) p := by
      rw [hfg]
    have hright :
        mfderiv JW I ((Subtype.val : X → M) ∘ g) p =
          (mfderiv JX I (Subtype.val : X → M) x).comp (mfderiv JW JX g p) := by
      simpa [Function.comp] using
        (mfderiv_comp (x := p) (g := (Subtype.val : X → M)) (f := g) hsubX hgdiff)
    exact hleft.trans (hmid.trans hright)
  simpa [LinearMap.comp_apply] using (congrArg (fun L ↦ L u) hcomp).symm

-- The next helper transports codimension from Theorem 6.30's witness structure to the chosen
-- preimage structure.
/-- Helper for Problem 6-10: the codimension of any chosen embedded structure on the transverse
preimage agrees with the codimension supplied by Theorem 6.30. -/
lemma preimageCodimension_eq_codimension_of_transverse
    {f : N → M} {JW : ModelWithCorners ℝ E'' H''}
    [ChartedSpace H'' (f ⁻¹' X)] [IsManifold JW ∞ (f ⁻¹' X)]
    [IsEmbeddedSubmanifold K JW (f ⁻¹' X)]
    (htrans : IsTransverseToSubmanifold I K JX X f)
    (p : f ⁻¹' X) :
    (inferInstance : IsEmbeddedSubmanifold K JW (f ⁻¹' X)).codimension =
      (inferInstance : IsEmbeddedSubmanifold I JX X).codimension := by
  -- Unpack Theorem 6.30's witness structure on the same carrier.
  have hwitness :=
    transverse_preimage_has_embedded_submanifold_structure
      (IM := I) (IN := K) (JS := JX) (S := X) (F := f) htrans
  dsimp only at hwitness
  rcases hwitness with ⟨cs, hs, hW, hcodW⟩
  letI : ChartedSpace
      (EuclideanSpace ℝ
        (Fin
          (Module.finrank ℝ F -
            (inferInstance : IsEmbeddedSubmanifold I JX X).codimension)))
      (f ⁻¹' X) := cs
  letI : IsManifold
      (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ
          (Fin
            (Module.finrank ℝ F -
              (inferInstance : IsEmbeddedSubmanifold I JX X).codimension))))
      ∞ (f ⁻¹' X) := hs
  letI : IsEmbeddedSubmanifold
      K
      (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ
          (Fin
            (Module.finrank ℝ F -
              (inferInstance : IsEmbeddedSubmanifold I JX X).codimension))))
      (f ⁻¹' X) := hW
  -- Transport codimension across the two embedded structures on the same subtype carrier.
  calc
    (inferInstance : IsEmbeddedSubmanifold K JW (f ⁻¹' X)).codimension
      = (inferInstance : IsEmbeddedSubmanifold
          K
          (modelWithCornersSelf ℝ
            (EuclideanSpace ℝ
              (Fin
                (Module.finrank ℝ F -
                  (inferInstance : IsEmbeddedSubmanifold I JX X).codimension))))
          (f ⁻¹' X)).codimension := by
            exact sameCarrierCodimension_eq_of_embeddedStructures
              (I := K)
              (J := JW)
              (J' := modelWithCornersSelf ℝ
                (EuclideanSpace ℝ
                  (Fin
                    (Module.finrank ℝ F -
                      (inferInstance : IsEmbeddedSubmanifold I JX X).codimension))))
              (S := f ⁻¹' X) p
    _ = (inferInstance : IsEmbeddedSubmanifold I JX X).codimension := hcodW

theorem tangentSpace_preimage_eq_comap_of_transverse_aux
    {f : N → M} {JW : ModelWithCorners ℝ E'' H''}
    [ChartedSpace H'' (f ⁻¹' X)] [IsManifold JW ∞ (f ⁻¹' X)]
    [IsEmbeddedSubmanifold K JW (f ⁻¹' X)]
    (htrans : IsTransverseToSubmanifold I K JX X f)
    (p : f ⁻¹' X) :
    let x : X := ⟨f p, p.2⟩
    T[JW; p] = (T[JX; x]).comap (mfderiv K I f p).toLinearMap := by
  -- Route correction: the remaining work is no longer a chart-level restriction lemma; it is the
  -- flat codimension comparison between the chosen preimage structure and Theorem 6.30's witness.
  dsimp
  let x : X := ⟨f p, p.2⟩
  let _ : FiniteDimensional ℝ (TangentSpace K (p : N)) := by
    simpa using (inferInstance : FiniteDimensional ℝ F)
  let _ : FiniteDimensional ℝ (TangentSpace I (f p)) := by
    simpa using (inferInstance : FiniteDimensional ℝ E)
  have hle :
      T[JW; p] ≤ (T[JX; x]).comap (mfderiv K I f p).toLinearMap := by
    -- Tangent vectors to the preimage already land in the tangent space of `X`.
    simpa [x] using
      preimageTangentSpace_le_comap
        (I := I) (K := K) (JX := JX) (X := X) (JW := JW) (f := f) htrans p
  have hsup :
      (mfderiv K I f p).range ⊔ (T[JX; x] : Submodule ℝ (TangentSpace I (f p))) = ⊤ := by
    -- Transversality gives the rank-nullity hypothesis for the derivative/comap pair.
    simpa [x] using htrans.tangent_sup_eq_top p
  have hcomapQuot :
      Module.finrank ℝ
          ((T[JX; x] : Submodule ℝ (TangentSpace I (f p))).comap
            (mfderiv K I f p).toLinearMap) +
        Module.finrank ℝ ((TangentSpace I (f p)) ⧸ T[JX; x]) =
          Module.finrank ℝ (TangentSpace K (p : N)) := by
    -- Rank-nullity computes the dimension of the comap once the derivative image and `TₓX`
    -- span the ambient tangent space.
    simpa using
      finrank_comap_add_finrank_quotient_of_range_sup_eq_top
        (A := (mfderiv K I f p).toLinearMap)
        (S := T[JX; x])
        hsup
  have hquotEq :
      Module.finrank ℝ ((TangentSpace K (p : N)) ⧸ T[JW; p]) =
        Module.finrank ℝ ((TangentSpace I (f p)) ⧸ T[JX; x]) := by
    -- Both quotient dimensions are the common codimension of the transverse preimage.
    calc
      Module.finrank ℝ ((TangentSpace K (p : N)) ⧸ T[JW; p])
        = (inferInstance : IsEmbeddedSubmanifold K JW (f ⁻¹' X)).codimension := by
            exact tangentQuotientFinrank_eq_codimension (I := K) (J := JW) (S := f ⁻¹' X) p
      _ = (inferInstance : IsEmbeddedSubmanifold I JX X).codimension := by
            exact preimageCodimension_eq_codimension_of_transverse
              (I := I) (K := K) (JX := JX) (X := X) (JW := JW) htrans p
      _ = Module.finrank ℝ ((TangentSpace I (f p)) ⧸ T[JX; x]) := by
            symm
            exact tangentQuotientFinrank_eq_codimension (I := I) (J := JX) (S := X) x
  have hpreimageSum :
      Module.finrank ℝ ((TangentSpace I (f p)) ⧸ T[JX; x]) +
        Module.finrank ℝ ↥(T[JW; p] : Submodule ℝ (TangentSpace K (p : N))) =
          Module.finrank ℝ (TangentSpace K (p : N)) := by
    -- Rewriting the quotient dimension turns the chosen preimage tangent space into the same
    -- additive complement as the comap.
    simpa [hquotEq] using
      (Submodule.finrank_quotient_add_finrank
        (T[JW; p] : Submodule ℝ (TangentSpace K (p : N))))
  have hcomapSum :
      Module.finrank ℝ ((TangentSpace I (f p)) ⧸ T[JX; x]) +
        Module.finrank ℝ
          ((T[JX; x] : Submodule ℝ (TangentSpace I (f p))).comap
            (mfderiv K I f p).toLinearMap) =
          Module.finrank ℝ (TangentSpace K (p : N)) := by
    -- Commute the two summands to align with the previous identity.
    simpa [add_comm] using hcomapQuot
  have hfin :
      Module.finrank ℝ ↥(T[JW; p] : Submodule ℝ (TangentSpace K (p : N))) =
        Module.finrank ℝ
          ((T[JX; x] : Submodule ℝ (TangentSpace I (f p))).comap
            (mfderiv K I f p).toLinearMap) := by
    -- Cancel the common quotient term from the two dimension formulas.
    exact Nat.add_left_cancel (hpreimageSum.trans hcomapSum.symm)
  -- Inclusion plus equality of dimensions forces equality of submodules.
  simpa [x] using (Submodule.eq_of_le_of_finrank_eq hle hfin)

/-- Helper for Problem 6-10: once the ambient manifold structures on `M` and `N` are available as
ordinary terms, the public preimage tangent-space statement is just the proved auxiliary theorem. -/
lemma preimageTangentSpaceEqComap_fromAmbientManifolds
    {f : N → M} {JW : ModelWithCorners ℝ E'' H''}
    [ChartedSpace H'' (f ⁻¹' X)] [IsManifold JW ∞ (f ⁻¹' X)]
    [IsEmbeddedSubmanifold K JW (f ⁻¹' X)]
    (hIM : IsManifold I ∞ M) (hKN : IsManifold K ∞ N)
    (htrans : IsTransverseToSubmanifold I K JX X f)
    (p : f ⁻¹' X) :
    let x : X := ⟨f p, p.2⟩
    T[JW; p] = (T[JX; x]).comap (mfderiv K I f p).toLinearMap := by
  -- Reinstall the ambient manifold structures as local instances and reuse the closed auxiliary
  -- theorem without any new geometry.
  let _ : IsManifold I ∞ M := hIM
  let _ : IsManifold K ∞ N := hKN
  simpa using
    (tangentSpace_preimage_eq_comap_of_transverse_aux
      (I := I) (K := K) (JX := JX) (X := X) (JW := JW) (f := f) htrans p)

omit [IsManifold I ∞ M] [IsManifold K ∞ N] in
/-- Helper for Problem 6-10: the public preimage tangent-space theorem can be reused under
`omit` once the ambient manifold structures are treated as ordinary implicit arguments. -/
lemma preimageTangentSpaceEqComap_omitAux
    {hIM : IsManifold I ∞ M} {hKN : IsManifold K ∞ N}
    {f : N → M} {JW : ModelWithCorners ℝ E'' H''}
    [ChartedSpace H'' (f ⁻¹' X)] [IsManifold JW ∞ (f ⁻¹' X)]
    [IsEmbeddedSubmanifold K JW (f ⁻¹' X)]
    (htrans : IsTransverseToSubmanifold I K JX X f)
    (p : f ⁻¹' X) :
    let x : X := ⟨f p, p.2⟩
    T[JW; p] = (T[JX; x]).comap (mfderiv K I f p).toLinearMap := by
  -- Reinstall the ambient manifold structures as instances and reuse the closed wrapper lemma.
  let _ : IsManifold I ∞ M := hIM
  let _ : IsManifold K ∞ N := hKN
  simpa using
    (preimageTangentSpaceEqComap_fromAmbientManifolds
      (I := I) (K := K) (JX := JX) (X := X) (JW := JW) (f := f) hIM hKN htrans p)

/-- Problem 6-10 (1): if `F : N → M` is transverse to the chosen embedded submanifold structure on
`X`, and `F ⁻¹' X` carries a chosen embedded submanifold structure, then the tangent space of
`F ⁻¹' X` is the inverse image of the tangent space of `X` under `dFₚ`, written in Lean as a
`Submodule.comap`. -/
theorem tangentSpace_preimage_eq_comap_of_transverse
    {f : N → M} {JW : ModelWithCorners ℝ E'' H''}
    [ChartedSpace H'' (f ⁻¹' X)] [IsManifold JW ∞ (f ⁻¹' X)]
    [IsEmbeddedSubmanifold K JW (f ⁻¹' X)]
    (htrans : IsTransverseToSubmanifold I K JX X f)
    (p : f ⁻¹' X) :
    let x : X := ⟨f p, p.2⟩
    T[JW; p] = (T[JX; x]).comap (mfderiv K I f p).toLinearMap := by
  -- Route correction: once this public theorem is outside the local `omit`, the section manifold
  -- instances are visible again and the omit-safe wrapper closes the statement directly.
  simpa using
    (preimageTangentSpaceEqComap_omitAux
      (I := I) (K := K) (JX := JX) (X := X) (JW := JW) (f := f)
      (hIM := inferInstance) (hKN := inferInstance) htrans p)

end TransversePreimageTangentSpace

section TransverseIntersectionTangentSpace

universe uE uE' uE'' uE''' uH uH' uH'' uH''' uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [FiniteDimensional ℝ E'']
variable {E''' : Type uE'''} [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [FiniteDimensional ℝ E''']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {H''' : Type uH'''} [TopologicalSpace H''']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {JX : ModelWithCorners ℝ E' H'} {X : Set M}
variable {JX' : ModelWithCorners ℝ E'' H''} {X' : Set M}
variable [ChartedSpace H' X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold I JX X]
variable [ChartedSpace H'' X'] [IsManifold JX' ∞ X'] [IsEmbeddedSubmanifold I JX' X']

/-- Helper for Problem 6-10: every tangent vector to the chosen intersection submanifold belongs to
the tangent spaces of both factors, hence to their infimum. -/
lemma intersectionTangentSpace_le_inf
    {JXX' : ModelWithCorners ℝ E''' H'''}
    [ChartedSpace H''' (X ∩ X' : Set M)] [IsManifold JXX' ∞ (X ∩ X' : Set M)]
    [IsEmbeddedSubmanifold I JXX' (X ∩ X' : Set M)]
    (p : (X ∩ X' : Set M)) :
    (T[JXX'; p] : Submodule ℝ (TangentSpace I (p : M))) ≤
      T[JX; ⟨(p : M), p.2.1⟩] ⊓ T[JX'; ⟨(p : M), p.2.2⟩] := by
  let gX : (X ∩ X' : Set M) → X :=
    Set.codRestrict (Subtype.val : (X ∩ X' : Set M) → M) X (fun y => y.2.1)
  let gX' : (X ∩ X' : Set M) → X' :=
    Set.codRestrict (Subtype.val : (X ∩ X' : Set M) → M) X' (fun y => y.2.2)
  have hsubInt : MDifferentiableAt JXX' I (Subtype.val : (X ∩ X' : Set M) → M) p :=
    (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
      (I := I) (JS := JXX') (S := (X ∩ X' : Set M))).mdifferentiableAt (by simp)
  have hsubX : MDifferentiableAt JX I (Subtype.val : X → M) ⟨(p : M), p.2.1⟩ :=
    (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
      (I := I) (JS := JX) (S := X)).mdifferentiableAt (by simp)
  have hsubX' : MDifferentiableAt JX' I (Subtype.val : X' → M) ⟨(p : M), p.2.2⟩ :=
    (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
      (I := I) (JS := JX') (S := X')).mdifferentiableAt (by simp)
  have hgXdiff : MDifferentiableAt JXX' JX gX p := by
    -- Restrict the ambient inclusion to the first factor.
    simpa [gX] using
      mdifferentiableAt_toSubtype_of_isEmbeddedSubmanifold
        (I := I) (J := JX) (K := JXX') (S := X)
        (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
          (I := I) (JS := JXX') (S := (X ∩ X' : Set M)))
        (fun y => y.2.1) p
  have hgX'diff : MDifferentiableAt JXX' JX' gX' p := by
    -- Restrict the ambient inclusion to the second factor.
    simpa [gX'] using
      mdifferentiableAt_toSubtype_of_isEmbeddedSubmanifold
        (I := I) (J := JX') (K := JXX') (S := X')
        (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
          (I := I) (JS := JXX') (S := (X ∩ X' : Set M)))
        (fun y => y.2.2) p
  rw [show (T[JXX'; p] : Submodule ℝ (TangentSpace I (p : M))) =
      (mfderiv JXX' I (Subtype.val : (X ∩ X' : Set M) → M) p).range by rfl]
  intro v hv
  rcases LinearMap.mem_range.1 hv with ⟨w, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [show T[JX; ⟨(p : M), p.2.1⟩] =
      (mfderiv JX I (Subtype.val : X → M) ⟨(p : M), p.2.1⟩).range by rfl]
    refine LinearMap.mem_range.2 ⟨mfderiv JXX' JX gX p w, ?_⟩
    have hcomp :
        mfderiv JXX' I (Subtype.val : (X ∩ X' : Set M) → M) p =
          (mfderiv JX I (Subtype.val : X → M) ⟨(p : M), p.2.1⟩).comp
            (mfderiv JXX' JX gX p) := by
      -- Differentiate the factorization through the first inclusion.
      simpa [gX, Function.comp] using
        (mfderiv_comp (x := p) (g := (Subtype.val : X → M)) (f := gX) hsubX hgXdiff)
    simpa [LinearMap.comp_apply] using (congrArg (fun L => L w) hcomp).symm
  · rw [show T[JX'; ⟨(p : M), p.2.2⟩] =
      (mfderiv JX' I (Subtype.val : X' → M) ⟨(p : M), p.2.2⟩).range by rfl]
    refine LinearMap.mem_range.2 ⟨mfderiv JXX' JX' gX' p w, ?_⟩
    have hcomp :
        mfderiv JXX' I (Subtype.val : (X ∩ X' : Set M) → M) p =
          (mfderiv JX' I (Subtype.val : X' → M) ⟨(p : M), p.2.2⟩).comp
            (mfderiv JXX' JX' gX' p) := by
      -- Differentiate the factorization through the second inclusion.
      simpa [gX', Function.comp] using
        (mfderiv_comp (x := p) (g := (Subtype.val : X' → M)) (f := gX') hsubX' hgX'diff)
    simpa [LinearMap.comp_apply] using (congrArg (fun L => L w) hcomp).symm

-- The next helper isolates the pure linear-algebra quotient computation needed in the
-- transverse-intersection endgame.
/-- Helper for Problem 6-10: when `P ⊔ Q = ⊤`, the quotient by `P ⊓ Q` has the sum of the two
quotient dimensions. -/
lemma finrank_quotient_inf_eq_add_finrank_quotient_of_sup_eq_top
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (P Q : Submodule ℝ V) (hPQ : P ⊔ Q = ⊤) :
    Module.finrank ℝ (V ⧸ (P ⊓ Q)) =
      Module.finrank ℝ (V ⧸ P) + Module.finrank ℝ (V ⧸ Q) := by
  have hsup :
      Module.finrank ℝ ↥(P ⊔ Q) + Module.finrank ℝ ↥(P ⊓ Q) =
        Module.finrank ℝ ↥P + Module.finrank ℝ ↥Q := by
    simpa using Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [hPQ, finrank_top] at hsup
  have hleft :
      Module.finrank ℝ (V ⧸ (P ⊓ Q)) +
        (Module.finrank ℝ ↥P + Module.finrank ℝ ↥Q) =
          Module.finrank ℝ V + Module.finrank ℝ V := by
    -- Rewrite the sum of submodule dimensions using `P ⊔ Q = ⊤`, then rank-nullity for `P ⊓ Q`
    -- finishes the left-hand side.
    calc
      Module.finrank ℝ (V ⧸ (P ⊓ Q)) + (Module.finrank ℝ ↥P + Module.finrank ℝ ↥Q)
          = Module.finrank ℝ (V ⧸ (P ⊓ Q)) +
              (Module.finrank ℝ V + Module.finrank ℝ ↥(P ⊓ Q)) := by
                rw [hsup]
      _ = (Module.finrank ℝ (V ⧸ (P ⊓ Q)) + Module.finrank ℝ ↥(P ⊓ Q)) +
            Module.finrank ℝ V := by
              ac_rfl
      _ = Module.finrank ℝ V + Module.finrank ℝ V := by
            rw [Submodule.finrank_quotient_add_finrank (P ⊓ Q)]
  have hright :
      (Module.finrank ℝ (V ⧸ P) + Module.finrank ℝ (V ⧸ Q)) +
        (Module.finrank ℝ ↥P + Module.finrank ℝ ↥Q) =
          Module.finrank ℝ V + Module.finrank ℝ V := by
    -- Rank-nullity for `P` and `Q` separately computes the right-hand side.
    calc
      (Module.finrank ℝ (V ⧸ P) + Module.finrank ℝ (V ⧸ Q)) +
          (Module.finrank ℝ ↥P + Module.finrank ℝ ↥Q)
          = (Module.finrank ℝ (V ⧸ P) + Module.finrank ℝ ↥P) +
              (Module.finrank ℝ (V ⧸ Q) + Module.finrank ℝ ↥Q) := by
                ac_rfl
      _ = Module.finrank ℝ V + Module.finrank ℝ V := by
            rw [Submodule.finrank_quotient_add_finrank P,
              Submodule.finrank_quotient_add_finrank Q]
  -- Cancel the same `finrank P + finrank Q` term from both sides.
  exact Nat.add_right_cancel <| hleft.trans hright.symm

/-- Helper for Problem 6-10: the codimension of any chosen embedded structure on the transverse
intersection agrees with the codimension supplied by Theorem 6.30. -/
lemma intersectionCodimension_eq_add_of_transverse
    {JXX' : ModelWithCorners ℝ E''' H'''}
    [ChartedSpace H''' (X ∩ X' : Set M)] [IsManifold JXX' ∞ (X ∩ X' : Set M)]
    [IsEmbeddedSubmanifold I JXX' (X ∩ X' : Set M)]
    (htrans : SubmanifoldsIntersectTransversely I JX X JX' X')
    (p : (X ∩ X' : Set M)) :
    (inferInstance : IsEmbeddedSubmanifold I JXX' (X ∩ X' : Set M)).codimension =
      (inferInstance : IsEmbeddedSubmanifold I JX X).codimension +
        (inferInstance : IsEmbeddedSubmanifold I JX' X').codimension := by
  -- Unpack Theorem 6.30's witness structure on the same carrier.
  have hwitness :=
    transverse_intersection_has_embedded_submanifold_structure
      (IM := I) (JS := JX) (S := X) (JS' := JX') (S' := X') htrans
  dsimp only at hwitness
  rcases hwitness with ⟨cs, hs, hW, hcodW⟩
  letI : ChartedSpace
      (EuclideanSpace ℝ
        (Fin
          (Module.finrank ℝ E -
            ((inferInstance : IsEmbeddedSubmanifold I JX X).codimension +
              (inferInstance : IsEmbeddedSubmanifold I JX' X').codimension))))
      (X ∩ X' : Set M) := cs
  letI : IsManifold
      (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ
          (Fin
            (Module.finrank ℝ E -
              ((inferInstance : IsEmbeddedSubmanifold I JX X).codimension +
                (inferInstance : IsEmbeddedSubmanifold I JX' X').codimension)))))
      ∞ (X ∩ X' : Set M) := hs
  letI : IsEmbeddedSubmanifold
      I
      (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ
          (Fin
            (Module.finrank ℝ E -
              ((inferInstance : IsEmbeddedSubmanifold I JX X).codimension +
                (inferInstance : IsEmbeddedSubmanifold I JX' X').codimension)))))
      (X ∩ X' : Set M) := hW
  -- Transport codimension across the two embedded structures on the same intersection carrier.
  calc
    (inferInstance : IsEmbeddedSubmanifold I JXX' (X ∩ X' : Set M)).codimension
      = (inferInstance : IsEmbeddedSubmanifold
          I
          (modelWithCornersSelf ℝ
            (EuclideanSpace ℝ
              (Fin
                (Module.finrank ℝ E -
                  ((inferInstance : IsEmbeddedSubmanifold I JX X).codimension +
                    (inferInstance : IsEmbeddedSubmanifold I JX' X').codimension)))))
          (X ∩ X' : Set M)).codimension := by
            exact sameCarrierCodimension_eq_of_embeddedStructures
              (I := I)
              (J := JXX')
              (J' := modelWithCornersSelf ℝ
                (EuclideanSpace ℝ
                  (Fin
                    (Module.finrank ℝ E -
                      ((inferInstance : IsEmbeddedSubmanifold I JX X).codimension +
                        (inferInstance : IsEmbeddedSubmanifold I JX' X').codimension)))))
              (S := (X ∩ X' : Set M)) p
    _ = (inferInstance : IsEmbeddedSubmanifold I JX X).codimension +
          (inferInstance : IsEmbeddedSubmanifold I JX' X').codimension := hcodW

theorem tangentSpace_inter_eq_inf_of_transverse_aux
    {JXX' : ModelWithCorners ℝ E''' H'''}
    [ChartedSpace H''' (X ∩ X' : Set M)] [IsManifold JXX' ∞ (X ∩ X' : Set M)]
    [IsEmbeddedSubmanifold I JXX' (X ∩ X' : Set M)]
    (htrans : SubmanifoldsIntersectTransversely I JX X JX' X')
    (p : (X ∩ X' : Set M)) :
    let px : X := ⟨p, p.2.1⟩
    let px' : X' := ⟨p, p.2.2⟩
    (T[JXX'; p] : Submodule ℝ (TangentSpace I (p : M))) = T[JX; px] ⊓ T[JX'; px'] := by
  -- Route correction: isolate the pure quotient-by-inf dimension identity and compare codimensions,
  -- instead of repeating transversality arithmetic inline in the manifold proof.
  dsimp
  let px : X := ⟨(p : M), p.2.1⟩
  let px' : X' := ⟨(p : M), p.2.2⟩
  let _ : FiniteDimensional ℝ (TangentSpace I (p : M)) := by
    simpa using (inferInstance : FiniteDimensional ℝ E)
  have hle :
      (T[JXX'; p] : Submodule ℝ (TangentSpace I (p : M))) ≤
        T[JX; px] ⊓ T[JX'; px'] := by
    -- Tangent vectors to the intersection lie in both factor tangent spaces.
    simpa [px, px'] using
      intersectionTangentSpace_le_inf
        (I := I) (JX := JX) (X := X) (JX' := JX') (X' := X') (JXX' := JXX') p
  have hquotInf :
      Module.finrank ℝ
          ((TangentSpace I (p : M)) ⧸
            (T[JX; px] ⊓ T[JX'; px'] :
              Submodule ℝ (TangentSpace I (p : M)))) =
        Module.finrank ℝ ((TangentSpace I (p : M)) ⧸ T[JX; px]) +
          Module.finrank ℝ ((TangentSpace I (p : M)) ⧸ T[JX'; px']) := by
    -- The tangent-space transversality condition is exactly the `P ⊔ Q = ⊤` hypothesis.
    simpa using
      finrank_quotient_inf_eq_add_finrank_quotient_of_sup_eq_top
        (P := T[JX; px])
        (Q := T[JX'; px'])
        (V := TangentSpace I (p : M))
        (hPQ := by simpa [px, px'] using htrans p)
  have hquotEq :
      Module.finrank ℝ ((TangentSpace I (p : M)) ⧸ T[JXX'; p]) =
        Module.finrank ℝ
          ((TangentSpace I (p : M)) ⧸
            (T[JX; px] ⊓ T[JX'; px'] :
              Submodule ℝ (TangentSpace I (p : M)))) := by
    -- Both quotient dimensions are the common codimension coming from Theorem 6.30.
    calc
      Module.finrank ℝ ((TangentSpace I (p : M)) ⧸ T[JXX'; p])
        = (inferInstance : IsEmbeddedSubmanifold I JXX' (X ∩ X' : Set M)).codimension := by
            exact tangentQuotientFinrank_eq_codimension
              (I := I) (J := JXX') (S := (X ∩ X' : Set M)) p
      _ = (inferInstance : IsEmbeddedSubmanifold I JX X).codimension +
            (inferInstance : IsEmbeddedSubmanifold I JX' X').codimension := by
              exact intersectionCodimension_eq_add_of_transverse
                (I := I) (JX := JX) (X := X) (JX' := JX') (X' := X')
                (JXX' := JXX') htrans p
      _ = Module.finrank ℝ ((TangentSpace I (p : M)) ⧸ T[JX; px]) +
            Module.finrank ℝ ((TangentSpace I (p : M)) ⧸ T[JX'; px']) := by
              rw [← tangentQuotientFinrank_eq_codimension (I := I) (J := JX) (S := X) px,
                ← tangentQuotientFinrank_eq_codimension (I := I) (J := JX') (S := X') px']
      _ = Module.finrank ℝ
            ((TangentSpace I (p : M)) ⧸
              (T[JX; px] ⊓ T[JX'; px'] :
                Submodule ℝ (TangentSpace I (p : M)))) := by
              symm
              exact hquotInf
  have hleft :
      Module.finrank ℝ ((TangentSpace I (p : M)) ⧸
          (T[JX; px] ⊓ T[JX'; px'] :
            Submodule ℝ (TangentSpace I (p : M)))) +
        Module.finrank ℝ ↥(T[JXX'; p] : Submodule ℝ (TangentSpace I (p : M))) =
          Module.finrank ℝ (TangentSpace I (p : M)) := by
    -- Rewriting the quotient term aligns the chosen intersection tangent space with the infimum.
    simpa [hquotEq] using
      (Submodule.finrank_quotient_add_finrank
        (T[JXX'; p] : Submodule ℝ (TangentSpace I (p : M))))
  have hright :
      Module.finrank ℝ ((TangentSpace I (p : M)) ⧸
          (T[JX; px] ⊓ T[JX'; px'] :
            Submodule ℝ (TangentSpace I (p : M)))) +
        Module.finrank ℝ
          (T[JX; px] ⊓ T[JX'; px'] :
            Submodule ℝ (TangentSpace I (p : M))) =
          Module.finrank ℝ (TangentSpace I (p : M)) := by
    -- Rank-nullity for the infimum gives the comparison submodule's dimension formula.
    exact Submodule.finrank_quotient_add_finrank
      (T[JX; px] ⊓ T[JX'; px'] :
        Submodule ℝ (TangentSpace I (p : M)))
  have hfin :
      Module.finrank ℝ ↥(T[JXX'; p] : Submodule ℝ (TangentSpace I (p : M))) =
        Module.finrank ℝ
          (T[JX; px] ⊓ T[JX'; px'] :
            Submodule ℝ (TangentSpace I (p : M))) := by
    -- Cancel the common quotient term from the two rank-nullity formulas.
    exact Nat.add_left_cancel (hleft.trans hright.symm)
  -- Inclusion plus equality of dimensions forces equality of tangent submodules.
  simpa [px, px'] using (Submodule.eq_of_le_of_finrank_eq hle hfin)

/-- Helper for Problem 6-10: once the ambient manifold structure on `M` is available as an
ordinary term, the public intersection tangent-space statement is just the proved auxiliary
theorem. -/
lemma intersectionTangentSpaceEqInf_fromAmbientManifold
    {JXX' : ModelWithCorners ℝ E''' H'''}
    [ChartedSpace H''' (X ∩ X' : Set M)] [IsManifold JXX' ∞ (X ∩ X' : Set M)]
    [IsEmbeddedSubmanifold I JXX' (X ∩ X' : Set M)]
    (hIM : IsManifold I ∞ M)
    (htrans : SubmanifoldsIntersectTransversely I JX X JX' X')
    (p : (X ∩ X' : Set M)) :
    let px : X := ⟨p, p.2.1⟩
    let px' : X' := ⟨p, p.2.2⟩
    (T[JXX'; p] : Submodule ℝ (TangentSpace I (p : M))) = T[JX; px] ⊓ T[JX'; px'] := by
  -- Reinstall the ambient manifold structure as a local instance and reuse the closed auxiliary
  -- theorem without any new transversality work.
  let _ : IsManifold I ∞ M := hIM
  simpa using
    (tangentSpace_inter_eq_inf_of_transverse_aux
      (I := I) (JX := JX) (X := X) (JX' := JX') (X' := X') (JXX' := JXX') htrans p)

omit [IsManifold I ∞ M] in
/-- Helper for Problem 6-10: the public intersection tangent-space theorem can be reused under
`omit` once the ambient manifold structure is treated as an ordinary implicit argument. -/
lemma intersectionTangentSpaceEqInf_omitAux
    {hIM : IsManifold I ∞ M}
    {JXX' : ModelWithCorners ℝ E''' H'''}
    [ChartedSpace H''' (X ∩ X' : Set M)] [IsManifold JXX' ∞ (X ∩ X' : Set M)]
    [IsEmbeddedSubmanifold I JXX' (X ∩ X' : Set M)]
    (htrans : SubmanifoldsIntersectTransversely I JX X JX' X')
    (p : (X ∩ X' : Set M)) :
    let px : X := ⟨p, p.2.1⟩
    let px' : X' := ⟨p, p.2.2⟩
    (T[JXX'; p] : Submodule ℝ (TangentSpace I (p : M))) = T[JX; px] ⊓ T[JX'; px'] := by
  -- Reinstall the ambient manifold structure as an instance and reuse the closed wrapper lemma.
  let _ : IsManifold I ∞ M := hIM
  simpa using
    (intersectionTangentSpaceEqInf_fromAmbientManifold
      (I := I) (JX := JX) (X := X) (JX' := JX') (X' := X') (JXX' := JXX') hIM htrans p)

/-- Problem 6-10 (2): if the chosen embedded submanifold structures on `X` and `X'` intersect
transversely, and `X ∩ X'` carries a chosen embedded submanifold structure, then the tangent space
of `X ∩ X'` is the intersection of the tangent spaces of `X` and `X'`. -/
theorem tangentSpace_inter_eq_inf_of_transverse
    {JXX' : ModelWithCorners ℝ E''' H'''}
    [ChartedSpace H''' (X ∩ X' : Set M)] [IsManifold JXX' ∞ (X ∩ X' : Set M)]
    [IsEmbeddedSubmanifold I JXX' (X ∩ X' : Set M)]
    (htrans : SubmanifoldsIntersectTransversely I JX X JX' X')
    (p : (X ∩ X' : Set M)) :
    let px : X := ⟨p, p.2.1⟩
    let px' : X' := ⟨p, p.2.2⟩
    (T[JXX'; p] : Submodule ℝ (TangentSpace I (p : M))) = T[JX; px] ⊓ T[JX'; px'] := by
  -- Route correction: restoring the ambient manifold instance at this theorem boundary lets the
  -- already-proved omit-safe wrapper finish the intersection statement without new geometry.
  simpa using
    (intersectionTangentSpaceEqInf_omitAux
      (I := I) (JX := JX) (X := X) (JX' := JX') (X' := X') (JXX' := JXX')
      (hIM := inferInstance) htrans p)

end TransverseIntersectionTangentSpace
