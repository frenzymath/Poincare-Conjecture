import LeeSmoothLib.Ch05.Sec05_30.Definition_5_30_extra_2
import LeeSmoothLib.Ch05.Sec05_32.Corollary_5_30
import LeeSmoothLib.Ch05.Sec05_32.Definition_5_32_extra_2
import LeeSmoothLib.Ch06.Sec06_38.Definition_6_38_extra_2
import LeeSmoothLib.Ch06.Sec06_44.Definition_6_44_extra_1
import LeeSmoothLib.Ch06.Sec06_44.Definition_6_44_extra_2
import LeeSmoothLib.Ch06.Sec06_39.Theorem_6_10
import LeeSmoothLib.Ch06.Sec06_44.Theorem_6_30
import LeeSmoothLib.Ch06.Sec06_44.Theorem_6_32
-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Manifold Set
open scoped ContDiff Manifold

-- Semantic search note: `lean_leansearch` did not return a usable parametric-transversality
-- theorem, so this file follows the local Chapter 6 owners `IsSmoothFamily`,
-- `IsTransverseToSubmanifold`, and `has_measure_zero_in_manifold`.

section ParametricTransversality

universe uEM uEN uES uEX uEW uHM uHN uHS uHX uHW uM uN uS

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
variable {ES : Type uES} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
variable {EX : Type uEX} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
variable {EW : Type uEW} [NormedAddCommGroup EW] [NormedSpace ℝ EW]
variable [MeasurableSpace ES] [BorelSpace ES]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {HS : Type uHS} [TopologicalSpace HS]
variable {HX : Type uHX} [TopologicalSpace HX]
variable {HW : Type uHW} [TopologicalSpace HW]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {S : Type uS} [TopologicalSpace S] [ChartedSpace HS S]
variable {IM : ModelWithCorners ℝ EM HM} [IsManifold IM ∞ M]
variable {IN : ModelWithCorners ℝ EN HN} [IsManifold IN ∞ N]
variable {IS : ModelWithCorners ℝ ES HS} [IsManifold IS ∞ S]
variable {X : Set M}
variable {JX : ModelWithCorners ℝ EX HX}
variable {JW : ModelWithCorners ℝ EW HW}
variable [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold IM JX X]

/-- Helper for Theorem 6.35: differentiating the slice `F s` amounts to differentiating the
uncurried map `Function.uncurry F` after the vertical inclusion `N → S × N`, `p' ↦ (s, p')`. -/
private theorem sliceMfderiv_eq_uncurryMfderiv_compInr
    {F : S → N → M} (hF : ContMDiff (IS.prod IN) IM ∞ (Function.uncurry F)) (s : S) (p : N) :
    mfderiv IN IM (F s) p =
      (mfderiv (IS.prod IN) IM (Function.uncurry F) (s, p)).comp
        (ContinuousLinearMap.inr ℝ (TangentSpace IS s) (TangentSpace IN p)) := by
  -- Rewrite the slice as the uncurried family composed with the vertical inclusion.
  have hslice :
      Function.uncurry F ∘ (fun p' : N ↦ (s, p')) = F s := by
    funext p'
    rfl
  rw [← hslice]
  -- The chain rule reduces the derivative to the product-right derivative normalization.
  simpa [Function.comp, mfderiv_prod_right] using
    (mfderiv_comp
      (x := p)
      (g := Function.uncurry F)
      (f := fun p' : N ↦ (s, p'))
      (hF.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id))

/-- Helper for Theorem 6.35: the derivative of the restricted parameter projection
`w ↦ w.1.1 : (Function.uncurry F) ⁻¹' X → S` is the first-factor projection after the derivative of
the subtype inclusion into `S × N`. -/
private theorem parametricPreimageProjectionMfderiv_eq_fst_comp
    {F : S → N → M}
    [ChartedSpace HW ((Function.uncurry F) ⁻¹' X)]
    [IsManifold JW ∞ ((Function.uncurry F) ⁻¹' X)]
    [IsEmbeddedSubmanifold (IS.prod IN) JW ((Function.uncurry F) ⁻¹' X)]
    (w : (Function.uncurry F) ⁻¹' X) :
    mfderiv JW IS (fun u : (Function.uncurry F) ⁻¹' X ↦ u.1.1) w =
      (ContinuousLinearMap.fst ℝ (TangentSpace IS w.1.1) (TangentSpace IN w.1.2)).comp
        (mfderiv JW (IS.prod IN)
          (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N) w) := by
  -- View the restricted projection as `Prod.fst ∘ Subtype.val`.
  have hproj :
      Prod.fst ∘ (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N) =
        (fun u : (Function.uncurry F) ⁻¹' X ↦ u.1.1) := by
    funext u
    rfl
  rw [← hproj]
  -- The chain rule then exposes the desired first-factor projection.
  simpa [Function.comp, mfderiv_fst] using
    (mfderiv_comp
      (x := w)
      (g := Prod.fst)
      (f := (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N))
      (contMDiff_fst.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
      ((subtypeVal_contMDiff_of_isEmbeddedSubmanifold
        (I := IS.prod IN) (JS := JW) (S := (Function.uncurry F) ⁻¹' X)).mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)))

/-- Helper for Theorem 6.35: every tangent vector to `(Function.uncurry F) ⁻¹' X` maps under the
ambient derivative of `Function.uncurry F` into the tangent space of `X`. -/
private theorem preimageSubtypeValRange_le_targetComap_at_parametricPoint
    {F : S → N → M}
    (hF : ContMDiff (IS.prod IN) IM ∞ (Function.uncurry F))
    [ChartedSpace HW ((Function.uncurry F) ⁻¹' X)]
    [IsManifold JW ∞ ((Function.uncurry F) ⁻¹' X)]
    [IsEmbeddedSubmanifold (IS.prod IN) JW ((Function.uncurry F) ⁻¹' X)]
    (w : (Function.uncurry F) ⁻¹' X) :
    let x : X := ⟨Function.uncurry F w, w.2⟩
    (mfderiv JW (IS.prod IN)
      (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N) w).range ≤
        (T[JX; x]).comap (mfderiv (IS.prod IN) IM (Function.uncurry F) w).toLinearMap := by
  dsimp
  let g : (Function.uncurry F) ⁻¹' X → X :=
    Set.codRestrict (fun y : (Function.uncurry F) ⁻¹' X ↦ Function.uncurry F y) X (fun y ↦ y.2)
  have hsubPre :
      MDifferentiableAt JW (IS.prod IN)
        (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N) w :=
    (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
      (I := IS.prod IN) (JS := JW) (S := (Function.uncurry F) ⁻¹' X)).mdifferentiableAt
      (by simp)
  have hsubX :
      MDifferentiableAt JX IM (Subtype.val : X → M) ⟨Function.uncurry F w, w.2⟩ :=
    (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
      (I := IM) (JS := JX) (S := X)).mdifferentiableAt
      (by simp)
  have hFpre : ContMDiff JW IM ∞ (fun y : (Function.uncurry F) ⁻¹' X ↦ Function.uncurry F y) := by
    simpa [Function.comp] using
      hF.comp
        (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
          (I := IS.prod IN) (JS := JW) (S := (Function.uncurry F) ⁻¹' X))
  have hgdiff : MDifferentiableAt JW JX g w := by
    let y : X := g w
    let hImm : IsImmersionAt JX IM ⊤ (Subtype.val : X → M) y :=
      IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val.isImmersion.isImmersionAt y
    let e : OpenPartialHomeomorph ((Function.uncurry F) ⁻¹' X) HW := chartAt HW w
    let w' : EW := e.extend JW w
    have hdom :
        hImm.domChart ∈ IsManifold.maximalAtlas JX 1 X :=
      IsManifold.maximalAtlas_subset_of_le
        (I := JX) (M := X) (m := 1) (n := ⊤) (by simp) hImm.domChart_mem_maximalAtlas
    have hcod :
        hImm.codChart ∈ IsManifold.maximalAtlas IM 1 M :=
      IsManifold.maximalAtlas_subset_of_le
        (I := IM) (M := M) (m := 1) (n := ⊤) (by simp) hImm.codChart_mem_maximalAtlas
    have hcont : ContinuousAt g w := (hFpre.continuous.continuousAt.codRestrict (fun y ↦ y.2))
    have hw : w ∈ e.source := mem_chart_source HW w
    have hy : g w ∈ hImm.domChart.source := hImm.mem_domChart_source
    have hy' : Function.uncurry F w ∈ hImm.codChart.source := hImm.mem_codChart_source
    letI : IsManifold JW 1 ((Function.uncurry F) ⁻¹' X) :=
      IsManifold.of_le (I := JW) (m := 1) (n := ∞) (by simp)
    letI : IsManifold JX 1 X := IsManifold.of_le (I := JX) (m := 1) (n := ∞) (by simp)
    have hiff :
        MDifferentiableAt JW JX g w ↔
          ContinuousAt g w ∧
            DifferentiableWithinAt ℝ ((hImm.domChart.extend JX) ∘ g ∘ (e.extend JW).symm)
              (Set.range JW) w' := by
      simpa [mdifferentiableWithinAt_univ, continuousWithinAt_univ, Set.preimage_univ,
        Set.univ_inter, w'] using
        (mdifferentiableWithinAt_iff_of_mem_maximalAtlas
          (I := JW) (I' := JX) (f := g) (s := Set.univ) (x := w) (e := e) (e' := hImm.domChart)
          (IsManifold.chart_mem_maximalAtlas w) hdom hw hy)
    rw [hiff]
    refine ⟨hcont, ?_⟩
    have hFwithin :
        MDifferentiableWithinAt JW IM (fun y : (Function.uncurry F) ⁻¹' X ↦ Function.uncurry F y)
          Set.univ w := by
      simpa [mdifferentiableWithinAt_univ] using
        hFpre.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hambient :
        DifferentiableWithinAt ℝ
          ((hImm.codChart.extend IM) ∘ (fun y : (Function.uncurry F) ⁻¹' X ↦ Function.uncurry F y) ∘
            (e.extend JW).symm)
          (Set.range JW) w' := by
      rw [mdifferentiableWithinAt_iff_of_mem_maximalAtlas
        (I := JW) (I' := IM) (f := fun y : (Function.uncurry F) ⁻¹' X ↦ Function.uncurry F y)
        (s := Set.univ) (x := w) (e := e) (e' := hImm.codChart)
        (IsManifold.chart_mem_maximalAtlas w) hcod hw hy',
        continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter] at hFwithin
      simpa [w'] using hFwithin.2
    have hproj :
        Differentiable ℝ (fun v ↦ (hImm.equiv.symm v).1) := by
      simpa using
        (contDiff_fst.comp hImm.equiv.symm.contDiff).differentiable
          (by simp : (⊤ : ℕ∞ω) ≠ 0)
    have hprojWithin :
        DifferentiableWithinAt ℝ (fun v ↦ (hImm.equiv.symm v).1) Set.univ
          (((hImm.codChart.extend IM) ∘
              (fun y : (Function.uncurry F) ⁻¹' X ↦ Function.uncurry F y) ∘
              (e.extend JW).symm) w') :=
      (hproj _).differentiableWithinAt
    have hcomp :
        DifferentiableWithinAt ℝ
          ((fun v ↦ (hImm.equiv.symm v).1) ∘
            (hImm.codChart.extend IM) ∘
            (fun y : (Function.uncurry F) ⁻¹' X ↦ Function.uncurry F y) ∘
            (e.extend JW).symm)
          (Set.range JW) w' := by
      exact hprojWithin.comp w' hambient (by intro z hz; simp)
    have hsource_mem : g ⁻¹' hImm.domChart.source ∈ nhds w := by
      have : hImm.domChart.source ∈ nhds (g w) :=
        hImm.domChart.open_source.mem_nhds hy
      exact hcont.preimage_mem_nhds this
    have hset_mem :
        (e.extend JW).symm ⁻¹' (g ⁻¹' hImm.domChart.source) ∈ nhdsWithin w' (Set.range JW) := by
      simpa [e, w', nhdsWithin_univ] using
        e.extend_preimage_mem_nhdsWithin (I := JW) (s := Set.univ) (t := g ⁻¹' hImm.domChart.source)
          hw (by simpa [nhdsWithin_univ] using hsource_mem)
    have heq :
        ((hImm.domChart.extend JX) ∘ g ∘ (e.extend JW).symm)
          =ᶠ[nhdsWithin w' (Set.range JW)]
            ((fun v ↦ (hImm.equiv.symm v).1) ∘
              (hImm.codChart.extend IM) ∘
              (fun y : (Function.uncurry F) ⁻¹' X ↦ Function.uncurry F y) ∘
              (e.extend JW).symm) := by
      refine Filter.eventuallyEq_of_mem hset_mem ?_
      intro z hz
      have hz_target :
          hImm.domChart.extend JX
              (Set.codRestrict (fun y : (Function.uncurry F) ⁻¹' X ↦ Function.uncurry F y)
                X (fun y ↦ y.2) ((e.extend JW).symm z)) ∈
            (hImm.domChart.extend JX).target :=
        (hImm.domChart.extend JX).map_source <| by
          simpa [g, Function.comp, OpenPartialHomeomorph.extend_coe] using hz
      simpa [Function.comp, g, OpenPartialHomeomorph.extend_coe,
        hImm.domChart.left_inv ((by simpa [g, OpenPartialHomeomorph.extend_coe] using hz) : _)] using
        (congrArg (fun v ↦ Prod.fst (hImm.equiv.symm v)) (hImm.writtenInCharts hz_target)).symm
    have hw'_target : w' ∈ (e.extend JW).target := (e.extend JW).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using hw
    have hw'_range : w' ∈ Set.range JW :=
      e.extend_target_subset_range hw'_target
    exact hcomp.congr_of_eventuallyEq_of_mem heq hw'_range
  intro v hv
  rcases LinearMap.mem_range.1 hv with ⟨u, rfl⟩
  let x : X := ⟨Function.uncurry F w, w.2⟩
  change (mfderiv (IS.prod IN) IM (Function.uncurry F) w)
      ((mfderiv JW (IS.prod IN)
        (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N) w) u) ∈ T[JX; x]
  rw [show T[JX; x] = (mfderiv JX IM (Subtype.val : X → M) x).range by rfl]
  refine LinearMap.mem_range.2 ?_
  refine ⟨mfderiv JW JX g w u, ?_⟩
  have hfg :
      Function.uncurry F ∘
          (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N) =
        (Subtype.val : X → M) ∘ g := by
    funext y
    rfl
  have hcomp :
      (mfderiv (IS.prod IN) IM (Function.uncurry F) w).comp
          (mfderiv JW (IS.prod IN)
            (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N) w) =
        (mfderiv JX IM (Subtype.val : X → M) x).comp (mfderiv JW JX g w) := by
    have hleft :
        mfderiv JW IM
            (Function.uncurry F ∘
              (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N)) w =
          (mfderiv (IS.prod IN) IM (Function.uncurry F) w).comp
            (mfderiv JW (IS.prod IN)
              (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N) w) := by
      simpa [Function.comp] using
        (mfderiv_comp
          (x := w) (g := Function.uncurry F)
          (f := (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N))
          (hF.mdifferentiableAt (by simp)) hsubPre)
    have hmid :
        mfderiv JW IM
            (Function.uncurry F ∘
              (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N)) w =
          mfderiv JW IM ((Subtype.val : X → M) ∘ g) w := by
      rw [hfg]
    have hright :
        mfderiv JW IM ((Subtype.val : X → M) ∘ g) w =
          (mfderiv JX IM (Subtype.val : X → M) x).comp (mfderiv JW JX g w) := by
      simpa [Function.comp] using
        (mfderiv_comp (x := w) (g := (Subtype.val : X → M)) (f := g) hsubX hgdiff)
    exact hleft.symm.trans (hmid.trans hright)
  simpa [LinearMap.comp_apply] using (congrArg (fun L ↦ L u) hcomp).symm

/-- Helper for Theorem 6.35: a nonempty embedded submanifold of a finite-dimensional ambient
manifold has finite-dimensional model space. -/
private theorem finiteDimensionalModelSpace_of_embeddedSubmanifold_point
    (hX : IsEmbeddedSubmanifold IM JX X := inferInstance)
    (x : X) :
    FiniteDimensional ℝ EX := by
  let hImm : Manifold.IsImmersionAt JX IM ⊤ (Subtype.val : X → M) x :=
    hX.isSmoothEmbedding_subtype_val.isImmersion.isImmersionAt x
  -- The immersion normal form identifies `EX × hImm.complement` with the ambient model space.
  let _ : FiniteDimensional ℝ (EX × hImm.complement) :=
    FiniteDimensional.of_injective hImm.equiv.toLinearMap hImm.equiv.injective
  -- Projecting to the first factor shows that the submanifold model space is finite-dimensional.
  exact
    FiniteDimensional.of_injective
      (ContinuousLinearMap.inl ℝ EX hImm.complement).toLinearMap
      LinearMap.inl_injective

/-- Helper for Theorem 6.35: if a lifted tangent space projects surjectively to the parameter
direction and maps into `TX` under `A`, then transversality of `A` implies transversality of the
slice derivative `A ∘ inr`. -/
private theorem supRange_slice_of_transverse_and_surjective_parametricLift
    {U V₁ V₂ W : Type*}
    [AddCommGroup U] [Module ℝ U]
    [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂]
    [AddCommGroup W] [Module ℝ W]
    (A : V₁ × V₂ →ₗ[ℝ] W) (B : U →ₗ[ℝ] V₁ × V₂) (TX : Submodule ℝ W)
    (htrans : A.range ⊔ TX = ⊤)
    (hB : B.range ≤ TX.comap A)
    (hsurj : Function.Surjective ((LinearMap.fst ℝ V₁ V₂).comp B)) :
    (A.comp (LinearMap.inr ℝ V₁ V₂)).range ⊔ TX = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have hw : w ∈ A.range ⊔ TX := by
    rw [htrans]
    trivial
  rcases Submodule.mem_sup.mp hw with ⟨a, ha, t, ht, rfl⟩
  rcases LinearMap.mem_range.mp ha with ⟨z, rfl⟩
  rcases hsurj z.1 with ⟨u, hu⟩
  have hBu : B u ∈ TX.comap A :=
    hB (LinearMap.mem_range_self _ u)
  have hABu : A (B u) ∈ TX := hBu
  have hfst : (B u).1 = z.1 := by
    simpa [LinearMap.comp_apply] using hu
  have hdecomp :
      A z = A (B u) + (A.comp (LinearMap.inr ℝ V₁ V₂)) (z.2 - (B u).2) := by
    have hpair : ((B u).1, z.2) = B u + (0, z.2 - (B u).2) := by
      apply Prod.ext
      · simp
      · simp
    calc
      A z = A ((B u).1, z.2) := by rw [hfst]
      _ = A (B u + (0, z.2 - (B u).2)) := by rw [hpair]
      _ = A (B u) + A (0, z.2 - (B u).2) := by rw [map_add]
      _ = A (B u) + (A.comp (LinearMap.inr ℝ V₁ V₂)) (z.2 - (B u).2) := by
        simp [LinearMap.comp_apply, LinearMap.inr_apply]
  refine Submodule.mem_sup.mpr ?_
  refine ⟨(A.comp (LinearMap.inr ℝ V₁ V₂)) (z.2 - (B u).2), ?_, A (B u) + t, ?_, ?_⟩
  · exact LinearMap.mem_range_self _ _
  · exact TX.add_mem hABu ht
  · simp [hdecomp, add_left_comm, add_comm]

/-- Helper for Theorem 6.35: if the natural projection from the transverse preimage
`(Function.uncurry F) ⁻¹' X ⊆ S × N` to the parameter manifold `S` has `s` as a regular value,
then the slice `F s : N → M` is transverse to `X`. -/
theorem isTransverseToSubmanifold_of_isRegularValue_parametricPreimageProjection
    {F : S → N → M}
    (htrans : IsTransverseToSubmanifold IM (IS.prod IN) JX X (Function.uncurry F))
    [ChartedSpace HW ((Function.uncurry F) ⁻¹' X)]
    [IsManifold JW ∞ ((Function.uncurry F) ⁻¹' X)]
    [IsEmbeddedSubmanifold (IS.prod IN) JW ((Function.uncurry F) ⁻¹' X)]
    {s : S}
    (hs : IsRegularValue JW IS (fun w : (Function.uncurry F) ⁻¹' X ↦ w.1.1) s) :
    IsTransverseToSubmanifold IM IN JX X (F s) := by
  have hFamily : IsSmoothFamily IM IS IN F := htrans.contMDiff
  refine ⟨hFamily.contMDiff_slice s, ?_⟩
  intro p
  let w : (Function.uncurry F) ⁻¹' X := ⟨(s, p), p.2⟩
  let x : X := ⟨F s p, p.2⟩
  have htransw :
      (mfderiv (IS.prod IN) IM (Function.uncurry F) w).range ⊔
        T[JX; x] = ⊤ := by
    simpa [w, x] using htrans.tangent_sup_eq_top w
  have hBw :
      (mfderiv JW (IS.prod IN)
        (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N) w).range ≤
          (T[JX; x]).comap
            (mfderiv (IS.prod IN) IM (Function.uncurry F) w).toLinearMap := by
    simpa [w, x] using
      preimageSubtypeValRange_le_targetComap_at_parametricPoint
        (F := F) (JW := JW) htrans.contMDiff w
  have hsurjProjection :
      Function.Surjective
        (mfderiv JW IS (fun u : (Function.uncurry F) ⁻¹' X ↦ u.1.1) w) :=
    hs w rfl
  have hsurjFst :
      Function.Surjective
        ((ContinuousLinearMap.fst ℝ (TangentSpace IS s) (TangentSpace IN (p : N))).comp
          (mfderiv JW (IS.prod IN)
            (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N) w)) := by
    rw [← parametricPreimageProjectionMfderiv_eq_fst_comp (F := F) (JW := JW) (w := w)]
    exact hsurjProjection
  have hslice :
      ((mfderiv (IS.prod IN) IM (Function.uncurry F) w).comp
        (ContinuousLinearMap.inr ℝ (TangentSpace IS s) (TangentSpace IN (p : N)))).range ⊔
          T[JX; x] = ⊤ := by
    exact
      supRange_slice_of_transverse_and_surjective_parametricLift
        (A := (mfderiv (IS.prod IN) IM (Function.uncurry F) w).toLinearMap)
        (B := (mfderiv JW (IS.prod IN)
          (Subtype.val : (Function.uncurry F) ⁻¹' X → S × N) w).toLinearMap)
        (TX := T[JX; x])
        htransw hBw hsurjFst
  simpa [w, x, sliceMfderiv_eq_uncurryMfderiv_compInr (F := F) htrans.contMDiff s (p : N)] using
    hslice

/-- Helper for Theorem 6.35: the restricted parameter projection on the transverse preimage is a
smooth map because it is the ambient first projection composed with the subtype inclusion. -/
private theorem parametricPreimageProjection_contMDiff
    {F : S → N → M}
    [ChartedSpace HW ((Function.uncurry F) ⁻¹' X)]
    [IsManifold JW ∞ ((Function.uncurry F) ⁻¹' X)]
    [IsEmbeddedSubmanifold (IS.prod IN) JW ((Function.uncurry F) ⁻¹' X)] :
    ContMDiff JW IS ∞ (fun w : (Function.uncurry F) ⁻¹' X ↦ w.1.1) := by
  -- The restricted projection is `Prod.fst` after the smooth subtype inclusion.
  simpa [Function.comp] using
    contMDiff_fst.comp
      (subtypeVal_contMDiff_of_isEmbeddedSubmanifold
        (I := IS.prod IN) (JS := JW) (S := (Function.uncurry F) ⁻¹' X))

/-- Helper for Theorem 6.35: a parameter with nontransverse slice is a critical value of the
restricted projection from the transverse preimage `(Function.uncurry F) ⁻¹' X` to `S`. -/
private theorem notTransverseSlice_subset_criticalValues_parametricProjection
    {F : S → N → M}
    (htrans : IsTransverseToSubmanifold IM (IS.prod IN) JX X (Function.uncurry F))
    [ChartedSpace HW ((Function.uncurry F) ⁻¹' X)]
    [IsManifold JW ∞ ((Function.uncurry F) ⁻¹' X)]
    [IsEmbeddedSubmanifold (IS.prod IN) JW ((Function.uncurry F) ⁻¹' X)] :
    {s : S | ¬ IsTransverseToSubmanifold IM IN JX X (F s)} ⊆
      {s : S | IsCriticalValue JW IS (fun w : (Function.uncurry F) ⁻¹' X ↦ w.1.1) s} := by
  intro s hsnot
  -- A regular value would force slice transversality, so nontransversality means critical value.
  simpa [Manifold.IsCriticalValue] using
    (fun hsreg ↦
      hsnot <|
        isTransverseToSubmanifold_of_isRegularValue_parametricPreimageProjection
          (F := F) (JW := JW) htrans hsreg)

variable [T2Space N] [SecondCountableTopology N]
variable [T2Space S] [SecondCountableTopology S]

/-- Theorem 6.35 (Parametric Transversality Theorem): if `F : S → N → M` is a smooth family and
its uncurried map `S × N → M` is transverse to the embedded submanifold `X ⊆ M`, then the set of
parameters `s : S` for which the slice `F s : N → M` fails to be transverse to `X` has measure
zero in `S`. Equivalently, the transverse slices occur for almost every parameter. -/
theorem parametric_transversality_setOf_not_transverse_has_measure_zero_in_manifold
    {F : S → N → M} (hF : IsSmoothFamily IM IS IN F)
    (htrans : IsTransverseToSubmanifold IM (IS.prod IN) JX X (Function.uncurry F)) :
    has_measure_zero_in_manifold IS {s : S | ¬ IsTransverseToSubmanifold IM IN JX X (F s)} :=
by
  classical
  by_cases hXempty : X = ∅
  · have hAllTransverse : ∀ s : S, IsTransverseToSubmanifold IM IN JX X (F s) := by
      intro s
      refine ⟨hF.contMDiff_slice s, ?_⟩
      intro p
      exact False.elim (by simpa [hXempty] using p.2)
    have hbadEmpty :
        {s : S | ¬ IsTransverseToSubmanifold IM IN JX X (F s)} = ∅ := by
      ext s
      simp [hAllTransverse s]
    intro μ hμ e he
    simp [hbadEmpty]
  · let hX : IsEmbeddedSubmanifold IM JX X := inferInstance
    obtain ⟨x, hx⟩ : Set.Nonempty X := Set.nonempty_iff_ne_empty.mpr hXempty
    let xX : X := ⟨x, hx⟩
    let _ : FiniteDimensional ℝ EX :=
      finiteDimensionalModelSpace_of_embeddedSubmanifold_point
        (IM := IM) (JX := JX) (X := X) (hX := hX) (x := xX)
    let W : Set (S × N) := (Function.uncurry F) ⁻¹' X
    let EW :=
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (ES × EN) - hX.codimension))
    let LW : ModelWithCorners ℝ EW EW := modelWithCornersSelf ℝ EW
    obtain ⟨csW, hEmbW, hsW, _⟩ := by
      simpa [W, EW, LW] using
        transverse_preimage_has_embedded_submanifold_structure
          (IN := IS.prod IN) (IM := IM) (JS := JX) (S := X)
          (F := Function.uncurry F) htrans
    let _ : ChartedSpace EW W := csW
    let _ : IsManifold LW ∞ W := hsW
    let _ : IsEmbeddedSubmanifold (IS.prod IN) LW W := hEmbW
    let _ : T2Space W := inferInstance
    let _ : SecondCountableTopology W := inferInstance
    have hsubset :
        {s : S | ¬ IsTransverseToSubmanifold IM IN JX X (F s)} ⊆
          {s : S | IsCriticalValue LW IS (fun w : W ↦ w.1.1) s} := by
      simpa [W] using
        notTransverseSlice_subset_criticalValues_parametricProjection
          (F := F) (IN := IN) (JW := LW) htrans
    have hprojContMDiff : ContMDiff LW IS ∞ (fun w : W ↦ w.1.1) := by
      simpa [W] using
        parametricPreimageProjection_contMDiff (F := F) (IN := IN) (JW := LW)
    have hcritical :
        has_measure_zero_in_manifold IS
          {s : S | IsCriticalValue LW IS (fun w : W ↦ w.1.1) s} :=
      critical_values_has_measure_zero_in_manifold_of_contMDiff hprojContMDiff
    intro μ hμ e he
    refine measure_mono_null ?_ (hcritical μ hμ e he)
    intro y hy
    rcases hy with ⟨s, hs, rfl⟩
    exact ⟨s, ⟨hsubset hs.1, hs.2⟩, rfl⟩

end ParametricTransversality
