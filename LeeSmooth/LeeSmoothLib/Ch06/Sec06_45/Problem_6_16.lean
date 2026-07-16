import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Compactness.Compact
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5
import LeeSmoothLib.Ch04.Sec04_21.Proposition_4_1
import LeeSmoothLib.Ch04.Sec04_24.Proposition_4_22
import LeeSmoothLib.Ch04.Sec04_24.Theorem_4_25
import LeeSmoothLib.Ch04.Sec04_25.Proposition_4_28
import LeeSmoothLib.Ch05.Sec05_32.Definition_5_32_extra_2
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_2
import LeeSmoothLib.Ch05.Sec05_33.Theorem_5_33
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_38
import LeeSmoothLib.Ch05.Sec05_37.Problem_5_7
import LeeSmoothLib.Ch06.Sec06_44.Definition_6_44_extra_1
import LeeSmoothLib.Ch06.Sec06_44.Definition_6_44_extra_2
import LeeSmoothLib.Ch06.Sec06_45.StableMapClass
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Set Manifold
open Topology.IsInducing

local notation "𝕜" => ℝ

universe u𝕜 uE uE' uH uH' uN uM uS uES uHS

section Problem616Local

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ N] [BoundarylessManifold I N]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ M] [BoundarylessManifold J M]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ N] [IsManifold J ∞ M] in
omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: differentiating the slice `F s` is the same as differentiating the
uncurried family after the vertical inclusion `x ↦ (s, x)`. -/
lemma sliceMfderiv_eq_uncurryMfderiv_compInr
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) (s : S) (x : N) :
    mfderiv I J (F s) x =
      (mfderiv (IS.prod I) J (Function.uncurry F) (s, x)).comp
        (ContinuousLinearMap.inr 𝕜 (TangentSpace IS s) (TangentSpace I x)) := by
  -- Rewrite the slice as the uncurried family composed with the vertical inclusion.
  have hslice :
      Function.uncurry F ∘ (fun x' : N ↦ (s, x')) = F s := by
    funext x'
    rfl
  rw [← hslice]
  -- The chain rule identifies the derivative with the right-factor product derivative.
  simpa [Function.comp, mfderiv_prod_right] using
    (mfderiv_comp x
      (hF.contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id))

/-- Helper lemma: if a product-valued derivative has first component equal to the
identity on the parameter factor, then injectivity is equivalent to injectivity of its vertical
component. -/
lemma injective_iff_injective_verticalPart_of_fst_comp_eq_fst
    {U : Type _} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    {V : Type _} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {W : Type _} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (A : U × V →L[𝕜] U × W)
    (hfst :
      (ContinuousLinearMap.fst 𝕜 U W).comp A = ContinuousLinearMap.fst 𝕜 U V) :
    Function.Injective A ↔
      Function.Injective
        (((ContinuousLinearMap.snd 𝕜 U W).comp A).comp
          (ContinuousLinearMap.inr 𝕜 U V)) := by
  let B : V →L[𝕜] W :=
    (((ContinuousLinearMap.snd 𝕜 U W).comp A).comp (ContinuousLinearMap.inr 𝕜 U V))
  constructor
  · intro hA v₁ v₂ hv
    -- Equal vertical parts force equality of the pure-vertical images under `A`.
    have hEq : A (0, v₁) = A (0, v₂) := by
      ext
      · have hfst₁ :
            Prod.fst (A (0, v₁)) = 0 := by
          simpa [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hfst (0, v₁)
        have hfst₂ :
            Prod.fst (A (0, v₂)) = 0 := by
          simpa [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hfst (0, v₂)
        simp [hfst₁, hfst₂]
      · simpa [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using hv
    have hPair : ((0 : U), v₁) = ((0 : U), v₂) := hA hEq
    simpa using congrArg Prod.snd hPair
  · intro hVert
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ hEq
    have hu : u₁ = u₂ := by
      calc
        u₁ = Prod.fst (A (u₁, v₁)) := by
          symm
          simpa [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hfst (u₁, v₁)
        _ = Prod.fst (A (u₂, v₂)) := by simpa using congrArg Prod.fst hEq
        _ = u₂ := by
          simpa [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hfst (u₂, v₂)
    subst u₂
    have hZero : A ((0 : U), v₁ - v₂) = 0 := by
      calc
        A ((0 : U), v₁ - v₂) = A ((u₁, v₁) - (u₁, v₂)) := by simp
        _ = A (u₁, v₁) - A (u₁, v₂) := by simpa using A.map_sub (u₁, v₁) (u₁, v₂)
        _ = 0 := by simp [hEq]
    have hVertZero : B (v₁ - v₂) = B 0 := by
      have hA0 : A ((0 : U), (0 : V)) = (0 : U × W) := by
        exact A.map_zero
      have hA0snd : Prod.snd (A ((0 : U), (0 : V))) = 0 := by
        simpa using congrArg Prod.snd hA0
      calc
        B (v₁ - v₂) = Prod.snd (A ((0 : U), v₁ - v₂)) := by
          simp [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
        _ = 0 := by simpa using congrArg Prod.snd hZero
        _ = Prod.snd (A ((0 : U), (0 : V))) := hA0snd.symm
        _ = B 0 := by simp [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    have hv : v₁ - v₂ = 0 := hVert hVertZero
    have hv' : v₁ = v₂ := sub_eq_zero.mp hv
    ext <;> simp [hv']

/-- Helper lemma: if a product-valued derivative has first component equal to the
identity on the parameter factor, then surjectivity is equivalent to surjectivity of its vertical
component. -/
lemma surjective_iff_surjective_verticalPart_of_fst_comp_eq_fst
    {U : Type _} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    {V : Type _} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {W : Type _} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (A : U × V →L[𝕜] U × W)
    (hfst :
      (ContinuousLinearMap.fst 𝕜 U W).comp A = ContinuousLinearMap.fst 𝕜 U V) :
    Function.Surjective A ↔
      Function.Surjective
        (((ContinuousLinearMap.snd 𝕜 U W).comp A).comp
          (ContinuousLinearMap.inr 𝕜 U V)) := by
  let B : V →L[𝕜] W :=
    (((ContinuousLinearMap.snd 𝕜 U W).comp A).comp (ContinuousLinearMap.inr 𝕜 U V))
  constructor
  · intro hA w
    -- Surjectivity of `A` on the pure-vertical target gives surjectivity of the vertical part.
    rcases hA (0, w) with ⟨⟨u, v⟩, huv⟩
    have hu : u = 0 := by
      have hfst_u :
          Prod.fst (A (u, v)) = u := by
        simpa [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hfst (u, v)
      have hfst_zero : Prod.fst (A (u, v)) = 0 := by
        simpa using congrArg Prod.fst huv
      exact hfst_u.symm.trans hfst_zero
    subst hu
    refine ⟨v, ?_⟩
    simpa [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using
      congrArg Prod.snd huv
  · intro hVert z
    rcases z with ⟨u, w⟩
    let correction : W := w - Prod.snd (A (u, 0))
    rcases hVert correction with ⟨v, hv⟩
    refine ⟨(u, v), ?_⟩
    -- Split `A (u, v)` into its horizontal part `A (u, 0)` and the vertical correction `A (0, v)`.
    have hsum : A (u, v) = A (u, 0) + A (0, v) := by
      calc
        A (u, v) = A ((u, 0) + (0, v)) := by simp
        _ = A (u, 0) + A (0, v) := by simpa using A.map_add (u, 0) (0, v)
    ext
    · -- The first component is fixed by the `fst ∘ A = fst` normalization.
      have hfst_uv :
          Prod.fst (A (u, v)) = u := by
        simpa [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hfst (u, v)
      exact hfst_uv
    · -- The chosen correction fills exactly the missing second-coordinate displacement.
      have hv' :
          Prod.snd (A (0, v)) = correction := by
        simpa [B, correction, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.inr_apply] using hv
      calc
        Prod.snd (A (u, v)) = Prod.snd (A (u, 0) + A (0, v)) := by
          simpa using congrArg Prod.snd hsum
        _ = Prod.snd (A (u, 0)) + Prod.snd (A (0, v)) := rfl
        _ = Prod.snd (A (u, 0)) + correction := by rw [hv']
        _ = w := by simp [correction]

/-- Helper lemma: if an open subset `W ⊆ S × N` contains the whole fiber
`{s0} ×ˢ univ`, compactness of `N` shrinks `W` to a product neighborhood of that fiber. -/
lemma parameterNeighborhood_of_openFiberLocus
    {S : Type _} [TopologicalSpace S] [CompactSpace N] {W : Set (S × N)} {s0 : S}
    (hW : IsOpen W) (hFiber : ({s0} : Set S) ×ˢ (Set.univ : Set N) ⊆ W) :
    ∃ U : Set S, IsOpen U ∧ s0 ∈ U ∧ U ×ˢ (Set.univ : Set N) ⊆ W := by
  -- Use the generalized tube lemma on the compact singleton fiber.
  obtain ⟨U, V, hUOpen, hVOpen, hs0U, hV, hUV⟩ :=
    generalized_tube_lemma (isCompact_singleton : IsCompact ({s0} : Set S))
      (isCompact_univ : IsCompact (Set.univ : Set N)) hW hFiber
  refine ⟨U, hUOpen, hs0U (by simp), ?_⟩
  -- Since the second factor already contains `univ`, the full product fiber lies in `W`.
  exact (Set.prod_mono subset_rfl hV).trans hUV

/-- Helper lemma: surjective continuous linear maps onto a finite-dimensional codomain
form an open subset of the continuous-linear-map space. -/
lemma ContinuousLinearMap.isOpen_surjective_ofFiniteDimensionalCodomain
    {U : Type _} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    {V : Type _} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [T2Space V]
    [FiniteDimensional ℝ V] :
    IsOpen {L : U →L[ℝ] V | Function.Surjective L} := by
  rw [isOpen_iff_eventually]
  intro A hA
  have hRange : A.range = ⊤ := LinearMap.range_eq_top.2 hA
  obtain ⟨B, hB⟩ := ContinuousLinearMap.exists_rightInverse_of_surjective A hRange
  have hCompCont : ContinuousAt (fun L : U →L[ℝ] V ↦ L.comp B) A :=
    (continuous_id.clm_comp_const B).continuousAt
  have hNear :
      (fun L : U →L[ℝ] V ↦ L.comp B) ⁻¹'
        Metric.ball (ContinuousLinearMap.id ℝ V) 1 ∈ nhds A := by
    apply hCompCont.preimage_mem_nhds
    simpa [hB] using
      (Metric.ball_mem_nhds (ContinuousLinearMap.id ℝ V) zero_lt_one)
  filter_upwards [hNear] with L hL
  have hDist :
      ‖ContinuousLinearMap.id ℝ V - L.comp B‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hL
  have hUnit :
      IsUnit (L.comp B) := by
    have hCancel :
        ContinuousLinearMap.id ℝ V -
            (ContinuousLinearMap.id ℝ V - L.comp B) =
          L.comp B := by
      ext v
      simp
    exact hCancel ▸ isUnit_one_sub_of_norm_lt_one hDist
  have hCompSurj : Function.Surjective (L.comp B) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hUnit).2
  -- Surjectivity of `L ∘ B` immediately yields surjectivity of `L`.
  intro z
  obtain ⟨w, hw⟩ := hCompSurj z
  exact ⟨B w, hw⟩

/-- Helper lemma: composing a product map with the vertical inclusion keeps only the
second factor. -/
lemma prodMap_comp_inr
    {U : Type _} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    {V : Type _} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {W : Type _} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {Z : Type _} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (A : U →L[𝕜] W) (B : V →L[𝕜] Z) :
    (A.prodMap B).comp (ContinuousLinearMap.inr 𝕜 U V) =
      (ContinuousLinearMap.inr 𝕜 W Z).comp B := by
  -- Evaluate both sides on a vertical vector and read off the same second component.
  ext v
  · simp [ContinuousLinearMap.inr_apply]
  · rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: the slice-derivative family is continuous after moving all tangent
spaces to the fixed model coordinates around `p0`. -/
lemma continuousAt_sliceMfderivInCoordinates
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) (p0 : S × N) :
    ContinuousAt
      (inTangentCoordinates I J Prod.snd (Function.uncurry F)
        (fun p ↦ mfderiv I J (F p.1) p.2) p0) p0 := by
  let f : S × N → N → M := fun p y ↦ F p.1 y
  have hSmooth :
      ContMDiff ((IS.prod I).prod I) J ∞ (Function.uncurry f) := by
    -- Route correction: differentiate the actual slice family in fixed coordinates instead of the
    -- older parametric-graph tangent transport route.
    have hProj :
        ContMDiff ((IS.prod I).prod I) (IS.prod I) ∞
          (fun q : (S × N) × N ↦ (q.1.1, q.2)) :=
      contMDiff_fst.fst.prodMk contMDiff_snd
    simpa [f, Function.comp, Function.uncurry] using hF.contMDiff.comp hProj
  have hCoords :
      ContMDiffAt (IS.prod I) 𝓘(𝕜, E →L[𝕜] E') 0
        (inTangentCoordinates I J Prod.snd (Function.uncurry F)
          (fun p ↦ mfderiv I J (F p.1) p.2) p0) p0 := by
    -- `ContMDiffAt.mfderiv` records continuity of the fixed-coordinate derivative family.
    simpa [f, Function.uncurry] using
      hSmooth.contMDiffAt.mfderiv f Prod.snd contMDiffAt_snd
        (by simp : (0 : WithTop ℕ∞) + 1 ≤ ∞)
  exact hCoords.continuousAt

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: in a common chart neighborhood of `p0`, injectivity of the slice
derivative is equivalent to injectivity of its fixed-coordinate representative. -/
lemma injective_sliceMfderiv_iff_inTangentCoordinates
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    (IS : ModelWithCorners 𝕜 ES HS) [IsManifold IS ∞ S]
    {F : S → N → M} (p0 p : S × N)
    (hx : p.2 ∈ (chartAt H p0.2).source)
    (hy : F p.1 p.2 ∈ (chartAt H' (F p0.1 p0.2)).source) :
    Function.Injective
        (mfderiv I J (F p.1) p.2) ↔
      Function.Injective
        (inTangentCoordinates I J Prod.snd (Function.uncurry F)
          (fun q ↦ mfderiv I J (F q.1) q.2) p0 p) := by
  -- Move the varying tangent-space map to fixed coordinates and remove the invertible chart
  -- changes on the left and right.
  rw [inTangentCoordinates_eq_mfderiv_comp hx hy]
  let B : TangentSpace J (F p.1 p.2) →L[𝕜] E' :=
    mfderiv% (extChartAt J (F p0.1 p0.2)) (F p.1 p.2)
  let C : E →L[𝕜] TangentSpace I p.2 :=
    mfderiv[range I] (extChartAt I p0.2).symm (extChartAt I p0.2 p.2)
  have hyExt : F p.1 p.2 ∈ (extChartAt J (F p0.1 p0.2)).source := by
    rwa [extChartAt_source]
  have hxExt : p.2 ∈ (extChartAt I p0.2).source := by
    rwa [extChartAt_source]
  have hB : B.IsInvertible := by
    simpa [B] using
      isInvertible_mfderiv_extChartAt hyExt
  have hC : C.IsInvertible := by
    simpa [C] using
      isInvertible_mfderivWithin_extChartAt_symm ((extChartAt I p0.2).map_source hxExt)
  -- The left chart derivative is injective, and the right chart derivative is bijective.
  calc
    Function.Injective (mfderiv I J (F p.1) p.2) ↔
        Function.Injective (B.comp (mfderiv I J (F p.1) p.2)) := by
          simpa [B] using
            (Function.Injective.of_comp_iff hB.bijective.1
              (mfderiv I J (F p.1) p.2)).symm
    _ ↔ Function.Injective ((B.comp (mfderiv I J (F p.1) p.2)).comp C) := by
          simpa [C] using
            (Function.Injective.of_comp_iff'
              (B.comp (mfderiv I J (F p.1) p.2)) hC.bijective).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: in a common chart neighborhood of `p0`, surjectivity of the slice
derivative is equivalent to surjectivity of its fixed-coordinate representative. -/
lemma surjective_sliceMfderiv_iff_inTangentCoordinates
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    (IS : ModelWithCorners 𝕜 ES HS) [IsManifold IS ∞ S]
    {F : S → N → M} (p0 p : S × N)
    (hx : p.2 ∈ (chartAt H p0.2).source)
    (hy : F p.1 p.2 ∈ (chartAt H' (F p0.1 p0.2)).source) :
    Function.Surjective
        (mfderiv I J (F p.1) p.2) ↔
      Function.Surjective
        (inTangentCoordinates I J Prod.snd (Function.uncurry F)
          (fun q ↦ mfderiv I J (F q.1) q.2) p0 p) := by
  -- The same coordinate change only inserts invertible linear maps on the left and right.
  rw [inTangentCoordinates_eq_mfderiv_comp hx hy]
  let B : TangentSpace J (F p.1 p.2) →L[𝕜] E' :=
    mfderiv% (extChartAt J (F p0.1 p0.2)) (F p.1 p.2)
  let C : E →L[𝕜] TangentSpace I p.2 :=
    mfderiv[range I] (extChartAt I p0.2).symm (extChartAt I p0.2 p.2)
  have hyExt : F p.1 p.2 ∈ (extChartAt J (F p0.1 p0.2)).source := by
    rwa [extChartAt_source]
  have hxExt : p.2 ∈ (extChartAt I p0.2).source := by
    rwa [extChartAt_source]
  have hB : B.IsInvertible := by
    simpa [B] using
      isInvertible_mfderiv_extChartAt hyExt
  have hC : C.IsInvertible := by
    simpa [C] using
      isInvertible_mfderivWithin_extChartAt_symm ((extChartAt I p0.2).map_source hxExt)
  -- Surjectivity is likewise unchanged after composing with bijective chart derivatives.
  calc
    Function.Surjective (mfderiv I J (F p.1) p.2) ↔
        Function.Surjective (B.comp (mfderiv I J (F p.1) p.2)) := by
          simpa [B] using
            (Function.Surjective.of_comp_iff' hB.bijective
              (mfderiv I J (F p.1) p.2)).symm
    _ ↔ Function.Surjective ((B.comp (mfderiv I J (F p.1) p.2)).comp C) := by
          simpa [C] using
            (Function.Surjective.of_comp_iff
              (B.comp (mfderiv I J (F p.1) p.2)) hC.bijective.2).symm

/-- Helper lemma: a bijective continuous linear map is invertible. -/
lemma ContinuousLinearMap.isInvertible_of_bijective
    {U : Type _} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [CompleteSpace U] {V : Type _} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    (A : U →L[𝕜] V) (hAinj : Function.Injective A) (hAsurj : Function.Surjective A) :
    A.IsInvertible := by
  -- Package the bijection as a continuous linear equivalence.
  let e : U ≃L[𝕜] V := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.2 hAinj) (LinearMap.range_eq_top.2 hAsurj)
  -- The inverse equivalence is exactly the required invertibility witness.
  refine ⟨e, ?_⟩
  simpa [e] using
    (ContinuousLinearEquiv.coe_ofBijective A (LinearMap.ker_eq_bot.2 hAinj)
      (LinearMap.range_eq_top.2 hAsurj))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I ∞ N] [BoundarylessManifold I N]
    [IsManifold J ∞ M] [BoundarylessManifold J M] in
/-- Helper lemma: a slice local diffeomorphism has bijective manifold derivative. -/
lemma sliceMfderiv_bijective_of_sliceLocalDiffeomorphAt
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} {p : S × N}
    (hp : IsLocalDiffeomorphAt I J ∞ (F p.1) p.2) :
    Function.Injective (mfderiv I J (F p.1) p.2) ∧
      Function.Surjective (mfderiv I J (F p.1) p.2) := by
  -- A local diffeomorphism identifies the tangent spaces by a continuous linear equivalence.
  let e := hp.mfderivToContinuousLinearEquiv (by simp : (∞ : ℕ∞ω) ≠ 0)
  exact ⟨e.injective, e.surjective⟩

/-- Helper lemma: at an interior source point, bijectivity of the slice derivative
upgrades the slice to a local diffeomorphism by the inverse function theorem. -/
lemma sliceLocalDiffeomorphAt_of_interior_bijectiveMfderiv
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) (p : S × N)
    (hpInterior : I.IsInteriorPoint p.2)
    (hInj : Function.Injective (mfderiv I J (F p.1) p.2))
    (hSurj : Function.Surjective (mfderiv I J (F p.1) p.2)) :
    IsLocalDiffeomorphAt I J ∞ (F p.1) p.2 := by
  letI : NormedAddCommGroup (TangentSpace I p.2) := by
    change NormedAddCommGroup E
    infer_instance
  letI : NormedSpace ℝ (TangentSpace I p.2) := by
    change NormedSpace ℝ E
    infer_instance
  letI : CompleteSpace (TangentSpace I p.2) := by
    change CompleteSpace E
    infer_instance
  letI : FiniteDimensional ℝ (TangentSpace I p.2) := by
    change FiniteDimensional ℝ E
    infer_instance
  letI : NormedAddCommGroup (TangentSpace J (F p.1 p.2)) := by
    change NormedAddCommGroup E'
    infer_instance
  letI : NormedSpace ℝ (TangentSpace J (F p.1 p.2)) := by
    change NormedSpace ℝ E'
    infer_instance
  letI : CompleteSpace (TangentSpace J (F p.1 p.2)) := by
    change CompleteSpace E'
    infer_instance
  letI : FiniteDimensional ℝ (TangentSpace J (F p.1 p.2)) := by
    change FiniteDimensional ℝ E'
    infer_instance
  -- Package the bijective manifold derivative as an invertible continuous linear map.
  have hInv : (mfderiv I J (F p.1) p.2).IsInvertible :=
    ContinuousLinearMap.isInvertible_of_bijective (mfderiv I J (F p.1) p.2) hInj hSurj
  -- The inverse function theorem upgrades pointwise invertibility to a local diffeomorphism.
  exact isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible
    (by simp) hpInterior (hF.contMDiff_slice p.1) hInv

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: the slice injective-derivative locus of a smooth family is open in
`S × N`. -/
lemma isOpen_setOf_sliceInjectiveMfderiv
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) :
    IsOpen {p : S × N | Function.Injective (mfderiv I J (F p.1) p.2)} := by
  have hUncurryCont : Continuous (Function.uncurry F) := hF.contMDiff.continuous
  rw [isOpen_iff_mem_nhds]
  intro p0 hp0
  let A : S × N → E →L[𝕜] E' :=
    inTangentCoordinates I J Prod.snd (Function.uncurry F)
      (fun p ↦ mfderiv I J (F p.1) p.2) p0
  have hAcont : ContinuousAt A p0 :=
    continuousAt_sliceMfderivInCoordinates hF p0
  have hp0Source : p0.2 ∈ (chartAt H p0.2).source := by
    simpa using mem_chart_source H p0.2
  have hp0Target : F p0.1 p0.2 ∈ (chartAt H' (F p0.1 p0.2)).source := by
    simpa using mem_chart_source H' (F p0.1 p0.2)
  have hA0iff :
      Function.Injective (mfderiv I J (F p0.1) p0.2) ↔ Function.Injective (A p0) := by
    simpa [A] using
      (injective_sliceMfderiv_iff_inTangentCoordinates IS p0 p0 hp0Source hp0Target)
  have hA0 :
      Function.Injective (A p0) :=
    hA0iff.mp hp0
  have hCharts :
      ({p : S × N | p.2 ∈ (chartAt H p0.2).source} ∩
          {p : S × N | F p.1 p.2 ∈ (chartAt H' (F p0.1 p0.2)).source} ∩
            A ⁻¹' {L : E →L[𝕜] E' | Function.Injective L}) ∈ nhds p0 := by
    -- Keep the preferred source and target charts valid while staying inside the open injective
    -- operator locus around the coordinate representative at `p0`.
    refine Filter.inter_mem
      (Filter.inter_mem
        (continuous_snd.continuousAt.preimage_mem_nhds (chart_source_mem_nhds H p0.2))
        (hUncurryCont.continuousAt.preimage_mem_nhds
          (chart_source_mem_nhds H' (F p0.1 p0.2))))
      ?_
    exact hAcont.preimage_mem_nhds
      (ContinuousLinearMap.isOpen_injective.mem_nhds hA0)
  refine Filter.mem_of_superset hCharts ?_
  intro p hp
  rcases hp with ⟨⟨hpSource, hpTarget⟩, hpA⟩
  exact
    (injective_sliceMfderiv_iff_inTangentCoordinates IS p0 p
      hpSource hpTarget).mpr hpA

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ N] [IsManifold J ∞ M] in
/-- Helper lemma: for a fixed map, the pointwise local-diffeomorphism locus is open. -/
lemma isOpen_setOf_isLocalDiffeomorphAt {f : N → M} :
    IsOpen {x : N | IsLocalDiffeomorphAt I J ∞ f x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨Φ, hxΦ, hEq⟩
  -- Keep the same local branch on its open source neighborhood.
  refine Filter.mem_of_superset (Φ.open_source.mem_nhds hxΦ) ?_
  intro y hy
  exact ⟨Φ, hy, hEq⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ N] [IsManifold J ∞ M] in
/-- Helper lemma: on the fixed parameter fiber, the local inverse of the parametric
graph map preserves the parameter coordinate. -/
lemma parametricGraphLocalInverse_fst_eq
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} {s : S} {x : N}
    (hΓ :
      IsLocalDiffeomorphAt (IS.prod I) (IS.prod J) ∞
        (fun p : S × N ↦ (p.1, F p.1 p.2)) (s, x))
    {z : M} (hz : (s, z) ∈ hΓ.localInverse.source) :
    (hΓ.localInverse (s, z)).1 = s := by
  -- Read off the first coordinate from the right-inverse identity on the total graph map.
  have hright := hΓ.localInverse_right_inv hz
  exact congrArg Prod.fst hright

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ N] [IsManifold J ∞ M] in
/-- Helper lemma: on the fixed parameter fiber, the local inverse of the parametric
graph map is a right inverse for the slice `F s`. -/
lemma parametricGraphLocalInverse_snd_rightInv
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} {s : S} {x : N}
    (hΓ :
      IsLocalDiffeomorphAt (IS.prod I) (IS.prod J) ∞
        (fun p : S × N ↦ (p.1, F p.1 p.2)) (s, x))
    {z : M} (hz : (s, z) ∈ hΓ.localInverse.source) :
    F s (hΓ.localInverse (s, z)).2 = z := by
  -- After fixing the parameter coordinate, the second coordinate gives the desired slice inverse.
  have hs :
      (hΓ.localInverse (s, z)).1 = s :=
    parametricGraphLocalInverse_fst_eq hΓ hz
  have hright := congrArg Prod.snd (hΓ.localInverse_right_inv hz)
  simpa [hs] using hright

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ N] [IsManifold J ∞ M] in
/-- Helper lemma: on the fixed parameter fiber, the local inverse of the parametric
graph map is a left inverse for the slice `F s`. -/
lemma parametricGraphLocalInverse_snd_leftInv
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} {s : S} {x : N}
    (hΓ :
      IsLocalDiffeomorphAt (IS.prod I) (IS.prod J) ∞
        (fun p : S × N ↦ (p.1, F p.1 p.2)) (s, x))
    {y : N} (hy : (s, y) ∈ hΓ.localInverse.target) :
    (hΓ.localInverse (s, F s y)).2 = y := by
  -- The left-inverse identity on the total graph specializes to the fixed slice fiber.
  exact congrArg Prod.snd (hΓ.localInverse_left_inv hy)

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: the slice surjective-derivative locus of a smooth family is open in
`S × N`. -/
-- Route correction: instead of a separate operator-open-locus theorem, use the parametric graph
-- and Proposition 4.1 for the total graph, then read surjectivity back through the vertical part.
lemma isOpen_setOf_sliceSubmersionAt
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) :
    IsOpen {p : S × N | Function.Surjective (mfderiv I J (F p.1) p.2)} :=
  by
  have hUncurryCont : Continuous (Function.uncurry F) := hF.contMDiff.continuous
  rw [isOpen_iff_mem_nhds]
  intro p0 hp0
  let A : S × N → E →L[𝕜] E' :=
    inTangentCoordinates I J Prod.snd (Function.uncurry F)
      (fun p ↦ mfderiv I J (F p.1) p.2) p0
  have hAcont : ContinuousAt A p0 :=
    continuousAt_sliceMfderivInCoordinates hF p0
  have hp0Source : p0.2 ∈ (chartAt H p0.2).source := by
    simpa using mem_chart_source H p0.2
  have hp0Target : F p0.1 p0.2 ∈ (chartAt H' (F p0.1 p0.2)).source := by
    simpa using mem_chart_source H' (F p0.1 p0.2)
  have hA0iff :
      Function.Surjective (mfderiv I J (F p0.1) p0.2) ↔ Function.Surjective (A p0) := by
    simpa [A] using
      (surjective_sliceMfderiv_iff_inTangentCoordinates IS p0 p0 hp0Source hp0Target)
  have hA0 :
      Function.Surjective (A p0) :=
    hA0iff.mp hp0
  have hCharts :
      ({p : S × N | p.2 ∈ (chartAt H p0.2).source} ∩
          {p : S × N | F p.1 p.2 ∈ (chartAt H' (F p0.1 p0.2)).source} ∩
            A ⁻¹' {L : E →L[𝕜] E' | Function.Surjective L}) ∈ nhds p0 := by
    -- The surjective coordinate representative stays surjective on a small operator neighborhood.
    refine Filter.inter_mem
      (Filter.inter_mem
        (continuous_snd.continuousAt.preimage_mem_nhds (chart_source_mem_nhds H p0.2))
        (hUncurryCont.continuousAt.preimage_mem_nhds
          (chart_source_mem_nhds H' (F p0.1 p0.2))))
      ?_
    exact hAcont.preimage_mem_nhds
      (ContinuousLinearMap.isOpen_surjective_ofFiniteDimensionalCodomain.mem_nhds hA0)
  refine Filter.mem_of_superset hCharts ?_
  intro p hp
  rcases hp with ⟨⟨hpSource, hpTarget⟩, hpA⟩
  exact
    (surjective_sliceMfderiv_iff_inTangentCoordinates IS p0 p
      hpSource hpTarget).mpr hpA

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: the slice local-diffeomorphism-at locus of a smooth family is open
in `S × N`. -/
-- TODO: upgrade each slice local diffeomorphism to a local diffeomorphism of the total graph and
-- read the nearby slice inverse back from the graph inverse, rather than reusing a blocked raw
-- slice-vs-total equivalence.
lemma isOpen_setOf_sliceLocalDiffeomorphAt
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    [BoundarylessManifold I N] [BoundarylessManifold J M]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) :
    IsOpen {p : S × N | IsLocalDiffeomorphAt I J ∞ (F p.1) p.2} :=
  by
  -- Route correction: the only usable proof in the current dependency closure is the boundaryless
  -- derivative-bijectivity route, so we state that route directly here.
  have hEq :
      {p : S × N | IsLocalDiffeomorphAt I J ∞ (F p.1) p.2} =
        {p : S × N | Function.Injective (mfderiv I J (F p.1) p.2)} ∩
          {p : S × N | Function.Surjective (mfderiv I J (F p.1) p.2)} := by
    ext p
    constructor
    · intro hp
      let e := hp.mfderivToContinuousLinearEquiv (by simp : (∞ : ℕ∞ω) ≠ 0)
      exact ⟨e.injective, e.surjective⟩
    · rintro ⟨hInj, hSurj⟩
      exact sliceLocalDiffeomorphAt_of_interior_bijectiveMfderiv hF p
        (show I.IsInteriorPoint p.2 from BoundarylessManifold.isInteriorPoint) hInj hSurj
  -- The injective and surjective slice-derivative loci are already open.
  rw [hEq]
  exact (isOpen_setOf_sliceInjectiveMfderiv hF).inter
    (isOpen_setOf_sliceSubmersionAt hF)

/-- Helper lemma: under the ambient boundaryless assumptions already present in this
section, the slice local-diffeomorphism-at locus is open. -/
lemma isOpen_setOf_sliceLocalDiffeomorphAt_boundaryless
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) :
    IsOpen {p : S × N | IsLocalDiffeomorphAt I J ∞ (F p.1) p.2} := by
  -- Reuse the identical boundaryless statement above.
  simpa using isOpen_setOf_sliceLocalDiffeomorphAt hF

/-- Helper lemma: pointwise transversality of a slice to `X` is a predicate on
`S × N` obtained by testing the tangent-space spanning condition whenever the point lands in `X`. -/
abbrev SliceTransverseAt
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] {JX : ModelWithCorners 𝕜 EX HX}
    [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold J JX X]
    (F : S → N → M) (p : S × N) : Prop :=
  ∀ hx : F p.1 p.2 ∈ X,
    let x : X := ⟨F p.1 p.2, hx⟩
    let TX : Submodule 𝕜 (TangentSpace J (F p.1 p.2)) := T[JX; x]
    (mfderiv I J (F p.1) p.2).range ⊔ TX = ⊤

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: for a surjective continuous linear map `B`, surjectivity of
`B.comp A` is equivalent to `A.range ⊔ B.ker = ⊤`. -/
lemma surjectiveComp_iff_range_sup_ker_eq_top
    {V W Z : Type _}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    {A : V →L[𝕜] W} {B : W →L[𝕜] Z} (hB : Function.Surjective B) :
    Function.Surjective (B.comp A) ↔ A.range ⊔ B.ker = ⊤ := by
  -- Reduce the spanning condition to the standard surjectivity criterion for the restriction of
  -- `B` to the image of `A`.
  have hdom :
      Function.Surjective (B.toLinearMap.domRestrict A.range) ↔
        A.range ⊔ B.ker = ⊤ := by
    simpa using (LinearMap.surjective_domRestrict_iff hB)
  constructor
  · intro hComp
    -- A preimage for `B ∘ A` immediately gives a preimage for the domain restriction of `B`.
    exact hdom.mp <| by
      intro z
      rcases hComp z with ⟨x, rfl⟩
      exact ⟨⟨A x, ⟨x, rfl⟩⟩, rfl⟩
  · intro hSup
    -- Conversely, surjectivity on the restricted range lifts back through the witness `A x`.
    have hDomSurj : Function.Surjective (B.toLinearMap.domRestrict A.range) :=
      hdom.mpr hSup
    intro z
    rcases hDomSurj z with ⟨y, hy⟩
    rcases y.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change B (A x) = z
    exact hx ▸ hy

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: after lowering the subtype immersion to the current `∞`
owner, the
front projection of the immersion normal form recovers the intrinsic source coordinates. -/
lemma immersionProjectionEqDomainCoordinatesInf
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] {JX : ModelWithCorners 𝕜 EX HX}
    [ChartedSpace HX X] [IsManifold JX ∞ X]
    {p q : X}
    (hImm : Manifold.IsImmersionAt JX J ∞ (Subtype.val : X → M) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E' →L[𝕜] EX :=
      let equivSymm := hImm.equiv.symm
      let eSymm := equivSymm.toContinuousLinearMap
      (ContinuousLinearMap.fst 𝕜 EX hImm.complement).comp eSymm
    π ((hImm.codChart.extend J) q) = (hImm.domChart.extend JX) q := by
  let equivSymm := hImm.equiv.symm
  let eSymm := equivSymm.toContinuousLinearMap
  let π : E' →L[𝕜] EX :=
    (ContinuousLinearMap.fst 𝕜 EX hImm.complement).comp eSymm
  have hq_source : q ∈ (hImm.domChart.extend JX).source := by
    simpa [hImm.domChart.extend_source] using hq
  have hq_target : (hImm.domChart.extend JX) q ∈ (hImm.domChart.extend JX).target :=
    (hImm.domChart.extend JX).map_source hq_source
  have hcoords := congrArg π (hImm.writtenInCharts hq_target)
  -- Apply the front projection to the immersion chart normal form and simplify the chart inverses.
  simpa [equivSymm, eSymm, π, Function.comp, ContinuousLinearMap.comp_apply,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, hq] using hcoords

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: the inverse of an extended maximal-atlas chart is differentiable
within the range of the model map. -/
lemma chartExtend_symm_mdifferentiableWithin_range
    {e : OpenPartialHomeomorph M H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ M) {p : M} (hp : p ∈ e.source) :
    MDifferentiableWithinAt 𝓘(𝕜, E') J (e.extend J).symm (Set.range J)
      (e.extend J p) := by
  letI : IsManifold J 1 M := IsManifold.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have he_one : e ∈ IsManifold.maximalAtlas J 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞) he
  have hid :
      MDifferentiableWithinAt J J (id : M → M) Set.univ p := by
    -- The inverse-chart differentiability comes from rewriting the identity map in chart
    -- coordinates.
    simpa using
      (mdifferentiableWithinAt_id :
        MDifferentiableWithinAt J J (id : M → M) Set.univ p)
  have hiff :
      MDifferentiableWithinAt J J (id : M → M) Set.univ p ↔
        MDifferentiableWithinAt 𝓘(𝕜, E') J ((id : M → M) ∘ (e.extend J).symm)
          ((e.extend J).symm ⁻¹' Set.univ ∩ Set.range J) (e.extend J p) :=
    mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas he_one hp
  simpa [Function.comp] using hiff.mp hid

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: differentiating the chart left-inverse identity on the chart source
produces a concrete left inverse for the derivative of an extended maximal-atlas chart. -/
lemma chartExtend_mfderiv_left_inverse
    {e : OpenPartialHomeomorph M H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ M) {p : M} (hp : p ∈ e.source) :
    (mfderivWithin 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p)).comp
      (mfderiv J 𝓘(𝕜, E') (e.extend J) p) =
      ContinuousLinearMap.id 𝕜 (TangentSpace J p) := by
  letI : IsManifold J 1 M := IsManifold.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have he_one : e ∈ IsManifold.maximalAtlas J 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞) he
  have hsource_unique : UniqueMDiffWithinAt J e.source p :=
    e.open_source.uniqueMDiffWithinAt hp
  have hchart :
      MDifferentiableAt J 𝓘(𝕜, E') (e.extend J) p := by
    -- Maximal-atlas charts are differentiable at every source point.
    exact
      (contMDiffAt_extend he_one hp).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hrange :
      MDifferentiableWithinAt 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p) :=
    chartExtend_symm_mdifferentiableWithin_range he hp
  have hchart_within :
      mfderiv J 𝓘(𝕜, E') (e.extend J) p =
        mfderivWithin J 𝓘(𝕜, E') (e.extend J) e.source p := by
    -- On the open chart source, the within derivative agrees with the ordinary derivative.
    symm
    exact mfderivWithin_eq_mfderiv hsource_unique hchart
  rw [hchart_within, ← mfderivWithin_comp_of_eq]
  · -- Differentiate the left-inverse identity on the chart source where `UniqueMDiffWithinAt`
    -- is available.
    rw [← mfderivWithin_id hsource_unique]
    apply Filter.EventuallyEq.mfderivWithin_eq_of_mem
    · refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
      intro z hz
      simpa [Function.comp] using
        (show (e.extend J).symm (e.extend J z) = z from e.extend_left_inv hz)
    · exact hp
  · exact hrange
  · exact hchart.mdifferentiableWithinAt
  · intro z hz
    have hz_target : e.extend J z ∈ (e.extend J).target :=
      (e.extend J).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hz
    exact e.extend_target_subset_range hz_target
  · exact hsource_unique
  · rfl

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: the derivative of an extended maximal-atlas chart is injective on
its chart source. -/
lemma chartExtend_mfderiv_injective
    {e : OpenPartialHomeomorph M H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ M) {p : M} (hp : p ∈ e.source) :
    Function.Injective (mfderiv J 𝓘(𝕜, E') (e.extend J) p) := by
  let Linv :=
    mfderivWithin 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p)
  intro w₁ w₂ hw
  have hleft := chartExtend_mfderiv_left_inverse he hp
  have hp_left : (e.extend J).symm (e.extend J p) = p :=
    e.extend_left_inv hp
  have hw_push : Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₁) =
      Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₂) := by
    simpa [Linv] using congrArg Linv hw
  have hw₁ :
      ((Linv.comp (mfderiv J 𝓘(𝕜, E') (e.extend J) p)) w₁) = w₁ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L w₁) hleft
  have hw₂ :
      ((Linv.comp (mfderiv J 𝓘(𝕜, E') (e.extend J) p)) w₂) = w₂ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L w₂) hleft
  have hw₁' : w₁ = Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₁) := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using hw₁.symm
  have hw₂' : Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₂) = w₂ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using hw₂
  -- Apply the derivative-level left inverse to both chart-coordinate tangent vectors.
  exact hw₁'.trans (hw_push.trans hw₂')

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: the derivative of an extended maximal-atlas chart is surjective on
its chart source because the domain and codomain tangent spaces have the same finite rank. -/
lemma chartExtend_mfderiv_surjective
    {e : OpenPartialHomeomorph M H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ M) {p : M} (hp : p ∈ e.source) :
    Function.Surjective (mfderiv J 𝓘(𝕜, E') (e.extend J) p) := by
  let A := (mfderiv J 𝓘(𝕜, E') (e.extend J) p).toLinearMap
  letI : FiniteDimensional 𝕜 (TangentSpace J p) := by
    change FiniteDimensional 𝕜 E'
    infer_instance
  letI : FiniteDimensional 𝕜 (TangentSpace 𝓘(𝕜, E') (e.extend J p)) := by
    change FiniteDimensional 𝕜 E'
    infer_instance
  have hfinrank :
      Module.finrank 𝕜 (TangentSpace J p) =
        Module.finrank 𝕜 (TangentSpace 𝓘(𝕜, E') (e.extend J p)) := by
    change Module.finrank 𝕜 E' = Module.finrank 𝕜 E'
    rfl
  have hAinj : Function.Injective A :=
    chartExtend_mfderiv_injective he hp
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mp hAinj

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: an embedded submanifold is locally cut out by the complement
coordinates coming from an immersion normal form, and these complement coordinates already form a
local defining map. -/
lemma immersionComplementCoordinates_levelSetOn
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] (JX : ModelWithCorners 𝕜 EX HX)
    [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold J JX X]
    (x : X) :
    ∃ (K : Type uE') (_ : NormedAddCommGroup K) (_ : NormedSpace 𝕜 K)
      (_ : FiniteDimensional 𝕜 K) (U : Set M) (Φ : M → K),
      (x : M) ∈ U ∧
        IsLocalDefiningMapOn J 𝓘(𝕜, K) X U Φ := by
  let hSubtype : IsSmoothEmbedding JX J ∞ ((↑) : X → M) := by
    -- Lower the canonical embedded-submanifold inclusion to the `∞` owner used here.
    exact
      isSmoothEmbedding_of_le (by simp)
        (show IsSmoothEmbedding JX J (⊤ : WithTop ℕ∞) ((↑) : X → M) from
          IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val)
  let hImm : Manifold.IsImmersionAt JX J ∞ (Subtype.val : X → M) x :=
    hSubtype.isImmersion.isImmersionAt x
  let K := hImm.complement
  letI : FiniteDimensional 𝕜 (EX × K) :=
    FiniteDimensional.of_injective hImm.equiv.toLinearMap hImm.equiv.injective
  letI : FiniteDimensional 𝕜 K := by
    exact
      FiniteDimensional.of_injective
        (ContinuousLinearMap.inr 𝕜 EX K).toLinearMap
        (by
          intro u v huv
          exact congrArg Prod.snd huv)
  let front : E' →L[𝕜] EX :=
    (ContinuousLinearMap.fst 𝕜 EX K).comp hImm.equiv.symm.toContinuousLinearMap
  let tail : E' →L[𝕜] K :=
    (ContinuousLinearMap.snd 𝕜 EX K).comp hImm.equiv.symm.toContinuousLinearMap
  let Φ : M → K := tail ∘ (hImm.codChart.extend J)
  -- Use the same ambient patch as the local-section construction: stay in the codomain chart and
  -- force the projected first coordinates into the intrinsic source-chart target.
  rcases subtypeVal.isOpen_iff.mp hImm.domChart.open_source with
    ⟨W, hWOpen, hW_eq⟩
  let T : Set EX := interior ((hImm.domChart.extend JX).target)
  have hT_sub : T ⊆ (hImm.domChart.extend JX).target := interior_subset
  have hxW : (x : M) ∈ W := by
    have hx_pre : x ∈ Subtype.val ⁻¹' W := by
      rw [hW_eq]
      exact hImm.mem_domChart_source
    exact hx_pre
  have hxT : (hImm.domChart.extend JX) x ∈ T := by
    have hInteriorPoint :
        JX.IsInteriorPoint x ↔
          (hImm.domChart.extend JX) x ∈ interior ((hImm.domChart.extend JX).target) :=
      JX.isInteriorPoint_iff_of_mem_maximalAtlas
        (show (∞ : ℕ∞ω) ≠ 0 by simp)
        hImm.domChart_mem_maximalAtlas hImm.mem_domChart_source
    exact hInteriorPoint.1 BoundarylessManifold.isInteriorPoint
  have hxProj :
      front ((hImm.codChart.extend J) x) = (hImm.domChart.extend JX) x :=
    immersionProjectionEqDomainCoordinatesInf hImm hImm.mem_domChart_source
  have hxProjT : (front ∘ (hImm.codChart.extend J)) (x : M) ∈ T := by
    have hxComp :
        (front ∘ (hImm.codChart.extend J)) (x : M) = (hImm.domChart.extend JX) x := by
      simpa [Function.comp] using hxProj
    rw [hxComp]
    exact hxT
  have hFrontCont :
      ContinuousAt (front ∘ (hImm.codChart.extend J)) (x : M) := by
    exact front.continuous.continuousAt.comp
      (hImm.codChart.continuousAt_extend hImm.mem_codChart_source)
  have hPreT :
      ((front ∘ (hImm.codChart.extend J)) ⁻¹' T) ∈ nhds (x : M) := by
    exact hFrontCont.preimage_mem_nhds (isOpen_interior.mem_nhds hxProjT)
  rcases mem_nhds_iff.mp hPreT with ⟨V₀, hV₀_sub, hV₀_open, hxV₀⟩
  let U : Set M := hImm.codChart.source ∩ (W ∩ V₀)
  have hUOpen : IsOpen U := hImm.codChart.open_source.inter (hWOpen.inter hV₀_open)
  have hxU : (x : M) ∈ U := ⟨hImm.mem_codChart_source, hxW, hxV₀⟩
  have hU_cod : U ⊆ hImm.codChart.source := fun _ hx ↦ hx.1
  have hFrontTarget :
      ∀ q ∈ U, front ((hImm.codChart.extend J) q) ∈ (hImm.domChart.extend JX).target := by
    intro q hq
    exact hT_sub (hV₀_sub hq.2.2)
  have hDomChart_of_mem :
      ∀ {q : M} (hqX : q ∈ X), q ∈ U → (⟨q, hqX⟩ : X) ∈ hImm.domChart.source := by
    intro q hqX hqU
    have hqPre : (⟨q, hqX⟩ : X) ∈ Subtype.val ⁻¹' W := hqU.2.1
    rwa [hW_eq] at hqPre
  have hPhi_eq_zero_of_mem :
      ∀ {q : M}, q ∈ X → q ∈ U → Φ q = 0 := by
    intro q hqX hqU
    let qX : X := ⟨q, hqX⟩
    have hqDom : qX ∈ hImm.domChart.source :=
      hDomChart_of_mem hqX hqU
    have hqDomExt : qX ∈ (hImm.domChart.extend JX).source := by
      simpa [hImm.domChart.extend_source] using hqDom
    have hqTarget :
        (hImm.domChart.extend JX) qX ∈ (hImm.domChart.extend JX).target :=
      (hImm.domChart.extend JX).map_source hqDomExt
    -- On points of the submanifold, the complement coordinates in the immersion normal form vanish.
    have hcoords := congrArg tail (hImm.writtenInCharts hqTarget)
    simpa [Φ, tail, Function.comp, ContinuousLinearMap.comp_apply,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, hqDom] using hcoords
  have hMem_of_phi_eq_zero :
      ∀ {q : M}, q ∈ U → Φ q = 0 → q ∈ X := by
    intro q hqU hqPhi
    let qFront : EX := front ((hImm.codChart.extend J) q)
    have hqFrontTarget : qFront ∈ (hImm.domChart.extend JX).target :=
      hFrontTarget q hqU
    let qX : X := (hImm.domChart.extend JX).symm qFront
    have hqXChart :
        (hImm.domChart.extend JX) qX = qFront := by
      exact (hImm.domChart.extend JX).right_inv hqFrontTarget
    have hqXDom :
        qX ∈ hImm.domChart.source := by
      have hqXDomExt : qX ∈ (hImm.domChart.extend JX).source := by
        simpa [OpenPartialHomeomorph.extend_source] using
          (hImm.domChart.extend JX).map_target hqFrontTarget
      simpa [hImm.domChart.extend_source] using hqXDomExt
    have hqXCod : ((qX : X) : M) ∈ hImm.codChart.source :=
      hImm.source_subset_preimage_source hqXDom
    have hqXTarget :
        (hImm.domChart.extend JX) qX ∈ (hImm.domChart.extend JX).target :=
      (hImm.domChart.extend JX).map_source <| by
        simpa [hImm.domChart.extend_source] using hqXDom
    have hqXCoords :
        (hImm.codChart.extend J) (qX : X) = hImm.equiv (qFront, (0 : K)) := by
      have hWritten := hImm.writtenInCharts hqXTarget
      have hLeftCoord :
          ((hImm.codChart.extend J) ∘ Subtype.val ∘ (hImm.domChart.extend JX).symm)
              ((hImm.domChart.extend JX) qX) =
            (hImm.codChart.extend J) (qX : X) := by
        simpa [Function.comp] using
          congrArg (fun z : X ↦ (hImm.codChart.extend J) (z : X))
            (hImm.domChart.extend_left_inv (I := JX) hqXDom)
      calc
        (hImm.codChart.extend J) (qX : X) =
            ((hImm.codChart.extend J) ∘ Subtype.val ∘ (hImm.domChart.extend JX).symm)
              ((hImm.domChart.extend JX) qX) := hLeftCoord.symm
        _ = hImm.equiv ((hImm.domChart.extend JX) qX, (0 : K)) := hWritten
        _ = hImm.equiv (qFront, (0 : K)) := by rw [hqXChart]
    have hqCoords :
        (hImm.codChart.extend J) q = hImm.equiv (qFront, (0 : K)) := by
      have hSymmEq :
          hImm.equiv.symm ((hImm.codChart.extend J) q) = (qFront, (0 : K)) := by
        apply Prod.ext
        · rfl
        · simpa [Φ, qFront, tail, front, Function.comp, ContinuousLinearMap.comp_apply] using hqPhi
      calc
        (hImm.codChart.extend J) q =
            hImm.equiv (hImm.equiv.symm ((hImm.codChart.extend J) q)) := by
              simpa using (hImm.equiv.apply_symm_apply ((hImm.codChart.extend J) q)).symm
        _ = hImm.equiv (qFront, (0 : K)) := by rw [hSymmEq]
    have hqCod : q ∈ hImm.codChart.source := hU_cod hqU
    have hEqExt :
        (hImm.codChart.extend J) q = (hImm.codChart.extend J) (qX : X) :=
      hqCoords.trans hqXCoords.symm
    have hEq : q = (qX : X) := by
      calc
        q = (hImm.codChart.extend J).symm ((hImm.codChart.extend J) q) := by
          symm
          exact hImm.codChart.extend_left_inv hqCod
        _ = (hImm.codChart.extend J).symm ((hImm.codChart.extend J) (qX : X)) := by
          rw [hEqExt]
        _ = (qX : X) := by
          exact hImm.codChart.extend_left_inv hqXCod
    exact hEq ▸ qX.2
  refine ⟨K, inferInstance, inferInstance, inferInstance, U, Φ, hxU, ?_⟩
  refine
    { isOpen_source := hUOpen
      smoothOn := ?_
      mem_iff_eq := ?_
      surjective_mfderiv := ?_ }
  · -- The complement-coordinate map is a linear projection of the ambient chart coordinates.
    have hChartSmooth :
        ContMDiffOn J 𝓘(𝕜, E') ∞ (hImm.codChart.extend J) U := by
      exact (contMDiffOn_extend hImm.codChart_mem_maximalAtlas).mono hU_cod
    simpa [Φ, Function.comp] using tail.contDiff.contMDiff.comp_contMDiffOn hChartSmooth
  · intro p q hpX hpU hqU
    have hpZero : Φ p = 0 := hPhi_eq_zero_of_mem hpX hpU
    constructor
    · intro hqX
      simpa [hpZero] using hPhi_eq_zero_of_mem hqX hqU
    · intro hEq
      exact hMem_of_phi_eq_zero hqU (by simpa [hpZero] using hEq)
  · intro p hpU
    have hpCod : p ∈ hImm.codChart.source := hU_cod hpU
    have hChartDiff :
        MDifferentiableAt J 𝓘(𝕜, E') (hImm.codChart.extend J) p := by
      exact
        (contMDiffAt_extend hImm.codChart_mem_maximalAtlas hpCod).mdifferentiableAt
          (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hTailDiff :
        MDifferentiableAt 𝓘(𝕜, E') 𝓘(𝕜, K) tail ((hImm.codChart.extend J) p) := by
      simpa [tail] using tail.contDiff.contMDiff.mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hTailSurj : Function.Surjective tail := by
      intro k
      refine ⟨hImm.equiv (0, k), ?_⟩
      simp [tail]
    have hChartSurj :
        Function.Surjective (mfderiv J 𝓘(𝕜, E') (hImm.codChart.extend J) p) :=
      chartExtend_mfderiv_surjective hImm.codChart_mem_maximalAtlas hpCod
    have hmf :
        mfderiv J 𝓘(𝕜, K) Φ p =
          tail.comp (mfderiv J 𝓘(𝕜, E') (hImm.codChart.extend J) p) := by
      rw [show Φ = tail ∘ (hImm.codChart.extend J) by rfl]
      simpa using mfderiv_comp p hTailDiff hChartDiff
    rw [hmf]
    exact hTailSurj.comp hChartSurj

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: a local defining map rewrites the slice transversality condition as
surjectivity of the defining-map composite derivative. -/
lemma sliceTransverseAt_iff_surjective_definingComposite
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    (IS : ModelWithCorners 𝕜 ES HS) [IsManifold IS ∞ S]
    {F : S → N → M}
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] (JX : ModelWithCorners 𝕜 EX HX)
    [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold J JX X]
    {K : Type _} [NormedAddCommGroup K] [NormedSpace 𝕜 K] [FiniteDimensional 𝕜 K]
    {U : Set M} {Φ : M → K} {p : S × N}
    (hΦ : IsLocalDefiningMapOn J 𝓘(𝕜, K) X U Φ)
    (hpU : F p.1 p.2 ∈ U) (hx : F p.1 p.2 ∈ X) :
    let x : X := ⟨F p.1 p.2, hx⟩
    let TX : Submodule 𝕜 (TangentSpace J (F p.1 p.2)) := T[JX; x]
    let A := mfderiv I J (F p.1) p.2
    let B := mfderiv J 𝓘(𝕜, K) Φ (F p.1 p.2)
    A.range ⊔ TX = ⊤ ↔ Function.Surjective (B.comp A) := by
  let x : X := ⟨F p.1 p.2, hx⟩
  let TX : Submodule 𝕜 (TangentSpace J (F p.1 p.2)) := T[JX; x]
  let A := mfderiv I J (F p.1) p.2
  let B := mfderiv J 𝓘(𝕜, K) Φ (F p.1 p.2)
  letI : NormedAddCommGroup (TangentSpace I p.2) := by
    change NormedAddCommGroup E
    infer_instance
  letI : NormedSpace ℝ (TangentSpace I p.2) := by
    change NormedSpace ℝ E
    infer_instance
  letI : FiniteDimensional ℝ (TangentSpace I p.2) := by
    change FiniteDimensional ℝ E
    infer_instance
  letI : NormedAddCommGroup (TangentSpace J (F p.1 p.2)) := by
    change NormedAddCommGroup E'
    infer_instance
  letI : NormedSpace ℝ (TangentSpace J (F p.1 p.2)) := by
    change NormedSpace ℝ E'
    infer_instance
  letI : FiniteDimensional ℝ (TangentSpace J (F p.1 p.2)) := by
    change FiniteDimensional ℝ E'
    infer_instance
  letI : NormedAddCommGroup (TangentSpace 𝓘(𝕜, K) (Φ (F p.1 p.2))) := by
    change NormedAddCommGroup K
    infer_instance
  letI : NormedSpace ℝ (TangentSpace 𝓘(𝕜, K) (Φ (F p.1 p.2))) := by
    change NormedSpace ℝ K
    infer_instance
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(𝕜, K) (Φ (F p.1 p.2))) := by
    change FiniteDimensional ℝ K
    infer_instance
  have hSubtype :
      IsSmoothEmbedding JX J ∞ ((↑) : X → M) := by
    -- Lower the canonical embedded-submanifold inclusion to the `∞` owner used here.
    exact
      isSmoothEmbedding_of_le (by simp)
        (show IsSmoothEmbedding JX J (⊤ : WithTop ℕ∞) ((↑) : X → M) from
          IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val)
  let hImm : Manifold.IsImmersionAt JX J ∞ (Subtype.val : X → M) x :=
    hSubtype.isImmersion.isImmersionAt x
  letI : FiniteDimensional ℝ (EX × hImm.complement) :=
    FiniteDimensional.of_injective hImm.equiv.toLinearMap hImm.equiv.injective
  letI : FiniteDimensional ℝ EX := by
    exact
      FiniteDimensional.of_injective
        (ContinuousLinearMap.inl ℝ EX hImm.complement).toLinearMap
        (by
          intro u v huv
          exact congrArg Prod.fst huv)
  have hTX :
      TX = B.ker := by
    -- Route correction: rewrite the tangent summand as the kernel of the local defining-map
    -- derivative before invoking the linear-algebra surjectivity criterion.
    simpa [x, TX, B] using
      tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn hSubtype hΦ x hpU
  have hBSurj : Function.Surjective B := by
    -- A local defining map has surjective derivative throughout its open source.
    simpa [B] using hΦ.surjective_mfderiv hpU
  have hTXRaw :
      T[JX; ⟨F p.1 p.2, hx⟩] =
        (mfderiv J 𝓘(𝕜, K) Φ (F p.1 p.2)).ker := by
    simpa [x, TX, B] using hTX
  have hCrit :
      Function.Surjective (B.comp A) ↔ A.range ⊔ B.ker = ⊤ :=
    surjectiveComp_iff_range_sup_ker_eq_top hBSurj
  -- After the tangent-space/kernel rewrite, the statement is exactly the standard range-plus-kernel
  -- criterion for surjectivity of a composite.
  constructor
  · intro hTop
    have hTop' :
        (mfderiv I J (F p.1) p.2).range ⊔
          (mfderiv J 𝓘(𝕜, K) Φ (F p.1 p.2)).ker = ⊤ := by
      rw [hTXRaw] at hTop
      exact hTop
    exact hCrit.2 hTop'
  · intro hComp
    have hTop' :
        (mfderiv I J (F p.1) p.2).range ⊔
          (mfderiv J 𝓘(𝕜, K) Φ (F p.1 p.2)).ker = ⊤ :=
      hCrit.1 hComp
    rw [hTXRaw]
    exact hTop'

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: restricting a local defining map to its open source gives an
ordinary smooth map on the corresponding open subtype. -/
lemma localDefiningMap_contMDiff_restrict
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] {JX : ModelWithCorners 𝕜 EX HX}
    [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold J JX X]
    {K : Type _} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    {U : Set M} {Φ : M → K}
    (hDef : IsLocalDefiningMapOn J 𝓘(𝕜, K) X U Φ) :
    let Uo : TopologicalSpace.Opens M := ⟨U, hDef.isOpen_source⟩
    ContMDiff J 𝓘(𝕜, K) ∞ (fun u : Uo ↦ Φ u.1) := by
  let Uo : TopologicalSpace.Opens M := ⟨U, hDef.isOpen_source⟩
  change ContMDiff J 𝓘(𝕜, K) ∞ (fun u : Uo ↦ Φ u.1)
  intro x
  -- Smoothness on the ambient open set upgrades to ordinary smoothness on the open subtype.
  have hxWithin : ContMDiffWithinAt J 𝓘(𝕜, K) ∞ Φ U x :=
    hDef.smoothOn x x.2
  have hxAt : ContMDiffAt J 𝓘(𝕜, K) ∞ Φ x :=
    hxWithin.contMDiffAt (Uo.2.mem_nhds x.2)
  exact contMDiffAt_subtype_iff.2 hxAt

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: on a product patch whose image stays in the source of a
local defining map, the defining-map composite is a smooth family on the corresponding open
subtypes. -/
lemma definingComposite_isSmoothFamilyOnProductPatch
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    (IS : ModelWithCorners 𝕜 ES HS) [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F)
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] (JX : ModelWithCorners 𝕜 EX HX)
    [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold J JX X]
    {K : Type _} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    {U : Set M} {Φ : M → K}
    (hDef : IsLocalDefiningMapOn J 𝓘(𝕜, K) X U Φ)
    {Us : TopologicalSpace.Opens S} {Oy : TopologicalSpace.Opens N}
    (hImg : ∀ p : Us × Oy, F p.1.1 p.2.1 ∈ U) :
    IsSmoothFamily 𝓘(𝕜, K) IS I (fun s : Us => fun y : Oy => Φ (F s.1 y.1)) := by
  let Uo : TopologicalSpace.Opens M := ⟨U, hDef.isOpen_source⟩
  have hProdIncl :
      ContMDiff (IS.prod I) (IS.prod I) ∞ (fun p : Us × Oy ↦ (p.1.1, p.2.1)) := by
    -- The product patch sits in the ambient product manifold through the open-subtype inclusions.
    exact
      ((contMDiff_subtype_val : ContMDiff IS IS ∞ (Subtype.val : Us → S)).comp contMDiff_fst).prodMk
        ((contMDiff_subtype_val : ContMDiff I I ∞ (Subtype.val : Oy → N)).comp contMDiff_snd)
  have hRestrictF :
      ContMDiff (IS.prod I) J ∞ (fun p : Us × Oy ↦ F p.1.1 p.2.1) := by
    -- Restrict the original smooth family to the chosen product patch.
    simpa [Function.uncurry] using hF.contMDiff.comp hProdIncl
  have hCodRestrict :
      ContMDiff (IS.prod I) J ∞
        (fun p : Us × Oy ↦ (⟨F p.1.1 p.2.1, hImg p⟩ : Uo)) := by
    -- The image containment upgrades the ambient map to a smooth map into the open source subtype.
    intro p
    have hpAmbient :
        ContMDiffAt (IS.prod I) J ∞
          ((Subtype.val : Uo → M) ∘
            (fun q : Us × Oy ↦ (⟨F q.1.1 q.2.1, hImg q⟩ : Uo))) p := by
      change ContMDiffAt (IS.prod I) J ∞ (fun q : Us × Oy ↦ F q.1.1 q.2.1) p
      exact hRestrictF.contMDiffAt (x := p)
    simpa [ContMDiffAt, ContMDiffWithinAt] using
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp (IS.prod I) J ∞)
        (f := fun q : Us × Oy ↦ (⟨F q.1.1 q.2.1, hImg q⟩ : Uo))
        (s := (Set.univ : Set (Us × Oy))) (x := p)).1 hpAmbient
  have hDefRestrict :
      ContMDiff J 𝓘(𝕜, K) ∞ (fun u : Uo ↦ Φ u.1) := by
    -- The local defining map is already smooth on its open source.
    simpa [Uo] using localDefiningMap_contMDiff_restrict (J := J) (JX := JX) hDef
  -- Compose the codomain restriction with the defining map restricted to its open source.
  change
    ContMDiff (IS.prod I) 𝓘(𝕜, K) ∞
      (fun p : Us × Oy ↦ Φ (F p.1.1 p.2.1))
  simpa [Function.comp] using hDefRestrict.comp hCodRestrict

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: on the source of a local defining map, the derivative of the slice
composite `Φ ∘ F s` is the composite of the derivatives. -/
lemma sliceComposite_mfderiv_eq
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    (IS : ModelWithCorners 𝕜 ES HS) [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F)
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] (JX : ModelWithCorners 𝕜 EX HX)
    [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold J JX X]
    {K : Type _} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    {U : Set M} {Φ : M → K}
    (hDef : IsLocalDefiningMapOn J 𝓘(𝕜, K) X U Φ)
    {s : S} {y : N} (hyU : F s y ∈ U) :
    mfderiv I 𝓘(𝕜, K) (fun z : N ↦ Φ (F s z)) y =
      (mfderiv J 𝓘(𝕜, K) Φ (F s y)).comp (mfderiv I J (F s) y) := by
  have hΦWithin : ContMDiffWithinAt J 𝓘(𝕜, K) ∞ Φ U (F s y) :=
    hDef.smoothOn (F s y) hyU
  have hΦAt : ContMDiffAt J 𝓘(𝕜, K) ∞ Φ (F s y) :=
    hΦWithin.contMDiffAt (hDef.isOpen_source.mem_nhds hyU)
  have hΦDiff :
      MDifferentiableAt J 𝓘(𝕜, K) Φ (F s y) :=
    hΦAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hSliceDiff : MDifferentiableAt I J (F s) y :=
    (hF.contMDiff_slice s).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  -- Differentiate the ambient slice composite directly by the chain rule.
  rw [show (fun z : N ↦ Φ (F s z)) = Φ ∘ F s by rfl]
  simpa using mfderiv_comp y hΦDiff hSliceDiff

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: on an open-source restriction, surjectivity of the restricted slice
derivative is equivalent to surjectivity of the ambient slice-composite derivative. -/
lemma surjective_restrictSliceCompositeMfderiv_iff
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    (IS : ModelWithCorners 𝕜 ES HS) [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F)
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] (JX : ModelWithCorners 𝕜 EX HX)
    [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold J JX X]
    {K : Type _} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    {U : Set M} {Φ : M → K}
    (hDef : IsLocalDefiningMapOn J 𝓘(𝕜, K) X U Φ)
    {Oy : TopologicalSpace.Opens N} {s : S} {y : Oy} (hyU : F s y.1 ∈ U) :
    Function.Surjective (mfderiv I 𝓘(𝕜, K) (fun z : Oy ↦ Φ (F s z.1)) y) ↔
      Function.Surjective (mfderiv I 𝓘(𝕜, K) (fun z : N ↦ Φ (F s z)) y.1) := by
  let A := mfderiv I I (Subtype.val : Oy → N) y
  let B := mfderiv I 𝓘(𝕜, K) (fun z : N ↦ Φ (F s z)) y.1
  have hΦWithin : ContMDiffWithinAt J 𝓘(𝕜, K) ∞ Φ U (F s y.1) :=
    hDef.smoothOn (F s y.1) hyU
  have hΦAt : ContMDiffAt J 𝓘(𝕜, K) ∞ Φ (F s y.1) :=
    hΦWithin.contMDiffAt (hDef.isOpen_source.mem_nhds hyU)
  have hΦDiff :
      MDifferentiableAt J 𝓘(𝕜, K) Φ (F s y.1) :=
    hΦAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hSliceDiff : MDifferentiableAt I J (F s) y.1 :=
    (hF.contMDiff_slice s).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hAmbientDiff :
      MDifferentiableAt I 𝓘(𝕜, K) (fun z : N ↦ Φ (F s z)) y.1 := by
    -- Differentiate the ambient slice composite directly by the chain rule.
    simpa [Function.comp] using hΦDiff.comp y.1 hSliceDiff
  have hSubtypeDiff :
      MDifferentiableAt I I (Subtype.val : Oy → N) y := by
    -- The open-subset inclusion is smooth, hence differentiable.
    exact contMDiff_subtype_val.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hComp :
      mfderiv I 𝓘(𝕜, K) (fun z : Oy ↦ Φ (F s z.1)) y = B.comp A := by
    -- The restricted slice is the ambient slice composed with the open inclusion.
    rw [show (fun z : Oy ↦ Φ (F s z.1)) =
        (fun z : N ↦ Φ (F s z)) ∘ (Subtype.val : Oy → N) by rfl]
    simpa [A, B] using mfderiv_comp y hAmbientDiff hSubtypeDiff
  have hAInv : A.IsInvertible := by
    -- The derivative of an open-subset inclusion is an isomorphism.
    let e := Oy.openPartialHomeomorphSubtypeCoe ⟨y⟩
    have hsymm : ContMDiffOn I I 1 e.symm (Oy : Set N) := by
      -- The inverse of the open inclusion is smooth because it is a local inverse to the subtype
      -- inclusion on the open source.
      intro z hz
      have hcomp : ContMDiffWithinAt I I 1 (Subtype.val ∘ e.symm) (Oy : Set N) z := by
        refine contMDiffWithinAt_id.congr_of_mem ?_ hz
        intro z' hz'
        simpa [e] using e.right_inv (by simpa [e] using hz')
      have hiff :
          ChartedSpace.LiftPropWithinAt (ContDiffWithinAtProp I I 1) (Subtype.val ∘ e.symm)
              (Oy : Set N) z ↔
            ChartedSpace.LiftPropWithinAt (ContDiffWithinAtProp I I 1) e.symm (Oy : Set N) z :=
        ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff e.symm (Oy : Set N) z
      simpa [ContMDiffWithinAt] using
        hiff.mp (by simpa [ContMDiffWithinAt] using hcomp)
    let Φopen : PartialDiffeomorph I I Oy N 1 := {
      toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        simpa [e] using
          ((contMDiff_subtype_val : ContMDiff I I 1 (Subtype.val : Oy → N)).contMDiffOn :
            ContMDiffOn I I 1 (Subtype.val : Oy → N) Set.univ)
      contMDiffOn_invFun := by
        simpa [e] using hsymm }
    have hySource : y ∈ Φopen.source := by
      simp [Φopen, e]
    have hlocal : IsLocalDiffeomorphAt I I 1 (Φopen : Oy → N) y := by
      exact ⟨Φopen, hySource, fun z _ ↦ rfl⟩
    have hinv : (mfderiv I I (Φopen : Oy → N) y).IsInvertible := by
      rw [← hlocal.mfderivToContinuousLinearEquiv_coe one_ne_zero]
      exact ContinuousLinearMap.isInvertible_equiv
    simpa [A, Φopen, e] using hinv
  -- Surjectivity is unchanged after composing on the right with the bijective inclusion
  -- derivative.
  simpa [hComp, A, B] using
    (Function.Surjective.of_comp_iff B hAInv.bijective.2)

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: surjectivity of the defining-map slice composite persists on an
ambient neighborhood once it holds at one point of the open source of a local defining map. -/
lemma sliceComposite_surjective_nhds_of_localDefiningMap
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    (IS : ModelWithCorners 𝕜 ES HS) [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F)
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] (JX : ModelWithCorners 𝕜 EX HX)
    [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold J JX X]
    {K : Type _} [NormedAddCommGroup K] [NormedSpace 𝕜 K] [FiniteDimensional 𝕜 K]
    {U : Set M} {Φ : M → K} {p0 : S × N}
    (hDef : IsLocalDefiningMapOn J 𝓘(𝕜, K) X U Φ)
    (hp0U : F p0.1 p0.2 ∈ U)
    (hp0Surj :
      Function.Surjective (mfderiv I 𝓘(𝕜, K) (fun y : N ↦ Φ (F p0.1 y)) p0.2)) :
    ∃ V : Set (S × N), IsOpen V ∧ p0 ∈ V ∧
      V ⊆ {q : S × N | F q.1 q.2 ∈ U} ∧
      ∀ q ∈ V, Function.Surjective (mfderiv I 𝓘(𝕜, K) (fun y : N ↦ Φ (F q.1 y)) q.2) := by
  have hOpenPreU :
      IsOpen ((Function.uncurry F) ⁻¹' U) := by
    -- Continuity of the uncurried family makes the defining-map source pull back to an open patch.
    exact hDef.isOpen_source.preimage hF.contMDiff.continuous
  have hp0PreU : p0 ∈ (Function.uncurry F) ⁻¹' U := by
    simpa [Function.uncurry] using hp0U
  obtain ⟨UsSet, OySet, hUsOpen, hOyOpen, hp0UsSet, hp0OySet, hPatchSub⟩ :=
    generalized_tube_lemma
      (isCompact_singleton : IsCompact ({p0.1} : Set S))
      (isCompact_singleton : IsCompact ({p0.2} : Set N))
      hOpenPreU
      (by
        intro q hq
        rcases hq with ⟨hq1, hq2⟩
        have hq1' : q.1 = p0.1 := by simpa using hq1
        have hq2' : q.2 = p0.2 := by simpa using hq2
        simpa [hq1', hq2', Function.uncurry] using hp0U)
  let Us : TopologicalSpace.Opens S := ⟨UsSet, hUsOpen⟩
  let Oy : TopologicalSpace.Opens N := ⟨OySet, hOyOpen⟩
  have hp0Us : p0.1 ∈ (Us : Set S) := hp0UsSet (by simp)
  have hp0Oy : p0.2 ∈ (Oy : Set N) := hp0OySet (by simp)
  have hImg : ∀ p : Us × Oy, F p.1.1 p.2.1 ∈ U := by
    intro p
    rcases p with ⟨s, y⟩
    have hpUs : s.1 ∈ UsSet := by
      simpa [Us] using s.2
    have hpOy : y.1 ∈ OySet := by
      simpa [Oy] using y.2
    have hpPatch : (s.1, y.1) ∈ UsSet ×ˢ OySet := ⟨hpUs, hpOy⟩
    simpa [Function.uncurry] using hPatchSub hpPatch
  have hPatchSmooth :
      IsSmoothFamily 𝓘(𝕜, K) IS I (fun s : Us => fun y : Oy => Φ (F s.1 y.1)) :=
    definingComposite_isSmoothFamilyOnProductPatch IS hF JX hDef hImg
  let p0Sub : Us × Oy :=
    ⟨⟨p0.1, by simpa [Us] using hp0Us⟩, ⟨p0.2, by simpa [Oy] using hp0Oy⟩⟩
  have hp0SubSurj :
      Function.Surjective
        (mfderiv I 𝓘(𝕜, K) (fun y : Oy ↦ Φ (F p0.1 y.1)) p0Sub.2) := by
    -- Move the ambient slice-surjectivity hypothesis to the restricted source patch.
    exact
      (surjective_restrictSliceCompositeMfderiv_iff
        (IS := IS) (hF := hF) (JX := JX) (hDef := hDef)
        (Oy := Oy) (s := p0.1) (y := p0Sub.2) hp0U).2 hp0Surj
  let Wsub : Set (Us × Oy) :=
    {q : Us × Oy |
      Function.Surjective
        (mfderiv I 𝓘(𝕜, K) (fun y : Oy ↦ Φ (F q.1.1 y.1)) q.2)}
  have hWsubOpen : IsOpen Wsub := by
    -- The restricted family has an open slice-submersion locus on the product patch.
    simpa [Wsub] using isOpen_setOf_sliceSubmersionAt hPatchSmooth
  have hp0Wsub : p0Sub ∈ Wsub := by
    simpa [Wsub] using hp0SubSurj
  let e : Us × Oy → S × N :=
    Prod.map (Subtype.val : Us → S) (Subtype.val : Oy → N)
  let V : Set (S × N) := e '' Wsub
  have hVOpen : IsOpen V := by
    -- Push the open restricted locus forward along the open embedding of the product patch.
    let he :
        Topology.IsOpenEmbedding e :=
      Us.2.isOpenEmbedding_subtypeVal.prodMap Oy.2.isOpenEmbedding_subtypeVal
    simpa [V] using (he.isOpen_iff_image_isOpen).1 hWsubOpen
  have hp0V : p0 ∈ V := by
    refine ⟨p0Sub, hp0Wsub, ?_⟩
    rfl
  have hVSubU : V ⊆ {q : S × N | F q.1 q.2 ∈ U} := by
    rintro q ⟨qSub, hqSub, rfl⟩
    exact hImg qSub
  refine ⟨V, hVOpen, hp0V, hVSubU, ?_⟩
  rintro q ⟨qSub, hqSub, rfl⟩
  have hqU : F qSub.1.1 qSub.2.1 ∈ U := hImg qSub
  have hqSubSurj :
      Function.Surjective
        (mfderiv I 𝓘(𝕜, K) (fun y : Oy ↦ Φ (F qSub.1.1 y.1)) qSub.2) := by
    simpa [Wsub] using hqSub
  -- Transport surjectivity back from the restricted patch to the ambient slice derivative.
  exact
    (surjective_restrictSliceCompositeMfderiv_iff
      (IS := IS) (hF := hF) (JX := JX) (hDef := hDef)
      (Oy := Oy) (s := qSub.1.1) (y := qSub.2) hqU).1 hqSubSurj

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: the pointwise slice transversality locus of a smooth family is open
in `S × N`. -/
lemma isOpen_setOf_sliceTransverseAt
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M}
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type _} [TopologicalSpace HX] {JX : ModelWithCorners 𝕜 EX HX}
    [ChartedSpace HX X] [IsManifold JX ∞ X] [IsEmbeddedSubmanifold J JX X]
    (hXproper : X.IsProperlyEmbedded) (hF : IsSmoothFamily J IS I F) :
    IsOpen {p : S × N |
      ∀ hx : F p.1 p.2 ∈ X,
        let x : X := ⟨F p.1 p.2, hx⟩
        let TX : Submodule 𝕜 (TangentSpace J (F p.1 p.2)) := T[JX; x]
        (mfderiv I J (F p.1) p.2).range ⊔ TX = ⊤} := by
  rw [isOpen_iff_mem_nhds]
  intro p0 hp0
  by_cases hx0 : F p0.1 p0.2 ∈ X
  · -- Route correction: the hard branch now passes through a local defining map and the proved
    -- transversality-to-surjectivity bridge above. Shrink to a product neighborhood inside the
    -- defining-map source, propagate slice-composite surjectivity there, and translate back.
    let x0 : X := ⟨F p0.1 p0.2, hx0⟩
    have hCoords :
        ∃ (K : Type uE') (_ : NormedAddCommGroup K) (_ : NormedSpace 𝕜 K)
          (_ : FiniteDimensional 𝕜 K) (U : Set M) (Φ : M → K),
          (x0 : M) ∈ U ∧ IsLocalDefiningMapOn J 𝓘(𝕜, K) X U Φ :=
      immersionComplementCoordinates_levelSetOn JX x0
    rcases hCoords with
      ⟨K, _, _, _, U, Φ, hx0U, hDef⟩
    have hp0CompositeSurj :
        Function.Surjective
          ((mfderiv J 𝓘(𝕜, K) Φ (F p0.1 p0.2)).comp (mfderiv I J (F p0.1) p0.2)) := by
      -- At the basepoint, transversality is exactly surjectivity of the defining-map composite.
      exact
        (sliceTransverseAt_iff_surjective_definingComposite IS JX hDef hx0U hx0).1
          (hp0 hx0)
    have hp0Surj :
        Function.Surjective (mfderiv I 𝓘(𝕜, K) (fun y : N ↦ Φ (F p0.1 y)) p0.2) := by
      -- Rewrite the defining-map composite derivative as the derivative of the ambient slice
      -- composite.
      have hCompEq := sliceComposite_mfderiv_eq IS hF JX hDef hx0U
      simpa [hCompEq] using hp0CompositeSurj
    rcases sliceComposite_surjective_nhds_of_localDefiningMap IS hF JX hDef hx0U hp0Surj with
      ⟨V, hVOpen, hp0V, hVSubU, hVSurj⟩
    refine Filter.mem_of_superset (hVOpen.mem_nhds hp0V) ?_
    intro q hq
    intro hx
    have hqU : F q.1 q.2 ∈ U := hVSubU hq
    have hCompositeSurj :
        Function.Surjective
          ((mfderiv J 𝓘(𝕜, K) Φ (F q.1 q.2)).comp (mfderiv I J (F q.1) q.2)) := by
      -- Rewrite the ambient slice-composite derivative into the defining-map composite.
      have hCompEq := sliceComposite_mfderiv_eq IS hF JX hDef hqU
      simpa [hCompEq] using hVSurj q hq
    exact
      (sliceTransverseAt_iff_surjective_definingComposite IS JX hDef hqU hx).2
        hCompositeSurj
  · haveI : T1Space M := J.t1Space M
    have hXclosed : IsClosed X := hXproper.isClosed
    have hOutside :
        {p : S × N | F p.1 p.2 ∉ X} ∈ nhds p0 := by
      -- Away from `X`, continuity of the uncurried family keeps the image in the open complement.
      have hCont : Continuous (Function.uncurry F) := hF.contMDiff.continuous
      have hOpen : IsOpen (Xᶜ) := hXclosed.isOpen_compl
      have hx0' : F p0.1 p0.2 ∈ Xᶜ := by
        simpa using hx0
      simpa [Function.uncurry, Set.mem_setOf_eq] using
        hCont.continuousAt.preimage_mem_nhds (hOpen.mem_nhds hx0')
    refine Filter.mem_of_superset hOutside ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    intro hx
    exact False.elim (hp hx)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I ∞ N] [BoundarylessManifold I N]
    [IsManifold J ∞ M] [BoundarylessManifold J M] in
/-- Helper lemma: for compact source pieces `K` and `L`, the parameters admitting a
collision `F s x = F s y` with `x ∈ K` and `y ∈ L` form a closed set. -/
lemma isClosed_setOf_exists_eqOnCompacts
    [T2Space M]
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F)
    {K L : Set N} (hK : IsCompact K) (hL : IsCompact L) :
    IsClosed {s : S | ∃ x ∈ K, ∃ y ∈ L, F s x = F s y} := by
  have hUncurryCont : Continuous (Function.uncurry F) := hF.contMDiff.continuous
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let _ : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let witnesses : Set (S × (K × L)) :=
    {q | F q.1 ((q.2.1 : K) : N) = F q.1 ((q.2.2 : L) : N)}
  have hLeftArg :
      Continuous fun q : S × (K × L) ↦ (q.1, ((q.2.1 : K) : N)) := by
    -- The left witness point is read continuously from the compact witness pair.
    exact continuous_fst.prodMk
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hRightArg :
      Continuous fun q : S × (K × L) ↦ (q.1, ((q.2.2 : L) : N)) := by
    -- The right witness point is read continuously in the same way.
    exact continuous_fst.prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  have hLeftCont :
      Continuous fun q : S × (K × L) ↦ F q.1 ((q.2.1 : K) : N) := by
    -- Compose the smooth family with the left witness projection.
    simpa [Function.comp, Function.uncurry] using hUncurryCont.comp hLeftArg
  have hRightCont :
      Continuous fun q : S × (K × L) ↦ F q.1 ((q.2.2 : L) : N) := by
    -- Compose the smooth family with the right witness projection.
    simpa [Function.comp, Function.uncurry] using hUncurryCont.comp hRightArg
  have hWitnessesClosed : IsClosed witnesses := by
    -- Equality in the Hausdorff target is the preimage of the diagonal under the paired evaluation.
    let evalPair : S × (K × L) → M × M :=
      fun q ↦ (F q.1 ((q.2.1 : K) : N), F q.1 ((q.2.2 : L) : N))
    have hEvalPair : Continuous evalPair := hLeftCont.prodMk hRightCont
    simpa [witnesses, evalPair] using isClosed_diagonal.preimage hEvalPair
  have hImageClosed : IsClosed (Prod.fst '' witnesses) :=
    isClosedMap_fst_of_compactSpace _ hWitnessesClosed
  have hImageEq :
      Prod.fst '' witnesses = {s : S | ∃ x ∈ K, ∃ y ∈ L, F s x = F s y} := by
    ext s
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨s, x, y⟩
      exact ⟨(x : N), x.2, (y : N), y.2, hq⟩
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨(s, (⟨x, hx⟩, ⟨y, hy⟩)), hxy, rfl⟩
  simpa [hImageEq] using hImageClosed

/-- Helper lemma: an injective map cannot identify points from disjoint source sets. -/
lemma not_exists_eqOnSets_of_injective
    {f : N → M} (hf : Function.Injective f) {K L : Set N} (hKL : Disjoint K L) :
    ¬ ∃ x ∈ K, ∃ y ∈ L, f x = f y := by
  -- An equality witness would place one point in both disjoint sets.
  rintro ⟨x, hx, y, hy, hxy⟩
  have hxy' : x = y := hf hxy
  exact hKL.le_bot ⟨hx, hxy' ▸ hy⟩

/-- Helper lemma: a manifold modeled on a real normed vector space is locally
connected because each chart model is homeomorphic to the convex range of its model-with-corners
map. -/
lemma chartedSpace_locallyConnectedSpace (J : ModelWithCorners ℝ E' H') :
    LocallyConnectedSpace M := by
  -- First transfer local path connectedness from the convex chart-model range to the chart model.
  letI : LocallyConnectedSpace H' := by
    letI : LocPathConnectedSpace (Set.range J) := J.convex_range.locPathConnectedSpace
    let e : H' ≃ₜ Set.range J := J.isClosedEmbedding.toHomeomorph
    exact e.locallyConnectedSpace
  -- Then push the local connectedness through the manifold atlas.
  exact ChartedSpace.locallyConnectedSpace H' M

/-- Helper lemma: the range of a local diffeomorphism from a compact source into a
Hausdorff target is both open and closed. -/
lemma isClopen_range_of_compact_localDiffeomorph
    [CompactSpace N] [T2Space M] {f : N → M} (hf : IsLocalDiffeomorph I J ∞ f) :
    IsClopen (Set.range f) := by
  refine ⟨?_, hf.isOpen_range⟩
  -- Compactness of the source makes the image compact, hence closed in the Hausdorff target.
  exact (isCompact_range (hf.contMDiff.continuous)).isClosed

/-- Helper lemma: a clopen subset that meets every connected component is all of the
ambient space. -/
lemma eq_univ_of_isClopen_hits_every_connectedComponent {A : Set M} (hA : IsClopen A)
    (hHit : ∀ y : M, ∃ z ∈ A, z ∈ connectedComponent y) :
    A = Set.univ := by
  ext y
  constructor
  · intro hy
    simp
  · intro _
    rcases hHit y with ⟨z, hzA, hzComp⟩
    have hCompEq : connectedComponent z = connectedComponent y :=
      (connectedComponent_eq hzComp).symm
    have hyComp : y ∈ connectedComponent z := by
      rw [hCompEq]
      exact mem_connectedComponent
    exact hA.connectedComponent_subset hzA hyComp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I ∞ N] [IsManifold J ∞ M]
    [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: for any compact family of source pairs, the parameters where a slice
identifies one of those pairs form a closed set. -/
lemma isClosed_setOf_exists_eqOnCompactPairs
    [T2Space M]
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F)
    {K : Set (N × N)} (hK : IsCompact K) :
    IsClosed {s : S | ∃ q ∈ K, F s q.1 = F s q.2} := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let witnesses : Set (S × K) := {r | F r.1 ((r.2 : N × N).1) = F r.1 ((r.2 : N × N).2)}
  have hUncurryCont : Continuous (Function.uncurry F) := hF.contMDiff.continuous
  have hLeftArg :
      Continuous fun r : S × K ↦ (r.1, ((r.2 : N × N).1)) := by
    -- Read the first point of the compact pair witness continuously.
    exact continuous_fst.prodMk
      (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
  have hRightArg :
      Continuous fun r : S × K ↦ (r.1, ((r.2 : N × N).2)) := by
    -- Read the second point of the compact pair witness continuously.
    exact continuous_fst.prodMk
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
  have hLeftCont :
      Continuous fun r : S × K ↦ F r.1 ((r.2 : N × N).1) := by
    -- Compose the family evaluation with the first compact-pair projection.
    simpa [Function.comp, Function.uncurry] using hUncurryCont.comp hLeftArg
  have hRightCont :
      Continuous fun r : S × K ↦ F r.1 ((r.2 : N × N).2) := by
    -- Compose the family evaluation with the second compact-pair projection.
    simpa [Function.comp, Function.uncurry] using hUncurryCont.comp hRightArg
  have hWitnessesClosed : IsClosed witnesses := by
    -- Equality in the Hausdorff target is the diagonal preimage of the paired evaluation map.
    let evalPair : S × K → M × M := fun r ↦ (F r.1 ((r.2 : N × N).1), F r.1 ((r.2 : N × N).2))
    have hEvalPair : Continuous evalPair := hLeftCont.prodMk hRightCont
    simpa [witnesses, evalPair] using isClosed_diagonal.preimage hEvalPair
  have hImageClosed : IsClosed (Prod.fst '' witnesses) :=
    isClosedMap_fst_of_compactSpace _ hWitnessesClosed
  have hImageEq :
      Prod.fst '' witnesses = {s : S | ∃ q ∈ K, F s q.1 = F s q.2} := by
    ext s
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(r.2 : N × N), r.2.2, hr⟩
    · rintro ⟨q, hq, hEq⟩
      exact ⟨(s, ⟨q, hq⟩), hEq, rfl⟩
  simpa [hImageEq] using hImageClosed

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: every point of the base embedding slice has an open neighborhood
with compact closure inside a neighborhood where the slice restriction is already a smooth
embedding. -/
lemma localEmbeddingNeighborhoodWithCompactClosure
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    [FiniteDimensional ℝ ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} {s0 : S}
    [LocallyCompactSpace N] [RegularSpace N]
    (hs0 : Manifold.IsSmoothEmbedding I J ∞ (F s0)) (x : N) :
    ∃ W : Set N, ∃ V : TopologicalSpace.Opens N,
      IsOpen W ∧ x ∈ W ∧ IsCompact (closure W) ∧ closure W ⊆ V ∧
        Manifold.IsSmoothEmbedding I J ∞ (F s0 ∘ (Subtype.val : V → N)) := by
  -- Start from the local embedding neighborhood supplied by the local embedding theorem.
  rcases
      ((Manifold.isImmersion_iff_forall_exists_open_restriction_isSmoothEmbedding :
          Manifold.IsImmersion I J ∞ (F s0) ↔
            ∀ x : N, ∃ V : TopologicalSpace.Opens N, x ∈ V ∧
              Manifold.IsSmoothEmbedding I J ∞ (F s0 ∘ (Subtype.val : V → N))).1
        hs0.isImmersion x) with
    ⟨V, hxV, hVemb⟩
  -- Shrink the point neighborhood to one with compact closure still contained in `V`.
  obtain ⟨W, hWOpen, hxWSet, hWclV, hWCompact⟩ :=
    exists_open_between_and_isCompact_closure
      isCompact_singleton
      V.2
      (by simpa [singleton_subset_iff] using hxV)
  refine ⟨W, V, hWOpen, ?_, hWCompact, hWclV, hVemb⟩
  exact hxWSet (by simp)

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: if the base slice has no collisions on a compact set of source
pairs, then the same compact set stays collision-free for all nearby parameters. -/
lemma avoidCompactPairCollisionsNearParameter
    [T2Space M]
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) {s0 : S}
    {K : Set (N × N)} (hK : IsCompact K)
    (hNoCollision : ∀ q ∈ K, F s0 q.1 ≠ F s0 q.2) :
    ∃ U : Set S, IsOpen U ∧ s0 ∈ U ∧
      ∀ s ∈ U, ∀ q ∈ K, F s q.1 ≠ F s q.2 := by
  let bad : Set S := {s : S | ∃ q ∈ K, F s q.1 = F s q.2}
  have hBadClosed : IsClosed bad :=
    isClosed_setOf_exists_eqOnCompactPairs hF hK
  have hs0NotBad : s0 ∉ bad := by
    intro hs0Bad
    rcases hs0Bad with ⟨q, hqK, hqEq⟩
    exact hNoCollision q hqK hqEq
  refine ⟨badᶜ, hBadClosed.isOpen_compl, hs0NotBad, ?_⟩
  intro s hs q hqK hqEq
  exact hs ⟨q, hqK, hqEq⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I ∞ N] [IsManifold J ∞ M]
    [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: injectivity of the slice derivative at `(s, x)` forces injectivity
of the derivative of the parametric graph `(s', y) ↦ (s', F s' y)` at the same point. -/
lemma parametricGraphMfderivInjective_of_sliceMfderivInjective
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) (s : S) (x : N)
    (hInj : Function.Injective (mfderiv I J (F s) x)) :
    Function.Injective
      (mfderiv (IS.prod I) (IS.prod J) (fun p : S × N ↦ (p.1, F p.1 p.2)) (s, x)) := by
  let Γ : S × N → S × M := fun p ↦ (p.1, F p.1 p.2)
  have hΓderiv :
      mfderiv (IS.prod I) (IS.prod J) Γ (s, x) =
        (mfderiv (IS.prod I) IS Prod.fst (s, x)).prod
          (mfderiv (IS.prod I) J (Function.uncurry F) (s, x)) := by
    -- Differentiate the graph into its parameter part and family-value part.
    simpa [Γ] using
      (mfderiv_prodMk
        mdifferentiableAt_fst
        (hF.contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
  have hfst :
      (ContinuousLinearMap.fst 𝕜 (TangentSpace IS s) (TangentSpace J (F s x))).comp
        (mfderiv (IS.prod I) (IS.prod J) Γ (s, x)) =
      ContinuousLinearMap.fst 𝕜 (TangentSpace IS s) (TangentSpace I x) := by
    -- The graph keeps the parameter coordinate unchanged.
    rw [hΓderiv, mfderiv_fst]
    ext u <;> rfl
  have hVert :
      (((ContinuousLinearMap.snd 𝕜 (TangentSpace IS s) (TangentSpace J (F s x))).comp
          (mfderiv (IS.prod I) (IS.prod J) Γ (s, x))).comp
        (ContinuousLinearMap.inr 𝕜 (TangentSpace IS s) (TangentSpace I x))) =
      mfderiv I J (F s) x := by
    -- The vertical part of the graph derivative is exactly the slice derivative.
    simpa [hΓderiv] using
      (sliceMfderiv_eq_uncurryMfderiv_compInr hF s x).symm
  -- Reduce injectivity of the graph derivative to injectivity of its vertical part.
  have hVertInj :
      Function.Injective
        (((ContinuousLinearMap.snd 𝕜 (TangentSpace IS s) (TangentSpace J (F s x))).comp
            (mfderiv (IS.prod I) (IS.prod J) Γ (s, x))).comp
          (ContinuousLinearMap.inr 𝕜 (TangentSpace IS s) (TangentSpace I x))) := by
    simpa [hVert] using hInj
  exact
    (injective_iff_injective_verticalPart_of_fst_comp_eq_fst
      (mfderiv (IS.prod I) (IS.prod J) Γ (s, x)) hfst).2 hVertInj

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper for compact-source stability: a point where the slice derivative is injective admits a product
neighborhood on which every nearby slice is injective. -/
lemma localSliceInjectivePatch_of_sliceMfderivInjective
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    [FiniteDimensional ℝ ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) (p0 : S × N)
    (hp0 : Function.Injective (mfderiv I J (F p0.1) p0.2)) :
    ∃ U : Set S, ∃ W : TopologicalSpace.Opens N,
      IsOpen U ∧ p0.1 ∈ U ∧ p0.2 ∈ W ∧
        ∀ s ∈ U, Function.Injective (fun y : W ↦ F s y) := by
  let Γ : S × N → S × M := fun p ↦ (p.1, F p.1 p.2)
  have hΓCont : ContMDiff (IS.prod I) (IS.prod J) ∞ Γ := by
    -- The graph is the pair of the parameter projection and the uncurried family.
    simpa [Γ] using contMDiff_fst.prodMk hF.contMDiff
  let V : TopologicalSpace.Opens (S × N) :=
    ⟨{p : S × N | Function.Injective (mfderiv I J (F p.1) p.2)},
      isOpen_setOf_sliceInjectiveMfderiv hF⟩
  have hp0V : p0 ∈ V := hp0
  have hsubDiff : ContMDiff (IS.prod I) (IS.prod I) ∞ (Subtype.val : V → S × N) := by
    simpa using
      (contMDiff_subtype_val :
        ContMDiff (IS.prod I) (IS.prod I) ∞ (Subtype.val : V → S × N))
  have hsubImm : Manifold.IsImmersion (IS.prod I) (IS.prod I) ∞ (Subtype.val : V → S × N) :=
    Manifold.IsImmersion.of_opens V
  have hRestrCont :
      ContMDiff (IS.prod I) (IS.prod J) ∞ (Γ ∘ (Subtype.val : V → S × N)) := by
    simpa [Function.comp] using hΓCont.comp hsubDiff
  have hRestrImm :
      Manifold.IsImmersion (IS.prod I) (IS.prod J) ∞ (Γ ∘ (Subtype.val : V → S × N)) := by
    refine (Manifold.is_immersion_iff_forall_injective_mfderiv hRestrCont).2 ?_
    intro q
    have hqAmbient :
        Function.Injective
          (mfderiv (IS.prod I) (IS.prod J) Γ (q : S × N)) :=
      parametricGraphMfderivInjective_of_sliceMfderivInjective hF q.1.1 q.1.2 q.2
    have hqSubtype :
        Function.Injective
          (mfderiv (IS.prod I) (IS.prod I) (Subtype.val : V → S × N) q) :=
      ((Manifold.is_immersion_iff_forall_injective_mfderiv hsubDiff).1 hsubImm) q
    -- The restricted graph derivative is the ambient graph derivative after the open inclusion.
    rw [mfderiv_comp q
      (hΓCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
      (hsubDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))]
    exact hqAmbient.comp hqSubtype
  obtain ⟨U0, hp0U0, hEmb⟩ :=
    ((Manifold.isImmersion_iff_forall_exists_open_restriction_isSmoothEmbedding :
        Manifold.IsImmersion (IS.prod I) (IS.prod J) ∞ (Γ ∘ (Subtype.val : V → S × N)) ↔
          ∀ q : V, ∃ U0 : TopologicalSpace.Opens V, q ∈ U0 ∧
            Manifold.IsSmoothEmbedding (IS.prod I) (IS.prod J) ∞
              (Γ ∘ (Subtype.val : V → S × N) ∘ (Subtype.val : U0 → V))).1
      hRestrImm ⟨p0, hp0V⟩)
  let O : TopologicalSpace.Opens (S × N) :=
    ⟨((↑) : V → S × N) '' (U0 : Set V),
      V.2.isOpenMap_subtype_val (U0 : Set V) U0.2⟩
  have hp0O : p0 ∈ O := ⟨⟨p0, hp0V⟩, hp0U0, rfl⟩
  have hSingleton : ({p0.1} : Set S) ×ˢ ({p0.2} : Set N) ⊆ O := by
    intro p hp
    rcases hp with ⟨hs, hx⟩
    have hs0 : p.1 = p0.1 := by simpa using hs
    have hx0 : p.2 = p0.2 := by simpa using hx
    have hp : p = p0 := by
      ext <;> assumption
    simpa [hp] using hp0O
  obtain ⟨U, W, hUOpen, hWOpen, hs0U, hxW, hUW⟩ :=
    generalized_tube_lemma
      (isCompact_singleton : IsCompact ({p0.1} : Set S))
      (isCompact_singleton : IsCompact ({p0.2} : Set N))
      O.2
      hSingleton
  let W0 : TopologicalSpace.Opens N := ⟨W, hWOpen⟩
  refine ⟨U, W0, hUOpen, hs0U (by simp), hxW (by simp), ?_⟩
  intro s hs y₁ y₂ hEq
  -- Two points of the same source patch with the same image give the same graph point in the
  -- local embedding neighborhood, hence they coincide.
  have hy₁O : (s, (y₁ : N)) ∈ O := hUW ⟨hs, y₁.2⟩
  have hy₂O : (s, (y₂ : N)) ∈ O := hUW ⟨hs, y₂.2⟩
  rcases hy₁O with ⟨q₁, hq₁U0, hq₁Eq⟩
  rcases hy₂O with ⟨q₂, hq₂U0, hq₂Eq⟩
  let u₁ : U0 := ⟨q₁, hq₁U0⟩
  let u₂ : U0 := ⟨q₂, hq₂U0⟩
  have hq₁s : q₁.1.1 = s := by simpa using congrArg Prod.fst hq₁Eq
  have hq₂s : q₂.1.1 = s := by simpa using congrArg Prod.fst hq₂Eq
  have hq₁y : q₁.1.2 = (y₁ : N) := by simpa using congrArg Prod.snd hq₁Eq
  have hq₂y : q₂.1.2 = (y₂ : N) := by simpa using congrArg Prod.snd hq₂Eq
  have hGraphEq :
      ((Γ ∘ (Subtype.val : V → S × N)) ∘ (Subtype.val : U0 → V)) u₁ =
        ((Γ ∘ (Subtype.val : V → S × N)) ∘ (Subtype.val : U0 → V)) u₂ := by
    -- Both lifted points map to the same graph point `(s, F s y)`.
    change Γ ((q₁ : V) : S × N) = Γ ((q₂ : V) : S × N)
    rw [hq₁Eq, hq₂Eq]
    simp [Γ, hEq]
  have hu : u₁ = u₂ := hEmb.isEmbedding.injective hGraphEq
  have hq : ((q₁ : V) : S × N) = ((q₂ : V) : S × N) := by
    exact congrArg (fun u : U0 ↦ (((u : U0) : V) : S × N)) hu
  have hPairEq : (s, (y₁ : N)) = (s, (y₂ : N)) := by
    calc
      (s, (y₁ : N)) = ((q₁ : V) : S × N) := hq₁Eq.symm
      _ = ((q₂ : V) : S × N) := hq
      _ = (s, (y₂ : N)) := hq₂Eq
  exact Subtype.ext (congrArg Prod.snd hPairEq)

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: near a parameter where the slice is a smooth embedding, nearby
slices remain injective. -/
private lemma injectiveSlice_near_s0_of_embeddingBase
    [CompactSpace N] [T2Space M]
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    [FiniteDimensional ℝ ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) {s0 : S}
    (hs0 : Manifold.IsSmoothEmbedding I J ∞ (F s0)) :
    ∃ U : Set S, IsOpen U ∧ s0 ∈ U ∧ ∀ s ∈ U, Function.Injective (F s) :=
  by
  classical
  have hImmInj :
      ∀ x : N, Function.Injective (mfderiv I J (F s0) x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv (hF.contMDiff_slice s0)).1
      hs0.isImmersion
  have hLocal :
      ∀ x : N,
        ∃ U : Set S, ∃ W : TopologicalSpace.Opens N,
          IsOpen U ∧ s0 ∈ U ∧ x ∈ W ∧
            ∀ s ∈ U, Function.Injective (fun y : W ↦ F s y) := by
    intro x
    -- Around each source point, the graph route gives one fixed patch where nearby slices are
    -- already injective.
    exact localSliceInjectivePatch_of_sliceMfderivInjective hF (s0, x) (hImmInj x)
  choose U W hUOpen hs0U hxW hPatchInj using hLocal
  have hCover :
      (Set.univ : Set N) ⊆ ⋃ x, (W x : Set N) := by
    intro x _
    exact mem_iUnion.2 ⟨x, hxW x⟩
  obtain ⟨t, ht⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun x : N ↦ (W x : Set N))
      (fun x ↦ (W x).2)
      hCover
  let Udiag : Set S := ⋂ x ∈ t, U x
  let Odiag : Set (N × N) := ⋃ x ∈ t, ((W x : Set N) ×ˢ (W x : Set N))
  have hUdiagOpen : IsOpen Udiag := by
    -- Intersect the finitely many parameter neighborhoods coming from the local graph patches.
    exact isOpen_biInter_finset fun x _ ↦ hUOpen x
  have hs0Udiag : s0 ∈ Udiag := by
    simp [Udiag, hs0U]
  have hOdiagOpen : IsOpen Odiag := by
    -- The near-diagonal neighborhood is the finite union of the product patches.
    exact isOpen_biUnion fun x hx ↦ ((W x).2.prod (W x).2)
  have hDiagSubset : Set.diagonal N ⊆ Odiag := by
    intro q hq
    rcases q with ⟨x, y⟩
    have hxy : x = y := by simpa [Set.mem_diagonal] using hq
    subst y
    have hxCover : x ∈ ⋃ z ∈ t, (W z : Set N) := ht (by simp)
    rcases mem_iUnion.1 hxCover with ⟨i, hxCover'⟩
    rcases mem_iUnion.1 hxCover' with ⟨hi, hxi⟩
    exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hi, ⟨hxi, hxi⟩⟩⟩
  have hNearDiag :
      ∀ s ∈ Udiag, ∀ x y : N, (x, y) ∈ Odiag → F s x = F s y → x = y := by
    intro s hs x y hxy hEq
    rcases mem_iUnion.1 hxy with ⟨i, hxyi⟩
    rcases mem_iUnion.1 hxyi with ⟨hi, hxyWi⟩
    have hsUi : s ∈ U i := by
      have hsAll : ∀ z ∈ t, s ∈ U z := by
        simpa [Udiag] using hs
      exact hsAll i hi
    have hPatch :
        Function.Injective (fun z : W i ↦ F s z) :=
      hPatchInj i s hsUi
    have hSubEq : (⟨x, hxyWi.1⟩ : W i) = ⟨y, hxyWi.2⟩ := by
      apply hPatch
      simpa using hEq
    exact congrArg Subtype.val hSubEq
  let Kfar : Set (N × N) := (Set.univ : Set (N × N)) \ Odiag
  have hKfarCompact : IsCompact Kfar := by
    -- Outside the finite near-diagonal neighborhood, the complement is closed in the compact
    -- product, hence compact.
    simpa [Kfar, Set.compl_eq_univ_diff] using hOdiagOpen.isClosed_compl.isCompact
  have hNoCollisionFar : ∀ q ∈ Kfar, F s0 q.1 ≠ F s0 q.2 := by
    intro q hq hEq
    have hqEq : q.1 = q.2 := hs0.isEmbedding.injective hEq
    have hqDiag : q ∈ Set.diagonal N := by simpa [Set.mem_diagonal] using hqEq
    have hqOdiag : q ∈ Odiag := hDiagSubset hqDiag
    exact hq.2 hqOdiag
  obtain ⟨Ufar, hUfarOpen, hs0Ufar, hFar⟩ :=
    avoidCompactPairCollisionsNearParameter
      hF hKfarCompact hNoCollisionFar
  refine ⟨Udiag ∩ Ufar, hUdiagOpen.inter hUfarOpen, ⟨hs0Udiag, hs0Ufar⟩, ?_⟩
  intro s hs x y hEq
  by_cases hxy : (x, y) ∈ Odiag
  · exact hNearDiag s hs.1 x y hxy hEq
  · have hxyFar : (x, y) ∈ Kfar := by simp [Kfar, hxy]
    exact False.elim ((hFar s hs.2 (x, y) hxyFar) hEq)

/-- Helper lemma: near a parameter where the slice is a diffeomorphism, nearby slices
remain surjective. -/
-- TODO: use the clopen-range/components route. First shrink to a neighborhood where every slice
-- is a local diffeomorphism, so its range is open. Then use compactness of the source to make the
-- range closed, and finally force the clopen range to contain every connected component of the
-- target by tracking finitely many sample points from the base diffeomorphism through continuity.
lemma surjectiveSlice_near_s0_of_diffeomorphBase
    [CompactSpace N] [T2Space M]
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) {s0 : S}
    (hs0 : F s0 ∈ range ((↑) : (N ≃ₘ⟮I, J⟯ M) → (N → M))) :
    ∃ U : Set S, IsOpen U ∧ s0 ∈ U ∧ ∀ s ∈ U, Function.Surjective (F s) :=
  by
  classical
  rcases hs0 with ⟨Φ0, hΦ0⟩
  letI : LocallyConnectedSpace M := chartedSpace_locallyConnectedSpace J
  letI : CompactSpace M := by
    rw [← isCompact_univ_iff]
    simpa using isCompact_univ.image Φ0.toHomeomorph.continuous
  letI : Fintype (ConnectedComponents M) := Fintype.ofFinite (ConnectedComponents M)
  have hs0Local : IsLocalDiffeomorph I J ∞ (F s0) := by
    -- The base diffeomorphism witness already provides the local-diffeomorphism owner.
    simpa [hΦ0] using Φ0.isLocalDiffeomorph
  have hFiberLoc :
      ({s0} : Set S) ×ˢ (Set.univ : Set N) ⊆
        {p : S × N | IsLocalDiffeomorphAt I J ∞ (F p.1) p.2} := by
    intro p hp
    rcases p with ⟨s, x⟩
    rcases hp with ⟨hs, -⟩
    have hs_eq : s = s0 := by
      simpa using hs
    subst s
    exact (isLocalDiffeomorph_iff.mp hs0Local) x
  obtain ⟨Uloc, hUlocOpen, hs0Uloc, hLoc⟩ :=
    parameterNeighborhood_of_openFiberLocus
      (isOpen_setOf_sliceLocalDiffeomorphAt_boundaryless hF)
      hFiberLoc
  let rep : ConnectedComponents M → M := fun c ↦
    Classical.choose (ConnectedComponents.surjective_coe c)
  have hrep : ∀ c : ConnectedComponents M, ((↑) : M → ConnectedComponents M) (rep c) = c := by
    intro c
    exact Classical.choose_spec (ConnectedComponents.surjective_coe c)
  let sample : ConnectedComponents M → N := fun c ↦ Φ0.symm (rep c)
  let Ucomp : ConnectedComponents M → Set S := fun c ↦
    (fun s : S ↦ F s (sample c)) ⁻¹' connectedComponent (rep c)
  have hUcompOpen : ∀ c : ConnectedComponents M, IsOpen (Ucomp c) := by
    intro c
    -- Each chosen representative stays in its connected component under a small parameter change.
    have hUncurryCont : Continuous (Function.uncurry F) := hF.contMDiff.continuous
    have hCont : Continuous fun s : S ↦ F s (sample c) := by
      simpa [Function.comp, Function.uncurry, sample] using
        hUncurryCont.comp (continuous_id.prodMk continuous_const)
    simpa [Ucomp] using
      (show IsOpen (connectedComponent (rep c)) from isOpen_connectedComponent).preimage hCont
  let Uhit : Set S := ⋂ c ∈ (Finset.univ : Finset (ConnectedComponents M)), Ucomp c
  have hUhitOpen : IsOpen Uhit := by
    -- Finiteness of connected components turns the intersection of all component neighborhoods
    -- into an open set.
    simpa [Uhit] using isOpen_iInter_of_finite hUcompOpen
  have hs0Uhit : s0 ∈ Uhit := by
    simp [Uhit, Ucomp]
    intro c
    have hFs0fun : F s0 = Φ0 := by
      simpa using hΦ0.symm
    have hBase : F s0 (sample c) = rep c := by
      simp [sample, hFs0fun]
    -- At the base parameter, each chosen sample point lands back on its representative.
    simpa [hBase] using (mem_connectedComponent : rep c ∈ connectedComponent (rep c))
  refine ⟨Uloc ∩ Uhit, hUlocOpen.inter hUhitOpen, ⟨hs0Uloc, hs0Uhit⟩, ?_⟩
  intro s hs
  have hLocSlice : IsLocalDiffeomorph I J ∞ (F s) := by
    -- Repackage the pointwise open-locus neighborhood back into the global slice owner.
    refine (isLocalDiffeomorph_iff).2 ?_
    intro x
    exact hLoc (show ((s, x) : S × N) ∈ Uloc ×ˢ (Set.univ : Set N) from ⟨hs.1, by simp⟩)
  have hClopen : IsClopen (Set.range (F s)) :=
    isClopen_range_of_compact_localDiffeomorph hLocSlice
  -- A nearby slice hits every connected component because each chosen representative stays in the
  -- same component as its base image, and clopen ranges contain whole connected components.
  rw [← Set.range_eq_univ]
  refine eq_univ_of_isClopen_hits_every_connectedComponent hClopen ?_
  intro y
  let c : ConnectedComponents M := ((↑) : M → ConnectedComponents M) y
  have hsComp : s ∈ Ucomp c := by
    have hsHit : s ∈ Uhit := hs.2
    have hsHit' : ∀ c : ConnectedComponents M, s ∈ Ucomp c := by
      simpa [Uhit] using hsHit
    exact hsHit' c
  have hRepInCompY : rep c ∈ connectedComponent y := by
    have hRepFiber :
        rep c ∈ ((↑) ⁻¹' ({((↑) : M → ConnectedComponents M) y} : Set (ConnectedComponents M)) :
          Set M) := by
      simp [c, hrep c]
    simpa [connectedComponents_preimage_singleton] using hRepFiber
  have hCompEq : connectedComponent (rep c) = connectedComponent y :=
    (connectedComponent_eq hRepInCompY).symm
  have hSampleInCompY : F s (sample c) ∈ connectedComponent y := by
    rw [← hCompEq]
    exact hsComp
  refine ⟨F s (sample c), ⟨sample c, rfl⟩, ?_⟩
  exact hSampleInCompY

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I ∞ N] [IsManifold J ∞ M]
    [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: a map in the diffeomorphism range is automatically a local
diffeomorphism. -/
lemma isLocalDiffeomorph_of_mem_diffeomorphRange
    {f : N → M}
    (hf : f ∈ range ((↑) : (N ≃ₘ⟮I, J⟯ M) → (N → M))) :
    IsLocalDiffeomorph I J ∞ f := by
  rcases hf with ⟨Φ, rfl⟩
  -- The canonical diffeomorphism witness already carries the local-diffeomorphism field.
  exact Φ.isLocalDiffeomorph

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: a map in the diffeomorphism range is automatically a smooth
embedding. -/
lemma isSmoothEmbedding_of_mem_diffeomorphRange
    {f : N → M}
    (hf : f ∈ range ((↑) : (N ≃ₘ⟮I, J⟯ M) → (N → M))) :
    Manifold.IsSmoothEmbedding I J ∞ f := by
  rcases hf with ⟨Φ, rfl⟩
  -- A diffeomorphism is both a local diffeomorphism and a topological embedding.
  refine
    ⟨(Manifold.is_immersion_iff_forall_injective_mfderiv Φ.contMDiff_toFun).2 ?_,
      Φ.toHomeomorph.isEmbedding⟩
  intro x
  simpa using (Φ.mfderivToContinuousLinearEquiv (by simp) x).injective

omit [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: near a parameter where the slice is a diffeomorphism, nearby slices
are bijective. -/
-- TODO: the omitted-assumption version still needs a boundaryless-free upgrade path from local
-- diffeomorphism openness plus injective/surjective persistence.
lemma bijectiveSlice_near_s0_of_diffeomorphBase
    [CompactSpace N] [T2Space M]
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    [FiniteDimensional ℝ ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    [BoundarylessManifold I N] [BoundarylessManifold J M]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) {s0 : S}
    (hs0 : F s0 ∈ range ((↑) : (N ≃ₘ⟮I, J⟯ M) → (N → M))) :
    ∃ U : Set S, IsOpen U ∧ s0 ∈ U ∧ ∀ s ∈ U, Function.Bijective (F s) :=
  by
  rcases hs0 with ⟨Φ0, hΦ0⟩
  -- Intersect the already-proved injective and surjective neighborhoods of the nearby slices.
  have hBaseEmbedding : Manifold.IsSmoothEmbedding I J ∞ (F s0) := by
    exact isSmoothEmbedding_of_mem_diffeomorphRange ⟨Φ0, hΦ0⟩
  obtain ⟨Uinj, hUinjOpen, hs0Uinj, hInj⟩ :=
    injectiveSlice_near_s0_of_embeddingBase hF hBaseEmbedding
  obtain ⟨Usurj, hUsurjOpen, hs0Usurj, hSurj⟩ :=
    surjectiveSlice_near_s0_of_diffeomorphBase hF ⟨Φ0, hΦ0⟩
  refine ⟨Uinj ∩ Usurj, hUinjOpen.inter hUsurjOpen, ⟨hs0Uinj, hs0Usurj⟩, ?_⟩
  intro s hs
  exact ⟨hInj s hs.1, hSurj s hs.2⟩

/-- Helper lemma: with the ambient boundaryless assumptions in scope, nearby slices of
a base diffeomorphism are bijective. -/
lemma bijectiveSlice_near_s0_of_diffeomorphBase_boundaryless
    [CompactSpace N] [T2Space M]
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    [FiniteDimensional ℝ ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} (hF : IsSmoothFamily J IS I F) {s0 : S}
    (hs0 : F s0 ∈ range ((↑) : (N ≃ₘ⟮I, J⟯ M) → (N → M))) :
    ∃ U : Set S, IsOpen U ∧ s0 ∈ U ∧ ∀ s ∈ U, Function.Bijective (F s) :=
  by
  -- Reuse the identical boundaryless statement above.
  simpa using bijectiveSlice_near_s0_of_diffeomorphBase hF hs0

/-- Source part (a) of Problem 6-16: if `N` is compact, then the class of immersions
`N → M` is stable. -/
theorem immersions_are_stable_under_smooth_families_from_compact_source [CompactSpace N] :
    IsStableMapClass I J {f : N → M | Manifold.IsImmersion I J ∞ f} := by
  intro S ES _ _ _ HS _ _ _ IS _ F hF s0 hs0
  -- The injective slice-derivative locus is open and contains the whole base fiber.
  have hFiber :
      ({s0} : Set S) ×ˢ (Set.univ : Set N) ⊆
        {p : S × N | Function.Injective (mfderiv I J (F p.1) p.2)} := by
    intro p hp
    rcases p with ⟨s, x⟩
    rcases hp with ⟨hs, -⟩
    have hs_eq : s = s0 := by simpa using hs
    subst s
    simpa using
      (Manifold.is_immersion_iff_forall_injective_mfderiv (hF.contMDiff_slice s0)).1 hs0 x
  obtain ⟨U, hUOpen, hs0U, hU⟩ :=
    parameterNeighborhood_of_openFiberLocus
      (isOpen_setOf_sliceInjectiveMfderiv hF) hFiber
  refine ⟨U, hUOpen, hs0U, ?_⟩
  intro s hs
  -- Every nearby slice has injective derivative at every point, hence is an immersion.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv (hF.contMDiff_slice s)).2 ?_
  intro x
  exact hU (show ((s, x) : S × N) ∈ U ×ˢ (Set.univ : Set N) from ⟨hs, by simp⟩)

/-- Source part (b) of Problem 6-16: if `N` is compact, then the class of smooth
submersions `N → M` is stable. -/
theorem submersions_are_stable_under_smooth_families_from_compact_source [CompactSpace N] :
    IsStableMapClass I J {f : N → M | Manifold.IsSmoothSubmersion I J f} := by
  intro S ES _ _ _ HS _ _ _ IS _ F hF s0 hs0
  -- The surjective slice-derivative locus is open and contains the whole base fiber.
  have hFiber :
      ({s0} : Set S) ×ˢ (Set.univ : Set N) ⊆
        {p : S × N | Function.Surjective (mfderiv I J (F p.1) p.2)} := by
    intro p hp
    rcases p with ⟨s, x⟩
    rcases hp with ⟨hs, -⟩
    have hs_eq : s = s0 := by simpa using hs
    subst s
    simpa using
      (Manifold.is_smooth_submersion_iff_forall_surjective_mfderiv
        (hF.contMDiff_slice s0)).1 hs0 x
  obtain ⟨U, hUOpen, hs0U, hU⟩ :=
    parameterNeighborhood_of_openFiberLocus
      (isOpen_setOf_sliceSubmersionAt hF) hFiber
  refine ⟨U, hUOpen, hs0U, ?_⟩
  intro s hs
  -- Surjective derivatives at every point are exactly the submersion criterion.
  refine (Manifold.is_smooth_submersion_iff_forall_surjective_mfderiv
    (hF.contMDiff_slice s)).2 ?_
  intro x
  exact hU (show ((s, x) : S × N) ∈ U ×ˢ (Set.univ : Set N) from ⟨hs, by simp⟩)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I ∞ N] [IsManifold J ∞ M]
    [BoundarylessManifold I N] [BoundarylessManifold J M] in
/-- Helper lemma: if the base slice `F s0` is a local diffeomorphism, then the whole
fiber `{s0} × N` lies in the pointwise slice local-diffeomorphism locus. -/
lemma singletonFiber_subset_setOf_sliceLocalDiffeomorphAt
    {S : Type _} {ES : Type _} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
    {HS : Type _} [TopologicalSpace HS] [TopologicalSpace S] [ChartedSpace HS S]
    {IS : ModelWithCorners 𝕜 ES HS} [IsManifold IS ∞ S]
    {F : S → N → M} {s0 : S}
    (hs0 : IsLocalDiffeomorph I J ∞ (F s0)) :
    ({s0} : Set S) ×ˢ (Set.univ : Set N) ⊆
      {p : S × N | IsLocalDiffeomorphAt I J ∞ (F p.1) p.2} := by
  intro p hp
  rcases p with ⟨s, x⟩
  rcases hp with ⟨hs, -⟩
  have hs_eq : s = s0 := by simpa using hs
  subst s
  -- Rewrite the global local-diffeomorphism owner to its pointwise form on the base slice.
  exact (isLocalDiffeomorph_iff.mp hs0) x

/-- Source part (e) of Problem 6-16: if `N` is compact, then the class of local
diffeomorphisms `N → M` is stable. -/
theorem local_diffeomorphisms_are_stable_under_smooth_families_from_compact_source
    [CompactSpace N] :
    IsStableMapClass I J {f : N → M | IsLocalDiffeomorph I J ∞ f} := by
  intro S ES _ _ _ HS _ _ _ IS _ F hF s0 hs0
  have hFiber :
      ({s0} : Set S) ×ˢ (Set.univ : Set N) ⊆
        {p : S × N | IsLocalDiffeomorphAt I J ∞ (F p.1) p.2} :=
    singletonFiber_subset_setOf_sliceLocalDiffeomorphAt
      (I := I) (J := J) (IS := IS) (F := F) (s0 := s0) hs0
  obtain ⟨U, hUOpen, hs0U, hU⟩ :=
    parameterNeighborhood_of_openFiberLocus
      (isOpen_setOf_sliceLocalDiffeomorphAt_boundaryless hF) hFiber
  refine ⟨U, hUOpen, hs0U, ?_⟩
  intro s hs
  -- Reassemble the pointwise local-diffeomorphism neighborhood into the global slice owner.
  refine (isLocalDiffeomorph_iff).2 ?_
  intro x
  exact hU (show ((s, x) : S × N) ∈ U ×ˢ (Set.univ : Set N) from ⟨hs, by simp⟩)

/-- Problem 6-16 (4): source part (f). For compact `N`, a properly embedded submanifold
`X ⊆ M` has a stable class of transverse maps `N → M`. -/
theorem transverse_maps_are_stable_under_smooth_families_from_compact_source [CompactSpace N]
    {X : Set M} {EX : Type _} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
    {HX : Type _} [TopologicalSpace HX] {JX : ModelWithCorners ℝ EX HX}
    [ChartedSpace HX X] [IsManifold JX ∞ X]
    [IsEmbeddedSubmanifold J JX X] (hXproper : X.IsProperlyEmbedded) :
    IsStableMapClass I J
      {f : N → M | IsTransverseToSubmanifold J I JX X f} := by
  intro S ES _ _ _ HS _ _ _ IS _ F hF s0 hs0
  let W : Set (S × N) :=
    {p : S × N |
      ∀ hx : F p.1 p.2 ∈ X,
        let x : X := ⟨F p.1 p.2, hx⟩
        let TX : Submodule ℝ (TangentSpace J (F p.1 p.2)) := T[JX; x]
        (mfderiv I J (F p.1) p.2).range ⊔ TX = ⊤}
  have hFiber :
      ({s0} : Set S) ×ˢ (Set.univ : Set N) ⊆ W := by
    intro p hp
    rcases p with ⟨s, x⟩
    rcases hp with ⟨hs, -⟩
    have hs_eq : s = s0 := by simpa using hs
    subst s
    intro hx
    -- On the base fiber, the pointwise transversality condition is exactly the class field.
    simpa using hs0.tangent_sup_eq_top ⟨x, hx⟩
  obtain ⟨U, hUOpen, hs0U, hU⟩ :=
    parameterNeighborhood_of_openFiberLocus
      (isOpen_setOf_sliceTransverseAt hXproper hF) hFiber
  refine ⟨U, hUOpen, hs0U, ?_⟩
  intro s hs
  -- Combine smoothness of the nearby slice with the pointwise spanning condition from `W`.
  refine (isTransverseToSubmanifold_iff (F s)).2 ?_
  refine ⟨hF.contMDiff_slice s, ?_⟩
  intro p
  exact hU (show ((s, p) : S × N) ∈ U ×ˢ (Set.univ : Set N) from ⟨hs, by simp⟩) p.2

end Problem616Local

section Problem616Embedding

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H' M] [T2Space M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ N] [BoundarylessManifold I N]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ M] [BoundarylessManifold J M]

/-- Source part (c) of Problem 6-16: if `N` is compact, then the class of smooth
embeddings `N → M` is stable. -/
theorem embeddings_are_stable_under_smooth_families_from_compact_source [CompactSpace N] :
    IsStableMapClass I J {f : N → M | Manifold.IsSmoothEmbedding I J ∞ f} := by
  intro S ES _ _ _ HS _ _ _ IS _ F hF s0 hs0
  obtain ⟨Uimm, hUimmOpen, hs0Uimm, hImm⟩ :=
    immersions_are_stable_under_smooth_families_from_compact_source
      (I := I) (J := J) hF hs0.isImmersion
  obtain ⟨Uinj, hUinjOpen, hs0Uinj, hInj⟩ :=
    injectiveSlice_near_s0_of_embeddingBase hF hs0
  refine ⟨Uimm ∩ Uinj, hUimmOpen.inter hUinjOpen, ⟨hs0Uimm, hs0Uinj⟩, ?_⟩
  intro s hs
  -- Near the base parameter, each slice is both an immersion and injective, so compactness
  -- upgrades it to a smooth embedding.
  exact smooth_embedding_of_compact_source_injective_isImmersion
    (hInj s hs.2) (hImm s hs.1)

/-- Source part (d) of Problem 6-16: if `N` is compact, then the class of
diffeomorphisms `N → M` is stable. -/
theorem diffeomorphisms_are_stable_under_smooth_families_from_compact_source [CompactSpace N] :
    IsStableMapClass I J (range ((↑) : (N ≃ₘ⟮I, J⟯ M) → (N → M))) := by
  intro S ES _ _ _ HS _ _ _ IS _ F hF s0 hs0
  have hs0Local : IsLocalDiffeomorph I J ∞ (F s0) :=
    isLocalDiffeomorph_of_mem_diffeomorphRange hs0
  obtain ⟨Uloc, hUlocOpen, hs0Uloc, hLoc⟩ :=
    local_diffeomorphisms_are_stable_under_smooth_families_from_compact_source
      (I := I) (J := J) hF hs0Local
  obtain ⟨Ubij, hUbijOpen, hs0Ubij, hBij⟩ :=
    bijectiveSlice_near_s0_of_diffeomorphBase_boundaryless hF hs0
  refine ⟨Uloc ∩ Ubij, hUlocOpen.inter hUbijOpen, ⟨hs0Uloc, hs0Ubij⟩, ?_⟩
  intro s hs
  -- A bijective local diffeomorphism is a diffeomorphism, so package the nearby slice through
  -- the canonical owner.
  let Φ : N ≃ₘ⟮I, J⟯ M := (hLoc s hs.1).diffeomorphOfBijective (hBij s hs.2)
  exact ⟨Φ, rfl⟩
end Problem616Embedding
