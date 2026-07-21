import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorField.Pullback
import LeeSmoothLib.Ch03.Sec03_14.Proposition_3_9
import LeeSmoothLib.Ch05.Sec05_32.Definition_5_32_extra_2
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch05.Sec05_36.Proposition_5_49
import LeeSmoothLib.Ch03.Sec03_16.Proposition_3_20
import LeeSmoothLib.Ch08.Sec08_57.Definition_8_57_extra_1
import LeeSmoothLib.Ch08.Sec08_57.Proposition_8_19
import LeeSmoothLib.Ch08.Sec08_58.Definition_8_58_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Domain sampling pass:
-- * source-facing layer: restriction of an ambient smooth vector field to an immersed submanifold;
-- * core/canonical smooth-field owner: bundled smooth tangent sections
--   `Cₛ^∞⟮I; E, TangentSpace I⟯`;
-- * source-facing immersed-submanifold owner: the Chapter 5 predicate
--   `IsImmersedSubmanifold I J S`;
-- * source-facing tangency owner: the intrinsic Chapter 8 predicate
--   `VectorField.IsTangentToSubmanifold`, defined pointwise by membership in `T[J; p]`;
-- * bridge/view layer: the relation to the inclusion `S ↪ M` is the chapter predicate
--   `VectorField.f_related`.
-- Primitive data for tangency is still the underlying rough section, but smooth vector fields
-- should use the chapter's bundled owner rather than a raw section plus a separate smoothness
-- conjunct in the public statement.

section

universe u𝕜 uE uH uM uE' uH'

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S]

namespace VectorField

local notation "SmoothVectorFieldOnM" => Cₛ^∞⟮I; E, TangentSpace I⟯
local notation "SmoothVectorFieldOnS" => Cₛ^∞⟮J; E', TangentSpace J⟯

omit [IsManifold J ∞ S] in
/-- Helper for Proposition 8.23: on an open set, ambient smoothness is equivalent to smoothness of
the restricted map on the corresponding open subtype. -/
private lemma contMDiffOn_iff_contMDiff_restrict
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H'' : Type*} [TopologicalSpace H'']
    {K : ModelWithCorners 𝕜 F H''}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]
    [IsManifold K (∞ : ℕ∞ω) N]
    (U : TopologicalSpace.Opens S) (f : S → N) :
    ContMDiffOn J K ∞ f U ↔ ContMDiff J K ∞ (fun x : U ↦ f x) := by
  constructor
  · intro hf x
    -- Upgrade smoothness on the open set to ambient smoothness at `x`, then reinterpret it on the
    -- corresponding open subtype.
    have hxWithin : ContMDiffWithinAt J K ∞ f (U : Set S) x := hf x x.2
    have hxAt : ContMDiffAt J K ∞ f x := hxWithin.contMDiffAt (U.2.mem_nhds x.2)
    exact (contMDiffAt_subtype_iff (U := U) (f := f) (x := x)).2 hxAt
  · intro hf x hx
    -- Conversely, read the restricted smoothness at `⟨x, hx⟩` as ambient smoothness at `x`.
    let xU : U := ⟨x, hx⟩
    have hxAt : ContMDiffAt J K ∞ f x := by
      exact (contMDiffAt_subtype_iff (U := U) (f := f) (x := xU)).1 (hf xU)
    exact hxAt.contMDiffWithinAt

omit [IsManifold J ∞ S] in
/-- Helper for Proposition 8.23: the derivative of a `C^∞` diffeomorphism is invertible at every
point. -/
private lemma diffeomorph_mfderiv_isInvertible
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold J (∞ : ℕ∞ω) M']
    (F : S ≃ₘ⟮J, J⟯ M') (x : S) :
    (mfderiv J J F x).IsInvertible := by
  -- Package the derivative as the canonical linear equivalence supplied by the diffeomorphism API.
  let e := F.mfderivToContinuousLinearEquiv (by simp) x
  refine ⟨e, ?_⟩
  simpa [e] using
    (Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := F) (hn := by simp) (x := x)).symm

/-- Helper for Proposition 8.23: a maximal-atlas chart is a diffeomorphism between its source open
subtype and its target open subtype. -/
private def chartSourceTargetDiffeomorph
    (e : OpenPartialHomeomorph S H')
    (he : e ∈ IsManifold.maximalAtlas J (∞ : ℕ∞ω) S) :
    (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S) ≃ₘ⟮J, J⟯
      (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H') where
  toEquiv := e.toHomeomorphSourceTarget.toEquiv
  contMDiff_toFun := by
    intro x
    let f :
        (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S) →
          (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H') := fun x ↦
      show (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H') from
        e.toHomeomorphSourceTarget x
    -- Coerce away the target subtype so the goal matches the ambient chart map.
    refine (ContMDiffAt.subtypeVal_comp_iff
      (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H') f x).1 ?_
    refine (contMDiffAt_subtype_iff
      (U := (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S))
      (f := fun x : S ↦ e x) (x := x)).2 ?_
    simpa using
      (contMDiffAt_of_mem_maximalAtlas
        (I := J) (n := (∞ : ℕ∞ω)) (e := e) he x.2)
  contMDiff_invFun := by
    intro y
    let f :
        (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H') →
          (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S) := fun y ↦
      show (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S) from
        e.toHomeomorphSourceTarget.symm y
    -- Coerce away the source subtype so the goal matches the ambient inverse chart map.
    refine (ContMDiffAt.subtypeVal_comp_iff
      (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S) f y).1 ?_
    refine (contMDiffAt_subtype_iff
      (U := (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H'))
      (f := fun y : H' ↦ e.symm y) (x := y)).2 ?_
    simpa using
      (contMDiffAt_symm_of_mem_maximalAtlas
        (I := J) (n := (∞ : ℕ∞ω)) (e := e) he y.2)

/-- Helper for Proposition 8.23: the forward map of `chartSourceTargetDiffeomorph` is the
homeomorphism induced by the chart. -/
private lemma chartSourceTargetDiffeomorph_apply
    (e : OpenPartialHomeomorph S H')
    (he : e ∈ IsManifold.maximalAtlas J (∞ : ℕ∞ω) S)
    (x : (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S)) :
    chartSourceTargetDiffeomorph (J := J) e he x = e.toHomeomorphSourceTarget x := rfl

/-- Helper for Proposition 8.23: over an open subset of the model space, the tangent-bundle chart
is the ambient inclusion after the canonical product identification. -/
private lemma modelOpensTangentBundleChartAt
    (V : TopologicalSpace.Opens H')
    (p : TangentBundle J V) :
    (chartAt (ModelProd H' E') p :
      TangentBundle J V → ModelProd H' E') =
      ((Prod.map (Subtype.val : V → H')
          (id : E' → E')) :
        V × E' → ModelProd H' E') ∘
        Bundle.TotalSpace.toProd V E' := by
  funext q
  have hchart : achart H' p.1 = achart H' q.1 := by
    ext y <;> simp [TopologicalSpace.Opens.chartAt_eq]
  apply Prod.ext
  · -- On an open subset of the model space, the base chart is the subtype inclusion.
    simp [Function.comp, TopologicalSpace.Opens.chartAt_eq]
  · -- The tangent coordinate change collapses to the identity once the base charts agree.
    simp_rw [TangentBundle.chartAt, FiberBundleCore.localTriv,
      FiberBundleCore.localTrivAsPartialEquiv, VectorBundleCore.toFiberBundleCore_baseSet,
      tangentBundleCore_baseSet, hchart]
    simp only [mfld_simps]
    simpa using
      (tangentBundleCore J V).coordChange_self (achart H' q.1) q.1
        (mem_achart_source H' q.1) q.2

/-- Helper for Proposition 8.23: over an open subset of the model space, every tangent-bundle
trivialization has full base set. -/
private lemma modelOpensTangentBundleTrivializationAt_baseSet_univ
    (V : TopologicalSpace.Opens H')
    (x : V) :
    (trivializationAt E' (TangentSpace J) x).baseSet = Set.univ := by
  -- The preferred chart on the open subset is global.
  ext y
  rw [TangentBundle.trivializationAt_baseSet]
  simp [TopologicalSpace.Opens.chartAt_eq]

/-- Helper for Proposition 8.23: over an open subset of the model space, the tangent-bundle
trivialization is defined on all tangent vectors. -/
private lemma modelOpensTangentBundleTrivializationAt_source_univ
    (V : TopologicalSpace.Opens H')
    (x : V) :
    (trivializationAt E' (TangentSpace J) x).source = Set.univ := by
  -- Once the base set is all of `V`, the trivialization source is all of the total space.
  rw [(trivializationAt E' (TangentSpace J) x).source_eq,
    modelOpensTangentBundleTrivializationAt_baseSet_univ (J := J) V x]
  simp

/-- Helper for Proposition 8.23: over an open subset of the model space, the tangent-bundle
trivialization targets all product coordinates. -/
private lemma modelOpensTangentBundleTrivializationAt_target_univ
    (V : TopologicalSpace.Opens H')
    (x : V) :
    (trivializationAt E' (TangentSpace J) x).target = Set.univ := by
  -- The target is `baseSet × univ`, so the global base chart yields all pairs.
  rw [(trivializationAt E' (TangentSpace J) x).target_eq,
    modelOpensTangentBundleTrivializationAt_baseSet_univ (J := J) V x]
  simp

/-- Helper for Proposition 8.23: over an open subset of the model space, the tangent-bundle
trivialization is exactly the canonical product identification. -/
private lemma modelOpensTangentBundleTrivializationAt_eq_toProd
    (V : TopologicalSpace.Opens H')
    (x : V) :
    (trivializationAt E' (TangentSpace J) x :
      TangentBundle J V → V × E') =
      Bundle.TotalSpace.toProd V E' := by
  funext p
  let q : TangentBundle J V := ⟨x, 0⟩
  have htriv :
      (chartAt (ModelProd H' E') q :
        TangentBundle J V → ModelProd H' E') p =
      Prod.map (Subtype.val : V → H')
        (id : E' → E')
        ((trivializationAt E' (TangentSpace J) x) p) := by
    -- Expanding the tangent-bundle chart shows it is the trivialization followed by the base
    -- inclusion.
    simpa [q, Function.comp, TopologicalSpace.Opens.chartAt_eq, prodChartedSpace_chartAt] using
      congrArg
        (fun e : OpenPartialHomeomorph (TangentBundle J V) (ModelProd H' E') ↦ e p)
        (FiberBundle.chartedSpace_chartAt
          (F := E') (E := TangentSpace J) (HB := H') (x := q))
  have hprod :
      (chartAt (ModelProd H' E') q :
        TangentBundle J V → ModelProd H' E') p =
      Prod.map (Subtype.val : V → H')
        (id : E' → E')
        ((Bundle.TotalSpace.toProd V E') p) := by
    -- The same chart also matches the canonical product identification on open model-space
    -- subsets.
    simpa [Function.comp] using
      congrArg
        (fun f : TangentBundle J V → ModelProd H' E' ↦ f p)
        (modelOpensTangentBundleChartAt (J := J) V q)
  exact (Subtype.val_injective.prodMap (fun _ _ h ↦ h)) (htriv.symm.trans hprod)

/-- Helper for Proposition 8.23: on an open subset of the model space, the explicit coordinate
map `r ↦ J r` has identity derivative on tangent vectors. -/
private lemma modelOpensCoordinate_eq_self
    (V : TopologicalSpace.Opens H')
    (q : V) (v : TangentSpace J q) :
    mfderiv J 𝓘(𝕜, E') (fun r : V ↦ J r) q v = v := by
  have hchart : (extChartAt J q : V → E') = fun r : V ↦ J r := by
    funext r
    rw [extChartAt_coe]
    rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
    simp
  have hmfderiv :
      mfderiv J 𝓘(𝕜, E') (fun r : V ↦ J r) q =
        mfderiv J 𝓘(𝕜, E') (extChartAt J q) q := by
    exact mfderiv_congr (x := q) hchart.symm
  rw [hmfderiv, mfderiv_extChartAt_self (I := J) (x := q)]
  change (ContinuousLinearMap.id 𝕜 (TangentSpace J q)) v = v
  exact ContinuousLinearMap.id_apply _

/-- Helper for Proposition 8.23: on an open subset of the model space, a vector field is smooth
exactly when its raw `E'`-valued coordinate map is smooth. -/
private lemma smoothOpenSubsetVectorField_iff_smoothCoordinates
    (V : TopologicalSpace.Opens H')
    (Z : ∀ q : V, TangentSpace J q) :
    ContMDiff J J.tangent ∞ (T% Z) ↔
      ContMDiff J 𝓘(𝕜, E') ∞ (fun q : V ↦ Z q) := by
  constructor
  · intro hZ q
    -- Replace the pointwise trivialization coordinate by the global product chart on `V`.
    have hZq : ContMDiffAt J J.tangent ∞ (T% Z) q := hZ q
    rw [Bundle.contMDiffAt_section q] at hZq
    have hEq :
        (fun r : V ↦ (trivializationAt E' (TangentSpace J) q ⟨r, Z r⟩).2) =
          fun r : V ↦ Z r := by
      funext r
      have htoProd :=
        modelOpensTangentBundleTrivializationAt_eq_toProd (J := J) V q
      simpa [Bundle.TotalSpace.toProd] using
        congrArg Prod.snd (congrArg (fun f => f ⟨r, Z r⟩) htoProd)
    simpa [hEq] using hZq
  · intro hZ q
    -- The same global trivialization turns smooth raw coordinates into a smooth section.
    have hZq : ContMDiffAt J 𝓘(𝕜, E') ∞ (fun r : V ↦ Z r) q := hZ q
    have hEq :
        (fun r : V ↦ (trivializationAt E' (TangentSpace J) q ⟨r, Z r⟩).2) =
          fun r : V ↦ Z r := by
      funext r
      have htoProd :=
        modelOpensTangentBundleTrivializationAt_eq_toProd (J := J) V q
      simpa [Bundle.TotalSpace.toProd] using
        congrArg Prod.snd (congrArg (fun f => f ⟨r, Z r⟩) htoProd)
    rw [Bundle.contMDiffAt_section q]
    simpa [hEq] using hZq

omit [IsManifold J ∞ S] in
/-- Helper for Proposition 8.23: pushing the pullback field along an open inclusion recovers the
original ambient vector field. -/
private lemma tangentMap_subtype_val_pullback_eq
    (U : TopologicalSpace.Opens S)
    (X : ∀ p : S, TangentSpace J p)
    (p : U) :
    tangentMap J J (Subtype.val : U → S)
      (T% (VectorField.mpullback J J (Subtype.val : U → S) X) p) =
      T% X p.1 := by
  -- The pullback along the open inclusion uses the inverse derivative of `Subtype.val`.
  simp only [tangentMap, VectorField.mpullback_apply, Bundle.TotalSpace.mk_inj]
  exact (mfderiv_open_subset_inclusion_isInvertible (I := J) U p).self_apply_inverse (X p.1)

omit [IsManifold J ∞ S] in
/-- Helper for Proposition 8.23: pulling back by the inverse of a diffeomorphism pushes vectors
forward by the derivative of the original diffeomorphism. -/
private lemma mpullback_diffeomorph_symm_apply
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H'']
    {K : ModelWithCorners 𝕜 E'' H''}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]
    [IsManifold K (∞ : ℕ∞ω) N]
    (F : S ≃ₘ⟮J, K⟯ N)
    (X : ∀ p : S, TangentSpace J p)
    (p : S) :
    VectorField.mpullback K J F.symm X (F p) = mfderiv J K F p (X p) := by
  -- Rewrite the pullback using the inverse derivative, then differentiate `F.symm ∘ F = id`.
  rw [VectorField.mpullback_apply, F.symm_apply_apply]
  let e := F.symm.mfderivToContinuousLinearEquiv (by simp) (F p)
  have hcoe :
      ↑(F.symm.mfderivToContinuousLinearEquiv (by simp) (F p)) =
        mfderiv K J F.symm (F p) :=
    F.symm.mfderivToContinuousLinearEquiv_coe (by simp) (x := F p)
  refine
    (ContinuousLinearMap.IsInvertible.inverse_apply_eq
      ⟨e, by
        simpa [e] using hcoe.symm⟩).2 ?_
  have hcomp :
      mfderiv J J (F.symm ∘ F) p (X p) =
        mfderiv K J F.symm (F p) (mfderiv J K F p (X p)) := by
    exact mfderiv_comp_apply
      (x := p)
      (g := F.symm)
      (f := F)
      (F.symm.contMDiff.mdifferentiableAt (by simp))
      (F.contMDiff.mdifferentiableAt (by simp))
      (X p)
  have hcomp' :
      mfderiv J J (fun x : S ↦ F.symm (F x)) p (X p) =
        mfderiv K J F.symm (F p) (mfderiv J K F p (X p)) := by
    simpa [Function.comp] using hcomp
  have hid : (fun x : S ↦ F.symm (F x)) = id := by
    funext x
    simp
  rw [hid, mfderiv_id] at hcomp'
  simpa using hcomp'

omit [IsManifold J ∞ S] in
/-- Helper for Proposition 8.23: pulling back by a diffeomorphism and then by its inverse returns
the original vector field. -/
private lemma mpullback_diffeomorph_cancel
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H'']
    {K : ModelWithCorners 𝕜 E'' H''}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]
    [IsManifold K (∞ : ℕ∞ω) N]
    (F : S ≃ₘ⟮J, K⟯ N)
    (X : ∀ p : S, TangentSpace J p) :
    VectorField.mpullback J K F (VectorField.mpullback K J F.symm X) = X := by
  funext p
  -- The inner pullback produces the pushed-forward vector at `F p`, and the outer pullback
  -- applies the inverse derivative of the same diffeomorphism.
  rw [VectorField.mpullback_apply]
  have hpush := mpullback_diffeomorph_symm_apply (J := J) (K := K) F X p
  let e := F.mfderivToContinuousLinearEquiv (by simp) p
  have hcoe :
      ↑(F.mfderivToContinuousLinearEquiv (by simp) p) = mfderiv J K F p :=
    F.mfderivToContinuousLinearEquiv_coe (by simp) (x := p)
  exact
    (ContinuousLinearMap.IsInvertible.inverse_apply_eq
      ⟨e, by
        simpa [e] using hcoe.symm⟩).2 hpush



omit [IsManifold I ∞ M] [IsManifold J ∞ S] in
/-- Helper for Proposition 8.23: lowering the differentiability index preserves immersions because
the same local normal-form charts still witness the immersion statement. -/
private theorem isImmersionOfLe
    {n m : WithTop ℕ∞} {f : S → M} (hmn : m ≤ n)
    (hf : Manifold.IsImmersion J I n f) :
    Manifold.IsImmersion J I m f := by
  -- Keep the same complement choice and the same pointwise chart presentation.
  let hComp := hf.complement
  let hCompImm := hf.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := J) (M := S) hmn) hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I) (M := M) hmn) hx.codChart_mem_maximalAtlas

/-- Helper for Proposition 8.23: choose, at each `p : S`, the unique intrinsic tangent vector
whose image under the derivative of the inclusion equals the ambient tangent vector `Y p`
guaranteed by tangency. -/
private noncomputable def restrictionChoice
    (Y : SmoothVectorFieldOnM) (hYtangent : IsTangentToSubmanifold S J Y) :
    ∀ p : S, TangentSpace J p :=
  fun p ↦
    Classical.choose <|
      (isTangentToSubmanifoldAt_iff_exists (J := J) (X := Y) p).mp (hYtangent p)

/-- Helper for Proposition 8.23: the chosen intrinsic tangent vector at `p : S` maps to the given
ambient tangent vector `Y p` under the derivative of the subtype inclusion. -/
private theorem restrictionChoice_spec
    (Y : SmoothVectorFieldOnM) (hYtangent : IsTangentToSubmanifold S J Y) (p : S) :
    mfderiv J I (Subtype.val : S → M) p (restrictionChoice (J := J) Y hYtangent p) = Y p := by
  -- Unpack the witness used to define the pointwise restriction candidate.
  exact
    Classical.choose_spec <|
      (isTangentToSubmanifoldAt_iff_exists (J := J) (X := Y) p).mp (hYtangent p)

/-- Helper for Proposition 8.23: the pointwise chosen field is already related to `Y`; only its
smoothness remains to be proved locally. -/
private theorem restrictionChoice_f_related
    (hS : IsImmersedSubmanifold I J S)
    (Y : SmoothVectorFieldOnM) (hYtangent : IsTangentToSubmanifold S J Y) :
    f_related (Subtype.val : S → M) (restrictionChoice (J := J) Y hYtangent) Y := by
  -- The inclusion `Subtype.val : S → M` is smooth, and the pointwise equality is the defining
  -- property of the chosen tangent vectors.
  have hsub : ContMDiff J I ∞ (Subtype.val : S → M) := by
    -- The immersed-submanifold hypothesis is exactly an immersion hypothesis on `Subtype.val`.
    let hSInf : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
      isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
        (n := (⊤ : ℕ∞ω)) (by simp) hS
    simpa using hSInf.contMDiff
  refine ⟨hsub, ?_⟩
  intro p
  exact restrictionChoice_spec (J := J) Y hYtangent p

omit [IsManifold I ∞ M] in
/-- Helper for Proposition 8.23: every point of the immersed submanifold has an open neighborhood
whose inclusion into the ambient manifold is a smooth embedding at the current `C^∞` surface. -/
private theorem embeddedNeighborhoodAtOfImmersedSubmanifold
    (hS : IsImmersedSubmanifold I J S) (p : S) :
    ∃ U : TopologicalSpace.Opens S, p ∈ U ∧
      Manifold.IsSmoothEmbedding J I ∞ ((↑) : U → M) := by
  -- Work directly with the immersion normal form at `p`, so the setup stays on the current file's
  -- `∞` surface instead of depending on the stronger packaged wrapper theorem.
  let hp := hS.isImmersionAt p
  let U : TopologicalSpace.Opens S := ⟨(hp.domChart.extend J).source,
    hp.domChart.isOpen_extend_source (I := J)⟩
  let j : U → (hp.codChart.extend I).source :=
    Set.codRestrict ((↑) : U → M) (hp.codChart.extend I).source fun x ↦ by
      simpa [U, OpenPartialHomeomorph.extend_source] using
        hp.source_subset_preimage_source (by
          simpa [U, OpenPartialHomeomorph.extend_source] using x.2)
  let modelSuper : (hp.domChart.extend J).target → E :=
    fun u ↦ hp.equiv (((u : E'), (0 : hp.complement)) : E' × hp.complement)
  let model : (hp.domChart.extend J).target → (hp.codChart.extend I).target :=
    Set.codRestrict modelSuper (hp.codChart.extend I).target fun u ↦
      hp.target_subset_preimage_target u.2
  let eDom :=
    partialEquiv_sourceTargetHomeomorph (hp.domChart.extend J)
      (hp.domChart.continuousOn_extend (I := J))
      (hp.domChart.continuousOn_extend_symm (I := J))
  let eCod :=
    partialEquiv_sourceTargetHomeomorph (hp.codChart.extend I)
      (hp.codChart.continuousOn_extend (I := I))
      (hp.codChart.continuousOn_extend_symm (I := I))
  have hmodelSuper_emb : Topology.IsEmbedding modelSuper := by
    -- In the immersion normal form, the model map is the standard `u ↦ (u, 0)` inclusion followed
    -- by the chosen linear equivalence.
    refine hp.equiv.toHomeomorph.isEmbedding.comp ?_
    exact (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id).comp
      (isEmbedding_prodMkLeft (0 : hp.complement))
  have hmodel_emb : Topology.IsEmbedding model := by
    -- Restrict the normal-form model map to the codomain chart target furnished by the immersion.
    exact hmodelSuper_emb.codRestrict (hp.codChart.extend I).target fun u ↦
      hp.target_subset_preimage_target u.2
  have hchartEq : eCod ∘ j = model ∘ eDom := by
    -- In the chosen charts, the restricted inclusion is exactly the standard model embedding.
    funext x
    apply Subtype.ext
    have hx_source : (x : S) ∈ hp.domChart.source := by
      simpa [U, OpenPartialHomeomorph.extend_source] using x.2
    have hx_cod_source : ((x : S) : M) ∈ hp.codChart.source := by
      simpa [OpenPartialHomeomorph.extend_source] using hp.source_subset_preimage_source hx_source
    have hx_target : hp.domChart.extend J x ∈ (hp.domChart.extend J).target :=
      (hp.domChart.extend J).map_source x.2
    simpa [U, j, model, modelSuper, eDom, eCod, partialEquiv_sourceTargetHomeomorph,
      Function.comp, OpenPartialHomeomorph.extend_coe, hx_source, hx_cod_source,
      hp.domChart.left_inv hx_source] using hp.writtenInCharts hx_target
  have hj_emb : Topology.IsEmbedding j := by
    -- Conjugate the restricted inclusion by the source and codomain chart homeomorphisms.
    have hcomp : Topology.IsEmbedding (eCod ∘ j) := by
      rw [hchartEq]
      exact hmodel_emb.comp eDom.isEmbedding
    exact (Topology.IsEmbedding.of_comp_iff eCod.isEmbedding).mp hcomp
  have hUemb : Topology.IsEmbedding ((↑) : U → M) := by
    -- Forget the codomain restriction from the chart source back to the ambient manifold.
    simpa [U, j, Function.comp] using Topology.IsEmbedding.subtypeVal.comp hj_emb
  refine ⟨U, ?_, ?_⟩
  · -- The point `p` lies in the source of the local immersion chart used to define `U`.
    simpa [U, OpenPartialHomeomorph.extend_source] using hp.mem_domChart_source
  · -- Compose the open-subtype immersion `U ↪ S` with the ambient immersed inclusion `S ↪ M`.
    let hSInf : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
      isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
        (n := (⊤ : ℕ∞ω)) (by simp) hS
    refine Manifold.IsSmoothEmbedding.mk ?_ hUemb
    simpa [Function.comp] using
      Manifold.IsImmersion.ex416_comp hSInf (Manifold.IsImmersion.of_opens U)

/-- Helper for Proposition 8.23: on an embedded patch, the pointwise chosen intrinsic tangent
vector still maps to the ambient vector `Y q`. -/
private theorem restrictionChoiceOnEmbeddedPatch_spec
    {U : TopologicalSpace.Opens S}
    (Y : SmoothVectorFieldOnM) (hYtangent : IsTangentToSubmanifold S J Y) :
    ∀ q : U,
      mfderiv J I (Subtype.val : S → M) q.1
        (restrictionChoice (J := J) Y hYtangent q.1) = Y q := by
  -- This is the original pointwise defining identity, now specialized to a patch point `q : U`.
  intro q
  exact restrictionChoice_spec (J := J) Y hYtangent q.1

/-- Helper for Proposition 8.23: differentiating the immersion normal form identifies the
subtype-inclusion derivative with the chart-level model map on tangent vectors. -/
private theorem chartExtend_symm_mdifferentiableWithin_range
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    {e : OpenPartialHomeomorph N H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ N) {p : N} (hp : p ∈ e.source) :
    MDifferentiableWithinAt 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p) := by
  letI : IsManifold J 1 N :=
    IsManifold.of_le (m := 1) (n := (∞ : ℕ∞ω)) (by simp)
  have he_one : e ∈ IsManifold.maximalAtlas J 1 N :=
    IsManifold.maximalAtlas_subset_of_le (I := J) (M := N)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) he
  have hid :
      MDifferentiableWithinAt J J (id : N → N) Set.univ p := by
    -- The inverse-chart derivative bridge starts from the trivial differentiability of `id`.
    simpa using
      (mdifferentiableWithinAt_id (I := J) (s := Set.univ) (x := p) :
        MDifferentiableWithinAt J J (id : N → N) Set.univ p)
  -- Re-express `id` in chart coordinates to read off differentiability of the inverse chart.
  simpa [Function.comp] using
    (mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas
      (I := J) (I' := J) (e := e) (f := id) (s := Set.univ) he_one hp).mp hid

/-- Helper for Proposition 8.23: differentiating the chart left-inverse identity on `e.source`
produces a concrete left inverse for the derivative of `e.extend`. -/
private theorem chartExtend_mfderiv_left_inverse
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    {e : OpenPartialHomeomorph N H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ N) {p : N} (hp : p ∈ e.source) :
    (mfderivWithin 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p)).comp
      (mfderiv J 𝓘(𝕜, E') (e.extend J) p) =
      ContinuousLinearMap.id 𝕜 (TangentSpace J p) := by
  letI : IsManifold J 1 N :=
    IsManifold.of_le (m := 1) (n := (∞ : ℕ∞ω)) (by simp)
  have he_one : e ∈ IsManifold.maximalAtlas J 1 N :=
    IsManifold.maximalAtlas_subset_of_le (I := J) (M := N)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) he
  have hsource_unique : UniqueMDiffWithinAt J e.source p :=
    e.open_source.uniqueMDiffWithinAt hp
  have hchart :
      MDifferentiableAt J 𝓘(𝕜, E') (e.extend J) p := by
    -- Maximal-atlas charts are differentiable at every source point.
    exact
      (contMDiffAt_extend (I := J) (e := e) he_one hp).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hrange :
      MDifferentiableWithinAt 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p) :=
    chartExtend_symm_mdifferentiableWithin_range (J := J) he hp
  have hchart_within :
      mfderiv J 𝓘(𝕜, E') (e.extend J) p =
        mfderivWithin J 𝓘(𝕜, E') (e.extend J) e.source p := by
    -- On the open chart source, the within derivative agrees with the ordinary derivative.
    symm
    exact mfderivWithin_eq_mfderiv hsource_unique hchart
  rw [hchart_within, ← mfderivWithin_comp_of_eq]
  · -- Differentiate the left-inverse identity on the chart source where the source-side
    -- `UniqueMDiffWithinAt` hypothesis is available.
    rw [← mfderivWithin_id hsource_unique]
    apply Filter.EventuallyEq.mfderivWithin_eq_of_mem
    · refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
      intro z hz
      simpa [Function.comp] using e.extend_left_inv (I := J) hz
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

/-- Helper for Proposition 8.23: the derivative of a maximal-atlas chart is injective because
the chart inverse cancels it on the chart source. -/
private theorem chartExtend_mfderiv_injective
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    {e : OpenPartialHomeomorph N H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ N) {p : N} (hp : p ∈ e.source) :
    Function.Injective (mfderiv J 𝓘(𝕜, E') (e.extend J) p) := by
  let Linv :=
    mfderivWithin 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p)
  intro w₁ w₂ hw
  have hleft := chartExtend_mfderiv_left_inverse (J := J) he hp
  have hp_left : (e.extend J).symm (e.extend J p) = p :=
    e.extend_left_inv (I := J) hp
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

/-- Helper for Proposition 8.23: differentiating the immersion normal form identifies the
subtype-inclusion derivative with the chart-level model map on tangent vectors. -/
private theorem subtypeVal_chartPushforward_eq_model
    (hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M))
    (p : S) (w : TangentSpace J p) :
    let hImmAt := hImm.isImmersionAt p
    let L : E' →L[𝕜] E :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
    (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) p))
      (mfderiv J I (Subtype.val : S → M) p w) =
      L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w) := by
  let hImmAt := hImm.isImmersionAt p
  let L : E' →L[𝕜] E :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
  have hdomChart_source : hImmAt.domChart.source ∈ nhds p :=
    IsOpen.mem_nhds hImmAt.domChart.open_source hImmAt.mem_domChart_source
  have hEqOn :
      Set.EqOn ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M))
        (L ∘ (hImmAt.domChart.extend J)) hImmAt.domChart.source := by
    intro y hy
    -- Read the immersion normal form directly on the source chart neighborhood.
    have hy_target :
        hImmAt.domChart.extend J y ∈ (hImmAt.domChart.extend J).target :=
      (hImmAt.domChart.extend J).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hy
    simpa [Function.comp, L, OpenPartialHomeomorph.extend_coe,
      hImmAt.domChart.left_inv hy, ContinuousLinearMap.comp_apply] using
      hImmAt.writtenInCharts hy_target
  have hEq :
      ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M)) =ᶠ[nhds p]
        L ∘ (hImmAt.domChart.extend J) :=
    hEqOn.eventuallyEq_of_mem hdomChart_source
  have hsub :
      MDifferentiableAt J I (Subtype.val : S → M) p :=
    hImm.contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hdomChart_mem_maximalAtlas_one :
      hImmAt.domChart ∈ IsManifold.maximalAtlas J 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := J) (M := S)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) hImmAt.domChart_mem_maximalAtlas
  have hcodChart_mem_maximalAtlas_one :
      hImmAt.codChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (I := I) (M := M)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) hImmAt.codChart_mem_maximalAtlas
  have hdom :
      MDifferentiableAt J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p := by
    -- Maximal-atlas charts are differentiable in model coordinates.
    exact
      (contMDiffAt_extend (I := J) (e := hImmAt.domChart)
        hdomChart_mem_maximalAtlas_one hImmAt.mem_domChart_source).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hcod :
      MDifferentiableAt I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) p) := by
    -- The ambient chart enjoys the same differentiability property.
    exact
      (contMDiffAt_extend (I := I) (e := hImmAt.codChart)
        hcodChart_mem_maximalAtlas_one hImmAt.mem_codChart_source).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hL :
      MDifferentiableAt 𝓘(𝕜, E') 𝓘(𝕜, E) L (hImmAt.domChart.extend J p) := by
    -- The linear model map differentiates to itself.
    exact L.contMDiffAt.mdifferentiableAt (by simp : (1 : ℕ∞ω) ≠ 0)
  have hmfderiv_eq :
      mfderiv J 𝓘(𝕜, E) (((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M))) p =
        mfderiv J 𝓘(𝕜, E) (L ∘ (hImmAt.domChart.extend J)) p := by
    -- Differentiate the two eventually equal source-side expressions at the base point.
    exact hEq.mfderiv_eq
  have hleft :
      (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) p))
        (mfderiv J I (Subtype.val : S → M) p w) =
      mfderiv J 𝓘(𝕜, E) (((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M))) p w := by
    symm
    exact mfderiv_comp_apply (x := p) hcod hsub w
  have hright :
      mfderiv J 𝓘(𝕜, E) (L ∘ (hImmAt.domChart.extend J)) p w =
        L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w) := by
    simpa [Function.comp, mfderiv_eq_fderiv] using
      (mfderiv_comp_apply (x := p) (g := L) (f := hImmAt.domChart.extend J)
        hL hdom w)
  -- Apply the chain rule on both sides of the source-side equality.
  exact hleft.trans <| hmfderiv_eq ▸ hright

omit [IsManifold I ∞ M] [IsManifold J ∞ S] in
/-- Helper for Proposition 8.23: the normal-form projection `fst ∘ hImmAt.equiv.symm` is a left
inverse for the immersion model map `hImmAt.equiv ∘ inl`. -/
private theorem normalFormProjection_leftInverse
    (hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M))
    (p : S) :
    let hImmAt := hImm.isImmersionAt p
    let L : E' →L[𝕜] E :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
    let P : E →L[𝕜] E' :=
      (ContinuousLinearMap.fst 𝕜 E' hImmAt.complement).comp
        hImmAt.equiv.symm.toContinuousLinearMap
    P.comp L = ContinuousLinearMap.id 𝕜 E' := by
  -- Evaluate the composite on a model vector and cancel the normal-form equivalence.
  ext u
  simp [ContinuousLinearMap.comp_apply]

/-- Helper for Proposition 8.23: fixing the immersion charts at `p` and differentiating their
normal-form identity at any `q` in the source chart gives the chart-level model formula for the
subtype inclusion derivative. -/
private theorem fixedImmersionChartPushforward_eq_model
    (hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M))
    (p : S)
    (q : (⟨(hImm.isImmersionAt p).domChart.source,
      (hImm.isImmersionAt p).domChart.open_source⟩ : TopologicalSpace.Opens S))
    (w : TangentSpace J q.1) :
    let hImmAt := hImm.isImmersionAt p
    let L : E' →L[𝕜] E :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
    (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) q.1))
      (mfderiv J I (Subtype.val : S → M) q.1 w) =
      L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1) w) := by
  let hImmAt := hImm.isImmersionAt p
  let L : E' →L[𝕜] E :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
  have hdomChart_source : hImmAt.domChart.source ∈ nhds q.1 :=
    IsOpen.mem_nhds hImmAt.domChart.open_source q.2
  have hEqOn :
      Set.EqOn ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M))
        (L ∘ (hImmAt.domChart.extend J)) hImmAt.domChart.source := by
    intro y hy
    -- The fixed immersion normal form at `p` already holds on the whole source chart.
    have hy_target :
        hImmAt.domChart.extend J y ∈ (hImmAt.domChart.extend J).target :=
      (hImmAt.domChart.extend J).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hy
    simpa [Function.comp, L, OpenPartialHomeomorph.extend_coe,
      hImmAt.domChart.left_inv hy, ContinuousLinearMap.comp_apply] using
      hImmAt.writtenInCharts hy_target
  have hEq :
      ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M)) =ᶠ[nhds q.1]
        L ∘ (hImmAt.domChart.extend J) :=
    hEqOn.eventuallyEq_of_mem hdomChart_source
  have hsub :
      MDifferentiableAt J I (Subtype.val : S → M) q.1 :=
    hImm.contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hdomChart_mem_maximalAtlas_one :
      hImmAt.domChart ∈ IsManifold.maximalAtlas J 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := J) (M := S)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) hImmAt.domChart_mem_maximalAtlas
  have hcodChart_mem_maximalAtlas_one :
      hImmAt.codChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (I := I) (M := M)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) hImmAt.codChart_mem_maximalAtlas
  have hdom :
      MDifferentiableAt J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1 := by
    -- The fixed source chart is differentiable at every point of its source.
    exact
      (contMDiffAt_extend (I := J) (e := hImmAt.domChart)
        hdomChart_mem_maximalAtlas_one q.2).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hq_cod_source : ((q.1 : S) : M) ∈ hImmAt.codChart.source :=
    hImmAt.source_subset_preimage_source q.2
  have hcod :
      MDifferentiableAt I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) q.1) := by
    -- The same holds for the fixed ambient chart at the image point.
    exact
      (contMDiffAt_extend (I := I) (e := hImmAt.codChart)
        hcodChart_mem_maximalAtlas_one hq_cod_source).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hL :
      MDifferentiableAt 𝓘(𝕜, E') 𝓘(𝕜, E) L (hImmAt.domChart.extend J q.1) := by
    -- The model-side inclusion map is linear, hence smooth.
    exact L.contMDiffAt.mdifferentiableAt (by simp : (1 : ℕ∞ω) ≠ 0)
  have hmfderiv_eq :
      mfderiv J 𝓘(𝕜, E) (((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M))) q.1 =
        mfderiv J 𝓘(𝕜, E) (L ∘ (hImmAt.domChart.extend J)) q.1 := by
    -- Differentiate the two eventually equal source-side expressions at `q`.
    exact hEq.mfderiv_eq
  have hleft :
      (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) q.1))
        (mfderiv J I (Subtype.val : S → M) q.1 w) =
      mfderiv J 𝓘(𝕜, E) (((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M))) q.1 w := by
    symm
    exact mfderiv_comp_apply (x := q.1) hcod hsub w
  have hright :
      mfderiv J 𝓘(𝕜, E) (L ∘ (hImmAt.domChart.extend J)) q.1 w =
        L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1) w) := by
    simpa [Function.comp, mfderiv_eq_fderiv] using
      (mfderiv_comp_apply (x := q.1) (g := L) (f := hImmAt.domChart.extend J)
        hL hdom w)
  -- Apply the chain rule to the fixed-chart identity.
  exact hleft.trans <| hmfderiv_eq ▸ hright

/-- Helper for Proposition 8.23: in the immersion source chart, the chosen restriction field has
coordinates obtained by projecting the ambient chart coordinates of `Y`. -/
private theorem restrictionChoice_sourceChartCoordinates_eq_projectedAmbient
    (hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M))
    (Y : SmoothVectorFieldOnM)
    (hYtangent : IsTangentToSubmanifold S J Y)
    (p : S)
    (q : (⟨(hImm.isImmersionAt p).domChart.source,
      (hImm.isImmersionAt p).domChart.open_source⟩ : TopologicalSpace.Opens S)) :
    ((ContinuousLinearMap.fst 𝕜 E' (hImm.isImmersionAt p).complement).comp
        (hImm.isImmersionAt p).equiv.symm.toContinuousLinearMap)
        ((mfderiv I 𝓘(𝕜, E) ((hImm.isImmersionAt p).codChart.extend I)
          ((Subtype.val : S → M) q.1)) (Y q.1))
      =
    (mfderiv J 𝓘(𝕜, E') ((hImm.isImmersionAt p).domChart.extend J) q.1)
      (restrictionChoice (J := J) Y hYtangent q.1) := by
  let hImmAt := hImm.isImmersionAt p
  let L : E' →L[𝕜] E :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
  let P : E →L[𝕜] E' :=
    (ContinuousLinearMap.fst 𝕜 E' hImmAt.complement).comp
      hImmAt.equiv.symm.toContinuousLinearMap
  have hpush :
      (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) q.1))
        (mfderiv J I (Subtype.val : S → M) q.1
          (restrictionChoice (J := J) Y hYtangent q.1)) =
      L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1)
        (restrictionChoice (J := J) Y hYtangent q.1)) := by
    -- Differentiate the fixed-chart immersion identity at `q` and evaluate it on the chosen
    -- intrinsic tangent vector.
    simpa [hImmAt, L] using
      fixedImmersionChartPushforward_eq_model (I := I) (J := J) hImm p q
        (restrictionChoice (J := J) Y hYtangent q.1)
  have hprojected :
      P ((mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) q.1)) (Y q.1)) =
        (P.comp L)
          ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1)
            (restrictionChoice (J := J) Y hYtangent q.1)) := by
    -- Apply the fixed projection to the model identity and rewrite the subtype derivative using
    -- the defining property of `restrictionChoice`.
    simpa [P, ContinuousLinearMap.comp_apply,
      restrictionChoice_spec (J := J) Y hYtangent q.1] using congrArg P hpush
  have hleftInv : P.comp L = ContinuousLinearMap.id 𝕜 E' := by
    simpa [hImmAt, L, P] using normalFormProjection_leftInverse (I := I) (J := J) hImm p
  -- Cancel the fixed model inclusion with the previously isolated left inverse.
  simpa [P, hleftInv, ContinuousLinearMap.comp_apply] using hprojected

/-- Helper for Proposition 8.23: the manifold derivative of an immersed subtype inclusion is
injective at every point. -/
private theorem subtypeVal_mfderiv_injective
    (hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M))
    (p : S) :
    Function.Injective (mfderiv J I (Subtype.val : S → M) p) := by
  let hImmAt := hImm.isImmersionAt p
  let L : E' →L[𝕜] E :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
  have hL_injective : Function.Injective L := by
    intro u v huv
    have hpair :
        (u, (0 : hImmAt.complement)) = (v, (0 : hImmAt.complement)) := by
      apply hImmAt.equiv.injective
      simpa [L, ContinuousLinearMap.comp_apply] using huv
    exact (Prod.mk.inj hpair).1
  intro w₁ w₂ hw
  have hw_chart :
      L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₁) =
        L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₂) := by
    have hw₁_model :
        L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₁) =
          (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) p))
            (mfderiv J I (Subtype.val : S → M) p w₁) := by
      simpa [hImmAt, L] using
        (subtypeVal_chartPushforward_eq_model (I := I) (J := J) hImm p w₁).symm
    have hw₂_model :
        (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) p))
            (mfderiv J I (Subtype.val : S → M) p w₂) =
          L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₂) := by
      simpa [hImmAt, L] using subtypeVal_chartPushforward_eq_model (I := I) (J := J) hImm p w₂
    -- Compare the two vectors after applying the ambient chart derivative.
    exact hw₁_model.trans <| by simpa [hw] using hw₂_model
  have hdomChart_mem_maximalAtlas_one :
      hImmAt.domChart ∈ IsManifold.maximalAtlas J 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := J) (M := S)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) hImmAt.domChart_mem_maximalAtlas
  have hsource_chart :
      (mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₁ =
        (mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₂ :=
    hL_injective hw_chart
  exact
    chartExtend_mfderiv_injective (J := J) hImmAt.domChart_mem_maximalAtlas
      hImmAt.mem_domChart_source hsource_chart

/-- Helper for Proposition 8.23: on the fixed immersion-chart source, the ambient chart
coordinates of `Y` vary smoothly when measured using the within-derivative on the ambient chart
source. -/
private theorem ambientWithinChartCoordinates_contMDiffOnDomChartSource
    (hS : IsImmersedSubmanifold I J S)
    (Y : SmoothVectorFieldOnM)
    (p : S) :
    let hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
      isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
        (n := (⊤ : ℕ∞ω)) (by simp) hS
    let hImmAt := hImm.isImmersionAt p
    ContMDiffOn J 𝓘(𝕜, E) ∞
      (fun q : S ↦
        (mfderivWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source
          q.1) (Y q.1))
      hImmAt.domChart.source := by
  let hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
    isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
      (n := (⊤ : ℕ∞ω)) (by simp) hS
  let hImmAt := hImm.isImmersionAt p
  have hsub : ContMDiff J I ∞ (Subtype.val : S → M) := by
    -- The immersed-submanifold hypothesis gives smoothness of the subtype inclusion.
    simpa using hImm.contMDiff
  have hYsubOn :
      ContMDiffOn J I.tangent ∞
        (fun q : S ↦ (show TangentBundle I M from ⟨q.1, Y q.1⟩)) hImmAt.domChart.source := by
    intro q hq
    -- Restrict the ambient smooth tangent section along the subtype inclusion pointwise.
    have hAt :
        ContMDiffAt J I.tangent ∞
          (fun q : S ↦ (show TangentBundle I M from ⟨q.1, Y q.1⟩)) q := by
      simpa [Function.comp] using (Y.contMDiff q.1).comp q (hsub q)
    exact hAt.contMDiffWithinAt
  have hcodChartOn :
      ContMDiffOn I 𝓘(𝕜, E) ∞ (hImmAt.codChart.extend I) hImmAt.codChart.source :=
    contMDiffOn_extend (I := I) (n := (∞ : ℕ∞ω)) hImmAt.codChart_mem_maximalAtlas
  have htan :
      ContMDiffOn I.tangent (𝓘(𝕜, E)).tangent ∞
        (tangentMapWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source)
        ((fun z : TangentBundle I M ↦ z.1) ⁻¹' hImmAt.codChart.source) := by
    -- The tangent map of the fixed ambient chart is smooth on the preimage of its chart source.
    exact hcodChartOn.contMDiffOn_tangentMapWithin
      (m := (∞ : ℕ∞ω)) (by simp) hImmAt.codChart.open_source.uniqueMDiffOn
  have hcomp :
      ContMDiffOn J (𝓘(𝕜, E)).tangent ∞
        ((tangentMapWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source) ∘
          (fun q : S ↦ (show TangentBundle I M from ⟨q.1, Y q.1⟩)))
        hImmAt.domChart.source := by
    -- Compose the tangent map with the ambient field restricted to the immersed source chart.
    refine htan.comp hYsubOn ?_
    intro q hq
    change q.1 ∈ hImmAt.codChart.source
    simpa using hImmAt.source_subset_preimage_source hq
  have hsnd :
      ContMDiffOn J 𝓘(𝕜, E) ∞
        (fun q : S ↦
          ((tangentMapWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source)
            (show TangentBundle I M from ⟨q.1, Y q.1⟩)).2)
        hImmAt.domChart.source := by
    -- On the model-space tangent bundle, smoothness of the second projection recovers the raw
    -- coordinate vector field.
    exact
      (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).comp_contMDiffOn hcomp
  simpa [tangentMapWithin_snd] using hsnd

/-- Helper for Proposition 8.23: on the fixed immersion-chart source, projecting the ambient chart
coordinates of `Y` to the tangent directions of the submanifold preserves smoothness. -/
private theorem projectedAmbientCoordinates_contMDiffOnDomChartSource
    (hS : IsImmersedSubmanifold I J S)
    (Y : SmoothVectorFieldOnM)
    (p : S) :
    let hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
      isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
        (n := (⊤ : ℕ∞ω)) (by simp) hS
    let hImmAt := hImm.isImmersionAt p
    let P : E →L[𝕜] E' :=
      (ContinuousLinearMap.fst 𝕜 E' hImmAt.complement).comp
        hImmAt.equiv.symm.toContinuousLinearMap
    ContMDiffOn J 𝓘(𝕜, E') ∞
      (fun q : S ↦
        P ((mfderivWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source
          q.1) (Y q.1)))
      hImmAt.domChart.source := by
  let hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
    isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
      (n := (⊤ : ℕ∞ω)) (by simp) hS
  let hImmAt := hImm.isImmersionAt p
  let P : E →L[𝕜] E' :=
    (ContinuousLinearMap.fst 𝕜 E' hImmAt.complement).comp
      hImmAt.equiv.symm.toContinuousLinearMap
  have hambient :
      ContMDiffOn J 𝓘(𝕜, E) ∞
        (fun q : S ↦
          (mfderivWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source
            q.1) (Y q.1))
        hImmAt.domChart.source :=
    ambientWithinChartCoordinates_contMDiffOnDomChartSource (I := I) (J := J) hS Y p
  -- The fixed linear projection from the immersion normal form preserves smoothness.
  simpa [P, ContinuousLinearMap.comp_apply] using P.contMDiff.comp_contMDiffOn hambient

/-- Helper for Proposition 8.23: after transporting the chosen restriction field to the chart
target open subset, its raw `E'`-valued coordinates agree with the projected ambient chart
coordinates of `Y`. -/
private theorem restrictionChoice_chartTarget_eq_projectedAmbient
    (hS : IsImmersedSubmanifold I J S)
    (Y : SmoothVectorFieldOnM)
    (hYtangent : IsTangentToSubmanifold S J Y)
    (p : S) :
    let hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
      isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
        (n := (⊤ : ℕ∞ω)) (by simp) hS
    let hImmAt := hImm.isImmersionAt p
    let U : TopologicalSpace.Opens S := ⟨hImmAt.domChart.source, hImmAt.domChart.open_source⟩
    let V : TopologicalSpace.Opens H' := ⟨hImmAt.domChart.target, hImmAt.domChart.open_target⟩
    let X : ∀ q : S, TangentSpace J q := restrictionChoice (J := J) Y hYtangent
    let XU : ∀ q : U, TangentSpace J q :=
      VectorField.mpullback J J (Subtype.val : U → S) X
    let F : U ≃ₘ⟮J, J⟯ V :=
      chartSourceTargetDiffeomorph (J := J) hImmAt.domChart hImmAt.domChart_mem_maximalAtlas
    let Z : ∀ q : V, TangentSpace J q := VectorField.mpullback J J F.symm XU
    let P : E →L[𝕜] E' :=
      (ContinuousLinearMap.fst 𝕜 E' hImmAt.complement).comp
        hImmAt.equiv.symm.toContinuousLinearMap
    (fun q : U ↦ Z (F q)) =
      (fun q : U ↦
        P ((mfderivWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source
          q.1) (Y q.1))) := by
  let hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
    isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
      (n := (⊤ : ℕ∞ω)) (by simp) hS
  let hImmAt := hImm.isImmersionAt p
  let U : TopologicalSpace.Opens S := ⟨hImmAt.domChart.source, hImmAt.domChart.open_source⟩
  let V : TopologicalSpace.Opens H' := ⟨hImmAt.domChart.target, hImmAt.domChart.open_target⟩
  let X : ∀ q : S, TangentSpace J q := restrictionChoice (J := J) Y hYtangent
  let XU : ∀ q : U, TangentSpace J q :=
    VectorField.mpullback J J (Subtype.val : U → S) X
  let F : U ≃ₘ⟮J, J⟯ V :=
    chartSourceTargetDiffeomorph (J := J) hImmAt.domChart hImmAt.domChart_mem_maximalAtlas
  let Z : ∀ q : V, TangentSpace J q := VectorField.mpullback J J F.symm XU
  let P : E →L[𝕜] E' :=
    (ContinuousLinearMap.fst 𝕜 E' hImmAt.complement).comp
      hImmAt.equiv.symm.toContinuousLinearMap
  funext q
  have hcoordFun :
      ((fun r : V ↦ J r) ∘ F) = (hImmAt.domChart.extend J) ∘ (Subtype.val : U → S) := by
    funext r
    change J (F r) = J (hImmAt.domChart r.1)
    have hFapply : F r = hImmAt.domChart.toHomeomorphSourceTarget r := by
      simpa [F] using
        chartSourceTargetDiffeomorph_apply (J := J) hImmAt.domChart
          hImmAt.domChart_mem_maximalAtlas r
    simpa using congrArg (fun z : V ↦ J z) hFapply
  have hcoordAt :
      MDifferentiableAt J 𝓘(𝕜, E') (fun r : V ↦ J r) (F q) := by
    -- On the target open subset, the preferred chart is the explicit coordinate map `r ↦ J r`.
    simpa [extChartAt_coe, TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq] using
      (contMDiffAt_extChartAt (I := J) (n := (∞ : ℕ∞ω)) (x := F q)).mdifferentiableAt
        (by simp)
  have hFAt : MDifferentiableAt J J F q := F.contMDiff.mdifferentiableAt (by simp)
  have hsubAt : MDifferentiableAt J J (Subtype.val : U → S) q := by
    exact
      (contMDiff_subtype_val : ContMDiff J J ∞ (Subtype.val : U → S)).mdifferentiableAt
        (by simp)
  have hextAt :
      MDifferentiableAt J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1 := by
    exact
      (contMDiffAt_extend (I := J) (e := hImmAt.domChart)
        (IsManifold.maximalAtlas_subset_of_le (I := J) (M := S)
          (m := 1) (n := (∞ : ℕ∞ω)) (by simp) hImmAt.domChart_mem_maximalAtlas)
        q.2).mdifferentiableAt (by simp : (1 : ℕ∞ω) ≠ 0)
  have hpush :
      Z (F q) = mfderiv J J F q (XU q) := by
    -- Reinterpret `Z` as the canonical pushforward `F _* XU`.
    simpa [Z] using
      (VectorField.f_related_apply (f_related_pushforward_of_diffeomorph F XU) q).symm
  have hchainLeft :
      mfderiv J 𝓘(𝕜, E') (fun r : V ↦ J r) (F q)
          (mfderiv J J F q (XU q)) =
        mfderiv J 𝓘(𝕜, E') (((fun r : V ↦ J r) ∘ F)) q (XU q) := by
    -- Differentiate the chart-target composite in model coordinates.
    symm
    simpa [Function.comp] using
      (mfderiv_comp_apply (x := q) (g := fun r : V ↦ J r) (f := F) hcoordAt hFAt (XU q))
  have hchainRight :
      mfderiv J 𝓘(𝕜, E') (((hImmAt.domChart.extend J) ∘ (Subtype.val : U → S))) q
          (XU q) =
        mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1
          (mfderiv J J (Subtype.val : U → S) q (XU q)) := by
    -- Differentiating the source-side factorization introduces the derivative of the open
    -- inclusion `Subtype.val : U → S`.
    simpa [Function.comp] using
      (mfderiv_comp_apply_of_eq (x := q) (g := hImmAt.domChart.extend J)
        (f := (Subtype.val : U → S)) hextAt hsubAt rfl (XU q))
  have hcoordDeriv :
      mfderiv J 𝓘(𝕜, E') (fun r : V ↦ J r) (F q)
          (mfderiv J J F q (XU q)) =
        mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1
          (mfderiv J J (Subtype.val : U → S) q (XU q)) := by
    have hcompMfderiv :
        mfderiv J 𝓘(𝕜, E') (((fun r : V ↦ J r) ∘ F)) q =
          mfderiv J 𝓘(𝕜, E') (((hImmAt.domChart.extend J) ∘ (Subtype.val : U → S))) q := by
      exact mfderiv_congr (x := q) hcoordFun
    have hmid :
        mfderiv J 𝓘(𝕜, E') (((fun r : V ↦ J r) ∘ F)) q (XU q) =
          mfderiv J 𝓘(𝕜, E') (((hImmAt.domChart.extend J) ∘ (Subtype.val : U → S))) q
            (XU q) := by
      simpa using congrArg
        (fun L : TangentSpace J q →L[𝕜] E' ↦ L (XU q)) hcompMfderiv
    exact hchainLeft.trans (hmid.trans hchainRight)
  have hsubApply :
      mfderiv J J (Subtype.val : U → S) q (XU q) = X q.1 := by
    -- The restricted field `XU` was defined by pulling `X` back along the open inclusion.
    simpa [tangentMap, XU, X] using tangentMap_subtype_val_pullback_eq (J := J) U X q
  have hstep1 :
      Z (F q) =
        mfderiv J 𝓘(𝕜, E') (fun r : V ↦ J r) (F q) (Z (F q)) := by
    symm
    exact modelOpensCoordinate_eq_self (J := J) V (F q) (Z (F q))
  have hstep2 :
      mfderiv J 𝓘(𝕜, E') (fun r : V ↦ J r) (F q) (Z (F q)) =
        mfderiv J 𝓘(𝕜, E') (fun r : V ↦ J r) (F q) (mfderiv J J F q (XU q)) := by
    rw [hpush]
  have hstep3 :
      mfderiv J 𝓘(𝕜, E') (fun r : V ↦ J r) (F q) (mfderiv J J F q (XU q)) =
        mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1
          (mfderiv J J (Subtype.val : U → S) q (XU q)) :=
    hcoordDeriv
  have hstep4 :
      mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1
          (mfderiv J J (Subtype.val : U → S) q (XU q)) =
        (mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1) (X q.1) := by
    rw [hsubApply]
  have hstep5 :
      (mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1) (X q.1) =
        P ((mfderivWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source
          q.1) (Y q.1)) := by
    have hq_cod_source : ((q.1 : S) : M) ∈ hImmAt.codChart.source :=
      hImmAt.source_subset_preimage_source q.2
    have hcod :
        MDifferentiableAt I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) q.1) := by
      exact
        (contMDiffAt_extend (I := I) (e := hImmAt.codChart)
          (IsManifold.maximalAtlas_subset_of_le (I := I) (M := M)
            (m := 1) (n := (∞ : ℕ∞ω)) (by simp) hImmAt.codChart_mem_maximalAtlas)
          hq_cod_source).mdifferentiableAt (by simp : (1 : ℕ∞ω) ≠ 0)
    have hwithin_eq :
        mfderivWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source q.1 =
          mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) q.1 := by
      exact
        mfderivWithin_eq_mfderiv
          (hImmAt.codChart.open_source.uniqueMDiffWithinAt hq_cod_source)
          hcod
    have hstep5' :
        (mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) q.1) (X q.1) =
          P ((mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) q.1) (Y q.1)) := by
      simpa [P, X] using
        (restrictionChoice_sourceChartCoordinates_eq_projectedAmbient
          (I := I) (J := J) hImm Y hYtangent p q).symm
    rw [hwithin_eq]
    exact hstep5'
  exact hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans hstep5)))

/-- Helper for Proposition 8.23: the pointwise chosen intrinsic restriction field is smooth at a
fixed point once one transports the problem to an embedded neighborhood patch. -/
private theorem restrictionChoiceContMDiffOnChartSource
    (hS : IsImmersedSubmanifold I J S)
    (Y : SmoothVectorFieldOnM)
    (hYtangent : IsTangentToSubmanifold S J Y)
    (p : S) :
    let hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
      isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
        (n := (⊤ : ℕ∞ω)) (by simp) hS
    let hImmAt := hImm.isImmersionAt p
    ContMDiffOn J J.tangent ∞ (T% (restrictionChoice (J := J) Y hYtangent))
      hImmAt.domChart.source := by
  let hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
    isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
      (n := (⊤ : ℕ∞ω)) (by simp) hS
  let hImmAt := hImm.isImmersionAt p
  let U : TopologicalSpace.Opens S := ⟨hImmAt.domChart.source, hImmAt.domChart.open_source⟩
  let V : TopologicalSpace.Opens H' := ⟨hImmAt.domChart.target, hImmAt.domChart.open_target⟩
  let X : ∀ q : S, TangentSpace J q := restrictionChoice (J := J) Y hYtangent
  let XU : ∀ q : U, TangentSpace J q := VectorField.mpullback J J (Subtype.val : U → S) X
  let F : U ≃ₘ⟮J, J⟯ V :=
    chartSourceTargetDiffeomorph (J := J) hImmAt.domChart hImmAt.domChart_mem_maximalAtlas
  let Z : ∀ q : V, TangentSpace J q := VectorField.mpullback J J F.symm XU
  let P : E →L[𝕜] E' :=
    (ContinuousLinearMap.fst 𝕜 E' hImmAt.complement).comp
      hImmAt.equiv.symm.toContinuousLinearMap
  have hbridge :
      (fun q : U ↦ Z (F q)) =
        (fun q : U ↦
          P ((mfderivWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source
            q.1) (Y q.1))) :=
    restrictionChoice_chartTarget_eq_projectedAmbient (I := I) (J := J) hS Y hYtangent p
  have hcoordSource :
      ContMDiff J 𝓘(𝕜, E') ∞ (fun q : U ↦ Z (F q)) := by
    have hproj :
        ContMDiffOn J 𝓘(𝕜, E') ∞
          (fun q : S ↦
            P ((mfderivWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source
              q.1) (Y q.1)))
          hImmAt.domChart.source :=
      projectedAmbientCoordinates_contMDiffOnDomChartSource (I := I) (J := J) hS Y p
    have hprojRestr :
        ContMDiff J 𝓘(𝕜, E') ∞
          (fun q : U ↦
            P ((mfderivWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source
              q.1) (Y q.1))) :=
      (contMDiffOn_iff_contMDiff_restrict
        (J := J) (K := 𝓘(𝕜, E')) U
        (fun q : S ↦
          P ((mfderivWithin I 𝓘(𝕜, E) (hImmAt.codChart.extend I) hImmAt.codChart.source
            q.1) (Y q.1)))).1 hproj
    rw [hbridge]
    exact hprojRestr
  have hcoordTarget :
      ContMDiff J 𝓘(𝕜, E') ∞ Z := by
    have hrewrite : Z = (fun q : U ↦ Z (F q)) ∘ F.symm := by
      funext q
      simpa [Function.comp] using congrArg Z (F.apply_symm_apply q).symm
    rw [hrewrite]
    exact hcoordSource.comp F.symm.contMDiff
  have hZ :
      ContMDiff J J.tangent ∞ (T% Z) :=
    (smoothOpenSubsetVectorField_iff_smoothCoordinates (J := J) V Z).2 hcoordTarget
  have hXU :
      ContMDiff J J.tangent ∞ (T% XU) := by
    -- Identify `XU` with the pushforward of `Z` along `F.symm`, then reuse the diffeomorphism
    -- pushforward smoothness API.
    have hEq : ((F.symm _* Z) : ∀ q : U, TangentSpace J q) = XU := by
      funext q
      change (mfderiv J J F q).inverse (Z (F q)) = XU q
      let e := F.mfderivToContinuousLinearEquiv (by simp) q
      have hcoe :
          ↑(F.mfderivToContinuousLinearEquiv (by simp) q) = mfderiv J J F q :=
        F.mfderivToContinuousLinearEquiv_coe (by simp) (x := q)
      refine
        (ContinuousLinearMap.IsInvertible.inverse_apply_eq
          ⟨e, by
            simpa [e] using hcoe.symm⟩).2 ?_
      simpa [Z] using
        (VectorField.f_related_apply (f_related_pushforward_of_diffeomorph F XU) q).symm
    simpa [hEq] using contMDiff_pushforward_of_diffeomorph F.symm hZ
  have hrest :
      ContMDiff J J.tangent ∞ (fun q : U ↦ T% X q.1) := by
    have hinc :
        ContMDiff J.tangent J.tangent ∞ (tangentMap J J (Subtype.val : U → S)) := by
      exact
        (contMDiff_subtype_val : ContMDiff J J ∞ (Subtype.val : U → S)).contMDiff_tangentMap
          (m := ∞) (by simp)
    have hcomp :
        ContMDiff J J.tangent ∞
          (fun q : U ↦ tangentMap J J (Subtype.val : U → S) (T% XU q)) :=
      hinc.comp hXU
    have hEq :
        (fun q : U ↦ tangentMap J J (Subtype.val : U → S) (T% XU q)) =
          fun q : U ↦ T% X q.1 := by
      funext q
      simpa [XU, X] using tangentMap_subtype_val_pullback_eq (J := J) U X q
    simpa [hEq] using hcomp
  -- Convert the smooth restricted field on the source open subtype back to `ContMDiffOn`.
  exact
    (contMDiffOn_iff_contMDiff_restrict
      (J := J) (K := J.tangent) U (T% X)).2 hrest

/-- Helper for Proposition 8.23: the pointwise chosen intrinsic restriction field is smooth at a
fixed point once one works on the governing immersion chart source. -/
private theorem restrictionChoiceContMDiffAt
    (hS : IsImmersedSubmanifold I J S)
    (Y : SmoothVectorFieldOnM)
    (hYtangent : IsTangentToSubmanifold S J Y) (p : S) :
    ContMDiffAt J J.tangent ∞ (T% (restrictionChoice (J := J) Y hYtangent)) p := by
  let hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
    isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
      (n := (⊤ : ℕ∞ω)) (by simp) hS
  let hImmAt := hImm.isImmersionAt p
  have hOn :
      ContMDiffOn J J.tangent ∞ (T% (restrictionChoice (J := J) Y hYtangent))
        hImmAt.domChart.source :=
    restrictionChoiceContMDiffOnChartSource (I := I) (J := J) hS Y hYtangent p
  have hWithin :
      ContMDiffWithinAt J J.tangent ∞ (T% (restrictionChoice (J := J) Y hYtangent))
        hImmAt.domChart.source p := hOn p hImmAt.mem_domChart_source
  -- The source chart is open, so local smoothness on it upgrades to smoothness at `p`.
  exact hWithin.contMDiffAt (hImmAt.domChart.open_source.mem_nhds hImmAt.mem_domChart_source)

/-- Proposition 8.23: if `Y` is a smooth vector field on `M` tangent to the immersed submanifold
`S`, then there exists a unique smooth vector field on `S` that is related to `Y` by the subtype
inclusion `ι : S ↪ M`. This is the restriction `Y|_S` from the text. -/
theorem existsUnique_restriction_to_submanifold
    (hS : IsImmersedSubmanifold I J S)
    (Y : SmoothVectorFieldOnM)
    (hYtangent : IsTangentToSubmanifold S J Y) :
    ∃! X : SmoothVectorFieldOnS,
      f_related (Subtype.val : S → M) X Y := by
  let X0 : ∀ p : S, TangentSpace J p := restrictionChoice (J := J) Y hYtangent
  have hX0_related : f_related (Subtype.val : S → M) X0 Y :=
    restrictionChoice_f_related (I := I) (J := J) hS Y hYtangent
  have hX0_smooth : ContMDiff J J.tangent ∞ (T% X0) := by
    -- Smoothness is local on `S`, so it suffices to invoke the embedded-patch pointwise lemma.
    intro p
    exact restrictionChoiceContMDiffAt (I := I) (J := J) hS Y hYtangent p
  let X : SmoothVectorFieldOnS := ContMDiffSection.mk X0 hX0_smooth
  refine ⟨X, ?_, ?_⟩
  · -- Existence is immediate once the chosen pointwise field is known to be smooth.
    simpa [X, X0] using hX0_related
  · intro X' hX'
    -- Uniqueness is pointwise: the immersed inclusion has injective derivative at every point, so
    -- any related field must agree with the chosen tangent vector whose image is `Y p`.
    have hSInf : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) := by
      exact
        isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
          (n := (⊤ : ℕ∞ω)) (by simp) hS
    refine ContMDiffSection.ext ?_
    intro p
    -- Push both candidates through the subtype derivative and cancel the common ambient vector.
    apply subtypeVal_mfderiv_injective (I := I) (J := J) hSInf p
    exact
      (VectorField.f_related_apply hX' p).trans
        (VectorField.f_related_apply hX0_related p).symm

end VectorField

end
