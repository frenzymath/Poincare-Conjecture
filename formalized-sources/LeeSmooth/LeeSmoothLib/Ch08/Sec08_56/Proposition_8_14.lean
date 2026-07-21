import Mathlib
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import LeeSmoothLib.Ch02.Sec02_11.Lemma_2_26
import LeeSmoothLib.Ch03.Sec03_14.Proposition_3_8
import LeeSmoothLib.Ch03.Sec03_20.Problem_3_7
import LeeSmoothLib.Ch05.Sec05_32.Definition_5_32_extra_2
import LeeSmoothLib.Ch08.Sec08_54.Definition_8_54_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

section

universe uE uH uM

-- Domain sampling pass:
-- * primary domain: rough and smooth vector fields acting on smooth scalar-valued functions;
-- * source-facing layer: Lee's test-function smoothness criterion for a rough vector field;
-- * core/canonical owners inspected: `VectorField.apply` for the pointwise action on smooth
--   functions, `VectorField.mpullback` for restriction to open subsets, and
--   `ContMDiffMap.restrictRingHom` for restricting smooth functions to an open subset;
-- * project bridges checked for the local-to-global step:
--   `smooth_on_chart_iff_smooth_components`,
--   `exists_smooth_bump_function_for`, and
--   `exists_supported_contMDiffMap_extension_of_isClosed`.
-- Primitive data is only the rough field `X : ∀ p, TangentSpace I p`; smoothness of the
-- action on test functions is derived via `VectorField.apply`, and the open-subset condition is
-- expressed using the canonical pullback owner `VectorField.mpullback`.
-- The chapter proof route is finite-dimensional and uses ambient bump/extension machinery, so the
-- source-facing criterion is stated under `[FiniteDimensional ℝ E] [T2Space M]
-- [SigmaCompactSpace M]` rather than for an arbitrary modeled manifold.

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

open VectorField

local notation "SmoothFunction" => C^∞⟮I, M; ℝ⟯

/-- Helper for Proposition 8.14: the preferred linear identification `ℝ ≃ ℝ¹`. -/
private noncomputable def realToR1Equiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- Helper for Proposition 8.14: package a scalar as the corresponding point of `ℝ¹`. -/
private noncomputable def realToR1 : ℝ → EuclideanSpace ℝ (Fin 1) :=
  realToR1Equiv

/-- Helper for Proposition 8.14: the unique coordinate of `realToR1 t` is `t`. -/
private theorem realToR1_apply_zero (t : ℝ) :
    realToR1 t 0 = t := by
  -- Unfold the preferred linear equivalence from `ℝ` to `ℝ¹`.
  simp [realToR1, realToR1Equiv]

/-- Helper for Proposition 8.14: postcomposing a smooth scalar map on a subset with the fixed
linear embedding `ℝ → ℝ¹` preserves `Function.IsSmoothOn`. -/
private lemma realToR1_isSmoothOn_of_real_isSmoothOn
    {S : Set M} {f : S → ℝ} (hf : f.IsSmoothOn I 𝓘(ℝ)) :
    (fun x : S ↦ realToR1 (f x)).IsSmoothOn I (𝓡 1) := by
  -- Rewrite the source-facing owner into local extensions and postcompose each local extension
  -- with the fixed continuous linear equivalence `ℝ ≃ ℝ¹`.
  rw [Function.isSmoothOn_iff_exists_local_extension] at hf ⊢
  intro x
  rcases hf x with ⟨V, hV_open, hxV, Fext, hFext, hEq⟩
  refine ⟨V, hV_open, hxV, realToR1 ∘ Fext, ?_, ?_⟩
  · -- The linear identification `ℝ → ℝ¹` is smooth, so it preserves the local extension.
    simpa [realToR1, Function.comp] using
      realToR1Equiv.toContinuousLinearMap.contMDiff.comp_contMDiffOn hFext
  · -- On the subset, the packaged extension is exactly the original scalar value.
    intro y hy
    simp [hEq y hy, realToR1]

/-- Helper for Proposition 8.14: applying a smooth rough vector field to a global smooth scalar
function produces a smooth scalar function. -/
private lemma contMDiff_apply_of_contMDiffVectorField
    (X : ∀ p : M, TangentSpace I p)
    (hX : ContMDiff I I.tangent ∞ (T% X))
    (f : SmoothFunction) :
    ContMDiff I 𝓘(ℝ) ∞ (VectorField.apply X f) := by
  -- Differentiate `f` on the tangent bundle and then project to the tangent fiber of `ℝ`.
  have hTangent :
      ContMDiff I.tangent 𝓘(ℝ).tangent ∞ (tangentMap I 𝓘(ℝ) f) :=
    f.contMDiff.contMDiff_tangentMap (m := ∞) le_rfl
  have hFiber :
      ContMDiff I.tangent 𝓘(ℝ) ∞
        (fun z : TangentBundle I M ↦ (tangentMap I 𝓘(ℝ) f z).2) := by
    simpa [Function.comp] using
      (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ)).comp hTangent
  -- Pull the smooth tangent-bundle map back along the smooth section `T% X`.
  simpa [VectorField.apply_def, tangentMap_snd, Function.comp] using hFiber.comp hX

/-- Helper for Proposition 8.14: smoothness on an open subset is equivalent to smoothness on the
corresponding open subtype. -/
private lemma contMDiffOn_iff_contMDiff_restrict
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Opens M} {g : M → F} :
    ContMDiffOn I 𝓘(ℝ, F) ∞ g U ↔ ContMDiff I 𝓘(ℝ, F) ∞ (fun x : U ↦ g x) := by
  constructor
  · intro hg x
    -- Upgrade smoothness on the open set to smoothness at the chosen point of the subtype.
    have hxWithin : ContMDiffWithinAt I 𝓘(ℝ, F) ∞ g (U : Set M) x := hg x x.2
    have hxAt : ContMDiffAt I 𝓘(ℝ, F) ∞ g x := hxWithin.contMDiffAt (U.2.mem_nhds x.2)
    exact (contMDiffAt_subtype_iff (U := U) (f := g) (x := x)).2 hxAt
  · intro hg x hx
    -- Conversely, reinterpret subtype smoothness as ambient smoothness on the open subset.
    let xU : U := ⟨x, hx⟩
    have hxAt : ContMDiffAt I 𝓘(ℝ, F) ∞ g x := by
      exact (contMDiffAt_subtype_iff (U := U) (f := g) (x := xU)).1 (hg xU)
    exact hxAt.contMDiffWithinAt

/-- Helper for Proposition 8.14: if `A ⊆ U` and `f` is smooth on the open subtype `U`, then the
ambient restriction `A → ℝ` is `Function.IsSmoothOn I 𝓘(ℝ)`. -/
private lemma isSmoothOn_restrict_closure_of_contMDiffMap
    {A : Set M} {U : Opens M} (hAU : A ⊆ U)
    (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) :
    (fun x : A ↦ f ⟨x.1, hAU x.2⟩).IsSmoothOn I 𝓘(ℝ) := by
  classical
  rw [Function.isSmoothOn_iff_exists_local_extension]
  intro x
  let Fext : M → ℝ := fun y ↦ if hy : y ∈ U then f ⟨y, hy⟩ else 0
  refine ⟨(U : Set M), U.2, hAU x.2, Fext, ?_, ?_⟩
  · -- The ambient piecewise definition is smooth on `U` because its restriction is exactly `f`.
    have hRestrict : ContMDiff I 𝓘(ℝ) ∞ (fun y : U ↦ Fext y) := by
      simpa [Fext] using f.contMDiff
    exact
      (contMDiffOn_iff_contMDiff_restrict
        (I := I) (U := U) (g := Fext)).mpr hRestrict
  · -- On `A`, the ambient extension agrees with the original subtype map.
    intro y hy
    change (if hy' : y.1 ∈ U then f ⟨y.1, hy'⟩ else 0) = f ⟨y.1, hAU y.2⟩
    split_ifs with hy'
    · have hSubtype : (⟨y.1, hy'⟩ : U) = ⟨y.1, hAU y.2⟩ := by
        apply Subtype.ext
        rfl
      rw [hSubtype]
    · exact (hy' hy).elim

/-- Helper for Proposition 8.14: restricting a global smooth function to an open subset and then
applying the pulled-back vector field agrees pointwise with first applying the global field. -/
private lemma mpullback_apply_restrict_eq
    (U : Opens M)
    (X : ∀ p : M, TangentSpace I p)
    (f : SmoothFunction)
    (x : U) :
    VectorField.apply
        (VectorField.mpullback I I (Subtype.val : U → M) X)
        ⟨fun y ↦ f y.1, f.contMDiff.comp contMDiff_subtype_val⟩
        x
      =
        VectorField.apply X f x.1 := by
  let XU : ∀ y : U, TangentSpace I y :=
    VectorField.mpullback I I (Subtype.val : U → M) X
  have hsub :
      MDifferentiableAt I I (Subtype.val : U → M) x := by
    exact
      (contMDiff_subtype_val : ContMDiff I I ∞ (Subtype.val : U → M)).mdifferentiableAt
        (by simp)
  have hf :
      MDifferentiableAt I 𝓘(ℝ) f x.1 := f.contMDiff.mdifferentiableAt (by simp)
  have hsubApply :
      mfderiv I I (Subtype.val : U → M) x (XU x) = X x.1 := by
    -- The pulled-back vector field is defined using the inverse derivative of the open inclusion.
    simpa [XU, VectorField.mpullback_apply] using
      (mfderiv_open_subset_inclusion_isInvertible (I := I) U x).self_apply_inverse (X x.1)
  have hchain :
      mfderiv I 𝓘(ℝ) (fun y : U ↦ f y.1) x (XU x) =
        mfderiv I 𝓘(ℝ) f x.1 (mfderiv I I (Subtype.val : U → M) x (XU x)) := by
    -- Differentiate the restricted function by the chain rule.
    simpa [Function.comp] using
      (mfderiv_comp_apply (x := x) (g := f) (f := (Subtype.val : U → M)) hf hsub (XU x))
  -- Cancel the derivative of the inclusion against the pulled-back vector field.
  change mfderiv I 𝓘(ℝ) (fun y : U ↦ f y.1) x (XU x) = VectorField.apply X f x.1
  rw [hchain, hsubApply]
  rfl

/-- Helper for Proposition 8.14: the global smooth-test-function hypothesis localizes to a
subtype neighborhood by extending the local function from the closed support of a bump function. -/
private lemma exists_open_nhds_contMDiffOn_apply_of_forall_smooth_apply
    (X : ∀ p : M, TangentSpace I p)
    (hApply : ∀ f : SmoothFunction, ContMDiff I 𝓘(ℝ) ∞ (VectorField.apply X f))
    {U : Opens M} (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) (x : U) :
    ∃ V : Set U, IsOpen V ∧ x ∈ V ∧
      ContMDiffOn I 𝓘(ℝ) ∞ (VectorField.apply (mpullback I I (Subtype.val : U → M) X) f) V := by
  classical
  have hbasis :
      (nhds x.1).HasBasis
        (fun b : SmoothBumpFunction I x.1 ↦ tsupport b ⊆ (U : Set M))
        fun b ↦ Function.support b :=
    SmoothBumpFunction.nhds_basis_support (U.2.mem_nhds x.2)
  obtain ⟨b, hb_tsupport, _hb_support⟩ :=
    hbasis.mem_iff.mp (U.2.mem_nhds x.2)
  let A : Set M := tsupport b
  have hAclosed : IsClosed A := isClosed_tsupport b
  have hAU : A ⊆ (U : Set M) := hb_tsupport
  have hfA :
      (fun y : A ↦ f ⟨y.1, hAU y.2⟩).IsSmoothOn I 𝓘(ℝ) :=
    isSmoothOn_restrict_closure_of_contMDiffMap (I := I) hAU f
  have hfA_r1 :
      (fun y : A ↦ realToR1 (f ⟨y.1, hAU y.2⟩)).IsSmoothOn I (𝓡 1) :=
    realToR1_isSmoothOn_of_real_isSmoothOn (I := I) hfA
  rcases exists_supported_contMDiffMap_extension_of_isClosed
      (I := I) (A := A) (U := (U : Set M)) hAclosed U.2 hAU
      (fun y : A ↦ realToR1 (f ⟨y.1, hAU y.2⟩)) hfA_r1 with
    ⟨F1, hF1_eq, _hF1_support⟩
  let proj0 :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)), EuclideanSpace ℝ (Fin 1); 𝓘(ℝ), ℝ⟯ :=
    (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)), EuclideanSpace ℝ (Fin 1); 𝓘(ℝ), ℝ⟯)
  let F : SmoothFunction := proj0.comp F1
  have hF_eq :
      ∀ y : A, F y.1 = f ⟨y.1, hAU y.2⟩ := by
    intro y
    -- Project the `ℝ¹` extension back to the scalar coordinate.
    simpa [F, proj0, realToR1_apply_zero] using
      congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) (hF1_eq y)
  have hbOne : {y : M | b y = 1} ∈ nhds x.1 := b.eventuallyEq_one
  rcases mem_nhds_iff.mp hbOne with ⟨W, hWsub, hWopen, hxW⟩
  let V : Set U := Subtype.val ⁻¹' W
  have hVopen : IsOpen V := hWopen.preimage continuous_subtype_val
  have hxV : x ∈ V := hxW
  let fRestrict : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ :=
    ⟨fun y ↦ F y.1, F.contMDiff.comp contMDiff_subtype_val⟩
  have hEqOnLocal : Set.EqOn (fun y : U ↦ fRestrict y) f V := by
    intro y hyV
    have hyOne : b y.1 = 1 := hWsub hyV
    have hySupport : y.1 ∈ Function.support b := by
      exact Function.mem_support.2 (by simpa [hyOne])
    have hyA : y.1 ∈ A := subset_tsupport b hySupport
    have hySubtype : (⟨y.1, hAU hyA⟩ : U) = y := by
      apply Subtype.ext
      rfl
    simpa [fRestrict, hySubtype] using hF_eq ⟨y.1, hyA⟩
  have hEqOnApply :
      Set.EqOn
        (VectorField.apply (mpullback I I (Subtype.val : U → M) X) f)
        (fun y : U ↦ VectorField.apply X F y.1)
        V := by
    intro y hyV
    have hLocalEq :
        VectorField.apply (mpullback I I (Subtype.val : U → M) X) f y =
          VectorField.apply (mpullback I I (Subtype.val : U → M) X) fRestrict y := by
      -- Equal local smooth functions have the same manifold derivative at the base point.
      have hEqEvent : (fun z : U ↦ fRestrict z) =ᶠ[nhds y] f := by
        refine Filter.mem_of_superset (hVopen.mem_nhds hyV) ?_
        intro z hz
        exact hEqOnLocal hz
      have hMfderivEq :
          mfderiv I 𝓘(ℝ) (fun z : U ↦ fRestrict z) y =
            mfderiv I 𝓘(ℝ) f y :=
        hEqEvent.mfderiv_eq
      simpa [fRestrict, VectorField.apply_def] using
        (congrArg (fun L => L ((mpullback I I (Subtype.val : U → M) X) y)) hMfderivEq).symm
    -- Rewrite the restricted global function back to the ambient global apply.
    exact hLocalEq.trans <|
      by simpa [fRestrict] using mpullback_apply_restrict_eq (I := I) (U := U) X F y
  have hGlobal :
      ContMDiff I 𝓘(ℝ) ∞ (fun y : U ↦ VectorField.apply X F y.1) := by
    simpa [Function.comp] using (hApply F).comp contMDiff_subtype_val
  refine ⟨V, hVopen, hxV, ?_⟩
  -- On the chosen neighborhood, the local apply agrees with the restriction of a global smooth
  -- apply, so the local apply is smooth there as well.
  exact hGlobal.contMDiffOn.congr fun _ hy ↦ hEqOnApply hy

/-- Proposition 8.14 (1): on a finite-dimensional smooth manifold with the ambient bump/extension
hypotheses, a rough vector field on `M` is smooth exactly when it sends every global smooth
real-valued function on `M` to a smooth real-valued function on `M`. -/
theorem roughVectorField_smooth_iff_forall_smooth_apply_smooth
    (X : ∀ p : M, TangentSpace I p) :
    ContMDiff I I.tangent ∞ (T% X) ↔
      ∀ f : SmoothFunction, ContMDiff I 𝓘(ℝ) ∞ (VectorField.apply X f) := by
  constructor
  · intro hX f
    -- A smooth tangent section acts on every global smooth test function by a smooth scalar map.
    exact contMDiff_apply_of_contMDiffVectorField (I := I) X hX f
  · intro hApply
    -- Route correction: rather than importing the Euclidean-only Proposition 8.1 route, rebuild
    -- each chart representative from scalar chart-coordinate test functions on the chart source.
    refine contMDiff_of_locally_contMDiffOn ?_
    intro p
    let U : Opens M := ⟨(chartAt H p).source, (chartAt H p).open_source⟩
    let chartRep : U → E := fun q ↦
      (trivializationAt E (TangentSpace I) p ⟨q.1, X q.1⟩).2
    let eCoord : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    have hCoordSmooth :
        ∀ i : Fin (Module.finrank ℝ E),
          ContMDiff I 𝓘(ℝ) ∞ (fun q : U ↦ eCoord (chartRep q) i) := by
      intro i
      let ℓi : E →L[ℝ] ℝ :=
        (ContinuousLinearMap.proj i).comp eCoord.toContinuousLinearMap
      have hcoordOn :
          ContMDiffOn I 𝓘(ℝ) ∞ (fun y : M ↦ ℓi (extChartAt I p y)) (U : Set M) := by
        -- Compose the local chart with the chosen scalar coordinate functional.
        simpa [ℓi, Function.comp] using
          ℓi.contMDiff.comp_contMDiffOn
            (contMDiffOn_extChartAt (I := I) (n := ∞) (x := p))
      let coordFunction : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ :=
        ⟨fun q ↦ ℓi (extChartAt I p q.1),
          (contMDiffOn_iff_contMDiff_restrict
            (I := I) (U := U) (g := fun y : M ↦ ℓi (extChartAt I p y))).1 hcoordOn⟩
      have hApplyCoord :
          ContMDiff I 𝓘(ℝ) ∞
            (VectorField.apply (mpullback I I (Subtype.val : U → M) X) coordFunction) := by
        -- Localize the global hypothesis to the chart source and then glue the resulting local
        -- smoothness data on the subtype.
        refine contMDiff_of_locally_contMDiffOn ?_
        intro q
        exact exists_open_nhds_contMDiffOn_apply_of_forall_smooth_apply
          (I := I) X hApply coordFunction q
      have hCoordEq :
          VectorField.apply (mpullback I I (Subtype.val : U → M) X) coordFunction =
            fun q : U ↦ eCoord (chartRep q) i := by
        funext q
        let XU : ∀ y : U, TangentSpace I y :=
          mpullback I I (Subtype.val : U → M) X
        have hsub :
            MDifferentiableAt I I (Subtype.val : U → M) q := by
          exact
            (contMDiff_subtype_val : ContMDiff I I ∞ (Subtype.val : U → M)).mdifferentiableAt
              (by simp)
        have hext :
            MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) q.1 := by
          exact
            (contMDiffAt_extChartAt' (I := I) (x := p) q.2).mdifferentiableAt
              (by simp : (∞ : ℕ∞ω) ≠ 0)
        have hcoordDiff :
            MDifferentiableAt I 𝓘(ℝ) (fun y : M ↦ ℓi (extChartAt I p y)) q.1 := by
          exact
            ((ℓi.contMDiffAt.comp q.1
              (contMDiffAt_extChartAt' (I := I) (x := p) q.2))).mdifferentiableAt
              (by simp : (∞ : ℕ∞ω) ≠ 0)
        have hsubApply :
            mfderiv I I (Subtype.val : U → M) q (XU q) = X q.1 := by
          -- The pulled-back field inverts the derivative of the open inclusion.
          simpa [XU, VectorField.mpullback_apply] using
            (mfderiv_open_subset_inclusion_isInvertible (I := I) U q).self_apply_inverse (X q.1)
        have hchainSub :
            mfderiv I 𝓘(ℝ) (fun y : U ↦ ℓi (extChartAt I p y.1)) q (XU q) =
              mfderiv I 𝓘(ℝ) (fun y : M ↦ ℓi (extChartAt I p y)) q.1
                (mfderiv I I (Subtype.val : U → M) q (XU q)) := by
          -- Differentiate the chart coordinate through the open-subtype inclusion.
          simpa [Function.comp] using
            (mfderiv_comp_apply
              (x := q)
              (g := fun y : M ↦ ℓi (extChartAt I p y))
              (f := (Subtype.val : U → M))
              hcoordDiff hsub (XU q))
        have hchainChart :
            mfderiv I 𝓘(ℝ) (fun y : M ↦ ℓi (extChartAt I p y)) q.1 (X q.1) =
              ℓi (mfderiv I 𝓘(ℝ, E) (extChartAt I p) q.1 (X q.1)) := by
          -- Then differentiate the scalar coordinate through the extended chart itself.
          simpa [Function.comp] using
            (mfderiv_comp_apply
              (x := q.1)
              (g := ℓi)
              (f := extChartAt I p)
              (ℓi.contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
              hext
              (X q.1))
        have hchartRep :
            chartRep q = mfderiv I 𝓘(ℝ, E) (extChartAt I p) q.1 (X q.1) := by
          have hqBase :
              q.1 ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
            simpa [TangentBundle.trivializationAt_baseSet] using q.2
          -- The tangent-bundle trivialization reads the tangent vector in chart coordinates.
          change (trivializationAt E (TangentSpace I) p ⟨q.1, X q.1⟩).2 =
            mfderiv I 𝓘(ℝ, E) (extChartAt I p) q.1 (X q.1)
          rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
            (R := ℝ)
            (e := trivializationAt E (TangentSpace I) p)
            hqBase
            (X q.1)]
          rw [TangentBundle.continuousLinearMapAt_trivializationAt
            (I := I) (H := H) (x₀ := p) (x := q.1) q.2]
          rfl
        change mfderiv I 𝓘(ℝ) (fun y : U ↦ ℓi (extChartAt I p y.1)) q (XU q) =
          eCoord (chartRep q) i
        rw [hchainSub, hsubApply, hchainChart, hchartRep]
        rfl
      simpa [hCoordEq] using hApplyCoord
    have hChartRepSmooth :
        ContMDiff I 𝓘(ℝ, E) ∞ chartRep := by
      have hPi :
          ContMDiff I 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) ∞
            (fun q : U ↦ eCoord (chartRep q)) := by
        -- Smoothness of the tuple-valued coordinate map is equivalent to smoothness of each
        -- scalar component.
        exact (contMDiff_pi_space
          (I := I)
          (n := (∞ : ℕ∞ω))
          (φ := fun q : U ↦ eCoord (chartRep q))).2 hCoordSmooth
      -- Reassemble the chart representative from its finite family of scalar coordinates.
      have hCompose :
          ContMDiff I 𝓘(ℝ, E) ∞ (fun q : U ↦ eCoord.symm (eCoord (chartRep q))) := by
        convert eCoord.symm.toContinuousLinearMap.contMDiff.comp hPi using 1
      exact hCompose.congr fun q ↦ (eCoord.symm_apply_apply (chartRep q)).symm
    have hChartRepOn :
        ContMDiffOn I 𝓘(ℝ, E) ∞
          (fun y : M ↦ (trivializationAt E (TangentSpace I) p ⟨y, X y⟩).2)
          (U : Set M) :=
      (contMDiffOn_iff_contMDiff_restrict
        (I := I)
        (F := E)
        (U := U)
        (g := fun y : M ↦ (trivializationAt E (TangentSpace I) p ⟨y, X y⟩).2)).2
        hChartRepSmooth
    have hSectionOn :
        ContMDiffOn I I.tangent ∞ (T% X) ((chartAt H p).source) := by
      -- Convert the smooth chart representative back to smoothness of the tangent-bundle section.
      simpa [U, TangentBundle.trivializationAt_baseSet] using
        ((Bundle.Trivialization.contMDiffOn_section_baseSet_iff
          (e := trivializationAt E (TangentSpace I) p)).2 hChartRepOn)
    exact ⟨(chartAt H p).source, (chartAt H p).open_source, mem_chart_source H p, hSectionOn⟩

/-- Helper for Proposition 8.14: global smoothness of `Xf` for every ambient smooth function
implies the corresponding local smoothness statement on every open subset. -/
private lemma forall_open_smooth_apply_of_forall_smooth_apply
    (X : ∀ p : M, TangentSpace I p)
    (hApply : ∀ f : SmoothFunction, ContMDiff I 𝓘(ℝ) ∞ (VectorField.apply X f))
    (U : Opens M) (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (VectorField.apply (mpullback I I (Subtype.val : U → M) X) f) := by
  -- Localize the global hypothesis pointwise, then use locality of `ContMDiff` on the subtype.
  refine contMDiff_of_locally_contMDiffOn ?_
  intro x
  exact exists_open_nhds_contMDiffOn_apply_of_forall_smooth_apply
    (I := I) X hApply f x

/-- Proposition 8.14 (2): the global test-function condition for a rough vector field is
equivalent to the corresponding local condition on every open subset, where the ambient vector
field is pulled back along the open-subset inclusion. The nontrivial global-to-local direction uses
the same finite-dimensional ambient bump/extension hypotheses as part (1). -/
theorem roughVectorField_forall_smooth_apply_smooth_iff_forall_open_forall_smooth_apply_smooth
    (X : ∀ p : M, TangentSpace I p) :
    (∀ f : SmoothFunction, ContMDiff I 𝓘(ℝ) ∞ (VectorField.apply X f)) ↔
      ∀ U : Opens M, ∀ f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯,
        ContMDiff I 𝓘(ℝ) ∞ (VectorField.apply (mpullback I I (Subtype.val : U → M) X) f) := by
  constructor
  · intro hApply U f
    -- Localize the global test-function hypothesis by shrinking, extending from `closure V`, and
    -- then comparing the resulting ambient action with the original local action near each point.
    exact forall_open_smooth_apply_of_forall_smooth_apply (I := I) X hApply U f
  · intro hOpen f
    let fTop : C^∞⟮I, (⊤ : Opens M); 𝓘(ℝ), ℝ⟯ :=
      ⟨fun x ↦ f x.1, f.contMDiff.comp contMDiff_subtype_val⟩
    have hTop :
        ContMDiff I 𝓘(ℝ) ∞
          (VectorField.apply
            (mpullback I I (Subtype.val : (⊤ : Opens M) → M) X)
            fTop) :=
      hOpen ⊤ fTop
    have hTopEq :
        VectorField.apply
            (mpullback I I (Subtype.val : (⊤ : Opens M) → M) X)
            fTop
          =
            fun x : (⊤ : Opens M) ↦ VectorField.apply X f x.1 := by
      funext x
      -- The pulled-back field on `⊤` is just the original field viewed on the open subtype.
      simpa [fTop] using mpullback_apply_restrict_eq (I := I) (U := (⊤ : Opens M)) X f x
    have hTop' :
        ContMDiff I 𝓘(ℝ) ∞
          (fun y : (⊤ : Opens M) ↦ VectorField.apply X f y.1) := by
      simpa [hTopEq] using hTop
    have hOnTop :
        ContMDiffOn I 𝓘(ℝ) ∞ (VectorField.apply X f) (⊤ : Opens M) :=
      (contMDiffOn_iff_contMDiff_restrict
        (I := I) (U := (⊤ : Opens M)) (g := VectorField.apply X f)).mpr hTop'
    -- The open subset `⊤` is the whole manifold, so smoothness on it is global smoothness.
    simpa using (contMDiffOn_univ).1 hOnTop

end
