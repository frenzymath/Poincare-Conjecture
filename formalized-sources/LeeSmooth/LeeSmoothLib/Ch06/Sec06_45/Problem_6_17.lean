import Mathlib
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
import LeeSmoothLib.Ch05.Sec05_35.Notation_5_35_extra_1
import LeeSmoothLib.Ch06.Sec06_44.Definition_6_44_extra_1
import LeeSmoothLib.Ch06.Sec06_45.StableMapClass
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold Set

section Problem617

-- Domain sampling pass: this counterexample lies in the stable-map-class / smooth-family domain.
-- Relevant owner declarations checked before refinement:
-- * `IsStableMapClass` from `StableMapClass`
-- * `IsSmoothFamily` from `Definition_6_44_extra_2`
-- * the map-class owners `IsImmersion`, `IsSmoothSubmersion`, `IsSmoothEmbedding`,
--   `IsLocalDiffeomorph`, `IsTransverseToSubmanifold`, and `≃ₘ⟮I, I⟯`
-- Layer triage:
-- * source-facing: the explicit Lee family `problem_6_17_family`
-- * core/canonical: the family-smoothness owner `IsSmoothFamily I I I`
-- * derived API: pointwise evaluation and the specialized stability counterexamples

local notation "I" => 𝓘(ℝ, ℝ)

/-- The Problem 6-17 family is `F_s(x) = x φ (s x)`. -/
def problem_6_17_family (φ : ℝ → ℝ) (s : ℝ) : ℝ → ℝ :=
  fun x ↦ x * φ (s * x)

/-- The defining formula for the Problem 6-17 family. -/
@[simp] lemma problem_6_17_family_apply (φ : ℝ → ℝ) (s x : ℝ) :
    problem_6_17_family φ s x = x * φ (s * x) :=
  rfl

/-- The Problem 6-17 family is a smooth family of maps `ℝ → ℝ` whenever `φ` is smooth. -/
lemma problem_6_17_family_isSmoothFamily {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) :
    IsSmoothFamily I I I (problem_6_17_family φ) := by
  -- Rewrite the family as the uncurried map `(s, x) ↦ x * φ (s * x)`.
  rw [IsSmoothFamily]
  -- Smoothness follows from the product projections, multiplication, and composition with `φ`.
  simpa [Function.uncurry, problem_6_17_family] using
    contMDiff_snd.mul (hφsmooth.contMDiff.comp (contMDiff_fst.mul contMDiff_snd))

/-- If `φ(0) = 1`, then the `s = 0` slice of the Problem 6-17 family is the identity map of `ℝ`.
-/
lemma problem_6_17_family_zero (φ : ℝ → ℝ) (hφ0 : φ 0 = 1) :
    problem_6_17_family φ 0 = id := by
  funext x
  simp [problem_6_17_family, hφ0]

/-- Compact support of `φ` forces each nonzero slice `F_s` to vanish outside a sufficiently large
compact interval. -/
lemma problem_6_17_family_eq_zero_outside_large_interval {φ : ℝ → ℝ} {s : ℝ}
    (hs : s ≠ 0) (hφsupport : HasCompactSupport φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R ≤ |x| → problem_6_17_family φ s x = 0 := by
  -- First transfer compact support from `φ` to the nonzero slice `x ↦ x * φ (s * x)`.
  have hsliceSupport : HasCompactSupport (problem_6_17_family φ s) := by
    simpa [problem_6_17_family, smul_eq_mul, Pi.mul_apply] using
      (hφsupport.comp_smul hs).mul_left (f := fun x : ℝ ↦ x)
  rcases (exists_compact_iff_hasCompactSupport).2 hsliceSupport with ⟨K, hKcompact, hKzero⟩
  rcases hKcompact.isBounded.subset_closedBall (0 : ℝ) with ⟨R, hKR⟩
  let R' : ℝ := max R 0 + 1
  refine ⟨R', by positivity, ?_⟩
  intro x hx
  -- Choosing a radius strictly larger than the compact support radius forces `x ∉ K`.
  have hRlt : R < R' := by
    dsimp [R']
    linarith [le_max_left R 0]
  have hRabs : R < |x| := lt_of_lt_of_le hRlt hx
  have hx_not_mem : x ∉ K := by
    intro hxK
    have hxBall : x ∈ Metric.closedBall (0 : ℝ) R := hKR hxK
    have hxAbsLe : |x| ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hxBall
    exact (not_le.mpr hRabs) hxAbsLe
  -- Outside the compact support, the slice vanishes.
  exact hKzero x hx_not_mem

/-- Helper for Problem 6-17: an open neighborhood of `0` in `ℝ` contains a positive point. -/
lemma exists_pos_mem_of_isOpen_of_zero_mem {U : Set ℝ} (hUOpen : IsOpen U) (h0U : (0 : ℝ) ∈ U) :
    ∃ s : ℝ, 0 < s ∧ s ∈ U := by
  -- Openness at `0` provides a ball contained in `U`.
  rcases Metric.isOpen_iff.mp hUOpen 0 h0U with ⟨ε, hεpos, hεU⟩
  refine ⟨ε / 2, by linarith, ?_⟩
  -- The midpoint `ε / 2` lies in that ball, hence in `U`.
  refine hεU ?_
  have hhalf_nonneg : 0 ≤ ε / 2 := by positivity
  have hhalf_lt : ε / 2 < ε := by linarith
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hhalf_nonneg]
  exact hhalf_lt

/-- Helper for Problem 6-17: a stable class stays inside the class on a neighborhood of any
parameter where a smooth family enters it. -/
lemma stableMapClass_exists_open_nhds {C : Set (ℝ → ℝ)}
    (hStable : IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I C)
    {S : Type} {ES : Type} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
    [FiniteDimensional ℝ ES] {HS : Type} [TopologicalSpace HS] [TopologicalSpace S]
    [ChartedSpace HS S] {IS : ModelWithCorners ℝ ES HS} [IsManifold IS ∞ S]
    {F : S → ℝ → ℝ} (hF : IsSmoothFamily I IS I F) {s0 : S} (hs0 : F s0 ∈ C) :
    ∃ U : Set S, IsOpen U ∧ s0 ∈ U ∧ ∀ s ∈ U, F s ∈ C := by
  -- Route correction: pin the parameter-manifold universes to `Type 0`, so the stability proof
  -- can be specialized to the concrete family without hidden universe metavariables.
  exact hStable (F := F) hF (s0 := s0) hs0

/-- Helper for Problem 6-17: a stable class of maps `ℝ → ℝ` contains all slices in a neighborhood
of any parameter where a smooth real family enters the class. -/
lemma stableMapClass_realFamily_exists_open_nhds {C : Set (ℝ → ℝ)}
    (hStable : IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I C) {F : ℝ → ℝ → ℝ}
    (hF : IsSmoothFamily I I I F) {s0 : ℝ} (hs0 : F s0 ∈ C) :
    ∃ U : Set ℝ, IsOpen U ∧ s0 ∈ U ∧ ∀ s ∈ U, F s ∈ C := by
  -- Specialize the generic neighborhood-stability helper to the real parameter manifold.
  simpa using stableMapClass_exists_open_nhds hStable hF hs0

/-- Helper for Problem 6-17: a smooth family that lies in `C` at `s = 0` and leaves `C` at every
nonzero parameter witnesses that `C` is not stable. -/
lemma notStableMapClass_ofSmoothFamilyCounterexample {C : Set (ℝ → ℝ)} {F : ℝ → ℝ → ℝ}
    (hF : IsSmoothFamily I I I F) (hZero : F 0 ∈ C)
    (hNonzero : ∀ ⦃s : ℝ⦄, s ≠ 0 → F s ∉ C) :
    ¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I C := by
  intro hStable
  rcases stableMapClass_realFamily_exists_open_nhds hStable hF hZero with ⟨U, hUOpen, h0U, hUC⟩
  rcases exists_pos_mem_of_isOpen_of_zero_mem hUOpen h0U with ⟨s, hspos, hsU⟩
  -- A positive parameter is nonzero, so the nonzero-slice obstruction contradicts local stability.
  have hsne : s ≠ 0 := by linarith
  exact hNonzero hsne (hUC s hsU)

/-- Helper for Problem 6-17: the identity map of `ℝ` is a smooth submersion. -/
lemma realIdentity_isSmoothSubmersion : IsSmoothSubmersion I I (id : ℝ → ℝ) := by
  -- The derivative of the identity map is the identity linear map at every point.
  refine ⟨contMDiff_id, ?_⟩
  intro x v
  refine ⟨v, ?_⟩
  rw [mfderiv_id]
  rfl

/-- Helper for Problem 6-17: every nonzero slice agrees with the constant-zero map near a tail
point, so its manifold derivative vanishes there. -/
lemma problem_6_17_nonzeroSlice_mfderiv_eq_zeroAtTailPoint {φ : ℝ → ℝ} {s : ℝ}
    (hs : s ≠ 0) (hφsupport : HasCompactSupport φ) :
    ∃ x0 : ℝ,
      0 < x0 ∧ problem_6_17_family φ s x0 = 0 ∧
        mfderiv I I (problem_6_17_family φ s) x0 = 0 := by
  rcases problem_6_17_family_eq_zero_outside_large_interval hs hφsupport with
    ⟨R, hRpos, hRzero⟩
  refine ⟨R + 1, by linarith, ?_, ?_⟩
  · -- The chosen tail point already lies outside the support radius.
    have hRabs : R ≤ |R + 1| := by
      rw [abs_of_nonneg]
      · linarith
      · linarith
    exact hRzero (R + 1) hRabs
  · -- Route correction: rewrite the slice to the constant-zero map on a tail neighborhood.
    have hEq :
        problem_6_17_family φ s =ᶠ[nhds (R + 1)] fun _ : ℝ ↦ (0 : ℝ) := by
      have hRp1 : R < R + 1 := by
        linarith
      have hIoi : Set.Ioi R ∈ nhds (R + 1 : ℝ) := isOpen_Ioi.mem_nhds hRp1
      filter_upwards [hIoi] with y hy
      have hy_nonneg : 0 ≤ y := le_trans hRpos.le hy.le
      have hRabs : R ≤ |y| := by
        rw [abs_of_nonneg hy_nonneg]
        exact le_of_lt hy
      exact hRzero y hRabs
    calc
      mfderiv I I (problem_6_17_family φ s) (R + 1)
          = mfderiv I I (fun _ : ℝ ↦ (0 : ℝ)) (R + 1) := hEq.mfderiv_eq
      _ = 0 := mfderiv_const

/-- Helper for Problem 6-17: every nonzero slice has two distinct tail points with the same image,
so it is not injective. -/
lemma problem_6_17_nonzeroSlice_notInjective {φ : ℝ → ℝ} {s : ℝ}
    (hs : s ≠ 0) (hφsupport : HasCompactSupport φ) :
    ¬ Function.Injective (problem_6_17_family φ s) := by
  rcases problem_6_17_family_eq_zero_outside_large_interval hs hφsupport with
    ⟨R, hRpos, hRzero⟩
  intro hinj
  have hzero1 : problem_6_17_family φ s (R + 1) = 0 := by
    apply hRzero
    rw [abs_of_nonneg]
    · linarith
    · linarith
  have hzero2 : problem_6_17_family φ s (R + 2) = 0 := by
    apply hRzero
    rw [abs_of_nonneg]
    · linarith
    · linarith
  have hEq : R + 1 = R + 2 := hinj (hzero1.trans hzero2.symm)
  linarith

/-- Helper for Problem 6-17: the zero derivative at a tail point rules out immersions for nonzero
slices. -/
lemma problem_6_17_nonzeroSlice_not_isImmersion {φ : ℝ → ℝ} {s : ℝ}
    (hs : s ≠ 0) (hφsupport : HasCompactSupport φ) :
    ¬ IsImmersion I I ∞ (problem_6_17_family φ s) := by
  intro hImm
  rcases problem_6_17_nonzeroSlice_mfderiv_eq_zeroAtTailPoint hs hφsupport with
    ⟨x0, -, -, hderiv0⟩
  have hinj :
      Function.Injective (mfderiv I I (problem_6_17_family φ s) x0) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv hImm.contMDiff).1 hImm x0
  -- The zero linear map cannot be injective on the one-dimensional tangent space.
  have hEq :
      mfderiv I I (problem_6_17_family φ s) x0 (0 : TangentSpace I x0) =
        mfderiv I I (problem_6_17_family φ s) x0 (1 : TangentSpace I x0) := by
    rw [hderiv0]
    rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply]
  have h01 : (0 : TangentSpace I x0) = 1 := hinj hEq
  -- Transport the tangent-space equality back to the concrete `ℝ` model and contradict `0 ≠ 1`.
  change (0 : ℝ) = 1 at h01
  exact zero_ne_one h01

/-- Helper for Problem 6-17: the zero derivative at a tail point rules out smooth submersions for
nonzero slices. -/
lemma problem_6_17_nonzeroSlice_not_isSmoothSubmersion {φ : ℝ → ℝ} {s : ℝ}
    (hs : s ≠ 0) (hφsupport : HasCompactSupport φ) :
    ¬ IsSmoothSubmersion I I (problem_6_17_family φ s) := by
  intro hSubm
  rcases problem_6_17_nonzeroSlice_mfderiv_eq_zeroAtTailPoint hs hφsupport with
    ⟨x0, -, -, hderiv0⟩
  have hsurj :
      Function.Surjective (mfderiv I I (problem_6_17_family φ s) x0) :=
    hSubm.surjective_mfderiv x0
  rcases hsurj (1 : TangentSpace I (problem_6_17_family φ s x0)) with ⟨v, hv⟩
  -- The zero linear map cannot hit the nonzero target vector `1`.
  rw [hderiv0] at hv
  rw [ContinuousLinearMap.zero_apply] at hv
  change (0 : ℝ) = 1 at hv
  exact zero_ne_one hv

/-- Helper for Problem 6-17: the tangent space of the singleton submanifold `{0}` is trivial. -/
lemma zeroSingletonTangentSpace_eq_bot
    {E0 : Type*} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type*} [TopologicalSpace H0] {J0 : ModelWithCorners ℝ E0 H0}
    [ChartedSpace H0 ({(0 : ℝ)} : Set ℝ)] [IsManifold J0 ∞ ({(0 : ℝ)} : Set ℝ)]
    [IsEmbeddedSubmanifold I J0 ({(0 : ℝ)} : Set ℝ)]
    (p : ({(0 : ℝ)} : Set ℝ)) :
    (T[J0; p] : Submodule ℝ (TangentSpace I (p : ℝ))) = ⊥ := by
  -- The inclusion `({0} : Set ℝ) → ℝ` is the constant-zero map.
  have hconst : (Subtype.val : ({(0 : ℝ)} : Set ℝ) → ℝ) = fun _ ↦ (0 : ℝ) := by
    funext q
    exact Set.mem_singleton_iff.mp q.2
  rw [Manifold.submanifoldTangentSpace, hconst, mfderiv_const]
  simp

/-- Helper for Problem 6-17: the zero derivative at a tail point and the trivial tangent space of
`{0}` rule out transversality to `{0}` for nonzero slices. -/
lemma problem_6_17_nonzeroSlice_not_transverseToZero
    {E0 : Type*} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type*} [TopologicalSpace H0] {J0 : ModelWithCorners ℝ E0 H0}
    [ChartedSpace H0 ({(0 : ℝ)} : Set ℝ)] [IsManifold J0 ∞ ({(0 : ℝ)} : Set ℝ)]
    [IsEmbeddedSubmanifold I J0 ({(0 : ℝ)} : Set ℝ)]
    {φ : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hφsupport : HasCompactSupport φ) :
    ¬ IsTransverseToSubmanifold I I J0 ({(0 : ℝ)} : Set ℝ) (problem_6_17_family φ s) := by
  intro hTrans
  rcases problem_6_17_nonzeroSlice_mfderiv_eq_zeroAtTailPoint hs hφsupport with
    ⟨x0, -, hx0zero, hderiv0⟩
  let p : problem_6_17_family φ s ⁻¹' ({(0 : ℝ)} : Set ℝ) :=
    ⟨x0, by simpa [problem_6_17_family] using hx0zero⟩
  let x : ({(0 : ℝ)} : Set ℝ) :=
    ⟨problem_6_17_family φ s x0, by simpa [problem_6_17_family] using hx0zero⟩
  have hTX :
      (T[J0; x] : Submodule ℝ (TangentSpace I (problem_6_17_family φ s x0))) = ⊥ := by
    -- The singleton target contributes no tangent directions.
    simpa [x] using zeroSingletonTangentSpace_eq_bot (J0 := J0) x
  have hSup :
      (mfderiv I I (problem_6_17_family φ s) x0).range ⊔
        (T[J0; x] : Submodule ℝ (TangentSpace I (problem_6_17_family φ s x0))) = ⊤ := by
    -- The transversality field specializes to the chosen zero-fiber preimage point.
    simpa [p, x] using hTrans.tangent_sup_eq_top p
  have hRange :
      (mfderiv I I (problem_6_17_family φ s) x0).range =
        (⊥ : Submodule ℝ (TangentSpace I (problem_6_17_family φ s x0))) := by
    -- The derivative image is trivial because the manifold derivative itself is zero.
    rw [hderiv0]
    simpa using
      (LinearMap.range_zero :
        LinearMap.range
            (0 :
              TangentSpace I x0 →ₗ[ℝ] TangentSpace I (problem_6_17_family φ s x0)) =
          ⊥)
  have hTop :
      (⊥ : Submodule ℝ (TangentSpace I (problem_6_17_family φ s x0))) = ⊤ := by
    -- Rewriting the derivative image and target tangent space to `⊥` leaves `⊥ = ⊤`.
    calc
      (⊥ : Submodule ℝ (TangentSpace I (problem_6_17_family φ s x0))) =
          (mfderiv I I (problem_6_17_family φ s) x0).range ⊔
            (T[J0; x] : Submodule ℝ (TangentSpace I (problem_6_17_family φ s x0))) := by
        rw [hRange, hTX]
        rw [bot_sup_eq]
      _ = ⊤ := hSup
  have hOneTop :
      (1 : TangentSpace I (problem_6_17_family φ s x0)) ∈
        (⊤ : Submodule ℝ (TangentSpace I (problem_6_17_family φ s x0))) := by
    -- The nonzero tangent vector `1` is automatically a member of the top submodule.
    exact Submodule.mem_top
  have hOne :
      (1 : TangentSpace I (problem_6_17_family φ s x0)) ∈
        (⊥ : Submodule ℝ (TangentSpace I (problem_6_17_family φ s x0))) := by
    -- Membership in `⊤` transports across `hTop` to impossible membership in `⊥`.
    rw [← hTop] at hOneTop
    exact hOneTop
  change (1 : ℝ) = 0 at hOne
  exact zero_ne_one hOne.symm

/-- First counterexample for Problem 6-17: using the family `F_s(x) = x φ (s x)`, the class of
immersions `ℝ → ℝ`
need not be stable when the source manifold is noncompact. -/
theorem immersions_need_not_be_stable_without_compact_source
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsImmersion I I ∞ f} := by
  -- The Lee family is smooth, starts at `id`, and every nonzero slice fails immersion.
  refine notStableMapClass_ofSmoothFamilyCounterexample
    (F := problem_6_17_family φ) (C := {f : ℝ → ℝ | IsImmersion I I ∞ f})
    (problem_6_17_family_isSmoothFamily hφsmooth) ?_ ?_
  · rw [problem_6_17_family_zero φ hφ0]
    exact IsLocalDiffeomorph.isImmersion (Diffeomorph.refl I ℝ ∞).isLocalDiffeomorph
  · intro s hs
    exact problem_6_17_nonzeroSlice_not_isImmersion hs hφsupport

/-- Second counterexample for Problem 6-17: using the same family, the class of smooth
submersions `ℝ → ℝ` need not be stable when the source manifold is noncompact. -/
theorem submersions_need_not_be_stable_without_compact_source
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsSmoothSubmersion I I f} := by
  -- The zero slice is the identity submersion, but every nonzero slice has zero derivative at
  -- a tail point.
  refine notStableMapClass_ofSmoothFamilyCounterexample
    (F := problem_6_17_family φ) (C := {f : ℝ → ℝ | IsSmoothSubmersion I I f})
    (problem_6_17_family_isSmoothFamily hφsmooth) ?_ ?_
  · rw [problem_6_17_family_zero φ hφ0]
    exact realIdentity_isSmoothSubmersion
  · intro s hs
    exact problem_6_17_nonzeroSlice_not_isSmoothSubmersion hs hφsupport

/-- Third counterexample for Problem 6-17: using the same family, the class of smooth embeddings
`ℝ → ℝ` need not be stable when the source manifold is noncompact. -/
theorem embeddings_need_not_be_stable_without_compact_source
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsSmoothEmbedding I I ∞ f} := by
  -- The identity map is a smooth embedding, whereas every nonzero slice is noninjective.
  refine notStableMapClass_ofSmoothFamilyCounterexample
    (F := problem_6_17_family φ) (C := {f : ℝ → ℝ | IsSmoothEmbedding I I ∞ f})
    (problem_6_17_family_isSmoothFamily hφsmooth) ?_ ?_
  · rw [problem_6_17_family_zero φ hφ0]
    exact
      Manifold.IsSmoothEmbedding.mk
        (IsLocalDiffeomorph.isImmersion (Diffeomorph.refl I ℝ ∞).isLocalDiffeomorph)
        ((Homeomorph.refl ℝ).isEmbedding)
  · intro s hs hEmb
    exact problem_6_17_nonzeroSlice_notInjective hs hφsupport hEmb.isEmbedding.injective

/-- Fourth counterexample for Problem 6-17: using the same family, the class of smooth
diffeomorphisms `ℝ → ℝ` need not be stable when the source manifold is noncompact. -/
theorem diffeomorphisms_need_not_be_stable_without_compact_source
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      (range ((↑) : (ℝ ≃ₘ⟮I, I⟯ ℝ) → (ℝ → ℝ))) := by
  -- The zero slice is the identity diffeomorphism, while every nonzero slice is noninjective.
  refine notStableMapClass_ofSmoothFamilyCounterexample
    (F := problem_6_17_family φ)
    (C := range ((↑) : (ℝ ≃ₘ⟮I, I⟯ ℝ) → (ℝ → ℝ)))
    (problem_6_17_family_isSmoothFamily hφsmooth) ?_ ?_
  · refine ⟨Diffeomorph.refl I ℝ ∞, ?_⟩
    rw [problem_6_17_family_zero φ hφ0]
    rfl
  · intro s hs
    rintro ⟨Φ, hΦ⟩
    have hinj : Function.Injective (problem_6_17_family φ s) := by
      simpa [← hΦ] using Φ.injective
    exact problem_6_17_nonzeroSlice_notInjective hs hφsupport hinj

/-- Fifth counterexample for Problem 6-17: using the same family, the class of local
diffeomorphisms `ℝ → ℝ` need not be stable when the source manifold is noncompact. -/
theorem local_diffeomorphisms_need_not_be_stable_without_compact_source
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsLocalDiffeomorph I I ∞ f} := by
  -- Local diffeomorphisms are immersions, so the same zero-derivative obstruction applies.
  refine notStableMapClass_ofSmoothFamilyCounterexample
    (F := problem_6_17_family φ) (C := {f : ℝ → ℝ | IsLocalDiffeomorph I I ∞ f})
    (problem_6_17_family_isSmoothFamily hφsmooth) ?_ ?_
  · rw [problem_6_17_family_zero φ hφ0]
    exact (Diffeomorph.refl I ℝ ∞).isLocalDiffeomorph
  · intro s hs hLocal
    exact problem_6_17_nonzeroSlice_not_isImmersion hs hφsupport
      (IsLocalDiffeomorph.isImmersion hLocal)

/-- Sixth counterexample for Problem 6-17: using the same family, the class of maps `ℝ → ℝ`
transverse to the chosen embedded submanifold structure on `{0}` need not be stable when the
source manifold is noncompact. -/
theorem transverse_maps_to_zero_need_not_be_stable_without_compact_source
    {E0 : Type*} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    {H0 : Type*} [TopologicalSpace H0] {J0 : ModelWithCorners ℝ E0 H0}
    [ChartedSpace H0 ({(0 : ℝ)} : Set ℝ)] [IsManifold J0 ∞ ({(0 : ℝ)} : Set ℝ)]
    [IsEmbeddedSubmanifold I J0 ({(0 : ℝ)} : Set ℝ)]
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    ¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ |
        IsTransverseToSubmanifold I I J0 ({(0 : ℝ)} : Set ℝ) f} := by
  -- The identity map is transverse to `{0}` because it is a smooth submersion, but every nonzero
  -- slice has both derivative image and singleton tangent space equal to `⊥` at a tail point.
  refine notStableMapClass_ofSmoothFamilyCounterexample
    (F := problem_6_17_family φ)
    (C := {f : ℝ → ℝ | IsTransverseToSubmanifold I I J0 ({(0 : ℝ)} : Set ℝ) f})
    (problem_6_17_family_isSmoothFamily hφsmooth) ?_ ?_
  · have hTransId :
        IsTransverseToSubmanifold I I J0 ({(0 : ℝ)} : Set ℝ) (id : ℝ → ℝ) :=
      Manifold.IsSmoothSubmersion.isTransverseToSubmanifold
        (JX := J0) (X := ({(0 : ℝ)} : Set ℝ)) realIdentity_isSmoothSubmersion
    rw [problem_6_17_family_zero φ hφ0]
    exact hTransId
  · intro s hs
    exact problem_6_17_nonzeroSlice_not_transverseToZero (J0 := J0) hs hφsupport

/-- Problem 6-17: if `φ : ℝ → ℝ` is smooth, compactly supported, and satisfies `φ 0 = 1`, then
the family `F_s(x) = x φ (s x)` shows that the map classes from Problem 6-16 need not be stable
when the source manifold is noncompact. -/
theorem notStableMapClass_ofZeroCounterexample
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    (¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsImmersion I I ∞ f}) ∧
    (¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsSmoothSubmersion I I f}) ∧
    (¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsSmoothEmbedding I I ∞ f}) ∧
    (¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      (range ((↑) : (ℝ ≃ₘ⟮I, I⟯ ℝ) → (ℝ → ℝ)))) ∧
    (¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsLocalDiffeomorph I I ∞ f}) ∧
    ∀ {E0 : Type*} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
      {H0 : Type*} [TopologicalSpace H0] {J0 : ModelWithCorners ℝ E0 H0}
      [ChartedSpace H0 ({(0 : ℝ)} : Set ℝ)] [IsManifold J0 ∞ ({(0 : ℝ)} : Set ℝ)]
      [IsEmbeddedSubmanifold I J0 ({(0 : ℝ)} : Set ℝ)],
      ¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
        {f : ℝ → ℝ | IsTransverseToSubmanifold I I J0 ({(0 : ℝ)} : Set ℝ) f} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact immersions_need_not_be_stable_without_compact_source hφsmooth hφsupport hφ0
  · exact submersions_need_not_be_stable_without_compact_source hφsmooth hφsupport hφ0
  · exact embeddings_need_not_be_stable_without_compact_source hφsmooth hφsupport hφ0
  · exact diffeomorphisms_need_not_be_stable_without_compact_source hφsmooth hφsupport hφ0
  · exact local_diffeomorphisms_need_not_be_stable_without_compact_source
      hφsmooth hφsupport hφ0
  · intro E0 _ _ H0 _ J0 _ _ _
    exact transverse_maps_to_zero_need_not_be_stable_without_compact_source
      (J0 := J0) hφsmooth hφsupport hφ0

/-- Summary for Problem 6-17: this packages the six counterexamples under the descriptive theorem
name used in the chapter API. -/
theorem standard_map_classes_need_not_be_stable_without_compact_source
    {φ : ℝ → ℝ} (hφsmooth : ContDiff ℝ ∞ φ) (hφsupport : HasCompactSupport φ)
    (hφ0 : φ 0 = 1) :
    (¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsImmersion I I ∞ f}) ∧
    (¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsSmoothSubmersion I I f}) ∧
    (¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsSmoothEmbedding I I ∞ f}) ∧
    (¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      (range ((↑) : (ℝ ≃ₘ⟮I, I⟯ ℝ) → (ℝ → ℝ)))) ∧
    (¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
      {f : ℝ → ℝ | IsLocalDiffeomorph I I ∞ f}) ∧
    ∀ {E0 : Type*} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
      {H0 : Type*} [TopologicalSpace H0] {J0 : ModelWithCorners ℝ E0 H0}
      [ChartedSpace H0 ({(0 : ℝ)} : Set ℝ)] [IsManifold J0 ∞ ({(0 : ℝ)} : Set ℝ)]
      [IsEmbeddedSubmanifold I J0 ({(0 : ℝ)} : Set ℝ)],
      ¬ IsStableMapClass.{0, 0, 0, 0, 0, 0, 0, 0, 0} I I
        {f : ℝ → ℝ | IsTransverseToSubmanifold I I J0 ({(0 : ℝ)} : Set ℝ) f} := by
  exact notStableMapClass_ofZeroCounterexample hφsmooth hφsupport hφ0

end Problem617
