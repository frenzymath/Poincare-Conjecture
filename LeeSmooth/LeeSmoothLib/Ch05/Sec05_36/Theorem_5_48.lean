import LeeSmoothLib.Ch02.Sec02_10.Lemma_2_21
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_1
import LeeSmoothLib.Ch01.Sec01_06.Theorem_1_46
import LeeSmoothLib.Ch02.Sec02_11.Definition_2_11_extra_2
import LeeSmoothLib.Ch02.Sec02_11.Lemma_2_26
import LeeSmoothLib.Ch02.Sec02_11.Definition_2_11_extra_3
import LeeSmoothLib.Ch02.Sec02_11.Proposition_2_28
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_15
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch04.Sec04_24.Exercise_4_16
import LeeSmoothLib.Ch05.Sec05_30.Definition_5_30_extra_2
import LeeSmoothLib.Ch05.Sec05_35.Exercise_5_44
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_41
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_43
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_2
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_4
import LeeSmoothLib.Ch05.Sec05_36.Proposition_5_46
-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` returned only partition-of-unity and bump-function
-- separation lemmas, so the source-facing statements here use the local owners
-- `Set.IsRegularDomain`, `IsDefiningFunction`, and `Function.IsExhaustionFunction`.

open Topology
open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M]

local notation "dimM" => Module.finrank ℝ E

/-- Helper for Theorem 5.48: a regular domain is closed in the ambient manifold because its
subtype inclusion is properly embedded. -/
lemma regularDomain_isClosed
    (I : ModelWithCorners ℝ E H) {D : Set M}
    [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D] [T1Space M] :
    IsClosed D := by
  -- The proper-embedding field in `Set.IsRegularDomain` is exactly the closedness owner here.
  let hRegular : Set.IsRegularDomain I D := inferInstance
  have hProper : Set.IsProperlyEmbedded D := hRegular.isProperlyEmbedded
  exact Set.IsProperlyEmbedded.isClosed hProper

/-- Helper for Theorem 5.48: shifting a defining function by its witnessing regular value produces
an equivalent defining function cut out at level `0`. -/
lemma exists_zeroLevelDefiningFunction
    {D : Set M} {g : M → ℝ} (hg : IsDefiningFunction I D g) :
    ∃ g0 : M → ℝ,
      IsDefiningFunction I D g0 ∧
        D = g0 ⁻¹' Set.Iic 0 ∧
          Manifold.IsRegularValue I 𝓘(ℝ, ℝ) g0 0 := by
  rcases hg.isRegularSublevelSet.exists_regular_value with ⟨b, hb, hD⟩
  let g0 : M → ℝ := fun x ↦ g x - b
  have hg0Smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ g0 := by
    -- Subtracting the scalar regular value keeps the defining function smooth.
    simpa [g0] using hg.contMDiff.sub contMDiff_const
  have hg0Regular : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) g0 0 := by
    intro x hx
    have hxg : g x = b := by
      dsimp [g0] at hx
      linarith
    have hgContMDiffAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ g x := hg.contMDiff.contMDiffAt
    have hgDiffAt : MDiffAt g x :=
      hgContMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hconstDiffAt : MDiffAt (fun _ : M ↦ b) x := mdifferentiableAt_const
    -- The manifold derivative is unchanged by subtracting a constant, so regularity transfers.
    have hmfderiv :
        (mfderiv% g0 x : TangentSpace I x →L[ℝ] ℝ) = mfderiv% g x := by
      change
        (mfderiv% (g - fun _ : M ↦ b) x : TangentSpace I x →L[ℝ] ℝ) = mfderiv% g x
      rw [mfderiv_sub hgDiffAt hconstDiffAt, mfderiv_const]
      exact sub_zero _
    rw [hmfderiv]
    exact hb x hxg
  have hD0 : D = g0 ⁻¹' Set.Iic 0 := by
    -- The shifted closed ray `(-∞, 0]` is exactly the original closed ray `(-∞, b]`.
    rw [hD]
    ext x
    simp [g0]
  refine ⟨g0, ?_, hD0, hg0Regular⟩
  -- Package the shifted function with its new regular sublevel-set witness.
  exact ⟨hg0Smooth, ⟨⟨0, hg0Regular, hD0⟩⟩⟩

/-- Helper for Theorem 5.48: the zero-dimensional boundary model is boundaryless, so a regular
domain of ambient dimension `0` has no manifold boundary points. -/
lemma zeroDimensionalBoundaryModel_not_isBoundaryPoint
    {n : ℕ} {D : Set M} [SmoothManifoldWithBoundary n D] (h0 : n = 0) (x : D) :
    ¬ (leeBoundaryModelWithCorners n).IsBoundaryPoint x := by
  -- Rewrite the abstract dimension parameter to the exact `0`-dimensional owner, where Lee's
  -- boundary model is boundaryless and every point is interior.
  subst n
  have hxInt : (leeBoundaryModelWithCorners 0).IsInteriorPoint x := by
    -- In dimension `0`, Lee's boundary model is the boundaryless Euclidean owner `𝓡 0`.
    simpa [leeBoundaryModelWithCorners] using
      (show (𝓡 0).IsInteriorPoint x from BoundarylessManifold.isInteriorPoint)
  exact ((leeBoundaryModelWithCorners 0).isInteriorPoint_iff_not_isBoundaryPoint x).1 hxInt

/-- Helper for Theorem 5.48: in ambient dimension `0`, a regular domain is clopen, so a smooth
`{0, 1}`-valued separator shifted by `1 / 2` is already a defining function. -/
lemma zeroDimensionalRegularDomain_hasDefiningFunction
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M] (h0 : dimM = 0) :
    ∃ f : M → ℝ, IsDefiningFunction I D f := by
  have hDClosed : IsClosed D := regularDomain_isClosed I
  have hFrontierEmpty : frontier D = ∅ := by
    have hBoundaryFrontier :
        Subtype.val '' (leeBoundaryModelWithCorners dimM).boundary D = frontier D :=
      @regular_domain_manifoldBoundary_image_eq_frontier E _ _ _ H _ I M _ _ _ _ D _ _
    rw [← hBoundaryFrontier]
    ext x
    constructor
    · rintro ⟨y, hyBoundary, rfl⟩
      have hyBoundaryPoint : (leeBoundaryModelWithCorners dimM).IsBoundaryPoint y := by
        simpa [ModelWithCorners.boundary] using hyBoundary
      exact False.elim (zeroDimensionalBoundaryModel_not_isBoundaryPoint h0 y hyBoundaryPoint)
    · intro hx
      exact False.elim hx
  have hClopen : IsClopen D := (isClopen_iff_frontier_eq_empty).2 hFrontierEmpty
  have hDComplClosed : IsClosed Dᶜ := hClopen.isOpen.isClosed_compl
  obtain ⟨g, hgSmooth, _hgRange, hDZero, hDComplOne⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed I hDClosed hDComplClosed
      (by simpa using disjoint_compl_right)
  refine ⟨fun x ↦ g x - (1 / 2 : ℝ), ?_⟩
  have hfSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ g x - (1 / 2 : ℝ)) := by
    -- Shifting the separator by a constant preserves smoothness.
    exact hgSmooth.sub contMDiff_const
  have hZeroFiberEmpty : (fun x ↦ g x - (1 / 2 : ℝ)) ⁻¹' ({0} : Set ℝ) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxEq : g x - (1 / 2 : ℝ) = 0 := by
        simpa using hx
      by_cases hxD : x ∈ D
      · have hgx : g x = 0 := (hDZero x).1 hxD
        linarith
      · have hgx : g x = 1 := (hDComplOne x).1 hxD
        linarith
    · intro hx
      exact False.elim hx
  have hfReg :
      Manifold.IsRegularValue I 𝓘(ℝ, ℝ) (fun x ↦ g x - (1 / 2 : ℝ)) 0 := by
    -- The separator takes only the values `-1 / 2` and `1 / 2`, so the zero fiber is empty.
    exact Manifold.isRegularValue_of_preimage_eq_empty hZeroFiberEmpty
  have hDLevel : D = (fun x ↦ g x - (1 / 2 : ℝ)) ⁻¹' Set.Iic 0 := by
    ext x
    constructor
    · intro hxD
      have hgx : g x = 0 := (hDZero x).1 hxD
      simp [hgx]
    · intro hx
      by_cases hxD : x ∈ D
      · exact hxD
      · have hgx : g x = 1 := (hDComplOne x).1 hxD
        have hPos : 0 < g x - (1 / 2 : ℝ) := by
          rw [hgx]
          norm_num
        exact False.elim (not_le_of_gt hPos hx)
  -- Package the shifted separator as a regular sublevel-set witness at level `0`.
  refine (isDefiningFunction_iff I D (fun x ↦ g x - (1 / 2 : ℝ))).2 ?_
  refine ⟨hfSmooth, ?_⟩
  refine (isRegularSublevelSet_iff I (fun x ↦ g x - (1 / 2 : ℝ)) D).2 ?_
  exact ⟨0, hfReg, hDLevel⟩

/-- Helper for Theorem 5.48: positive ambient dimension can be rewritten in successor form. -/
lemma dimM_eq_succ_of_ne_zero (h0 : dimM ≠ 0) :
    ∃ n : ℕ, dimM = n + 1 := by
  -- This is the dimension rewrite needed before invoking the boundary owners on `D`.
  simpa [Nat.succ_eq_add_one] using Nat.exists_eq_succ_of_ne_zero h0

/-- Helper for Theorem 5.48: at a positive successor dimension, Lee's boundary-model owner is the
standard half-space model. -/
lemma leeBoundaryModelWithCorners_succ (n : ℕ) :
    leeBoundaryModelWithCorners (n + 1) = 𝓡∂ (n + 1) := by
  -- Route correction: use an explicit successor-form owner equality instead of dependent
  -- elimination on ambient-dimension proofs.
  simp [leeBoundaryModelWithCorners]

/-- Helper for Theorem 5.48: the successor-form owner rewrite is also available as a heterogeneous
equality, which isolates the remaining transport blocker to the manifold structure on `D`. -/
lemma leeBoundaryModelWithCorners_succ_heq (n : ℕ) :
    HEq (leeBoundaryModelWithCorners (n + 1)) (𝓡∂ (n + 1)) := by
  -- This records that the owner itself is not the hard part; the remaining blocker is transporting
  -- owner-dependent predicates across the induced manifold instances on the subtype.
  change HEq (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
  exact HEq.rfl

/-- Helper for Theorem 5.48: boundary-point statements can be transported from the original
regular-domain owner to the successor-form half-space owner. -/
lemma leeBoundaryModelWithCorners_isBoundaryPoint_iff_succ
    {m : ℕ} {D : Set M} [hOld : SmoothManifoldWithBoundary m D]
    [hSucc : SmoothManifoldWithBoundary (n + 1) D]
    (hm : m = n + 1)
    (hSucc_eq : hSucc = by simpa [hm] using hOld) {p : D} :
    (leeBoundaryModelWithCorners m).IsBoundaryPoint p ↔ (𝓡∂ (n + 1)).IsBoundaryPoint p := by
  -- The successor boundary structure is the one rebuilt from the original `dimM` owner, so after
  -- fixing that boundary structure, rewriting the owner index is now harmless.
  cases hSucc_eq
  cases hm
  exact Iff.rfl

/-- Helper for Theorem 5.48: immersion statements can be transported from the original
regular-domain owner to the successor-form half-space owner. -/
lemma leeBoundaryModelWithCorners_isImmersion_iff_succ
    {m : ℕ} {D : Set M} [hOld : SmoothManifoldWithBoundary m D]
    [hSucc : SmoothManifoldWithBoundary (n + 1) D]
    (hm : m = n + 1)
    (hSucc_eq : hSucc = by simpa [hm] using hOld) :
    Manifold.IsImmersion (leeBoundaryModelWithCorners m) I ∞ (Subtype.val : D → M) ↔
      Manifold.IsImmersion (𝓡∂ (n + 1)) I ∞ (Subtype.val : D → M) := by
  -- The successor boundary structure is definitionally rebuilt from the original one, so only the
  -- owner normalization remains.
  cases hSucc_eq
  cases hm
  exact Iff.rfl

/-- Helper for Theorem 5.48: on a boundaryless manifold, the preferred extended chart becomes a
genuine `E`-valued local chart after shrinking its target to the interior. -/
noncomputable def boundarylessLocalChart (x : M) : OpenPartialHomeomorph M E where
  toPartialEquiv :=
    { toFun := extChartAt I x
      invFun := (extChartAt I x).symm
      source := (extChartAt I x) ⁻¹' interior (extChartAt I x).target ∩ (extChartAt I x).source
      target := interior (extChartAt I x).target
      map_source' := by
        intro y hy
        -- The shrunken chart still lands in the chosen interior target.
        exact hy.1
      map_target' := by
        intro y hy
        have hyTarget : y ∈ (extChartAt I x).target := interior_subset hy
        have hySource : (extChartAt I x).symm y ∈ (extChartAt I x).source :=
          (extChartAt I x).map_target hyTarget
        have hyEq : extChartAt I x ((extChartAt I x).symm y) = y :=
          PartialEquiv.right_inv (extChartAt I x) hyTarget
        -- The inverse of the extended chart returns to the shrunken source.
        refine ⟨?_, hySource⟩
        show extChartAt I x ((extChartAt I x).symm y) ∈ interior (extChartAt I x).target
        exact hyEq.symm ▸ hy
      left_inv' := by
        intro y hy
        -- On the source, the new chart agrees with the original extended chart.
        exact PartialEquiv.left_inv (extChartAt I x) hy.2
      right_inv' := by
        intro y hy
        -- On the shrunken target, the inverse is still the original extended-chart inverse.
        exact PartialEquiv.right_inv (extChartAt I x) (interior_subset hy) }
  open_source := by
    -- The source is the preimage of an ambient-open target under the extended chart.
    let s : Set E := interior (extChartAt I x).target
    have hOpen :
        IsOpen ((chartAt H x).source ∩ (chartAt H x).extend I ⁻¹' s) :=
      (chartAt H x).isOpen_extend_preimage isOpen_interior
    simpa [s, extChartAt, Set.inter_comm] using hOpen
  open_target := by
    -- By construction the target is an interior subset of `E`.
    exact isOpen_interior
  continuousOn_toFun := by
    intro y hy
    -- Shrinking the source does not affect continuity of the extended chart.
    exact ((continuousOn_extChartAt x) y hy.2).mono <| by
      intro z hz
      exact hz.2
  continuousOn_invFun := by
    intro y hy
    -- The inverse remains continuous on the smaller interior target.
    exact ((continuousOn_extChartAt_symm x) y (interior_subset hy)).mono <| by
      intro z hz
      exact interior_subset hz

/-- Helper for Theorem 5.48: the boundaryless ambient manifold admits a repaired
`ChartedSpace E M` whose charts are the original `H`-charts viewed in `E`-coordinates. -/
noncomputable abbrev boundarylessModelChartedSpace
    (I : ModelWithCorners ℝ E H) [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M] :
    ChartedSpace E M :=
  -- Route correction: `extChartAt I x` is only a `PartialEquiv`, so we replace it by the
  -- shrunken open chart `boundarylessLocalChart x`.
  { atlas := Set.range (fun x : M ↦ boundarylessLocalChart x)
    chartAt := fun x : M ↦ boundarylessLocalChart x
    mem_chart_source := by
      intro x
      -- Boundarylessness puts the base point in the interior of the extended-chart target.
      refine ⟨?_, ?_⟩
      · show extChartAt I x x ∈ interior (extChartAt I x).target
        exact (I.isInteriorPoint_iff).mp
          (show I.IsInteriorPoint x from BoundarylessManifold.isInteriorPoint)
      · show x ∈ (extChartAt I x).source
        rw [extChartAt_source I]
        exact mem_chart_source H x
    chart_mem_atlas := by
      intro x
      exact ⟨x, rfl⟩ }

/-- Helper for Theorem 5.48: the extended `E`-valued atlas is smooth because transitions are the
standard `I.extendCoordChange` maps between original maximal-atlas charts. -/
lemma boundarylessModelIsManifold
    (I : ModelWithCorners ℝ E H) [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M] :
    let _ : ChartedSpace E M := boundarylessModelChartedSpace I
    IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace I
  -- Each repaired chart change is the original `I.extendCoordChange` restricted to interior chart
  -- targets, so the old maximal-atlas smoothness theorem still applies after shrinking the domain.
  exact isManifold_of_contDiffOn (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M <| by
    intro e e' he he'
    rcases he with ⟨x, rfl⟩
    rcases he' with ⟨y, rfl⟩
    refine (I.contDiffOn_extendCoordChange
        (IsManifold.chart_mem_maximalAtlas x)
        (IsManifold.chart_mem_maximalAtlas y)).mono ?_
    intro z hz
    -- The repaired transition source is a smaller subset of the original change-of-coordinates
    -- source because both charts were shrunk to interior targets.
    simp [boundarylessLocalChart, extChartAt, ModelWithCorners.extendCoordChange,
      Set.preimage_comp] at hz ⊢
    rcases hz with ⟨hzx, hrest⟩
    rcases hrest with ⟨_, hzSource⟩
    refine ⟨?_, hzSource⟩
    refine ⟨⟨I.symm z, I.right_inv (interior_subset hzx.1)⟩, ?_⟩
    simpa [(chartAt H x).open_target.interior_eq] using interior_subset hzx.2

/-- Helper for Theorem 5.48: an ordered basis gives a fixed continuous linear equivalence
`ℝ^(n + 1) ≃L[ℝ] E` for the repaired self-model atlas. -/
noncomputable def ambientBasisContinuousLinearEquiv
    {n : ℕ} (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] E :=
  let e : E ≃ₗ[ℝ] Fin (n + 1) → ℝ := b.equivFun
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).trans e.symm.toContinuousLinearEquiv

/-- Helper for Theorem 5.48: an ordered basis gives a fixed diffeomorphism from `ℝ^(n + 1)` to
the ambient model space `E`. -/
noncomputable def ambientBasisDiffeomorph
    {n : ℕ} (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₘ[ℝ] E :=
  (ambientBasisContinuousLinearEquiv hn b).toDiffeomorph

/-- Helper for Theorem 5.48: the corresponding Euclidean coordinate change on `E` as an open
partial homeomorphism. -/
noncomputable abbrev ambientBasisModelChart
    {n : ℕ} (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E) :
    OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (n + 1))) :=
  (ambientBasisDiffeomorph hn b).symm.toHomeomorph.toOpenPartialHomeomorph

/-- Helper for Theorem 5.48: conjugating an `E`-smooth chart transition by the fixed basis chart
produces a Euclidean-smooth transition. -/
lemma ambientBasisTransition_mem_contDiffGroupoid
    {n : ℕ} (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E)
    {e : OpenPartialHomeomorph E E}
    (he : e ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E)) :
    let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (n + 1))) :=
      ambientBasisModelChart hn b
    (eModel.symm.trans e).trans eModel ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (n + 1)) := by
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (n + 1))) :=
    ambientBasisModelChart hn b
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at he ⊢
  have he_left : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (e : E → E) e.source := by
    simpa using he.1
  have he_right : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (e.symm : E → E) e.target := by
    simpa using he.2
  have heModel_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞) (eModel : E → EuclideanSpace ℝ (Fin (n + 1))) := by
    -- The basis chart is the inverse of a fixed continuous linear equivalence `ℝ^(n + 1) ≃L E`.
    simpa [eModel, ambientBasisModelChart, ambientBasisDiffeomorph, ambientBasisContinuousLinearEquiv] using
      (ambientBasisContinuousLinearEquiv hn b).symm.toContinuousLinearMap.contDiff
  have heModel_symm_contDiff :
      ContDiff ℝ (⊤ : WithTop ℕ∞) (eModel.symm : EuclideanSpace ℝ (Fin (n + 1)) → E) := by
    -- Its inverse is the original continuous linear equivalence `ℝ^(n + 1) ≃L E`.
    simpa [eModel, ambientBasisModelChart, ambientBasisDiffeomorph, ambientBasisContinuousLinearEquiv] using
      (ambientBasisContinuousLinearEquiv hn b).toContinuousLinearMap.contDiff
  have hsource :
      eModel.symm ⁻¹' e.source = ((eModel.symm.trans e).trans eModel).source := by
    -- The fixed basis chart is globally defined, so the transported source is just a preimage.
    ext x
    simp [eModel]
  have htarget :
      eModel.symm ⁻¹' e.target = ((eModel.symm.trans e).trans eModel).target := by
    -- The same simplification holds for the target.
    ext x
    simp [eModel]
  constructor
  · -- Compose the original `E`-smooth transition with the fixed Euclidean coordinate changes.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ e (eModel.symm x))
          (eModel.symm ⁻¹' e.source) := by
      refine he_left.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ eModel (e (eModel.symm x)))
          (eModel.symm ⁻¹' e.source) := by
      refine (heModel_contDiff.contDiffOn :
          ContDiffOn ℝ (⊤ : WithTop ℕ∞) eModel Set.univ).comp hmid ?_
      intro x hx
      simp [Set.mem_univ, eModel]
    simpa [hsource, eModel, Function.comp, OpenPartialHomeomorph.trans_source] using hfinal
  · -- Apply the same conjugation to the inverse transition.
    have hmid :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ e.symm (eModel.symm x))
          (eModel.symm ⁻¹' e.target) := by
      refine he_right.comp heModel_symm_contDiff.contDiffOn ?_
      intro x hx
      simpa using hx
    have hfinal :
        ContDiffOn ℝ (⊤ : WithTop ℕ∞)
          (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ eModel (e.symm (eModel.symm x)))
          (eModel.symm ⁻¹' e.target) := by
      refine (heModel_contDiff.contDiffOn :
          ContDiffOn ℝ (⊤ : WithTop ℕ∞) eModel Set.univ).comp hmid ?_
      intro x hx
      simp [Set.mem_univ, eModel]
    simpa [htarget, eModel, Function.comp, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc] using
      hfinal

/-- Helper for Theorem 5.48: after installing the repaired self-model atlas on `M`, transport it
to Euclidean coordinates through the fixed basis chart on `E`. -/
noncomputable abbrev ambientBasisChartedSpace
    (I : ModelWithCorners ℝ E H) [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M]
    {n : ℕ} (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E) :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace I
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (n + 1))) :=
    ambientBasisModelChart hn b
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) E :=
    eModel.singletonChartedSpace (by
      ext x
      simp [eModel, ambientBasisModelChart, ambientBasisDiffeomorph, ambientBasisContinuousLinearEquiv])
  exact ChartedSpace.comp (EuclideanSpace ℝ (Fin (n + 1))) E M

/-- Helper for Theorem 5.48: the Euclidean ambient structure on `M` is the canonical basis-model
transport of the repaired self-model atlas. -/
lemma ambientBasisIsManifold
    (I : ModelWithCorners ℝ E H) [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M]
    {n : ℕ} (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      (ambientBasisChartedSpace I hn b :
        ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M)
    IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace I
  let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
    (boundarylessModelIsManifold I :
      let _ : ChartedSpace E M := boundarylessModelChartedSpace I
      IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (n + 1))) :=
    ambientBasisModelChart hn b
  have heModel_source : eModel.source = Set.univ := by
    -- The basis model change is global because it comes from a diffeomorphism.
    ext x
    simp [eModel, ambientBasisContinuousLinearEquiv]
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) E :=
    eModel.singletonChartedSpace heModel_source
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    (ambientBasisChartedSpace I hn b :
      ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M)
  have hGroupoid :
      HasGroupoid M (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (n + 1))) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hcEq : c = eModel := by
      simpa [eModel] using
        eModel.singletonChartedSpace_mem_atlas_eq heModel_source c hc
    have hc'Eq : c' = eModel := by
      simpa [eModel] using
        eModel.singletonChartedSpace_mem_atlas_eq heModel_source c' hc'
    subst c
    subst c'
    -- Every transported transition is the old self-model transition conjugated by the fixed basis
    -- chart.
    have hcompat_old :
        f.symm.trans f' ∈ contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E) :=
      HasGroupoid.compatible hf hf'
    simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, eModel] using
      ambientBasisTransition_mem_contDiffGroupoid hn b hcompat_old
  let _ : HasGroupoid M (contDiffGroupoid (⊤ : WithTop ℕ∞) (𝓡 (n + 1))) := hGroupoid
  exact IsManifold.mk' (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M

/-- Helper for Theorem 5.48: an extended original chart stays in the Euclidean maximal atlas after
the basis-model transport. -/
lemma ambientBasisChart_mem_maximalAtlas
    (I : ModelWithCorners ℝ E H) [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M]
    {n : ℕ} (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E)
    {chart : OpenPartialHomeomorph M E}
    (hchart :
      let _ : ChartedSpace E M := boundarylessModelChartedSpace I
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      (ambientBasisChartedSpace I hn b :
        ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M)
    let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
      (ambientBasisIsManifold I hn b :
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
          (ambientBasisChartedSpace I hn b :
            ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M)
        IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M)
    let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (n + 1))) :=
      ambientBasisModelChart hn b
    chart.trans eModel ∈ IsManifold.maximalAtlas (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace I
  let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
    (boundarylessModelIsManifold I :
      let _ : ChartedSpace E M := boundarylessModelChartedSpace I
      IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (n + 1))) :=
    ambientBasisModelChart hn b
  have heModel_source : eModel.source = Set.univ := by
    -- The fixed basis chart is globally defined.
    ext x
    simp [eModel, ambientBasisContinuousLinearEquiv]
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) E :=
    eModel.singletonChartedSpace heModel_source
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    (ambientBasisChartedSpace I hn b :
      ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M)
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    (ambientBasisIsManifold I hn b :
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
        (ambientBasisChartedSpace I hn b :
          ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M)
      IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M)
  rw [IsManifold.mem_maximalAtlas_iff]
  intro c hc
  rcases hc with ⟨f, hf, c', hc', rfl⟩
  have hc'Eq : c' = eModel := by
    simpa [eModel] using
      eModel.singletonChartedSpace_mem_atlas_eq heModel_source c' hc'
  subst c'
  have hleft_old : chart.symm.trans f ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E) := by
    exact (IsManifold.mem_maximalAtlas_iff.mp hchart) f hf |>.1
  have hright_old : f.symm.trans chart ∈
      contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℝ E) := by
    exact (IsManifold.mem_maximalAtlas_iff.mp hchart) f hf |>.2
  constructor
  · -- Transport left compatibility from the repaired self-model atlas.
    simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, eModel] using
      ambientBasisTransition_mem_contDiffGroupoid hn b hleft_old
  · -- Transport right compatibility from the repaired self-model atlas.
    simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, eModel] using
      ambientBasisTransition_mem_contDiffGroupoid hn b hright_old

private noncomputable abbrev boundarylessChartedSpaceFor
    (I : ModelWithCorners ℝ E H)
    [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M] :
    ChartedSpace E M :=
  boundarylessModelChartedSpace I

private noncomputable abbrev boundarylessModelIsManifoldFor
    (I : ModelWithCorners ℝ E H)
    [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M] :
    let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
    IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M := by
  let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
  simpa [boundarylessChartedSpaceFor] using
    (boundarylessModelIsManifold I :
      let _ : ChartedSpace E M := boundarylessModelChartedSpace I
      IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)

private noncomputable abbrev boundarylessLocalChartFor
    (I : ModelWithCorners ℝ E H)
    [IsManifold I (⊤ : WithTop ℕ∞) M] [BoundarylessManifold I M]
    (x : M) : OpenPartialHomeomorph M E :=
  @boundarylessLocalChart E _ _ H _ M _ _ I x

/-- Helper for Theorem 5.48: the repaired boundaryless self-modeled atlas on `M` still embeds
smoothly into the original ambient manifold structure `I` via the identity map. -/
lemma boundarylessAmbientId_isSmoothEmbedding
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    [BoundarylessManifold I M] :
    let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
    let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
      (boundarylessModelIsManifoldFor I :
        let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
        IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
    Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ E) I (⊤ : WithTop ℕ∞) (id : M → M) := by
  let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
  let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
    (boundarylessModelIsManifoldFor I :
      let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
      IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  refine ⟨?_, Topology.IsEmbedding.id⟩
  refine ⟨PUnit.{uE + 1}, inferInstance, inferInstance, ?_⟩
  intro x
  let domChart : OpenPartialHomeomorph M E := boundarylessLocalChartFor I x
  -- The repaired self-modeled chart and the original ambient chart both read the identity map as
  -- the identity on `E` in written-in-extended-charts form.
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuousAt_id
    (ContinuousLinearEquiv.prodUnique ℝ E PUnit.{uE + 1})
    domChart
    (chartAt H x)
    ?_
    ?_
    ?_
    ?_
    ?_
  · simpa [domChart, boundarylessModelChartedSpace] using
      (show x ∈ (boundarylessLocalChartFor I x).source from by
        refine ⟨?_, ?_⟩
        · show extChartAt I x x ∈ interior (extChartAt I x).target
          exact (I.isInteriorPoint_iff).mp
            (show I.IsInteriorPoint x from BoundarylessManifold.isInteriorPoint)
        · show x ∈ (extChartAt I x).source
          rw [extChartAt_source I]
          exact mem_chart_source H x)
  · simpa using (mem_chart_source H x)
  · simpa [domChart, boundarylessChartedSpaceFor, boundarylessLocalChartFor,
      boundarylessModelChartedSpace] using
      (IsManifold.chart_mem_maximalAtlas x :
        chartAt E x ∈
          IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  · simpa using
      (IsManifold.chart_mem_maximalAtlas x :
        chartAt H x ∈ IsManifold.maximalAtlas I (⊤ : WithTop ℕ∞) M)
  · intro u hu
    have hu_target : u ∈ domChart.target := by
      -- On the self-modeled source, the extended target is the ordinary chart target.
      simpa [domChart, OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe] using hu
    -- The repaired self-modeled chart is exactly `extChartAt I x` on its target.
    simpa [domChart, boundarylessLocalChart, extChartAt, Function.comp,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm] using
      domChart.right_inv hu_target

/-- Helper for Theorem 5.48: after Euclideanizing the repaired boundaryless ambient atlas, the
identity map remains a smooth embedding back into that self-modeled ambient structure. -/
lemma ambientBasisBoundarylessAmbientId_isSmoothEmbedding
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    [BoundarylessManifold I M]
    {n : ℕ} (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E) :
    let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
    let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
      (boundarylessModelIsManifoldFor I :
        let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
        IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      ambientBasisChartedSpace I hn b
    let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
      ambientBasisIsManifold I hn b
    Manifold.IsSmoothEmbedding
      (𝓡 (n + 1))
      (modelWithCornersSelf ℝ E)
      (⊤ : WithTop ℕ∞)
      (id : M → M) := by
  let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
  let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
    (boundarylessModelIsManifoldFor I :
      let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
      IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    ambientBasisChartedSpace I hn b
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold I hn b
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (n + 1))) :=
    (ambientBasisDiffeomorph hn b).symm.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨?_, Topology.IsEmbedding.id⟩
  refine ⟨PUnit, inferInstance, inferInstance, ?_⟩
  intro x
  let codChart : OpenPartialHomeomorph M E := boundarylessLocalChartFor I x
  let domChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
    codChart.trans eModel
  let equiv :
      (EuclideanSpace ℝ (Fin (n + 1)) × PUnit.{uE + 1}) ≃L[ℝ] E :=
    (ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin (n + 1))) PUnit.{uE + 1}).trans
      (ambientBasisContinuousLinearEquiv hn b)
  have hcodChart :
      codChart ∈ IsManifold.maximalAtlas
        (modelWithCornersSelf ℝ E)
        (⊤ : WithTop ℕ∞)
        M := by
    simpa [codChart, boundarylessChartedSpaceFor, boundarylessLocalChartFor,
      boundarylessModelChartedSpace] using
      (IsManifold.chart_mem_maximalAtlas x :
        chartAt E x ∈
          IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  have hdomChart :
      domChart ∈ IsManifold.maximalAtlas (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M := by
    -- Transport the repaired self-modeled chart through the fixed basis chart once.
    simpa [domChart, codChart, eModel] using
      (ambientBasisChart_mem_maximalAtlas I hn b hcodChart)
  -- In the Euclideanized chart, the identity map is the fixed basis linear equivalence back to
  -- the repaired self-modeled ambient coordinates.
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuousAt_id
    equiv
    domChart
    codChart
    ?_
    ?_
    hdomChart
    hcodChart
    ?_
  · have hx_cod : x ∈ codChart.source := by
      refine ⟨?_, ?_⟩
      · show extChartAt I x x ∈ interior (extChartAt I x).target
        exact (I.isInteriorPoint_iff).mp
          (show I.IsInteriorPoint x from BoundarylessManifold.isInteriorPoint)
      · show x ∈ (extChartAt I x).source
        rw [extChartAt_source I]
        exact mem_chart_source H x
    simpa [domChart, codChart, eModel, OpenPartialHomeomorph.trans_source] using hx_cod
  · refine ⟨?_, ?_⟩
    · show extChartAt I x x ∈ interior (extChartAt I x).target
      exact (I.isInteriorPoint_iff).mp
        (show I.IsInteriorPoint x from BoundarylessManifold.isInteriorPoint)
    · show x ∈ (extChartAt I x).source
      rw [extChartAt_source I]
      exact mem_chart_source H x
  · intro u hu
    have hu_target :
        (ambientBasisContinuousLinearEquiv hn b) u ∈ codChart.target := by
      -- The extended source target is the Euclidean image of the repaired self-model target.
      simpa [domChart, codChart, eModel, OpenPartialHomeomorph.extend_target,
        OpenPartialHomeomorph.trans_target, ambientBasisDiffeomorph,
        ambientBasisContinuousLinearEquiv] using hu
    -- After undoing the Euclidean basis change, both source and target charts are the same
    -- repaired self-modeled chart.
    simpa [equiv, domChart, codChart, eModel, Function.comp,
      ambientBasisDiffeomorph, ambientBasisContinuousLinearEquiv,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm] using
      codChart.right_inv hu_target

/-- Helper for Theorem 5.48: after Euclideanizing the repaired boundaryless ambient atlas, the
identity map is also a smooth embedding in the reverse direction from the self-modeled ambient
structure to the Euclidean ambient structure. -/
lemma boundarylessAmbientBasisId_isSmoothEmbedding
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    [BoundarylessManifold I M]
    {n : ℕ} (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E) :
    let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
    let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
      (boundarylessModelIsManifoldFor I :
        let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
        IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      ambientBasisChartedSpace I hn b
    let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
      ambientBasisIsManifold I hn b
    Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ E)
      (𝓡 (n + 1))
      (⊤ : WithTop ℕ∞)
      (id : M → M) := by
  let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
  let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
    (boundarylessModelIsManifoldFor I :
      let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
      IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    ambientBasisChartedSpace I hn b
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold I hn b
  let eModel : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (n + 1))) :=
    (ambientBasisDiffeomorph hn b).symm.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨?_, Topology.IsEmbedding.id⟩
  refine ⟨PUnit, inferInstance, inferInstance, ?_⟩
  intro x
  let domChart : OpenPartialHomeomorph M E := boundarylessLocalChartFor I x
  let codChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))) :=
    domChart.trans eModel
  let equiv :
      (E × PUnit) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (ContinuousLinearEquiv.prodUnique ℝ E PUnit).trans
      (ambientBasisContinuousLinearEquiv hn b).symm
  have hdomChart :
      domChart ∈ IsManifold.maximalAtlas
        (modelWithCornersSelf ℝ E)
        (⊤ : WithTop ℕ∞)
        M := by
    simpa [domChart, boundarylessChartedSpaceFor, boundarylessLocalChartFor,
      boundarylessModelChartedSpace] using
      (IsManifold.chart_mem_maximalAtlas x :
        chartAt E x ∈
          IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  have hcodChart :
      codChart ∈ IsManifold.maximalAtlas (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M := by
    -- Transport the repaired self-modeled chart through the fixed Euclidean basis chart once.
    simpa [codChart, domChart, eModel] using
      (ambientBasisChart_mem_maximalAtlas I hn b hdomChart)
  -- The reverse identity bridge is the same fixed basis linear equivalence, now read from the
  -- repaired self-model coordinates into the Euclidean ambient coordinates.
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuousAt_id
    equiv
    domChart
    codChart
    ?_
    ?_
    hdomChart
    hcodChart
    ?_
  · refine ⟨?_, ?_⟩
    · show extChartAt I x x ∈ interior (extChartAt I x).target
      exact (I.isInteriorPoint_iff).mp
        (show I.IsInteriorPoint x from BoundarylessManifold.isInteriorPoint)
    · show x ∈ (extChartAt I x).source
      rw [extChartAt_source I]
      exact mem_chart_source H x
  · have hx_dom : x ∈ domChart.source := by
      refine ⟨?_, ?_⟩
      · show extChartAt I x x ∈ interior (extChartAt I x).target
        exact (I.isInteriorPoint_iff).mp
          (show I.IsInteriorPoint x from BoundarylessManifold.isInteriorPoint)
      · show x ∈ (extChartAt I x).source
        rw [extChartAt_source I]
        exact mem_chart_source H x
    refine ⟨hx_dom, ?_⟩
    simpa [eModel, ambientBasisContinuousLinearEquiv]
  · intro u hu
    have hu_target :
        (ambientBasisContinuousLinearEquiv hn b).symm u ∈ codChart.target := by
      -- The Euclidean target coordinates are exactly the image of the repaired self-model target
      -- under the fixed basis chart.
      simpa [domChart, codChart, eModel, OpenPartialHomeomorph.extend_target,
        OpenPartialHomeomorph.trans_target, ambientBasisDiffeomorph,
        ambientBasisContinuousLinearEquiv] using hu
    -- After applying the repaired self-model chart inverse, the transported codomain chart is
    -- exactly the fixed Euclidean basis change on the same self-model coordinates.
    simpa [equiv, domChart, codChart, eModel, Function.comp,
      ambientBasisDiffeomorph, ambientBasisContinuousLinearEquiv,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm] using
      codChart.right_inv hu_target

/-- Helper for Theorem 5.48: the Euclideanized ambient atlas should be transported back to the
original ambient model only once, at the frontier normal-form step. -/
lemma ambientBasisAmbientId_isSmoothEmbedding
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    [BoundarylessManifold I M]
    {n : ℕ} (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E) :
    let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
    let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
      (boundarylessModelIsManifoldFor I :
        let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
        IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      ambientBasisChartedSpace I hn b
    let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
      ambientBasisIsManifold I hn b
    Manifold.IsSmoothEmbedding (𝓡 (n + 1)) I (⊤ : WithTop ℕ∞) (id : M → M) := by
  let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
  let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
    (boundarylessModelIsManifoldFor I :
      let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
      IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    ambientBasisChartedSpace I hn b
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold I hn b
  -- Route correction: compose the Euclidean-to-self-model identity bridge with the repaired
  -- self-model-to-ambient identity bridge in the same owner-normal form as Problem 5-21.
  simpa [Function.comp] using
    Manifold.IsSmoothEmbedding.comp
      boundarylessAmbientId_isSmoothEmbedding
      (ambientBasisBoundarylessAmbientId_isSmoothEmbedding hn b)

/-- Helper for Theorem 5.48: the regular-domain structure already provides the subtype inclusion as
an `∞`-smooth embedding into the original ambient model. -/
lemma regularDomainSubtypeVal_isSmoothEmbedding_infty
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D] :
    Manifold.IsSmoothEmbedding
      (leeBoundaryModelWithCorners dimM)
      I
      ∞
      (Subtype.val : D → M) := by
  -- The regular-domain API stores exactly this embedding.
  let hRegular : Set.IsRegularDomain I D := inferInstance
  exact hRegular.isSmoothEmbedding_subtype_val

/-- Helper for Theorem 5.48: the regular-domain subtype inclusion is already `C^∞` in the
ambient owner, so later transport work only needs to change owners, not recover smoothness. -/
lemma regularDomainSubtypeVal_contMDiff_infty
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D] :
    ContMDiff (leeBoundaryModelWithCorners dimM) I ∞ (Subtype.val : D → M) := by
  -- This records the smoothness part of the regular-domain API in the theorem-local owner.
  exact (regularDomainSubtypeVal_isSmoothEmbedding_infty (I := I) (D := D)).isImmersion.contMDiff

/-- Helper for Theorem 5.48: in full ambient dimension, a Euclidean half-slice is exactly the
ambient chart target together with nonnegativity of the last coordinate. -/
lemma fullDimensionalHalfSlice_mem_iff_lastCoord_nonneg
    {n : ℕ} {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {c : Fin ((n + 1) - (n + 1)) → ℝ}
    {z : EuclideanSpace ℝ (Fin (n + 1))} :
    z ∈ Set.euclideanHalfSlice V (n + 1) (Nat.succ_pos _) le_rfl c ↔
      z ∈ V ∧ 0 ≤ z (Fin.last n) := by
  -- In full dimension there are no tail coordinates to freeze, so only the last-coordinate
  -- nonnegativity condition remains.
  rw [Set.euclideanHalfSlice, Set.euclideanSlice]
  constructor
  · rintro ⟨⟨hzV, _hzTail⟩, hzLast⟩
    exact ⟨hzV, by simpa [Set.euclideanHalfSlice, Set.euclideanSlice] using hzLast⟩
  · rintro ⟨hzV, hzLast⟩
    refine ⟨⟨hzV, ?_⟩, ?_⟩
    · intro i
      exact False.elim ((Nat.not_lt_zero i.1) <| by simpa using i.2)
    · simpa [Set.euclideanHalfSlice, Set.euclideanSlice] using hzLast

/-- Helper for Theorem 5.48: on the source of a full-dimensional boundary slice chart for `D`,
membership in `D` is exactly nonnegativity of the last chart coordinate. -/
lemma mem_iff_nonneg_lastCoord_of_boundarySliceChart
    {n : ℕ} {D : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M]
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1)))}
    (he : e.IsBoundarySliceChart D (n + 1)) {y : M} (hy : y ∈ e.source) :
    y ∈ D ↔ 0 ≤ e y (Fin.last n) := by
  classical
  have hhkn :
      ∃ hkn : n + 1 ≤ n + 1, ∃ c : Fin ((n + 1) - (n + 1)) → ℝ,
        e '' (D ∩ e.source) =
          Set.euclideanHalfSlice e.target (n + 1) (Nat.succ_pos _) hkn c := by
    -- Unpack the boundary-slice chart witness and normalize the proof arguments for the
    -- full-dimensional half-slice owner.
    simpa [Set.IsHalfSliceInChart, Set.IsEuclideanHalfSlice] using
      (Classical.choose_spec he.2)
  let hkn : n + 1 ≤ n + 1 := Classical.choose hhkn
  have hc :
      ∃ c : Fin ((n + 1) - (n + 1)) → ℝ,
        e '' (D ∩ e.source) =
          Set.euclideanHalfSlice e.target (n + 1) (Nat.succ_pos _) hkn c := by
    simpa [hkn] using (Classical.choose_spec hhkn)
  let c : Fin ((n + 1) - (n + 1)) → ℝ := Classical.choose hc
  have hHalfSlice :
      e '' (D ∩ e.source) =
        Set.euclideanHalfSlice e.target (n + 1) (Nat.succ_pos _) hkn c :=
    Classical.choose_spec hc
  have hkn_eq : hkn = le_rfl := Subsingleton.elim _ _
  subst hkn
  have hHalfSliceMem :
      e y ∈ Set.euclideanHalfSlice e.target (n + 1) (Nat.succ_pos _) le_rfl c ↔
        e y ∈ e.target ∧ 0 ≤ e y (Fin.last n) :=
    fullDimensionalHalfSlice_mem_iff_lastCoord_nonneg
  constructor
  · intro hyD
    -- Push the point into the chart image of `D` and read membership there as a last-coordinate
    -- inequality.
    have hey : e y ∈ e '' (D ∩ e.source) := ⟨y, ⟨hyD, hy⟩, rfl⟩
    rw [hHalfSlice] at hey
    exact hHalfSliceMem.1 hey |>.2
  · intro hyLast
    -- Conversely, the half-slice condition gives an image witness coming from a point of
    -- `D ∩ e.source`, and injectivity of the chart on its source identifies that witness with `y`.
    have heyHalf :
        e y ∈ Set.euclideanHalfSlice e.target (n + 1) (Nat.succ_pos _) le_rfl c :=
      hHalfSliceMem.2 ⟨e.map_source hy, hyLast⟩
    have hey : e y ∈ e '' (D ∩ e.source) := by
      rw [hHalfSlice]
      exact heyHalf
    rcases hey with ⟨z, ⟨hzD, hzsource⟩, hzy⟩
    exact (e.injOn hzsource hy hzy) ▸ hzD

/-- Helper for Theorem 5.48: a boundary defining function vanishes exactly at the boundary
points of the manifold-with-boundary source. -/
lemma boundaryDefiningFunction_eq_zero_iff
    {n : ℕ} {N : Type*} [TopologicalSpace N] [SmoothManifoldWithBoundary (n + 1) N]
    {β : N → ℝ} (hβ : @IsBoundaryDefiningFunction n N _ _ β) {p : N} :
    β p = 0 ↔ (𝓡∂ (n + 1)).IsBoundaryPoint p := by
  constructor
  · intro hp
    have hpSet : p ∈ β ⁻¹' ({0} : Set ℝ) := by
      simpa using hp
    rwa [hβ.zero_preimage] at hpSet
  · intro hp
    have hpSet : p ∈ {q : N | (𝓡∂ (n + 1)).IsBoundaryPoint q} := hp
    rwa [← hβ.zero_preimage] at hpSet

/-- Helper for Theorem 5.48: away from boundary points, a boundary defining function is strictly
positive because it is globally nonnegative and its zero set is the boundary. -/
lemma boundaryDefiningFunction_pos_iff_not_boundaryPoint
    {n : ℕ} {N : Type*} [TopologicalSpace N] [SmoothManifoldWithBoundary (n + 1) N]
    {β : N → ℝ} (hβ : @IsBoundaryDefiningFunction n N _ _ β) {p : N} :
    0 < β p ↔ ¬ (𝓡∂ (n + 1)).IsBoundaryPoint p := by
  constructor
  · intro hp hpBoundary
    have hZero : β p = 0 := (boundaryDefiningFunction_eq_zero_iff hβ).2 hpBoundary
    exact (lt_irrefl 0) <| by simpa [hZero] using hp
  · intro hpNotBoundary
    have hNonneg : 0 ≤ β p := hβ.nonneg p
    have hNe : β p ≠ 0 := by
      intro hpZero
      exact hpNotBoundary ((boundaryDefiningFunction_eq_zero_iff hβ).1 hpZero)
    exact lt_of_le_of_ne hNonneg (by simpa using hNe.symm)

/-- Helper for Theorem 5.48: when the local boundary inclusion form has equal source and target
dimension, it is literally the ambient inclusion of the half-space coordinates. -/
lemma boundaryImmersionNormalForm_self {n : ℕ} [NeZero (n + 1)]
    (x : EuclideanHalfSpace (n + 1)) :
    boundary_immersion_normal_form (n + 1) (n + 1) x = x.1 := by
  -- Compare coordinates one by one and use the full-rank normal-form formula.
  ext i
  rw [boundary_immersion_normal_form_apply]
  exact rank_normal_form_apply_of_lt i.2 i.2 x.1

/-- Helper for Theorem 5.48: a nonzero real-valued continuous linear map is automatically
surjective. -/
lemma surjective_of_ne_zero_realContinuousLinearMap
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {L : V →L[ℝ] ℝ} (hL : L ≠ 0) :
    Function.Surjective L := by
  -- Pick one vector with nonzero image and rescale it to hit any target real number.
  have hExists : ∃ v : V, L v ≠ 0 := by
    by_contra hNo
    apply hL
    ext v
    by_contra hLv
    exact hNo ⟨v, hLv⟩
  rcases hExists with ⟨v, hv⟩
  intro y
  refine ⟨(y / L v) • v, ?_⟩
  rw [map_smul]
  have hmul : (y / L v) * L v = y := by
    field_simp [hv]
  simpa [smul_eq_mul] using hmul

/-- Helper for Theorem 5.48: frontier points of a regular domain are exactly the ambient images of
boundary points of the domain's manifold-with-boundary structure. -/
lemma mem_frontier_iff_exists_boundaryPoint
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D] {x : M} :
    x ∈ frontier D ↔
      ∃ p : D, (leeBoundaryModelWithCorners dimM).IsBoundaryPoint p ∧ p.1 = x := by
  -- Proposition 5.46 identifies the ambient frontier with the subtype image of the boundary.
  have hBoundaryFrontier :
      Subtype.val '' (leeBoundaryModelWithCorners dimM).boundary D = frontier D :=
    @regular_domain_manifoldBoundary_image_eq_frontier E _ _ _ H _ I M _ _ _ _ D _ _
  rw [← hBoundaryFrontier]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, ?_, rfl⟩
    simpa [ModelWithCorners.boundary] using hp
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩

/-- Helper for Theorem 5.48: a boundary point of the regular-domain structure maps to an ambient
frontier point. -/
lemma boundaryPoint_mem_frontier
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    {p : D} (hp : (leeBoundaryModelWithCorners dimM).IsBoundaryPoint p) :
    p.1 ∈ frontier D := by
  -- Proposition 5.46 already identifies the ambient frontier with the image of the manifold
  -- boundary of `D`.
  exact (mem_frontier_iff_exists_boundaryPoint (I := I) (D := D) (x := p.1)).2 ⟨p, hp, rfl⟩

/-- Helper for Theorem 5.48: a point of `D` outside the ambient frontier is not a boundary point of
the regular-domain structure. -/
lemma not_boundaryPoint_of_mem_diff_frontier
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    {p : D} (hp : p.1 ∈ D \ frontier D) :
    ¬ (leeBoundaryModelWithCorners dimM).IsBoundaryPoint p := by
  -- The previous lemma turns any boundary point into an ambient frontier point, which contradicts
  -- the hypothesis.
  intro hpBoundary
  exact hp.2 (boundaryPoint_mem_frontier (I := I) hpBoundary)

/-- Helper for Theorem 5.48: for the codimension-`0` immersion coming from the subtype inclusion of
a regular domain, the complementary factor in the pointwise immersion normal form is trivial. -/
lemma immersionComplement_subsingleton_of_equalFinrank
    {n : ℕ} {D : Set M} [SmoothManifoldWithBoundary (n + 1) D]
    (hn : dimM = n + 1)
    {p : D} (hImm : Manifold.IsImmersionAt (𝓡∂ (n + 1)) I ∞ (Subtype.val : D → M) p) :
    Subsingleton hImm.complement := by
  -- Repeat the linear-algebra argument directly for the boundary-model source: the immersion chart
  -- identifies `E` with the product of the `(n + 1)`-dimensional source model and the complement.
  let L := hImm.equiv.toContinuousLinearMap
  have hinj_comp :
      Function.Injective
        ((L.comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin (n + 1))) hImm.complement)).toLinearMap) := by
    intro x y hxy
    have hxy' :
        ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin (n + 1))) hImm.complement x =
          ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin (n + 1))) hImm.complement y :=
      hImm.equiv.injective hxy
    simpa using congrArg Prod.snd hxy'
  letI : FiniteDimensional ℝ hImm.complement :=
    FiniteDimensional.of_injective
      ((L.comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin (n + 1))) hImm.complement)).toLinearMap)
      hinj_comp
  have hdim :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = Module.finrank ℝ E := by
    calc
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by simp
      _ = Module.finrank ℝ E := by simpa using hn.symm
  have hprod :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)) × hImm.complement) =
        Module.finrank ℝ E := by
    let e :
        (EuclideanSpace ℝ (Fin (n + 1)) × hImm.complement) ≃ₗ[ℝ] E :=
      hImm.equiv.toLinearEquiv
    simpa [e] using e.finrank_eq
  have hzero : Module.finrank ℝ hImm.complement = 0 := by
    rw [Module.finrank_prod, hdim] at hprod
    omega
  exact (Module.finrank_zero_iff).1 hzero

/-- Helper for Theorem 5.48: the source chart domain in the boundary local normal form is exactly
the subtype preimage of an ambient open patch. -/
lemma boundaryLocalNormalForm_source_eq_subtypePatch
    {D : Set M} {n : ℕ} [SmoothManifoldWithBoundary (n + 1) D]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M]
    {p : D}
    (hNF :
      BoundaryLocalCoordinateNormalFormAt
        (Subtype.val : D → M) p
        (boundary_immersion_normal_form (n + 1) (n + 1))) :
    ∃ W : Set M, IsOpen W ∧ p.1 ∈ W ∧ hNF.domChart.source = {y : D | y.1 ∈ W} := by
  rcases (IsInducing.subtypeVal.isOpen_iff).1 hNF.domChart.open_source with
    ⟨W, hWOpen, hWSource⟩
  refine ⟨W, hWOpen, ?_, ?_⟩
  · -- The centered source point lies in the ambient patch because the source chart domain is its
    -- subtype preimage.
    have hpSource : p ∈ hNF.domChart.source := hNF.domChart_centered.1
    have hpPatch : p ∈ Subtype.val ⁻¹' W := by
      rw [hWSource]
      exact hpSource
    exact hpPatch
  · -- Rewrite the source chart domain from a subtype preimage to the explicit ambient-patch form.
    ext y
    constructor
    · intro hy
      have hyPatch : y ∈ Subtype.val ⁻¹' W := by
        rw [hWSource]
        exact hy
      exact hyPatch
    · intro hy
      rw [← hWSource]
      exact hy

/-- Helper for Theorem 5.48: the half-space target of the source chart is an ambient open patch
cut out by nonnegativity of the first coordinate. -/
lemma boundaryLocalNormalForm_targetImage_eq_firstCoordPatch
    {D : Set M} {n : ℕ} [SmoothManifoldWithBoundary (n + 1) D]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M]
    {p : D}
    (hNF :
      BoundaryLocalCoordinateNormalFormAt
        (Subtype.val : D → M) p
        (boundary_immersion_normal_form (n + 1) (n + 1))) :
    ∃ V : Set (EuclideanSpace ℝ (Fin (n + 1))),
      IsOpen V ∧
        ((fun z : EuclideanHalfSpace (n + 1) ↦ z.1) '' hNF.domChart.target) =
          {z | z ∈ V ∧ 0 ≤ z 0} := by
  rcases
      (IsInducing.subtypeVal.image_eq_isOpen_inter_range hNF.domChart.open_target) with
    ⟨V, hVOpen, hVImage⟩
  refine ⟨V, hVOpen, ?_⟩
  -- The half-space target is an ambient-open set intersected with the half-space range.
  calc
    Subtype.val '' hNF.domChart.target =
        V ∩ Set.range (Subtype.val : EuclideanHalfSpace (n + 1) →
          EuclideanSpace ℝ (Fin (n + 1))) := hVImage
    _ = {z | z ∈ V ∧ 0 ≤ z 0} := by
      rw [range_euclideanHalfSpace]
      ext z
      simp

/-- Helper for Theorem 5.48: once the boundary local normal form is restricted to an ambient open
patch matching the domain-chart source, its source image is exactly the corresponding ambient
intersection patch. -/
lemma restrictedBoundaryLocalNormalForm_source_image_eq_restrictedPatch
    {D : Set M} {n : ℕ} [SmoothManifoldWithBoundary (n + 1) D]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M]
    {p : D}
    (hNF :
      BoundaryLocalCoordinateNormalFormAt
        (Subtype.val : D → M) p
        (boundary_immersion_normal_form (n + 1) (n + 1)))
    {W : Set M} (hW_open : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : D | y.1 ∈ W}) :
    Subtype.val '' hNF.domChart.source = D ∩ (hNF.codChart.restr W).source := by
  -- Normalize the restricted ambient source to `W`, and recover codomain-source membership from
  -- the local normal form instead of assuming a global inclusion `W ⊆ codChart.source`.
  apply Set.ext
  intro y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzW : z.1 ∈ W := by
      simpa [hW_eq] using hz
    have hzCod : z.1 ∈ hNF.codChart.source := by
      exact BoundaryLocalCoordinateNormalFormAt.mapsTo_source hNF hz
    refine ⟨z.2, ?_⟩
    rw [hNF.codChart.restr_source' W hW_open]
    exact ⟨hzCod, hzW⟩
  · rintro ⟨hyD, hyRestr⟩
    rw [hNF.codChart.restr_source' W hW_open] at hyRestr
    let yD : D := ⟨y, hyD⟩
    have hyDom : yD ∈ hNF.domChart.source := by
      simpa [hW_eq, yD] using hyRestr.2
    exact ⟨yD, hyDom, rfl⟩

/-- Helper for Theorem 5.48: on the restricted ambient patch coming from the boundary local normal
form, points of the regular domain land in the nonnegative side of the first coordinate. -/
lemma restrictedBoundaryLocalNormalForm_nonneg_firstCoord_of_mem
    {D : Set M} {n : ℕ} [SmoothManifoldWithBoundary (n + 1) D]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M]
    {p : D}
    (hNF :
      BoundaryLocalCoordinateNormalFormAt
        (Subtype.val : D → M) p
        (boundary_immersion_normal_form (n + 1) (n + 1)))
    {W : Set M} (hW_open : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : D | y.1 ∈ W})
    {y : M} (hyD : y ∈ D) (hy : y ∈ (hNF.codChart.restr W).source) :
    0 ≤ (hNF.codChart.restr W) y 0 := by
  -- First move the ambient point back to the source chart of the normal form.
  have hyImage : y ∈ Subtype.val '' hNF.domChart.source := by
    rw [restrictedBoundaryLocalNormalForm_source_image_eq_restrictedPatch
      hNF hW_open hW_eq]
    exact ⟨hyD, hy⟩
  rcases hyImage with ⟨yD, hyDom, rfl⟩
  have hyTarget : hNF.domChart yD ∈ hNF.domChart.target :=
    hNF.domChart.map_source hyDom
  have hyLeftInv : hNF.domChart.symm (hNF.domChart yD) = yD := by
    exact hNF.domChart.left_inv hyDom
  have hcoord :
      (hNF.codChart.restr W) yD.1 =
        boundary_immersion_normal_form (n + 1) (n + 1) (hNF.domChart yD) := by
    -- On the domain patch, the restricted ambient chart is written by the inclusion normal form.
    simpa [hyLeftInv, Function.comp] using hNF.eqOn hyTarget
  have hnonneg : 0 ≤ (hNF.domChart yD).1 0 := (hNF.domChart yD).2
  -- The full-rank boundary normal form simply forgets the half-space proof, so the first
  -- coordinate stays nonnegative.
  simpa [hcoord, boundaryImmersionNormalForm_self] using hnonneg

/-- Helper for Theorem 5.48: in any smooth boundary chart, a boundary point has vanishing first
coordinate in chart coordinates. -/
lemma boundaryChart_zero_firstCoord_of_boundaryPoint
    {n : ℕ} {N : Type*} [TopologicalSpace N] [SmoothManifoldWithBoundary (n + 1) N]
    {e : OpenPartialHomeomorph N (EuclideanHalfSpace (n + 1))} {y : N}
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ (n + 1)) (⊤ : WithTop ℕ∞) N)
    (hySource : y ∈ e.source) (hyBoundary : (𝓡∂ (n + 1)).IsBoundaryPoint y) :
    (e y).1 0 = 0 := by
  have hyTarget : e y ∈ e.target := e.map_source hySource
  by_contra hzero
  have hpos : 0 < (e y).1 0 := by
    exact lt_of_le_of_ne (e y).2 (Ne.symm hzero)
  have hyChartInterior :
      e.extend (𝓡∂ (n + 1)) y ∈ interior (e.extend (𝓡∂ (n + 1))).target := by
    -- A positive first coordinate puts the chart image in the interior half-space.
    have hNeighborhood :
        ∃ V₀ : Set (EuclideanSpace ℝ (Fin (n + 1))),
          IsOpen V₀ ∧ (e y).1 ∈ V₀ ∧ ((𝓡∂ (n + 1)) ⁻¹' V₀) ⊆ e.target :=
      open_halfSpace_neighborhood_of_open_subtype_set e.open_target hyTarget
    rcases hNeighborhood with
      ⟨V₀, hV₀Open, hyV₀, hV₀Target⟩
    let V : Set (EuclideanSpace ℝ (Fin (n + 1))) := V₀ ∩ {w | 0 < w 0}
    have hVOpen : IsOpen V := by
      exact hV₀Open.inter (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0))
    have hyV : e.extend (𝓡∂ (n + 1)) y ∈ V := by
      exact ⟨hyV₀, hpos⟩
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (hVOpen.mem_nhds hyV) ?_
    intro w hw
    rw [OpenPartialHomeomorph.extend_target']
    refine ⟨⟨w, le_of_lt hw.2⟩, ?_, rfl⟩
    exact hV₀Target <| by simpa using hw.1
  have hyInterior : (𝓡∂ (n + 1)).IsInteriorPoint y := by
    -- Maximal-atlas charts detect interior points through interior chart images.
    exact ((𝓡∂ (n + 1)).isInteriorPoint_iff_of_mem_maximalAtlas
      (by simp) he hySource).2 hyChartInterior
  exact
    ((𝓡∂ (n + 1)).isBoundaryPoint_iff_not_isInteriorPoint y).1 hyBoundary hyInterior

/-- Helper for Theorem 5.48: on the restricted ambient patch coming from the boundary local normal
form, the image of `D` is exactly the first-coordinate half-space inside a normalized ambient
target patch. -/
lemma restrictedBoundaryLocalNormalForm_image_eq_firstCoordPatch
    {D : Set M} {n : ℕ} [SmoothManifoldWithBoundary (n + 1) D]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M]
    {p : D}
    (hNF :
      BoundaryLocalCoordinateNormalFormAt
        (Subtype.val : D → M) p
        (boundary_immersion_normal_form (n + 1) (n + 1)))
    {W : Set M} (hW_open : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : D | y.1 ∈ W}) :
    ∃ V : Set (EuclideanSpace ℝ (Fin (n + 1))), IsOpen V ∧
      (hNF.codChart.restr W) '' (D ∩ (hNF.codChart.restr W).source) = {z | z ∈ V ∧ 0 ≤ z 0} := by
  rcases boundaryLocalNormalForm_targetImage_eq_firstCoordPatch hNF with ⟨V, hV_open, hV_eq⟩
  refine ⟨V, hV_open, ?_⟩
  ext z
  constructor
  · rintro ⟨y, ⟨hyD, hySource⟩, rfl⟩
    have hyImage : y ∈ Subtype.val '' hNF.domChart.source := by
      rw [restrictedBoundaryLocalNormalForm_source_image_eq_restrictedPatch
        hNF hW_open hW_eq]
      exact ⟨hyD, hySource⟩
    rcases hyImage with ⟨yD, hyDom, rfl⟩
    have hyTarget : hNF.domChart yD ∈ hNF.domChart.target :=
      hNF.domChart.map_source hyDom
    have hyLeftInv : hNF.domChart.symm (hNF.domChart yD) = yD := by
      exact hNF.domChart.left_inv hyDom
    have hcoord :
        (hNF.codChart.restr W) yD.1 = (hNF.domChart yD).1 := by
      -- On `D`, the restricted ambient chart is literally the inclusion normal form.
      simpa [hyLeftInv, Function.comp, boundaryImmersionNormalForm_self] using
        hNF.eqOn hyTarget
    have hzPatch : (hNF.domChart yD).1 ∈ {z | z ∈ V ∧ 0 ≤ z 0} := by
      -- The source-chart target was normalized earlier as an ambient open patch intersected with
      -- the Euclidean half-space.
      have hzImage : (hNF.domChart yD).1 ∈ Subtype.val '' hNF.domChart.target := by
        exact ⟨hNF.domChart yD, hyTarget, rfl⟩
      change (hNF.domChart yD).1 ∈ (fun z : EuclideanHalfSpace (n + 1) ↦ z.1) '' hNF.domChart.target at hzImage
      rw [hV_eq] at hzImage
      exact hzImage
    simpa [hcoord] using hzPatch
  · intro hz
    have hzImage : z ∈ Subtype.val '' hNF.domChart.target := by
      -- Rewrite the ambient half-space condition back to the source-chart target image.
      change z ∈ (fun z : EuclideanHalfSpace (n + 1) ↦ z.1) '' hNF.domChart.target
      rw [hV_eq]
      exact hz
    rcases hzImage with ⟨u, huTarget, rfl⟩
    let yD : D := hNF.domChart.symm u
    have hyDom : yD ∈ hNF.domChart.source := by
      exact hNF.domChart.map_target huTarget
    have hyCodSource : yD.1 ∈ hNF.codChart.source := by
      exact BoundaryLocalCoordinateNormalFormAt.mapsTo_source hNF hyDom
    have hyW : yD.1 ∈ W := by
      -- The chosen ambient patch is exactly the subtype image of the source-chart domain.
      simpa [hW_eq, yD] using hyDom
    have hySource : yD.1 ∈ (hNF.codChart.restr W).source := by
      rw [hNF.codChart.restr_source' W hW_open]
      exact ⟨hyCodSource, hyW⟩
    have hyRightInv : hNF.domChart yD = u := by
      exact hNF.domChart.right_inv huTarget
    have hcoord :
        (hNF.codChart.restr W) yD.1 = u.1 := by
      -- Pulling the half-space witness back through `domChart.symm` gives the required ambient
      -- point of `D`.
      simpa [yD, hyRightInv, Function.comp, boundaryImmersionNormalForm_self] using
        hNF.eqOn huTarget
    refine ⟨yD.1, ⟨yD.2, hySource⟩, ?_⟩
    simpa [hcoord]

/-- Helper for Theorem 5.48: on a normalized restricted ambient patch, nonnegativity of the first
coordinate forces membership in the regular domain. -/
lemma restrictedBoundaryLocalNormalForm_mem_of_nonneg_firstCoord
    {D : Set M} {n : ℕ} [SmoothManifoldWithBoundary (n + 1) D]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M]
    {p : D}
    (hNF :
      BoundaryLocalCoordinateNormalFormAt
        (Subtype.val : D → M) p
        (boundary_immersion_normal_form (n + 1) (n + 1)))
    {W : Set M} (hW_open : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : D | y.1 ∈ W})
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV_eq :
      (hNF.codChart.restr W) '' (D ∩ (hNF.codChart.restr W).source) = {z | z ∈ V ∧ 0 ≤ z 0})
    {y : M} (hy : y ∈ (hNF.codChart.restr W).source)
    (hyV : (hNF.codChart.restr W) y ∈ V)
    (hyNonneg : 0 ≤ (hNF.codChart.restr W) y 0) :
    y ∈ D := by
  have hyImage : (hNF.codChart.restr W) y ∈
      (hNF.codChart.restr W) '' (D ∩ (hNF.codChart.restr W).source) := by
    -- The normalized half-space image theorem packages the needed converse witness.
    rw [hV_eq]
    exact ⟨hyV, hyNonneg⟩
  rcases hyImage with ⟨z, ⟨hzD, hzSource⟩, hzy⟩
  -- Injectivity of the restricted ambient chart on its source identifies the witness point with `y`.
  exact (hNF.codChart.restr W).injOn hzSource hy hzy ▸ hzD

/-- Helper for Theorem 5.48: on the normalized restricted ambient patch, membership in the regular
domain is equivalent to nonpositivity of the signed first coordinate. -/
lemma restrictedBoundaryLocalNormalForm_mem_iff_signedCoord_nonpos
    {D : Set M} {n : ℕ} [SmoothManifoldWithBoundary (n + 1) D]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M]
    {p : D}
    (hNF :
      BoundaryLocalCoordinateNormalFormAt
        (Subtype.val : D → M) p
        (boundary_immersion_normal_form (n + 1) (n + 1)))
    {W : Set M} (hW_open : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : D | y.1 ∈ W})
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV_eq :
      (hNF.codChart.restr W) '' (D ∩ (hNF.codChart.restr W).source) = {z | z ∈ V ∧ 0 ≤ z 0})
    {y : M} (hy : y ∈ (hNF.codChart.restr W).source)
    (hyV : (hNF.codChart.restr W) y ∈ V) :
    y ∈ D ↔ -((hNF.codChart.restr W) y 0) ≤ 0 := by
  constructor
  · intro hyD
    -- Membership in `D` gives nonnegativity of the first coordinate, hence nonpositivity of its
    -- negative.
    have hyNonneg :
        0 ≤ (hNF.codChart.restr W) y 0 :=
      restrictedBoundaryLocalNormalForm_nonneg_firstCoord_of_mem
        hNF hW_open hW_eq hyD hy
    linarith
  · intro hySigned
    -- Conversely, the signed inequality is just first-coordinate nonnegativity on the same patch.
    have hyNonneg :
        0 ≤ (hNF.codChart.restr W) y 0 := by
      linarith
    exact restrictedBoundaryLocalNormalForm_mem_of_nonneg_firstCoord
      hNF hW_open hW_eq hV_eq hy hyV hyNonneg

/-- Helper for Theorem 5.48: on the restricted ambient normal-form patch, frontier points of the
regular domain map to first coordinate `0`. -/
lemma restrictedBoundaryLocalNormalForm_zero_firstCoord_of_frontier
    {D : Set M} {n : ℕ} [SmoothManifoldWithBoundary dimM D]
    [SmoothManifoldWithBoundary (n + 1) D] [Set.IsRegularDomain I D] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M]
    {p : D}
    (hNF :
      BoundaryLocalCoordinateNormalFormAt
        (Subtype.val : D → M) p
        (boundary_immersion_normal_form (n + 1) (n + 1)))
    {W : Set M} (hW_open : IsOpen W)
    (hW_eq : hNF.domChart.source = {y : D | y.1 ∈ W})
    {y : M} (hyFrontier : y ∈ frontier D) (hy : y ∈ (hNF.codChart.restr W).source) :
    (hNF.codChart.restr W) y 0 = 0 := by
  have hDClosed : IsClosed D := regularDomain_isClosed I
  have hyD : y ∈ D := by
    -- A frontier point of a closed regular domain still lies in the domain itself.
    simpa [hDClosed.closure_eq] using hyFrontier.1
  rcases restrictedBoundaryLocalNormalForm_image_eq_firstCoordPatch
      hNF hW_open hW_eq with ⟨V, hV_open, hV_eq⟩
  have hyV : (hNF.codChart.restr W) y ∈ V := by
    have hyImage : (hNF.codChart.restr W) y ∈
        (hNF.codChart.restr W) '' (D ∩ (hNF.codChart.restr W).source) := by
      exact ⟨y, ⟨hyD, hy⟩, rfl⟩
    rw [hV_eq] at hyImage
    exact hyImage.1
  have hyNonneg : 0 ≤ (hNF.codChart.restr W) y 0 :=
    restrictedBoundaryLocalNormalForm_nonneg_firstCoord_of_mem
      hNF hW_open hW_eq hyD hy
  have hyNotPos : ¬ 0 < (hNF.codChart.restr W) y 0 := by
    intro hyPos
    let S : Set (EuclideanSpace ℝ (Fin (n + 1))) := V ∩ {z | 0 < z 0}
    have hS_open : IsOpen S := by
      -- The normalized target patch stays open after requiring strict positivity of the first
      -- coordinate.
      exact hV_open.inter (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0))
    have hS_subset_target : S ⊆ (hNF.codChart.restr W).target := by
      intro z hzS
      have hzImage : z ∈ (hNF.codChart.restr W) '' (D ∩ (hNF.codChart.restr W).source) := by
        rw [hV_eq]
        exact ⟨hzS.1, le_of_lt hzS.2⟩
      rcases hzImage with ⟨x, ⟨_hxD, hxSource⟩, rfl⟩
      exact (hNF.codChart.restr W).map_source hxSource
    let U : Set M := (hNF.codChart.restr W).symm '' S
    have hU_open : IsOpen U := by
      -- Pull the positive-coordinate target patch back through the restricted ambient chart.
      exact (hNF.codChart.restr W).isOpen_image_symm_of_subset_target hS_open hS_subset_target
    have hyU : y ∈ U := by
      refine ⟨(hNF.codChart.restr W) y, ⟨hyV, hyPos⟩, ?_⟩
      exact (hNF.codChart.restr W).left_inv hy
    have hU_subset_D : U ⊆ D := by
      intro z hzU
      rcases hzU with ⟨w, hwS, rfl⟩
      have hwTarget : w ∈ (hNF.codChart.restr W).target := hS_subset_target hwS
      have hzSource : (hNF.codChart.restr W).symm w ∈ (hNF.codChart.restr W).source :=
        (hNF.codChart.restr W).map_target hwTarget
      have hwCoord :
          (hNF.codChart.restr W) ((hNF.codChart.restr W).symm w) = w :=
        (hNF.codChart.restr W).right_inv hwTarget
      have hwV :
          (hNF.codChart.restr W) ((hNF.codChart.restr W).symm w) ∈ V := by
        rw [hwCoord]
        exact hwS.1
      have hwNonneg :
          0 ≤ (hNF.codChart.restr W) ((hNF.codChart.restr W).symm w) 0 := by
        rw [hwCoord]
        exact le_of_lt hwS.2
      -- On the normalized target patch, nonnegative first coordinate forces membership in `D`.
      exact restrictedBoundaryLocalNormalForm_mem_of_nonneg_firstCoord
        hNF hW_open hW_eq hV_eq hzSource hwV hwNonneg
    have hyInterior : y ∈ interior D := by
      -- The positive-coordinate patch gives an ambient open neighborhood of `y` contained in `D`.
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (hU_open.mem_nhds hyU) hU_subset_D
    exact hyFrontier.2 hyInterior
  exact le_antisymm (le_of_not_gt hyNotPos) hyNonneg

/-- Helper for Theorem 5.48: the fixed Euclidean coordinate swap sends the last coordinate to
slot `0`. -/
lemma swapZeroLastLinearIsometryApplyZero
    (n : ℕ) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.swap 0 (Fin.last n)) z) 0 = z (Fin.last n) := by
  -- The permutation linear isometry acts by precomposing with the chosen swap on `Fin (n + 1)`.
  simp

/-- Helper for Theorem 5.48: the same Euclidean coordinate swap sends slot `0` to the last
coordinate. -/
lemma swapZeroLastLinearIsometryApplyLast
    (n : ℕ) (z : EuclideanSpace ℝ (Fin (n + 1))) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Equiv.swap 0 (Fin.last n)) z) (Fin.last n) = z 0 := by
  -- This is the inverse coordinate identity for the same global permutation chart.
  simp

/-- Helper for Theorem 5.48: lowering the differentiability index preserves immersions by reusing
the same chart normal forms. -/
lemma isImmersion_of_le
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    {I₁ : ModelWithCorners 𝕜 E₁ H₁} [IsManifold I₁ (⊤ : WithTop ℕ∞) M₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {H₂ : Type*} [TopologicalSpace H₂]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    {I₂ : ModelWithCorners 𝕜 E₂ H₂} [IsManifold I₂ (⊤ : WithTop ℕ∞) M₂]
    {n m : WithTop ℕ∞} {f : M₁ → M₂} (hmn : m ≤ n)
    (hf : Manifold.IsImmersion I₁ I₂ n f) :
    Manifold.IsImmersion I₁ I₂ m f := by
  -- Keep the same complement and local chart presentation, lowering only the atlas regularity.
  let hComp := hf.complement
  let hCompImm := hf.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I₁) (M := M₁) hmn) hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I₂) (M := M₂) hmn) hx.codChart_mem_maximalAtlas

/-- Helper for Theorem 5.48: after installing the Euclidean ambient atlas, the identity map is a
local diffeomorphism from the original ambient owner into the Euclidean owner. -/
lemma ambientId_isLocalDiffeomorph_toAmbientBasis
    {n : ℕ}
    (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      ambientBasisChartedSpace I hn b
    let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
      ambientBasisIsManifold I hn b
    IsLocalDiffeomorph I (𝓡 (n + 1)) ∞ (id : M → M) := by
  let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
  let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
    (boundarylessModelIsManifoldFor I :
      let _ : ChartedSpace E M := (boundarylessChartedSpaceFor I : ChartedSpace E M)
      IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    ambientBasisChartedSpace I hn b
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold I hn b
  change IsLocalDiffeomorph I (𝓡 (n + 1)) ∞ (id : M → M)
  have hdim :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = Module.finrank ℝ E := by
    -- The Euclideanized ambient atlas has the same dimension as the original ambient model.
    calc
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := by simp
      _ = dimM := by simpa using hn.symm
      _ = Module.finrank ℝ E := rfl
  have hForward :
      IsLocalDiffeomorph (𝓡 (n + 1)) I ∞ (id : M → M) := by
    let hAmbientIdTop :=
      ambientBasisAmbientId_isSmoothEmbedding (I := I) (M := M) hn b
    have hAmbientIdInf :
        Manifold.IsSmoothEmbedding (𝓡 (n + 1)) I ∞ (id : M → M) :=
      ⟨isImmersion_of_le (m := (∞ : WithTop ℕ∞)) (n := (⊤ : WithTop ℕ∞)) (by simp)
          hAmbientIdTop.isImmersion, hAmbientIdTop.isEmbedding⟩
    -- Route correction: first prove the forward Euclidean-to-ambient identity is a local
    -- diffeomorphism, then flip its local branches to read the reverse identity map.
    exact hAmbientIdInf.isImmersion.isLocalDiffeomorph_of_eq_finrank hdim
  intro x
  let hx := hForward x
  refine ⟨hx.localInverse, hx.localInverse_mem_source, ?_⟩
  -- The local inverse of the forward identity branch is again the identity on its source patch.
  intro y hy
  simpa [Function.comp] using (hx.localInverse_eqOn_right hy).symm

/-- Helper for Theorem 5.48: after installing the Euclidean ambient atlas, the identity map is an
immersion from the original ambient owner into the Euclidean owner. -/
lemma ambientId_isImmersion_toAmbientBasis
    {n : ℕ}
    (hn : dimM = n + 1) (b : Module.Basis (Fin (n + 1)) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      ambientBasisChartedSpace I hn b
    let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
      ambientBasisIsManifold I hn b
    Manifold.IsImmersion I (𝓡 (n + 1)) ∞ (id : M → M) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    ambientBasisChartedSpace I hn b
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold I hn b
  change Manifold.IsImmersion I (𝓡 (n + 1)) ∞ (id : M → M)
  -- The local-diffeomorphism bridge immediately yields the desired immersion.
  exact (ambientId_isLocalDiffeomorph_toAmbientBasis (I := I) (M := M) hn b).isImmersion

/-- Helper for Theorem 5.48: once the Euclidean ambient immersion of the subtype inclusion is
available, any boundary point of `D` has the Euclidean boundary normal form from Theorem 4.15. -/
lemma boundaryPoint_hasEuclideanBoundaryLocalNormalForm_of_immersion
    {D : Set M} {n : ℕ} [SmoothManifoldWithBoundary (n + 1) D]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M]
    (hImm :
      Manifold.IsImmersion (𝓡∂ (n + 1)) (𝓡 (n + 1))
        ∞ (Subtype.val : D → M))
    {p : D} (hpBoundary : (𝓡∂ (n + 1)).IsBoundaryPoint p) :
    ∃ hNF :
      BoundaryLocalCoordinateNormalFormAt
        (Subtype.val : D → M) p
        (boundary_immersion_normal_form (n + 1) (n + 1)),
      True := by
  have hpMemBoundary : p ∈ (𝓡∂ (n + 1)).boundary D := by
    simpa [ModelWithCorners.boundary] using hpBoundary
  -- Theorem 4.15 now applies directly at the boundary point `p`.
  exact smooth_immersion_boundary_local_inclusion_form hImm hpMemBoundary

/-- Helper for Theorem 5.48: after rewriting the regular-domain subtype immersion into successor
form, the reverse ambient identity immersion transports it to the Euclidean ambient owner. -/
lemma regularDomainSubtypeVal_isImmersion_toAmbientBasis
    {D : Set M} {n : ℕ} [hOld : SmoothManifoldWithBoundary dimM D]
    [hSucc : SmoothManifoldWithBoundary (n + 1) D] [Set.IsRegularDomain I D]
    (hn : dimM = n + 1)
    (hSucc_eq : hSucc = by simpa [hn] using hOld)
    (b : Module.Basis (Fin (n + 1)) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      ambientBasisChartedSpace I hn b
    let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
      ambientBasisIsManifold I hn b
    Manifold.IsImmersion
      (𝓡∂ (n + 1))
      (𝓡 (n + 1))
      ∞
      (Subtype.val : D → M) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    ambientBasisChartedSpace I hn b
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold I hn b
  have hSubtypeImm :
      Manifold.IsImmersion
        (𝓡∂ (n + 1))
        I
        ∞
        (Subtype.val : D → M) := by
    have hSubtypeImm0 :
        Manifold.IsImmersion
          (leeBoundaryModelWithCorners dimM)
          I
          ∞
          (Subtype.val : D → M) :=
      (regularDomainSubtypeVal_isSmoothEmbedding_infty (I := I) (D := D)).isImmersion
    -- Rewrite the regular-domain embedding once into successor-form boundary coordinates.
    exact (leeBoundaryModelWithCorners_isImmersion_iff_succ
      (I := I) (D := D) (n := n) hn hSucc_eq).1 hSubtypeImm0
  -- Compose the subtype immersion with the ambient identity immersion into the Euclideanized
  -- atlas.
  simpa [Function.comp] using
    Manifold.IsImmersion.ex416_comp
      (ambientId_isImmersion_toAmbientBasis (I := I) hn b)
      hSubtypeImm

/-- Helper for Theorem 5.48: after Theorem 4.15 is available at a boundary point, the source
chart can be normalized to an ambient open patch of `M`, which is the exact source-side owner
consumed by the restricted first-coordinate patch lemmas proved above. -/
lemma boundaryPoint_hasBoundarySourcePatch_of_immersion
    {D : Set M} {n : ℕ} [SmoothManifoldWithBoundary (n + 1) D]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M]
    (hImm :
      Manifold.IsImmersion (𝓡∂ (n + 1)) (𝓡 (n + 1))
        ∞ (Subtype.val : D → M))
    {p : D} (hpBoundary : (𝓡∂ (n + 1)).IsBoundaryPoint p) :
    ∃ hNF :
      BoundaryLocalCoordinateNormalFormAt
        (Subtype.val : D → M) p
        (boundary_immersion_normal_form (n + 1) (n + 1)),
      ∃ W : Set M, IsOpen W ∧ p.1 ∈ W ∧ hNF.domChart.source = {y : D | y.1 ∈ W} := by
  rcases boundaryPoint_hasEuclideanBoundaryLocalNormalForm_of_immersion
      (D := D) (n := n) hImm hpBoundary with ⟨hNF, _⟩
  rcases boundaryLocalNormalForm_source_eq_subtypePatch hNF with ⟨W, hWOpen, hpW, hW_eq⟩
  -- This packages the normal-form source chart in the ambient-open form used later by the
  -- restricted ambient patch arguments.
  exact ⟨hNF, W, hWOpen, hpW, hW_eq⟩

/-- Helper for Theorem 5.48: every ambient frontier point lifts to a boundary point of `D`
together with the Euclidean source patch needed for the remaining local signed-function work. -/
lemma frontierPoint_hasBoundarySourcePatch
    {D : Set M} {n : ℕ} [hOld : SmoothManifoldWithBoundary dimM D]
    [hSucc : SmoothManifoldWithBoundary (n + 1) D] [Set.IsRegularDomain I D]
    (hn : dimM = n + 1)
    (hSucc_eq : hSucc = by simpa [hn] using hOld)
    (b : Module.Basis (Fin (n + 1)) ℝ E)
    {y : M} (hyFrontier : y ∈ frontier D) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      ambientBasisChartedSpace I hn b
    let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
      ambientBasisIsManifold I hn b
    ∃ p : D,
      p.1 = y ∧
        ∃ hNF :
          BoundaryLocalCoordinateNormalFormAt
            (Subtype.val : D → M) p
            (boundary_immersion_normal_form (n + 1) (n + 1)),
          ∃ W : Set M, IsOpen W ∧ y ∈ W ∧ hNF.domChart.source = {z : D | z.1 ∈ W} := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    ambientBasisChartedSpace I hn b
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold I hn b
  rcases (mem_frontier_iff_exists_boundaryPoint (I := I) (D := D) (x := y)).1 hyFrontier with
    ⟨p, hpBoundary, hpy⟩
  have hpBoundary' : (𝓡∂ (n + 1)).IsBoundaryPoint p := by
    have hpBoundary0 : (leeBoundaryModelWithCorners dimM).IsBoundaryPoint p := hpBoundary
    -- Rewrite the boundary witness into the successor-form source owner used by Theorem 4.15.
    exact (leeBoundaryModelWithCorners_isBoundaryPoint_iff_succ
      (D := D) (n := n) hn hSucc_eq).1 hpBoundary0
  rcases boundaryPoint_hasBoundarySourcePatch_of_immersion
      (D := D) (n := n)
      (regularDomainSubtypeVal_isImmersion_toAmbientBasis
        (I := I) (D := D) hn hSucc_eq b)
      hpBoundary' with
    ⟨hNF, W, hWOpen, hpW, hW_eq⟩
  -- The frontier witness already identifies the subtype point with the ambient frontier point.
  exact ⟨p, hpy, hNF, W, hWOpen, by simpa [hpy] using hpW, hW_eq⟩

/-- Helper for Theorem 5.48: every boundary point of the successor half-space owner admits an
outward-pointing tangent vector, obtained by pulling back the model vector with negative first
coordinate through the preferred chart at that point. -/
lemma boundaryPoint_existsOutwardVector
    {D : Set M} {n : ℕ} [SmoothManifoldWithBoundary (n + 1) D] {p : D}
    (hp : p ∈ (𝓡∂ (n + 1)).boundary D) :
    ∃ v : TangentSpace (𝓡∂ (n + 1)) p, IsOutwardPointing p v := by
  let modelVec : EuclideanSpace ℝ (Fin (n + 1)) :=
    EuclideanSpace.single 0 (-1 : ℝ)
  let u :
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (extChartAt (𝓡∂ (n + 1)) p p) :=
    (NormedSpace.fromTangentSpace (extChartAt (𝓡∂ (n + 1)) p p)).symm modelVec
  obtain ⟨v, hv⟩ :=
    (isInvertible_mfderiv_extChartAt
      (I := 𝓡∂ (n + 1)) (x := p) (y := p) (mem_extChartAt_source p)).surjective u
  refine ⟨v, ?_⟩
  have hcoord :
      boundary_coordinate_component (chartAt (EuclideanHalfSpace (n + 1)) p) p v < 0 := by
    -- The chart derivative was chosen to hit the model vector with first coordinate `-1`.
    have hcoordEq :
        boundary_coordinate_component (chartAt (EuclideanHalfSpace (n + 1)) p) p v = -1 := by
      simpa [boundary_coordinate_component, modelVec, u, extChartAt]
        using congrArg
          (fun z ↦
            (NormedSpace.fromTangentSpace (extChartAt (𝓡∂ (n + 1)) p p) z) 0)
          hv
    linarith
  -- Proposition 5.41 upgrades the negative boundary coordinate into an outward-pointing vector.
  exact
    (outward_pointing_iff_boundary_coordinate_component_neg
      (p := p) hp (chart_mem_atlas (EuclideanHalfSpace (n + 1)) p)
      (mem_chart_source (EuclideanHalfSpace (n + 1)) p)).2 hcoord

/-- Helper for Theorem 5.48: once the restriction `z ↦ -ρ z.1` is boundary-defining on the source
regular-domain manifold, the ambient derivative of `ρ` at the same point is a nonzero real linear
map, hence surjective. -/
lemma boundaryDefiningAt_surjectiveAmbientMfderiv
    {D : Set M} {n : ℕ} [hOld : SmoothManifoldWithBoundary dimM D]
    [hSucc : SmoothManifoldWithBoundary (n + 1) D] [Set.IsRegularDomain I D]
    (hn : dimM = n + 1)
    (hSucc_eq : hSucc = by simpa [hn] using hOld)
    {ρ : M → ℝ} (hρSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ)
    {xD : D}
    (hbd :
      IsBoundaryDefiningFunctionAt (M := D) (n := n + 1) xD (fun z : D ↦ -ρ z.1)) :
    Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) ρ xD.1) := by
  obtain ⟨v, hvOut⟩ := boundaryPoint_existsOutwardVector (D := D) (n := n) hbd.1
  have hneg :
      boundary_defining_derivative (fun z : D ↦ -ρ z.1) v < 0 :=
    (outwardPointing_iff_boundaryDefiningDerivative_neg hbd v).1 hvOut
  have hImmOld :
      Manifold.IsImmersion (leeBoundaryModelWithCorners dimM) I ∞ (Subtype.val : D → M) :=
    (regularDomainSubtypeVal_isSmoothEmbedding_infty (I := I) (D := D)).isImmersion
  have hImmNew :
      Manifold.IsImmersion (𝓡∂ (n + 1)) I ∞ (Subtype.val : D → M) := by
    exact (leeBoundaryModelWithCorners_isImmersion_iff_succ
      (I := I) (D := D) (n := n) hn hSucc_eq).1 hImmOld
  have hValMDiff : MDifferentiableAt (𝓡∂ (n + 1)) I (Subtype.val : D → M) xD := by
    have hValSmooth : ContMDiff (𝓡∂ (n + 1)) I ∞ (Subtype.val : D → M) := hImmNew.contMDiff
    exact hValSmooth.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hρMDiff : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ xD.1 := by
    exact hρSmooth.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hAmbientNonzero : (mfderiv I 𝓘(ℝ, ℝ) ρ xD.1 : TangentSpace I xD.1 →L[ℝ] ℝ) ≠ 0 := by
    intro hzero
    have hcomp :
        mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (fun z : D ↦ ρ z.1) xD =
          (mfderiv I 𝓘(ℝ, ℝ) ρ xD.1).comp
            (mfderiv (𝓡∂ (n + 1)) I (Subtype.val : D → M) xD) := by
      -- The derivative of the restriction is exactly the ambient derivative after the subtype map.
      simpa [Function.comp] using
        (mfderiv_comp (x := xD) (g := ρ) (f := (Subtype.val : D → M)) hρMDiff hValMDiff)
    have hcompZero :
        mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (fun z : D ↦ ρ z.1) xD = 0 := by
      -- Chain the derivative through the subtype inclusion and collapse the zero ambient map.
      rw [hcomp, hzero, ContinuousLinearMap.zero_comp]
    have hnegDerivZero :
        mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (fun z : D ↦ -ρ z.1) xD = 0 := by
      -- Negating the restricted function only negates its derivative, so the zero derivative is stable.
      calc
        mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (fun z : D ↦ -ρ z.1) xD
            = -mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) (fun z : D ↦ ρ z.1) xD := by
              simpa using (mfderiv_neg (fun z : D ↦ ρ z.1) xD)
        _ = 0 := by
          rw [hcompZero]
          simp
    have hzeroBoundary :
        boundary_defining_derivative (fun z : D ↦ -ρ z.1) v = 0 := by
      -- If the ambient derivative vanished, then the boundary-defining derivative would vanish too.
      have hxZero : (fun z : D ↦ -ρ z.1) xD = 0 := by
        simpa using hbd.eq_zero
      unfold boundary_defining_derivative
      rw [hxZero, hnegDerivZero]
      rfl
    linarith
  let L : TangentSpace I xD.1 →L[ℝ] ℝ :=
    (NormedSpace.fromTangentSpace (ρ xD.1)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ, ℝ) ρ xD.1)
  have hLnonzero : L ≠ 0 := by
    intro hLzero
    apply hAmbientNonzero
    ext v
    apply (NormedSpace.fromTangentSpace (ρ xD.1)).injective
    have hv := congrArg (fun T : TangentSpace I xD.1 →L[ℝ] ℝ => T v) hLzero
    simpa [L] using hv
  have hLExists : ∃ a : TangentSpace I xD.1, L a ≠ 0 := by
    by_contra hNo
    apply hLnonzero
    ext a
    by_contra ha
    exact hNo ⟨a, ha⟩
  intro y
  let y' : ℝ := NormedSpace.fromTangentSpace (ρ xD.1) y
  rcases hLExists with ⟨a, ha⟩
  have ha' : ∃ b : TangentSpace I xD.1, L b = y' := by
    refine ⟨(y' / L a) • a, ?_⟩
    rw [ContinuousLinearMap.map_smul]
    have hmul : (y' / L a) * L a = y' := by
      field_simp [ha]
    simpa [smul_eq_mul] using hmul
  rcases ha' with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  apply (NormedSpace.fromTangentSpace (ρ xD.1)).injective
  simpa [L, y'] using ha

/-- Helper for Theorem 5.48: the preferred linear identification `ℝ ≃ ℝ¹`. -/
private noncomputable def realToR1Equiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- Helper for Theorem 5.48: the chosen map from `ℝ` into `ℝ¹`. -/
private noncomputable def realToR1 : ℝ → EuclideanSpace ℝ (Fin 1) :=
  realToR1Equiv

/-- Helper for Theorem 5.48: the unique coordinate of the preferred `ℝ¹` point recovers the
original scalar. -/
private theorem realToR1_apply_zero (t : ℝ) :
    realToR1 t 0 = t := by
  -- The preferred identification is the inverse of the standard `ℝ¹ ≃ ℝ`.
  simp [realToR1, realToR1Equiv]

/-- Helper for Theorem 5.48: postcomposing a smooth scalar map on a subset with the fixed
linear embedding `ℝ → ℝ¹` preserves `Function.IsSmoothOn`. -/
private lemma realToR1_isSmoothOn_of_real_isSmoothOn
    {S : Set M} {f : S → ℝ} (hf : f.IsSmoothOn I 𝓘(ℝ)) :
    (fun x : S ↦ realToR1 (f x)).IsSmoothOn I (𝓡 1) := by
  -- Rewrite the subset-smoothness owner into local extensions and postcompose each local
  -- extension with the fixed continuous linear equivalence `ℝ ≃ ℝ¹`.
  rw [Function.isSmoothOn_iff_exists_local_extension] at hf ⊢
  intro x
  rcases hf x with ⟨V, hVOpen, hxV, Fext, hFext, hEq⟩
  refine ⟨V, hVOpen, hxV, realToR1 ∘ Fext, ?_, ?_⟩
  · -- The linear identification `ℝ → ℝ¹` is smooth, so it preserves the local extension.
    simpa [realToR1, Function.comp] using
      realToR1Equiv.toContinuousLinearMap.contMDiff.comp_contMDiffOn hFext
  · -- On the subset, the packaged extension is exactly the original scalar value.
    intro y hy
    simp [hEq y hy, realToR1]

/-- Helper for Theorem 5.48: near each frontier point, one can shrink the Euclidean boundary patch
and globally extend its signed first coordinate while keeping equality on the closed shrink. -/
lemma frontierPoint_hasExtendedSignedCoordinatePatch
    {D : Set M} {n : ℕ} [hOld : SmoothManifoldWithBoundary dimM D]
    [hSucc : SmoothManifoldWithBoundary (n + 1) D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M]
    (hn : dimM = n + 1)
    (hSucc_eq : hSucc = by simpa [hn] using hOld)
    (b : Module.Basis (Fin (n + 1)) ℝ E)
    {y : M} (hyFrontier : y ∈ frontier D) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      ambientBasisChartedSpace I hn b
    let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
      ambientBasisIsManifold I hn b
    ∃ p : D,
      p.1 = y ∧
        ∃ hNF :
          BoundaryLocalCoordinateNormalFormAt
            (Subtype.val : D → M) p
            (boundary_immersion_normal_form (n + 1) (n + 1)),
          ∃ W V : Set M,
            IsOpen W ∧
              IsOpen V ∧
                y ∈ V ∧
                  hNF.domChart.source = {z : D | z.1 ∈ W} ∧
                    closure V ⊆ (hNF.codChart.restr W).source ∧
                      ∃ ρ : M → ℝ,
                        ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧
                          Set.EqOn ρ (fun x ↦ -((hNF.codChart.restr W) x 0)) (closure V) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    ambientBasisChartedSpace I hn b
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold I hn b
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  letI : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  letI : T4Space M := T4Space.of_paracompactSpace_t2Space
  have hAmbientRev :
      IsLocalDiffeomorph I (𝓡 (n + 1)) ∞ (id : M → M) :=
    ambientId_isLocalDiffeomorph_toAmbientBasis (I := I) (M := M) hn b
  rcases frontierPoint_hasBoundarySourcePatch
      (I := I) (D := D) hn hSucc_eq b hyFrontier with
    ⟨p, hpy, hNF, W, hWOpen, hyW, hW_eq⟩
  let U : Set M := (hNF.codChart.restr W).source
  have hUOpen : IsOpen U := (hNF.codChart.restr W).open_source
  have hpDom : p ∈ hNF.domChart.source := hNF.domChart_centered.1
  have hyCod : y ∈ hNF.codChart.source := by
    simpa [hpy] using BoundaryLocalCoordinateNormalFormAt.mapsTo_source hNF hpDom
  have hyU : y ∈ U := by
    rw [show U = (hNF.codChart.restr W).source by rfl, hNF.codChart.restr_source' W hWOpen]
    exact ⟨hyCod, hyW⟩
  obtain ⟨V, hVOpen, hyV, hClosureV⟩ :=
    normal_exists_closure_subset (isClosed_singleton : IsClosed ({y} : Set M)) hUOpen (by
      simpa using hyU)
  let A : Set M := closure V
  have hAClosed : IsClosed A := isClosed_closure
  have hAU : A ⊆ U := hClosureV
  have hRestrMem :
      hNF.codChart.restr W ∈
        IsManifold.maximalAtlas (𝓡 (n + 1)) ∞ M := by
    -- Restricting a maximal-atlas chart to an open subset keeps it inside the same maximal atlas.
    exact restr_mem_maximalAtlas
      (contDiffGroupoid ∞ (𝓡 (n + 1))) hNF.codChart_mem_maximalAtlas hWOpen
  have hChartSmoothAmbientBasis :
      ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (hNF.codChart.restr W) U := by
    -- The restricted chart is smooth in the Euclideanized ambient structure because it remains a
    -- maximal-atlas chart there.
    simpa [U] using contMDiffOn_of_mem_maximalAtlas hRestrMem
  have hChartSmooth :
      ContMDiffOn I (𝓡 (n + 1)) ∞ (hNF.codChart.restr W) U := by
    -- Route correction: compose the Euclideanized chart smoothness with the already-stabilized
    -- reverse ambient immersion instead of reopening owner transport.
    simpa [U, Function.comp] using
      hChartSmoothAmbientBasis.comp hAmbientRev.contMDiff.contMDiffOn (by
        intro x hx
        exact hx)
  let coord : M → ℝ := fun x ↦ -((hNF.codChart.restr W) x 0)
  have hProjSmooth :
      ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞
        (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z 0) := by
    -- Coordinate projections on Euclidean space are smooth linear maps.
    simpa using
      (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) :
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).contMDiff)
  have hCoordSmooth :
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ coord U := by
    -- The signed first coordinate is the smooth Euclidean projection composed with the chart.
    simpa [coord, Function.comp] using hProjSmooth.neg.comp_contMDiffOn hChartSmooth
  have hCoordSmoothOnClosed :
      (fun x : A ↦ coord x.1).IsSmoothOn I 𝓘(ℝ) := by
    -- Any point of the closed shrink already lies in the restricted chart source, so the same
    -- signed coordinate serves as a local extension there.
    rw [Function.isSmoothOn_iff_exists_local_extension]
    intro x
    refine ⟨U, hUOpen, hAU x.2, coord, hCoordSmooth, ?_⟩
    intro z hz
    rfl
  have hCoordSmoothOnClosedR1 :
      (fun x : A ↦ realToR1 (coord x.1)).IsSmoothOn I (𝓡 1) :=
    realToR1_isSmoothOn_of_real_isSmoothOn hCoordSmoothOnClosed
  rcases exists_supported_contMDiffMap_extension_of_isClosed
      (I := I) (A := A) (U := U) hAClosed hUOpen hAU
      (fun x : A ↦ realToR1 (coord x.1)) hCoordSmoothOnClosedR1 with
    ⟨ρ₁, hρ₁Eq, _hρ₁Support⟩
  let ρ : M → ℝ := fun x ↦ ρ₁ x 0
  have hρSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ := by
    -- Project the global `ℝ¹` extension back to a scalar-valued smooth function.
    simpa [ρ, Function.comp] using
      (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) :
        EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).contMDiff.comp ρ₁.contMDiff)
  have hρEq : Set.EqOn ρ coord A := by
    intro x hx
    -- The extension theorem identifies the `ℝ¹` extension with the packaged local coordinate on
    -- the whole closed shrink.
    have hxEq := hρ₁Eq ⟨x, hx⟩
    simpa [ρ, coord, realToR1_apply_zero] using
      congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) hxEq
  refine ⟨p, hpy, hNF, W, V, hWOpen, hVOpen, ?_, hW_eq, hClosureV, ρ, hρSmooth, hρEq⟩
  -- The shrink was chosen around the frontier point itself.
  simpa using hyV (by simp)

/-- Helper for Theorem 5.48: after retaining the exact source-side patch equation from the
extended signed-coordinate construction, one can shrink once more so that the signed local
coordinate genuinely controls domain membership on the whole neighborhood. -/
lemma frontierSignedPatch_hasSignZero
    {D : Set M} {n : ℕ} [hOld : SmoothManifoldWithBoundary dimM D]
    [hSucc : SmoothManifoldWithBoundary (n + 1) D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M]
    (hn : dimM = n + 1)
    (hSucc_eq : hSucc = by simpa [hn] using hOld)
    (b : Module.Basis (Fin (n + 1)) ℝ E)
    {y : M} (hyFrontier : y ∈ frontier D) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      ambientBasisChartedSpace I hn b
    let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
      ambientBasisIsManifold I hn b
    ∃ V : Set M,
      IsOpen V ∧
        y ∈ V ∧
          ∃ ρ : M → ℝ,
            ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧
              (∀ x ∈ V, x ∈ D ↔ ρ x ≤ 0) ∧
                (∀ x ∈ V, x ∈ frontier D → ρ x = 0) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    ambientBasisChartedSpace I hn b
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold I hn b
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  letI : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  letI : T4Space M := T4Space.of_paracompactSpace_t2Space
  rcases frontierPoint_hasExtendedSignedCoordinatePatch
      (I := I) (D := D) hn hSucc_eq b hyFrontier with
    ⟨p, hpy, hNF, W, V₀, hWOpen, hV₀Open, hyV₀, hW_eq, hClosureV₀, ρ, hρSmooth, hρEq⟩
  rcases restrictedBoundaryLocalNormalForm_image_eq_firstCoordPatch hNF hWOpen hW_eq with
    ⟨P, hPOpen, hP_eq⟩
  have hDClosed : IsClosed D := regularDomain_isClosed I
  have hyD : y ∈ D := by
    -- A frontier point of the closed regular domain still lies in the domain.
    simpa [hDClosed.closure_eq] using hyFrontier.1
  have hySource : y ∈ (hNF.codChart.restr W).source := by
    -- The original shrink already stayed inside the restricted ambient chart source.
    exact hClosureV₀ (subset_closure hyV₀)
  have hyP : (hNF.codChart.restr W) y ∈ P := by
    -- Route correction: the extended patch now remembers `hW_eq`, so the normalized target-patch
    -- membership theorem can be applied to the same `hNF` and `W`.
    have hyImage : (hNF.codChart.restr W) y ∈
        (hNF.codChart.restr W) '' (D ∩ (hNF.codChart.restr W).source) := by
      exact ⟨y, ⟨hyD, hySource⟩, rfl⟩
    rw [hP_eq] at hyImage
    exact hyImage.1
  let U : Set M := V₀ ∩ ((hNF.codChart.restr W).source ∩ (hNF.codChart.restr W) ⁻¹' P)
  have hUOpen : IsOpen U := by
    have hPatchOpen :
        IsOpen ((hNF.codChart.restr W).source ∩ (hNF.codChart.restr W) ⁻¹' P) := by
      exact (hNF.codChart.restr W).continuousOn_toFun.isOpen_inter_preimage
        (hNF.codChart.restr W).open_source hPOpen
    -- Shrink the old neighborhood once more so every point stays in the normalized target patch.
    simpa [U, Set.inter_assoc] using hV₀Open.inter hPatchOpen
  have hyU : y ∈ U := by
    exact ⟨hyV₀, hySource, hyP⟩
  obtain ⟨V, hVOpen, hyV, hClosureV⟩ :=
    normal_exists_closure_subset (isClosed_singleton : IsClosed ({y} : Set M)) hUOpen (by
      simpa [U] using hyU)
  have hVSubsetV₀ : V ⊆ V₀ := by
    intro x hxV
    exact (hClosureV (subset_closure hxV)).1
  have hClosureVV₀ : closure V ⊆ closure V₀ := closure_mono hVSubsetV₀
  refine ⟨V, hVOpen, ?_, ρ, hρSmooth, ?_, ?_⟩
  · -- The refined neighborhood still contains the chosen frontier point.
    simpa using hyV (by simp)
  · intro x hxV
    have hxClosure : x ∈ closure V := subset_closure hxV
    have hxSource : x ∈ (hNF.codChart.restr W).source := by
      exact (hClosureV hxClosure).2.1
    have hxP : (hNF.codChart.restr W) x ∈ P := by
      exact (hClosureV hxClosure).2.2
    have hρx :
        ρ x = -((hNF.codChart.restr W) x 0) := by
      exact hρEq (hClosureVV₀ hxClosure)
    -- On the normalized restricted patch, domain membership is exactly the signed-coordinate test.
    simpa [hρx] using
      (restrictedBoundaryLocalNormalForm_mem_iff_signedCoord_nonpos
        hNF hWOpen hW_eq hP_eq hxSource hxP)
  · intro x hxV hxFrontier'
    have hxClosure : x ∈ closure V := subset_closure hxV
    have hxSource : x ∈ (hNF.codChart.restr W).source := by
      exact (hClosureV hxClosure).2.1
    have hρx :
        ρ x = -((hNF.codChart.restr W) x 0) := by
      exact hρEq (hClosureVV₀ hxClosure)
    have hcoordZero :
        (hNF.codChart.restr W) x 0 = 0 :=
      restrictedBoundaryLocalNormalForm_zero_firstCoord_of_frontier
        (I := I) (D := D) hNF hWOpen hW_eq hxFrontier' hxSource
    -- Frontier points are still exactly zeroes of the signed coordinate on the refined patch.
    simpa [hρx, hcoordZero]

/-- Helper for Theorem 5.48: on the refined signed patch, the zero set is exactly the ambient
frontier of the regular domain. -/
lemma frontierSignedPatch_hasZeroIffFrontier
    {D : Set M} {n : ℕ} [hOld : SmoothManifoldWithBoundary dimM D]
    [hSucc : SmoothManifoldWithBoundary (n + 1) D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M]
    (hn : dimM = n + 1)
    (hSucc_eq : hSucc = by simpa [hn] using hOld)
    (b : Module.Basis (Fin (n + 1)) ℝ E)
    {y : M} (hyFrontier : y ∈ frontier D) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
      ambientBasisChartedSpace I hn b
    let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
      ambientBasisIsManifold I hn b
    ∃ V : Set M,
      IsOpen V ∧
        y ∈ V ∧
          ∃ ρ : M → ℝ,
            ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧
              (∀ x ∈ V, x ∈ D ↔ ρ x ≤ 0) ∧
                (∀ x ∈ V, x ∈ frontier D ↔ ρ x = 0) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    ambientBasisChartedSpace I hn b
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold I hn b
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  letI : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  letI : T4Space M := T4Space.of_paracompactSpace_t2Space
  rcases frontierPoint_hasExtendedSignedCoordinatePatch
      (I := I) (D := D) hn hSucc_eq b hyFrontier with
    ⟨p, hpy, hNF, W, V₀, hWOpen, hV₀Open, hyV₀, hW_eq, hClosureV₀, ρ, hρSmooth, hρEq⟩
  rcases restrictedBoundaryLocalNormalForm_image_eq_firstCoordPatch hNF hWOpen hW_eq with
    ⟨P, hPOpen, hP_eq⟩
  have hDClosed : IsClosed D := regularDomain_isClosed I
  have hyD : y ∈ D := by
    -- A frontier point of the closed regular domain still lies in the domain.
    simpa [hDClosed.closure_eq] using hyFrontier.1
  have hySource : y ∈ (hNF.codChart.restr W).source := by
    -- The original shrink already stayed inside the restricted ambient chart source.
    exact hClosureV₀ (subset_closure hyV₀)
  have hyP : (hNF.codChart.restr W) y ∈ P := by
    -- The normalized target patch is the image of the regular domain in the restricted ambient
    -- chart.
    have hyImage : (hNF.codChart.restr W) y ∈
        (hNF.codChart.restr W) '' (D ∩ (hNF.codChart.restr W).source) := by
      exact ⟨y, ⟨hyD, hySource⟩, rfl⟩
    rw [hP_eq] at hyImage
    exact hyImage.1
  let U : Set M := V₀ ∩ ((hNF.codChart.restr W).source ∩ (hNF.codChart.restr W) ⁻¹' P)
  have hUOpen : IsOpen U := by
    have hPatchOpen :
        IsOpen ((hNF.codChart.restr W).source ∩ (hNF.codChart.restr W) ⁻¹' P) := by
      exact (hNF.codChart.restr W).continuousOn_toFun.isOpen_inter_preimage
        (hNF.codChart.restr W).open_source hPOpen
    -- Shrink once more so every point stays in the normalized target patch.
    simpa [U, Set.inter_assoc] using hV₀Open.inter hPatchOpen
  have hyU : y ∈ U := by
    exact ⟨hyV₀, hySource, hyP⟩
  obtain ⟨V, hVOpen, hyV, hClosureV⟩ :=
    normal_exists_closure_subset (isClosed_singleton : IsClosed ({y} : Set M)) hUOpen (by
      simpa [U] using hyU)
  have hVSubsetV₀ : V ⊆ V₀ := by
    intro x hxV
    exact (hClosureV (subset_closure hxV)).1
  have hClosureVV₀ : closure V ⊆ closure V₀ := closure_mono hVSubsetV₀
  refine ⟨V, hVOpen, ?_, ρ, hρSmooth, ?_, ?_⟩
  · -- The refined neighborhood still contains the chosen frontier point.
    simpa using hyV (by simp)
  · intro x hxV
    have hxClosure : x ∈ closure V := subset_closure hxV
    have hxSource : x ∈ (hNF.codChart.restr W).source := by
      exact (hClosureV hxClosure).2.1
    have hxP : (hNF.codChart.restr W) x ∈ P := by
      exact (hClosureV hxClosure).2.2
    have hρx :
        ρ x = -((hNF.codChart.restr W) x 0) := by
      exact hρEq (hClosureVV₀ hxClosure)
    -- On the normalized restricted patch, domain membership is exactly the signed-coordinate test.
    simpa [hρx] using
      (restrictedBoundaryLocalNormalForm_mem_iff_signedCoord_nonpos
        hNF hWOpen hW_eq hP_eq hxSource hxP)
  · intro x hxV
    constructor
    · intro hxFrontier'
      have hxClosure : x ∈ closure V := subset_closure hxV
      have hxSource : x ∈ (hNF.codChart.restr W).source := by
        exact (hClosureV hxClosure).2.1
      have hρx :
          ρ x = -((hNF.codChart.restr W) x 0) := by
        exact hρEq (hClosureVV₀ hxClosure)
      have hcoordZero :
          (hNF.codChart.restr W) x 0 = 0 :=
        restrictedBoundaryLocalNormalForm_zero_firstCoord_of_frontier
          (I := I) (D := D) hNF hWOpen hW_eq hxFrontier' hxSource
      -- Frontier points are still exactly zeroes of the signed coordinate on the refined patch.
      simpa [hρx, hcoordZero]
    · intro hρZero
      have hxClosure : x ∈ closure V := subset_closure hxV
      have hxRestrSource : x ∈ (hNF.codChart.restr W).source := by
        exact (hClosureV hxClosure).2.1
      have hxP : (hNF.codChart.restr W) x ∈ P := by
        exact (hClosureV hxClosure).2.2
      have hρx :
          ρ x = -((hNF.codChart.restr W) x 0) := by
        exact hρEq (hClosureVV₀ hxClosure)
      have hcoordZero :
          (hNF.codChart.restr W) x 0 = 0 := by
        linarith [hρZero]
      have hxD : x ∈ D := by
        -- The sign equivalence still puts any zero of `ρ` inside the regular domain.
        exact ((restrictedBoundaryLocalNormalForm_mem_iff_signedCoord_nonpos
          hNF hWOpen hW_eq hP_eq hxRestrSource hxP).2 (by linarith [hcoordZero]))
      let xD : D := ⟨x, hxD⟩
      have hxW : x ∈ W := by
        rw [hNF.codChart.restr_source' W hWOpen] at hxRestrSource
        exact hxRestrSource.2
      have hxDom : xD ∈ hNF.domChart.source := by
        simpa [hW_eq, xD] using hxW
      have hxTarget : hNF.domChart xD ∈ hNF.domChart.target :=
        hNF.domChart.map_source hxDom
      have hcoordChart :
          (hNF.codChart.restr W) x = (hNF.domChart xD).1 := by
        -- On `D`, the restricted ambient chart is the source chart followed by the inclusion
        -- normal form.
        simpa [xD, Function.comp, boundaryImmersionNormalForm_self,
          hNF.domChart.left_inv hxDom] using hNF.eqOn hxTarget
      have hchartZero : (hNF.domChart xD).1 0 = 0 := by
        simpa [hcoordChart] using hcoordZero
      let Φ :
          PartialDiffeomorph
            (𝓡∂ (n + 1))
            (𝓡∂ (n + 1))
            D
            (EuclideanHalfSpace (n + 1))
            ∞ :=
        { toPartialEquiv := hNF.domChart.toPartialEquiv
          open_source := hNF.domChart.open_source
          open_target := hNF.domChart.open_target
          contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hNF.domChart_mem_maximalAtlas
          contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hNF.domChart_mem_maximalAtlas }
      have hChartBoundary : (𝓡∂ (n + 1)).IsBoundaryPoint (hNF.domChart xD) := by
        -- In the Euclidean half-space model, the boundary is exactly the zero set of the first
        -- coordinate.
        rw [(𝓡∂ (n + 1)).isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace]
        simpa [extChartAt] using hchartZero.symm
      have hLocal :
          IsLocalDiffeomorphAt
            (𝓡∂ (n + 1))
            (𝓡∂ (n + 1))
            ∞
            (Φ : D → EuclideanHalfSpace (n + 1))
            xD := by
        exact ⟨Φ, hxDom, fun z _ => rfl⟩
      have hxBoundaryNew : (𝓡∂ (n + 1)).IsBoundaryPoint xD := by
        -- The source chart is a local diffeomorphism, so it preserves boundary points.
        exact (hLocal.isBoundaryPoint_iff (by simp)).2 hChartBoundary
      have hxBoundaryOld : (leeBoundaryModelWithCorners dimM).IsBoundaryPoint xD := by
        -- Transport the boundary witness back to the original regular-domain owner.
        exact (leeBoundaryModelWithCorners_isBoundaryPoint_iff_succ
          (D := D) (n := n) hn hSucc_eq).2 hxBoundaryNew
      exact boundaryPoint_mem_frontier (I := I) (D := D) hxBoundaryOld

/-- Helper for Theorem 5.48: negating a local signed patch and restricting it to `D` produces a
source-side boundary-defining function at every local zero. -/
lemma frontierSignedPatch_negRestrict_isBoundaryDefiningAt
    {D : Set M} {n : ℕ} [hOld : SmoothManifoldWithBoundary dimM D]
    [hSucc : SmoothManifoldWithBoundary (n + 1) D] [Set.IsRegularDomain I D]
    (hn : dimM = n + 1)
    (hSucc_eq : hSucc = by simpa [hn] using hOld)
    {V : Set M} (hVOpen : IsOpen V) {ρ : M → ℝ}
    (hρSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ)
    (hρSign : ∀ x ∈ V, x ∈ D ↔ ρ x ≤ 0)
    (hρZero : ∀ x ∈ V, x ∈ frontier D ↔ ρ x = 0)
    {x : M} (hxV : x ∈ V) (hxD : x ∈ D) (hρx : ρ x = 0) :
    let xD : D := ⟨x, hxD⟩
    IsBoundaryDefiningFunctionAt (M := D) (n := n + 1) xD (fun z : D ↦ -ρ z.1) := by
  let xD : D := ⟨x, hxD⟩
  have hxFrontier : x ∈ frontier D := (hρZero x hxV).2 hρx
  have hxBoundaryOld : (leeBoundaryModelWithCorners dimM).IsBoundaryPoint xD := by
    rcases (mem_frontier_iff_exists_boundaryPoint (I := I) (D := D) (x := x)).1 hxFrontier with
      ⟨p, hp, hpx⟩
    have hpEq : p = xD := Subtype.ext hpx
    simpa [hpEq] using hp
  have hxBoundaryNew : (𝓡∂ (n + 1)).IsBoundaryPoint xD := by
    exact (leeBoundaryModelWithCorners_isBoundaryPoint_iff_succ
      (D := D) (n := n) hn hSucc_eq).1 hxBoundaryOld
  have hxBoundaryMem : xD ∈ (𝓡∂ (n + 1)).boundary D := by
    simpa [ModelWithCorners.boundary] using hxBoundaryNew
  have hImmOld :
      Manifold.IsImmersion (leeBoundaryModelWithCorners dimM) I ∞ (Subtype.val : D → M) :=
    (regularDomainSubtypeVal_isSmoothEmbedding_infty (I := I) (D := D)).isImmersion
  have hImmNew :
      Manifold.IsImmersion (𝓡∂ (n + 1)) I ∞ (Subtype.val : D → M) := by
    exact (leeBoundaryModelWithCorners_isImmersion_iff_succ
      (I := I) (D := D) (n := n) hn hSucc_eq).1 hImmOld
  have hNegSmooth :
      ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ (fun z : D ↦ -ρ z.1) xD := by
    have hValSmooth : ContMDiff (𝓡∂ (n + 1)) I ∞ (Subtype.val : D → M) := hImmNew.contMDiff
    simpa [Function.comp] using (hρSmooth.neg.comp hValSmooth).contMDiffAt
  refine ⟨hxBoundaryMem, hNegSmooth, ?_⟩
  refine ⟨{z : D | z.1 ∈ V}, hVOpen.preimage continuous_subtype_val, ?_, ?_, ?_⟩
  · simpa [xD]
  · intro z hz
    constructor
    · intro hzBoundaryMem
      have hzBoundaryNew : (𝓡∂ (n + 1)).IsBoundaryPoint z := by
        simpa [ModelWithCorners.boundary] using hzBoundaryMem
      have hzBoundaryOld : (leeBoundaryModelWithCorners dimM).IsBoundaryPoint z := by
        exact (leeBoundaryModelWithCorners_isBoundaryPoint_iff_succ
          (D := D) (n := n) hn hSucc_eq).2 hzBoundaryNew
      have hzFrontier : z.1 ∈ frontier D := boundaryPoint_mem_frontier (I := I) (D := D) hzBoundaryOld
      have hzZero : ρ z.1 = 0 := (hρZero z.1 hz).1 hzFrontier
      simpa [hzZero]
    · intro hzZeroNeg
      have hzZero : ρ z.1 = 0 := by linarith
      have hzFrontier : z.1 ∈ frontier D := (hρZero z.1 hz).2 hzZero
      have hzBoundaryOld : (leeBoundaryModelWithCorners dimM).IsBoundaryPoint z := by
        rcases (mem_frontier_iff_exists_boundaryPoint
            (I := I) (D := D) (x := z.1)).1 hzFrontier with ⟨p, hp, hpz⟩
        simpa using (Subtype.ext hpz) ▸ hp
      have hzBoundaryNew : (𝓡∂ (n + 1)).IsBoundaryPoint z := by
        exact (leeBoundaryModelWithCorners_isBoundaryPoint_iff_succ
          (D := D) (n := n) hn hSucc_eq).1 hzBoundaryOld
      simpa [ModelWithCorners.boundary] using hzBoundaryNew
  · intro z hz
    constructor
    · intro hzInterior
      have hzInteriorPoint : (𝓡∂ (n + 1)).IsInteriorPoint z := by
        simpa [ModelWithCorners.interior] using hzInterior
      have hzNotBoundaryNew :
          ¬ (𝓡∂ (n + 1)).IsBoundaryPoint z :=
        ((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint z).1 hzInteriorPoint
      have hzNotBoundaryOld :
          ¬ (leeBoundaryModelWithCorners dimM).IsBoundaryPoint z := by
        intro hzBoundaryOld
        exact hzNotBoundaryNew <|
          (leeBoundaryModelWithCorners_isBoundaryPoint_iff_succ
            (D := D) (n := n) hn hSucc_eq).1 hzBoundaryOld
      have hzLe : ρ z.1 ≤ 0 := (hρSign z.1 hz).1 z.2
      have hzNotFrontier : z.1 ∉ frontier D := by
        intro hzFrontier
        exact hzNotBoundaryOld <| by
          rcases (mem_frontier_iff_exists_boundaryPoint
              (I := I) (D := D) (x := z.1)).1 hzFrontier with ⟨p, hp, hpz⟩
          simpa using (Subtype.ext hpz) ▸ hp
      have hzNe : ρ z.1 ≠ 0 := by
        intro hzZero
        exact hzNotFrontier ((hρZero z.1 hz).2 hzZero)
      have hzLt : ρ z.1 < 0 := lt_of_le_of_ne hzLe hzNe
      linarith
    · intro hzPos
      have hzLt : ρ z.1 < 0 := by linarith
      have hzNotFrontier : z.1 ∉ frontier D := by
        intro hzFrontier
        have hzZero : ρ z.1 = 0 := (hρZero z.1 hz).1 hzFrontier
        linarith
      have hzNotBoundaryOld :
          ¬ (leeBoundaryModelWithCorners dimM).IsBoundaryPoint z :=
        not_boundaryPoint_of_mem_diff_frontier (I := I) (D := D) ⟨z.2, hzNotFrontier⟩
      have hzNotBoundaryNew :
          ¬ (𝓡∂ (n + 1)).IsBoundaryPoint z := by
        intro hzBoundaryNew
        exact hzNotBoundaryOld <|
          (leeBoundaryModelWithCorners_isBoundaryPoint_iff_succ
            (D := D) (n := n) hn hSucc_eq).2 hzBoundaryNew
      have hzInteriorPoint : (𝓡∂ (n + 1)).IsInteriorPoint z :=
        ((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint z).2 hzNotBoundaryNew
      simpa [ModelWithCorners.interior] using hzInteriorPoint

/-- Helper for Theorem 5.48: once a smooth signed function is available on an open neighborhood of
the frontier, one can splice it with global sign-control terms to obtain a genuine defining
function for the whole regular domain. -/
lemma globalizeFrontierNeighborhoodSignedFunction
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M]
    {U : Set M} (hUOpen : IsOpen U) (hFrontierU : frontier D ⊆ U)
    {ρ : M → ℝ} (hρSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ)
    (hρSign : ∀ y ∈ U, y ∈ D ↔ ρ y ≤ 0)
    (hρZero : ∀ y ∈ U, y ∈ frontier D ↔ ρ y = 0)
    (hρRegular : ∀ y ∈ U, ρ y = 0 → Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) ρ y)) :
    ∃ f : M → ℝ, IsDefiningFunction I D f := by
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  letI : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  letI : T4Space M := T4Space.of_paracompactSpace_t2Space
  have hDClosed : IsClosed D := regularDomain_isClosed I
  have hFrontierClosed : IsClosed (frontier D) := isClosed_frontier
  obtain ⟨U₀, hU₀Open, hFrontierU₀, hClosureU₀⟩ :=
    normal_exists_closure_subset hFrontierClosed hUOpen hFrontierU
  have hU₀SubsetU : U₀ ⊆ U := fun x hx ↦ hClosureU₀ (subset_closure hx)
  rcases exists_contMDiffMap_one_nhds_of_subset_interior I hFrontierClosed
      (show frontier D ⊆ interior U₀ by simpa [hU₀Open.interior_eq] using hFrontierU₀) with
    ⟨χ, hχOne, hχZero, hχRange⟩
  obtain ⟨N, hNOpen, hFrontierN, hNχ⟩ := mem_nhdsSet_iff_exists.mp hχOne
  have hNSubsetU₀ : N ⊆ U₀ := by
    intro x hxN
    by_contra hxU₀
    have hχx : χ x = 0 := hχZero x hxU₀
    have : (0 : ℝ) = 1 := by simpa [hχx] using hNχ hxN
    exact zero_ne_one this
  have hNSubsetU : N ⊆ U := fun x hxN ↦ hU₀SubsetU (hNSubsetU₀ hxN)
  have hDdiffNClosed : IsClosed (D \ N) := by
    simpa [Set.diff_eq] using hDClosed.inter hNOpen.isClosed_compl
  have hDdiffNInterior : D \ N ⊆ interior D := by
    intro x hx
    have hxNotFrontier : x ∉ frontier D := fun hxFrontier ↦ hx.2 (hFrontierN hxFrontier)
    by_contra hxInterior
    exact hxNotFrontier ⟨by simpa [hDClosed.closure_eq] using hx.1, hxInterior⟩
  rcases exists_contMDiffMap_one_nhds_of_subset_interior I hDdiffNClosed hDdiffNInterior with
    ⟨θ, hθOne, hθZero, hθRange⟩
  obtain ⟨η, hηSmooth, hηRange, hηZero, _hηOneEmpty⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed I hDClosed isClosed_empty
      (by simpa using (disjoint_empty_right : Disjoint D (∅ : Set M)))
  let g : M → ℝ := fun x ↦ η x - (1 / 2 : ℝ) * θ x
  let f : M → ℝ := fun x ↦ χ x * ρ x + (1 - χ x) * g x
  have hθOneOnDdiffN : ∀ x ∈ D \ N, θ x = 1 := by
    intro x hx
    have hθxNhds : {y : M | θ y = 1} ∈ nhds x := (mem_nhdsSet_iff_forall.mp hθOne) x hx
    have hxMem : x ∈ {y : M | θ y = 1} := mem_of_mem_nhds hθxNhds
    exact hxMem
  have hgNonposOnD : ∀ x ∈ D, g x ≤ 0 := by
    intro x hxD
    have hηx : η x = 0 := (hηZero x).1 hxD
    have hθNonneg : 0 ≤ θ x := (hθRange x).1
    -- On the domain, the auxiliary separator vanishes and the cutoff subtraction keeps the sign nonpositive.
    simp [g, hηx, hθNonneg]
  have hgStrictNegOnDdiffN : ∀ x ∈ D \ N, g x < 0 := by
    intro x hx
    have hηx : η x = 0 := (hηZero x).1 hx.1
    have hθx : θ x = 1 := hθOneOnDdiffN x hx
    -- Away from the frontier neighborhood, the negative cutoff term forces a strict sign.
    simp [g, hηx, hθx]
  have hgPosOffD : ∀ x ∉ D, 0 < g x := by
    intro x hxD
    have hθx : θ x = 0 := hθZero x hxD
    have hηnonneg : 0 ≤ η x := (hηRange ⟨x, rfl⟩).1
    have hηne : η x ≠ 0 := by
      intro hηx
      exact hxD ((hηZero x).2 hηx)
    have hηpos : 0 < η x := by
      exact lt_of_le_of_ne hηnonneg (by simpa using hηne.symm)
    -- Outside the domain, the exact-zero owner for `η` makes the auxiliary function strictly positive.
    simpa [g, hθx] using hηpos
  have hfNonposOnD : ∀ x ∈ D, f x ≤ 0 := by
    intro x hxD
    by_cases hxU₀ : x ∈ U₀
    · have hxU : x ∈ U := hU₀SubsetU hxU₀
      have hρle : ρ x ≤ 0 := (hρSign x hxU).1 hxD
      have hgle : g x ≤ 0 := hgNonposOnD x hxD
      have hχNonneg : 0 ≤ χ x := (hχRange x).1
      have hOneSubNonneg : 0 ≤ 1 - χ x := sub_nonneg.mpr (hχRange x).2
      -- On the frontier neighborhood, both summands are nonpositive, so the splice is nonpositive.
      have hFirst : χ x * ρ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hχNonneg hρle
      have hSecond : (1 - χ x) * g x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hOneSubNonneg hgle
      dsimp [f]
      exact add_nonpos hFirst hSecond
    · have hχx : χ x = 0 := hχZero x hxU₀
      -- Outside the frontier neighborhood, the splice reduces to the global sign controller `g`.
      simpa [f, hχx] using hgNonposOnD x hxD
  have hfPosOffD : ∀ x ∉ D, 0 < f x := by
    intro x hxD
    by_cases hxU₀ : x ∈ U₀
    · have hxU : x ∈ U := hU₀SubsetU hxU₀
      have hρPos : 0 < ρ x := by
        have hρNotLe : ¬ ρ x ≤ 0 := by
          intro hρle
          exact hxD ((hρSign x hxU).2 hρle)
        exact lt_of_not_ge hρNotLe
      have hgPos : 0 < g x := hgPosOffD x hxD
      have hχNonneg : 0 ≤ χ x := (hχRange x).1
      by_cases hχx : χ x = 0
      · -- If the frontier cutoff vanishes, positivity comes entirely from the global separator.
        simpa [f, hχx] using hgPos
      · have hχPos : 0 < χ x := by
          refine lt_of_le_of_ne hχNonneg ?_
          intro hχx'
          exact hχx hχx'.symm
        have hOneSubNonneg : 0 ≤ 1 - χ x := sub_nonneg.mpr (hχRange x).2
        have hFirstPos : 0 < χ x * ρ x := mul_pos hχPos hρPos
        have hSecondNonneg : 0 ≤ (1 - χ x) * g x := mul_nonneg hOneSubNonneg hgPos.le
        -- When the frontier cutoff is active, the local signed model and the global separator are both positive.
        have hPosSum : 0 < χ x * ρ x + (1 - χ x) * g x := add_pos_of_pos_of_nonneg hFirstPos hSecondNonneg
        dsimp [f]
        exact hPosSum
    · have hχx : χ x = 0 := hχZero x hxU₀
      -- Away from the frontier neighborhood, positivity again comes from `g`.
      simpa [f, hχx] using hgPosOffD x hxD
  have hDLevel : D = f ⁻¹' Set.Iic 0 := by
    ext x
    constructor
    · intro hxD
      simpa [Set.mem_Iic] using hfNonposOnD x hxD
    · intro hfx
      by_contra hxD
      exact (not_le_of_gt (hfPosOffD x hxD)) hfx
  have hfRegular : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f 0 := by
    intro x hx0
    have hxD : x ∈ D := by
      have hxLevel : x ∈ f ⁻¹' Set.Iic 0 := by simp [hx0]
      simpa [hDLevel] using hxLevel
    have hxU₀ : x ∈ U₀ := by
      by_contra hxU₀
      have hxNotN : x ∉ N := fun hxN ↦ hxU₀ (hNSubsetU₀ hxN)
      have hgxNeg : g x < 0 := hgStrictNegOnDdiffN x ⟨hxD, hxNotN⟩
      have : f x < 0 := by simpa [f, hχZero x hxU₀] using hgxNeg
      exact (ne_of_lt this) hx0
    have hxU : x ∈ U := hU₀SubsetU hxU₀
    have hxN : x ∈ N := by
      by_contra hxN
      by_cases hχx : χ x = 1
      · have hρx : ρ x = 0 := by simpa [f, hχx] using hx0
        exact hxN (hFrontierN ((hρZero x hxU).2 hρx))
      · have hχLt : χ x < 1 := lt_of_le_of_ne (hχRange x).2 hχx
        have hρle : ρ x ≤ 0 := (hρSign x hxU).1 hxD
        have hgxNeg : g x < 0 := hgStrictNegOnDdiffN x ⟨hxD, hxN⟩
        have hχNonneg : 0 ≤ χ x := (hχRange x).1
        have hOneSubPos : 0 < 1 - χ x := sub_pos.mpr hχLt
        have : f x < 0 := by
          -- Outside the exact `χ = 1` patch, the strict negativity of `g` rules out any new zero.
          have hFirstNonpos : χ x * ρ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hχNonneg hρle
          have hSecondNeg : (1 - χ x) * g x < 0 := mul_neg_of_pos_of_neg hOneSubPos hgxNeg
          have hNegSum : χ x * ρ x + (1 - χ x) * g x < 0 :=
            add_neg_of_nonpos_of_neg hFirstNonpos hSecondNeg
          dsimp [f]
          exact hNegSum
        exact (ne_of_lt this) hx0
    have hEq : f =ᶠ[nhds x] ρ := by
      filter_upwards [hNOpen.mem_nhds hxN] with y hyN
      -- On the open patch where `χ = 1`, the splice is exactly the local frontier function `ρ`.
      have hχy : χ y = 1 := hNχ hyN
      simp [f, hχy]
    have hρx : ρ x = 0 := by
      have hfx : f x = ρ x := hEq.eq_of_nhds
      simpa [hx0] using hfx.symm
    -- The regularity test is local, and on the exact `χ = 1` patch the splice agrees with `ρ`.
    rw [hEq.mfderiv_eq]
    exact hρRegular x hxU hρx
  have hgSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ g := by
    -- The global sign controller is built from the exact-zero separator and a cutoff-supported constant subtraction.
    exact hηSmooth.sub (contMDiff_const.mul θ.contMDiff)
  refine ⟨f, ?_⟩
  -- Package the global splice with the regular value `0` coming from the frontier neighborhood model.
  refine ⟨?_, ?_⟩
  · exact (χ.contMDiff.mul hρSmooth).add ((contMDiff_const.sub χ.contMDiff).mul hgSmooth)
  · exact ⟨⟨0, hfRegular, hDLevel⟩⟩

/-- Helper for Theorem 5.48: in positive ambient dimension, the remaining task is to build one
smooth signed function on an open neighborhood of `frontier D` with the correct local sign and
regular-value behavior. -/
lemma frontierPartitionOfUnitySignedSum_hasSignZero
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M]
    (hFrontierSignedPatch :
      ∀ y ∈ frontier D,
        ∃ V : Set M,
          IsOpen V ∧
            y ∈ V ∧
              ∃ ρ : M → ℝ,
                ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧
                  (∀ x ∈ V, x ∈ D ↔ ρ x ≤ 0) ∧
                    (∀ x ∈ V, x ∈ frontier D ↔ ρ x = 0)) :
    ∃ U : Set M, IsOpen U ∧ frontier D ⊆ U ∧
      ∃ ρ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧
        (∀ y ∈ U, y ∈ D ↔ ρ y ≤ 0) ∧
        (∀ y ∈ U, y ∈ frontier D ↔ ρ y = 0) := by
  classical
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  letI : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  letI : T4Space M := T4Space.of_paracompactSpace_t2Space
  choose W hWOpen hyW ρloc hρSmoothLocal hρSignLocal hρZeroLocal using hFrontierSignedPatch
  let cover : frontier D → Set M := fun y ↦ W y.1 y.2
  let localρ : frontier D → M → ℝ := fun y ↦ ρloc y.1 y.2
  have hcoverOpen : ∀ y : frontier D, IsOpen (cover y) := by
    intro y
    exact hWOpen y.1 y.2
  have hcoverMem : ∀ y : frontier D, y.1 ∈ cover y := by
    intro y
    exact hyW y.1 y.2
  have hcoverFrontier : frontier D ⊆ ⋃ y : frontier D, cover y := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hcoverMem ⟨x, hx⟩⟩
  obtain ⟨φ, hφSub⟩ :
      ∃ φ : SmoothPartitionOfUnity (frontier D) I M (frontier D), φ.IsSubordinate cover :=
    SmoothPartitionOfUnity.exists_isSubordinate I isClosed_frontier cover hcoverOpen hcoverFrontier
  let σ : M → ℝ := fun x ↦ ∑ᶠ y : frontier D, φ y x
  let U : Set M := {x | 0 < σ x}
  let ρ : M → ℝ := fun x ↦ ∑ᶠ y : frontier D, φ y x * localρ y x
  have hσSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ σ := by
    -- The total partition weight is a smooth weighted sum with constant local data.
    simpa [σ, smul_eq_mul] using
      (φ.contMDiff_finsum_smul (g := fun _ _ ↦ (1 : ℝ))
        (fun _ _ _ ↦ contMDiffAt_const))
  have hUOpen : IsOpen U := by
    -- The positive-total-weight locus is open because the total partition weight is continuous.
    have hpre : IsOpen (σ ⁻¹' Set.Ioi (0 : ℝ)) :=
      hσSmooth.continuous.isOpen_preimage (Set.Ioi (0 : ℝ)) isOpen_Ioi
    simpa [U] using hpre
  have hFrontierU : frontier D ⊆ U := by
    intro x hx
    -- On the frontier itself the partition of unity has total weight exactly `1`.
    have hσx : σ x = 1 := by
      simpa [σ] using φ.sum_eq_one hx
    simpa [U, hσx]
  have hρSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ := by
    -- Subordination lets the weighted sum use each local signed patch only on its own open set.
    simpa [ρ, smul_eq_mul] using
      hφSub.contMDiff_finsum_smul (g := localρ) hcoverOpen
        (fun y ↦ (hρSmoothLocal y.1 y.2).contMDiffOn)
  have hσ_finsupport (x : M) :
      (φ.finsupport x).sum (fun y ↦ φ y x) = σ x := by
    -- The scalar-valued partition sum is the `A = ℝ` specialization of the standard finsupport
    -- rewrite for smooth partitions of unity.
    simpa [σ] using
      (φ.sum_finsupport_smul_eq_finsum (x₀ := x) (φ := fun _ _ ↦ (1 : ℝ)))
  have hρ_finsupport (x : M) :
      (φ.finsupport x).sum (fun y ↦ φ y x * localρ y x) = ρ x := by
    -- The weighted sum uses the same finsupport rewrite, now with the local signed patches as
    -- the coefficient family.
    simpa [ρ, smul_eq_mul] using
      (φ.sum_finsupport_smul_eq_finsum (x₀ := x) (φ := localρ))
  have hcoeff_pos {x : M} {y : frontier D} (hy : y ∈ φ.finsupport x) : 0 < φ y x := by
    have hy_support : y ∈ Function.support (fun z : frontier D ↦ φ z x) := by
      simpa using (φ.mem_finsupport (x₀ := x) (i := y)).1 hy
    have hy_ne : φ y x ≠ 0 := by
      simpa [Function.support] using hy_support
    exact lt_of_le_of_ne (φ.nonneg y x) hy_ne.symm
  have hmem_cover_of_finsupport {x : M} {y : frontier D} (hy : y ∈ φ.finsupport x) :
      x ∈ cover y := by
    have hy_support : x ∈ Function.support (φ y) := by
      exact Function.mem_support.2 (ne_of_gt (hcoeff_pos hy))
    have hy_tsupport : x ∈ tsupport (φ y) := subset_closure hy_support
    exact hφSub y hy_tsupport
  have exists_active (x : M) (hxU : x ∈ U) : ∃ y : frontier D, y ∈ φ.finsupport x := by
    have hxσ : 0 < σ x := by
      simpa [U] using hxU
    by_contra hnone
    have hempty : φ.finsupport x = ∅ := by
      ext y
      constructor
      · intro hy
        exact False.elim (hnone ⟨y, hy⟩)
      · intro hy
        cases hy
    have hσzero : σ x = 0 := by
      rw [← hσ_finsupport x, hempty]
      simp
    linarith
  have hρ_nonpos_of_mem (x : M) (hxD : x ∈ D) :
      ρ x ≤ 0 := by
    -- On `D`, every active local defining patch is nonpositive, so the weighted sum is too.
    rw [← hρ_finsupport x]
    refine Finset.sum_nonpos ?_
    intro y hy
    have hxCover : x ∈ cover y := hmem_cover_of_finsupport hy
    have hlocal : localρ y x ≤ 0 := (hρSignLocal y.1 y.2 x hxCover).1 hxD
    exact mul_nonpos_of_nonneg_of_nonpos (φ.nonneg y x) hlocal
  have hρ_pos_of_not_mem (x : M) (hxU : x ∈ U) (hxD : x ∉ D) :
      0 < ρ x := by
    -- Outside `D`, every active local patch is strictly positive, and one active coefficient is
    -- positive because the total partition weight is positive.
    rcases exists_active x hxU with ⟨y, hy⟩
    have hyCoeff : 0 < φ y x := hcoeff_pos hy
    have hxCoverY : x ∈ cover y := hmem_cover_of_finsupport hy
    have hyLocal : 0 < localρ y x := by
      have hyNotLe : ¬ localρ y x ≤ 0 := by
        intro hyLe
        exact hxD ((hρSignLocal y.1 y.2 x hxCoverY).2 hyLe)
      linarith
    have htermPos : 0 < φ y x * localρ y x := mul_pos hyCoeff hyLocal
    have hrestNonneg :
        0 ≤ (φ.finsupport x \ {y}).sum (fun z ↦ φ z x * localρ z x) := by
      refine Finset.sum_nonneg ?_
      intro z hz
      have hzCover : x ∈ cover z := hmem_cover_of_finsupport (Finset.mem_sdiff.1 hz).1
      have hzLocal : 0 ≤ localρ z x := by
        have hzNotLe : ¬ localρ z x ≤ 0 := by
          intro hzLe
          exact hxD ((hρSignLocal z.1 z.2 x hzCover).2 hzLe)
        linarith
      exact mul_nonneg (φ.nonneg z x) hzLocal
    have hsumPos :
        0 < (φ.finsupport x).sum (fun z ↦ φ z x * localρ z x) := by
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hy]
      exact add_pos_of_pos_of_nonneg htermPos hrestNonneg
    simpa [hρ_finsupport x] using hsumPos
  have hρ_neg_of_not_frontier (x : M) (hxU : x ∈ U) (hxD : x ∈ D)
      (hxFrontier : x ∉ frontier D) :
      ρ x < 0 := by
    -- Inside `D` but away from the frontier, every active local patch is strictly negative.
    rcases exists_active x hxU with ⟨y, hy⟩
    have hyCoeff : 0 < φ y x := hcoeff_pos hy
    have hxCoverY : x ∈ cover y := hmem_cover_of_finsupport hy
    have hyLocalLe : localρ y x ≤ 0 := (hρSignLocal y.1 y.2 x hxCoverY).1 hxD
    have hyLocalNe : localρ y x ≠ 0 := by
      intro hyZero
      exact hxFrontier ((hρZeroLocal y.1 y.2 x hxCoverY).2 hyZero)
    have hyLocalNeg : localρ y x < 0 := lt_of_le_of_ne hyLocalLe hyLocalNe
    have htermNeg : φ y x * localρ y x < 0 := mul_neg_of_pos_of_neg hyCoeff hyLocalNeg
    have hrestNonpos :
        (φ.finsupport x \ {y}).sum (fun z ↦ φ z x * localρ z x) ≤ 0 := by
      refine Finset.sum_nonpos ?_
      intro z hz
      have hzCover : x ∈ cover z := hmem_cover_of_finsupport (Finset.mem_sdiff.1 hz).1
      have hzLocal : localρ z x ≤ 0 := (hρSignLocal z.1 z.2 x hzCover).1 hxD
      exact mul_nonpos_of_nonneg_of_nonpos (φ.nonneg z x) hzLocal
    have hsumNeg :
        (φ.finsupport x).sum (fun z ↦ φ z x * localρ z x) < 0 := by
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hy]
      exact add_neg_of_neg_of_nonpos htermNeg hrestNonpos
    simpa [hρ_finsupport x] using hsumNeg
  have hSign : ∀ x ∈ U, x ∈ D ↔ ρ x ≤ 0 := by
    intro x hxU
    constructor
    · intro hxD
      exact hρ_nonpos_of_mem x hxD
    · intro hxρ
      by_contra hxD
      exact (not_le_of_gt (hρ_pos_of_not_mem x hxU hxD)) hxρ
  have hZero : ∀ x ∈ U, x ∈ frontier D ↔ ρ x = 0 := by
    intro x hxU
    constructor
    · intro hxFrontier
      -- On the ambient frontier, every active local patch vanishes, so the weighted sum vanishes.
      rw [← hρ_finsupport x]
      refine Finset.sum_eq_zero ?_
      intro y hy
      have hxCover : x ∈ cover y := hmem_cover_of_finsupport hy
      have hlocalZero : localρ y x = 0 := (hρZeroLocal y.1 y.2 x hxCover).1 hxFrontier
      simp [hlocalZero]
    · intro hρx
      have hxD : x ∈ D := (hSign x hxU).2 (by simpa [hρx])
      by_contra hxFrontier
      exact (ne_of_lt (hρ_neg_of_not_frontier x hxU hxD hxFrontier)) hρx
  exact ⟨U, hUOpen, hFrontierU, ρ, hρSmooth, hSign, hZero⟩

/-- Helper for Theorem 5.48: in positive ambient dimension, the remaining task is to build one
smooth signed function on an open neighborhood of `frontier D` with the correct local sign and
regular-value behavior. -/
lemma existsFrontierNeighborhoodSignedFunction
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M] (h0 : dimM ≠ 0) :
    ∃ U : Set M, IsOpen U ∧ frontier D ⊆ U ∧
      ∃ ρ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧
        (∀ y ∈ U, y ∈ D ↔ ρ y ≤ 0) ∧
        (∀ y ∈ U, y ∈ frontier D ↔ ρ y = 0) ∧
        (∀ y ∈ U, ρ y = 0 → Function.Surjective (mfderiv I 𝓘(ℝ, ℝ) ρ y)) := by
  by_cases hFrontierEmpty : frontier D = ∅
  · -- If the frontier is empty, the neighborhood problem is vacuous, so the empty neighborhood
    -- and the zero function already satisfy the requested package.
    refine ⟨∅, isOpen_empty, ?_, fun _ ↦ 0, contMDiff_const, ?_, ?_, ?_⟩
    · simpa [hFrontierEmpty]
    · intro y hy
      exact False.elim hy
    · intro y hy
      exact False.elim hy
    · intro y hy _
      exact False.elim hy
  rcases dimM_eq_succ_of_ne_zero h0 with ⟨n, hn⟩
  letI : SmoothManifoldWithBoundary (n + 1) D := by
    simpa [hn] using (inferInstance : SmoothManifoldWithBoundary dimM D)
  have hSmoothBoundarySucc_eq :
      (inferInstance : SmoothManifoldWithBoundary (n + 1) D) = by
        simpa [hn] using (inferInstance : SmoothManifoldWithBoundary dimM D) := rfl
  let b : Module.Basis (Fin (n + 1)) ℝ E := by
    -- Fix one Euclidean basis for the positive-dimensional ambient model before choosing local
    -- frontier charts.
    simpa [hn] using (Module.finBasis ℝ E : Module.Basis (Fin dimM) ℝ E)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M :=
    ambientBasisChartedSpace I hn b
  let _ : IsManifold (𝓡 (n + 1)) (⊤ : WithTop ℕ∞) M :=
    ambientBasisIsManifold I hn b
  have hFrontierSignedPatch :
      ∀ y ∈ frontier D,
        ∃ V : Set M,
          IsOpen V ∧
            y ∈ V ∧
              ∃ ρ : M → ℝ,
                ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧
                  (∀ x ∈ V, x ∈ D ↔ ρ x ≤ 0) ∧
                    (∀ x ∈ V, x ∈ frontier D ↔ ρ x = 0) := by
    intro y hyFrontier
    -- Route correction: the local patch now already carries the exact zero/frontier equivalence
    -- needed for the partition-of-unity glue step.
    exact frontierSignedPatch_hasZeroIffFrontier
      (I := I) (D := D) hn hSmoothBoundarySucc_eq b hyFrontier
  rcases frontierPartitionOfUnitySignedSum_hasSignZero (I := I) (D := D) hFrontierSignedPatch with
    ⟨U, hUOpen, hFrontierU, ρ, hρSmooth, hρSign, hρZero⟩
  refine ⟨U, hUOpen, hFrontierU, ρ, hρSmooth, hρSign, hρZero, ?_⟩
  intro x hxU hρx
  have hxD : x ∈ D := (hρSign x hxU).2 (by simpa [hρx])
  let xD : D := ⟨x, hxD⟩
  have hbd :
      IsBoundaryDefiningFunctionAt (M := D) (n := n + 1) xD (fun z : D ↦ -ρ z.1) := by
    -- The glued neighborhood function already has the exact sign/zero package needed on `D`.
    exact frontierSignedPatch_negRestrict_isBoundaryDefiningAt
      (I := I) (D := D) (n := n) hn hSmoothBoundarySucc_eq
      hUOpen hρSmooth hρSign hρZero hxU hxD hρx
  -- The source-side boundary-defining function forces the ambient real derivative to be nonzero.
  exact boundaryDefiningAt_surjectiveAmbientMfderiv
    (I := I) (D := D) (n := n) hn hSmoothBoundarySucc_eq hρSmooth hbd

/-- Theorem 5.48: every regular domain in a smooth manifold without boundary admits a
defining function. -/
theorem exists_definingFunction_of_isRegularDomain
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M] :
    ∃ f : M → ℝ, IsDefiningFunction I D f := by
  by_cases hdim0 : dimM = 0
  · -- In ambient dimension `0`, the regular domain is already cut out by the clopen separator.
    exact zeroDimensionalRegularDomain_hasDefiningFunction (I := I) hdim0
  · -- In positive dimension, globalize the signed neighborhood model built near `frontier D`.
    rcases existsFrontierNeighborhoodSignedFunction (I := I) (D := D) hdim0 with
      ⟨U, hUOpen, hFrontierU, ρ, hρSmooth, hρSign, hρZero, hρRegular⟩
    exact globalizeFrontierNeighborhoodSignedFunction (I := I) hUOpen hFrontierU
      hρSmooth hρSign hρZero hρRegular

/-- Helper for Theorem 5.48: a zero-level defining function on a compact regular domain should be
spliced with a positive smooth exhaustion so the zero set and regularity stay unchanged near
`frontier D` while the final function is proper. -/
lemma spliceZeroLevelDefiningWithPositiveExhaustion
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M] (hD : IsCompact D)
    {g0 : M → ℝ} (hg0 : IsDefiningFunction I D g0)
    (hD0 : D = g0 ⁻¹' Set.Iic 0)
    (hg0Regular : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) g0 0) :
    ∃ f : M → ℝ, IsDefiningFunction I D f ∧ Function.IsExhaustionFunction f := by
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  letI : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  letI : T4Space M := T4Space.of_paracompactSpace_t2Space
  obtain ⟨h, hhPos, hhExhaust⟩ :=
    exists_positive_smooth_exhaustion_function (I := I) (M := M)
  obtain ⟨V, hVOpen, hDV, hVCompact⟩ := exists_isOpen_superset_and_isCompact_closure hD
  rcases exists_contMDiffMap_one_nhds_of_subset_interior I hD.isClosed
      (show D ⊆ interior V by simpa [hVOpen.interior_eq] using hDV) with
    ⟨χ, hχOne, hχZero, hχRange⟩
  obtain ⟨N, hNOpen, hDN, hNχ⟩ := mem_nhdsSet_iff_exists.mp hχOne
  let f : M → ℝ := fun x ↦ χ x * g0 x + (1 - χ x) * h x
  have hfSmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := by
    -- Route correction: compactness lets one splice `g0` directly with a positive exhaustion.
    exact (χ.contMDiff.mul hg0.contMDiff).add ((contMDiff_const.sub χ.contMDiff).mul h.contMDiff)
  have hfPosOffD : ∀ x ∉ D, 0 < f x := by
    intro x hxD
    have hg0Pos : 0 < g0 x := by
      have hg0NotNonpos : ¬ g0 x ≤ 0 := by
        intro hg0Nonpos
        exact hxD (by simpa [hD0, Set.mem_preimage, Set.mem_Iic] using hg0Nonpos)
      exact lt_of_not_ge hg0NotNonpos
    have hχNonneg : 0 ≤ χ x := (hχRange x).1
    have hOneSubNonneg : 0 ≤ 1 - χ x := sub_nonneg.mpr (hχRange x).2
    by_cases hχx : χ x = 1
    · -- On the exact-`1` region, the splice is the original zero-level defining function.
      have hFirstPos : 0 < χ x * g0 x := by simpa [hχx] using hg0Pos
      have hSecondNonneg : 0 ≤ (1 - χ x) * h x := by
        exact mul_nonneg hOneSubNonneg (hhPos x).le
      simpa [f] using add_pos_of_pos_of_nonneg hFirstPos hSecondNonneg
    · -- Away from the exact-`1` patch, the positive exhaustion term forces strict positivity.
      have hχLt : χ x < 1 := lt_of_le_of_ne (hχRange x).2 hχx
      have hFirstNonneg : 0 ≤ χ x * g0 x := mul_nonneg hχNonneg hg0Pos.le
      have hSecondPos : 0 < (1 - χ x) * h x := by
        exact mul_pos (sub_pos.mpr hχLt) (hhPos x)
      simpa [f] using add_pos_of_nonneg_of_pos hFirstNonneg hSecondPos
  have hDLevel : D = f ⁻¹' Set.Iic 0 := by
    ext x
    constructor
    · intro hxD
      have hxN : x ∈ N := hDN hxD
      have hχx : χ x = 1 := hNχ hxN
      have hg0Nonpos : g0 x ≤ 0 := by
        simpa [hD0, Set.mem_preimage, Set.mem_Iic] using hxD
      -- On the neighborhood where `χ = 1`, the splice agrees with `g0`.
      simpa [f, hχx] using hg0Nonpos
    · intro hfx
      by_contra hxD
      exact (not_le_of_gt (hfPosOffD x hxD)) hfx
  have hfRegular : Manifold.IsRegularValue I 𝓘(ℝ, ℝ) f 0 := by
    intro x hx0
    have hxD : x ∈ D := by
      have hxLevel : x ∈ f ⁻¹' Set.Iic 0 := by simpa [hx0]
      simpa [hDLevel] using hxLevel
    have hxN : x ∈ N := hDN hxD
    have hEq : f =ᶠ[nhds x] g0 := by
      filter_upwards [hNOpen.mem_nhds hxN] with y hyN
      -- On the open neighborhood where `χ = 1`, the splice is exactly `g0`.
      have hχy : χ y = 1 := hNχ hyN
      simp [f, hχy]
    have hg0x : g0 x = 0 := by
      have hfx : f x = g0 x := hEq.eq_of_nhds
      simpa [hx0] using hfx.symm
    -- Regularity at `0` is local, so it transfers from `g0` on the exact-`1` patch.
    rw [hEq.mfderiv_eq]
    exact hg0Regular x hg0x
  have hfExhaust : Function.IsExhaustionFunction f := by
    refine ⟨hfSmooth.continuous, ?_⟩
    intro c
    refine (hVCompact.union (hhExhaust.isCompact_sublevelSet c)).of_isClosed_subset
      (isClosed_Iic.preimage hfSmooth.continuous) ?_
    intro x hx
    by_cases hxClosureV : x ∈ closure V
    · exact Or.inl hxClosureV
    · have hxNotV : x ∉ V := fun hxV ↦ hxClosureV (subset_closure hxV)
      -- Outside the precompact neighborhood, the cutoff vanishes and the splice is the exhaustion.
      have hfx : f x = h x := by simp [f, hχZero x hxNotV]
      exact Or.inr (by simpa [hfx] using hx)
  refine ⟨f, ?_, hfExhaust⟩
  refine (isDefiningFunction_iff I D f).2 ?_
  refine ⟨hfSmooth, ?_⟩
  exact (isRegularSublevelSet_iff I f D).2 ⟨0, hfRegular, hDLevel⟩

/-- If a compact regular domain `D` lies in a smooth manifold without boundary,
then it admits a defining function that is also an exhaustion function on the ambient manifold. -/
theorem exists_exhaustion_definingFunction_of_isCompact_regularDomain
    {D : Set M} [SmoothManifoldWithBoundary dimM D] [Set.IsRegularDomain I D]
    [T2Space M] [SigmaCompactSpace M] (hD : IsCompact D) :
    ∃ f : M → ℝ, IsDefiningFunction I D f ∧ Function.IsExhaustionFunction f := by
  -- First normalize an arbitrary defining function to level `0`, then defer the compact splice.
  rcases exists_definingFunction_of_isRegularDomain (I := I) (D := D) with ⟨g, hg⟩
  rcases exists_zeroLevelDefiningFunction (I := I) hg with ⟨g0, hg0, hD0, hg0Regular⟩
  exact spliceZeroLevelDefiningWithPositiveExhaustion (I := I) hD hg0 hD0 hg0Regular
