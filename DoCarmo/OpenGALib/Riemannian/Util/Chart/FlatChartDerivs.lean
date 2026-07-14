import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import OpenGALib.Riemannian.TangentBundle.LocallyConstant

/-!
# Tangent bundle — chart-derivative engineering

Flat-codomain (type-erased) chart-derivative wrappers and the framework's
parametric chart-mfderiv smoothness theorems.

The flat-typed wrappers retype the dependent codomain
`E →L[ℝ] TangentSpace I y` to `E →L[ℝ] E` via the def-eq
`TangentSpace I y = E`, hiding the cast. Smoothness statements on
`M → (E →L[ℝ] E)` are the user-facing API; clients never see the
def-eq bridge.

Most helpers are `private` (Layer 1-4 framework infrastructure for
constant-section smoothness, finite-dim continuous linear map lift, and chart-inverse
smoothness via `inverse` composition). The four public theorems are
`continuousLinearMapAtFlat_contMDiffAt`, `symmLFlat_mdifferentiableAt`,
`contMDiff_constSection_TangentSpace` (used by `SmoothVectorField.const`).
-/

open scoped ContDiff Manifold Topology

namespace TangentBundle
/-- **Eng.** Flat-codomain inverse trivialization: `(trivAt x).symmL ℝ y` retyped
as `E →L[ℝ] E` via `TangentSpace I y = E`. -/
noncomputable def symmLFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x y : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x).symmL ℝ y
/-- **Eng.** Flat-codomain forward chart-mfderiv:
`(trivAt x₀).continuousLinearMapAt ℝ y` retyped as `E →L[ℝ] E`. -/
noncomputable def continuousLinearMapAtFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x₀ y : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ y
/-- **Eng.** Flat-codomain `mfderivWithin (range I) (extChartAt I x).symm e₀`. -/
private noncomputable def mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) (e₀ : E) : E →L[ℝ] E :=
  mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) e₀

/-! ### Layer 1 — constant-section smoothness for the tangent bundle -/

/-- **Eng.** Forward chart-mfderiv as a continuous linear map-valued function of basepoint, smooth
at `b₀`. With `IsLocallyConstantChartedSpace`, locally constant on
`chartAt H b₀ = chartAt H b₀`'s neighborhood and equals the identity
continuous linear map via `coordChange_self`. -/
theorem continuousLinearMapAtFlat_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (b₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (continuousLinearMapAtFlat (I := I) (M := M) b₀) b₀ := by
  refine (contMDiffAt_const (c := ContinuousLinearMap.id ℝ E)).congr_of_eventuallyEq ?_
  have h_chart_eq : ∀ᶠ b in 𝓝 b₀, chartAt H b = chartAt H b₀ :=
    chartAt_eventually_eq_of_locallyConstant b₀
  have h_chart_src : (chartAt H b₀).source ∈ 𝓝 b₀ :=
    (chartAt H b₀).open_source.mem_nhds (mem_chart_source H b₀)
  filter_upwards [h_chart_eq, h_chart_src] with b hb_eq hb_src
  show continuousLinearMapAtFlat (I := I) (M := M) b₀ b = ContinuousLinearMap.id ℝ E
  show (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
    = ContinuousLinearMap.id ℝ E
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hb_src]
  have h_achart_eq : achart H b = achart H b₀ := Subtype.ext hb_eq
  rw [h_achart_eq]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H b₀) b
    (by simpa [tangentBundleCore_baseSet] using hb_src) v

private theorem mfderiv_extChartAt_apply_smoothAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (b₀ : M) (v : E) :
    ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun b : M => mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v) b₀ := by
  have h_cLMA := continuousLinearMapAtFlat_contMDiffAt (I := I) (M := M) b₀
  have h_apply : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun b : M => continuousLinearMapAtFlat (I := I) (M := M) b₀ b v) b₀ :=
    h_cLMA.clm_apply contMDiffAt_const
  have h_base : (chartAt H b₀).source ∈ 𝓝 b₀ :=
    (chartAt H b₀).open_source.mem_nhds (mem_chart_source H b₀)
  have h_eq : (fun b : M => continuousLinearMapAtFlat (I := I) (M := M) b₀ b v)
      =ᶠ[𝓝 b₀] (fun b : M => mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v) := by
    filter_upwards [h_base] with b hb
    show (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b v
      = mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hb]
    rfl
  exact h_apply.congr_of_eventuallyEq h_eq.symm

/-- **Math.** Constant-vector tangent section is smooth. For `v : E`, the section
`b ↦ ⟨b, v⟩` (with `v` viewed as fiber via `TangentSpace I b = E`) is
$C^\infty$. Used by `SmoothVectorField.const`. -/
theorem contMDiff_constSection_TangentSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (v : E) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, v⟩ : TangentBundle I M)) := by
  intro b₀
  set e := trivializationAt E (TangentSpace I) b₀ with he_def
  have h_he : (Bundle.TotalSpace.mk b₀ v : TangentBundle I M) ∈ e.source := by
    rw [Bundle.Trivialization.mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' (F := E) b₀
  refine (Bundle.Trivialization.contMDiffAt_iff (IM := I) (IB := I) (e := e)
    (f := fun b : M => (Bundle.TotalSpace.mk b v : TangentBundle I M)) (n := ∞) h_he).mpr ?_
  refine ⟨contMDiffAt_id, ?_⟩
  have h_base : e.baseSet ∈ 𝓝 b₀ :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' b₀)
  have h_eqOn : (fun b : M => (e ⟨b, v⟩).2)
      =ᶠ[𝓝 b₀] (fun b : M => mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v) := by
    filter_upwards [h_base] with b hb
    have hb' : b ∈ (chartAt H b₀).source := by
      rwa [TangentBundle.trivializationAt_baseSet] at hb
    show (e ⟨b, v⟩).2 = mfderiv I 𝓘(ℝ, E) (extChartAt I b₀) b v
    rw [(Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hb v).symm,
        TangentBundle.continuousLinearMapAt_trivializationAt hb']
    rfl
  exact (mfderiv_extChartAt_apply_smoothAt (I := I) (M := M) b₀ v).congr_of_eventuallyEq
    h_eqOn

/-! ### Layer 2 — finite-dim continuous linear map lift -/

/-- **Eng.** Basis decomposition of a continuous linear map-valued family:
`T y = ∑ i, (basis.coord i).smulRight (T y (basis i))`. Pure linear-algebra
identity shared by the `ContMDiffOn`/`MDifferentiableAt` componentwise lifts. -/
theorem continuousLinearMap_of_components_decomp
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {M : Type*}
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (T : M → F₁ →L[𝕜] F₂) {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι 𝕜 F₁) :
    T = fun y => ∑ i, (basis.coord i).toContinuousLinearMap.smulRight (T y (basis i)) := by
  funext y
  ext v
  rw [ContinuousLinearMap.sum_apply]
  have hv : v = ∑ i, basis.repr v i • basis i := by simp
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [ContinuousLinearMap.smulRight_apply,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
    (T y).map_smul]

/-- **Eng.** Componentwise smoothness `(y ↦ T y bᵢ) : M → F₂` lifts to continuous linear map-valued
smoothness `T : M → (F₁ →L[𝕜] F₂)` via basis decomposition. -/
private theorem contMDiffOn_continuousLinearMap_of_components
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
    {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {n : ℕ∞ω}
    (T : M → F₁ →L[𝕜] F₂) {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι 𝕜 F₁) (s : Set M)
    (h_components : ∀ i : ι, ContMDiffOn IM 𝓘(𝕜, F₂) n
      (fun y : M => T y (basis i)) s) :
    ContMDiffOn IM 𝓘(𝕜, F₁ →L[𝕜] F₂) n T s := by
  rw [continuousLinearMap_of_components_decomp T basis]
  apply contMDiffOn_finset_sum
  intro i _
  have h_smulRight : ContMDiff 𝓘(𝕜, F₂) 𝓘(𝕜, F₁ →L[𝕜] F₂) n
      (fun w : F₂ => (basis.coord i).toContinuousLinearMap.smulRight w) := by
    have h_eq : (fun w : F₂ => (basis.coord i).toContinuousLinearMap.smulRight w)
        = ContinuousLinearMap.smulRightL 𝕜 F₁ F₂ (basis.coord i).toContinuousLinearMap := by
      funext w; rfl
    rw [h_eq]
    exact (ContinuousLinearMap.smulRightL 𝕜 F₁ F₂
      (basis.coord i).toContinuousLinearMap).contMDiff
  exact h_smulRight.comp_contMDiffOn (h_components i)

/-! ### Layer 3-4 — chart-mfderiv smoothness on `baseSet` -/

private theorem contMDiffOn_continuousLinearMapAt_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (x₀ : M) (v : E) :
    ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b : M => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b v)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have h_const := contMDiff_constSection_TangentSpace (I := I) (M := M) v
  set e : Bundle.Trivialization E (Bundle.TotalSpace.proj (E := TangentSpace I (M := M))) :=
    trivializationAt E (TangentSpace I) x₀ with he_def
  have h_maps : Set.MapsTo (fun b : M => (⟨b, v⟩ : TangentBundle I M)) e.baseSet e.source :=
    fun b hb => e.mem_source.mpr hb
  have h_iff := e.contMDiffOn_iff (IB := I) (IM := I) (n := ∞)
    (f := fun b : M => (⟨b, v⟩ : TangentBundle I M)) h_maps
  have h_snd : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun b => (e ⟨b, v⟩).2) e.baseSet := (h_iff.mp h_const.contMDiffOn).2
  apply h_snd.congr
  intro b hb
  exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hb v

private theorem contMDiffOn_continuousLinearMapAtFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (continuousLinearMapAtFlat (I := I) (M := M) x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  set basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Module.finBasis ℝ E with h_basis
  apply contMDiffOn_continuousLinearMap_of_components
    (continuousLinearMapAtFlat (I := I) (M := M) x₀)
    basis _
  intro i
  exact contMDiffOn_continuousLinearMapAt_apply x₀ (basis i)

private theorem contMDiffOn_mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (x : M) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (mfderivWithinFlat (I := I) (M := M) x) (extChartAt I x).target := by
  have h_fwd : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (continuousLinearMapAtFlat (I := I) (M := M) x)
      (trivializationAt E (TangentSpace I) x).baseSet :=
    contMDiffOn_continuousLinearMapAtFlat x
  have h_symm : ContMDiffOn 𝓘(ℝ, E) I ∞
      (extChartAt I x).symm (extChartAt I x).target :=
    contMDiffOn_extChartAt_symm x
  have h_maps_to : Set.MapsTo (extChartAt I x).symm
      (extChartAt I x).target
      (trivializationAt E (TangentSpace I) x).baseSet := by
    intro e₀ he₀
    have h_src : (extChartAt I x).symm e₀ ∈ (extChartAt I x).source :=
      PartialEquiv.map_target _ he₀
    rwa [extChartAt_source] at h_src
  have h_compose : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun e₀ => continuousLinearMapAtFlat (I := I) (M := M) x
        ((extChartAt I x).symm e₀))
      (extChartAt I x).target :=
    h_fwd.comp h_symm h_maps_to
  have h_invertible : ∀ e₀ ∈ (extChartAt I x).target,
      (continuousLinearMapAtFlat (I := I) (M := M) x
        ((extChartAt I x).symm e₀)).IsInvertible := by
    intro e₀ he₀
    have h_src : (extChartAt I x).symm e₀ ∈ (extChartAt I x).source :=
      PartialEquiv.map_target _ he₀
    have h_chart_src : (extChartAt I x).symm e₀ ∈ (chartAt H x).source := by
      rwa [extChartAt_source] at h_src
    show ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ
      ((extChartAt I x).symm e₀)).IsInvertible
    rw [TangentBundle.continuousLinearMapAt_trivializationAt h_chart_src]
    exact isInvertible_mfderiv_extChartAt h_src
  have h_inverse_comp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun e₀ => ContinuousLinearMap.inverse
        (continuousLinearMapAtFlat (I := I) (M := M) x
          ((extChartAt I x).symm e₀)))
      (extChartAt I x).target := by
    intro e₀ he₀
    have h_inv_at : (continuousLinearMapAtFlat (I := I) (M := M) x
        ((extChartAt I x).symm e₀)).IsInvertible :=
      h_invertible e₀ he₀
    have h_cd : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
        (continuousLinearMapAtFlat x ((extChartAt I x).symm e₀)) :=
      ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse h_inv_at
    exact h_cd.contMDiffAt.contMDiffWithinAt.comp e₀ (h_compose e₀ he₀) (Set.mapsTo_univ _ _)
  apply h_inverse_comp.congr
  intro e₀ he₀
  show mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) e₀
    = ContinuousLinearMap.inverse
        (continuousLinearMapAtFlat (I := I) (M := M) x ((extChartAt I x).symm e₀))
  have h_chart_src : (extChartAt I x).symm e₀ ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact PartialEquiv.map_target _ he₀
  have h_eq_mfderiv :
      continuousLinearMapAtFlat (I := I) (M := M) x ((extChartAt I x).symm e₀)
        = mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm e₀) := by
    show (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ
        ((extChartAt I x).symm e₀)
      = mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm e₀)
    exact TangentBundle.continuousLinearMapAt_trivializationAt h_chart_src
  rw [h_eq_mfderiv]
  have h_chain := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x) he₀
  have h_chain' := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := x) he₀
  exact (ContinuousLinearMap.inverse_eq h_chain h_chain').symm

private theorem mfderivWithinFlat_mdifferentiableWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (x : M) :
    MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat (I := I) (M := M) x) (Set.range I) (extChartAt I x x) := by
  have h_top_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have h_on : MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat (I := I) (M := M) x) (extChartAt I x).target :=
    (contMDiffOn_mfderivWithinFlat x).mdifferentiableOn h_top_ne_zero
  have h_at_target : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E)
      (mfderivWithinFlat x) (extChartAt I x).target (extChartAt I x x) :=
    h_on _ (mem_extChartAt_target x)
  exact h_at_target.mono_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin x)
private theorem symmLFlat_eventuallyEq_mfderivWithinFlat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) :
    (fun y : M => symmLFlat (I := I) (M := M) x y)
      =ᶠ[𝓝 x]
      (fun y : M => mfderivWithinFlat (I := I) (M := M) x (extChartAt I x y)) := by
  have h_chart_nhds : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h_chart_nhds] with y hy
  show (trivializationAt E (TangentSpace I) x).symmL ℝ y =
    mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) (extChartAt I x y)
  exact TangentBundle.symmL_trivializationAt hy

/-- **Eng.** Smoothness of `symmLFlat` as a map `M → (E →L[ℝ] E)`. The
`TangentSpace I y = E` def-eq is hidden inside the definition. -/
theorem symmLFlat_mdifferentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsLocallyConstantChartedSpace H M]
    (x : M) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => symmLFlat (I := I) (M := M) x y) x := by
  have h_chart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have h_inv := mfderivWithinFlat_mdifferentiableWithinAt (I := I) (M := M) x
  have h_chart_within : MDifferentiableWithinAt I 𝓘(ℝ, E) (extChartAt I x) Set.univ x :=
    h_chart.mdifferentiableWithinAt
  have h_preimage : (extChartAt I x) ⁻¹' Set.range I ∈ 𝓝[Set.univ] x := by
    rw [nhdsWithin_univ]
    refine Filter.mem_of_superset
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)) ?_
    intro y _hy
    rw [Set.mem_preimage, extChartAt_coe]
    exact Set.mem_range_self _
  have h_within : MDifferentiableWithinAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => mfderivWithinFlat (I := I) (M := M) x (extChartAt I x y))
      Set.univ x :=
    h_inv.comp_of_preimage_mem_nhdsWithin _ h_chart_within h_preimage
  have h_comp : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y : M => mfderivWithinFlat (I := I) (M := M) x (extChartAt I x y)) x :=
    mdifferentiableWithinAt_univ.mp h_within
  exact h_comp.congr_of_eventuallyEq
    (symmLFlat_eventuallyEq_mfderivWithinFlat (I := I) (M := M) x)

end TangentBundle
