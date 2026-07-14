import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import OpenGALib.Riemannian.TangentBundle.LocallyConstant
import OpenGALib.Riemannian.Util.Chart.FlatChartDerivs

/-!
# Tangent bundle smoothness API

Smoothness of tangent vector fields and chart-frame derivatives. The
file collects:

* `IsLocallyConstantChartedSpace` — chart-coherence typeclass needed for
  parametric chart-mfderiv smoothness.
* `TangentSmoothAt` + closure under the $C^\infty(M)$-module operations.
* Flat-codomain chart-frame trivializations `symmLFlat`,
  `continuousLinearMapAtFlat` and their basepoint smoothness.
* Bundled smooth vector fields `SmoothVectorField`.
* Chart-frame `mfderiv` smoothness in constant and smoothly-varying
  directions.

Reference: Lee, *Smooth Manifolds*, Ch. 8 and Ch. 11.
-/

open scoped ContDiff Manifold Topology

-- `IsLocallyConstantChartedSpace` typeclass + chart-constancy lemma +
-- strict-interior nbhd propagation live in
-- `TangentBundle/LocallyConstant.lean`.
-- Flat-codomain chart-derivative wrappers + parametric chart-mfderiv
-- smoothness live in `Util/FlatChartDerivs.lean`.

/-! ## Tangent vector field smoothness predicate

`TangentSmoothAt V x` is the framework's canonical smoothness predicate
for tangent sections, equivalent to the bundle-form
`MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y ↦ ⟨y, V y⟩) x` but
opaque to elaborator unfolding for tactic-search performance.
-/

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The section $V \colon M \to TM$ is **smooth at $x$**:
$y \mapsto \langle y, V(y)\rangle$ is `MDifferentiableAt` at $x$ as a
map $M \to TM$. -/
def TangentSmoothAt (V : (y : M) → TangentSpace I y) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E))
    (fun y => (⟨y, V y⟩ : TangentBundle I M)) x

namespace TangentSmoothAt

theorem mk {V : (y : M) → TangentSpace I y} {x : M}
    (h : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) x) :
    TangentSmoothAt V x := h

theorem toBundleSection {V : (y : M) → TangentSpace I y} {x : M}
    (h : TangentSmoothAt V x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => (⟨y, V y⟩ : TangentBundle I M)) x := h

/-- **Eng.** Chart-coordinate form: `y ↦ (trivAt x ⟨y, V y⟩).2 : M → E` is smooth. -/
theorem coordSmoothAt {V : (y : M) → TangentSpace I y} {x : M}
    (hV : TangentSmoothAt V x) :
    MDifferentiableAt I 𝓘(ℝ, E)
      (fun y => ((trivializationAt E (TangentSpace I) x) ⟨y, V y⟩).2) x := by
  have h := hV.toBundleSection
  rw [mdifferentiableAt_totalSpace] at h
  exact h.2

theorem iff_coord {V : (y : M) → TangentSpace I y} {x : M} :
    TangentSmoothAt V x ↔
      MDifferentiableAt I 𝓘(ℝ, E)
        (fun y => ((trivializationAt E (TangentSpace I) x) ⟨y, V y⟩).2) x := by
  unfold TangentSmoothAt
  rw [mdifferentiableAt_totalSpace]
  exact ⟨And.right, fun h => ⟨mdifferentiableAt_id, h⟩⟩

/-- **Math.** The zero vector field is smooth. -/
theorem zero (x : M) : TangentSmoothAt (fun y : M => (0 : TangentSpace I y)) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  apply (mdifferentiableAt_const (c := (0 : E))).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, (0 : TangentSpace I y)⟩).2 = (0 : E)
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  exact map_zero _

theorem add {Y Z : (y : M) → TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    TangentSmoothAt (Y + Z) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  have hY' := hY.coordSmoothAt
  have hZ' := hZ.coordSmoothAt
  apply (hY'.add hZ').congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, (Y + Z) y⟩).2 = (e ⟨y, Y y⟩).2 + (e ⟨y, Z y⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  show (e.continuousLinearMapAt ℝ y) ((Y + Z) y)
      = (e.continuousLinearMapAt ℝ y) (Y y) + (e.continuousLinearMapAt ℝ y) (Z y)
  show (e.continuousLinearMapAt ℝ y) (Y y + Z y)
      = (e.continuousLinearMapAt ℝ y) (Y y) + (e.continuousLinearMapAt ℝ y) (Z y)
  exact ContinuousLinearMap.map_add _ _ _

theorem neg {V : (y : M) → TangentSpace I y} {x : M}
    (hV : TangentSmoothAt V x) :
    TangentSmoothAt (-V) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  have hV' := hV.coordSmoothAt
  apply hV'.neg.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, (-V) y⟩).2 = -(e ⟨y, V y⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  show (e.continuousLinearMapAt ℝ y) ((-V) y) = -(e.continuousLinearMapAt ℝ y) (V y)
  show (e.continuousLinearMapAt ℝ y) (-V y) = -(e.continuousLinearMapAt ℝ y) (V y)
  exact ContinuousLinearMap.map_neg _ _

theorem sub {Y Z : (y : M) → TangentSpace I y} {x : M}
    (hY : TangentSmoothAt Y x) (hZ : TangentSmoothAt Z x) :
    TangentSmoothAt (Y - Z) x := by
  have h_eq : (Y - Z : (y : M) → TangentSpace I y) = Y + (-Z) := by
    funext y
    show Y y - Z y = Y y + -Z y
    exact sub_eq_add_neg _ _
  rw [h_eq]
  exact hY.add hZ.neg

theorem smul {f : M → ℝ} {V : (y : M) → TangentSpace I y} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hV : TangentSmoothAt V x) :
    TangentSmoothAt (fun y => f y • V y) x := by
  rw [TangentSmoothAt.iff_coord]
  set e := trivializationAt E (TangentSpace I) x
  have hV' := hV.coordSmoothAt
  apply (hf.smul hV').congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  show (e ⟨y, f y • V y⟩).2 = f y • (e ⟨y, V y⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy,
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hy]
  show (e.continuousLinearMapAt ℝ y) (f y • V y)
      = f y • (e.continuousLinearMapAt ℝ y) (V y)
  exact ContinuousLinearMap.map_smul _ _ _

end TangentSmoothAt

end Riemannian

-- Flat-codomain chart-derivative wrappers (`symmLFlat`,
-- `continuousLinearMapAtFlat`, `mfderivWithinFlat`) and their basepoint
-- smoothness theorems live in `Util/FlatChartDerivs.lean`.
-- They are reachable through the import above.


/-! ## Bundled smooth vector fields

`SmoothVectorField I M` packages a tangent section with its $C^\infty$
smoothness witness. Algebraic operations (zero, add, sub, neg, smul,
constant section) are defined; clients use the bundled type to avoid
threading `ContMDiff` premises through every theorem.
-/

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A (not necessarily smooth) section of the tangent bundle:
the pointwise data assigning a tangent vector to each base point. Thin
abbreviation over the dependent product `Π y : M, TangentSpace I y` for
signature readability. `SmoothVectorField` adds a smoothness witness on
top. -/
abbrev VectorFieldSection (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] : Type _ :=
  Π y : M, TangentSpace I y

/-- **Math.** A smooth tangent vector field on `M`. -/
structure SmoothVectorField (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- Underlying tangent section. -/
  toFun : Π y : M, TangentSpace I y
  /-- Smoothness of the bundle section. -/
  smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
    (fun y => (⟨y, toFun y⟩ : TangentBundle I M))

namespace SmoothVectorField

instance : CoeFun (SmoothVectorField I M) fun _ => Π y : M, TangentSpace I y :=
  ⟨toFun⟩

@[simp] lemma coe_mk (f : Π y : M, TangentSpace I y) (h) :
    ⇑(⟨f, h⟩ : SmoothVectorField I M) = f := rfl

theorem smoothAt (X : SmoothVectorField I M) (x : M) : TangentSmoothAt X x :=
  TangentSmoothAt.mk ((X.smooth x).mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))

noncomputable def zero : SmoothVectorField I M where
  toFun := fun _ => 0
  smooth := Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M)) (n := ∞)

noncomputable instance : Zero (SmoothVectorField I M) := ⟨zero⟩

@[simp] lemma zero_apply (y : M) : (0 : SmoothVectorField I M) y = 0 := rfl

noncomputable def add (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => X y + Y y
  smooth := ContMDiff.add_section X.smooth Y.smooth

noncomputable instance : Add (SmoothVectorField I M) := ⟨add⟩

@[simp] lemma add_apply (X Y : SmoothVectorField I M) (y : M) :
    (X + Y) y = X y + Y y := rfl

noncomputable def neg (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => -X y
  smooth := ContMDiff.neg_section X.smooth

noncomputable instance : Neg (SmoothVectorField I M) := ⟨neg⟩

@[simp] lemma neg_apply (X : SmoothVectorField I M) (y : M) :
    (-X) y = -X y := rfl

noncomputable def sub (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => X y - Y y
  smooth := ContMDiff.sub_section X.smooth Y.smooth

noncomputable instance : Sub (SmoothVectorField I M) := ⟨sub⟩

@[simp] lemma sub_apply (X Y : SmoothVectorField I M) (y : M) :
    (X - Y) y = X y - Y y := rfl

noncomputable def constSMul (a : ℝ) (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => a • X y
  smooth := ContMDiff.const_smul_section (a := a) X.smooth

noncomputable instance : SMul ℝ (SmoothVectorField I M) := ⟨constSMul⟩

@[simp] lemma constSMul_apply (a : ℝ) (X : SmoothVectorField I M) (y : M) :
    (a • X) y = a • X y := by
  show (constSMul a X) y = a • X y; rfl

/-- **Math.** Smooth-scalar-function multiplication `f • X` for `f : M → ℝ` smooth. -/
noncomputable def smul (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun y => f y • X y
  smooth := ContMDiff.smul_section hf X.smooth

@[simp] lemma smul_apply (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : SmoothVectorField I M) (y : M) :
    (smul f hf X) y = f y • X y := rfl

/-- **Math.** Constant `E`-valued section as a `SmoothVectorField`. -/
noncomputable def const [_root_.IsLocallyConstantChartedSpace H M] (v : E) :
    SmoothVectorField I M where
  toFun := fun _ => v
  smooth := TangentBundle.contMDiff_constSection_TangentSpace v

@[simp] lemma const_apply [_root_.IsLocallyConstantChartedSpace H M] (v : E) (y : M) :
    (const (I := I) v) y = v := rfl

end SmoothVectorField

end Riemannian

/-! ## `mfderiv` smoothness in chart-frame directions

For a globally smooth scalar $f : M \to \mathbb{R}$ and either a
constant direction $v : E$ or a smoothly-varying direction $V : M \to E$,
the function $y \mapsto \mathrm{d}f_y(V(y))$ is smooth at every point.

These are boundary-agnostic: the chart-pullback formula
$\mathrm{d}f_y = \mathrm{fderivWithin}_{\mathrm{range}\, I}(f \circ
\mathrm{chart.symm})$ combined with `IsLocallyConstantChartedSpace`
(which makes `extChartAt I y = extChartAt I x` constant on a
neighborhood of `x`) lifts $C^\infty$ regularity from the chart side
to the manifold side via `comp_of_preimage_mem_nhdsWithin`.
-/

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- **Math.** Smoothness of $y \mapsto \mathrm{d}f_y(v)$ for chart-frame-constant $v$. -/
theorem mfderiv_const_dir_smoothAt
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) (v : E) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => mfderiv I 𝓘(ℝ, ℝ) f y v) x := by
  have h_symm_within : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
      (Set.range I) (extChartAt I x x) :=
    contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target x)
  have h_eqx : (extChartAt I x).symm (extChartAt I x x) = x := by simp
  have h_comp_within : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (f ∘ (extChartAt I x).symm) (Set.range I) (extChartAt I x x) :=
    (hf x).comp_contMDiffWithinAt_of_eq h_symm_within h_eqx
  have h_f_hat : ContDiffWithinAt ℝ ∞ (f ∘ (extChartAt I x).symm) (Set.range I)
      (extChartAt I x x) :=
    h_comp_within.contDiffWithinAt
  have h_unique : UniqueDiffOn ℝ (Set.range (I : H → E)) := I.uniqueDiffOn
  have h_mem : extChartAt I x x ∈ Set.range (I : H → E) := Set.mem_range_self _
  have h_fderiv_within : ContDiffWithinAt ℝ ∞
      (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I))
      (Set.range I) (extChartAt I x x) :=
    h_f_hat.fderivWithin_right h_unique (le_refl _) h_mem
  have h_fderiv_apply_within : ContDiffWithinAt ℝ ∞
      (fun e₀ : E => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I) e₀ v)
      (Set.range I) (extChartAt I x x) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt.contDiffWithinAt.comp
      (extChartAt I x x) h_fderiv_within (Set.mapsTo_univ _ _)
  have h_fderiv_mdiff_within : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (fun e₀ : E => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I) e₀ v)
      (Set.range I) (extChartAt I x x) :=
    h_fderiv_apply_within.contMDiffWithinAt.mdifferentiableWithinAt (by decide)
  have h_chart_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x : M → E) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have h_chart_within : MDifferentiableWithinAt I 𝓘(ℝ, E)
      (extChartAt I x) Set.univ x :=
    h_chart_mdiff.mdifferentiableWithinAt
  have h_preimage : (extChartAt I x) ⁻¹' Set.range I ∈ 𝓝[Set.univ] x := by
    rw [nhdsWithin_univ]
    refine Filter.mem_of_superset
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)) ?_
    intro y _hy
    rw [Set.mem_preimage, extChartAt_coe]
    exact Set.mem_range_self _
  have h_fderiv_compose_within : MDifferentiableWithinAt I 𝓘(ℝ, ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y) v)
      Set.univ x :=
    h_fderiv_mdiff_within.comp_of_preimage_mem_nhdsWithin _ h_chart_within h_preimage
  have h_fderiv_at : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y) v) x :=
    mdifferentiableWithinAt_univ.mp h_fderiv_compose_within
  apply h_fderiv_at.congr_of_eventuallyEq
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have h_top_ne : (∞ : ℕ∞ω) ≠ 0 := by decide
  filter_upwards [h_chart_eq, h_chart_src] with y hy_chart hy_src
  have hf_at_y : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    (hf y).mdifferentiableAt h_top_ne
  have h_extChart_eq : extChartAt I y = extChartAt I x := by
    show (chartAt H y).extend I = (chartAt H x).extend I
    rw [hy_chart]
  show mfderiv I 𝓘(ℝ, ℝ) f y v
      = fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
          ((extChartAt I x) y) v
  rw [hf_at_y.mfderiv]
  have h_written :
      writtenInExtChartAt I 𝓘(ℝ, ℝ) y f = f ∘ (extChartAt I x).symm := by
    funext z
    show (extChartAt 𝓘(ℝ, ℝ) (f y)) (f ((extChartAt I y).symm z))
        = f ((extChartAt I x).symm z)
    rw [h_extChart_eq]
    rfl
  rw [h_written, h_extChart_eq]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- **Math.** Smoothness of $y \mapsto \mathrm{d}f_y(V(y))$ for smoothly-varying $V : M \to E$. -/
theorem mfderiv_smoothDir_smoothAt
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    {V : M → E} (hV : ContMDiffAt I 𝓘(ℝ, E) ∞ V x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => mfderiv I 𝓘(ℝ, ℝ) f y (V y)) x := by
  have h_symm_within : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
      (Set.range I) (extChartAt I x x) :=
    contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target x)
  have h_eqx : (extChartAt I x).symm (extChartAt I x x) = x := by simp
  have h_comp_within : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (f ∘ (extChartAt I x).symm) (Set.range I) (extChartAt I x x) :=
    (hf x).comp_contMDiffWithinAt_of_eq h_symm_within h_eqx
  have h_f_hat : ContDiffWithinAt ℝ ∞ (f ∘ (extChartAt I x).symm) (Set.range I)
      (extChartAt I x x) :=
    h_comp_within.contDiffWithinAt
  have h_unique : UniqueDiffOn ℝ (Set.range (I : H → E)) := I.uniqueDiffOn
  have h_mem : extChartAt I x x ∈ Set.range (I : H → E) := Set.mem_range_self _
  have h_fderiv_within : ContDiffWithinAt ℝ ∞
      (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I))
      (Set.range I) (extChartAt I x x) :=
    h_f_hat.fderivWithin_right h_unique (le_refl _) h_mem
  have h_fderiv_mdiff_within : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] ℝ)
      (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I))
      (Set.range I) (extChartAt I x x) :=
    h_fderiv_within.contMDiffWithinAt.mdifferentiableWithinAt (by decide)
  have h_chart_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x : M → E) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  have h_chart_within : MDifferentiableWithinAt I 𝓘(ℝ, E)
      (extChartAt I x) Set.univ x :=
    h_chart_mdiff.mdifferentiableWithinAt
  have h_preimage : (extChartAt I x) ⁻¹' Set.range I ∈ 𝓝[Set.univ] x := by
    rw [nhdsWithin_univ]
    refine Filter.mem_of_superset
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)) ?_
    intro y _hy
    rw [Set.mem_preimage, extChartAt_coe]
    exact Set.mem_range_self _
  have h_fderiv_compose_within : MDifferentiableWithinAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y))
      Set.univ x :=
    h_fderiv_mdiff_within.comp_of_preimage_mem_nhdsWithin _ h_chart_within h_preimage
  have h_fderiv_at : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y)) x :=
    mdifferentiableWithinAt_univ.mp h_fderiv_compose_within
  have hV_mdiff : MDifferentiableAt I 𝓘(ℝ, E) V x :=
    hV.mdifferentiableAt (by decide)
  have h_compose : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
        ((extChartAt I x) y) (V y)) x :=
    h_fderiv_at.clm_apply hV_mdiff
  apply h_compose.congr_of_eventuallyEq
  have h_chart_eq : ∀ᶠ y in 𝓝 x, chartAt H y = chartAt H x :=
    chartAt_eventually_eq_of_locallyConstant x
  have h_chart_src : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have h_top_ne : (∞ : ℕ∞ω) ≠ 0 := by decide
  filter_upwards [h_chart_eq, h_chart_src] with y hy_chart hy_src
  have hf_at_y : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    (hf y).mdifferentiableAt h_top_ne
  have h_extChart_eq : extChartAt I y = extChartAt I x := by
    show (chartAt H y).extend I = (chartAt H x).extend I
    rw [hy_chart]
  show mfderiv I 𝓘(ℝ, ℝ) f y (V y)
      = fderivWithin ℝ (f ∘ (extChartAt I x).symm) (Set.range I)
          ((extChartAt I x) y) (V y)
  rw [hf_at_y.mfderiv]
  have h_written :
      writtenInExtChartAt I 𝓘(ℝ, ℝ) y f = f ∘ (extChartAt I x).symm := by
    funext z
    show (extChartAt 𝓘(ℝ, ℝ) (f y)) (f ((extChartAt I y).symm z))
        = f ((extChartAt I x).symm z)
    rw [h_extChart_eq]
    rfl
  rw [h_written, h_extChart_eq]
  rfl

end Riemannian
