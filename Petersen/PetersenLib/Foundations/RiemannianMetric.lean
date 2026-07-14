import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import PetersenLib.Foundations.BilinearForm.Basic
import PetersenLib.Foundations.BilinearForm.Riesz
import PetersenLib.Foundations.Attributes

/-!
# Riemannian metric

A smooth, symmetric, positive-definite tensor field $g$ on $M$ assigning
an inner product $g_x : T_xM \times T_xM \to \mathbb{R}$. In PetersenLib,
`RiemannianMetric I M` aliases Mathlib's
`Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)` — i.e., *data*
(structure inhabitant), not a typeclass. Operators take `g` as an
explicit argument; multiple metrics on the same manifold coexist.

Provides `g.metricInner` (bilinear-form algebra), `g.metricRiesz` (Riesz
duality $(T_xM)^* \to T_xM$), their smoothness, and bridge instances on
`TangentSpace I x` (NormedAddCommGroup, InnerProductSpace, FiniteDimensional).

Reference: Petersen §1.1; do Carmo §1.2; Lee, *Smooth Manifolds*, Ch. 13.
Mathlib upstream: `Mathlib.Geometry.Manifold.VectorBundle.Riemannian`.

Vendored from the shared OpenGALib metric core
(`OpenGALib/Riemannian/Metric/RiemannianMetric.lean`, identical in the
openga and DoCarmo projects), with the `Riemannian` namespace renamed to
`PetersenLib` so blueprint `\lean{PetersenLib.*}` anchors resolve.
-/

open Bundle
open scoped ContDiff Manifold Topology Bundle

namespace PetersenLib

/-! ## The metric type -/

/-- **Math.** A **Riemannian metric** on a smooth manifold $M$ modelled
on $(E, H, I)$: a smoothly varying inner product $g_x$ on each tangent
space $T_xM$ (Petersen, Def. of Riemannian manifold, §1.1). Mathlib's
`Bundle.ContMDiffRiemannianMetric` aliased: data, not a typeclass
attribute. -/
abbrev RiemannianMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)

/-- **Math.** **`[HasMetric I M]` typeclass**: thin wrapper around
`RiemannianMetric I M` to make the metric instance-bindable when
downstream code binds `{I : ModelWithCorners ...}` independently of
the manifold's bundled `modelI`. Single-field class. -/
class HasMetric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    where
  /-- The Riemannian metric on $(M, I)$. -/
  metric : RiemannianMetric I M

/-- **Eng.** Bridge: `[HasMetric I M]` induces a global
`Bundle.RiemannianBundle (TangentSpace I : M → Type _)`, activating
Mathlib's scoped `NormedAddCommGroup` and `InnerProductSpace ℝ`
instances on each fibre. Single `NormedAddCommGroup` / `InnerProductSpace` source. -/
noncomputable instance instRiemannianBundleOfHasMetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [hm : HasMetric I M] :
    Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
  ⟨hm.metric.toRiemannianMetric⟩

end PetersenLib

namespace PetersenLib.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Inner product -/

/-- **Math.** The **metric inner product** $\langle V, W\rangle_g = g_x(V, W)$. -/
noncomputable def metricInner (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) : ℝ :=
  g.inner x V W

@[simp]
theorem metricInner_apply (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x V W = g.inner x V W := rfl

/-- **Math.** Symmetry: $\langle V, W\rangle_g = \langle W, V\rangle_g$. -/
theorem metricInner_comm (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x V W = g.metricInner x W V :=
  g.symm x V W

/-- **Math.** Positive-definiteness: $V \ne 0 \Rightarrow \langle V, V\rangle_g > 0$. -/
theorem metricInner_self_pos (g : RiemannianMetric I M)
    (x : M) (V : TangentSpace I x) (hV : V ≠ 0) :
    0 < g.metricInner x V V :=
  g.pos x V hV

@[metric_simp]
theorem metricInner_add_left (g : RiemannianMetric I M)
    (x : M) (V₁ V₂ W : TangentSpace I x) :
    g.metricInner x (V₁ + V₂) W = g.metricInner x V₁ W + g.metricInner x V₂ W := by
  show g.inner x (V₁ + V₂) W = g.inner x V₁ W + g.inner x V₂ W
  rw [(g.inner x).map_add]; rfl

@[metric_simp]
theorem metricInner_add_right (g : RiemannianMetric I M)
    (x : M) (V W₁ W₂ : TangentSpace I x) :
    g.metricInner x V (W₁ + W₂) = g.metricInner x V W₁ + g.metricInner x V W₂ :=
  (g.inner x V).map_add W₁ W₂

@[metric_simp]
theorem metricInner_smul_left (g : RiemannianMetric I M)
    (x : M) (c : ℝ) (V W : TangentSpace I x) :
    g.metricInner x (c • V) W = c * g.metricInner x V W := by
  show g.inner x (c • V) W = c * g.inner x V W
  rw [(g.inner x).map_smul]; rfl

@[metric_simp]
theorem metricInner_smul_right (g : RiemannianMetric I M)
    (x : M) (c : ℝ) (V W : TangentSpace I x) :
    g.metricInner x V (c • W) = c * g.metricInner x V W := by
  show g.inner x V (c • W) = c * g.inner x V W
  rw [(g.inner x V).map_smul]; rfl

@[simp, metric_simp]
theorem metricInner_zero_left (g : RiemannianMetric I M)
    (x : M) (W : TangentSpace I x) :
    g.metricInner x 0 W = 0 := by
  show g.inner x 0 W = 0
  rw [(g.inner x).map_zero]; rfl

@[simp, metric_simp]
theorem metricInner_zero_right (g : RiemannianMetric I M)
    (x : M) (V : TangentSpace I x) :
    g.metricInner x V 0 = 0 :=
  (g.inner x V).map_zero

@[simp, metric_simp]
theorem metricInner_neg_left (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x (-V) W = -g.metricInner x V W := by
  show g.inner x (-V) W = -g.inner x V W
  rw [(g.inner x).map_neg]; rfl

@[simp, metric_simp]
theorem metricInner_neg_right (g : RiemannianMetric I M)
    (x : M) (V W : TangentSpace I x) :
    g.metricInner x V (-W) = -g.metricInner x V W :=
  (g.inner x V).map_neg W

@[simp, metric_simp]
theorem metricInner_sub_left (g : RiemannianMetric I M)
    (x : M) (V₁ V₂ W : TangentSpace I x) :
    g.metricInner x (V₁ - V₂) W = g.metricInner x V₁ W - g.metricInner x V₂ W := by
  show g.inner x (V₁ - V₂) W = g.inner x V₁ W - g.inner x V₂ W
  rw [(g.inner x).map_sub]; rfl

@[simp, metric_simp]
theorem metricInner_sub_right (g : RiemannianMetric I M)
    (x : M) (V W₁ W₂ : TangentSpace I x) :
    g.metricInner x V (W₁ - W₂) = g.metricInner x V W₁ - g.metricInner x V W₂ :=
  (g.inner x V).map_sub W₁ W₂

/-- **Math.** $\langle V, V\rangle_g \ge 0$ for any $V$. -/
@[simp, metric_simp]
theorem metricInner_self_nonneg (g : RiemannianMetric I M)
    (x : M) (V : TangentSpace I x) :
    0 ≤ g.metricInner x V V := by
  rcases eq_or_ne V 0 with hV | hV
  · rw [hV, g.metricInner_zero_left]
  · exact le_of_lt (g.metricInner_self_pos x V hV)

end PetersenLib.RiemannianMetric

/-! ## TangentSpace fibre instances

`NormedAddCommGroup`, `NormedSpace`, and `InnerProductSpace` on each
fibre `TangentSpace I x` are *not* declared here. Instead, they are
supplied by Mathlib's scoped `Bundle.RiemannianBundle`-derived
instances, which become active once a `RiemannianBundle E` is in scope
(e.g., via the global instance from `[HasMetric I M]`, or via a
local `letI`). Routing through `RiemannianBundle` ensures that the
inner product the Mathlib `inner` projection lands on is *exactly*
`g.inner b · ·`, sidestepping the lean4#13063 `NormedAddCommGroup` diamond.

The non-metric fibre instance `FiniteDimensional` is orthogonal to the
`NormedAddCommGroup` / `InnerProductSpace` chain and is transported here
via the `TangentSpace I x = E` def-eq. -/

namespace PetersenLib

section TangentSpaceInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

instance instFiniteDimensionalTangent [FiniteDimensional ℝ E] (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) := by
  show FiniteDimensional ℝ E
  infer_instance

end TangentSpaceInstances

end PetersenLib

/-! ## Riesz duality

In a finite-dim inner product space $V$, every continuous linear functional
$\varphi : V \to \mathbb{R}$ is uniquely represented as $\langle V_\varphi, \cdot\rangle_g$. -/

namespace PetersenLib.RiemannianMetric

section Riesz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Eng.** Bridge from the metric's continuous bilinear form to the
algebraic-core `BilinearForm.Form ℝ E`. -/
private noncomputable def toBilinForm (g : RiemannianMetric I M) (x : M) :
    BilinearForm.Form ℝ E :=
  LinearMap.mk₂ ℝ
    (fun v w => g.inner x v w)
    (fun v₁ v₂ w => by
      simp only [show g.inner x (v₁ + v₂) = g.inner x v₁ + g.inner x v₂
        from (g.inner x).map_add v₁ v₂, ContinuousLinearMap.add_apply])
    (fun c v w => by
      simp only [show g.inner x (c • v) = c • g.inner x v
        from (g.inner x).map_smul c v, ContinuousLinearMap.smul_apply])
    (fun v w₁ w₂ => (g.inner x v).map_add w₁ w₂)
    (fun c v w => (g.inner x v).map_smul c w)

omit [FiniteDimensional ℝ E] in
private theorem toBilinForm_isPosDef (g : RiemannianMetric I M) (x : M) :
    BilinearForm.IsPosDef (g.toBilinForm x) := by
  intro v hv
  show 0 < g.inner x v v
  exact g.pos x v hv

/-- **Math.** Forward Riesz $V \mapsto g_x(V, \cdot)$. -/
noncomputable def metricToDual (g : RiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  g.inner x

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricToDual_apply (g : RiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.metricToDual x v w = g.metricInner x v w := rfl

omit [FiniteDimensional ℝ E] in
theorem metricToDual_injective (g : RiemannianMetric I M) (x : M) :
    Function.Injective (g.metricToDual x) := by
  intro v₁ v₂ h
  apply BilinearForm.toDual_injective (g.toBilinForm_isPosDef x)
  ext w
  show g.inner x v₁ w = g.inner x v₂ w
  exact congrArg (fun (f : TangentSpace I x →L[ℝ] ℝ) => f w) h

omit [FiniteDimensional ℝ E] in
/-- **Math.** Non-degeneracy: vectors with equal inner-products against everything are equal. -/
theorem metricInner_eq_iff_eq (g : RiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    (∀ Z : TangentSpace I x, g.metricInner x v Z = g.metricInner x w Z) ↔ v = w :=
  BilinearForm.inner_eq_iff_eq (g.toBilinForm_isPosDef x) v w

/-- **Math.** Inverse Riesz $\varphi \mapsto V_\varphi$ such that $g_x(V_\varphi, W) = \varphi(W)$.

Constructed via the algebraic-core `BilinearForm.riesz` applied to the
`LinearMap` coercion of the continuous functional. -/
noncomputable def metricRiesz (g : RiemannianMetric I M) (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x :=
  BilinearForm.riesz (g.toBilinForm_isPosDef x)
    ((φ : TangentSpace I x →ₗ[ℝ] ℝ))

/-- **Math.** Defining property of Riesz: $\langle \text{metricRiesz}\,\varphi, W\rangle_g = \varphi(W)$. -/
@[simp]
theorem metricRiesz_inner (g : RiemannianMetric I M) (x : M)
    (φ : TangentSpace I x →L[ℝ] ℝ) (V : TangentSpace I x) :
    g.metricInner x (g.metricRiesz x φ) V = φ V :=
  BilinearForm.riesz_inner (g.toBilinForm_isPosDef x)
    ((φ : TangentSpace I x →ₗ[ℝ] ℝ)) V

/-- **Math.** Uniqueness: if $g_x(V, \cdot) = \varphi$, then $V = \text{metricRiesz}\,\varphi$. -/
theorem metricRiesz_unique (g : RiemannianMetric I M) (x : M)
    (v : TangentSpace I x) (φ : TangentSpace I x →L[ℝ] ℝ)
    (h : ∀ w, g.metricInner x v w = φ w) :
    v = g.metricRiesz x φ :=
  BilinearForm.riesz_unique (g.toBilinForm_isPosDef x) v
    ((φ : TangentSpace I x →ₗ[ℝ] ℝ)) h

theorem metricToDual_bijective (g : RiemannianMetric I M) (x : M) :
    Function.Bijective (g.metricToDual x) := by
  refine ⟨g.metricToDual_injective x, ?_⟩
  intro φ
  refine ⟨g.metricRiesz x φ, ?_⟩
  ext v
  exact g.metricRiesz_inner x φ v

/-- **Math.** The Riesz isomorphism `T_xM ≃ₗ[ℝ] (T_xM →L[ℝ] ℝ)`, built directly
from `metricToDual` and its bijectivity. The forward map is
`v ↦ g.inner x v` (the metric-induced continuous functional); the inverse
is `g.metricRiesz x`. -/
noncomputable def metricToDualEquiv (g : RiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  LinearEquiv.ofBijective (g.metricToDual x).toLinearMap (g.metricToDual_bijective x)

end Riesz

end PetersenLib.RiemannianMetric

/-! ## Smoothness of the metric inner product — Math headline

`g_y(v(y), w(y))` is `ContMDiffWithinAt` whenever the tangent-bundle
sections `v, w` are. -/

namespace PetersenLib.RiemannianMetric

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {v w : ∀ x : M, TangentSpace I x} {s : Set M} {x : M}

variable {n : ℕ∞ω} [hLE : ENat.LEInfty n]

/-- **Math.** $\langle v(\cdot), w(\cdot)\rangle_g$ is `ContMDiffWithinAt` whenever
the tangent-bundle sections `v`, `w` are. -/
theorem metricInner_contMDiffWithinAt
    (g : RiemannianMetric I M)
    (hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) s x)
    (hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) n
      (fun y => (⟨y, w y⟩ : TangentBundle I M)) s x) :
    ContMDiffWithinAt I 𝓘(ℝ, ℝ) n
      (fun y => g.metricInner y (v y) (w y)) s x := by
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ContMDiffWithinAt.inner_bundle (IB := I) (F := E)
    (E := (TangentSpace I : M → Type _)) (b := fun y => y)
    (v := v) (w := w) (IM := I) hv hw

end Smoothness

end PetersenLib.RiemannianMetric
