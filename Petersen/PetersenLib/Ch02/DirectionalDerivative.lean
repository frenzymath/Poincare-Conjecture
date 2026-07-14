import PetersenLib.Foundations.RiemannianMetric
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Petersen Ch. 2, §2.1.1 — Directional derivatives and the gradient

The directional derivative `D_Y f = df(Y)` of a function along a vector
field (`directionalDerivative`), its pointwise algebra (linearity in the
direction, linearity and the Leibniz rule in the function), and the
gradient `∇f` of a function on a Riemannian manifold, defined through
the Riesz duality of Ch. 1 by `g(∇f, v) = df(v)` (`gradient`,
`metricInner_gradient`, `gradient_unique`).

## Design notes

* A vector field is a dependent function `Y : Π x : M, TangentSpace I x`
  (Mathlib's convention for `VectorField.mlieBracket` etc.); no bundling.
* `directionalDerivative Y f x = mfderiv I 𝓘(ℝ) f x (Y x)`. Petersen
  writes this interchangeably as `∇_Y f = D_Y f = L_Y f = df(Y) = Y(f)`.
* The gradient is `metricRiesz` applied to `mfderiv`; its defining
  property and uniqueness are inherited from the Ch. 1 Riesz API.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.1.1.
-/

open Bundle Set Function
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Eng.** A vector field (a dependent function `Π x, TangentSpace I x`) is
*smooth* when the associated section of the tangent bundle is `C^∞`. This is the
unbundled counterpart of the bundled `SmoothVectorField` structure of the
vendored OpenGA infrastructure. -/
def IsSmoothVectorField (X : Π x : M, TangentSpace I x) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => (⟨x, X x⟩ : TangentBundle I M))

/-! ## The directional derivative -/

/-- **Math.** The **directional derivative** of `f : M → ℝ` in the direction of
the vector field `Y`, written interchangeably `∇_Y f = D_Y f = L_Y f = df(Y) = Y(f)`
(Petersen §2.1.1). -/
def directionalDerivative (Y : Π x : M, TangentSpace I x) (f : M → ℝ) (x : M) : ℝ :=
  mfderiv I 𝓘(ℝ) f x (Y x)

omit [IsManifold I ∞ M] in
@[simp]
theorem directionalDerivative_apply (Y : Π x : M, TangentSpace I x) (f : M → ℝ) (x : M) :
    directionalDerivative Y f x = mfderiv I 𝓘(ℝ) f x (Y x) := rfl

/-! ### Tensoriality in the direction -/

omit [IsManifold I ∞ M] in
theorem directionalDerivative_add_left (Y Z : Π x : M, TangentSpace I x) (f : M → ℝ) (x : M) :
    directionalDerivative (fun x => Y x + Z x) f x =
      directionalDerivative Y f x + directionalDerivative Z f x :=
  (mfderiv I 𝓘(ℝ) f x).map_add (Y x) (Z x)

omit [IsManifold I ∞ M] in
/-- `D_{hY} f = h · D_Y f`: the directional derivative is `C^∞(M)`-linear (tensorial)
in the direction. -/
theorem directionalDerivative_smul_left (h : M → ℝ) (Y : Π x : M, TangentSpace I x)
    (f : M → ℝ) (x : M) :
    directionalDerivative (fun x => h x • Y x) f x = h x * directionalDerivative Y f x :=
  (mfderiv I 𝓘(ℝ) f x).map_smul (h x) (Y x)

omit [IsManifold I ∞ M] in
theorem directionalDerivative_neg_left (Y : Π x : M, TangentSpace I x) (f : M → ℝ) (x : M) :
    directionalDerivative (fun x => -Y x) f x = -directionalDerivative Y f x :=
  (mfderiv I 𝓘(ℝ) f x).map_neg (Y x)

omit [IsManifold I ∞ M] in
@[simp]
theorem directionalDerivative_zero_left (f : M → ℝ) (x : M) :
    directionalDerivative (fun x => (0 : TangentSpace I x)) f x = 0 :=
  (mfderiv I 𝓘(ℝ) f x).map_zero

omit [IsManifold I ∞ M] in
/-- The directional derivative at `x` only involves the value `Y x` of the direction. -/
theorem directionalDerivative_congr_left {Y Z : Π x : M, TangentSpace I x} {x : M}
    (h : Y x = Z x) (f : M → ℝ) :
    directionalDerivative Y f x = directionalDerivative Z f x :=
  congrArg (fun v => mfderiv I 𝓘(ℝ) f x v) h

/-! ### Derivation properties in the function -/

omit [IsManifold I ∞ M] in
theorem directionalDerivative_add {f g : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (Y : Π x : M, TangentSpace I x) :
    directionalDerivative Y (f + g) x =
      directionalDerivative Y f x + directionalDerivative Y g x :=
  congrArg (fun L => L (Y x)) (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv

omit [IsManifold I ∞ M] in
/-- **Math.** Leibniz rule: `D_Y(f·g) = f·D_Y g + g·D_Y f`. -/
theorem directionalDerivative_mul {f g : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (Y : Π x : M, TangentSpace I x) :
    directionalDerivative Y (f * g) x =
      f x * directionalDerivative Y g x + g x * directionalDerivative Y f x := by
  have h := congrArg (fun L => L (Y x)) (hf.hasMFDerivAt.mul' hg.hasMFDerivAt).mfderiv
  calc directionalDerivative Y (f * g) x
      = f x * directionalDerivative Y g x + directionalDerivative Y f x * g x := h
    _ = f x * directionalDerivative Y g x + g x * directionalDerivative Y f x := by ring

omit [IsManifold I ∞ M] in
theorem directionalDerivative_sub {f g : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (Y : Π x : M, TangentSpace I x) :
    directionalDerivative Y (f - g) x =
      directionalDerivative Y f x - directionalDerivative Y g x :=
  congrArg (fun L => L (Y x)) (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv

theorem directionalDerivative_const (Y : Π x : M, TangentSpace I x) (c : ℝ) (x : M) :
    directionalDerivative Y (fun _ => c) x = 0 := by
  rw [directionalDerivative_apply, mfderiv_const]
  rfl

theorem directionalDerivative_const_smul {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (c : ℝ) (Y : Π x : M, TangentSpace I x) :
    directionalDerivative Y (fun x => c * f x) x = c * directionalDerivative Y f x := by
  have h1 : (fun x => c * f x) = c • f := rfl
  rw [directionalDerivative_apply, h1]
  exact congrArg (fun L => L (Y x)) ((hf.hasMFDerivAt.const_smul c).mfderiv)

/-! ## The gradient -/

section Gradient

variable [FiniteDimensional ℝ E]

/-- **Math.** The **gradient** `∇f = grad f` of `f : (M, g) → ℝ`: the vector field
with `g(∇f, v) = df(v)` for all `v ∈ TM` (Petersen §2.1.1), obtained from `df`
through the Riesz duality of the metric. -/
def gradient (g : RiemannianMetric I M) (f : M → ℝ) (x : M) : TangentSpace I x :=
  g.metricRiesz x (mfderiv I 𝓘(ℝ) f x)

/-- **Math.** Defining property of the gradient: `⟨∇f, v⟩_g = df(v)`. -/
@[simp]
theorem metricInner_gradient (g : RiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.metricInner x (gradient g f x) v = mfderiv I 𝓘(ℝ) f x v :=
  g.metricRiesz_inner x _ v

/-- **Math.** `D_Y f = ⟨∇f, Y⟩_g`: the directional derivative is the inner product
with the gradient. -/
theorem directionalDerivative_eq_metricInner_gradient (g : RiemannianMetric I M)
    (f : M → ℝ) (Y : Π x : M, TangentSpace I x) (x : M) :
    directionalDerivative Y f x = g.metricInner x (gradient g f x) (Y x) :=
  (metricInner_gradient g f x (Y x)).symm

/-- **Math.** Uniqueness of the gradient: any vector `v` with `⟨v, w⟩_g = df(w)`
for all `w` is `∇f` at that point. -/
theorem gradient_unique (g : RiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) (h : ∀ w, g.metricInner x v w = mfderiv I 𝓘(ℝ) f x w) :
    v = gradient g f x :=
  g.metricRiesz_unique x v _ h

end Gradient

end PetersenLib
