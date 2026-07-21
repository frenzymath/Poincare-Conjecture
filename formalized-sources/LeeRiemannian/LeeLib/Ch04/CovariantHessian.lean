/-
Chapter 4, "Connections", eq. (4.13), Prop. 4.15(a), Ex. 4.22 and Prop. 4.21
(function case): the covariant derivative of covector fields, the pairing Leibniz
rule, and the covariant Hessian of a function.

Given a connection `∇` in the tangent bundle `TM`, Lee extends `∇` to covariant
1-tensor fields (covector fields) by demanding the Leibniz rule for the pairing
`⟨w, Y⟩`, obtaining eq. (4.13):

  `(∇_X w)(Y) = X(w(Y)) − w(∇_X Y)`.

The right-hand side is manifestly a *tensorial* operation in `Y` (the two
`(Xf)·w(Y)` terms produced by rescaling `Y ↦ fY` cancel exactly as in the torsion
computation), so it packages into a genuine covector `∇_X w : T_x M →L ℝ`.
Pairing this against a vector field recovers Prop. 4.15(a) for 1-forms.  Taking
`w = du` gives the **covariant Hessian** of a function `u` (Ex. 4.22):

  `∇²u (X, Y) = X(Yu) − (∇_X Y)u`,

a genuine `(0,2)`-tensor, and the function case of the second-covariant-derivative
formula (Prop. 4.21):

  `∇²u (X, Y) = ∇_X(∇_Y u) − ∇_{∇_X Y} u`.

(Blueprint note: Prop. 4.21 is written with `∇_{[X,Y]}`, but the identity that
Ex. 4.22 actually derives — and the one that holds — is the `∇_{∇_X Y}` form; we
formalise that corrected version.)

The full induced connection on the tensor bundle (Prop. 4.15 (i)–(iv), Prop. 4.17,
the general Prop. 4.21) is *not* available: mathlib has no induced covariant
derivative on `Hom`/dual/tensor bundles, and no tensor-product vector bundle.  We
therefore formalise only the *bare tensorial operation* of eq. (4.13) and its
function specialisation, packaged via `Bundle.TensorialAt.mkHom` / `mkHom₂` exactly
as `LeeLib.Ch04.Torsion` packages the torsion tensor.

Because the pairing `y ↦ w y (Y y)` of a covector field with a vector field is a
section of a `Hom`-bundle, its smoothness is carried as an explicit hypothesis
`hw : ∀ Z, MDiffAt (T% Z) x → MDiffAt (fun y ↦ w y (Z y)) x` ("`w` is a smooth
covector field"), matching the pointwise-on-smooth-sections style of this chapter.
(The covector is written `w` here because `ω` is reserved notation in the `ContDiff`
scope.)

* `covDerivCovectorApp` / `covDerivCovectorApp_eq` — the eq. (4.13) action.
* `covDerivCovector` / `covDerivCovector_apply` — `∇_X w` as a genuine covector.
* `covDeriv_pairing_leibniz` — Prop. 4.15(a) for 1-forms.
* `covariantHessian` / `covariantHessian_apply` — Ex. 4.22.
* `covariantHessianTensor` / `covariantHessianTensor_apply` — the Hessian `(0,2)`-tensor.
* `secondCovariantDeriv_function` — Prop. 4.21 (function case, corrected).
-/
import LeeLib.Ch04.Connection
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

namespace LeeLib.Ch04

open Bundle
open scoped Manifold ContDiff Topology

-- The fibre `[FiniteDimensional ℝ E] [CompleteSpace E]` hypotheses are needed by the
-- `TensorialAt.mkHom`/`mkHom₂` packaging in the definitions, but not by the bare
-- pointwise lemmas; silence the section-variable linter file-wide.
set_option linter.unusedSectionVars false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- **Directional derivative** `Xu` of a scalar function `u` along a vector field
`X`, i.e. `du(X)`.  Used to read `X(w(Y))` and the covariant Hessian in Lee's
notation. -/
noncomputable def dirDeriv (X : Π x : M, TangentSpace I x) (u : M → ℝ) : M → ℝ :=
  fun x => (d% u x) (X x)

@[simp] theorem dirDeriv_apply (X : Π x : M, TangentSpace I x) (u : M → ℝ) (x : M) :
    dirDeriv X u x = (d% u x) (X x) := rfl

/-- **Covariant derivative of a covector field** (Lee, eq. (4.13)), as a bare
function `M → ℝ`: the action `(∇_X w)(Y) = X(w(Y)) − w(∇_X Y)` on a vector field
`Y`.  This is tensorial in `Y` (see `covDerivCovector`), but here we keep it
unbundled. -/
noncomputable def covDerivCovectorApp (cov : TangentConnection I M)
    (X : Π x : M, TangentSpace I x) (w : Π x : M, TangentSpace I x →L[ℝ] ℝ)
    (Y : Π x : M, TangentSpace I x) : M → ℝ :=
  fun x => (d% (fun y => w y (Y y)) x) (X x) - w x (covariantDeriv cov X Y x)

/-- Lee's eq. (4.13) defining formula: `(∇_X w)(Y) = X(w(Y)) − w(∇_X Y)`. -/
theorem covDerivCovectorApp_eq (cov : TangentConnection I M)
    (X : Π x : M, TangentSpace I x) (w : Π x : M, TangentSpace I x →L[ℝ] ℝ)
    (Y : Π x : M, TangentSpace I x) (x : M) :
    covDerivCovectorApp cov X w Y x
      = dirDeriv X (fun y => w y (Y y)) x - w x (covariantDeriv cov X Y x) := rfl

/-- **Tensoriality in `Y`** of the eq. (4.13) action (the crux): for a fixed
direction `X` and a smooth covector field `w`, the operation
`Y ↦ (∇_X w)(Y)|_x` is tensorial at `x`.  As in the torsion computation, the two
`(Xf)·w(Y)` terms produced by `Y ↦ fY` cancel. -/
theorem covDerivCovector_tensorialAt (cov : TangentConnection I M)
    (X : Π x : M, TangentSpace I x) (w : Π x : M, TangentSpace I x →L[ℝ] ℝ) (x : M)
    (hw : ∀ Z : (Π p : M, TangentSpace I p),
      MDiffAt (T% Z) x → MDiffAt (fun y => w y (Z y)) x) :
    TensorialAt I E (fun Y => covDerivCovectorApp cov X w Y x) x where
  smul {f σ} hf hσ := by
    have hg : (fun y => w y ((f • σ) y)) = f * (fun y => w y (σ y)) := by
      funext y; simp only [Pi.smul_apply', map_smul, smul_eq_mul, Pi.mul_apply]
    simp only [covDerivCovectorApp]
    rw [hg, mvfderiv_mul hf (hw σ hσ), covariantDeriv_smul_fun cov X hσ hf]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_add, map_smul,
      smul_eq_mul]
    ring
  add {σ σ'} hσ hσ' := by
    have hg : (fun y => w y ((σ + σ') y)) = (fun y => w y (σ y)) + (fun y => w y (σ' y)) := by
      funext y; simp only [Pi.add_apply, map_add]
    simp only [covDerivCovectorApp]
    rw [hg, mvfderiv_add (hw σ hσ) (hw σ' hσ'), covariantDeriv_add_section cov X hσ hσ']
    simp only [ContinuousLinearMap.add_apply, map_add]
    ring

/-- **Covariant derivative of a covector field** `∇_X w` (Lee, eq. (4.13)), as a
genuine covector `T_x M →L[ℝ] ℝ`: it is `C^∞`-linear (indeed pointwise linear) in
its vector-field argument.  Packaged from `covDerivCovectorApp` via
`TensorialAt.mkHom`.  `hw` records that `w` is a smooth covector field. -/
noncomputable def covDerivCovector (cov : TangentConnection I M)
    (X : Π x : M, TangentSpace I x) (w : Π x : M, TangentSpace I x →L[ℝ] ℝ) (x : M)
    (hw : ∀ Z : (Π p : M, TangentSpace I p),
      MDiffAt (T% Z) x → MDiffAt (fun y => w y (Z y)) x) :
    TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom (fun Y => covDerivCovectorApp cov X w Y x) x
    (covDerivCovector_tensorialAt cov X w x hw)

/-- The value of `∇_X w` on a vector field `Y` differentiable at `x` is Lee's
eq. (4.13) action `X(w(Y)) − w(∇_X Y)`. -/
theorem covDerivCovector_apply (cov : TangentConnection I M)
    (X : Π x : M, TangentSpace I x) (w : Π x : M, TangentSpace I x →L[ℝ] ℝ) (x : M)
    (hw : ∀ Z : (Π p : M, TangentSpace I p),
      MDiffAt (T% Z) x → MDiffAt (fun y => w y (Z y)) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    covDerivCovector cov X w x hw (Y x) = covDerivCovectorApp cov X w Y x :=
  TensorialAt.mkHom_apply (covDerivCovector_tensorialAt cov X w x hw) hY

/-- **Prop. 4.15(a) for 1-forms** (the pairing Leibniz rule):
`X(⟨w, Y⟩) = ⟨∇_X w, Y⟩ + ⟨w, ∇_X Y⟩`.  Near-definitional from eq. (4.13). -/
theorem covDeriv_pairing_leibniz (cov : TangentConnection I M)
    (X : Π x : M, TangentSpace I x) (w : Π x : M, TangentSpace I x →L[ℝ] ℝ) (x : M)
    (hw : ∀ Z : (Π p : M, TangentSpace I p),
      MDiffAt (T% Z) x → MDiffAt (fun y => w y (Z y)) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    dirDeriv X (fun y => w y (Y y)) x
      = covDerivCovector cov X w x hw (Y x) + w x (covariantDeriv cov X Y x) := by
  rw [covDerivCovector_apply cov X w x hw hY, covDerivCovectorApp_eq]
  ring

/-! ### The covariant Hessian of a function -/

/-- **Covariant Hessian** of a function `u` (Lee, Ex. 4.22), as a bare function:
the eq. (4.13) action of `∇` on the exact 1-form `du`.  Explicitly
`∇²u (X, Y) = X(Yu) − (∇_X Y)u`. -/
noncomputable def covariantHessian (cov : TangentConnection I M) (u : M → ℝ)
    (X Y : Π x : M, TangentSpace I x) : M → ℝ :=
  covDerivCovectorApp cov X (d% u) Y

/-- Lee's Ex. 4.22 reading of the covariant Hessian: `∇²u (X, Y) = X(Yu) − (∇_X Y)u`. -/
theorem covariantHessian_apply (cov : TangentConnection I M) (u : M → ℝ)
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    covariantHessian cov u X Y x
      = dirDeriv X (dirDeriv Y u) x - (d% u x) (covariantDeriv cov X Y x) := rfl

/-- **Prop. 4.21, function case** (corrected form): the covariant Hessian is the
second covariant derivative `∇²u (X, Y) = ∇_X(∇_Y u) − ∇_{∇_X Y} u`, where
`∇_Y u = Yu` is the directional derivative.  (Definitional; the blueprint's
`∇_{[X,Y]}` should read `∇_{∇_X Y}`, which is what Ex. 4.22 derives.) -/
theorem secondCovariantDeriv_function (cov : TangentConnection I M) (u : M → ℝ)
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    covariantHessian cov u X Y x
      = dirDeriv X (dirDeriv Y u) x - dirDeriv (covariantDeriv cov X Y) u x := rfl

/-- **X-tensoriality** of the covariant Hessian: for a fixed vector field `Y`, the
map `X ↦ ∇²u (X, Y)|_x` is tensorial at `x` (indeed pointwise linear, since the
direction enters only through `X_x`). -/
theorem covariantHessian_tensorialAt_left (cov : TangentConnection I M) (u : M → ℝ)
    (Y : Π x : M, TangentSpace I x) (x : M) :
    TensorialAt I E (fun X => covariantHessian cov u X Y x) x where
  smul {f σ} _ _ := by
    simp only [covariantHessian, covDerivCovectorApp, Pi.smul_apply', covariantDeriv_apply,
      map_smul, smul_eq_mul]
    ring
  add {σ σ'} _ _ := by
    simp only [covariantHessian, covDerivCovectorApp, Pi.add_apply, covariantDeriv_apply, map_add]
    ring

/-- **Covariant Hessian tensor** `∇²u` (Lee, Ex. 4.22), as a genuine `(0,2)`-tensor
`T_x M →L[ℝ] T_x M →L[ℝ] ℝ`.  Packaged from the bare Hessian via `TensorialAt.mkHom₂`
(pointwise linearity in `X`, and eq. (4.13) tensoriality in `Y` with `w = du`).
`hu` records that `du` is a smooth covector field (the `C²`-regularity of `u`). -/
noncomputable def covariantHessianTensor (cov : TangentConnection I M) (u : M → ℝ) (x : M)
    (hu : ∀ Z : (Π p : M, TangentSpace I p),
      MDiffAt (T% Z) x → MDiffAt (fun y => (d% u y) (Z y)) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Y => covariantHessian cov u X Y x) x
    (fun τ _ => covariantHessian_tensorialAt_left cov u τ x)
    (fun σ _ => covDerivCovector_tensorialAt cov σ (d% u) x hu)

/-- The value of the covariant Hessian tensor on vector fields `X, Y` differentiable
at `x` is Lee's Ex. 4.22 action `X(Yu) − (∇_X Y)u`. -/
theorem covariantHessianTensor_apply (cov : TangentConnection I M) (u : M → ℝ) (x : M)
    (hu : ∀ Z : (Π p : M, TangentSpace I p),
      MDiffAt (T% Z) x → MDiffAt (fun y => (d% u y) (Z y)) x)
    {X Y : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    covariantHessianTensor cov u x hu (X x) (Y x) = covariantHessian cov u X Y x := by
  unfold covariantHessianTensor
  exact TensorialAt.mkHom₂_apply _ _ hX hY

end LeeLib.Ch04
