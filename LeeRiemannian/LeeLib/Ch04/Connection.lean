/-
Chapter 4, "Connections", §"Connections": the definition of a connection and its
defining properties.

Lee defines a **connection** in a smooth vector bundle `E → M` to be a map
`∇ : 𝔛(M) × Γ(E) → Γ(E)`, `(X, Y) ↦ ∇_X Y`, that is

  (i)   linear over `C^∞(M)` in `X`,
  (ii)  linear over `ℝ` in `Y`, and
  (iii) satisfies the product rule `∇_X (fY) = f ∇_X Y + (Xf) Y`.

This is exactly mathlib's `Bundle.CovariantDerivative I F V` (Koszul connection),
introduced by Massot–Rothgang–Macbeth.  Mathlib bakes property (i) — that
`(∇_X Y)|_p` depends only on `X_p` (Lee's Proposition 4.5) — directly into the
representation: a `CovariantDerivative` sends a section `σ : Π x, V x` to a
section `∇σ` of `Hom(TM, V)`, so that `∇_X σ` at `x` is `∇σ x (X x)`, manifestly
`C^∞(M)`-linear (indeed pointwise-linear) in `X`.  `Connection` below is a type
alias, and this file recovers Lee's own reading:

* `Connection.covariantDeriv ∇ X Y` — Lee's `∇_X Y`, the section `x ↦ ∇ Y x (X x)`.
* `covariantDeriv_add_dir` / `covariantDeriv_smul_dir` — property (i): linearity
  over `C^∞(M)` (indeed pointwise) in `X`.
* `covariantDeriv_add_section` / `covariantDeriv_smul_const` — property (ii):
  linearity over `ℝ` in `Y`.
* `covariantDeriv_smul_fun` — property (iii): the product rule `∇_X (fY) = f ∇_X Y
  + (Xf) Y`, with `Xf` read as the directional derivative `d% f x (X x)`.
* `covariantDeriv_apply_eq_of_dir_eq` — Lee's Proposition 4.5: `∇_X Y|_p` depends on
  `X` only through its value `X_p` at `p`.

A **connection on `M`** in Lee's sense (a connection in the tangent bundle `TM`)
is the special case `Connection I E (TangentSpace I)`; see `TangentConnection`.
-/
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

namespace LeeLib.Ch04

open Bundle
open scoped Manifold ContDiff Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V]

variable (I F V) in
/-- **Connection** (Lee, §4, "Connections"): a connection in a smooth vector
bundle `V → M` with model fiber `F`.  Aliases mathlib's Koszul
`Bundle.CovariantDerivative I F V`; see the file docstring for the correspondence
with Lee's three defining properties. -/
abbrev Connection : Type _ := CovariantDerivative I F V

variable (I M) in
/-- **Connection on `M`** (Lee, §4, "Connections in the Tangent Bundle"): a
connection in the tangent bundle `TM`, i.e. a map `∇ : 𝔛(M) × 𝔛(M) → 𝔛(M)` with
Lee's properties (i)–(iii). -/
abbrev TangentConnection [IsManifold I 1 M] : Type _ :=
  Connection I E (TangentSpace I : M → Type _)

/-- Lee's covariant derivative `∇_X Y` of a section `Y` in the direction of a
vector field `X`: the section `x ↦ ∇ Y x (X x)`.  (Argument order matches Lee's
`∇_X Y`, not mathlib's total-derivative `∇ Y`.) -/
noncomputable def covariantDeriv (cov : Connection I F V) (X : Π x : M, TangentSpace I x)
    (σ : Π x : M, V x) : Π x : M, V x :=
  fun x => cov σ x (X x)

@[simp] theorem covariantDeriv_apply (cov : Connection I F V)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    covariantDeriv cov X σ x = cov σ x (X x) := rfl

/-- Lee's Proposition 4.5: `∇_X Y|_p` depends on `X` only through its value at `p`.
Immediate from the representation, since `∇_X Y|_p = ∇ Y p (X p)`. -/
theorem covariantDeriv_apply_eq_of_dir_eq (cov : Connection I F V)
    {X X' : Π x : M, TangentSpace I x} (σ : Π x : M, V x) {p : M} (h : X p = X' p) :
    covariantDeriv cov X σ p = covariantDeriv cov X' σ p := by
  simp [h]

/-- Property (i), additivity in the direction `X` (Lee's connection axiom (i)). -/
theorem covariantDeriv_add_dir (cov : Connection I F V)
    (X X' : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    covariantDeriv cov (X + X') σ = covariantDeriv cov X σ + covariantDeriv cov X' σ := by
  funext x
  simp [map_add]

/-- Property (i), `C^∞(M)`-linearity (indeed pointwise) in the direction `X`
(Lee's connection axiom (i)): `∇_{fX} Y = f ∇_X Y`. -/
theorem covariantDeriv_smul_dir (cov : Connection I F V) (f : M → ℝ)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    covariantDeriv cov (fun x => f x • X x) σ = f • covariantDeriv cov X σ := by
  funext x
  simp [map_smul]

/-- Property (ii), additivity in the section `Y` (Lee's connection axiom (ii)),
for sections differentiable at `x`. -/
theorem covariantDeriv_add_section (cov : Connection I F V)
    (X : Π x : M, TangentSpace I x) {σ σ' : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) :
    covariantDeriv cov X (σ + σ') x = covariantDeriv cov X σ x + covariantDeriv cov X σ' x := by
  simp only [covariantDeriv_apply, cov.isCovariantDerivativeOn.add hσ hσ',
    ContinuousLinearMap.add_apply]

/-- Property (ii), `ℝ`-linearity in the section `Y` (Lee's connection axiom (ii)),
for sections differentiable at `x`: `∇_X (aY) = a ∇_X Y`. -/
theorem covariantDeriv_smul_const (cov : Connection I F V)
    (X : Π x : M, TangentSpace I x) (a : ℝ) {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) :
    covariantDeriv cov X (a • σ) x = a • covariantDeriv cov X σ x := by
  simp only [covariantDeriv_apply, cov.isCovariantDerivativeOn.smul_const a hσ,
    ContinuousLinearMap.smul_apply]

/-- Property (iii), the product rule (Lee's connection axiom (iii)):
`∇_X (fY) = f ∇_X Y + (Xf) Y`, where `Xf` is the directional derivative
`d% f x (X x)`.  Stated for sections and functions differentiable at `x`. -/
theorem covariantDeriv_smul_fun (cov : Connection I F V)
    (X : Π x : M, TangentSpace I x) {f : M → ℝ} {σ : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hf : MDiffAt f x) :
    covariantDeriv cov X (f • σ) x
      = f x • covariantDeriv cov X σ x + (d% f x) (X x) • σ x := by
  simp only [covariantDeriv_apply, cov.isCovariantDerivativeOn.leibniz hσ hf,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]

end LeeLib.Ch04
