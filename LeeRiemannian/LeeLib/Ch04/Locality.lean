/-
Chapter 4, "Connections", §"Connections": a connection is a local operator.

Although a connection `∇` in a vector bundle `E → M` is defined by its action on
*global* sections, Lee's Lemma 4.1 shows it is in fact a **local operator**: the
value `∇_X Y|_p` depends only on the values of `X` and `Y` in an arbitrarily small
neighborhood of `p`.  Lee's proof uses a bump function and the product rule to
show `∇_X Y|_p = 0` whenever `Y` vanishes near `p`.

In mathlib's Koszul-connection theory this locality is already available:
`Bundle.IsCovariantDerivativeOn.congr_of_eventuallyEq` proves the germ-dependence
in the section slot `Y` (by the same bump-function argument), while dependence on
`X` only through its value `X_p` at `p` is built into the representation (Lee's
Proposition 4.5), since `∇_X Y|_p = ∇ Y p (X p)`.  This file assembles them into
Lee's statements:

* `covariantDeriv_congr_germ` — Lee's Lemma 4.1 in the section slot: if `Y` and
  `Ỹ` agree near `p` (and are differentiable at `p`), then `∇_X Y|_p = ∇_X Ỹ|_p`.
* `covariantDeriv_local` — Lee's Lemma 4.1 in full: if `X = X̃` at `p` and `Y = Ỹ`
  near `p`, then `∇_X Y|_p = ∇_{X̃} Ỹ|_p`.
* `covariantDeriv_dependence_at_point` — Lee's Proposition 4.5: `∇_X Y|_p` depends
  only on the germ of `Y` at `p` and on the single value `X_p`.
-/
import LeeLib.Ch04.Connection

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

/-- Lee's Lemma 4.1, section slot: `∇_X Y|_p` depends only on the germ of `Y` at
`p`.  If `Y` and `Ỹ` agree on a neighborhood of `p` and are both differentiable
at `p`, then `∇_X Y|_p = ∇_X Ỹ|_p`.  (Proved by mathlib's bump-function argument
`IsCovariantDerivativeOn.congr_of_eventuallyEq`.) -/
theorem covariantDeriv_congr_germ (cov : Connection I F V)
    (X : Π x : M, TangentSpace I x) {σ σ' : Π x : M, V x} {p : M}
    (hσ : MDiffAt (T% σ) p) (hσ' : MDiffAt (T% σ') p) (h : ∀ᶠ x in 𝓝 p, σ x = σ' x) :
    covariantDeriv cov X σ p = covariantDeriv cov X σ' p := by
  simp only [covariantDeriv_apply]
  rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq hσ hσ' Filter.univ_mem h]

/-- Lee's Lemma 4.1 (Locality), full statement: the covariant derivative is a
local operator.  If `X = X̃` at `p` and `Y = Ỹ` on a neighborhood of `p` (with
`Y, Ỹ` differentiable at `p`), then `∇_X Y|_p = ∇_{X̃} Ỹ|_p`. -/
theorem covariantDeriv_local (cov : Connection I F V)
    {X X' : Π x : M, TangentSpace I x} {σ σ' : Π x : M, V x} {p : M}
    (hσ : MDiffAt (T% σ) p) (hσ' : MDiffAt (T% σ') p)
    (hX : X p = X' p) (h : ∀ᶠ x in 𝓝 p, σ x = σ' x) :
    covariantDeriv cov X σ p = covariantDeriv cov X' σ' p := by
  rw [covariantDeriv_congr_germ cov X hσ hσ' h,
    covariantDeriv_apply_eq_of_dir_eq cov σ' hX]

/-- Lee's Proposition 4.5: `∇_X Y|_p` depends only on the values of `Y` near `p`
and the value of `X` at `p`.  This is the packaging of `covariantDeriv_local`:
same germ of `Y`, same value `X_p`, same covariant derivative at `p`. -/
theorem covariantDeriv_dependence_at_point (cov : Connection I F V)
    {X X' : Π x : M, TangentSpace I x} {σ σ' : Π x : M, V x} {p : M}
    (hσ : MDiffAt (T% σ) p) (hσ' : MDiffAt (T% σ') p)
    (hX : X p = X' p) (h : ∀ᶠ x in 𝓝 p, σ x = σ' x) :
    covariantDeriv cov X σ p = covariantDeriv cov X' σ' p :=
  covariantDeriv_local cov hσ hσ' hX h

end LeeLib.Ch04
