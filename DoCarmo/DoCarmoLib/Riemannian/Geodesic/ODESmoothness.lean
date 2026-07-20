import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# `C^∞` bootstrapping for linear ODEs

A solution `Y : ℝ → E` of a first-order linear ODE `Y'(t) = B(t) Y(t)` with a *smooth*
operator coefficient `B : ℝ → E →L[ℝ] E` is itself smooth.  This is the standard elliptic
bootstrap for the (constant-in-`Y`, linear) system: `Y'` is a smooth function of `Y`, so once
`Y` is `Cⁿ` its derivative is `Cⁿ`, hence `Y` is `Cⁿ⁺¹`.

DoCarmoLib's `Riemannian.LinearODE` engine (built for parallel transport) only ever produces
`HasDerivWithinAt`/`C¹` solutions from *continuous* coefficients — no smoothness bootstrap was
available, a gap explicitly recorded in `HadamardNonpos.lean`.  These two lemmas close it: they
upgrade any such solution to `ContDiff ℝ ∞` (global) or `ContDiffOn ℝ ∞` (on an open set), given
that the coefficient is smooth.  They are the regularity input for the parallel-orthonormal-frame
Taylor expansion of `|J(t)|²` (do Carmo Ch. 5, Prop. 2.7) and, more generally, for the smoothness
of parallel transport and of Jacobi fields along a smooth geodesic.

The proofs use only `ContDiff.clm_apply` (the map `y ↦ B(t) y` is smooth in `(t)` jointly with a
smooth `Y`) and the successor characterisation of `ContDiff`/`ContDiffOn` via the derivative.
-/

open scoped ContDiff Topology

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **`C^∞` bootstrap for a linear ODE (global form).** If `Y` solves `Y'(t) = B(t) Y(t)` at
every `t` and the operator coefficient `B` is `C^∞`, then `Y` is `C^∞`.  Proof by induction on the
order `n`: the base case is continuity of the differentiable `Y`; the step writes
`deriv Y = fun t => B t (Y t)`, which is `Cⁿ` by `ContDiff.clm_apply` once `Y` is `Cⁿ`, so `Y` is
`Cⁿ⁺¹`. -/
theorem contDiff_infty_of_hasDerivAt_clm_apply
    {B : ℝ → E →L[ℝ] E} {Y : ℝ → E}
    (hB : ContDiff ℝ ∞ B) (hY : ∀ t, HasDerivAt Y (B t (Y t)) t) :
    ContDiff ℝ ∞ Y := by
  have hderiv : deriv Y = fun t => B t (Y t) := funext fun t => (hY t).deriv
  have hdiff : Differentiable ℝ Y := fun t => (hY t).differentiableAt
  rw [contDiff_infty]
  intro n
  induction n with
  | zero => rw [Nat.cast_zero]; exact contDiff_zero.mpr hdiff.continuous
  | succ k ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
    rw [hderiv]
    exact (contDiff_infty.mp hB k).clm_apply ih

/-- **`C^∞` bootstrap for a linear ODE (open-set form).** If `Y` solves `Y'(t) = B(t) Y(t)` for
every `t` in an open set `s` and the operator coefficient `B` is `C^∞` on `s`, then `Y` is `C^∞`
on `s`.  This is the form used for parallel transport and Jacobi fields along a geodesic, whose
chart data is only smooth on the open time interval where the geodesic stays in a fixed chart. -/
theorem contDiffOn_infty_of_hasDerivAt_clm_apply
    {B : ℝ → E →L[ℝ] E} {Y : ℝ → E} {s : Set ℝ} (hs : IsOpen s)
    (hB : ContDiffOn ℝ ∞ B s) (hY : ∀ t ∈ s, HasDerivAt Y (B t (Y t)) t) :
    ContDiffOn ℝ ∞ Y s := by
  have hderiveq : Set.EqOn (deriv Y) (fun t => B t (Y t)) s := fun t ht => (hY t ht).deriv
  have hdiff : DifferentiableOn ℝ Y s :=
    fun t ht => (hY t ht).differentiableAt.differentiableWithinAt
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero => rw [Nat.cast_zero]; exact contDiffOn_zero.mpr hdiff.continuousOn
  | succ k ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hs]
    exact ⟨hdiff, fun h => absurd h (by simp),
      ((contDiffOn_infty.mp hB k).clm_apply ih).congr hderiveq⟩

end Riemannian
