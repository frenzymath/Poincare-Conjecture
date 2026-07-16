import OpenGALib.Riemannian.Jacobi.JacobiEquationODE
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Jacobi fields under nonpositive curvature: the no-conjugate-point core

This file formalizes the analytic heart of do Carmo, *Riemannian Geometry*,
Ch. 7, Lemma 3.2 (`lem:dc-ch7-3-2`): **a manifold of nonpositive sectional
curvature has no conjugate points.**  do Carmo's proof, read in a parallel
orthonormal frame along the geodesic `γ` (so that `D/dt` is the ordinary
derivative and `⟨·,·⟩` is the standard inner product — see
`OpenGALib/Riemannian/Jacobi/JacobiEquationODE.lean`), is the following purely
analytic argument about a solution `f` of the second-order linear ODE
`f'' + A(t) f = 0`, where `A(t)` is the curvature contraction and the
nonpositive-curvature hypothesis reads `⟪A(t) x, x⟫ ≤ 0`:

* the energy `q(t) = ⟨J, J⟩ = ⟪f, f⟫` satisfies

    `q''(t) = 2 |J'|² - 2 ⟪R(γ',J)γ', J⟫ = 2 |v|² - 2 ⟪A(t) f, f⟫ ≥ 0`

  (do Carmo's `⟨J,J⟩'' = 2|J'|² - 2K(γ',J)|γ'∧J|² ≥ 0`);
* hence `q'` is nondecreasing; since `J(0) = 0` gives `q'(0) = 0`, `q'` is
  nonnegative, so `q` is nondecreasing and `q ≥ 0`;
* if moreover `J'(0) ≠ 0` (a nontrivial field with `J(0) = 0`), then `q(t) > 0`
  for every `t > 0`, i.e. `J(t) ≠ 0`: there are no interior zeros, so no
  conjugate points.

## Main results

* `Riemannian.Jacobi.hasDerivWithinAt_energy` / `hasDerivWithinAt_energyDeriv`
  — the first and second derivatives of the energy `q = ⟪f, f⟫`.
* `Riemannian.Jacobi.energyDeriv2_nonneg` — the energy inequality `q'' ≥ 0`
  under nonpositive curvature (do Carmo's `⟨J,J⟩'' ≥ 0`).
* `Riemannian.Jacobi.IsJacobiPairOn.ne_zero_of_nonpos_curv` — the
  no-conjugate-point conclusion: a nontrivial Jacobi field with `f(0) = 0` and
  `v(0) ≠ 0` never vanishes on `(0, b]`.

Wiring these frame-coordinate statements to the intrinsic geometric Jacobi field
(parallel orthonormal frame along `γ` + the pointwise curvature operator
`curvatureOperatorAt`, with `⟪A(t) x, x⟫ = K(γ',J)|γ'∧J|²`) is the remaining step
to close `lem:dc-ch7-3-2` and, downstream, `thm:dc-ch7-3-1`.
-/

open Set
open scoped Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : ℝ → E →L[ℝ] E} {a b : ℝ} {f v : ℝ → E}

/-- The energy `q = ⟪f, f⟫` (`= ⟨J, J⟩`). -/
def energy (f : ℝ → E) (t : ℝ) : ℝ := inner ℝ (f t) (f t)

/-- The first-derivative curve of the energy, `q'(t) = ⟪f, v⟫ + ⟪v, f⟫` (`= 2⟨J, J'⟩`). -/
def energyDeriv (f v : ℝ → E) (t : ℝ) : ℝ := inner ℝ (f t) (v t) + inner ℝ (v t) (f t)

/-- The second-derivative curve of the energy along the Jacobi ODE. -/
def energyDeriv2 (A : ℝ → E →L[ℝ] E) (f v : ℝ → E) (t : ℝ) : ℝ :=
  (inner ℝ (f t) (-(A t) (f t)) + inner ℝ (v t) (v t))
    + (inner ℝ (v t) (v t) + inner ℝ (-(A t) (f t)) (f t))

/-- **First derivative of the energy** `q(t) = ⟪f(t), f(t)⟫`: `q' = ⟪f, v⟫ + ⟪v, f⟫`
(`= 2⟨J, J'⟩`, do Carmo's `⟨J,J⟩' = 2⟨J, DJ/dt⟩`). -/
theorem hasDerivWithinAt_energy (hfv : IsJacobiPairOn A a b f v) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (energy f) (energyDeriv f v t) (Icc a b) t :=
  HasDerivWithinAt.inner ℝ (hfv.1 t ht) (hfv.1 t ht)

/-- **Second derivative of the energy.** Differentiating `q' = ⟪f, v⟫ + ⟪v, f⟫`
along the Jacobi ODE `v' = -A(t) f`, `f' = v` gives
`q''(t) = (⟪f, -A f⟫ + ⟪v, v⟫) + (⟪v, v⟫ + ⟪-A f, f⟫)`. -/
theorem hasDerivWithinAt_energyDeriv (hfv : IsJacobiPairOn A a b f v) {t : ℝ}
    (ht : t ∈ Icc a b) :
    HasDerivWithinAt (energyDeriv f v) (energyDeriv2 A f v t) (Icc a b) t :=
  (HasDerivWithinAt.inner ℝ (hfv.1 t ht) (hfv.2 t ht)).add
    (HasDerivWithinAt.inner ℝ (hfv.2 t ht) (hfv.1 t ht))

/-- **The energy inequality (do Carmo `lem:dc-ch7-3-2`).** Under nonpositive
curvature `⟪A(t) x, x⟫ ≤ 0`, the second derivative of the energy is nonnegative:
`q''(t) = 2|v|² - 2⟪A f, f⟫ ≥ 0`. -/
theorem energyDeriv2_nonneg {t : ℝ} (hA : ∀ x : E, inner ℝ (A t x) x ≤ (0 : ℝ)) :
    (0 : ℝ) ≤ energyDeriv2 A f v t := by
  have hvv : (0 : ℝ) ≤ inner ℝ (v t) (v t) := real_inner_self_nonneg
  have h1 : (0 : ℝ) ≤ inner ℝ (f t) (-(A t) (f t)) := by
    rw [inner_neg_right, real_inner_comm]
    exact neg_nonneg.mpr (hA (f t))
  have h2 : (0 : ℝ) ≤ inner ℝ (-(A t) (f t)) (f t) := by
    rw [inner_neg_left]
    exact neg_nonneg.mpr (hA (f t))
  simp only [energyDeriv2]
  linarith

theorem energyDeriv_zero_of_left_zero (hf0 : f a = 0) : energyDeriv f v a = 0 := by
  simp [energyDeriv, hf0]

theorem energy_zero_of_zero {t : ℝ} (h : f t = 0) : energy f t = 0 := by
  simp [energy, h]

/-- `q'` is nondecreasing on `[0, b]` when the curvature is nonpositive. -/
theorem monotoneOn_energyDeriv (hfv : IsJacobiPairOn A 0 b f v)
    (hA : ∀ t, ∀ x : E, inner ℝ (A t x) x ≤ (0 : ℝ)) :
    MonotoneOn (energyDeriv f v) (Icc 0 b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := energyDeriv2 A f v) (convex_Icc 0 b)
    (fun t ht => (hasDerivWithinAt_energyDeriv hfv ht).continuousWithinAt)
    (fun t ht => ?_) (fun t ht => ?_)
  · exact (hasDerivWithinAt_energyDeriv hfv (interior_subset ht)).mono interior_subset
  · exact energyDeriv2_nonneg (hA t)

/-- `q'` is nonnegative on `[0, b]` when `J(0) = 0`. -/
theorem energyDeriv_nonneg (hb : (0 : ℝ) ≤ b) (hfv : IsJacobiPairOn A 0 b f v)
    (hA : ∀ t, ∀ x : E, inner ℝ (A t x) x ≤ (0 : ℝ)) (hf0 : f 0 = 0)
    {t : ℝ} (ht : t ∈ Icc 0 b) : (0 : ℝ) ≤ energyDeriv f v t := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb⟩
  have := monotoneOn_energyDeriv hfv hA h0 ht ht.1
  rwa [energyDeriv_zero_of_left_zero hf0] at this

/-- `q = ⟪f, f⟫` is nondecreasing on `[0, b]` (do Carmo: `⟨J,J⟩` nondecreasing). -/
theorem monotoneOn_energy (hb : (0 : ℝ) ≤ b) (hfv : IsJacobiPairOn A 0 b f v)
    (hA : ∀ t, ∀ x : E, inner ℝ (A t x) x ≤ (0 : ℝ)) (hf0 : f 0 = 0) :
    MonotoneOn (energy f) (Icc 0 b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := energyDeriv f v) (convex_Icc 0 b)
    (fun t ht => (hasDerivWithinAt_energy hfv ht).continuousWithinAt)
    (fun t ht => ?_) (fun t ht => ?_)
  · exact (hasDerivWithinAt_energy hfv (interior_subset ht)).mono interior_subset
  · exact energyDeriv_nonneg hb hfv hA hf0 (interior_subset ht)

/-- **No conjugate points (do Carmo `lem:dc-ch7-3-2`).** For nonpositive curvature
`⟪A(t) x, x⟫ ≤ 0`, a nontrivial Jacobi field `f` with `f(0) = 0` and `v(0) ≠ 0`
does not vanish at any `t ∈ (0, b]`.  Equivalently, along a geodesic in a manifold
of nonpositive curvature no point is conjugate to its starting point. -/
theorem IsJacobiPairOn.ne_zero_of_nonpos_curv
    (hfv : IsJacobiPairOn A 0 b f v) (hA : ∀ t, ∀ x : E, inner ℝ (A t x) x ≤ (0 : ℝ))
    (hf0 : f 0 = 0) (hv0 : v 0 ≠ 0) : ∀ t ∈ Ioc 0 b, f t ≠ 0 := by
  rintro t₀ ht₀ hzero
  have hb : (0 : ℝ) ≤ b := le_trans ht₀.1.le ht₀.2
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le ht₀.1 ht₀.2
  have hmono := monotoneOn_energy hb hfv hA hf0
  have ht₀mem : t₀ ∈ Icc 0 b := ⟨ht₀.1.le, ht₀.2⟩
  have h0mem : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb⟩
  have hq0 : energy f 0 = 0 := energy_zero_of_zero hf0
  have hqt₀ : energy f t₀ = 0 := energy_zero_of_zero hzero
  -- `q ≡ 0` on `[0, t₀]`, hence `f ≡ 0` there.
  have hfzero : ∀ s ∈ Icc 0 t₀, f s = 0 := by
    intro s hs
    have hsmem : s ∈ Icc 0 b := ⟨hs.1, le_trans hs.2 ht₀.2⟩
    have hge : (0 : ℝ) ≤ energy f s := hq0 ▸ hmono h0mem hsmem hs.1
    have hle : energy f s ≤ 0 := hqt₀ ▸ hmono hsmem ht₀mem hs.2
    have hzero_s : (inner ℝ (f s) (f s) : ℝ) = 0 := le_antisymm hle hge
    exact inner_self_eq_zero.mp hzero_s
  -- Hence `v 0 = 0`, contradicting nontriviality.
  have hev : (fun _ => (0 : E)) =ᶠ[𝓝[Icc 0 b] 0] f := by
    have hmemU : Icc 0 t₀ ∈ 𝓝[Icc 0 b] (0 : ℝ) := by
      refine mem_nhdsWithin.mpr ⟨Iio t₀, isOpen_Iio, ht₀.1, ?_⟩
      rintro x ⟨hxlt, hx0, _⟩
      exact ⟨hx0, hxlt.le⟩
    filter_upwards [hmemU] with x hx using (hfzero x hx).symm
  have hderiv0 : HasDerivWithinAt (fun _ => (0 : E)) (v 0) (Icc 0 b) 0 :=
    (hfv.1 0 h0mem).congr_of_eventuallyEq hev (by simp [hf0])
  have hderivc : HasDerivWithinAt (fun _ => (0 : E)) 0 (Icc 0 b) 0 :=
    hasDerivWithinAt_const 0 (Icc 0 b) 0
  have huniq : UniqueDiffWithinAt ℝ (Icc 0 b) 0 :=
    uniqueDiffOn_Icc hbpos 0 ⟨le_rfl, hbpos.le⟩
  have heq := huniq.eq hderiv0.hasFDerivWithinAt hderivc.hasFDerivWithinAt
  exact hv0 (by simpa using DFunLike.congr_fun heq (1 : ℝ))

/-- **No conjugate points, from nontriviality (do Carmo `lem:dc-ch7-3-2`).** The
form matching do Carmo's statement: for nonpositive curvature, a Jacobi field with
`J(0) = 0` that is *not identically zero* (`f t₁ ≠ 0` for some `t₁`) has no interior
zero on `(0, b]` — no point of `γ` is conjugate to `γ(0)`. -/
theorem IsJacobiPairOn.ne_zero_of_nonpos_curv_of_nontrivial
    (hcont : ContinuousOn A (Icc 0 b)) (hfv : IsJacobiPairOn A 0 b f v)
    (hA : ∀ t, ∀ x : E, inner ℝ (A t x) x ≤ (0 : ℝ)) (hf0 : f 0 = 0)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc 0 b) (hnt : f t₁ ≠ 0) : ∀ t ∈ Ioc 0 b, f t ≠ 0 :=
  hfv.ne_zero_of_nonpos_curv hA hf0
    (hfv.velocity_ne_zero_of_left_zero hcont hf0 ht₁ hnt)

end Riemannian.Jacobi
