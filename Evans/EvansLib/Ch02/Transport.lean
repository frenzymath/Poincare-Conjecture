import EvansLib.Ch01.MoreExamples
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Evans, Ch. 2 §2.1 — The transport equation

This file formalizes the solution formulas of Evans, *Partial Differential
Equations* (2nd ed.), §2.1 for the constant-coefficient **transport equation**
`u_t + b · Du = 0` on space–time `ℝⁿ × ℝ`.

We reuse the space–time setup and the `transportSymbol` jet symbol of
`EvansLib.Ch01.MoreExamples`: a point of `SpaceTime n = ℝ^{n+1}` has time
coordinate `0` and spatial coordinates `1, …, n`, and
`transportSymbol n b (pdeJet 1 u p) p = 0` is exactly Evans' equation
`u_t + b · Du = 0` at the space–time point `p` (see `IsPDESolutionOn`).

## The characteristic direction

Evans' key observation (§2.1) is that the transport equation says a single
directional derivative of `u` vanishes: along each line
`s ↦ (x + sb, t + s)`, the function `u` is constant. The constant direction is
`(b, 1) ∈ ℝ^{n+1}` — here `charDir n b`, with time-slot `1` and spatial slot `i`
equal to `bⁱ`. We prove `transportSymbol_pdeJet`:
`transportSymbol n b (pdeJet 1 u p) p = Du(p)·(b,1)`, turning the PDE into the
statement that the directional derivative along `charDir` vanishes.

## The explicit solution

The linear map `transportProj n b : ℝ^{n+1} → ℝⁿ`, `p ↦ x - t·b` (with `t = p₀`,
`x = (p₁,…,pₙ)`), sends a space–time point to the foot `x - tb` of its
characteristic line on `{t = 0}`, and **annihilates the characteristic
direction** (`transportProj_charDir`). Evans' solution `u(x,t) = g(x - tb)`
(formula (3)) is therefore `transportSolution n b g = g ∘ transportProj n b`.
Because `transportProj` kills `charDir`, the chain rule gives
`Du·(b,1) = Dg(x-tb)·(transportProj (b,1)) = Dg(x-tb)·0 = 0`, so the formula
solves the equation. The initial condition `u = g` on `{t = 0}` is
`transportSolution_init`.

## Main results

* `transportProj_charDir` — the projection annihilates the characteristic
  direction `(b, 1)`.
* `transportSymbol_pdeJet` — the transport symbol on the jet of `u` equals the
  directional derivative `Du(p)·(b,1)` (Evans' `ż(s) = Du·b + u_t`).
* `transportSolution_contDiff` — `g ↦ g(x - tb)` preserves `Cᵏ` regularity.
* `transportSolution_isPDESolution` / `transportSolution_isClassicalSolution` —
  **Evans §2.1, formula (3):** `u(x,t) = g(x - tb)` solves `u_t + b · Du = 0`.
* `transportSolution_init` — the initial condition `u(·, 0) = g`.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.1.
-/

open scoped BigOperators

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## The characteristic direction `(b, 1)` -/

/-- The **characteristic direction** `(b, 1)` of the transport equation, as a
vector of space–time `ℝ^{n+1}`: time-slot `1`, spatial slot `i` equal to `bⁱ`.
Evans' lines `s ↦ (x + sb, t + s)` all have this constant direction, and the
transport equation asserts that the directional derivative of `u` along it
vanishes. -/
def charDir (n : ℕ) (b : Fin n → ℝ) : SpaceTime n :=
  timeDir n + ∑ i, b i • spaceDir n i

@[simp] lemma charDir_apply_zero (b : Fin n → ℝ) : (charDir n b) 0 = 1 := by
  simp only [charDir, timeDir, spaceDir, PiLp.add_apply, PiLp.ofLp_single]
  simp

@[simp] lemma charDir_apply_succ (b : Fin n → ℝ) (j : Fin n) : (charDir n b) j.succ = b j := by
  simp only [charDir, timeDir, spaceDir, PiLp.add_apply, PiLp.ofLp_single]
  simp [Pi.single_apply, Fin.succ_inj]

/-! ## The transport projection `p ↦ x - t·b` -/

/-- The linear map `L_b : ℝ^{n+1} → ℝⁿ`, `L_b(p) = x - t·b` where `t = p₀` and
`x = (p₁, …, pₙ)`. It maps a space–time point to the foot `x - tb` of its
characteristic line on the initial plane `{t = 0}`. -/
def transportProjₗ (n : ℕ) (b : Fin n → ℝ) : SpaceTime n →ₗ[ℝ] EuclideanℝN n where
  toFun p := WithLp.toLp 2 (fun i => p i.succ - p 0 * b i)
  map_add' p q := by ext i; simp [PiLp.add_apply]; ring
  map_smul' c p := by ext i; simp [PiLp.smul_apply]; ring

/-- The transport projection `L_b : ℝ^{n+1} → ℝⁿ`, `p ↦ x - t·b`, as a continuous
linear map (automatic since the domain is finite dimensional). -/
def transportProj (n : ℕ) (b : Fin n → ℝ) : SpaceTime n →L[ℝ] EuclideanℝN n :=
  (transportProjₗ n b).toContinuousLinearMap

@[simp] lemma transportProj_apply (b : Fin n → ℝ) (p : SpaceTime n) (i : Fin n) :
    transportProj n b p i = p i.succ - p 0 * b i := by
  simp only [transportProj, LinearMap.coe_toContinuousLinearMap', transportProjₗ,
    LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]

/-- **The transport projection annihilates the characteristic direction.**
`L_b(b, 1) = 0`: this is the algebraic heart of §2.1 — the characteristic line
through any point is level for `L_b`, so `u = g ∘ L_b` is constant along it. -/
lemma transportProj_charDir (b : Fin n → ℝ) : transportProj n b (charDir n b) = 0 := by
  ext j
  simp [transportProj_apply, charDir_apply_zero, charDir_apply_succ]

/-! ## The spatial embedding of the initial plane `{t = 0}` -/

/-- The embedding `ℝⁿ ↪ ℝ^{n+1}` of the initial plane `{t = 0}`: `x ↦ (0, x)`
(time `0`, spatial part `x`). -/
def spaceEmbed (n : ℕ) (x : EuclideanℝN n) : SpaceTime n := ∑ i, x i • spaceDir n i

@[simp] lemma spaceEmbed_apply_zero (x : EuclideanℝN n) : (spaceEmbed n x) 0 = 0 := by
  simp only [spaceEmbed, spaceDir]; simp

@[simp] lemma spaceEmbed_apply_succ (x : EuclideanℝN n) (j : Fin n) :
    (spaceEmbed n x) j.succ = x j := by
  simp only [spaceEmbed, spaceDir]
  simp [Pi.single_apply, Fin.succ_inj]

lemma transportProj_spaceEmbed (b : Fin n → ℝ) (x : EuclideanℝN n) :
    transportProj n b (spaceEmbed n x) = x := by
  ext j
  simp only [transportProj_apply, spaceEmbed_apply_zero, spaceEmbed_apply_succ]
  ring

/-! ## The explicit solution `u(x, t) = g(x - tb)` (Evans §2.1, (3)) -/

/-- **Evans §2.1, formula (3): the explicit solution** `u(x, t) = g(x - tb)` of
the transport initial-value problem, written as `g ∘ L_b`. -/
def transportSolution (n : ℕ) (b : Fin n → ℝ) (g : EuclideanℝN n → ℝ) : SpaceTime n → ℝ :=
  fun p => g (transportProj n b p)

/-- The explicit solution is as regular as its initial datum: `g ∈ Cᵏ ⇒
u ∈ Cᵏ`. -/
lemma transportSolution_contDiff {k : WithTop ℕ∞} {g : EuclideanℝN n → ℝ}
    (b : Fin n → ℝ) (hg : ContDiff ℝ k g) : ContDiff ℝ k (transportSolution n b g) :=
  hg.comp (transportProj n b).contDiff

/-! ## The transport symbol is the directional derivative along `(b, 1)` -/

/-- The order-`1` jet contraction against `v`, evaluated on the `1`-jet of `u`,
is the directional derivative `Du(p)·v`. -/
lemma jetD1_pdeJet_one (v : SpaceTime n) (u : SpaceTime n → ℝ) (p : SpaceTime n) :
    jetD1 v ((pdeJet 1 u p) 1) = fderiv ℝ u p v := by
  have h : (pdeJet 1 u p) 1 = iteratedFDeriv ℝ 1 u p := rfl
  rw [h, jetD1, ContinuousMultilinearMap.apply_apply, iteratedFDeriv_one_apply,
    Matrix.cons_val_zero]

/-- **The transport symbol equals the directional derivative along `(b, 1)`.**
For any `u`, `transportSymbol n b (pdeJet 1 u p) p = Du(p)·(b,1)`. This is Evans'
computation `ż(s) = Du·b + u_t` (§2.1): the equation `u_t + b · Du = 0` says
precisely that the derivative of `u` along the characteristic direction
`(b, 1)` vanishes. -/
lemma transportSymbol_pdeJet (b : Fin n → ℝ) (u : SpaceTime n → ℝ) (p : SpaceTime n) :
    transportSymbol n b (pdeJet 1 u p) p = fderiv ℝ u p (charDir n b) := by
  rw [transportSymbol]
  rw [show timeD1 n = jetD1 (timeDir n) from rfl]
  rw [jetD1_pdeJet_one]
  simp_rw [jetD1_pdeJet_one]
  rw [charDir, map_add, map_sum]
  simp only [map_smul, smul_eq_mul]

/-! ## The explicit formula solves the transport equation -/

/-- The directional derivative of the explicit solution along the characteristic
direction vanishes: the chain rule reduces it to `Dg(x-tb)·(L_b(b,1)) =
Dg(x-tb)·0 = 0`. -/
lemma transportSolution_fderiv_charDir {g : EuclideanℝN n → ℝ} (b : Fin n → ℝ)
    (hg : Differentiable ℝ g) (p : SpaceTime n) :
    fderiv ℝ (transportSolution n b g) p (charDir n b) = 0 := by
  have h1 : HasFDerivAt (transportProj n b) (transportProj n b) p :=
    (transportProj n b).hasFDerivAt
  have h2 : HasFDerivAt g (fderiv ℝ g (transportProj n b p)) (transportProj n b p) :=
    (hg _).hasFDerivAt
  have h3 : HasFDerivAt (transportSolution n b g)
      ((fderiv ℝ g (transportProj n b p)).comp (transportProj n b)) p := h2.comp p h1
  rw [h3.fderiv, ContinuousLinearMap.comp_apply, transportProj_charDir, map_zero]

/-- **Evans §2.1, formula (3): the transport equation is solved by
`u(x, t) = g(x - tb)`.** For `C¹` (indeed differentiable) initial data `g`, the
explicit formula is a solution on all of space–time of the transport equation
`u_t + b · Du = 0` (in the `IsPDESolutionOn` sense of Ch. 1). -/
theorem transportSolution_isPDESolution {g : EuclideanℝN n → ℝ} (b : Fin n → ℝ)
    (hg : Differentiable ℝ g) :
    IsPDESolutionOn 1 Set.univ (transportSymbol n b) (transportSolution n b g) := by
  intro p _
  rw [transportSymbol_pdeJet]
  exact transportSolution_fderiv_charDir b hg p

/-- **Evans §2.1: the initial condition** `u(·, 0) = g` on the plane `{t = 0}`:
`u(x, 0) = g(x - 0·b) = g(x)`. -/
theorem transportSolution_init {g : EuclideanℝN n → ℝ} (b : Fin n → ℝ) (x : EuclideanℝN n) :
    transportSolution n b g (spaceEmbed n x) = g x := by
  rw [transportSolution, transportProj_spaceEmbed]

/-- **Evans §2.1, formula (3): the explicit formula is a classical solution.**
For `C¹` initial data `g`, `u(x, t) = g(x - tb)` is a `C¹` solution of the
transport equation on all of space–time. -/
theorem transportSolution_isClassicalSolution {g : EuclideanℝN n → ℝ} (b : Fin n → ℝ)
    (hg : ContDiff ℝ 1 g) :
    IsClassicalSolutionOn 1 Set.univ (transportSymbol n b) (transportSolution n b g) :=
  ⟨(transportSolution_contDiff b hg).contDiffOn,
    transportSolution_isPDESolution b (hg.differentiable one_ne_zero)⟩

/-! ## Uniqueness: every regular solution is given by the formula (Evans §2.1) -/

/-- Flowing a space–time point `p` back along the characteristic direction until
it reaches the initial plane `{t = 0}` lands it at the foot `x - tb`: with
`t = p₀`, `p - t·(b, 1) = (0, x - tb)`. -/
lemma transport_char_line_foot (b : Fin n → ℝ) (p : SpaceTime n) :
    p + (-(p 0)) • charDir n b = spaceEmbed n (transportProj n b p) := by
  ext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [PiLp.add_apply, PiLp.smul_apply, charDir_apply_zero]
  · simp only [PiLp.add_apply, PiLp.smul_apply, charDir_apply_succ, spaceEmbed_apply_succ,
      transportProj_apply, smul_eq_mul]
    ring

/-- **Evans §2.1, uniqueness.** Along each characteristic line the directional
derivative of a solution vanishes, so any (differentiable) solution `v` of the
transport equation with initial data `g` is constant on characteristics and
hence must equal the explicit formula `v(x, t) = g(x - tb)`. -/
theorem transportSolution_unique {g : EuclideanℝN n → ℝ} (b : Fin n → ℝ)
    {v : SpaceTime n → ℝ} (hv : Differentiable ℝ v)
    (hsol : IsPDESolutionOn 1 Set.univ (transportSymbol n b) v)
    (hinit : ∀ x, v (spaceEmbed n x) = g x) :
    v = transportSolution n b g := by
  -- the directional derivative of `v` along `(b, 1)` vanishes everywhere
  have hd : ∀ q, fderiv ℝ v q (charDir n b) = 0 := by
    intro q
    rw [← transportSymbol_pdeJet]
    exact hsol q (Set.mem_univ q)
  funext p
  -- the restriction of `v` to the characteristic line through `p` has zero derivative
  have hline : ∀ s : ℝ, HasDerivAt (fun s => v (p + s • charDir n b)) 0 s := by
    intro s
    have hpath : HasDerivAt (fun s : ℝ => p + s • charDir n b) (charDir n b) s := by
      simpa using ((hasDerivAt_id s).smul_const (charDir n b)).const_add p
    have hcomp := (hv (p + s • charDir n b)).hasFDerivAt.comp_hasDerivAt s hpath
    rwa [hd (p + s • charDir n b)] at hcomp
  -- hence `v` is constant along the line; compare `s = 0` with `s = -p₀`
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hline s).differentiableAt) (fun s => (hline s).deriv) 0 (-(p 0))
  simp only [zero_smul, add_zero] at hconst
  rw [transportSolution, hconst, transport_char_line_foot, hinit]

/-! ## §2.1 Nonhomogeneous problem (Evans (4), (5)) -/

/-- The transport projection is invariant along the characteristic direction:
`L_b(p + r(b,1)) = L_b(p)`, since `L_b` annihilates `(b, 1)`. -/
lemma transportProj_add_smul_charDir (b : Fin n → ℝ) (p : SpaceTime n) (r : ℝ) :
    transportProj n b (p + r • charDir n b) = transportProj n b p := by
  rw [map_add, map_smul, transportProj_charDir, smul_zero, add_zero]

/-- The time coordinate advances by `r` along the characteristic direction:
`(p + r(b,1))₀ = p₀ + r`. -/
lemma charDir_time_add_smul (b : Fin n → ℝ) (p : SpaceTime n) (r : ℝ) :
    (p + r • charDir n b) 0 = p 0 + r := by
  rw [PiLp.add_apply, PiLp.smul_apply, charDir_apply_zero, smul_eq_mul, mul_one]

/-- Reparametrizing from the base point `p + r(b,1)` at time `p₀ + r` back to `p`
leaves the characteristic foot at time `s` unchanged. -/
lemma charLine_shift (b : Fin n → ℝ) (p : SpaceTime n) (r s : ℝ) :
    (p + r • charDir n b) + (s - (p 0 + r)) • charDir n b
      = p + (s - p 0) • charDir n b := by
  module

/-- **Evans §2.1, formula (5): the explicit solution of the nonhomogeneous
transport problem** `u_t + b · Du = f`, `u = g` on `{t = 0}`:
$$u(x,t) = g(x - tb) + \int_0^t f\bigl(x + (s - t)b,\ s\bigr)\,ds.$$
Here the integrand `f(p + (s - p₀)(b,1))` is the value of `f` at the point of
the characteristic line through `p` at time `s`. -/
def transportSolutionNonhom (n : ℕ) (b : Fin n → ℝ) (g : EuclideanℝN n → ℝ)
    (f : SpaceTime n → ℝ) : SpaceTime n → ℝ :=
  fun p => g (transportProj n b p) + ∫ s in (0:ℝ)..(p 0), f (p + (s - p 0) • charDir n b)

/-- **Evans §2.1: the nonhomogeneous solution attains the initial data**
`u(·, 0) = g`: the integral over `[0, 0]` vanishes and the homogeneous part
gives `g`. -/
theorem transportSolutionNonhom_init (b : Fin n → ℝ) (g : EuclideanℝN n → ℝ)
    (f : SpaceTime n → ℝ) (x : EuclideanℝN n) :
    transportSolutionNonhom n b g f (spaceEmbed n x) = g x := by
  rw [transportSolutionNonhom, transportProj_spaceEmbed, spaceEmbed_apply_zero,
    intervalIntegral.integral_same, add_zero]

/-- **Evans §2.1, formula (5): the nonhomogeneous transport equation holds along
characteristics.** For continuous `f`, the derivative of `u(x, t) = g(x - tb) +
∫₀ᵗ f(x + (s-t)b, s)\,ds` along the characteristic direction `(b, 1)` at any
space–time point `p` equals `f(p)`. This is Evans' identity `ż(s) = f`; when `u`
is differentiable this directional derivative equals `Du · (b, 1) = u_t + b · Du`,
so it expresses `u_t + b · Du = f`. (Under mere continuity of `f` the individual
partials of `u` need not exist, so we state the directional form, which is what
the characteristic derivation actually establishes.) The homogeneous part is
constant along characteristics, and the integral part reduces, along `(b, 1)`, to
`∫₀^{p₀+r} f(·)` with a characteristic-invariant integrand, so its derivative is
`f` by the fundamental theorem of calculus. -/
theorem transportSolutionNonhom_char_deriv (b : Fin n → ℝ) (g : EuclideanℝN n → ℝ)
    {f : SpaceTime n → ℝ} (hf : Continuous f) (p : SpaceTime n) :
    HasDerivAt (fun r : ℝ => transportSolutionNonhom n b g f (p + r • charDir n b)) (f p) 0 := by
  have hcont : Continuous (fun s : ℝ => f (p + (s - p 0) • charDir n b)) := by fun_prop
  have hΦ : (fun r : ℝ => transportSolutionNonhom n b g f (p + r • charDir n b))
      = fun r => g (transportProj n b p)
          + ∫ s in (0:ℝ)..(p 0 + r), f (p + (s - p 0) • charDir n b) := by
    funext r
    rw [transportSolutionNonhom, transportProj_add_smul_charDir, charDir_time_add_smul]
    congr 1
    exact intervalIntegral.integral_congr (fun s _ => by rw [charLine_shift])
  rw [hΦ]
  have hlin : HasDerivAt (fun r : ℝ => p 0 + r) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add (p 0)
  have hFTC : HasDerivAt
      (fun u => ∫ s in (0:ℝ)..u, f (p + (s - p 0) • charDir n b)) (f p) (p 0 + 0) := by
    rw [add_zero]
    simpa using intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 (p 0))
      (hcont.stronglyMeasurableAtFilter _ _)
      hcont.continuousAt
  have hB : HasDerivAt
      (fun r : ℝ => ∫ s in (0:ℝ)..(p 0 + r), f (p + (s - p 0) • charDir n b)) (f p) 0 := by
    simpa using hFTC.comp 0 hlin
  exact hB.const_add (g (transportProj n b p))

end EvansLib
