import EvansLib.Ch02.Transport
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Evans, Ch. 2 — Problems

Formalizations of selected end-of-chapter problems from Evans, *Partial
Differential Equations* (2nd ed., AMS GSM 19), §2.5. These are the gap-free
exercises: they reuse the representation-formula machinery of §§2.1–2.4 and need
no divergence theorem on balls, surface measure, or singular parametric
integrals (the pieces mathlib still lacks and which gate the harder Ch. 2 nodes).

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.5.
-/

open scoped BigOperators

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## Problem 1 — first-order equation with constant reaction term

Evans, Ch. 2, Problem 1. Solve
`u_t + b · Du + c u = 0` in `ℝⁿ × (0,∞)`, `u = g` on `{t = 0}`,
for constants `c ∈ ℝ`, `b ∈ ℝⁿ`.

The explicit solution is `u(x,t) = e^{-ct} g(x - tb)`: the transport solution
`g(x-tb)` damped by the integrating factor `e^{-ct}` that absorbs the reaction
term. As in §2.1 we phrase `u_t + b · Du` as the derivative of `u` along the
characteristic direction `(b,1)` (`charDir`); by `transportSymbol_pdeJet` this
directional derivative *is* `transportSymbol n b (pdeJet 1 u ·) ·`, i.e.
`u_t + b·Du`. The equation is then `Du·(b,1) + c u = 0`. -/

/-- **Evans, Ch. 2, Problem 1: the explicit solution** `u(x,t) = e^{-ct} g(x - tb)`
of the first-order initial-value problem `u_t + b·Du + c u = 0`, `u(·,0) = g`. -/
def transportReactionSolution (n : ℕ) (b : Fin n → ℝ) (c : ℝ) (g : EuclideanℝN n → ℝ) :
    SpaceTime n → ℝ :=
  fun p => Real.exp (-c * p 0) * transportSolution n b g p

/-- **Evans, Ch. 2, Problem 1: the initial condition** `u(·,0) = g`. On the plane
`{t = 0}` the integrating factor is `e^{-c·0} = 1` and the transport part is `g`. -/
theorem transportReactionSolution_init (b : Fin n → ℝ) (c : ℝ) (g : EuclideanℝN n → ℝ)
    (x : EuclideanℝN n) :
    transportReactionSolution n b c g (spaceEmbed n x) = g x := by
  simp only [transportReactionSolution, spaceEmbed_apply_zero, mul_zero,
    Real.exp_zero, one_mul]
  exact transportSolution_init b x

/-- **Evans, Ch. 2, Problem 1: the equation holds along characteristics.** For
differentiable `g`, the derivative of `u(x,t) = e^{-ct} g(x-tb)` along the
characteristic direction `(b,1)` at any space–time point `p` equals `-c·u(p)`.
Since the characteristic derivative *is* `u_t + b·Du` (Evans §2.1,
`transportSymbol_pdeJet`), this says `u_t + b·Du = -c u`, i.e. `u_t + b·Du + c u = 0`.
The transport part `g(x-tb)` is constant along `(b,1)`
(`transportSolution_fderiv_charDir`); the integrating factor `e^{-ct}` supplies the
`-c u` from its own time-derivative. -/
theorem transportReactionSolution_char_deriv {g : EuclideanℝN n → ℝ} (b : Fin n → ℝ) (c : ℝ)
    (hg : Differentiable ℝ g) (p : SpaceTime n) :
    HasDerivAt (fun r : ℝ => transportReactionSolution n b c g (p + r • charDir n b))
      (-(c * transportReactionSolution n b c g p)) 0 := by
  have hpath : HasDerivAt (fun r : ℝ => p + r • charDir n b) (charDir n b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (charDir n b)).const_add p
  -- transport part: its directional derivative along `(b,1)` vanishes
  have hwD : Differentiable ℝ (transportSolution n b g) :=
    fun q => (hg _).comp q (transportProj n b).differentiableAt
  have hW : HasDerivAt (fun r : ℝ => transportSolution n b g (p + r • charDir n b)) 0 0 := by
    have h := (hwD (p + (0 : ℝ) • charDir n b)).hasFDerivAt.comp_hasDerivAt 0 hpath
    rwa [transportSolution_fderiv_charDir b hg (p + (0 : ℝ) • charDir n b)] at h
  -- integrating factor: `(p + r·(b,1))₀ = p₀ + r`, so `e^{-c(p₀+r)}` has derivative `-c e^{-cp₀}`
  have hcoord : HasDerivAt (fun r : ℝ => (p + r • charDir n b) 0) 1 0 := by
    have hfun : (fun r : ℝ => (p + r • charDir n b) 0) = fun r : ℝ => p 0 + r := by
      funext r; exact charDir_time_add_smul b p r
    rw [hfun]; simpa using (hasDerivAt_id (0 : ℝ)).const_add (p 0)
  have hE := (hcoord.const_mul (-c)).exp
  have hprod := hE.mul hW
  convert hprod using 1
  simp only [zero_smul, add_zero, transportReactionSolution]
  ring

/-- **Evans, Ch. 2, Problem 1: the formula solves the equation.** For differentiable
`g`, `u(x,t) = e^{-ct} g(x-tb)` satisfies `Du·(b,1) + c u = 0` at every space–time
point, i.e. `u_t + b·Du + c u = 0`. This is the `fderiv` restatement of
`transportReactionSolution_char_deriv`, obtained by identifying the characteristic
derivative with `fderiv u p (charDir n b)` (uniqueness of the line derivative). -/
theorem transportReactionSolution_pde {g : EuclideanℝN n → ℝ} (b : Fin n → ℝ) (c : ℝ)
    (hg : Differentiable ℝ g) (p : SpaceTime n) :
    fderiv ℝ (transportReactionSolution n b c g) p (charDir n b)
      + c * transportReactionSolution n b c g p = 0 := by
  have hpath : HasDerivAt (fun r : ℝ => p + r • charDir n b) (charDir n b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (charDir n b)).const_add p
  have hwD : Differentiable ℝ (transportSolution n b g) :=
    fun q => (hg _).comp q (transportProj n b).differentiableAt
  have huD : Differentiable ℝ (transportReactionSolution n b c g) := by
    have hc0 : Differentiable ℝ (fun q : SpaceTime n => q 0) := by
      simpa only [EuclideanSpace.coe_proj] using
        (EuclideanSpace.proj (0 : Fin (n + 1)) : SpaceTime n →L[ℝ] ℝ).differentiable
    have hφ : Differentiable ℝ (fun q : SpaceTime n => Real.exp (-c * q 0)) :=
      Real.differentiable_exp.comp (hc0.const_mul (-c))
    exact hφ.mul hwD
  have hpt : p + (0 : ℝ) • charDir n b = p := by simp
  have hfd : HasDerivAt (fun r : ℝ => transportReactionSolution n b c g (p + r • charDir n b))
      (fderiv ℝ (transportReactionSolution n b c g) p (charDir n b)) 0 := by
    have h := (huD (p + (0 : ℝ) • charDir n b)).hasFDerivAt.comp_hasDerivAt 0 hpath
    rw [hpt] at h
    exact h
  have huniq := (transportReactionSolution_char_deriv b c hg p).unique hfd
  rw [← huniq]; ring

end EvansLib
