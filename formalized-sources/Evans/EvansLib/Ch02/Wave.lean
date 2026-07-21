import EvansLib.Ch02.Transport
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Evans, Ch. 2 §2.4.1 — d'Alembert's formula for the 1-D wave equation

This file formalizes Evans, *Partial Differential Equations* (2nd ed.), §2.4.1:
the initial-value problem for the one-dimensional wave equation
`u_tt - u_xx = 0` on `ℝ × ℝ` with initial data `u = g`, `u_t = h` on `{t = 0}`,
and **d'Alembert's formula** (Evans (8))
$$u(x,t) = \tfrac12\bigl[g(x+t) + g(x-t)\bigr]
  + \tfrac12 \int_{x-t}^{x+t} h(y)\,dy.$$

We work on the space–time `SpaceTime 1 = ℝ²` of `EvansLib.Ch01.MoreExamples`,
coordinate `0` = time `t`, coordinate `1` = space `x`, and reuse the
second-order wave symbol `waveSymbol 1 = u_tt - Δu` already defined there.

## Strategy

The factorization `u_tt - u_xx = (∂_t+∂_x)(∂_t-∂_x)u` underlying Evans' derivation
manifests here as: **every summand of d'Alembert's formula is `φ ∘ L` for a `C²`
one-variable function `φ` and a linear form `L : ℝ² → ℝ` that is either
`(x,t) ↦ x+t` or `(x,t) ↦ x-t`.** For such an `L` the second-order chain rule gives
`u_tt = φ''(Lp)·(L e_t)²` and `u_xx = φ''(Lp)·(L e_x)²`; since both characteristic
forms satisfy `(L e_t)² = (L e_x)²` (indeed `(±1)² = 1²`), we get `u_tt = u_xx`.
The wave operator `u ↦ u_tt - u_xx` is linear on `C²` functions, so this vanishing
propagates from each summand to the whole formula.

## Main results

* `iteratedFDeriv_two_comp_clm` — the second-order chain rule
  `D²(φ∘L)(p)(v,w) = L v · L w · φ''(Lp)` (reusable infrastructure).
* `dAlembert` — d'Alembert's formula (Evans (8)).
* `dAlembert_contDiff` — **(i)** `g ∈ C², h ∈ C¹ ⟹ u ∈ C²`.
* `dAlembert_isClassicalSolution` — **(ii)** `u` is a classical solution of the
  wave equation `u_tt - u_xx = 0` on all of space–time.
* `dAlembert_init`, `dAlembert_init_time` — **(iii)** `u = g` and `u_t = h` on
  `{t = 0}`.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.4.1.
-/

open scoped BigOperators

noncomputable section

namespace EvansLib

/-! ## Second- and first-order chain rules for a scalar function of a linear form -/

/-- **Second-order chain rule for `φ ∘ L` with `L` a linear form.** For a `C²`
function `φ : ℝ → ℝ` and a continuous linear functional `L : E → ℝ`,
`D²(φ∘L)(p)(v, w) = L v · L w · φ''(Lp)`. This is the key computation behind the
d'Alembert (and, later, heat/wave) verifications: a scalar function of one linear
combination of the coordinates has a rank-one Hessian. -/
lemma iteratedFDeriv_two_comp_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (L : E →L[ℝ] ℝ) (p v w : E) :
    iteratedFDeriv ℝ 2 (φ ∘ L) p ![v, w] = L v * L w * iteratedDeriv 2 φ (L p) := by
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hφ p (le_refl 2),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hrw : (fun i => L (![v, w] i)) = (fun i : Fin 2 => (L (![v, w] i)) • (1 : ℝ)) := by
    funext i; rw [smul_eq_mul, mul_one]
  rw [hrw, ContinuousMultilinearMap.map_smul_univ, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, iteratedDeriv_eq_iteratedFDeriv,
    smul_eq_mul]

/-- **First-order chain rule for `φ ∘ L` with `L` a linear form.**
`D(φ∘L)(p)(v) = φ'(Lp) · L v`. Used for the initial velocity `u_t(·,0) = h`. -/
lemma fderiv_comp_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (L : E →L[ℝ] ℝ) (p v : E) :
    fderiv ℝ (φ ∘ L) p v = deriv φ (L p) * L v := by
  rw [fderiv_comp p (hφ (L p)) L.differentiableAt, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [show fderiv ℝ φ (L p) (L v) = (L v) • deriv φ (L p) from ?_]
  · rw [smul_eq_mul]; ring
  · rw [← fderiv_apply_one_eq_deriv, ← ContinuousLinearMap.map_smul]
    congr 1; rw [smul_eq_mul, mul_one]

/-! ## The antiderivative of the initial velocity -/

/-- The antiderivative `H(y) = ∫₀ʸ h` of the initial velocity `h`. When `h ∈ C¹`
this is a `C²` function with `H' = h`, letting us write the d'Alembert integral
`∫_{x-t}^{x+t} h = H(x+t) - H(x-t)` as a difference of compositions. -/
def daAntideriv (h : ℝ → ℝ) : ℝ → ℝ := fun y => ∫ z in (0:ℝ)..y, h z

lemma daAntideriv_hasDerivAt {h : ℝ → ℝ} (hh : Continuous h) (y : ℝ) :
    HasDerivAt (daAntideriv h) (h y) y :=
  intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable 0 y)
    (hh.stronglyMeasurableAtFilter _ _) hh.continuousAt

lemma daAntideriv_deriv {h : ℝ → ℝ} (hh : Continuous h) : deriv (daAntideriv h) = h := by
  funext y; exact (daAntideriv_hasDerivAt hh y).deriv

/-- `h ∈ C¹ ⟹ H = ∫₀ʸ h ∈ C²`. -/
lemma daAntideriv_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 2 (daAntideriv h) := by
  have hc : Continuous h := hh.continuous
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun y => (daAntideriv_hasDerivAt hc y).differentiableAt, ?_, ?_⟩
  · intro hcon; exact absurd hcon (by simp)
  · rw [daAntideriv_deriv hc]; exact hh

/-- `H(b) - H(a) = ∫ₐᵇ h`, rewriting the d'Alembert integral as a difference. -/
lemma daAntideriv_sub {h : ℝ → ℝ} (hh : Continuous h) (a b : ℝ) :
    daAntideriv h b - daAntideriv h a = ∫ z in a..b, h z := by
  have hadj : (∫ z in a..(0:ℝ), h z) + (∫ z in (0:ℝ)..b, h z) = ∫ z in a..b, h z :=
    intervalIntegral.integral_add_adjacent_intervals
      (hh.intervalIntegrable a 0) (hh.intervalIntegrable 0 b)
  have hsymm : (∫ z in a..(0:ℝ), h z) = -(∫ z in (0:ℝ)..a, h z) :=
    intervalIntegral.integral_symm 0 a
  rw [daAntideriv, daAntideriv, ← hadj, hsymm]; ring

/-! ## The two characteristic linear forms `(x,t) ↦ x ± t` -/

/-- The linear form `(x, t) ↦ x + t` on space–time (`x = p₁`, `t = p₀`): the
`x+t` characteristic coordinate. -/
def stAddₗ : SpaceTime 1 →ₗ[ℝ] ℝ where
  toFun p := p 1 + p 0
  map_add' p q := by simp [PiLp.add_apply]; ring
  map_smul' c p := by simp [PiLp.smul_apply]; ring

/-- The linear form `(x, t) ↦ x - t` on space–time: the `x-t` characteristic
coordinate. -/
def stSubₗ : SpaceTime 1 →ₗ[ℝ] ℝ where
  toFun p := p 1 - p 0
  map_add' p q := by simp [PiLp.add_apply]; ring
  map_smul' c p := by simp [PiLp.smul_apply]; ring

/-- `(x,t) ↦ x + t` as a continuous linear form. -/
def stAdd : SpaceTime 1 →L[ℝ] ℝ := stAddₗ.toContinuousLinearMap

/-- `(x,t) ↦ x - t` as a continuous linear form. -/
def stSub : SpaceTime 1 →L[ℝ] ℝ := stSubₗ.toContinuousLinearMap

@[simp] lemma stAdd_apply (p : SpaceTime 1) : stAdd p = p 1 + p 0 := rfl
@[simp] lemma stSub_apply (p : SpaceTime 1) : stSub p = p 1 - p 0 := rfl

@[simp] lemma stAdd_timeDir : stAdd (timeDir 1) = 1 := by
  simp only [stAdd_apply, timeDir, PiLp.single_apply]; norm_num
@[simp] lemma stAdd_spaceDir : stAdd (spaceDir 1 0) = 1 := by
  simp [stAdd_apply, spaceDir]
@[simp] lemma stSub_timeDir : stSub (timeDir 1) = -1 := by
  simp only [stSub_apply, timeDir, PiLp.single_apply]; norm_num
@[simp] lemma stSub_spaceDir : stSub (spaceDir 1 0) = 1 := by
  simp [stSub_apply, spaceDir]

/-! ## d'Alembert's formula -/

/-- **Evans §2.4.1, formula (8): d'Alembert's formula** for the solution of the
1-D wave initial-value problem `u_tt - u_xx = 0`, `u = g`, `u_t = h` on `{t=0}`:
$$u(x,t) = \tfrac12[g(x+t)+g(x-t)] + \tfrac12\int_{x-t}^{x+t} h(y)\,dy.$$
Here `x = p₁`, `t = p₀` in space–time coordinates. -/
def dAlembert (g h : ℝ → ℝ) : SpaceTime 1 → ℝ :=
  fun p => 2⁻¹ * (g (p 1 + p 0) + g (p 1 - p 0)) + 2⁻¹ * (∫ y in (p 1 - p 0)..(p 1 + p 0), h y)

/-- d'Alembert's formula written as a linear combination of compositions
`φ ∘ (x±t)` (with `φ ∈ {g, H}`, `H = ∫₀ʸ h`), the form used for the derivative
computations. -/
lemma dAlembert_eq {g h : ℝ → ℝ} (hh : Continuous h) :
    dAlembert g h =
      ((2⁻¹ : ℝ) • (g ∘ stAdd)) + ((2⁻¹ : ℝ) • (g ∘ stSub))
        + ((2⁻¹ : ℝ) • (daAntideriv h ∘ stAdd)) + ((-2⁻¹ : ℝ) • (daAntideriv h ∘ stSub)) := by
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, stAdd_apply, stSub_apply,
    smul_eq_mul]
  rw [dAlembert, ← daAntideriv_sub hh (p 1 - p 0) (p 1 + p 0)]
  ring

/-- Each composition summand of d'Alembert's formula is `C²`. -/
lemma dAlembert_contDiff {g h : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 2 (dAlembert g h) := by
  have hH : ContDiff ℝ 2 (daAntideriv h) := daAntideriv_contDiff hh
  rw [dAlembert_eq hh.continuous]
  exact ((((hg.comp stAdd.contDiff).const_smul (2⁻¹ : ℝ)).add
    ((hg.comp stSub.contDiff).const_smul (2⁻¹ : ℝ))).add
    ((hH.comp stAdd.contDiff).const_smul (2⁻¹ : ℝ))).add
    ((hH.comp stSub.contDiff).const_smul (-2⁻¹ : ℝ))

/-! ## The wave operator on `C²` functions -/

/-- The value `waveSymbol 1 (D²u(p)) = u_tt(p) - u_xx(p)` of the wave operator,
written as the difference of pure second directional derivatives along the time
and space axes. -/
lemma waveSymbol_eq (u : SpaceTime 1 → ℝ) (p : SpaceTime 1) :
    waveSymbol 1 (pdeJet 2 u p) p =
      iteratedFDeriv ℝ 2 u p ![timeDir 1, timeDir 1]
        - iteratedFDeriv ℝ 2 u p ![spaceDir 1 0, spaceDir 1 0] := by
  have key : pdeJet 2 u p 2 = iteratedFDeriv ℝ 2 u p := rfl
  rw [waveSymbol, key, timeD2, jetD2, ContinuousMultilinearMap.apply_apply,
    spatialLaplace, ContinuousLinearMap.sum_apply, Fin.sum_univ_one, jetD2,
    ContinuousMultilinearMap.apply_apply]

/-- **The wave operator vanishes on `φ ∘ L` for a characteristic form `L`.**
For `C²` `φ`, `(φ∘L)_tt - (φ∘L)_xx = (L e_t² - L e_x²)·φ''(Lp)`; both `stAdd` and
`stSub` satisfy `L e_t² = L e_x²`, so the wave operator annihilates them. -/
lemma waveSymbol_comp_char {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {L : SpaceTime 1 →L[ℝ] ℝ}
    (hL : L (timeDir 1) * L (timeDir 1) = L (spaceDir 1 0) * L (spaceDir 1 0))
    (p : SpaceTime 1) :
    waveSymbol 1 (pdeJet 2 (φ ∘ L) p) p = 0 := by
  rw [waveSymbol_eq, iteratedFDeriv_two_comp_clm hφ, iteratedFDeriv_two_comp_clm hφ, hL]
  ring

/-- Additivity of the wave operator on `C²` functions. -/
lemma waveSymbol_add {u v : SpaceTime 1 → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (p : SpaceTime 1) :
    waveSymbol 1 (pdeJet 2 (u + v) p) p =
      waveSymbol 1 (pdeJet 2 u p) p + waveSymbol 1 (pdeJet 2 v p) p := by
  rw [waveSymbol_eq, waveSymbol_eq, waveSymbol_eq,
    iteratedFDeriv_add_apply hu.contDiffAt hv.contDiffAt]
  simp only [ContinuousMultilinearMap.add_apply]
  ring

/-- Homogeneity of the wave operator on `C²` functions. -/
lemma waveSymbol_smul {u : SpaceTime 1 → ℝ} (hu : ContDiff ℝ 2 u) (c : ℝ)
    (p : SpaceTime 1) :
    waveSymbol 1 (pdeJet 2 (c • u) p) p = c * waveSymbol 1 (pdeJet 2 u p) p := by
  rw [waveSymbol_eq, waveSymbol_eq,
    iteratedFDeriv_const_smul_apply hu.contDiffAt]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

/-! ## d'Alembert's formula solves the wave equation -/

/-- **Evans §2.4.1, Thm (ii): d'Alembert's formula solves the wave equation**
`u_tt - u_xx = 0` on all of space–time. Each summand `φ ∘ (x±t)` is annihilated by
the wave operator (characteristic forms have `(L e_t)² = (L e_x)²`), and the
operator is linear on `C²` functions. -/
theorem dAlembert_isPDESolution {g h : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) :
    IsPDESolutionOn 2 Set.univ (waveSymbol 1) (dAlembert g h) := by
  intro p _
  have hH : ContDiff ℝ 2 (daAntideriv h) := daAntideriv_contDiff hh
  have cA : ContDiff ℝ 2 (g ∘ stAdd) := hg.comp stAdd.contDiff
  have cB : ContDiff ℝ 2 (g ∘ stSub) := hg.comp stSub.contDiff
  have cC : ContDiff ℝ 2 (daAntideriv h ∘ stAdd) := hH.comp stAdd.contDiff
  have cD : ContDiff ℝ 2 (daAntideriv h ∘ stSub) := hH.comp stSub.contDiff
  have hA : ContDiff ℝ 2 ((2⁻¹ : ℝ) • (g ∘ stAdd)) := cA.const_smul (2⁻¹ : ℝ)
  have hB : ContDiff ℝ 2 ((2⁻¹ : ℝ) • (g ∘ stSub)) := cB.const_smul (2⁻¹ : ℝ)
  have hC : ContDiff ℝ 2 ((2⁻¹ : ℝ) • (daAntideriv h ∘ stAdd)) := cC.const_smul (2⁻¹ : ℝ)
  have hD : ContDiff ℝ 2 ((-2⁻¹ : ℝ) • (daAntideriv h ∘ stSub)) := cD.const_smul (-2⁻¹ : ℝ)
  have hAB : ContDiff ℝ 2 ((2⁻¹ : ℝ) • (g ∘ stAdd) + (2⁻¹ : ℝ) • (g ∘ stSub)) := hA.add hB
  have hABC : ContDiff ℝ 2 ((2⁻¹ : ℝ) • (g ∘ stAdd) + (2⁻¹ : ℝ) • (g ∘ stSub)
      + (2⁻¹ : ℝ) • (daAntideriv h ∘ stAdd)) := hAB.add hC
  have hAdd : stAdd (timeDir 1) * stAdd (timeDir 1)
      = stAdd (spaceDir 1 0) * stAdd (spaceDir 1 0) := by rw [stAdd_timeDir, stAdd_spaceDir]
  have hSub : stSub (timeDir 1) * stSub (timeDir 1)
      = stSub (spaceDir 1 0) * stSub (spaceDir 1 0) := by
    rw [stSub_timeDir, stSub_spaceDir]; norm_num
  rw [dAlembert_eq hh.continuous,
    waveSymbol_add hABC hD, waveSymbol_add hAB hC, waveSymbol_add hA hB,
    waveSymbol_smul cA, waveSymbol_smul cB, waveSymbol_smul cC, waveSymbol_smul cD,
    waveSymbol_comp_char hg hAdd, waveSymbol_comp_char hg hSub,
    waveSymbol_comp_char hH hAdd, waveSymbol_comp_char hH hSub]
  ring

/-- **Evans §2.4.1, Thm (i)+(ii): d'Alembert's formula is a classical solution.**
For `g ∈ C²`, `h ∈ C¹`, `u(x,t) = ½[g(x+t)+g(x-t)] + ½∫_{x-t}^{x+t} h` is a `C²`
solution of the wave equation on all of space–time. -/
theorem dAlembert_isClassicalSolution {g h : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) :
    IsClassicalSolutionOn 2 Set.univ (waveSymbol 1) (dAlembert g h) :=
  ⟨(dAlembert_contDiff hg hh).contDiffOn, dAlembert_isPDESolution hg hh⟩

/-! ## Initial conditions -/

/-- **Evans §2.4.1, Thm (iii): the initial displacement** `u(x, 0) = g(x)`. On
`{t = 0}` (`p₀ = 0`), the two `g`-terms coincide and the integral over `[x, x]`
vanishes. -/
theorem dAlembert_init {g h : ℝ → ℝ} (p : SpaceTime 1) (hp : p 0 = 0) :
    dAlembert g h p = g (p 1) := by
  simp only [dAlembert, hp, add_zero, sub_zero, intervalIntegral.integral_same, mul_zero]
  ring

/-- **Evans §2.4.1, Thm (iii): the initial velocity** `u_t(x, 0) = h(x)`, stated as
the directional derivative of `u` along the time axis on `{t = 0}`. The `g`-terms
contribute `±½g'(x)` (cancelling) and the `H`-terms contribute `½h(x) + ½h(x) =
h(x)`. -/
theorem dAlembert_init_time {g h : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h)
    (p : SpaceTime 1) (hp : p 0 = 0) :
    fderiv ℝ (dAlembert g h) p (timeDir 1) = h (p 1) := by
  have hH : ContDiff ℝ 2 (daAntideriv h) := daAntideriv_contDiff hh
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hHd : Differentiable ℝ (daAntideriv h) := hH.differentiable (by norm_num)
  have dA : Differentiable ℝ (g ∘ stAdd) := hgd.comp stAdd.differentiable
  have dB : Differentiable ℝ (g ∘ stSub) := hgd.comp stSub.differentiable
  have dC : Differentiable ℝ (daAntideriv h ∘ stAdd) := hHd.comp stAdd.differentiable
  have dD : Differentiable ℝ (daAntideriv h ∘ stSub) := hHd.comp stSub.differentiable
  rw [dAlembert_eq hh.continuous]
  rw [fderiv_add ((((dA.const_smul (2⁻¹ : ℝ)).add (dB.const_smul (2⁻¹ : ℝ))).add
        (dC.const_smul (2⁻¹ : ℝ))).differentiableAt)
      ((dD.const_smul (-2⁻¹ : ℝ)).differentiableAt),
    fderiv_add (((dA.const_smul (2⁻¹ : ℝ)).add (dB.const_smul (2⁻¹ : ℝ))).differentiableAt)
      ((dC.const_smul (2⁻¹ : ℝ)).differentiableAt),
    fderiv_add ((dA.const_smul (2⁻¹ : ℝ)).differentiableAt)
      ((dB.const_smul (2⁻¹ : ℝ)).differentiableAt),
    fderiv_const_smul (dA.differentiableAt), fderiv_const_smul (dB.differentiableAt),
    fderiv_const_smul (dC.differentiableAt), fderiv_const_smul (dD.differentiableAt)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_comp_clm hgd, fderiv_comp_clm hgd, fderiv_comp_clm hHd, fderiv_comp_clm hHd,
    stAdd_timeDir, stSub_timeDir]
  simp only [stAdd_apply, stSub_apply, hp, add_zero, sub_zero]
  rw [daAntideriv_deriv hh.continuous]
  ring

/-! ## General solution of the 1-D wave equation (Evans §2.4.1) -/

/-- The **general form of a 1-D wave** `u(x,t) = F(x+t) + G(x-t)`: a right-moving
profile `G` superposed with a left-moving profile `F`. d'Alembert's formula (8)
exhibits every solution of the initial-value problem in this form; conversely any
such `u` solves the wave equation. -/
def waveGeneralSol (F G : ℝ → ℝ) : SpaceTime 1 → ℝ :=
  fun p => F (p 1 + p 0) + G (p 1 - p 0)

lemma waveGeneralSol_eq (F G : ℝ → ℝ) :
    waveGeneralSol F G = (F ∘ stAdd) + (G ∘ stSub) := by
  funext p
  simp only [waveGeneralSol, Pi.add_apply, Function.comp_apply, stAdd_apply, stSub_apply]

/-- **Evans §2.4.1: every `F(x+t) + G(x-t)` solves the wave equation.** For
`F, G ∈ C²`, `u(x,t) = F(x+t) + G(x-t)` solves `u_tt - u_xx = 0` on all of
space–time. Both summands are `φ ∘ (x±t)` with a characteristic form, and the wave
operator annihilates each. -/
theorem waveGeneralSol_isPDESolution {F G : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G) :
    IsPDESolutionOn 2 Set.univ (waveSymbol 1) (waveGeneralSol F G) := by
  intro p _
  have hFc : ContDiff ℝ 2 (F ∘ stAdd) := hF.comp stAdd.contDiff
  have hGc : ContDiff ℝ 2 (G ∘ stSub) := hG.comp stSub.contDiff
  have hAdd : stAdd (timeDir 1) * stAdd (timeDir 1)
      = stAdd (spaceDir 1 0) * stAdd (spaceDir 1 0) := by rw [stAdd_timeDir, stAdd_spaceDir]
  have hSub : stSub (timeDir 1) * stSub (timeDir 1)
      = stSub (spaceDir 1 0) * stSub (spaceDir 1 0) := by
    rw [stSub_timeDir, stSub_spaceDir]; norm_num
  rw [waveGeneralSol_eq, waveSymbol_add hFc hGc,
    waveSymbol_comp_char hF hAdd, waveSymbol_comp_char hG hSub]
  ring

/-- The general 1-D wave `F(x+t) + G(x-t)` is `C²` when `F, G ∈ C²`. -/
theorem waveGeneralSol_contDiff {F G : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) :
    ContDiff ℝ 2 (waveGeneralSol F G) := by
  rw [waveGeneralSol_eq]
  exact (hF.comp stAdd.contDiff).add (hG.comp stSub.contDiff)

/-- **Evans §2.4.1: `F(x+t) + G(x-t)` is a classical solution of the wave
equation** for `F, G ∈ C²`. -/
theorem waveGeneralSol_isClassicalSolution {F G : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G) :
    IsClassicalSolutionOn 2 Set.univ (waveSymbol 1) (waveGeneralSol F G) :=
  ⟨(waveGeneralSol_contDiff hF hG).contDiffOn, waveGeneralSol_isPDESolution hF hG⟩

end EvansLib
