import EvansLib.Ch01.Examples
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Evans, Ch. 1 §1.2 — More examples of partial differential equations

A catalogue of concrete PDE from Evans §1.2, each expressed as a symbol in the
jet framework of `EvansLib.Ch01.PDE` and placed in the
linear / semilinear / quasilinear / fully-nonlinear classification of
`EvansLib.IsLinearPDE` etc. Together with `EvansLib.Ch01.Examples` (Laplace),
these validate the classification predicates across every class and across
orders 1–4.

To handle the **evolution** equations of the catalogue (heat, wave, transport,
…), which involve a time derivative `u_t` alongside the spatial gradient, we
work on the space–time domain `ℝ^{n+1}`, using coordinate `0` for time `t` and
coordinates `1, …, n` for the spatial variables `x₁, …, xₙ`.

## Reusable jet contractions

For a normed space `E`, evaluating the order-`j` jet slot on a fixed tuple of
directions is a continuous linear functional. We package the three cases we
need:

* `jetEval` — order `0`, `u ↦ u(x)`;
* `jetD1 v` — order `1`, `Du ↦ Du(x)·v` (directional derivative along `v`);
* `jetD2 v w` — order `2`, `D²u ↦ D²u(x)(v, w)`.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §1.2.
-/

open scoped BigOperators

noncomputable section

namespace EvansLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Reusable jet-slot contractions -/

/-- Order-`0` jet evaluation `u(x)`: the continuous linear functional sending the
`0`-linear form `u(x)` to its (unique) value. -/
def jetEval (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    PDEJetSlot 0 E ℝ →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ ![]

/-- Order-`1` directional contraction `Du(x) · v`: the continuous linear
functional sending the `1`-linear form `Du(x)` to its value on `v`. Taking
`v = eᵢ` gives the partial derivative `u_{xᵢ}`. -/
def jetD1 (v : E) : PDEJetSlot 1 E ℝ →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => E) ℝ ![v]

/-- Order-`2` contraction `D²u(x)(v, w)`: the continuous linear functional sending
the bilinear form `D²u(x)` to its value on `(v, w)`. Taking `v = w = eᵢ` gives the
pure second partial `u_{xᵢxᵢ}`; taking `v = eᵢ, w = eⱼ` gives `u_{xᵢxⱼ}`. -/
def jetD2 (v w : E) : PDEJetSlot 2 E ℝ →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![v, w]

/-! ## Space–time domain for evolution equations -/

/-- Space–time `ℝ^{n+1}`: coordinate `0` is time `t`, coordinates `1, …, n` are the
spatial variables. -/
abbrev SpaceTime (n : ℕ) : Type := EuclideanℝN (n + 1)

/-- The time basis vector `e₀` of space–time `ℝ^{n+1}`. -/
def timeDir (n : ℕ) : SpaceTime n := EuclideanSpace.single 0 (1 : ℝ)

/-- The `i`-th spatial basis vector `e_{i+1}` of space–time `ℝ^{n+1}`. -/
def spaceDir (n : ℕ) (i : Fin n) : SpaceTime n := EuclideanSpace.single i.succ (1 : ℝ)

/-- The time derivative `u_t = Du(x)·e₀` as a functional on the order-`1` slot. -/
def timeD1 (n : ℕ) : PDEJetSlot 1 (SpaceTime n) ℝ →L[ℝ] ℝ := jetD1 (timeDir n)

/-- The second time derivative `u_{tt} = D²u(x)(e₀, e₀)`. -/
def timeD2 (n : ℕ) : PDEJetSlot 2 (SpaceTime n) ℝ →L[ℝ] ℝ := jetD2 (timeDir n) (timeDir n)

/-- The **spatial Laplacian contraction** `Δ_x u = ∑_{i=1}^n u_{xᵢxᵢ}` on space–time:
the trace of the second-order jet slot over the spatial directions only (excluding
time). -/
def spatialLaplace (n : ℕ) : PDEJetSlot 2 (SpaceTime n) ℝ →L[ℝ] ℝ :=
  ∑ i : Fin n, jetD2 (spaceDir n i) (spaceDir n i)

/-! ## Helmholtz's (eigenvalue) equation (Evans §1.2.1a) -/

/-- **Evans §1.2.1a, Helmholtz's equation** `-Δu = λu`, i.e. `-Δu - λu = 0`.
The symbol contracts the second-order slot to `-Δu` and the zeroth-order slot to
`-λ u`. -/
def helmholtzSymbol (n : ℕ) (lam : ℝ) : PDEJet 2 (EuclideanℝN n) ℝ → EuclideanℝN n → ℝ :=
  fun ξ _ => -laplaceContraction n (ξ 2) - lam * jetEval (EuclideanℝN n) (ξ 0)

/-- Linear coefficients exhibiting Helmholtz's equation: the top order (`j = 2`)
coefficient is `-Δ`, the zeroth order (`j = 0`) coefficient is `-λ·(eval)`, and the
first order coefficient vanishes. -/
def helmholtzCoeff (n : ℕ) (lam : ℝ) :
    (j : Fin 3) → EuclideanℝN n → (PDEJetSlot (j : ℕ) (EuclideanℝN n) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => fun _ => -lam • jetEval (EuclideanℝN n)
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => fun _ => -laplaceContraction n
  | ⟨m + 3, h⟩ => absurd h (by omega)

/-- **Helmholtz's equation is a linear (2nd-order) PDE** (Evans Def. 2(i)):
`-Δu - λu = 0` has constant coefficients and no source. -/
theorem helmholtzSymbol_isLinearPDE (n : ℕ) (lam : ℝ) :
    IsLinearPDE 2 (helmholtzSymbol n lam) := by
  refine ⟨helmholtzCoeff n lam, 0, ?_⟩
  intro ξ x
  show -laplaceContraction n (ξ 2) - lam * jetEval (EuclideanℝN n) (ξ 0)
    = (∑ j, helmholtzCoeff n lam j x (ξ j)) - (0 : EuclideanℝN n → ℝ) x
  rw [Fin.sum_univ_three]
  have h0 : helmholtzCoeff n lam 0 x (ξ 0) = -lam • jetEval (EuclideanℝN n) (ξ 0) := rfl
  have h1 : helmholtzCoeff n lam 1 x (ξ 1) = 0 := rfl
  have h2 : helmholtzCoeff n lam 2 x (ξ 2) = -laplaceContraction n (ξ 2) := rfl
  rw [h0, h1, h2]
  simp only [smul_eq_mul, Pi.zero_apply]
  ring

/-! ## Linear transport equation (Evans §1.2.1a) -/

/-- **Evans §1.2.1a, linear transport equation** `u_t + ∑ᵢ bⁱ u_{xᵢ} = 0` with
constant velocity `b : Fin n → ℝ`, on space–time. First order in the jet. -/
def transportSymbol (n : ℕ) (b : Fin n → ℝ) :
    PDEJet 1 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ => timeD1 n (ξ 1) + ∑ i : Fin n, b i * jetD1 (spaceDir n i) (ξ 1)

/-- Linear coefficients for the transport equation: the order-`1` coefficient is
`u_t + ∑ bⁱ u_{xᵢ}`, the order-`0` coefficient vanishes. -/
def transportCoeff (n : ℕ) (b : Fin n → ℝ) :
    (j : Fin 2) → SpaceTime n → (PDEJetSlot (j : ℕ) (SpaceTime n) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => timeD1 n + ∑ i : Fin n, b i • jetD1 (spaceDir n i)
  | ⟨m + 2, h⟩ => absurd h (by omega)

/-- **The linear transport equation is a linear (1st-order) PDE** (Evans Def. 2(i)). -/
theorem transportSymbol_isLinearPDE (n : ℕ) (b : Fin n → ℝ) :
    IsLinearPDE 1 (transportSymbol n b) := by
  refine ⟨transportCoeff n b, 0, ?_⟩
  intro ξ x
  show timeD1 n (ξ 1) + ∑ i : Fin n, b i * jetD1 (spaceDir n i) (ξ 1)
    = (∑ j, transportCoeff n b j x (ξ j)) - (0 : SpaceTime n → ℝ) x
  rw [Fin.sum_univ_two]
  have h0 : transportCoeff n b 0 x (ξ 0) = 0 := rfl
  have h1 : transportCoeff n b 1 x (ξ 1)
      = timeD1 n (ξ 1) + ∑ i : Fin n, b i * jetD1 (spaceDir n i) (ξ 1) := by
    show (timeD1 n + ∑ i : Fin n, b i • jetD1 (spaceDir n i)) (ξ 1) = _
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [h0, h1]
  simp

/-! ## Heat (diffusion) equation (Evans §1.2.1a) -/

/-- **Evans §1.2.1a, heat equation** `u_t - Δu = 0`, on space–time. Second order. -/
def heatSymbol (n : ℕ) : PDEJet 2 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ => timeD1 n (ξ 1) - spatialLaplace n (ξ 2)

/-- Linear coefficients for the heat equation. -/
def heatCoeff (n : ℕ) :
    (j : Fin 3) → SpaceTime n → (PDEJetSlot (j : ℕ) (SpaceTime n) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => timeD1 n
  | ⟨2, _⟩ => fun _ => -spatialLaplace n
  | ⟨m + 3, h⟩ => absurd h (by omega)

/-- **The heat equation is a linear (2nd-order) PDE** (Evans Def. 2(i)). -/
theorem heatSymbol_isLinearPDE (n : ℕ) : IsLinearPDE 2 (heatSymbol n) := by
  refine ⟨heatCoeff n, 0, ?_⟩
  intro ξ x
  show timeD1 n (ξ 1) - spatialLaplace n (ξ 2)
    = (∑ j, heatCoeff n j x (ξ j)) - (0 : SpaceTime n → ℝ) x
  rw [Fin.sum_univ_three]
  have h0 : heatCoeff n 0 x (ξ 0) = 0 := rfl
  have h1 : heatCoeff n 1 x (ξ 1) = timeD1 n (ξ 1) := rfl
  have h2 : heatCoeff n 2 x (ξ 2) = -spatialLaplace n (ξ 2) := rfl
  rw [h0, h1, h2]
  simp [sub_eq_add_neg]

/-! ## Wave equation (Evans §1.2.1a) -/

/-- **Evans §1.2.1a, wave equation** `u_{tt} - Δu = 0`, on space–time. Second order. -/
def waveSymbol (n : ℕ) : PDEJet 2 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ => timeD2 n (ξ 2) - spatialLaplace n (ξ 2)

/-- Linear coefficients for the wave equation: the top-order coefficient is
`u_{tt} - Δu = D²u(e₀,e₀) - ∑ᵢ D²u(eᵢ,eᵢ)`. -/
def waveCoeff (n : ℕ) :
    (j : Fin 3) → SpaceTime n → (PDEJetSlot (j : ℕ) (SpaceTime n) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => fun _ => timeD2 n - spatialLaplace n
  | ⟨m + 3, h⟩ => absurd h (by omega)

/-- **The wave equation is a linear (2nd-order) PDE** (Evans Def. 2(i)). -/
theorem waveSymbol_isLinearPDE (n : ℕ) : IsLinearPDE 2 (waveSymbol n) := by
  refine ⟨waveCoeff n, 0, ?_⟩
  intro ξ x
  show timeD2 n (ξ 2) - spatialLaplace n (ξ 2)
    = (∑ j, waveCoeff n j x (ξ j)) - (0 : SpaceTime n → ℝ) x
  rw [Fin.sum_univ_three]
  have h0 : waveCoeff n 0 x (ξ 0) = 0 := rfl
  have h1 : waveCoeff n 1 x (ξ 1) = 0 := rfl
  have h2 : waveCoeff n 2 x (ξ 2) = timeD2 n (ξ 2) - spatialLaplace n (ξ 2) := rfl
  rw [h0, h1, h2]
  simp

/-! ## Nonlinear Poisson equation (Evans §1.2.1b) -/

/-- **Evans §1.2.1b, nonlinear Poisson equation** `-Δu = f(u)`, i.e.
`-Δu - f(u) = 0`. The reaction term `f(u)` depends on `u` through an arbitrary
function `f : ℝ → ℝ`, so the equation is semilinear but generally not linear. -/
def nonlinearPoissonSymbol (n : ℕ) (f : ℝ → ℝ) :
    PDEJet 2 (EuclideanℝN n) ℝ → EuclideanℝN n → ℝ :=
  fun ξ _ => -laplaceContraction n (ξ 2) - f (jetEval (EuclideanℝN n) (ξ 0))

/-- **The nonlinear Poisson equation is a semilinear (2nd-order) PDE** (Evans
Def. 2(ii)): the top-order part `-Δu` is linear with constant coefficient, and
the lower-order part `-f(u)` is an arbitrary function of `u`. -/
theorem nonlinearPoissonSymbol_isSemilinearPDE (n : ℕ) (f : ℝ → ℝ) :
    IsSemilinearPDE 2 (nonlinearPoissonSymbol n f) := by
  refine ⟨fun _ => -laplaceContraction n,
    fun low _ => -f (jetEval (EuclideanℝN n) (low 0)), ?_⟩
  intro ξ x
  show -laplaceContraction n (ξ 2) - f (jetEval (EuclideanℝN n) (ξ 0))
    = (-laplaceContraction n) (ξ 2) + -f (jetEval (EuclideanℝN n) (ξ 0))
  rw [ContinuousLinearMap.neg_apply]
  ring

/-! ## Reaction–diffusion equation (Evans §1.2.1b) -/

/-- **Evans §1.2.1b, scalar reaction–diffusion equation** `u_t - Δu = f(u)`, i.e.
`u_t - Δu - f(u) = 0`, on space–time. Semilinear: the top-order diffusion `-Δu`
is linear, the reaction `f(u)` is an arbitrary function of `u`. -/
def reactionDiffusionSymbol (n : ℕ) (f : ℝ → ℝ) :
    PDEJet 2 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ => timeD1 n (ξ 1) - spatialLaplace n (ξ 2) - f (jetEval (SpaceTime n) (ξ 0))

/-- **The reaction–diffusion equation is a semilinear (2nd-order) PDE** (Evans
Def. 2(ii)). -/
theorem reactionDiffusionSymbol_isSemilinearPDE (n : ℕ) (f : ℝ → ℝ) :
    IsSemilinearPDE 2 (reactionDiffusionSymbol n f) := by
  refine ⟨fun _ => -spatialLaplace n,
    fun low _ => timeD1 n (low 1) - f (jetEval (SpaceTime n) (low 0)), ?_⟩
  intro ξ x
  show timeD1 n (ξ 1) - spatialLaplace n (ξ 2) - f (jetEval (SpaceTime n) (ξ 0))
    = (-spatialLaplace n) (ξ 2) + (timeD1 n (ξ 1) - f (jetEval (SpaceTime n) (ξ 0)))
  rw [ContinuousLinearMap.neg_apply]
  ring

/-! ## Eikonal equation (Evans §1.2.1b) — a fully nonlinear PDE -/

/-- **Evans §1.2.1b, eikonal equation** `|Du| = 1`, i.e. `|Du| - 1 = 0`.
The symbol is `‖Du(x)‖ - 1`, where `‖Du(x)‖` is the operator norm of the
first-order jet slot `Du(x)` — for `E = ℝⁿ` this is exactly the Euclidean norm
of the gradient. First order. -/
def eikonalSymbol (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    PDEJet 1 E ℝ → E → ℝ :=
  fun ξ _ => ‖ξ 1‖ - 1

/-- **The eikonal equation is fully nonlinear** (Evans Def. 2(iv)): on any
nontrivial space it is *not* quasilinear, because its symbol `‖Du‖ - 1` depends
on the top-order derivative `Du` through the norm `‖·‖`, which is not affine.

Were the equation quasilinear the map `v ↦ ‖v‖ - 1` on the order-`1` slot would
be affine, `‖v‖ - 1 = A v + c` for a fixed continuous linear `A` and constant
`c`; evaluating at `0` gives `c = -1`, and adding the relations at `v = w` and
`v = -w` for a nonzero `w` cancels the linear part and forces `‖w‖ = 0`,
contradicting `w ≠ 0`. Such a `w` exists by Hahn–Banach on the nontrivial `E`. -/
theorem eikonalSymbol_isFullyNonlinearPDE (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] :
    IsFullyNonlinearPDE 1 (eikonalSymbol E) := by
  -- A nonzero element `w` of the order-`1` slot exists on any nontrivial space:
  -- take `x ≠ 0` and a Hahn–Banach functional `g` with `g x = ‖x‖ ≠ 0`, then
  -- transport `g` to the order-`1` jet slot via the currying isometry.
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  obtain ⟨g, _, hgx⟩ := exists_dual_vector ℝ x (norm_ne_zero_iff.mpr hx)
  set w : PDEJetSlot 1 E ℝ := (continuousMultilinearCurryFin1 ℝ E ℝ).symm g with hw_def
  have hw : w ≠ 0 := by
    intro hzero
    have hval : g x = 0 := by
      have hz : w (fun _ => x) = 0 := by rw [hzero]; rfl
      rwa [hw_def, continuousMultilinearCurryFin1_symm_apply] at hz
    rw [hgx] at hval
    exact (norm_ne_zero_iff.mpr hx) (by exact_mod_cast hval)
  -- Suppose, for contradiction, the eikonal symbol were quasilinear.
  intro hq
  obtain ⟨aTop, a₀, h⟩ := hq
  -- The affine data `A`, `c` determined by the (fixed) zero lower slot.
  set A : PDEJetSlot 1 E ℝ →L[ℝ] ℝ := aTop (fun _ => 0) 0 with hA
  set c : ℝ := a₀ (fun _ => 0) 0 with hc
  -- The quasilinear representation, restricted to jets with top slot `v` and
  -- lower slot `0`, is exactly the affine map `v ↦ A v + c`.
  have key : ∀ v : PDEJetSlot 1 E ℝ, ‖v‖ - 1 = A v + c := by
    intro v
    obtain ⟨J, hJ⟩ : ∃ J : PDEJet 1 E ℝ, J = Fin.lastCases v (fun _ => 0) := ⟨_, rfl⟩
    have hval := h J 0
    have htop : J (Fin.last 1) = v := by rw [hJ]; exact Fin.lastCases_last
    have hlow : (fun j : Fin 1 => J j.castSucc) = fun _ => 0 := by
      rw [hJ]; funext j; simp
    have hJ1 : J 1 = v := by rw [hJ]; exact Fin.lastCases_last
    rw [htop, hlow] at hval
    rw [eikonalSymbol, hJ1] at hval
    rw [hA, hc]; exact hval
  -- At `v = 0`: `c = -1`.
  have hc0 : c = -1 := by
    have h0 := key 0
    simp only [norm_zero, zero_sub, map_zero, zero_add] at h0
    linarith
  -- Adding the relations at `w` and `-w` cancels the linear part `A`.
  have e1 := key w
  have e2 := key (-w)
  rw [map_neg, norm_neg] at e2
  have hnorm : ‖w‖ = 0 := by rw [hc0] at e1 e2; linarith
  exact hw (norm_eq_zero.mp hnorm)

/-! ## Higher-order linear equations: Airy and beam (Evans §1.2.1a) -/

/-- Order-`3` pure directional contraction `D³u(x)(v, v, v)`. Taking `v = eₓ`
gives the third partial `u_{xxx}`. -/
def jetD3 (v : E) : PDEJetSlot 3 E ℝ →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => E) ℝ ![v, v, v]

/-- Order-`4` pure directional contraction `D⁴u(x)(v, v, v, v)`. Taking `v = eₓ`
gives the fourth partial `u_{xxxx}`. -/
def jetD4 (v : E) : PDEJetSlot 4 E ℝ →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 => E) ℝ ![v, v, v, v]

/-- **Evans §1.2.1a, Airy's equation** `u_t + u_{xxx} = 0`, on space–time `ℝ²`
(one spatial variable). Third order. -/
def airySymbol : PDEJet 3 (SpaceTime 1) ℝ → SpaceTime 1 → ℝ :=
  fun ξ _ => timeD1 1 (ξ 1) + jetD3 (spaceDir 1 0) (ξ 3)

/-- Linear coefficients for Airy's equation. -/
def airyCoeff :
    (j : Fin 4) → SpaceTime 1 → (PDEJetSlot (j : ℕ) (SpaceTime 1) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => timeD1 1
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => fun _ => jetD3 (spaceDir 1 0)
  | ⟨m + 4, h⟩ => absurd h (by omega)

/-- **Airy's equation is a linear (3rd-order) PDE** (Evans Def. 2(i)). -/
theorem airySymbol_isLinearPDE : IsLinearPDE 3 airySymbol := by
  refine ⟨airyCoeff, 0, ?_⟩
  intro ξ x
  show timeD1 1 (ξ 1) + jetD3 (spaceDir 1 0) (ξ 3)
    = (∑ j, airyCoeff j x (ξ j)) - (0 : SpaceTime 1 → ℝ) x
  rw [Fin.sum_univ_four]
  have h0 : airyCoeff 0 x (ξ 0) = 0 := rfl
  have h1 : airyCoeff 1 x (ξ 1) = timeD1 1 (ξ 1) := rfl
  have h2 : airyCoeff 2 x (ξ 2) = 0 := rfl
  have h3 : airyCoeff 3 x (ξ 3) = jetD3 (spaceDir 1 0) (ξ 3) := rfl
  rw [h0, h1, h2, h3]
  simp

/-- **Evans §1.2.1a, beam equation** `u_t + u_{xxxx} = 0`, on space–time `ℝ²`.
Fourth order. -/
def beamSymbol : PDEJet 4 (SpaceTime 1) ℝ → SpaceTime 1 → ℝ :=
  fun ξ _ => timeD1 1 (ξ 1) + jetD4 (spaceDir 1 0) (ξ 4)

/-- Linear coefficients for the beam equation. -/
def beamCoeff :
    (j : Fin 5) → SpaceTime 1 → (PDEJetSlot (j : ℕ) (SpaceTime 1) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => timeD1 1
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => fun _ => jetD4 (spaceDir 1 0)
  | ⟨m + 5, h⟩ => absurd h (by omega)

/-- **The beam equation is a linear (4th-order) PDE** (Evans Def. 2(i)). -/
theorem beamSymbol_isLinearPDE : IsLinearPDE 4 beamSymbol := by
  refine ⟨beamCoeff, 0, ?_⟩
  intro ξ x
  show timeD1 1 (ξ 1) + jetD4 (spaceDir 1 0) (ξ 4)
    = (∑ j, beamCoeff j x (ξ j)) - (0 : SpaceTime 1 → ℝ) x
  rw [Fin.sum_univ_five]
  have h0 : beamCoeff 0 x (ξ 0) = 0 := rfl
  have h1 : beamCoeff 1 x (ξ 1) = timeD1 1 (ξ 1) := rfl
  have h2 : beamCoeff 2 x (ξ 2) = 0 := rfl
  have h3 : beamCoeff 3 x (ξ 3) = 0 := rfl
  have h4 : beamCoeff 4 x (ξ 4) = jetD4 (spaceDir 1 0) (ξ 4) := rfl
  rw [h0, h1, h2, h3, h4]
  simp

/-! ## General constant-coefficient spatial operators

The remaining linear examples of Evans §1.2.1a — Liouville, Kolmogorov,
Fokker–Planck, telegraph, general wave — are constant-coefficient linear
combinations of first- and second-order spatial partials `∑ᵢ bⁱ u_{xᵢ}` and
`∑_{i,j} aⁱʲ u_{xᵢxⱼ}`. We package these two operators once and reuse them. -/

/-- The **general constant-coefficient first-order spatial operator**
`∑ᵢ bⁱ u_{xᵢ}` as a functional on the order-`1` slot of space–time. -/
def spatialFirstOrder (n : ℕ) (b : Fin n → ℝ) :
    PDEJetSlot 1 (SpaceTime n) ℝ →L[ℝ] ℝ :=
  ∑ i : Fin n, b i • jetD1 (spaceDir n i)

/-- The **general constant-coefficient second-order spatial operator**
`∑_{i,j} aⁱʲ u_{xᵢxⱼ}` as a functional on the order-`2` slot of space–time.
Taking `a = I` (the identity) recovers the Laplacian `spatialLaplace`. -/
def spatialSecondOrder (n : ℕ) (a : Fin n → Fin n → ℝ) :
    PDEJetSlot 2 (SpaceTime n) ℝ →L[ℝ] ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, a i j • jetD2 (spaceDir n i) (spaceDir n j)

/-! ## Liouville's equation (Evans §1.2.1a) -/

/-- **Evans §1.2.1a, Liouville's equation** `u_t - ∑ᵢ (bⁱu)_{xᵢ} = 0` with constant
drift `b`; since `b` is constant this is `u_t - ∑ᵢ bⁱ u_{xᵢ} = 0`. First order. -/
def liouvilleSymbol (n : ℕ) (b : Fin n → ℝ) :
    PDEJet 1 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ => timeD1 n (ξ 1) - spatialFirstOrder n b (ξ 1)

/-- Linear coefficients for Liouville's equation. -/
def liouvilleCoeff (n : ℕ) (b : Fin n → ℝ) :
    (j : Fin 2) → SpaceTime n → (PDEJetSlot (j : ℕ) (SpaceTime n) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => timeD1 n - spatialFirstOrder n b
  | ⟨m + 2, h⟩ => absurd h (by omega)

/-- **Liouville's equation is a linear (1st-order) PDE** (Evans Def. 2(i)). -/
theorem liouvilleSymbol_isLinearPDE (n : ℕ) (b : Fin n → ℝ) :
    IsLinearPDE 1 (liouvilleSymbol n b) := by
  refine ⟨liouvilleCoeff n b, 0, ?_⟩
  intro ξ x
  show timeD1 n (ξ 1) - spatialFirstOrder n b (ξ 1)
    = (∑ j, liouvilleCoeff n b j x (ξ j)) - (0 : SpaceTime n → ℝ) x
  rw [Fin.sum_univ_two]
  have h0 : liouvilleCoeff n b 0 x (ξ 0) = 0 := rfl
  have h1 : liouvilleCoeff n b 1 x (ξ 1) = timeD1 n (ξ 1) - spatialFirstOrder n b (ξ 1) := by
    show (timeD1 n - spatialFirstOrder n b) (ξ 1) = _
    rw [ContinuousLinearMap.sub_apply]
  rw [h0, h1]
  simp

/-! ## Kolmogorov's equation (Evans §1.2.1a) -/

/-- **Evans §1.2.1a, Kolmogorov's equation**
`u_t - ∑_{i,j} aⁱʲ u_{xᵢxⱼ} + ∑ᵢ bⁱ u_{xᵢ} = 0` with constant coefficients.
Second order. -/
def kolmogorovSymbol (n : ℕ) (a : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    PDEJet 2 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ => timeD1 n (ξ 1) - spatialSecondOrder n a (ξ 2) + spatialFirstOrder n b (ξ 1)

/-- Linear coefficients for Kolmogorov's equation. -/
def kolmogorovCoeff (n : ℕ) (a : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    (j : Fin 3) → SpaceTime n → (PDEJetSlot (j : ℕ) (SpaceTime n) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => timeD1 n + spatialFirstOrder n b
  | ⟨2, _⟩ => fun _ => -spatialSecondOrder n a
  | ⟨m + 3, h⟩ => absurd h (by omega)

/-- **Kolmogorov's equation is a linear (2nd-order) PDE** (Evans Def. 2(i)). -/
theorem kolmogorovSymbol_isLinearPDE (n : ℕ) (a : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    IsLinearPDE 2 (kolmogorovSymbol n a b) := by
  refine ⟨kolmogorovCoeff n a b, 0, ?_⟩
  intro ξ x
  show timeD1 n (ξ 1) - spatialSecondOrder n a (ξ 2) + spatialFirstOrder n b (ξ 1)
    = (∑ j, kolmogorovCoeff n a b j x (ξ j)) - (0 : SpaceTime n → ℝ) x
  rw [Fin.sum_univ_three]
  have h0 : kolmogorovCoeff n a b 0 x (ξ 0) = 0 := rfl
  have h1 : kolmogorovCoeff n a b 1 x (ξ 1)
      = timeD1 n (ξ 1) + spatialFirstOrder n b (ξ 1) := by
    show (timeD1 n + spatialFirstOrder n b) (ξ 1) = _
    rw [ContinuousLinearMap.add_apply]
  have h2 : kolmogorovCoeff n a b 2 x (ξ 2) = -spatialSecondOrder n a (ξ 2) := rfl
  rw [h0, h1, h2]
  simp only [Pi.zero_apply]
  ring

/-! ## Fokker–Planck equation (Evans §1.2.1a) -/

/-- **Evans §1.2.1a, Fokker–Planck equation**
`u_t - ∑_{i,j} (aⁱʲu)_{xᵢxⱼ} - ∑ᵢ (bⁱu)_{xᵢ} = 0` with constant coefficients;
in that case it reads `u_t - ∑_{i,j} aⁱʲ u_{xᵢxⱼ} - ∑ᵢ bⁱ u_{xᵢ} = 0`. Second
order. -/
def fokkerPlanckSymbol (n : ℕ) (a : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    PDEJet 2 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ => timeD1 n (ξ 1) - spatialSecondOrder n a (ξ 2) - spatialFirstOrder n b (ξ 1)

/-- Linear coefficients for the Fokker–Planck equation. -/
def fokkerPlanckCoeff (n : ℕ) (a : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    (j : Fin 3) → SpaceTime n → (PDEJetSlot (j : ℕ) (SpaceTime n) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => timeD1 n - spatialFirstOrder n b
  | ⟨2, _⟩ => fun _ => -spatialSecondOrder n a
  | ⟨m + 3, h⟩ => absurd h (by omega)

/-- **The Fokker–Planck equation is a linear (2nd-order) PDE** (Evans Def. 2(i)). -/
theorem fokkerPlanckSymbol_isLinearPDE (n : ℕ) (a : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    IsLinearPDE 2 (fokkerPlanckSymbol n a b) := by
  refine ⟨fokkerPlanckCoeff n a b, 0, ?_⟩
  intro ξ x
  show timeD1 n (ξ 1) - spatialSecondOrder n a (ξ 2) - spatialFirstOrder n b (ξ 1)
    = (∑ j, fokkerPlanckCoeff n a b j x (ξ j)) - (0 : SpaceTime n → ℝ) x
  rw [Fin.sum_univ_three]
  have h0 : fokkerPlanckCoeff n a b 0 x (ξ 0) = 0 := rfl
  have h1 : fokkerPlanckCoeff n a b 1 x (ξ 1)
      = timeD1 n (ξ 1) - spatialFirstOrder n b (ξ 1) := by
    show (timeD1 n - spatialFirstOrder n b) (ξ 1) = _
    rw [ContinuousLinearMap.sub_apply]
  have h2 : fokkerPlanckCoeff n a b 2 x (ξ 2) = -spatialSecondOrder n a (ξ 2) := rfl
  rw [h0, h1, h2]
  simp only [Pi.zero_apply]
  ring

/-! ## Telegraph equation (Evans §1.2.1a) -/

/-- **Evans §1.2.1a, telegraph equation** `u_{tt} + d u_t - u_{xx} = 0` on
space–time `ℝ²` (one spatial variable), with constant damping `d`. Second order. -/
def telegraphSymbol (d : ℝ) : PDEJet 2 (SpaceTime 1) ℝ → SpaceTime 1 → ℝ :=
  fun ξ _ => timeD2 1 (ξ 2) + d * timeD1 1 (ξ 1) - jetD2 (spaceDir 1 0) (spaceDir 1 0) (ξ 2)

/-- Linear coefficients for the telegraph equation. -/
def telegraphCoeff (d : ℝ) :
    (j : Fin 3) → SpaceTime 1 → (PDEJetSlot (j : ℕ) (SpaceTime 1) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => d • timeD1 1
  | ⟨2, _⟩ => fun _ => timeD2 1 - jetD2 (spaceDir 1 0) (spaceDir 1 0)
  | ⟨m + 3, h⟩ => absurd h (by omega)

/-- **The telegraph equation is a linear (2nd-order) PDE** (Evans Def. 2(i)). -/
theorem telegraphSymbol_isLinearPDE (d : ℝ) : IsLinearPDE 2 (telegraphSymbol d) := by
  refine ⟨telegraphCoeff d, 0, ?_⟩
  intro ξ x
  show timeD2 1 (ξ 2) + d * timeD1 1 (ξ 1) - jetD2 (spaceDir 1 0) (spaceDir 1 0) (ξ 2)
    = (∑ j, telegraphCoeff d j x (ξ j)) - (0 : SpaceTime 1 → ℝ) x
  rw [Fin.sum_univ_three]
  have h0 : telegraphCoeff d 0 x (ξ 0) = 0 := rfl
  have h1 : telegraphCoeff d 1 x (ξ 1) = d * timeD1 1 (ξ 1) := by
    show (d • timeD1 1) (ξ 1) = _
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have h2 : telegraphCoeff d 2 x (ξ 2)
      = timeD2 1 (ξ 2) - jetD2 (spaceDir 1 0) (spaceDir 1 0) (ξ 2) := by
    show (timeD2 1 - jetD2 (spaceDir 1 0) (spaceDir 1 0)) (ξ 2) = _
    rw [ContinuousLinearMap.sub_apply]
  rw [h0, h1, h2]
  simp only [Pi.zero_apply]
  ring

/-! ## General wave equation (Evans §1.2.1a) -/

/-- **Evans §1.2.1a, general wave equation**
`u_{tt} - ∑_{i,j} aⁱʲ u_{xᵢxⱼ} + ∑ᵢ bⁱ u_{xᵢ} = 0` with constant coefficients.
Second order; specializes to the wave equation when `a = I`, `b = 0`. -/
def generalWaveSymbol (n : ℕ) (a : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    PDEJet 2 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ => timeD2 n (ξ 2) - spatialSecondOrder n a (ξ 2) + spatialFirstOrder n b (ξ 1)

/-- Linear coefficients for the general wave equation. -/
def generalWaveCoeff (n : ℕ) (a : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    (j : Fin 3) → SpaceTime n → (PDEJetSlot (j : ℕ) (SpaceTime n) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => spatialFirstOrder n b
  | ⟨2, _⟩ => fun _ => timeD2 n - spatialSecondOrder n a
  | ⟨m + 3, h⟩ => absurd h (by omega)

/-- **The general wave equation is a linear (2nd-order) PDE** (Evans Def. 2(i)). -/
theorem generalWaveSymbol_isLinearPDE (n : ℕ) (a : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    IsLinearPDE 2 (generalWaveSymbol n a b) := by
  refine ⟨generalWaveCoeff n a b, 0, ?_⟩
  intro ξ x
  show timeD2 n (ξ 2) - spatialSecondOrder n a (ξ 2) + spatialFirstOrder n b (ξ 1)
    = (∑ j, generalWaveCoeff n a b j x (ξ j)) - (0 : SpaceTime n → ℝ) x
  rw [Fin.sum_univ_three]
  have h0 : generalWaveCoeff n a b 0 x (ξ 0) = 0 := rfl
  have h1 : generalWaveCoeff n a b 1 x (ξ 1) = spatialFirstOrder n b (ξ 1) := rfl
  have h2 : generalWaveCoeff n a b 2 x (ξ 2)
      = timeD2 n (ξ 2) - spatialSecondOrder n a (ξ 2) := by
    show (timeD2 n - spatialSecondOrder n a) (ξ 2) = _
    rw [ContinuousLinearMap.sub_apply]
  rw [h0, h1, h2]
  simp only [Pi.zero_apply]
  ring

end EvansLib
