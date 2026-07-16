import EvansLib.Ch01.NonlinearExamples
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Evans, Ch. 1 §1.2.1b — Divergence-structure quasilinear equations and Hamilton–Jacobi

The remaining genuinely nonlinear scalar examples of Evans' catalogue (§1.2.1b)
whose classification is settled here in the jet framework of `EvansLib.Ch01.PDE`:

* **Scalar conservation law** `u_t + div 𝐅(u) = 0`. For a classical solution the
  chain rule gives `u_t + ∑ᵢ (Fⁱ)'(u) u_{xᵢ} = 0`; the top-order (first) derivative
  enters with coefficients `(Fⁱ)'(u)` depending on `u`, so it is *quasilinear*.
  Inviscid Burgers (`EvansLib.burgersSymbol`) is the case `n = 1`, `F(u) = u²/2`.
* **Nonlinear diffusion / porous medium** `u_t - Δ(φ(u)) = 0`. The chain rule gives
  `u_t - φ'(u) Δu - φ''(u) |Du|² = 0`, quasilinear at order `2`. The porous-medium
  equation `u_t - Δ(uᵞ) = 0` is the case `φ(u) = uᵞ`, `φ'(u) = γ uᵞ⁻¹`,
  `φ''(u) = γ(γ-1) uᵞ⁻²`.
* **Nonlinear wave (divergence form)** `u_{tt} - div 𝐚(Du) = 0`. The chain rule
  gives `u_{tt} - ∑_{i,j} (∂aⱼ/∂pᵢ)(Du) u_{xᵢxⱼ} = 0`, quasilinear at order `2`.
* **Hamilton–Jacobi** `u_t + H(Du, x) = 0`. For the archetypal quadratic
  Hamiltonian `H(p, x) = |p|²` (giving `u_t + |Du|² = 0`) the symbol is *quadratic*
  in the top-order slot, hence *fully nonlinear* — the same scaling obstruction as
  Monge–Ampère.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §1.2.1b.
-/

open scoped BigOperators

noncomputable section

namespace EvansLib

/-! ## Scalar conservation law (Evans §1.2.1b) — quasilinear, first order -/

/-- **Evans §1.2.1b, scalar conservation law** `u_t + div 𝐅(u) = 0` on space–time
`ℝ^{n+1}`. For a classical solution the chain rule turns `div 𝐅(u)` into
`∑ᵢ (Fⁱ)'(u) u_{xᵢ}`; we parametrize by the flux velocity `a s = 𝐅'(s)`, so the
symbol is `u_t + ∑ᵢ aⁱ(u) u_{xᵢ}`. First order. The top-order coefficient `aⁱ(u)`
depends on the solution value `u`, so this is genuinely *quasilinear*. -/
def conservationLawSymbol (n : ℕ) (a : ℝ → Fin n → ℝ) :
    PDEJet 1 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ => timeD1 n (ξ 1)
    + ∑ i : Fin n, a (jetEval (SpaceTime n) (ξ 0)) i * jetD1 (spaceDir n i) (ξ 1)

/-- **The scalar conservation law is a quasilinear (1st-order) PDE** (Evans
Def. 2(iii)): its top-order coefficients `aⁱ(u)` depend on the lower-order jet
`u`. Generalizes `EvansLib.burgersSymbol_isQuasilinearPDE`. -/
theorem conservationLawSymbol_isQuasilinearPDE (n : ℕ) (a : ℝ → Fin n → ℝ) :
    IsQuasilinearPDE 1 (conservationLawSymbol n a) := by
  refine ⟨fun low _ => timeD1 n
      + ∑ i : Fin n, a (jetEval (SpaceTime n) (low 0)) i • jetD1 (spaceDir n i),
    fun _ _ => 0, ?_⟩
  intro ξ x
  show timeD1 n (ξ 1)
      + ∑ i : Fin n, a (jetEval (SpaceTime n) (ξ 0)) i * jetD1 (spaceDir n i) (ξ 1)
    = (timeD1 n
        + ∑ i : Fin n, a (jetEval (SpaceTime n) (ξ 0)) i • jetD1 (spaceDir n i)) (ξ 1) + 0
  rw [add_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
  simp [ContinuousLinearMap.smul_apply]

/-! ## Nonlinear diffusion / porous medium (Evans §1.2.1b) — quasilinear, 2nd order -/

/-- **Evans §1.2.1b, nonlinear diffusion equation** `u_t - Δ(φ(u)) = 0` on
space–time `ℝ^{n+1}`. For a classical solution the chain rule gives
`Δ(φ(u)) = φ'(u) Δu + φ''(u) |Du|²`; we parametrize by `dφ = φ'` and `ddφ = φ''`,
so the symbol is `u_t - φ'(u) Δu - φ''(u) |Du|²`. Second order. The **porous-medium
equation** `u_t - Δ(uᵞ) = 0` is the case `φ(u) = uᵞ`. -/
def nonlinearDiffusionSymbol (n : ℕ) (dφ ddφ : ℝ → ℝ) :
    PDEJet 2 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ =>
    timeD1 n (ξ 1)
      - dφ (jetEval (SpaceTime n) (ξ 0)) * spatialLaplace n (ξ 2)
      - ddφ (jetEval (SpaceTime n) (ξ 0))
          * ∑ i : Fin n, (jetD1 (spaceDir n i) (ξ 1)) ^ 2

/-- **The nonlinear diffusion (porous-medium) equation is a quasilinear (2nd-order)
PDE** (Evans Def. 2(iii)): the top-order coefficient `-φ'(u)` multiplying `Δu`
depends on the lower-order jet `u`, while `φ''(u) |Du|²` is a lower-order
(first-order) nonlinearity. -/
theorem nonlinearDiffusionSymbol_isQuasilinearPDE (n : ℕ) (dφ ddφ : ℝ → ℝ) :
    IsQuasilinearPDE 2 (nonlinearDiffusionSymbol n dφ ddφ) := by
  refine ⟨fun low _ => (-(dφ (jetEval (SpaceTime n) (low 0)))) • spatialLaplace n,
    fun low _ => timeD1 n (low 1)
      - ddφ (jetEval (SpaceTime n) (low 0))
          * ∑ i : Fin n, (jetD1 (spaceDir n i) (low 1)) ^ 2, ?_⟩
  intro ξ x
  show timeD1 n (ξ 1)
      - dφ (jetEval (SpaceTime n) (ξ 0)) * spatialLaplace n (ξ 2)
      - ddφ (jetEval (SpaceTime n) (ξ 0))
          * ∑ i : Fin n, (jetD1 (spaceDir n i) (ξ 1)) ^ 2
    = ((-(dφ (jetEval (SpaceTime n) (ξ 0)))) • spatialLaplace n) (ξ 2)
      + (timeD1 n (ξ 1)
        - ddφ (jetEval (SpaceTime n) (ξ 0))
            * ∑ i : Fin n, (jetD1 (spaceDir n i) (ξ 1)) ^ 2)
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-! ## Nonlinear wave equation, divergence form (Evans §1.2.1b) — quasilinear -/

/-- **Evans §1.2.1b, nonlinear wave equation (divergence form)**
`u_{tt} - div 𝐚(Du) = 0` on space–time `ℝ^{n+1}`. For a classical solution the
chain rule gives `div 𝐚(Du) = ∑_{i,j} (∂aⱼ/∂pᵢ)(Du) u_{xᵢxⱼ}`; we parametrize by
the Jacobian field `Da p i j = (∂aⱼ/∂pᵢ)(p)`, so the symbol is
`u_{tt} - ∑_{i,j} (Da(Du))ᵢⱼ u_{xᵢxⱼ}`. Second order, quasilinear: the top-order
coefficients depend on `Du`. This is the second form listed under Evans' nonlinear
wave equations. -/
def nonlinearWaveDivSymbol (n : ℕ) (Da : (Fin n → ℝ) → Fin n → Fin n → ℝ) :
    PDEJet 2 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ =>
    timeD2 n (ξ 2)
      - ∑ i : Fin n, ∑ j : Fin n,
          Da (fun l => jetD1 (spaceDir n l) (ξ 1)) i j
            * jetD2 (spaceDir n i) (spaceDir n j) (ξ 2)

/-- **The divergence-form nonlinear wave equation is a quasilinear (2nd-order)
PDE** (Evans Def. 2(iii)): the top-order coefficients `(Da(Du))ᵢⱼ` depend on the
lower-order jet `Du`. -/
theorem nonlinearWaveDivSymbol_isQuasilinearPDE (n : ℕ)
    (Da : (Fin n → ℝ) → Fin n → Fin n → ℝ) :
    IsQuasilinearPDE 2 (nonlinearWaveDivSymbol n Da) := by
  refine ⟨fun low _ => timeD2 n
      - ∑ i : Fin n, ∑ j : Fin n,
          Da (fun l => jetD1 (spaceDir n l) (low 1)) i j
            • jetD2 (spaceDir n i) (spaceDir n j),
    fun _ _ => 0, ?_⟩
  intro ξ x
  show timeD2 n (ξ 2)
      - ∑ i : Fin n, ∑ j : Fin n,
          Da (fun l => jetD1 (spaceDir n l) (ξ 1)) i j
            * jetD2 (spaceDir n i) (spaceDir n j) (ξ 2)
    = (timeD2 n - ∑ i : Fin n, ∑ j : Fin n,
          Da (fun l => jetD1 (spaceDir n l) (ξ 1)) i j
            • jetD2 (spaceDir n i) (spaceDir n j)) (ξ 2) + 0
  rw [add_zero, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ## Hamilton–Jacobi equation (Evans §1.2.1b) — fully nonlinear -/

/-- **Evans §1.2.1b, Hamilton–Jacobi equation** `u_t + H(Du, x) = 0` on space–time
`ℝ^{n+1}`, with Hamiltonian `H : ℝⁿ × ℝ^{n+1} → ℝ` acting on the spatial gradient
values `Du = (u_{x₁}, …, u_{xₙ})` and the base point. First order. -/
def hamiltonJacobiSymbol (n : ℕ) (H : (Fin n → ℝ) → SpaceTime n → ℝ) :
    PDEJet 1 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ x => timeD1 n (ξ 1) + H (fun i => jetD1 (spaceDir n i) (ξ 1)) x

/-- The Hamilton–Jacobi equation with the archetypal **quadratic Hamiltonian**
`H(p, x) = |p|² = ∑ᵢ pᵢ²`, i.e. `u_t + |Du|² = 0`. -/
def hamiltonJacobiQuadraticSymbol (n : ℕ) :
    PDEJet 1 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  hamiltonJacobiSymbol n (fun p _ => ∑ i : Fin n, (p i) ^ 2)

/-- **The quadratic Hamilton–Jacobi equation `u_t + |Du|² = 0` is fully nonlinear**
(Evans Def. 2(iv)): its symbol is *quadratic*, not affine, in the top-order slot
`Du`. Were it quasilinear, `s ↦ Φ(s·w)` would be affine in `s` for every order-`1`
slot `w`; but along a slot `w` with nonzero spatial gradient (`∑ᵢ w(eᵢ)² ≠ 0`) it
equals `s·(u_t\text{-part}) + s²·|Du|²`, whose `s = 0, 1, 2` values force
`∑ᵢ w(eᵢ)² = 0`, a contradiction. Such a witness `w` exists whenever `n ≥ 1`. -/
theorem hamiltonJacobiQuadraticSymbol_isFullyNonlinearPDE (n : ℕ)
    (w : PDEJetSlot 1 (SpaceTime n) ℝ)
    (hw : (∑ i : Fin n, (jetD1 (spaceDir n i) w) ^ 2) ≠ 0) :
    IsFullyNonlinearPDE 1 (hamiltonJacobiQuadraticSymbol n) := by
  intro hq
  obtain ⟨aTop, a₀, h⟩ := hq
  set Q : ℝ := ∑ i : Fin n, (jetD1 (spaceDir n i) w) ^ 2 with hQ
  -- The quadratic term scales as `s²`.
  have hscale : ∀ s : ℝ,
      (∑ i : Fin n, (jetD1 (spaceDir n i) (s • w)) ^ 2) = s ^ 2 * Q := by
    intro s
    rw [hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul, mul_pow]
  -- Restricting the quasilinear representation to jets with top slot `s • w`,
  -- lower slot `0` and base point `0` gives the affine-in-`s` identity.
  have key : ∀ s : ℝ,
      s * timeD1 n w + s ^ 2 * Q
        = s * (aTop (fun _ => 0) 0) w + a₀ (fun _ => 0) 0 := by
    intro s
    obtain ⟨J, hJ⟩ : ∃ J : PDEJet 1 (SpaceTime n) ℝ,
        J = Fin.lastCases (s • w) (fun _ => 0) := ⟨_, rfl⟩
    have hval := h J 0
    have htop : J (Fin.last 1) = s • w := by rw [hJ]; exact Fin.lastCases_last
    have hlow : (fun j : Fin 1 => J j.castSucc) = fun _ => 0 := by
      rw [hJ]; funext j; simp
    have hJ1 : J 1 = s • w := by rw [hJ]; exact Fin.lastCases_last
    rw [htop, hlow] at hval
    rw [hamiltonJacobiQuadraticSymbol, hamiltonJacobiSymbol, hJ1, hscale s,
      map_smul, smul_eq_mul, map_smul, smul_eq_mul] at hval
    exact hval
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  norm_num at k0 k1 k2
  -- `k0 : a₀ = 0`; combining `k1`, `k2` forces `Q = 0`, contradicting `hw`.
  exact hw (by linarith [k0, k1, k2])

/-! ## `p`-Laplacian and minimal-surface equations (Evans §1.2.1b) — quasilinear -/

/-- The **Hessian–gradient contraction** `D²u(Du, Du) = ∑_{i,j} u_{xᵢ} u_{xⱼ} u_{xᵢxⱼ}`
on `ℝⁿ`, as a continuous linear functional of the second-order jet slot with
coefficients built from the (first-order) gradient values `u_{xᵢ} = jetD1 eᵢ`. It
is linear in the second-order slot, so it contributes to the top-order coefficient
of a quasilinear symbol. -/
def hessGradContract (n : ℕ) (v : PDEJetSlot 1 (EuclideanℝN n) ℝ) :
    PDEJetSlot 2 (EuclideanℝN n) ℝ →L[ℝ] ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    ((jetD1 (EuclideanSpace.single i (1 : ℝ)) v)
        * (jetD1 (EuclideanSpace.single j (1 : ℝ)) v))
      • jetD2 (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))

/-- **Evans §1.2.1b, `p`-Laplacian equation** `div(|Du|^{p-2} Du) = 0` on `ℝⁿ`.
For a classical solution the divergence expands to
`|Du|^{p-2} Δu + (p-2) |Du|^{p-4} D²u(Du, Du) = 0`, the form used here. Second
order. Reduces to Laplace's equation when `p = 2`. -/
def pLaplacianSymbol (n : ℕ) (p : ℝ) :
    PDEJet 2 (EuclideanℝN n) ℝ → EuclideanℝN n → ℝ :=
  fun ξ _ =>
    ‖ξ 1‖ ^ (p - 2) * laplaceContraction n (ξ 2)
      + (p - 2) * ‖ξ 1‖ ^ (p - 4) * hessGradContract n (ξ 1) (ξ 2)

/-- **The `p`-Laplacian is a quasilinear (2nd-order) PDE** (Evans Def. 2(iii)):
its top-order coefficients `|Du|^{p-2}` and `(p-2)|Du|^{p-4} (Du ⊗ Du)` depend on
the lower-order jet `Du`, and the equation is linear (indeed homogeneous) in the
top-order derivative `D²u`. -/
theorem pLaplacianSymbol_isQuasilinearPDE (n : ℕ) (p : ℝ) :
    IsQuasilinearPDE 2 (pLaplacianSymbol n p) := by
  refine ⟨fun low _ =>
      ‖low 1‖ ^ (p - 2) • laplaceContraction n
        + ((p - 2) * ‖low 1‖ ^ (p - 4)) • hessGradContract n (low 1),
    fun _ _ => 0, ?_⟩
  intro ξ x
  show ‖ξ 1‖ ^ (p - 2) * laplaceContraction n (ξ 2)
      + (p - 2) * ‖ξ 1‖ ^ (p - 4) * hessGradContract n (ξ 1) (ξ 2)
    = (‖ξ 1‖ ^ (p - 2) • laplaceContraction n
        + ((p - 2) * ‖ξ 1‖ ^ (p - 4)) • hessGradContract n (ξ 1)) (ξ 2) + 0
  rw [add_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]

/-- **Evans §1.2.1b, minimal-surface equation**
`div(Du / (1 + |Du|²)^{1/2}) = 0` on `ℝⁿ`. For a classical solution the divergence
expands to `(1 + |Du|²)^{-1/2} Δu - (1 + |Du|²)^{-3/2} D²u(Du, Du) = 0`, the form
used here. Second order. -/
def minimalSurfaceSymbol (n : ℕ) :
    PDEJet 2 (EuclideanℝN n) ℝ → EuclideanℝN n → ℝ :=
  fun ξ _ =>
    (1 + ‖ξ 1‖ ^ 2) ^ (-(1 : ℝ) / 2) * laplaceContraction n (ξ 2)
      - (1 + ‖ξ 1‖ ^ 2) ^ (-(3 : ℝ) / 2) * hessGradContract n (ξ 1) (ξ 2)

/-- **The minimal-surface equation is a quasilinear (2nd-order) PDE** (Evans
Def. 2(iii)): its top-order coefficients depend on the lower-order jet `Du`
through `(1 + |Du|²)^{-1/2}` and `(1 + |Du|²)^{-3/2}`, and it is homogeneous
linear in the top-order derivative `D²u`. -/
theorem minimalSurfaceSymbol_isQuasilinearPDE (n : ℕ) :
    IsQuasilinearPDE 2 (minimalSurfaceSymbol n) := by
  refine ⟨fun low _ =>
      (1 + ‖low 1‖ ^ 2) ^ (-(1 : ℝ) / 2) • laplaceContraction n
        - (1 + ‖low 1‖ ^ 2) ^ (-(3 : ℝ) / 2) • hessGradContract n (low 1),
    fun _ _ => 0, ?_⟩
  intro ξ x
  show (1 + ‖ξ 1‖ ^ 2) ^ (-(1 : ℝ) / 2) * laplaceContraction n (ξ 2)
      - (1 + ‖ξ 1‖ ^ 2) ^ (-(3 : ℝ) / 2) * hessGradContract n (ξ 1) (ξ 2)
    = ((1 + ‖ξ 1‖ ^ 2) ^ (-(1 : ℝ) / 2) • laplaceContraction n
        - (1 + ‖ξ 1‖ ^ 2) ^ (-(3 : ℝ) / 2) • hessGradContract n (ξ 1)) (ξ 2) + 0
  rw [add_zero, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]

end EvansLib
