import EvansLib.Ch01.MoreExamples

/-!
# Evans, Ch. 1 §1.2.1b — Nonlinear scalar equations

The genuinely nonlinear scalar examples of Evans' catalogue (§1.2.1b), expressed
as symbols in the jet framework of `EvansLib.Ch01.PDE` and classified as
quasilinear, semilinear, or fully nonlinear.

Unlike the linear catalogue (`EvansLib.Ch01.Examples`,
`EvansLib.Ch01.MoreExamples`), these exhibit the classification predicates in
their essential, non-degenerate forms:

* **Burgers' equation** `u_t + u u_x = 0` is our first *genuinely quasilinear*
  example — the top-order coefficient `u` depends on the lower-order jet (`u`
  itself), not merely on `x`, so it is captured by `IsQuasilinearPDE` but not by
  the semilinear reduction used for Laplace/heat/wave.
* **The KdV equation** `u_t + u u_x + u_{xxx} = 0` is semilinear at order `3`:
  its top-order term `u_{xxx}` is linear, while the nonlinearity `u u_x` sits in
  the lower-order part.
* **The nonlinear wave equation** `u_{tt} - Δu = f(u)` is semilinear at order `2`.
* **The Monge–Ampère equation** `det(D²u) = f` is *fully nonlinear*: its symbol is
  *quadratic* in the second-order derivatives, hence not affine in the top slot.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §1.2.1b.
-/

open scoped BigOperators

noncomputable section

namespace EvansLib

/-! ## Inviscid Burgers' equation (Evans §1.2.1b) — genuinely quasilinear -/

/-- **Evans §1.2.1b, inviscid Burgers' equation** `u_t + u u_x = 0` on space–time
`ℝ²` (one spatial variable). First order. The coefficient `u` of the top-order
derivative `u_x` depends on the solution value `u`, so this is the archetypal
*quasilinear* (but not semilinear) PDE. -/
def burgersSymbol : PDEJet 1 (SpaceTime 1) ℝ → SpaceTime 1 → ℝ :=
  fun ξ _ => timeD1 1 (ξ 1) + jetEval (SpaceTime 1) (ξ 0) * jetD1 (spaceDir 1 0) (ξ 1)

/-- **Burgers' equation is a quasilinear (1st-order) PDE** (Evans Def. 2(iii)):
its top-order coefficient `u_t + u·(·)_x` depends on the lower-order jet `u`. -/
theorem burgersSymbol_isQuasilinearPDE : IsQuasilinearPDE 1 burgersSymbol := by
  refine ⟨fun low _ => timeD1 1 + jetEval (SpaceTime 1) (low 0) • jetD1 (spaceDir 1 0),
    fun _ _ => 0, ?_⟩
  intro ξ x
  show timeD1 1 (ξ 1) + jetEval (SpaceTime 1) (ξ 0) * jetD1 (spaceDir 1 0) (ξ 1)
    = (timeD1 1 + jetEval (SpaceTime 1) (ξ 0) • jetD1 (spaceDir 1 0)) (ξ 1) + 0
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-! ## Korteweg–de Vries equation (Evans §1.2.1b) — semilinear, third order -/

/-- **Evans §1.2.1b, Korteweg–de Vries (KdV) equation** `u_t + u u_x + u_{xxx} = 0`
on space–time `ℝ²`. Third order. The top-order term `u_{xxx}` is linear with
constant coefficient; the nonlinearity `u u_x` involves only lower-order
derivatives, so the equation is *semilinear*. -/
def kdvSymbol : PDEJet 3 (SpaceTime 1) ℝ → SpaceTime 1 → ℝ :=
  fun ξ _ => timeD1 1 (ξ 1) + jetEval (SpaceTime 1) (ξ 0) * jetD1 (spaceDir 1 0) (ξ 1)
    + jetD3 (spaceDir 1 0) (ξ 3)

/-- **The KdV equation is a semilinear (3rd-order) PDE** (Evans Def. 2(ii)). -/
theorem kdvSymbol_isSemilinearPDE : IsSemilinearPDE 3 kdvSymbol := by
  refine ⟨fun _ => jetD3 (spaceDir 1 0),
    fun low _ => timeD1 1 (low 1) + jetEval (SpaceTime 1) (low 0) * jetD1 (spaceDir 1 0) (low 1),
    ?_⟩
  intro ξ x
  show timeD1 1 (ξ 1) + jetEval (SpaceTime 1) (ξ 0) * jetD1 (spaceDir 1 0) (ξ 1)
      + jetD3 (spaceDir 1 0) (ξ 3)
    = jetD3 (spaceDir 1 0) (ξ 3)
      + (timeD1 1 (ξ 1) + jetEval (SpaceTime 1) (ξ 0) * jetD1 (spaceDir 1 0) (ξ 1))
  ring

/-! ## Nonlinear wave equation (Evans §1.2.1b) — semilinear, second order -/

/-- **Evans §1.2.1b, nonlinear wave equation** `u_{tt} - Δu = f(u)`, i.e.
`u_{tt} - Δu - f(u) = 0`, on space–time. Semilinear: the top-order wave operator
`u_{tt} - Δu` is linear, the reaction `f(u)` is an arbitrary function of `u`. -/
def nonlinearWaveSymbol (n : ℕ) (f : ℝ → ℝ) :
    PDEJet 2 (SpaceTime n) ℝ → SpaceTime n → ℝ :=
  fun ξ _ => timeD2 n (ξ 2) - spatialLaplace n (ξ 2) - f (jetEval (SpaceTime n) (ξ 0))

/-- **The nonlinear wave equation is a semilinear (2nd-order) PDE** (Evans
Def. 2(ii)). -/
theorem nonlinearWaveSymbol_isSemilinearPDE (n : ℕ) (f : ℝ → ℝ) :
    IsSemilinearPDE 2 (nonlinearWaveSymbol n f) := by
  refine ⟨fun _ => timeD2 n - spatialLaplace n,
    fun low _ => -f (jetEval (SpaceTime n) (low 0)), ?_⟩
  intro ξ x
  show timeD2 n (ξ 2) - spatialLaplace n (ξ 2) - f (jetEval (SpaceTime n) (ξ 0))
    = (timeD2 n - spatialLaplace n) (ξ 2) + -f (jetEval (SpaceTime n) (ξ 0))
  rw [ContinuousLinearMap.sub_apply]
  ring

/-! ## Monge–Ampère equation (Evans §1.2.1b) — fully nonlinear via the determinant -/

/-- The **Monge–Ampère determinant** `det(D²u) = u_{xx} u_{yy} - u_{xy} u_{yx}` on
`ℝ²`, as a function of the second-order jet slot. It is *quadratic* in the slot,
which is the source of full nonlinearity. -/
def mongeDet (M : PDEJetSlot 2 (EuclideanℝN 2) ℝ) : ℝ :=
  jetD2 (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) M
      * jetD2 (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) M
    - jetD2 (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) M
      * jetD2 (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1) M

/-- **Evans §1.2.1b, Monge–Ampère equation** `det(D²u) = f` on `ℝ²`, i.e.
`u_{xx} u_{yy} - u_{xy} u_{yx} - f = 0`. Second order. -/
def mongeAmpereSymbol (f : EuclideanℝN 2 → ℝ) :
    PDEJet 2 (EuclideanℝN 2) ℝ → EuclideanℝN 2 → ℝ :=
  fun ξ x => mongeDet (ξ 2) - f x

/-- The determinant scales *quadratically*: `det(s·M) = s² det(M)`. This is the
algebraic obstruction to being affine (quasilinear) in the top-order slot. -/
theorem mongeDet_smul (s : ℝ) (M : PDEJetSlot 2 (EuclideanℝN 2) ℝ) :
    mongeDet (s • M) = s ^ 2 * mongeDet M := by
  simp only [mongeDet, map_smul, smul_eq_mul]
  ring

/-- **The Monge–Ampère equation is fully nonlinear** (Evans Def. 2(iv)): its
symbol `det(D²u) - f` is quadratic, not affine, in the top-order derivative
`D²u`. Concretely, were it quasilinear, `s ↦ det(s·M) = s² det(M)` restricted to
a line through a Hessian `M` with `det M ≠ 0` would be affine in `s`; evaluating
at `s = 0, 1, 2` forces `det M = 0`, a contradiction. The witness `M` (any
`2×2` jet slot with nonzero determinant) exists on `ℝ²`. -/
theorem mongeAmpereSymbol_isFullyNonlinearPDE (f : EuclideanℝN 2 → ℝ)
    (M : PDEJetSlot 2 (EuclideanℝN 2) ℝ) (hM : mongeDet M ≠ 0) :
    IsFullyNonlinearPDE 2 (mongeAmpereSymbol f) := by
  intro hq
  obtain ⟨aTop, a₀, h⟩ := hq
  -- The quasilinear representation at the zero lower jet and base point `0`,
  -- restricted to top slot `s • M`, gives for every scalar `s` the relation
  -- `s² det M - f 0 = s · aTop(0) M + a₀(0)`.
  have key : ∀ s : ℝ,
      s ^ 2 * mongeDet M - f 0 = s * aTop (fun _ => 0) 0 M + a₀ (fun _ => 0) 0 := by
    intro s
    -- The order-`2` jet `J` with top slot `s • M` and vanishing lower slots.
    obtain ⟨J, hJ⟩ : ∃ J : PDEJet 2 (EuclideanℝN 2) ℝ,
        J = Fin.lastCases (s • M) (fun _ => 0) := ⟨_, rfl⟩
    have hval := h J 0
    have htop : J (Fin.last 2) = s • M := by rw [hJ]; exact Fin.lastCases_last
    have hlow : (fun j : Fin 2 => J j.castSucc) = fun _ => 0 := by
      rw [hJ]; funext j; simp
    have hJ2 : J 2 = s • M := by rw [hJ]; exact Fin.lastCases_last
    rw [htop, hlow] at hval
    rw [mongeAmpereSymbol, hJ2, mongeDet_smul] at hval
    simp only [map_smul, smul_eq_mul] at hval
    exact hval
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  norm_num at k0 k1 k2
  exact hM (by linarith)

end EvansLib
