import EvansLib.Ch01.Systems

/-!
# Evans, Ch. 1 §1.2.2 — Maxwell, Euler and Navier–Stokes systems

This file completes Evans' §1.2.2 catalogue of physically important **systems** of
PDE in the jet framework of `EvansLib.Ch01.PDE` / `EvansLib.Ch01.Systems`:

* **Maxwell's equations** (§1.2.2a) `𝐄_t = curl 𝐁`, `𝐁_t = -curl 𝐄`,
  `div 𝐁 = div 𝐄 = 0` — a first-order **linear** system for `(𝐄, 𝐁) : ℝ⁴ → ℝ⁶`.
  It is *overdetermined*: `8` scalar equations for `6` unknowns, illustrating
  Evans' remark that "other systems may have fewer or more equations than
  unknowns". We therefore use a **non-square** linear-system predicate
  `IsLinearPDESystemGen`, with unknown space `ℝ⁶` and equation space `ℝ⁸`.
* **Euler's equations** (§1.2.2b) `𝐮_t + 𝐮·D𝐮 = -Dp`, `div 𝐮 = 0` for
  incompressible inviscid flow — a first-order **quasilinear** square system for
  the velocity–pressure pair `(𝐮, p) : ℝ^{n+1} → ℝ^{n+1}`. The convective term
  `𝐮·D𝐮 = ∑ⱼ uʲ 𝐮_{xⱼ}` carries the top-order (first) derivative with a
  coefficient `uʲ` depending on the lower-order jet `𝐮`.
* **Navier–Stokes equations** (§1.2.2b) `𝐮_t + 𝐮·D𝐮 - Δ𝐮 = -Dp`, `div 𝐮 = 0`
  for incompressible viscous flow — a second-order **semilinear** square system:
  the top-order operator `-Δ𝐮` (viscosity) is linear with constant coefficients,
  and the convective nonlinearity `𝐮·D𝐮` is of lower (first) order. Its
  lower-order part is exactly Euler's operator, so `EvansLib.eulerOp` is reused
  verbatim as the semilinear remainder `a₀`.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §1.2.2.
-/

open scoped BigOperators

noncomputable section

namespace EvansLib

/-! ## Scalar component extractors from vector jets

For a vector-valued unknown `𝐮 : ℝ^{n+1} → ℝᵐ` on space–time, we frequently need
the individual scalar partials `∂ₜ𝐮ᵃ`, `∂_{xᵢ}𝐮ᵃ`, `∂²_{xᵢxⱼ}𝐮ᵃ` and values `𝐮ᵃ`.
Each is a continuous linear functional of the corresponding jet slot, obtained by
post-composing the vector contractions of `EvansLib.Ch01.Systems` with the
coordinate projection `EuclideanSpace.proj a`. -/

/-- The value `𝐮ᵃ(x)` of the `a`-th component, a functional on the order-`0`
vector slot. -/
def valC (n m : ℕ) (a : Fin m) :
    PDEJetSlot 0 (SpaceTime n) (EuclideanℝN m) →L[ℝ] ℝ :=
  (EuclideanSpace.proj a).comp (jetEvalV n m)

/-- The time partial `∂ₜ𝐮ᵃ`, a functional on the order-`1` vector slot. -/
def timeDerivC (n m : ℕ) (a : Fin m) :
    PDEJetSlot 1 (SpaceTime n) (EuclideanℝN m) →L[ℝ] ℝ :=
  (EuclideanSpace.proj a).comp (timeD1V n m)

/-- The spatial partial `∂_{xᵢ}𝐮ᵃ`, a functional on the order-`1` vector slot. -/
def spaceDerivC (n m : ℕ) (i : Fin n) (a : Fin m) :
    PDEJetSlot 1 (SpaceTime n) (EuclideanℝN m) →L[ℝ] ℝ :=
  (EuclideanSpace.proj a).comp (jetD1V n m i)

/-- The second spatial partial `∂²_{xⱼxₖ}𝐮ᵃ`, a functional on the order-`2`
vector slot. -/
def space2DerivC (n m : ℕ) (j k : Fin n) (a : Fin m) :
    PDEJetSlot 2 (SpaceTime n) (EuclideanℝN m) →L[ℝ] ℝ :=
  (EuclideanSpace.proj a).comp (jetD2VecST n m (spaceDir n j) (spaceDir n k))

/-! ## Non-square linear systems (Evans, Def. 3 remark)

Evans notes that a system "may have fewer or more equations than unknowns". We
capture this with linear-system predicates whose unknown space `V` and equation
space `W` may differ; the square predicates of `EvansLib.Ch01.Systems` are the
case `V = W = ℝᵐ`. -/

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Non-square linear system.** A `k`th-order symbol `Φ` with unknown values in
`V` and equations valued in `W` is **linear** if
`Φ ξ x = (∑_{j ≤ k} A_j(x)(ξ_j)) - 𝐟(x)` for coefficient maps
`A_j x : PDEJetSlot j E V →L[ℝ] W` and a source `𝐟 : E → W`. -/
def IsLinearPDESystemGen (k : ℕ) (Φ : PDEJet k E V → E → W) : Prop :=
  ∃ (A : (j : Fin (k + 1)) → E → (PDEJetSlot (j : ℕ) E V →L[ℝ] W)) (f : E → W),
    ∀ (ξ : PDEJet k E V) (x : E), Φ ξ x = (∑ j, A j x (ξ j)) - f x

/-- **Non-square homogeneous linear system.** The source `𝐟 ≡ 0`. -/
def IsHomogeneousLinearPDESystemGen (k : ℕ) (Φ : PDEJet k E V → E → W) : Prop :=
  ∃ A : (j : Fin (k + 1)) → E → (PDEJetSlot (j : ℕ) E V →L[ℝ] W),
    ∀ (ξ : PDEJet k E V) (x : E), Φ ξ x = ∑ j, A j x (ξ j)

/-- A non-square homogeneous linear system is linear (take `𝐟 = 0`). -/
theorem IsHomogeneousLinearPDESystemGen.isLinearPDESystemGen {k : ℕ}
    {Φ : PDEJet k E V → E → W} (h : IsHomogeneousLinearPDESystemGen k Φ) :
    IsLinearPDESystemGen k Φ := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, 0, fun ξ x => by simp [hA ξ x]⟩

/-! ## Maxwell's equations (Evans §1.2.2a) — overdetermined linear system

The electromagnetic field on space–time `ℝ⁴ = ℝ_t × ℝ³` is the pair
`𝐮 = (𝐄, 𝐁) : ℝ⁴ → ℝ⁶`, with `𝐄 = (𝐮⁰, 𝐮¹, 𝐮²)` the electric field and
`𝐁 = (𝐮³, 𝐮⁴, 𝐮⁵)` the magnetic field. Maxwell's equations (physical constants
set to `1`) read
`𝐄_t = curl 𝐁`, `𝐁_t = -curl 𝐄`, `div 𝐄 = 0`, `div 𝐁 = 0`,
a total of `3 + 3 + 1 + 1 = 8` scalar equations for the `6` unknowns — an
*overdetermined* first-order linear system, valued in `ℝ⁸`. Here
`curl 𝐯 = (∂₁v² - ∂₂v¹, ∂₂v⁰ - ∂₀v², ∂₀v¹ - ∂₁v⁰)` with spatial coordinates
`x₀, x₁, x₂`. -/

/-- **Evans §1.2.2a, Maxwell operator.** The assembled first-order linear operator
`(𝐄, 𝐁) ↦ (𝐄_t - curl 𝐁, 𝐁_t + curl 𝐄, div 𝐄, div 𝐁) ∈ ℝ⁸`, written row by row
in the output basis `e₀, …, e₇`:

* rows `0,1,2`: `𝐄_t - curl 𝐁`, i.e.
  `∂ₜ𝐮⁰ - (∂₁𝐮⁵ - ∂₂𝐮⁴)`, `∂ₜ𝐮¹ - (∂₂𝐮³ - ∂₀𝐮⁵)`, `∂ₜ𝐮² - (∂₀𝐮⁴ - ∂₁𝐮³)`;
* rows `3,4,5`: `𝐁_t + curl 𝐄`, i.e.
  `∂ₜ𝐮³ + (∂₁𝐮² - ∂₂𝐮¹)`, `∂ₜ𝐮⁴ + (∂₂𝐮⁰ - ∂₀𝐮²)`, `∂ₜ𝐮⁵ + (∂₀𝐮¹ - ∂₁𝐮⁰)`;
* row `6`: `div 𝐄 = ∂₀𝐮⁰ + ∂₁𝐮¹ + ∂₂𝐮²`;
* row `7`: `div 𝐁 = ∂₀𝐮³ + ∂₁𝐮⁴ + ∂₂𝐮⁵`. -/
def maxwellOp : PDEJetSlot 1 (SpaceTime 3) (EuclideanℝN 6) →L[ℝ] EuclideanℝN 8 :=
  (timeDerivC 3 6 0 - (spaceDerivC 3 6 1 5 - spaceDerivC 3 6 2 4)).smulRight (euclidDir 8 0)
  + (timeDerivC 3 6 1 - (spaceDerivC 3 6 2 3 - spaceDerivC 3 6 0 5)).smulRight (euclidDir 8 1)
  + (timeDerivC 3 6 2 - (spaceDerivC 3 6 0 4 - spaceDerivC 3 6 1 3)).smulRight (euclidDir 8 2)
  + (timeDerivC 3 6 3 + (spaceDerivC 3 6 1 2 - spaceDerivC 3 6 2 1)).smulRight (euclidDir 8 3)
  + (timeDerivC 3 6 4 + (spaceDerivC 3 6 2 0 - spaceDerivC 3 6 0 2)).smulRight (euclidDir 8 4)
  + (timeDerivC 3 6 5 + (spaceDerivC 3 6 0 1 - spaceDerivC 3 6 1 0)).smulRight (euclidDir 8 5)
  + (spaceDerivC 3 6 0 0 + spaceDerivC 3 6 1 1 + spaceDerivC 3 6 2 2).smulRight (euclidDir 8 6)
  + (spaceDerivC 3 6 0 3 + spaceDerivC 3 6 1 4 + spaceDerivC 3 6 2 5).smulRight (euclidDir 8 7)

/-- **Evans §1.2.2a, Maxwell's equations** `𝐄_t = curl 𝐁`, `𝐁_t = -curl 𝐄`,
`div 𝐄 = div 𝐁 = 0`, as the symbol `(𝐄, 𝐁) ↦ maxwellOp(D𝐮) ∈ ℝ⁸` for
`𝐮 = (𝐄, 𝐁) : ℝ⁴ → ℝ⁶`. First order; `8` equations, `6` unknowns
(overdetermined). -/
def maxwellSymbol : PDEJet 1 (SpaceTime 3) (EuclideanℝN 6) → SpaceTime 3 → EuclideanℝN 8 :=
  fun ξ _ => maxwellOp (ξ 1)

/-- Homogeneous-linear-system coefficients for Maxwell's equations: the
first-order (`j = 1`) coefficient is `maxwellOp`, the zeroth-order coefficient
vanishes, and there is no source. -/
def maxwellCoeff : (j : Fin 2) → SpaceTime 3 →
    (PDEJetSlot (j : ℕ) (SpaceTime 3) (EuclideanℝN 6) →L[ℝ] EuclideanℝN 8) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => fun _ => maxwellOp
  | ⟨p + 2, h⟩ => absurd h (by omega)

/-- **Maxwell's equations form a homogeneous linear (1st-order, overdetermined)
system** (Evans Def. 3, non-square case): the symbol is `maxwellOp(D𝐮)` with no
source and no zeroth-order term. -/
theorem maxwellSymbol_isHomogeneousLinearPDESystemGen :
    IsHomogeneousLinearPDESystemGen 1 maxwellSymbol := by
  refine ⟨maxwellCoeff, ?_⟩
  intro ξ x
  show maxwellOp (ξ 1) = ∑ j, maxwellCoeff j x (ξ j)
  rw [Fin.sum_univ_two]
  have h0 : maxwellCoeff 0 x (ξ 0) = 0 := rfl
  have h1 : maxwellCoeff 1 x (ξ 1) = maxwellOp (ξ 1) := rfl
  rw [h0, h1, zero_add]

/-- Maxwell's equations are, in particular, a (non-square) linear system. -/
theorem maxwellSymbol_isLinearPDESystemGen :
    IsLinearPDESystemGen 1 maxwellSymbol :=
  maxwellSymbol_isHomogeneousLinearPDESystemGen.isLinearPDESystemGen

/-! ## Euler's equations (Evans §1.2.2b) — quasilinear system

Incompressible inviscid flow has velocity–pressure unknown
`𝐮 = (u⁰, …, u^{n-1}, p) : ℝ^{n+1} → ℝ^{n+1}`, with velocity
`v = (u⁰, …, u^{n-1})` (components `0, …, n-1`) and pressure `p = u^n`
(component `n`). Euler's equations are the `n` momentum equations
`vⁱ_t + ∑ⱼ vʲ vⁱ_{xⱼ} + p_{xᵢ} = 0` together with incompressibility
`div v = ∑ⱼ vʲ_{xⱼ} = 0`, an `(n+1) × (n+1)` first-order system. -/

/-- **Evans §1.2.2b, Euler operator.** The first-order operator assembling the
momentum and incompressibility rows: for each velocity coordinate `i`,
`vⁱ_t + ∑ⱼ vʲ vⁱ_{xⱼ} + p_{xᵢ}` (row `i`), and `div v = ∑ⱼ vʲ_{xⱼ}` in the
pressure row `n`. The convective coefficients `vʲ = valC j (𝐮)` depend on the
lower-order jet value `𝐮(x)`, supplied via `u0`. This same operator is the
lower-order (first-order) part of Navier–Stokes. -/
def eulerOp (n : ℕ) (u0 : PDEJetSlot 0 (SpaceTime n) (EuclideanℝN (n + 1))) :
    PDEJetSlot 1 (SpaceTime n) (EuclideanℝN (n + 1)) →L[ℝ] EuclideanℝN (n + 1) :=
  (∑ i : Fin n,
    (timeDerivC n (n + 1) i.castSucc
      + ∑ j : Fin n, (valC n (n + 1) j.castSucc u0) • spaceDerivC n (n + 1) j i.castSucc
      + spaceDerivC n (n + 1) i (Fin.last n)).smulRight (euclidDir (n + 1) i.castSucc))
  + (∑ j : Fin n, spaceDerivC n (n + 1) j j.castSucc).smulRight (euclidDir (n + 1) (Fin.last n))

/-- **Evans §1.2.2b, Euler's equations** `𝐮_t + 𝐮·D𝐮 = -Dp`, `div 𝐮 = 0` for
incompressible inviscid flow, as the symbol `ξ ↦ eulerOp(𝐮(x))(D𝐮(x))` for the
velocity–pressure field `𝐮 = (v, p) : ℝ^{n+1} → ℝ^{n+1}`. First order. -/
def eulerSymbol (n : ℕ) :
    PDEJet 1 (SpaceTime n) (EuclideanℝN (n + 1)) → SpaceTime n → EuclideanℝN (n + 1) :=
  fun ξ _ => eulerOp n (ξ 0) (ξ 1)

/-- **Euler's equations form a quasilinear (1st-order) system** (Evans
Def. 2(iii) for systems): the top-order (first-derivative) coefficients include
the convective factors `vʲ`, which depend on the lower-order jet `𝐮`; there is no
zeroth-order remainder. -/
theorem eulerSymbol_isQuasilinearPDESystem (n : ℕ) :
    IsQuasilinearPDESystem (n + 1) 1 (eulerSymbol n) := by
  refine ⟨fun low _ => eulerOp n (low 0), fun _ _ => 0, ?_⟩
  intro ξ x
  show eulerOp n (ξ 0) (ξ 1) = eulerOp n (ξ 0) (ξ 1) + 0
  rw [add_zero]

/-! ## Navier–Stokes equations (Evans §1.2.2b) — semilinear system

Adding viscosity `-Δ𝐮` to Euler gives incompressible viscous flow:
`𝐮_t + 𝐮·D𝐮 - Δ𝐮 = -Dp`, `div 𝐮 = 0`. The viscous term `-Δv` is the top-order
(second) operator, linear with constant coefficients; the convective term
`𝐮·D𝐮` is of lower (first) order. Hence the system is **semilinear**, and its
lower-order remainder is precisely Euler's operator `eulerOp`. -/

/-- **Evans §1.2.2b, viscous (Stokes) operator** `-Δv`: for each velocity
coordinate `i`, the second-order operator `-Δvⁱ = -∑ⱼ ∂²_{xⱼxⱼ}𝐮ⁱ` placed in
output row `i`; the pressure row is `0`. This is the top-order part of
Navier–Stokes. -/
def viscousOp (n : ℕ) :
    PDEJetSlot 2 (SpaceTime n) (EuclideanℝN (n + 1)) →L[ℝ] EuclideanℝN (n + 1) :=
  ∑ i : Fin n,
    (-∑ j : Fin n, space2DerivC n (n + 1) j j i.castSucc).smulRight (euclidDir (n + 1) i.castSucc)

/-- **Evans §1.2.2b, Navier–Stokes equations** `𝐮_t + 𝐮·D𝐮 - Δ𝐮 = -Dp`,
`div 𝐮 = 0` for incompressible viscous flow, as the symbol
`ξ ↦ viscousOp(D²𝐮) + eulerOp(𝐮)(D𝐮)`: the viscous second-order part plus
Euler's first-order part. Second order. -/
def nsSymbol (n : ℕ) :
    PDEJet 2 (SpaceTime n) (EuclideanℝN (n + 1)) → SpaceTime n → EuclideanℝN (n + 1) :=
  fun ξ _ => viscousOp n (ξ 2) + eulerOp n (ξ 0) (ξ 1)

/-- **The Navier–Stokes equations form a semilinear (2nd-order) system** (Evans
Def. 2(ii) for systems): the top-order coefficient is the constant linear
viscous operator `-Δ`, and the convective nonlinearity `𝐮·D𝐮` (Euler's operator)
is of lower order. -/
theorem nsSymbol_isSemilinearPDESystem (n : ℕ) :
    IsSemilinearPDESystem (n + 1) 2 (nsSymbol n) := by
  refine ⟨fun _ => viscousOp n, fun low _ => eulerOp n (low 0) (low 1), ?_⟩
  intro ξ x
  rfl

/-- The Navier–Stokes equations are, in particular, a quasilinear system. -/
theorem nsSymbol_isQuasilinearPDESystem (n : ℕ) :
    IsQuasilinearPDESystem (n + 1) 2 (nsSymbol n) :=
  (nsSymbol_isSemilinearPDESystem n).isQuasilinearPDESystem

end EvansLib
