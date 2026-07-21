import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Evans, Ch. 1 §1.1 — Partial differential equations: basic notions

This file formalizes the foundational definitions of Evans, *Partial Differential
Equations* (2nd ed.), Chapter 1 "Introduction": the notion of a `k`th-order PDE
and its solutions, the linear / semilinear / quasilinear / fully nonlinear
classification, systems of PDE, and the meaning of a well-posed problem and of a
classical solution.

## The jet formulation

Fix an open set `U ⊆ ℝⁿ`. Evans (Appendix A) writes the collection of all
`k`th-order partial derivatives of `u` at `x`, ordered as a point of `ℝ^(nᵏ)`, as
`Dᵏu(x)`. The faithful coordinate-free counterpart is the `k`th iterated Fréchet
derivative `iteratedFDeriv ℝ k u x`, a continuous `k`-linear form on `E = ℝⁿ`
(its `n^k` coordinates are exactly the partials `∂_{i₁}⋯∂_{i_k} u`).

Accordingly the **`k`-jet** of `u` at `x` is the tuple
`(u(x), Du(x), …, Dᵏu(x))`, packaged as a dependent function assigning to each
order `j ≤ k` the `j`-linear form `Dʲu(x)`. Evans' symbol
`F : ℝ^(nᵏ) × ⋯ × ℝ × U → ℝ` then becomes a function of the jet and the base
point, and equation (1) `F(Dᵏu(x), …, Du(x), u(x), x) = 0` says exactly that
`F (pdeJet k u x) x = 0`.

## Main definitions

* `PDEJet k E F` — the space of `k`-jet data valued in `F` (all `Dʲ`, `j ≤ k`).
* `pdeJet k u x` — the `k`-jet of `u : E → F` at `x`.
* `IsPDESolutionOn` — Evans Def. 1: `u` solves the `k`th-order PDE on `U`.
* `IsPDESystemSolutionOn` — Evans Def. 3: solutions of a `k`th-order system.
* `IsLinearPDE`, `IsHomogeneousLinearPDE`, `IsSemilinearPDE`, `IsQuasilinearPDE`,
  `IsFullyNonlinearPDE` — Evans Def. 2, the classification of a PDE symbol.
* `IsClassicalSolutionOn` — Evans §1.3: a `Cᵏ` solution.
* `PDEProblem`, `PDEProblem.IsWellPosed` — Evans §1.3: well-posedness.

## Main results

* `IsHomogeneousLinearPDE.isLinearPDE`, `IsLinearPDE.isSemilinearPDE`,
  `IsSemilinearPDE.isQuasilinearPDE` — the classification inclusions
  homogeneous-linear ⊆ linear ⊆ semilinear ⊆ quasilinear.
* `IsQuasilinearPDE.not_isFullyNonlinearPDE` — quasilinear PDE are, by
  definition, not fully nonlinear.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), Ch. 1.
-/

open scoped BigOperators

noncomputable section

namespace EvansLib

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## The jet of a function (Evans, Appendix A.3) -/

/-- The **order-`j` derivative slot**: a continuous `j`-linear form `Eʲ → F`.
For `E = ℝⁿ` and `F = ℝ` this is Evans' `ℝ^(nʲ)`, the ambient space of
`Dʲu(x)`. -/
abbrev PDEJetSlot (j : ℕ) (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Type _ :=
  ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F

/-- The space of **`k`-jet data** valued in `F`: an assignment, to each
derivative order `j ≤ k`, of an element of the order-`j` slot `PDEJetSlot j E F`.
This is the domain of Evans' symbol `F` (together with the base point). -/
abbrev PDEJet (k : ℕ) (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Type _ :=
  (j : Fin (k + 1)) → PDEJetSlot (j : ℕ) E F

/-- The **`k`-jet of `u` at `x`**: the tuple `(u(x), Du(x), …, Dᵏu(x))`, with the
order-`j` entry given by the `j`th iterated Fréchet derivative
`iteratedFDeriv ℝ j u x`. This is Evans' `(Dᵏu(x), …, Du(x), u(x))`. -/
def pdeJet (k : ℕ) (u : E → F) (x : E) : PDEJet k E F :=
  fun j => iteratedFDeriv ℝ (j : ℕ) u x

@[simp] lemma pdeJet_apply (k : ℕ) (u : E → F) (x : E) (j : Fin (k + 1)) :
    pdeJet k u x j = iteratedFDeriv ℝ (j : ℕ) u x := rfl

/-! ## `k`th-order partial differential equations (Evans, Def. 1) -/

/-- **Evans, Ch. 1, Def. 1 (`k`th-order PDE).** A function `u : E → F` is a
**solution on `U`** of the `k`th-order partial differential equation with symbol
`F` if
`F (Dᵏu(x), …, Du(x), u(x), x) = 0` for every `x ∈ U`,
i.e. `F (pdeJet k u x) x = 0`. The scalar case `F = ℝ` is Evans' equation (1);
`U` is an open subset of `E = ℝⁿ`. -/
def IsPDESolutionOn (k : ℕ) (U : Set E) (Φ : PDEJet k E F → E → F) (u : E → F) :
    Prop :=
  ∀ x ∈ U, Φ (pdeJet k u x) x = 0

/-- **Evans, Ch. 1, Def. 3 (`k`th-order system).** A map
`u : E → EuclideanSpace ℝ (Fin m)` (an `m`-tuple `(u¹, …, uᵐ)` of unknowns) is a
**solution on `U`** of the `k`th-order system with symbol `𝐅` if
`𝐅 (Dᵏu(x), …, u(x), x) = 0 ∈ ℝᵐ` for every `x ∈ U`. This is `IsPDESolutionOn`
with vector-valued codomain `ℝᵐ`. -/
def IsPDESystemSolutionOn (m k : ℕ) (U : Set E)
    (Φ : PDEJet k E (EuclideanSpace ℝ (Fin m)) → E → EuclideanSpace ℝ (Fin m))
    (u : E → EuclideanSpace ℝ (Fin m)) : Prop :=
  IsPDESolutionOn k U Φ u

/-! ## Classification: linear, semilinear, quasilinear, fully nonlinear
(Evans, Ch. 1, Def. 2) -/

/-- **Evans, Def. 2(i).** A scalar PDE symbol `Φ` is **linear** if it has the form
`∑_{|α| ≤ k} a_α(x) Dᵅu − f(x)`, i.e. there are coefficient functionals
`a j x : PDEJetSlot j E ℝ →L[ℝ] ℝ` (one per order `j ≤ k`, depending only on `x`)
and a source term `f` with
`Φ ξ x = (∑ j, a j x (ξ j)) − f x` for all jets `ξ` and points `x`.

Here `a j x` ranges over the dual of the order-`j` slot, which is precisely the
family of finite combinations `∑_{|α|=j} a_α(x) (·)_α` of the order-`j`
partials. -/
def IsLinearPDE (k : ℕ) (Φ : PDEJet k E ℝ → E → ℝ) : Prop :=
  ∃ (a : (j : Fin (k + 1)) → E → (PDEJetSlot (j : ℕ) E ℝ →L[ℝ] ℝ)) (f : E → ℝ),
    ∀ (ξ : PDEJet k E ℝ) (x : E), Φ ξ x = (∑ j, a j x (ξ j)) - f x

/-- **Evans, Def. 2(i), homogeneous case.** A linear PDE is **homogeneous** if the
source term vanishes, `f ≡ 0`; equivalently `Φ ξ x = ∑ j, a j x (ξ j)`. -/
def IsHomogeneousLinearPDE (k : ℕ) (Φ : PDEJet k E ℝ → E → ℝ) : Prop :=
  ∃ a : (j : Fin (k + 1)) → E → (PDEJetSlot (j : ℕ) E ℝ →L[ℝ] ℝ),
    ∀ (ξ : PDEJet k E ℝ) (x : E), Φ ξ x = ∑ j, a j x (ξ j)

/-- **Evans, Def. 2(ii).** A `k`th-order scalar PDE symbol `Φ` is **semilinear**
if it is linear in the top-order derivative with coefficients depending only on
`x`, plus an arbitrary function of the lower-order derivatives and `x`:
`Φ ξ x = aTop x (ξ (last k)) + a₀ (ξ|_{<k}) x`,
matching Evans' `∑_{|α|=k} a_α(x) Dᵅu + a₀(D^{k-1}u, …, u, x)`. -/
def IsSemilinearPDE (k : ℕ) (Φ : PDEJet k E ℝ → E → ℝ) : Prop :=
  ∃ (aTop : E → (PDEJetSlot k E ℝ →L[ℝ] ℝ))
    (a₀ : ((j : Fin k) → PDEJetSlot (j : ℕ) E ℝ) → E → ℝ),
    ∀ (ξ : PDEJet k E ℝ) (x : E),
      Φ ξ x = aTop x (ξ (Fin.last k)) + a₀ (fun j => ξ j.castSucc) x

/-- **Evans, Def. 2(iii).** A `k`th-order scalar PDE symbol `Φ` is **quasilinear**
if it is linear (affine) in the top-order derivative with coefficients that may
depend on the lower-order derivatives and on `x`:
`Φ ξ x = aTop (ξ|_{<k}) x (ξ (last k)) + a₀ (ξ|_{<k}) x`,
matching Evans' `∑_{|α|=k} a_α(D^{k-1}u, …, u, x) Dᵅu + a₀(D^{k-1}u, …, u, x)`. -/
def IsQuasilinearPDE (k : ℕ) (Φ : PDEJet k E ℝ → E → ℝ) : Prop :=
  ∃ (aTop : ((j : Fin k) → PDEJetSlot (j : ℕ) E ℝ) → E → (PDEJetSlot k E ℝ →L[ℝ] ℝ))
    (a₀ : ((j : Fin k) → PDEJetSlot (j : ℕ) E ℝ) → E → ℝ),
    ∀ (ξ : PDEJet k E ℝ) (x : E),
      Φ ξ x =
        aTop (fun j => ξ j.castSucc) x (ξ (Fin.last k)) + a₀ (fun j => ξ j.castSucc) x

/-- **Evans, Def. 2(iv).** A PDE is **fully nonlinear** if it depends nonlinearly
on the highest-order derivatives; formalized as the negation of being
quasilinear (affine in the top-order slot). -/
def IsFullyNonlinearPDE (k : ℕ) (Φ : PDEJet k E ℝ → E → ℝ) : Prop :=
  ¬ IsQuasilinearPDE k Φ

/-! ### The classification inclusions -/

/-- A homogeneous linear PDE is linear (take `f = 0`). -/
theorem IsHomogeneousLinearPDE.isLinearPDE {k : ℕ} {Φ : PDEJet k E ℝ → E → ℝ}
    (h : IsHomogeneousLinearPDE k Φ) : IsLinearPDE k Φ := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, 0, ?_⟩
  intro ξ x
  simp [ha ξ x]

/-- Every linear PDE is semilinear: the top-order coefficient depends only on `x`
and the whole lower-order-plus-source part is absorbed into `a₀`. -/
theorem IsLinearPDE.isSemilinearPDE {k : ℕ} {Φ : PDEJet k E ℝ → E → ℝ}
    (h : IsLinearPDE k Φ) : IsSemilinearPDE k Φ := by
  obtain ⟨a, f, ha⟩ := h
  refine ⟨fun x => a (Fin.last k) x,
    fun ξlow x => (∑ j : Fin k, a j.castSucc x (ξlow j)) - f x, ?_⟩
  intro ξ x
  rw [ha ξ x, Fin.sum_univ_castSucc (fun j => a j x (ξ j)), add_sub_right_comm, add_comm]
  rfl

/-- Every semilinear PDE is quasilinear: a top-order coefficient that depends only
on `x` is a special case of one that may also depend on the lower-order
derivatives. -/
theorem IsSemilinearPDE.isQuasilinearPDE {k : ℕ} {Φ : PDEJet k E ℝ → E → ℝ}
    (h : IsSemilinearPDE k Φ) : IsQuasilinearPDE k Φ := by
  obtain ⟨aTop, a₀, h⟩ := h
  exact ⟨fun _ x => aTop x, a₀, h⟩

/-- A quasilinear PDE is not fully nonlinear (fully nonlinear is defined as the
negation of quasilinear). -/
theorem IsQuasilinearPDE.not_isFullyNonlinearPDE {k : ℕ} {Φ : PDEJet k E ℝ → E → ℝ}
    (h : IsQuasilinearPDE k Φ) : ¬ IsFullyNonlinearPDE k Φ :=
  fun hfn => hfn h

/-! ## Classical solutions and well-posedness (Evans, §1.3) -/

/-- **Evans, §1.3, classical solution.** A **classical solution on `U`** of a
`k`th-order PDE is a `k`-times continuously differentiable function that satisfies
the equation on `U`. Requiring `u ∈ Cᵏ(U)` guarantees that all the derivatives
appearing in the equation exist and are continuous. -/
def IsClassicalSolutionOn (k : ℕ) (U : Set E) (Φ : PDEJet k E F → E → F)
    (u : E → F) : Prop :=
  ContDiffOn ℝ k u U ∧ IsPDESolutionOn k U Φ u

/-- An abstract boundary/initial-value **problem**: to each admissible datum
`d : D` it assigns the set `sol d ⊆ S` of solutions produced by that datum. -/
structure PDEProblem (D S : Type*) where
  /-- The set of solutions associated with a given datum. -/
  sol : D → Set S

/-- **Evans, §1.3, Def. (well-posed problem).** The problem `P` is **well-posed**
if there is a continuous solution operator `Φ : D → S` with `P.sol d = {Φ d}` for
every datum `d`. This encodes Evans' three requirements simultaneously:
(a) *existence* — `Φ d ∈ P.sol d`; (b) *uniqueness* — `P.sol d` is the singleton
`{Φ d}`; (c) *continuous dependence on the data* — `Φ` is continuous. -/
def PDEProblem.IsWellPosed {D S : Type*} [TopologicalSpace D] [TopologicalSpace S]
    (P : PDEProblem D S) : Prop :=
  ∃ Φ : D → S, Continuous Φ ∧ ∀ d, P.sol d = {Φ d}

end EvansLib
