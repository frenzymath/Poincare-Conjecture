import EvansLib.Ch01.PDE

/-!
# Evans, Ch. 1 §1.2 — Examples of partial differential equations

Concrete PDE from Evans' catalogue (§1.2), expressed as symbols in the jet
framework of `EvansLib.Ch01.PDE`, together with their place in the
linear / semilinear / quasilinear / fully nonlinear classification.

The flagship is **Laplace's equation** `Δu = ∑ᵢ u_{xᵢxᵢ} = 0`
(Evans §1.2.1a), whose symbol is the trace (contraction) of the second-order
jet slot; we verify it is a linear PDE, validating the classification
machinery end-to-end.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §1.2.
-/

open scoped BigOperators

noncomputable section

namespace EvansLib

/-- Euclidean `n`-space `ℝⁿ`, the domain space for the spatial PDE below. -/
abbrev EuclideanℝN (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-! ## Laplace's equation (Evans §1.2.1a) -/

/-- The **Laplacian contraction** on the second-order jet slot: the continuous
linear functional `M ↦ ∑ᵢ M(eᵢ, eᵢ)` sending the bilinear form `D²u(x)` to its
trace `∑ᵢ u_{xᵢxᵢ}(x) = Δu(x)`. Here `eᵢ = EuclideanSpace.single i 1` are the
standard basis vectors of `ℝⁿ`. -/
def laplaceContraction (n : ℕ) : PDEJetSlot 2 (EuclideanℝN n) ℝ →L[ℝ] ℝ :=
  ∑ i : Fin n, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => EuclideanℝN n) ℝ
    (fun _ => EuclideanSpace.single i (1 : ℝ))

/-- **Evans §1.2.1a, Laplace's equation** `Δu = ∑ᵢ u_{xᵢxᵢ} = 0`.
The symbol `F(D²u(x), …, x) = Δu(x)` is the trace of the second-order jet slot;
solutions on `U` are exactly the functions harmonic on `U`. -/
def laplaceSymbol (n : ℕ) : PDEJet 2 (EuclideanℝN n) ℝ → EuclideanℝN n → ℝ :=
  fun ξ _ => laplaceContraction n (ξ 2)

/-- The coefficient family exhibiting Laplace's equation as a linear PDE: the
top-order (`j = 2`) coefficient is the Laplacian contraction, and the lower-order
coefficients vanish. -/
def laplaceCoeff (n : ℕ) :
    (j : Fin 3) → EuclideanℝN n → (PDEJetSlot (j : ℕ) (EuclideanℝN n) ℝ →L[ℝ] ℝ) :=
  fun j => match j with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => fun _ => laplaceContraction n
  | ⟨m + 3, h⟩ => absurd h (by omega)

/-- **Laplace's equation is a linear (hence 2nd-order) PDE** (Evans Def. 2(i)):
`Δu = ∑_{|α| = 2} a_α Dᵅu` with constant coefficients `a_α ∈ {0, 1}` and no
source term. This validates the linear-classification predicate on a concrete
equation from Evans' catalogue. -/
theorem laplaceSymbol_isLinearPDE (n : ℕ) : IsLinearPDE 2 (laplaceSymbol n) := by
  refine ⟨laplaceCoeff n, 0, ?_⟩
  intro ξ x
  show laplaceContraction n (ξ 2) = (∑ j, laplaceCoeff n j x (ξ j)) - (0 : EuclideanℝN n → ℝ) x
  rw [Fin.sum_univ_three]
  have h0 : laplaceCoeff n 0 x (ξ 0) = 0 := rfl
  have h1 : laplaceCoeff n 1 x (ξ 1) = 0 := rfl
  have h2 : laplaceCoeff n 2 x (ξ 2) = laplaceContraction n (ξ 2) := rfl
  rw [h0, h1, h2]
  simp

/-- Laplace's equation is, in particular, semilinear and quasilinear (Evans
Def. 2), by the classification inclusions. -/
theorem laplaceSymbol_isQuasilinearPDE (n : ℕ) : IsQuasilinearPDE 2 (laplaceSymbol n) :=
  (laplaceSymbol_isLinearPDE n).isSemilinearPDE.isQuasilinearPDE

end EvansLib
