/-
Chapter 4, "Connections", §"Connections in the Tangent Bundle": the transformation
law for connection coefficients under a change of local frame (Lee, Proposition 4.7).

Let `∇` be a connection in `TM` and let `(E_i) = s` and `(Ẽ_i) = s'` be two smooth
local frames for `TM` over the same open set `u`, related by the transition matrix
`A^j_i(x) = hs.coeff j x (s' i x)` (the components of `Ẽ_i` in the `E`-frame), so that
`Ẽ_i = A^j_i E_j`.  Write `(A^{-1})^k_p(x) = hs'.coeff k x (s p x)` (the components of
`E_p` in the `Ẽ`-frame) for the inverse transition, and `Γ^k_{ij}`, `Γ̃^k_{ij}` for the
connection coefficients (Lee (4.8)) in the two frames.  Lee's Proposition 4.7 states

  `Γ̃^k_{ij} = (A^{-1})^k_p A^q_i A^r_j Γ^p_{qr} + (A^{-1})^k_p A^q_i E_q(A^p_j)`,

where `E_q(A^p_j) = (d% A^p_j)(E_q)` is the directional derivative of the transition
component `A^p_j` along the frame vector `E_q`.  The first term is the `(1,2)`-tensor
transformation law; the second, inhomogeneous term involves derivatives of the
transition matrix, reflecting that a connection is not a tensor.

The proof reuses Lee's frame formula (4.9) `covariantDeriv_eq_connectionCoeff_formula`:
`∇_{Ẽ_i} Ẽ_j` is computed by rewriting the section `Ẽ_j = ∑_r A^r_j E_r` in the
`E`-frame (locality `covariantDeriv_congr_germ` swaps the germ; the transition
components are smooth by `IsLocalFrameOn.contMDiffAt_coeff`), and then reading off the
`k`-th component in the `Ẽ`-frame.  Expanding the direction `Ẽ_i = A^q_i E_q` in the
derivative term yields Lee's explicit `A^q_i E_q(A^p_j)`.
-/
import LeeLib.Ch04.ConnectionCoefficients
import LeeLib.Ch04.Locality
import LeeLib.AppendixA.LocalFrameCriterion

namespace LeeLib.Ch04

open Bundle
open scoped Manifold ContDiff Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι] {n : ℕ∞ω} [ENat.LEInfty n] {u : Set M}
  {s s' : ι → Π x : M, TangentSpace I x}

/-- **Lee's Proposition 4.7 (Transformation Law for Connection Coefficients).**
For two smooth local frames `(E_i) = s` and `(Ẽ_i) = s'` for `TM` over an open set `u`,
with transition components `A^q_i = hs.coeff q · (s' i ·)` (`Ẽ_i = A^q_i E_q`) and inverse
`(A^{-1})^k_p = hs'.coeff k · (s p ·)` (`E_p = (A^{-1})^k_p Ẽ_k`), the connection
coefficients transform as

  `Γ̃^k_{ij} = (A^{-1})^k_p A^q_i A^r_j Γ^p_{qr} + (A^{-1})^k_p A^q_i E_q(A^p_j)`,

with `E_q(A^p_j) = (d% (A^p_j))(E_q)` the directional derivative of the transition
component `A^p_j = hs.coeff p · (s' j ·)` along `E_q = s q`. -/
theorem connectionCoeff_transformation_law
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (cov : Connection I E (TangentSpace I : M → Type _))
    (hs : IsLocalFrameOn I E n s u) (hs' : IsLocalFrameOn I E n s' u)
    (hu : IsOpen u) (hn : 1 ≤ n) {x : M} (hx : x ∈ u) (i j k : ι) :
    connectionCoeff cov hs' i j k x
      = (∑ p, ∑ q, ∑ r, hs'.coeff k x (s p x) * hs.coeff q x (s' i x)
            * hs.coeff r x (s' j x) * connectionCoeff cov hs q r p x)
        + ∑ p, ∑ q, hs'.coeff k x (s p x) * hs.coeff q x (s' i x)
            * (d% (fun y => hs.coeff p y (s' j y)) x) (s q x) := by
  classical
  have hn0 : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  -- smoothness of the old frame vectors and of the transition-matrix component functions
  have hsr : ∀ r, MDiffAt (T% (s r)) x := fun r => (hs.contMDiffAt hu hx r).mdifferentiableAt hn0
  have hAmd : ∀ r, MDiffAt (fun y => hs.coeff r y (s' j y)) x := fun r =>
    (IsLocalFrameOn.contMDiffAt_coeff hs hu hx (hs'.contMDiffAt hu hx j) r).mdifferentiableAt hn0
  have hYmd : MDiffAt (T% (fun y => ∑ r, hs.coeff r y (s' j y) • s r y)) x :=
    MDifferentiableAt.sum_section (fun r => (hAmd r).smul_section (hsr r))
  have hsj' : MDiffAt (T% (s' j)) x := (hs'.contMDiffAt hu hx j).mdifferentiableAt hn0
  -- `Ẽ_j` agrees with its `E`-frame expansion near `x` (locality)
  have hev : ∀ᶠ y in 𝓝 x, s' j y = (fun y => ∑ r, hs.coeff r y (s' j y) • s r y) y := by
    filter_upwards [hu.mem_nhds hx] with y hy
    exact hs.coeff_sum_eq (s' j) hy
  -- `∇_{Ẽ_i} Ẽ_j` via Lee's frame formula (4.9), read in the `E`-frame
  have hcov : covariantDeriv cov (s' i) (s' j) x
      = ∑ p, ((d% (fun y => hs.coeff p y (s' j y)) x) (s' i x)
              + ∑ q, ∑ r, hs.coeff q x (s' i x) * hs.coeff r x (s' j x)
                  * connectionCoeff cov hs q r p x) • s p x := by
    rw [covariantDeriv_congr_germ cov (s' i) hsj' hYmd hev]
    exact covariantDeriv_eq_connectionCoeff_formula cov hs hu hn (s' i)
      (fun r => fun y => hs.coeff r y (s' j y)) hx hAmd
  -- Expand `Ẽ_i(A^p_j) = (d% A^p_j)(Ẽ_i) = ∑_q A^q_i E_q(A^p_j)`
  have hexp : ∀ p, (d% (fun y => hs.coeff p y (s' j y)) x) (s' i x)
      = ∑ q, hs.coeff q x (s' i x)
          * (d% (fun y => hs.coeff p y (s' j y)) x) (s q x) := by
    intro p
    conv_lhs => rw [hs.coeff_sum_eq (s' i) hx]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  -- Read off the `k`-th component of `∇_{Ẽ_i} Ẽ_j` in the `Ẽ`-frame, then match Lee's formula
  rw [show connectionCoeff cov hs' i j k x
      = hs'.coeff k x (covariantDeriv cov (s' i) (s' j) x) from rfl, hcov, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [hexp p, add_mul, add_comm]
  refine congr_arg₂ (· + ·) ?_ ?_
  · -- tensor term
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  · -- inhomogeneous derivative term
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring

end LeeLib.Ch04
