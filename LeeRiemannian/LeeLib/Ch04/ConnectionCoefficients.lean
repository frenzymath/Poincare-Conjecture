/-
Chapter 4, "Connections", §"Connections in the Tangent Bundle": connection
coefficients.

Let `∇` be a connection in `TM` and `(E_i)` a smooth local frame for `TM` over an
open set `U`.  Expanding `∇_{E_i} E_j` in the frame defines Lee's **connection
coefficients** `Γ^k_{ij} : U → ℝ` by

  `∇_{E_i} E_j = Γ^k_{ij} E_k`   (Lee's equation (4.8)).

This file introduces `connectionCoeff` and proves this defining relation using the
frame-coefficient machinery `Bundle.IsLocalFrameOn.coeff` / `coeff_sum_eq`.  The
connection coefficients are the data that turn the covariant derivative into the
concrete coordinate expression (Lee's Proposition 4.6, equation (4.9)) underlying
the geodesic equation and parallel transport.
-/
import LeeLib.Ch04.Connection
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

namespace LeeLib.Ch04

open Bundle
open scoped Manifold ContDiff Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {ι : Type*} [Fintype ι] {n : ℕ∞ω} {u : Set M}
  {s : ι → Π x : M, TangentSpace I x}

/-- **Connection coefficients** (Lee, equation (4.8)): given a connection `∇` in
`TM` and a smooth local frame `(E_i) = s` for `TM` over `u`, the coefficient
`Γ^k_{ij}(x)` is the `k`-th frame component of `∇_{E_i} E_j` at `x`.  Off `u` it is
the junk value `0`. -/
noncomputable def connectionCoeff (cov : Connection I E (TangentSpace I : M → Type _))
    (hs : IsLocalFrameOn I E n s u) (i j k : ι) : M → ℝ :=
  fun x => hs.coeff k x (covariantDeriv cov (s i) (s j) x)

/-- Lee's equation (4.8), the defining relation of the connection coefficients:
`∇_{E_i} E_j = Γ^k_{ij} E_k` on the frame domain `u`. -/
theorem covariantDeriv_frame_eq_sum_connectionCoeff (cov : Connection I E (TangentSpace I : M → Type _))
    (hs : IsLocalFrameOn I E n s u) (i j : ι) {x : M} (hx : x ∈ u) :
    covariantDeriv cov (s i) (s j) x
      = ∑ k, connectionCoeff cov hs i j k x • s k x :=
  hs.coeff_sum_eq (covariantDeriv cov (s i) (s j)) hx

/-- Direction-decomposition step of Lee's formula (4.9): the covariant derivative
of a frame vector `E_j` in an arbitrary direction `X = X^i E_i` expands as
`∇_X E_j = X^i ∇_{E_i} E_j` on the frame domain `u`.  This is `C^∞(M)`-linearity
of `∇` in its direction argument, read off in the frame (`X^i = hs.coeff i X`). -/
theorem covariantDeriv_dir_frame_eq_sum (cov : Connection I E (TangentSpace I : M → Type _))
    (hs : IsLocalFrameOn I E n s u) (X : Π x : M, TangentSpace I x) (j : ι)
    {x : M} (hx : x ∈ u) :
    covariantDeriv cov X (s j) x
      = ∑ i, hs.coeff i x (X x) • covariantDeriv cov (s i) (s j) x := by
  simp only [covariantDeriv_apply]
  conv_lhs => rw [hs.coeff_sum_eq X hx]
  rw [map_sum]
  simp only [map_smul]

/-- Combining the two previous results: in a smooth local frame, `∇_X E_j` is
determined by the connection coefficients and the frame components of `X`,
`∇_X E_j = X^i Γ^k_{ij} E_k`, on the frame domain `u`. -/
theorem covariantDeriv_dir_frame_eq_sum_connectionCoeff
    (cov : Connection I E (TangentSpace I : M → Type _))
    (hs : IsLocalFrameOn I E n s u) (X : Π x : M, TangentSpace I x) (j : ι)
    {x : M} (hx : x ∈ u) :
    covariantDeriv cov X (s j) x
      = ∑ i, ∑ k, hs.coeff i x (X x) • connectionCoeff cov hs i j k x • s k x := by
  rw [covariantDeriv_dir_frame_eq_sum cov hs X j hx]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [covariantDeriv_frame_eq_sum_connectionCoeff cov hs i j hx, Finset.smul_sum]

/-- Covariant differentiation commutes with finite sums of sections, each differentiable at the
point: `∇_X (∑_j σ_j) = ∑_j ∇_X σ_j`.  (This is `ℝ`-additivity of `∇` in its section argument,
iterated over a `Finset`.) -/
theorem covariantDeriv_finset_sum {κ : Type*}
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (cov : Connection I E (TangentSpace I : M → Type _)) (X : Π x : M, TangentSpace I x)
    (t : Finset κ) (σ : κ → Π x : M, TangentSpace I x) {x : M}
    (hσ : ∀ j, MDiffAt (T% (σ j ·)) x) :
    covariantDeriv cov X (fun y => ∑ j ∈ t, σ j y) x = ∑ j ∈ t, covariantDeriv cov X (σ j) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      show cov (fun _ => (0 : TangentSpace I _)) x (X x) = 0
      rw [show (fun _ : M => (0 : TangentSpace I _)) = (0 : Π x : M, TangentSpace I x) from rfl,
        cov.zero]
      simp
  | @insert j t hj ih =>
      have hP : MDiffAt (T% (fun y => ∑ i ∈ t, σ i y)) x := MDifferentiableAt.sum_section hσ
      have hsec : (fun y => ∑ i ∈ insert j t, σ i y)
          = σ j + (fun y => ∑ i ∈ t, σ i y) := by
        funext y; simp [Finset.sum_insert hj]
      rw [Finset.sum_insert hj, hsec, covariantDeriv_add_section cov X (hσ j) hP, ih]

/-- **Lee's Proposition 4.6, equation (4.9)**: the frame expression of the covariant derivative.
For a smooth vector field `Y = Y^j E_j` written in a smooth local frame `(E_i) = s` over an open
set `u`, and any direction `X` with frame components `X^i = hs.coeff i (X)`, the covariant
derivative is
`∇_X Y = (X(Y^k) + X^i Y^j Γ^k_{ij}) E_k`
on `u`, where `Γ^k_{ij}` are the connection coefficients and `X(Y^k) = d% Y^k (X)` is the
directional derivative of the `k`-th component.  Here `Y^k = f k` is presented as the given
smooth frame-component functions. -/
theorem covariantDeriv_eq_connectionCoeff_formula
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (cov : Connection I E (TangentSpace I : M → Type _))
    (hs : IsLocalFrameOn I E n s u) (hu : IsOpen u) (hn : 1 ≤ n)
    (X : Π x : M, TangentSpace I x) (f : ι → M → ℝ) {x : M} (hx : x ∈ u)
    (hf : ∀ j, MDiffAt (f j) x) :
    covariantDeriv cov X (fun y => ∑ j, f j y • s j y) x
      = ∑ k, ((d% (f k) x) (X x)
              + ∑ i, ∑ j, hs.coeff i x (X x) * f j x * connectionCoeff cov hs i j k x) • s k x := by
  have hn0 : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  have hsj : ∀ j, MDiffAt (T% (s j)) x := fun j => (hs.contMDiffAt hu hx j).mdifferentiableAt hn0
  -- Split the finite sum of sections, then apply the product rule to each term.
  have hsplit : covariantDeriv cov X (fun y => ∑ j, f j y • s j y) x
      = ∑ j, covariantDeriv cov X (f j • s j) x :=
    covariantDeriv_finset_sum cov X Finset.univ (fun j => f j • s j)
      (fun j => (hf j).smul_section (hsj j))
  rw [hsplit]
  -- Each term: `∇_X (Y^j E_j) = Y^j ∇_X E_j + X(Y^j) E_j`, and `∇_X E_j = X^i Γ^k_{ij} E_k`.
  have hterm : ∀ j, covariantDeriv cov X (f j • s j) x
      = f j x • (∑ i, ∑ k, hs.coeff i x (X x) • connectionCoeff cov hs i j k x • s k x)
        + (d% (f j) x) (X x) • s j x := fun j => by
    rw [covariantDeriv_smul_fun cov X (hsj j) (hf j),
      covariantDeriv_dir_frame_eq_sum_connectionCoeff cov hs X j hx]
  simp only [hterm]
  rw [Finset.sum_add_distrib, add_comm]
  -- Split the target the same way (grouped by the output index `k`).
  simp only [add_smul]
  rw [Finset.sum_add_distrib]
  -- The product-rule terms `∑_j X(Y^j) E_j = ∑_k X(Y^k) E_k` match on the nose; only the
  -- Christoffel terms need reindexing to group by the output frame index `k`.
  refine congr_arg₂ (· + ·) rfl ?_
  simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  ring

end LeeLib.Ch04
