import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.BigOperators.Pi

/-!
# Basis invariance of the diagonal of a bilinear map over orthonormal bases

For a real inner product space $V$, an arbitrary $\mathbb{R}$-module
$W$, a bilinear map $B : V \to_\ell[\mathbb{R}] V \to_\ell[\mathbb{R}] W$
and two orthonormal bases $b, b'$ of $V$:
$$\sum_i B(b_i, b_i) \;=\; \sum_i B(b'_i, b'_i).$$

Proof: expand each $b'_j$ via `OrthonormalBasis.sum_repr'` as
$\sum_k \langle b_k, b'_j\rangle b_k$, distribute through bilinearity,
swap sums, apply Parseval (`OrthonormalBasis.sum_inner_mul_inner`) to
collapse $\sum_j \langle b_k, b'_j\rangle\langle b_l, b'_j\rangle$ to
$\langle b_k, b_l\rangle$, then use orthonormality of $b$
($\langle b_k, b_l\rangle = \delta_{kl}$) to collapse the double sum
to $\sum_k B(b_k, b_k)$.

Result: basis-invariance of the trace-style diagonal of a bilinear
form over a real inner product space — independent of any symmetry
of $B$ (the antisymmetric part contributes zero on the diagonal
automatically).

Used in: heart-of-Bochner closure, where $B$ is the bilinear map
$(v, w) \mapsto \mathrm{secondCovDerivAt}\,(\nabla f)\,\alpha\,v\,w$
and the basis-invariance bridges `smoothOrthoFrame g α · α` to
`stdOrthonormalBasis ℝ (TangentSpace I α)`.
-/

namespace OrthonormalBasis

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

open scoped InnerProductSpace

/-- Expand `B (b' j) (b' j)` via the representation of `b' j` in basis
$b$, distributing bilinearity in both slots. -/
private lemma expand_diagonal_via_other_basis
    (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis ι' ℝ V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (j : ι') :
    B (b' j) (b' j) =
      ∑ k, ∑ l, (⟪b k, b' j⟫_ℝ * ⟪b l, b' j⟫_ℝ) • B (b k) (b l) := by
  have h_repr : b' j = ∑ k, ⟪b k, b' j⟫_ℝ • b k := (b.sum_repr' (b' j)).symm
  -- Slot 1 substitute, then distribute B (slot 1 is a LinearMap-action).
  calc B (b' j) (b' j)
      = B (∑ k, ⟪b k, b' j⟫_ℝ • b k) (b' j) := by rw [← h_repr]
    _ = (∑ k, ⟪b k, b' j⟫_ℝ • B (b k)) (b' j) := by
        congr 1
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        exact LinearMap.map_smul B _ _
    _ = ∑ k, (⟪b k, b' j⟫_ℝ • B (b k)) (b' j) := LinearMap.sum_apply _ _ _
    _ = ∑ k, ⟪b k, b' j⟫_ℝ • B (b k) (b' j) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        exact LinearMap.smul_apply _ _ _
    _ = ∑ k, ⟪b k, b' j⟫_ℝ • B (b k) (∑ l, ⟪b l, b' j⟫_ℝ • b l) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [← h_repr]
    _ = ∑ k, ⟪b k, b' j⟫_ℝ • ∑ l, ⟪b l, b' j⟫_ℝ • B (b k) (b l) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        congr 1
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro l _
        exact LinearMap.map_smul (B (b k)) _ _
    _ = ∑ k, ∑ l, ⟪b k, b' j⟫_ℝ • ⟪b l, b' j⟫_ℝ • B (b k) (b l) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.smul_sum]
    _ = ∑ k, ∑ l, (⟪b k, b' j⟫_ℝ * ⟪b l, b' j⟫_ℝ) • B (b k) (b l) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [smul_smul]

/-- After exchanging sums, $\sum_j \langle b_k, b'_j\rangle\langle b_l, b'_j\rangle$
collapses to $\langle b_k, b_l\rangle$ by Parseval. -/
private lemma sum_inner_mul_inner_other_basis
    (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis ι' ℝ V)
    (k l : ι) :
    ∑ j, ⟪b k, b' j⟫_ℝ * ⟪b l, b' j⟫_ℝ = ⟪b k, b l⟫_ℝ := by
  -- Real-inner symmetry: ⟪b l, b' j⟫ = ⟪b' j, b l⟫.
  have hsymm : ∀ j, ⟪b l, b' j⟫_ℝ = ⟪b' j, b l⟫_ℝ := fun j => real_inner_comm _ _
  simp only [hsymm]
  exact b'.sum_inner_mul_inner (b k) (b l)

/-- **Basis invariance of the diagonal of a bilinear map over
orthonormal bases.** For two orthonormal bases $b, b'$ of a real
inner product space $V$ and any bilinear map
$B : V \to_\ell V \to_\ell W$,
$$\sum_i B(b_i, b_i) = \sum_i B(b'_i, b'_i).$$ -/
theorem sum_apply_diagonal_invariant
    (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis ι' ℝ V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) :
    ∑ i, B (b i) (b i) = ∑ i, B (b' i) (b' i) := by
  classical
  symm
  calc ∑ j, B (b' j) (b' j)
      = ∑ j, ∑ k, ∑ l, (⟪b k, b' j⟫_ℝ * ⟪b l, b' j⟫_ℝ) • B (b k) (b l) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        exact expand_diagonal_via_other_basis b b' B j
    _ = ∑ k, ∑ l, (∑ j, ⟪b k, b' j⟫_ℝ * ⟪b l, b' j⟫_ℝ) • B (b k) (b l) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [← Finset.sum_smul]
    _ = ∑ k, ∑ l, ⟪b k, b l⟫_ℝ • B (b k) (b l) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [sum_inner_mul_inner_other_basis b b' k l]
    _ = ∑ k, B (b k) (b k) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.sum_eq_single k]
        · -- l = k case: ⟪b k, b k⟫ • B (b k) (b k) = B (b k) (b k).
          have h1 : ⟪b k, b k⟫_ℝ = 1 := by
            have hnorm : ‖b k‖ = 1 := b.orthonormal.1 k
            rw [@real_inner_self_eq_norm_mul_norm, hnorm]; ring
          rw [h1, one_smul]
        · -- l ≠ k case: ⟪b k, b l⟫ = 0 by orthonormality, so smul kills.
          intro l _ hl_ne_k
          have h0 : ⟪b k, b l⟫_ℝ = 0 := b.orthonormal.inner_eq_zero hl_ne_k.symm
          rw [h0, zero_smul]
        · -- k ∈ Finset.univ trivially.
          intro h; exact absurd (Finset.mem_univ k) h

end OrthonormalBasis
