import OpenGALib.Riemannian.Manifold.DoCarmoCh4Sectional
import OpenGALib.Riemannian.Manifold.DoCarmoCh4Ricci

/-!
# Petersen Ch. 4, §4.1 — Computational Simplifications

The three pointwise algebraic lemmas Petersen isolates before computing
curvature on examples. All three live on a single tangent space `T_pM`,
modelled as a real inner product space `V`, with the curvature tensor at `p`
represented by an algebraic curvature form `B : V⁴ → ℝ` (the vendored
`IsAlgCurvatureForm` layer: multilinear with the two antisymmetries and the
first Bianchi identity, from which the pair symmetry `B x y z t = B z t x y`
follows).

* `diagonalCurvatureOperatorFromTripleVanishing` (Prop 4.1.2): if
  `R(e_i,e_j)e_k = 0` for mutually distinct `i,j,k`, the wedges `e_i ∧ e_j`
  diagonalize the curvature operator — in components, `B(e_i,e_j,e_k,e_l)`
  has the Kronecker form `λ_{ij}(δ_{ik}δ_{jl} − δ_{il}δ_{jk})` with
  `λ_{ij} = B(e_i,e_j,e_i,e_j)`.
* `secBoundsFromDiagonalCurvatureOperator` (Prop 4.1.1): if the wedges of an
  orthonormal basis diagonalize the curvature operator with eigenvalues
  `λ_{ij}`, every sectional curvature lies between the smallest and largest
  `λ_{ij}` — stated for arbitrary enclosing bounds `lo ≤ λ_{ij} ≤ hi`, so it
  applies directly to the pinching statements of §4.2–§4.5.
* `ricciDiagonalFromTripleVanishing` (Prop 4.1.3): if
  `⟨R(e_i,e_j)e_k, e_i⟩ = 0` whenever `i,j,k` are mutually distinct, the basis
  `e_i` diagonalizes the Ricci tensor (the trace form `ricciForm`).

Petersen's convention `g(𝔊(e_i∧e_j), e_k∧e_l) = −g(R(e_i,e_j)e_k, e_l)` only
permutes/negates the slots of `B`; all statements here are invariant under
that relabelling, so the propositions apply verbatim to either convention.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §4.1, pp. 133–134.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace PetersenLib

open Riemannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## Prop 4.1.2 — pairwise vanishing diagonalizes the curvature operator -/

/-- **Math.** Petersen **Prop 4.1.2**: if `R(e_i,e_j)e_k = 0` whenever `i,j,k`
are mutually distinct (hypothesis `htriple`, stated as vanishing of the form
`B(e_i,e_j,e_k,·)`), then the wedges `e_i ∧ e_j` diagonalize the curvature
operator: in components,
`B(e_i,e_j,e_k,e_l) = B(e_i,e_j,e_i,e_j) · (δ_{ik}δ_{jl} − δ_{il}δ_{jk})`,
which for an orthonormal basis says exactly
`𝔊(e_i∧e_j) = λ_{ij} e_i∧e_j` with `λ_{ij} = B(e_i,e_j,e_i,e_j)`. The proof
is pure symmetry algebra (no orthonormality is needed for the component
identity): if `{k,l} ⊄ {i,j}` then either `i,j,k` or `i,j,l` are mutually
distinct and the entry vanishes by `htriple` and the antisymmetries; the
remaining entries are `±λ_{ij}`. -/
theorem diagonalCurvatureOperatorFromTripleVanishing
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    {ι : Type*} [DecidableEq ι] (e : ι → V)
    (htriple : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ t, B (e i) (e j) (e k) t = 0)
    (i j k l : ι) :
    B (e i) (e j) (e k) (e l) =
      B (e i) (e j) (e i) (e j) *
        ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
          - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)) := by
  by_cases hij : i = j
  · subst hij
    rw [hB.self_left]
    ring
  by_cases hkl : k = l
  · subst hkl
    rw [hB.self_right]
    ring
  by_cases hik : i = k
  · subst hik
    by_cases hjl : j = l
    · subst hjl
      simp [hij, Ne.symm hij]
    · -- here `l ∉ {i,j}`, so the triple `i,j,l` is mutually distinct
      have hil : i ≠ l := hkl
      rw [hB.antisymm₃₄, htriple i j l hij hjl hil (e i)]
      simp [hjl, hil]
  by_cases hjk : j = k
  · subst hjk
    by_cases hil : i = l
    · subst hil
      rw [hB.antisymm₃₄]
      simp [hij, Ne.symm hij]
    · -- here `l ∉ {i,j}`, so the triple `i,j,l` is mutually distinct
      have hjl : j ≠ l := hkl
      rw [hB.antisymm₃₄, htriple i j l hij hjl hil (e j)]
      simp [hik, hil]
  · -- here `k ∉ {i,j}`, so the triple `i,j,k` is mutually distinct
    rw [htriple i j k hij hjk hik (e l)]
    simp [hik, hjk]

/-! ## Prop 4.1.1 — sectional curvature bounds from a diagonalized operator -/

/-- The eigenvalues read off from a Kronecker diagonalization are symmetric off
the diagonal: `λ_{ij} = B(e_i,e_j,e_i,e_j) = B(e_j,e_i,e_j,e_i) = λ_{ji}`. -/
theorem diag_eigenvalue_symm {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    {ι : Type*} [DecidableEq ι] {e : ι → V} {lam : ι → ι → ℝ}
    (hdiag : ∀ i j k l, B (e i) (e j) (e k) (e l) =
      lam i j * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    {i j : ι} (hij : i ≠ j) : lam i j = lam j i := by
  have h3 : B (e i) (e j) (e i) (e j) = B (e j) (e i) (e j) (e i) := by
    rw [hB.antisymm₁₂ (e i) (e j), hB.antisymm₃₄ (e j) (e i)]
    ring
  rw [hdiag i j i j, hdiag j i j i] at h3
  simpa [hij, Ne.symm hij] using h3

/-- **Math.** Petersen **Prop 4.1.1**, working form: if the wedges of an
orthonormal basis diagonalize the curvature operator with eigenvalues
`λ_{ij}` (hypothesis `hdiag`), and `lo ≤ λ_{ij} ≤ hi` for all `i ≠ j`, then
for every orthonormal pair `v, w` the sectional numerator satisfies
`lo ≤ B(v,w,v,w) ≤ hi`. Expanding `v, w` in the basis,
`B(v,w,v,w) = ½ ∑_{ij} λ_{ij} α_{ij}²` with `α_{ij} = v_i w_j − v_j w_i`, and
`∑_{ij} α_{ij}² = 2(|v|²|w|² − ⟨v,w⟩²) = 2` (Lagrange's identity), so the
value is a convex combination of the eigenvalues `λ_{ij}`, `i ≠ j`. -/
theorem secNumerator_bounds_of_diagonal {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ V) {lam : ι → ι → ℝ}
    (hdiag : ∀ i j k l, B (e i) (e j) (e k) (e l) =
      lam i j * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    {lo hi : ℝ} (hlo : ∀ i j, i ≠ j → lo ≤ lam i j)
    (hhi : ∀ i j, i ≠ j → lam i j ≤ hi)
    {v w : V} (hv : ⟪v, v⟫ = 1) (hw : ⟪w, w⟫ = 1) (hvw : ⟪v, w⟫ = 0) :
    B v w v w ∈ Set.Icc lo hi := by
  classical
  have hv' : (∑ i, ⟪e i, v⟫ • e i) = v := e.sum_repr' v
  have hw' : (∑ i, ⟪e i, w⟫ • e i) = w := e.sum_repr' w
  -- Stage 1: collapse the last two slots against the diagonalization.
  have hcollapse : ∀ i j, B (e i) (e j) v w =
      lam i j * (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫) := by
    intro i j
    conv_lhs => rw [← hv', ← hw']
    rw [hB.sum_three]
    have hinner : ∀ k, B (e i) (e j) (e k) (∑ l, ⟪e l, w⟫ • e l) =
        lam i j * ((if i = k then (1 : ℝ) else 0) * ⟪e j, w⟫
          - (if j = k then (1 : ℝ) else 0) * ⟪e i, w⟫) := by
      intro k
      rw [hB.sum_four]
      have hterm : ∀ l, ⟪e l, w⟫ * B (e i) (e j) (e k) (e l) =
          (if j = l then (if i = k then (1 : ℝ) else 0) * (lam i j * ⟪e l, w⟫) else 0)
            - (if i = l then (if j = k then (1 : ℝ) else 0) * (lam i j * ⟪e l, w⟫)
                else 0) := by
        intro l
        rw [hdiag i j k l]
        by_cases hjl : j = l <;> by_cases hil : i = l <;> simp [hjl, hil] <;> ring
      simp only [hterm]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq Finset.univ j,
        Finset.sum_ite_eq Finset.univ i]
      simp only [Finset.mem_univ, if_true]
      ring
    simp only [hinner]
    have hterm2 : ∀ k, ⟪e k, v⟫ * (lam i j * ((if i = k then (1 : ℝ) else 0) * ⟪e j, w⟫
        - (if j = k then (1 : ℝ) else 0) * ⟪e i, w⟫)) =
        (if i = k then lam i j * (⟪e k, v⟫ * ⟪e j, w⟫) else 0)
          - (if j = k then lam i j * (⟪e k, v⟫ * ⟪e i, w⟫) else 0) := by
      intro k
      by_cases hik : i = k <;> by_cases hjk : j = k <;> simp [hik, hjk] <;> ring
    simp only [hterm2]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq Finset.univ i,
      Finset.sum_ite_eq Finset.univ j]
    simp only [Finset.mem_univ, if_true]
    ring
  -- Stage 2: expand the first two slots.
  have hexpand : B v w v w = ∑ i, ∑ j, ⟪e i, v⟫ * ⟪e j, w⟫ *
      (lam i j * (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫)) := by
    conv_lhs => rw [← hv', ← hw']
    rw [hB.sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB.sum_two, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hv', hw', hcollapse i j]
    ring
  -- Symmetrize: 2·B(v,w,v,w) = ∑_{ij} λ_{ij} α_{ij}².
  have hsymm : 2 * B v w v w = ∑ i, ∑ j, lam i j *
      (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫) ^ 2 := by
    have hswap : B v w v w = ∑ i, ∑ j, ⟪e j, v⟫ * ⟪e i, w⟫ *
        (lam j i * (⟪e j, v⟫ * ⟪e i, w⟫ - ⟪e i, v⟫ * ⟪e j, w⟫)) := by
      rw [hexpand, Finset.sum_comm]
    calc 2 * B v w v w
        = (∑ i, ∑ j, ⟪e i, v⟫ * ⟪e j, w⟫ *
            (lam i j * (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫)))
          + ∑ i, ∑ j, ⟪e j, v⟫ * ⟪e i, w⟫ *
            (lam j i * (⟪e j, v⟫ * ⟪e i, w⟫ - ⟪e i, v⟫ * ⟪e j, w⟫)) := by
          rw [← hexpand, ← hswap]; ring
      _ = ∑ i, ∑ j, (⟪e i, v⟫ * ⟪e j, w⟫ *
            (lam i j * (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫))
          + ⟪e j, v⟫ * ⟪e i, w⟫ *
            (lam j i * (⟪e j, v⟫ * ⟪e i, w⟫ - ⟪e i, v⟫ * ⟪e j, w⟫))) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => (Finset.sum_add_distrib).symm
      _ = ∑ i, ∑ j, lam i j *
            (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hij : i = j
          · subst hij; ring
          · rw [← diag_eigenvalue_symm hB hdiag hij]
            ring
  -- Parseval: the coefficient sums.
  have hcc : ∑ i, ⟪e i, v⟫ * ⟪e i, v⟫ = 1 := by
    have h := e.sum_inner_mul_inner v v
    rw [hv] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (e i) v]
  have hdd : ∑ i, ⟪e i, w⟫ * ⟪e i, w⟫ = 1 := by
    have h := e.sum_inner_mul_inner w w
    rw [hw] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (e i) w]
  have hcd : ∑ i, ⟪e i, v⟫ * ⟪e i, w⟫ = 0 := by
    have h := e.sum_inner_mul_inner v w
    rw [hvw] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (e i) v]
  -- Lagrange's identity: ∑_{ij} α_{ij}² = 2(|v|²|w|² − ⟨v,w⟩²) = 2.
  have hT : ∑ i, ∑ j,
      (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫) ^ 2 = 2 := by
    calc ∑ i, ∑ j, (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫) ^ 2
        = (∑ i, ∑ j, (⟪e i, v⟫ * ⟪e i, v⟫) * (⟪e j, w⟫ * ⟪e j, w⟫))
          - 2 * ∑ i, ∑ j, (⟪e i, v⟫ * ⟪e i, w⟫) * (⟪e j, v⟫ * ⟪e j, w⟫)
          + ∑ i, ∑ j, (⟪e j, v⟫ * ⟪e j, v⟫) * (⟪e i, w⟫ * ⟪e i, w⟫) := by
          simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by ring
      _ = 1 * 1 - 2 * (0 * 0) + 1 * 1 := by
          rw [Finset.sum_comm (f := fun i j => (⟪e j, v⟫ * ⟪e j, v⟫) *
              (⟪e i, w⟫ * ⟪e i, w⟫)),
            ← Finset.sum_mul_sum, ← Finset.sum_mul_sum,
            hcc, hdd, hcd]
      _ = 2 := by ring
  -- Per-term bounds and assembly.
  have hlower : lo * ∑ i, ∑ j,
      (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫) ^ 2 ≤
      ∑ i, ∑ j, lam i j *
        (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · exact mul_le_mul_of_nonneg_right (hlo i j hij) (sq_nonneg _)
  have hupper : (∑ i, ∑ j, lam i j *
        (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫) ^ 2) ≤
      hi * ∑ i, ∑ j,
        (⟪e i, v⟫ * ⟪e j, w⟫ - ⟪e j, v⟫ * ⟪e i, w⟫) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · exact mul_le_mul_of_nonneg_right (hhi i j hij) (sq_nonneg _)
  rw [hT] at hlower hupper
  constructor
  · linarith [hsymm]
  · linarith [hsymm]

/-- **Math.** Petersen **Prop 4.1.1**: let `e_i` be an orthonormal basis of
`T_pM` whose wedges `e_i ∧ e_j` diagonalize the curvature operator with
eigenvalues `λ_{ij}` (hypothesis `hdiag`, the components of `B` in the
Kronecker form). Then every sectional curvature lies between the eigenvalue
bounds: if `lo ≤ λ_{ij} ≤ hi` for all `i ≠ j`, then for every 2-plane
`π ⊂ T_pM` — represented by an orthonormal pair `v, w` spanning it —
`sec(π) = B(v,w,v,w)/|v∧w|² ∈ [lo, hi]`. In particular
`sec(π) ∈ [min λ_{ij}, max λ_{ij}]`. -/
theorem secBoundsFromDiagonalCurvatureOperator {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ V) {lam : ι → ι → ℝ}
    (hdiag : ∀ i j k l, B (e i) (e j) (e k) (e l) =
      lam i j * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0)))
    {lo hi : ℝ} (hlo : ∀ i j, i ≠ j → lo ≤ lam i j)
    (hhi : ∀ i j, i ≠ j → lam i j ≤ hi)
    {v w : V} (hv : ⟪v, v⟫ = 1) (hw : ⟪w, w⟫ = 1) (hvw : ⟪v, w⟫ = 0) :
    sectionalCurvature B v w ∈ Set.Icc lo hi := by
  have hwedge : wedgeSq v w = 1 := by
    unfold wedgeSq
    rw [hv, hw, hvw]
    ring
  have hnum := secNumerator_bounds_of_diagonal hB e hdiag hlo hhi hv hw hvw
  unfold sectionalCurvature
  rw [hwedge, div_one]
  exact hnum

/-! ## Prop 4.1.3 — a criterion for diagonalizing the Ricci tensor -/

/-- **Math.** Petersen **Prop 4.1.3**: let `e_i` be an orthonormal basis of
`T_pM`. If `⟨R(e_i,e_j)e_k, e_i⟩ = 0` whenever three of the indices
`i,j,k,i` are mutually distinct — i.e. whenever `i,j,k` are mutually
distinct (hypothesis `htriple`, the pattern `B(e_a,e_b,e_c,e_a) = 0`) — then
the `e_i` diagonalize the Ricci tensor: `Ric(e_i,e_j) = 0` for `i ≠ j`,
where `Ric` is the trace form `ricciForm`. In the trace
`Ric(e_i,e_j) = ∑_k B(e_i,e_k,e_j,e_k)`, the terms with `k ∉ {i,j}` vanish
by `htriple` (after moving `e_k` to the first slot by antisymmetry) and the
terms `k = i`, `k = j` vanish by the repeated-pair antisymmetries. -/
theorem ricciDiagonalFromTripleVanishing [FiniteDimensional ℝ V]
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V)
    (htriple : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      B (e i) (e j) (e k) (e i) = 0)
    {i j : ι} (hij : i ≠ j) :
    ricciForm hB (e i) (e j) = 0 := by
  rw [ricciForm_eq_sum hB _ _ e]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hki : k = i
  · subst hki
    exact hB.self_left _ _ _
  by_cases hkj : k = j
  · subst hkj
    exact hB.self_right _ _ _
  · rw [hB.antisymm₁₂, htriple k i j hki hij hkj, neg_zero]

end PetersenLib
