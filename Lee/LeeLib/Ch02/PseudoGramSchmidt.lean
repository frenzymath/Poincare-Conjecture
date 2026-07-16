/-
Chapter 2, "Riemannian Metrics", §6 "Scalar Products": the Gram-Schmidt algorithm for
an indefinite symmetric bilinear form, *as an explicit formula*.

`LeeLib.Ch02.ScalarProduct` already proves Lee's Proposition 2.63 — a nondegenerate
tuple in a scalar product space can be replaced by an orthonormal tuple spanning the
same flag.  But it proves it as an **existence statement**, by an induction whose
inductive step begins `obtain ⟨b, hbon, hbspan⟩ := ih`.  The output is therefore an
opaque witness of a `Prop`-level `∃`: nothing about it is definitionally a formula,
and no statement about it can be proved beyond the two it is packaged with.

That is fatal for Lee's Proposition 2.66 (smooth orthonormal frames on a
pseudo-Riemannian manifold), which needs the Gram-Schmidt output to *depend smoothly
on a parameter* — the base point of a bundle.  Smoothness is a statement about a
function, and there is no function to talk about until the algorithm is a `def`.

So this file re-runs Lee's Proposition 2.63 as a recursion:

  `u_j = v_j - ∑_{i < j} (⟪u_i, v_j⟫ / ⟪u_i, u_i⟫) • u_i`,        (`gramSchmidtBilin`)
  `b_j = (√|⟪u_j, u_j⟫|)⁻¹ • u_j`.                         (`gramSchmidtBilinNormed`)

The shape is mathlib's `gramSchmidt`/`gramSchmidtNormed`, and deliberately so: the
smooth-frame file downstream is then a transcription of `LeeLib.Ch02.OrthonormalFrame`,
which runs the same induction against mathlib's positive-definite version.

Two things genuinely differ from the positive-definite case, and both are the same
point Lee makes:

* **The denominators can vanish.**  In mathlib's `gramSchmidt`, `⟪u_j, u_j⟫ > 0` for
  free from `u_j ≠ 0`, so the recursion is unconditionally well-behaved.  Here a
  nonzero `u_j` can be *null*, and then the recursion divides by zero and the output
  is junk.  Everything below is therefore conditional on `IsNondegenerateTuple B v`,
  Lee's hypothesis, and the work is `gramSchmidtBilin_apply_self_ne_zero`: nondegeneracy
  of `span (v_1, …, v_j)` is what rules the null case out.
* **Normalization is by `√|⟪u_j, u_j⟫|`, not `√⟪u_j, u_j⟫`**, so `⟪b_j, b_j⟫ = ±1`
  rather than `= 1` — Lee's `IsOrthonormal`, already defined in `ScalarProduct`.

`gramSchmidtBilin_isOrthonormal` and `prefixSpan_gramSchmidtBilinNormed` reprove
Lee's Proposition 2.63 about the explicit formula, so `ScalarProduct`'s existence
statements are recovered as immediate corollaries
(`exists_isOrthonormal_prefixSpan_eq_of_gramSchmidt`) — the two developments agree.
-/
import LeeLib.Ch02.ScalarProduct

namespace LeeLib.Ch02

open Module Submodule
open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} {B : BilinForm ℝ V}

/-- **The unnormalized Gram-Schmidt recursion against a bilinear form** (Lee, proof of
Proposition 2.63): subtract from `v_j` its `B`-projections onto the previously
constructed vectors.

This is a total function: like mathlib's `gramSchmidt`, and like the `c i = ⟪v_j, b_i⟫
/ ⟪b_i, b_i⟫` of `ScalarProduct`'s existence proof, it uses Lean's total division, so
no nonvanishing hypothesis is needed to *state* it.  The hypotheses appear only in the
theorems, where they must: if some `⟪u_i, u_i⟫` vanishes the formula still evaluates,
but the output is meaningless. -/
noncomputable def gramSchmidtBilin (B : BilinForm ℝ V) (v : Fin n → V) (j : Fin n) : V :=
  v j - ∑ i : Finset.Iio j,
    (B (gramSchmidtBilin B v i) (v j) / B (gramSchmidtBilin B v i) (gramSchmidtBilin B v i)) •
      gramSchmidtBilin B v i
  termination_by j
  decreasing_by exact Fin.lt_def.mp (Finset.mem_Iio.mp i.2)

/-- The defining recursion, with `∑ i ∈ Iio j` rather than the subtype sum the
well-founded definition needs — the form every proof below rewrites with.  This
mirrors mathlib's `gramSchmidt_def`. -/
theorem gramSchmidtBilin_def (B : BilinForm ℝ V) (v : Fin n → V) (j : Fin n) :
    gramSchmidtBilin B v j = v j - ∑ i ∈ Finset.Iio j,
      (B (gramSchmidtBilin B v i) (v j) / B (gramSchmidtBilin B v i) (gramSchmidtBilin B v i)) •
        gramSchmidtBilin B v i := by
  rw [← Finset.sum_attach (Finset.Iio j), Finset.attach_eq_univ, gramSchmidtBilin]

/-- **The Gram-Schmidt normalization** (Lee, Proposition 2.63): rescale each `u_j` to
have `⟪b_j, b_j⟫ = ±1`.

The absolute value is the whole difference from the positive-definite case: `⟪u_j,u_j⟫`
may be negative, so `√⟪u_j,u_j⟫` would be junk, and the sign that survives normalization
is exactly the `±1` recorded by `IsOrthonormal`. -/
noncomputable def gramSchmidtBilinNormed (B : BilinForm ℝ V) (v : Fin n → V) (j : Fin n) : V :=
  (Real.sqrt |B (gramSchmidtBilin B v j) (gramSchmidtBilin B v j)|)⁻¹ • gramSchmidtBilin B v j

/-! ### The flag, orthogonality, and the nonvanishing of the denominators

These three are proved by a single induction, because they are mutually dependent:
orthogonality of `u_j` against its predecessors needs their denominators to be nonzero,
the denominator `⟪u_j,u_j⟫ ≠ 0` needs `span (u_1,…,u_j) = span (v_1,…,v_j)`, and that
span identity needs `u_j ≡ v_j` modulo the earlier span.  Splitting them into separate
theorems would make each one's induction hypothesis unavailable to the others.

The statement is packaged as `GramSchmidtBilinSpec` over an initial segment `k` of the
index set, and `gramSchmidtBilin_spec` proves it for every `k ≤ n`. -/

variable (B) in
/-- The conjunction proved by the Gram-Schmidt induction, over the first `k` indices:
the denominators are nonzero, the vectors are pairwise `B`-orthogonal, and the flag is
reproduced.  See the section comment for why the three cannot be separated. -/
structure GramSchmidtBilinSpec (v : Fin n → V) (k : ℕ) : Prop where
  /-- The denominators of the recursion do not vanish — the indefinite case's burden. -/
  apply_self_ne_zero : ∀ i : Fin n, (i : ℕ) < k →
    B (gramSchmidtBilin B v i) (gramSchmidtBilin B v i) ≠ 0
  /-- The constructed vectors are pairwise `B`-orthogonal. -/
  ortho : ∀ i j : Fin n, (i : ℕ) < k → (j : ℕ) < k → i ≠ j →
    B (gramSchmidtBilin B v i) (gramSchmidtBilin B v j) = 0
  /-- Lee's flag condition: `span (u_1, …, u_j) = span (v_1, …, v_j)` for every `j ≤ k`. -/
  prefixSpan_eq : ∀ j ≤ k, prefixSpan (gramSchmidtBilin B v) j = prefixSpan v j

/-- `u_j` is `B`-orthogonal to each earlier `u_k`.

This is the computation at the heart of Gram-Schmidt: expanding the recursion, the sum
`∑_{i<j} (⟪u_i,v_j⟫/⟪u_i,u_i⟫) ⟪u_k,u_i⟫` collapses to its `i = k` term by orthogonality
of the earlier vectors, and that term is exactly `⟪u_k, v_j⟫` by the choice of
coefficient — so the two cancel. -/
theorem gramSchmidtBilin_apply_of_lt {v : Fin n → V} {k : ℕ}
    (hden : ∀ i : Fin n, (i : ℕ) < k → B (gramSchmidtBilin B v i) (gramSchmidtBilin B v i) ≠ 0)
    (hortho : ∀ i j : Fin n, (i : ℕ) < k → (j : ℕ) < k → i ≠ j →
      B (gramSchmidtBilin B v i) (gramSchmidtBilin B v j) = 0)
    {j : Fin n} (hjk : (j : ℕ) = k) {c : Fin n} (hc : c < j) :
    B (gramSchmidtBilin B v c) (gramSchmidtBilin B v j) = 0 := by
  have hck : (c : ℕ) < k := hjk ▸ Fin.lt_def.mp hc
  rw [gramSchmidtBilin_def B v j]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single c]
  · rw [div_mul_cancel₀ _ (hden c hck), sub_self]
  · intro i hi hic
    have hik : (i : ℕ) < k := hjk ▸ Fin.lt_def.mp (Finset.mem_Iio.mp hi)
    rw [hortho c i hck hik (Ne.symm hic), mul_zero]
  · intro h
    exact absurd (Finset.mem_Iio.2 hc) h

/-- The main induction.  See the section comment. -/
theorem gramSchmidtBilin_spec (hB : B.IsSymm) {v : Fin n → V} (hv : IsNondegenerateTuple B v) :
    ∀ k ≤ n, GramSchmidtBilinSpec B v k := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i j hi => absurd hi (Nat.not_lt_zero _),
      fun j hj => by rw [Nat.le_zero.mp hj, prefixSpan_zero, prefixSpan_zero]⟩
  | succ k ih =>
    intro hk
    obtain ⟨hden, hortho, hspan⟩ := ih (by omega)
    have hkn : k < n := by omega
    set j : Fin n := ⟨k, hkn⟩ with hj
    set u := gramSchmidtBilin B v with hu
    have hjval : (j : ℕ) = k := by rw [hj]
    have hSb : prefixSpan u k = prefixSpan v k := hspan k le_rfl
    -- `u_j` is orthogonal to every earlier `u_c`, hence to `span (u_1, …, u_k)`.
    have hzb : ∀ c : Fin n, c < j → B (u c) (u j) = 0 := fun c hc =>
      gramSchmidtBilin_apply_of_lt hden hortho hjval hc
    have hzS : ∀ w ∈ prefixSpan v k, B (u j) w = 0 := by
      intro w hw
      rw [← hSb, prefixSpan] at hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        exact hB.isRefl _ _ (hzb i (Fin.lt_def.mpr (by rw [hjval]; exact hi)))
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [map_smul, hx, smul_zero]
    -- `u_j ≡ v_j` modulo `span (u_1, …, u_k) = span (v_1, …, v_k)`.
    have hsum : (∑ i ∈ Finset.Iio j,
        (B (u i) (v j) / B (u i) (u i)) • u i) ∈ prefixSpan v k := by
      rw [← hSb]
      refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨i, by simpa [hj, Fin.lt_def] using Finset.mem_Iio.1 hi, rfl⟩
    have hujv : u j = v j - ∑ i ∈ Finset.Iio j, (B (u i) (v j) / B (u i) (u i)) • u i :=
      gramSchmidtBilin_def B v j
    -- `v_j` is new: otherwise the flag would not grow in dimension.
    have hvkS : v j ∉ prefixSpan v k := by
      intro hmem
      have hcollapse : prefixSpan v (k + 1) = prefixSpan v k := by
        rw [prefixSpan_succ v hkn, sup_eq_left, Submodule.span_singleton_le_iff_mem]
        exact hmem
      have h1 := (hv (k + 1) hk).1
      rw [hcollapse, (hv k (by omega)).1] at h1
      omega
    have hzne : u j ≠ 0 := by
      intro h0
      rw [h0, eq_comm, sub_eq_zero] at hujv
      exact hvkS (hujv ▸ hsum)
    have hTz : prefixSpan v (k + 1) = prefixSpan v k ⊔ Submodule.span ℝ {u j} := by
      rw [prefixSpan_succ v hkn]
      refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
      · rw [Submodule.span_singleton_le_iff_mem,
          show v j = u j + ∑ i ∈ Finset.Iio j, (B (u i) (v j) / B (u i) (u i)) • u i by
            rw [hujv]; abel]
        exact Submodule.add_mem _
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
          (Submodule.mem_sup_left hsum)
      · rw [Submodule.span_singleton_le_iff_mem, hujv]
        exact Submodule.sub_mem _
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
          (Submodule.mem_sup_left hsum)
    have hzmem : u j ∈ prefixSpan v (k + 1) := by
      rw [hTz]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    -- **The indefinite step**: a null `u_j` would be orthogonal to the whole
    -- nondegenerate `span (v_1, …, v_{k+1})`, forcing `u_j = 0`.
    have hzz : B (u j) (u j) ≠ 0 := by
      intro h0
      have hzT : ∀ w ∈ prefixSpan v (k + 1), B (u j) w = 0 := by
        intro w hw
        rw [hTz] at hw
        obtain ⟨s, hs, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
        simp [hzS s hs, h0]
      exact hzne (congrArg Subtype.val
        ((hv (k + 1) hk).2.1 ⟨u j, hzmem⟩ fun w => by simpa using hzT (w : V) w.2))
    -- Assemble the three conclusions at stage `k + 1`.
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_or_ge (i : ℕ) k with h | h
      · exact hden i h
      · obtain rfl : i = j := Fin.ext (by omega)
        exact hzz
    · intro a b ha hb hab
      rcases Nat.lt_or_ge (a : ℕ) k with hak | hak
      · rcases Nat.lt_or_ge (b : ℕ) k with hbk | hbk
        · exact hortho a b hak hbk hab
        · obtain rfl : b = j := Fin.ext (by omega)
          exact hzb a (Fin.lt_def.mpr (by omega))
      · obtain rfl : a = j := Fin.ext (by omega)
        rcases Nat.lt_or_ge (b : ℕ) k with hbk | hbk
        · exact hB.isRefl _ _ (hzb b (Fin.lt_def.mpr (by omega)))
        · exact absurd (Fin.ext (show (j : ℕ) = (b : ℕ) by omega)) hab
    · intro m hm
      rcases Nat.lt_or_ge m (k + 1) with hmk | hmk
      · exact hspan m (by omega)
      · obtain rfl : m = k + 1 := by omega
        rw [prefixSpan_succ u hkn, hSb, hTz]

/-- **The denominators of the Gram-Schmidt recursion never vanish** on a nondegenerate
tuple — Lee's "if `⟪z,z⟫ = 0` then `z` is orthogonal to `span (v_1, …, v_{k+1})`,
contradicting the nondegeneracy assumption".

This is the one statement with no positive-definite counterpart, and the reason
`IsNondegenerateTuple` is the right hypothesis for an indefinite Gram-Schmidt: for a
*positive definite* form `⟪u_j, u_j⟫ ≠ 0` follows from `u_j ≠ 0` alone. -/
theorem gramSchmidtBilin_apply_self_ne_zero (hB : B.IsSymm) {v : Fin n → V}
    (hv : IsNondegenerateTuple B v) (j : Fin n) :
    B (gramSchmidtBilin B v j) (gramSchmidtBilin B v j) ≠ 0 :=
  (gramSchmidtBilin_spec hB hv n le_rfl).apply_self_ne_zero j j.isLt

/-- The unnormalized Gram-Schmidt vectors are pairwise `B`-orthogonal. -/
theorem gramSchmidtBilin_apply_ne (hB : B.IsSymm) {v : Fin n → V}
    (hv : IsNondegenerateTuple B v) {i j : Fin n} (hij : i ≠ j) :
    B (gramSchmidtBilin B v i) (gramSchmidtBilin B v j) = 0 :=
  (gramSchmidtBilin_spec hB hv n le_rfl).ortho i j i.isLt j.isLt hij

/-- The unnormalized Gram-Schmidt vectors reproduce Lee's flag. -/
theorem prefixSpan_gramSchmidtBilin (hB : B.IsSymm) {v : Fin n → V}
    (hv : IsNondegenerateTuple B v) (j : ℕ) (hj : j ≤ n) :
    prefixSpan (gramSchmidtBilin B v) j = prefixSpan v j :=
  (gramSchmidtBilin_spec hB hv n le_rfl).prefixSpan_eq j hj

/-! ### The normalized family -/

/-- The normalizing scalar is nonzero, so normalization does not collapse the flag. -/
theorem gramSchmidtBilin_normalizer_ne_zero (hB : B.IsSymm) {v : Fin n → V}
    (hv : IsNondegenerateTuple B v) (j : Fin n) :
    (Real.sqrt |B (gramSchmidtBilin B v j) (gramSchmidtBilin B v j)|)⁻¹ ≠ 0 := by
  have hpos : (0 : ℝ) < |B (gramSchmidtBilin B v j) (gramSchmidtBilin B v j)| :=
    abs_pos.mpr (gramSchmidtBilin_apply_self_ne_zero hB hv j)
  simp only [ne_eq, inv_eq_zero]
  positivity

/-- **The Gram-Schmidt output is orthonormal** (Lee, Proposition 2.63), for the explicit
formula rather than for an existential witness. -/
theorem gramSchmidtBilin_isOrthonormal (hB : B.IsSymm) {v : Fin n → V}
    (hv : IsNondegenerateTuple B v) : IsOrthonormal B (gramSchmidtBilinNormed B v) := by
  constructor
  · intro i j hij
    simp only [gramSchmidtBilinNormed, map_smul, LinearMap.smul_apply, smul_eq_mul,
      gramSchmidtBilin_apply_ne hB hv hij, mul_zero]
  · intro i
    exact apply_self_normalize (gramSchmidtBilin_apply_self_ne_zero hB hv i)

/-- **The Gram-Schmidt output reproduces Lee's flag** (Lee, Proposition 2.63): the
normalized family spans the same initial subspaces as the input, because rescaling by a
nonzero scalar does not change a span. -/
theorem prefixSpan_gramSchmidtBilinNormed (hB : B.IsSymm) {v : Fin n → V}
    (hv : IsNondegenerateTuple B v) (j : ℕ) (hj : j ≤ n) :
    prefixSpan (gramSchmidtBilinNormed B v) j = prefixSpan v j := by
  rw [← prefixSpan_gramSchmidtBilin hB hv j hj]
  unfold prefixSpan
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rintro _ ⟨i, hi, rfl⟩
    have : gramSchmidtBilin B v i =
        (Real.sqrt |B (gramSchmidtBilin B v i) (gramSchmidtBilin B v i)|) •
          gramSchmidtBilinNormed B v i := by
      rw [gramSchmidtBilinNormed, smul_smul,
        mul_inv_cancel₀ (by
          have := gramSchmidtBilin_normalizer_ne_zero hB hv i
          simpa using inv_ne_zero this), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

/-- **Lee's Proposition 2.63, recovered from the explicit algorithm.**  This is
`ScalarProduct.exists_isOrthonormal_prefixSpan_eq` with the witness exhibited rather
than obtained from an induction, confirming that the recursion in this file computes
what that existence proof asserts. -/
theorem exists_isOrthonormal_prefixSpan_eq_of_gramSchmidt (hB : B.IsSymm) {v : Fin n → V}
    (hv : IsNondegenerateTuple B v) :
    ∃ b : Fin n → V, IsOrthonormal B b ∧ ∀ j ≤ n, prefixSpan b j = prefixSpan v j :=
  ⟨gramSchmidtBilinNormed B v, gramSchmidtBilin_isOrthonormal hB hv,
    prefixSpan_gramSchmidtBilinNormed hB hv⟩

end LeeLib.Ch02
