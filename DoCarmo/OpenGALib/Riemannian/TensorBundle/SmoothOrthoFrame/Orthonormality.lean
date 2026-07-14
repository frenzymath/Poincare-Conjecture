import OpenGALib.Riemannian.Metric.RiemannianMetric
import OpenGALib.Riemannian.TensorBundle.SmoothOrthoFrame.ChartBasis

/-!
# Orthonormality of the chart-frame Gram-Schmidt

Engineering proof chain for `chartFrameNormFiber_orthonormal` and
`chartFrameNorm_orthonormal`: the inductive $g$-Gram-Schmidt step
preserves orthogonality and unit length on the trivialization base
set.

The proof is by strong induction on the index $i.\mathrm{val}$; the
bundled IH carries three facts at every $i$: $\mathrm{raw}_i \ne 0$,
$\langle e_j, e_i\rangle = 0$ for $j < i$, and $\langle e_i, e_i\rangle
= 1$. Non-degeneracy of $\mathrm{raw}_i$ uses linear independence of
the chart-basis family (`chartBasisFamily_linearIndependent`) and the
inductive span identity
$e_0, \ldots, e_{i-1} \in \mathrm{span}(v_0, \ldots, v_{i-1})$.

Construction prerequisites live in
`Tensor/SmoothOrthoFrame/ChartBasis.lean`; the public bumped-section
API and `OrthonormalBasis` packaging live in the anchor
`Tensor/SmoothOrthoFrame.lean`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set FiberBundle Filter
open scoped Manifold Topology ContDiff Bundle

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Stage 3a: orthonormality of the un-bumped Gram-Schmidt frame

The inductive Gram-Schmidt step preserves orthogonality and unit length
on the trivialization base set. The proof is by strong induction on the
index $i.\mathrm{val}$; the bundled IH carries three facts at every
$i$: $\mathrm{raw}_i \ne 0$, $\langle e_j, e_i\rangle = 0$ for $j < i$,
and $\langle e_i, e_i\rangle = 1$.

The non-degeneracy step $\mathrm{raw}_i \ne 0$ uses linear independence
of the chart-basis family (`chartBasisFamily_linearIndependent`) and
the inductive span identity
$e_0, \ldots, e_{i-1} \in \mathrm{span}(v_0, \ldots, v_{i-1})$. -/

/-- **Eng.** Bilinear distribution of `g.inner b u (·)` over a finite sum. -/
private lemma g_inner_sum_right
    (g : RiemannianMetric I M) (b : M) (v : TangentSpace I b)
    {ι : Type*} (s : Finset ι) (w : ι → TangentSpace I b)
    (c : ι → ℝ) :
    g.inner b v (∑ k ∈ s, c k • w k) = ∑ k ∈ s, c k * g.inner b v (w k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [show ((g.inner b) v) (c a • w a + ∑ x ∈ s, c x • w x) =
        ((g.inner b) v) (c a • w a) + ((g.inner b) v) (∑ x ∈ s, c x • w x) from by
      rw [map_add]]
    rw [show ((g.inner b) v) (c a • w a) = c a * ((g.inner b) v) (w a) from by
      rw [map_smul]; rfl]
    rw [ih]

/-- **Eng.** Bilinear distribution of `g.inner b (·) w` over a finite sum. -/
private lemma g_inner_sum_left
    (g : RiemannianMetric I M) (b : M)
    {ι : Type*} (s : Finset ι) (v : ι → TangentSpace I b)
    (c : ι → ℝ) (w : TangentSpace I b) :
    g.inner b (∑ k ∈ s, c k • v k) w = ∑ k ∈ s, c k * g.inner b (v k) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [show ((g.inner b) (c a • v a + ∑ x ∈ s, c x • v x)) =
        ((g.inner b) (c a • v a)) + ((g.inner b) (∑ x ∈ s, c x • v x)) from by
      rw [map_add]]
    rw [ContinuousLinearMap.add_apply]
    rw [show ((g.inner b) (c a • v a)) w = c a * ((g.inner b) (v a)) w from by
      rw [map_smul]; rfl]
    rw [ih]

/-- **Eng.** Generic normalisation: scaling a positive-norm vector by
$(\sqrt{\langle v, v\rangle})^{-1}$ in the **second** slot equals the
analogous left-slot scaling, factored through the same helper. Used
twice (orthogonality + unit-norm) in the strong-induction succ step,
where `v` is `chartFrameRawFiber g α b i`. -/
private lemma g_inner_smul_right_normalised
    (g : RiemannianMetric I M) (b : M) (v u : TangentSpace I b) (s : ℝ) :
    g.inner b u (s⁻¹ • v) = s⁻¹ * g.inner b u v := by
  rw [map_smul]; rfl

/-- **Math.** **Span identity** (recursion-structural): for every $m$ with
$m.\mathrm{val} < i.\mathrm{val}$, the normalised Gram-Schmidt vector
$e_m(b) = \mathrm{chartFrameNormFiber}\,g\,\alpha\,b\,m$ lies in the
$\mathbb{R}$-span of the chart-basis vectors $v_0(b), \ldots,
v_{i-1}(b)$. Proved by strong induction on $m.\mathrm{val}$ using the
recursive Gram-Schmidt formula `chartFrameNormFiber_eq`; entirely
self-contained (no orthonormality IH required). -/
private lemma chartFrameNormFiber_mem_span_chartBasis
    (g : RiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∀ kk : ℕ, ∀ m : Fin (Module.finrank ℝ E),
      m.val ≤ kk → m.val < i.val →
      chartFrameNormFiber (I := I) g α b m ∈
        Submodule.span ℝ
          ((fun n : Fin i.val =>
            chartBasisVecFiber (I := I) α
              ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
            Set.univ) := by
  intro kk
  induction kk with
  | zero =>
    intro m hm_le hm_lt
    have hm_val : m.val = 0 := Nat.le_zero.mp hm_le
    have hm_eq : m = ⟨0, NeZero.pos _⟩ := Fin.ext hm_val
    subst hm_eq
    rw [chartFrameNormFiber_at_zero]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨0, hm_lt⟩, Set.mem_univ _, rfl⟩
  | succ kk ih_kk =>
    intro m hm_le hm_lt
    by_cases hcase : m.val ≤ kk
    · exact ih_kk m hcase hm_lt
    · rw [chartFrameNormFiber_eq]
      apply Submodule.smul_mem
      unfold chartFrameRawFiber
      apply Submodule.sub_mem
      · apply Submodule.subset_span
        exact ⟨⟨m.val, hm_lt⟩, Set.mem_univ _, rfl⟩
      · apply Submodule.sum_mem
        intro j _
        apply Submodule.smul_mem
        have hj_in_fin : j.val < i.val := lt_trans j.isLt hm_lt
        have hj_le_kk : j.val ≤ kk := by
          have : j.val < m.val := j.isLt
          omega
        have hj_lt_total : j.val < Module.finrank ℝ E :=
          lt_trans hj_in_fin i.isLt
        exact ih_kk ⟨j.val, hj_lt_total⟩ hj_le_kk hj_in_fin

/-- **Math.** **Non-degeneracy of the unnormalised Gram-Schmidt step**: at any
base-set point, $\mathrm{raw}_i \ne 0$.

Argument: if $\mathrm{raw}_i = 0$, then $v_i$ equals its projection
onto $\mathrm{span}(e_0, \ldots, e_{i-1})$. By
`chartFrameNormFiber_mem_span_chartBasis`, this span is contained in
$\mathrm{span}(v_0, \ldots, v_{i-1})$, so
$v_i \in \mathrm{span}(v_0, \ldots, v_{i-1})$ — contradicting linear
independence of the chart-basis family. -/
lemma chartFrameRawFiber_ne_zero
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartFrameRawFiber (I := I) g α b i ≠ 0 := by
  classical
  have hLI : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) α i b) :=
    chartBasisFamily_linearIndependent (I := I) α hb
  intro hraw_zero
  have hv_eq : chartBasisVecFiber (I := I) α i b =
      ∑ j' : Fin i.val,
        (g.inner b (chartBasisVecFiber (I := I) α i b)
          (chartFrameNormFiber (I := I) g α b
            ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
          chartFrameNormFiber (I := I) g α b
            ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := by
    have h_eq : chartBasisVecFiber (I := I) α i b -
        ∑ j' : Fin i.val,
          (g.inner b (chartBasisVecFiber (I := I) α i b)
              (chartFrameNormFiber (I := I) g α b
                ⟨j'.val, lt_trans j'.isLt i.isLt⟩)) •
            chartFrameNormFiber (I := I) g α b
              ⟨j'.val, lt_trans j'.isLt i.isLt⟩ = 0 := by
      simpa [chartFrameRawFiber] using hraw_zero
    exact sub_eq_zero.mp h_eq
  have hvi_in_span : chartBasisVecFiber (I := I) α i b ∈
      Submodule.span ℝ
        ((fun n : Fin i.val =>
          chartBasisVecFiber (I := I) α
            ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
          Set.univ) := by
    rw [hv_eq]
    apply Submodule.sum_mem
    intro j' _
    apply Submodule.smul_mem
    exact chartFrameNormFiber_mem_span_chartBasis (I := I) g α b i
      (Module.finrank ℝ E) ⟨j'.val, lt_trans j'.isLt i.isLt⟩
      (Nat.le_of_lt (lt_trans j'.isLt i.isLt)) j'.isLt
  have hset_eq :
      ((fun n : Fin i.val =>
        chartBasisVecFiber (I := I) α
          ⟨n.val, lt_trans n.isLt i.isLt⟩ b) ''
        Set.univ) =
      ((fun n : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) α n b) ''
        {n : Fin (Module.finrank ℝ E) | n.val < i.val}) := by
    ext v
    constructor
    · rintro ⟨n, _, rfl⟩
      exact ⟨⟨n.val, lt_trans n.isLt i.isLt⟩, n.isLt, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n.val, hn⟩, Set.mem_univ _, rfl⟩
  rw [hset_eq] at hvi_in_span
  have hi_notin : i ∉ {n : Fin (Module.finrank ℝ E) | n.val < i.val} := by
    simp [Set.mem_setOf_eq]
  exact hLI.notMem_span_image hi_notin hvi_in_span

/-- **Math.** **Orthogonality of `raw_i` to each previous `e_j`**, given that
$\{e_0, \ldots, e_{i-1}\}$ is already $g$-orthonormal at $b$.

Bilinear unfold of $\mathrm{raw}_i = v_i - \sum_{m < i} \langle v_i,
e_m\rangle e_m$ paired with $e_j$ on the left: only the $m = j$ term
of the sum survives (orthonormality), and that term equals
$\langle e_j, v_i\rangle$ via $g.\mathrm{symm}$, cancelling the
leading $\langle e_j, v_i\rangle$ to give $0$. -/
private lemma chartFrameRawFiber_orth_to_orthonormal_prefix
    (g : RiemannianMetric I M) (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E))
    (h_orth : ∀ j j' : Fin (Module.finrank ℝ E),
      j.val < i.val → j'.val < i.val →
      g.inner b
          (chartFrameNormFiber (I := I) g α b j)
          (chartFrameNormFiber (I := I) g α b j') =
        if j = j' then 1 else 0) :
    ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
      g.inner b
          (chartFrameNormFiber (I := I) g α b j)
          (chartFrameRawFiber (I := I) g α b i) = 0 := by
  classical
  intro j hj_lt
  -- Local notation for the recurring index-coerced normalised vector.
  set e := fun (j' : Fin i.val) =>
    chartFrameNormFiber (I := I) g α b
      ⟨j'.val, lt_trans j'.isLt i.isLt⟩ with he_def
  set vi := chartBasisVecFiber (I := I) α i b with hvi_def
  set ej := chartFrameNormFiber (I := I) g α b j with hej_def
  set c : Fin i.val → ℝ := fun j' => g.inner b vi (e j') with hc_def
  -- Unfold raw_i to the explicit subtraction form, then bilinearity.
  change g.inner b ej (vi - ∑ j' : Fin i.val, c j' • e j') = 0
  rw [show (g.inner b) ej (vi - ∑ j' : Fin i.val, c j' • e j') =
      (g.inner b) ej vi - (g.inner b) ej (∑ j' : Fin i.val, c j' • e j') from
    map_sub _ _ _]
  rw [g_inner_sum_right (I := I) g b ej Finset.univ e c]
  -- The sum: only j' = ⟨j.val, hj_lt⟩ survives.
  set j_inFin : Fin i.val := ⟨j.val, hj_lt⟩ with hj_inFin_def
  have hj_eq_inFin : (⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩ :
      Fin (Module.finrank ℝ E)) = j := Fin.ext rfl
  have hsingleton :
      ∑ j' ∈ (Finset.univ : Finset (Fin i.val)),
          c j' * g.inner b ej (e j') =
        c j_inFin * g.inner b ej (e j_inFin) := by
    refine Finset.sum_eq_single j_inFin ?_ ?_
    · intro j' _ hj'_ne
      have hj'_ne_val : j'.val ≠ j.val := fun h => hj'_ne (Fin.ext h)
      have hj'_in_total : (⟨j'.val, lt_trans j'.isLt i.isLt⟩ :
          Fin (Module.finrank ℝ E)).val < i.val := j'.isLt
      have hj_in_total : j.val < i.val := hj_lt
      have hj_ne_j' : j ≠ ⟨j'.val, lt_trans j'.isLt i.isLt⟩ := by
        intro h
        exact hj'_ne_val (congrArg Fin.val h).symm
      have hzero := h_orth j ⟨j'.val, lt_trans j'.isLt i.isLt⟩
        hj_in_total hj'_in_total
      rw [if_neg hj_ne_j'] at hzero
      show c j' * g.inner b ej (chartFrameNormFiber (I := I) g α b
          ⟨j'.val, lt_trans j'.isLt i.isLt⟩) = 0
      rw [hzero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j_inFin) h
  rw [hsingleton]
  have hej_eq : e j_inFin = ej := by
    show chartFrameNormFiber (I := I) g α b
        ⟨j_inFin.val, lt_trans j_inFin.isLt i.isLt⟩ = ej
    rw [hj_eq_inFin]
  rw [hej_eq]
  have hjj_unit : g.inner b ej ej = 1 := by
    have h := h_orth j j hj_lt hj_lt
    rw [if_pos rfl] at h
    exact h
  rw [hjj_unit, mul_one]
  -- c j_inFin = ⟨v_i, e j_inFin⟩ = ⟨v_i, ej⟩ = ⟨ej, v_i⟩ by g.symm.
  have hc_eq : c j_inFin = g.inner b vi ej := by
    show g.inner b vi (e j_inFin) = g.inner b vi ej
    rw [hej_eq]
  rw [hc_eq, g.symm]; ring

/-- **Eng.** The strong-induction package for the orthonormality of
`chartFrameNormFiber`. The conclusion bundles three facts at every
$i \le k$:

1. $\mathrm{chartFrameRawFiber}\,g\,\alpha\,b\,i \ne 0$;
2. for all $j < i$, $\langle e_j, e_i\rangle_g = 0$;
3. $\langle e_i, e_i\rangle_g = 1$.

Now a thin wrapper: the bundled IH is unpacked into an "orthonormality
on a prefix" hypothesis, which is fed to the standalone helpers
`chartFrameRawFiber_ne_zero` (Step 2) and
`chartFrameRawFiber_orth_to_orthonormal_prefix` (Step 1). The Step 3
normalisation uses `g_inner_normalised`. No `maxHeartbeats` bump
required — each helper compiles in isolation under defaults. -/
private theorem chartFrameNormFiber_orth_strong_aux
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∀ k : ℕ, ∀ i : Fin (Module.finrank ℝ E), i.val ≤ k →
      chartFrameRawFiber (I := I) g α b i ≠ 0 ∧
      (∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
        g.inner b
            (chartFrameNormFiber (I := I) g α b j)
            (chartFrameNormFiber (I := I) g α b i) = 0) ∧
      g.inner b
          (chartFrameNormFiber (I := I) g α b i)
          (chartFrameNormFiber (I := I) g α b i) = 1 := by
  classical
  intro k
  induction k with
  | zero =>
    intro i hi_le
    have hi_val : i.val = 0 := Nat.le_zero.mp hi_le
    have hi_eq : i = ⟨0, NeZero.pos _⟩ := Fin.ext hi_val
    subst hi_eq
    refine ⟨?_, ?_, ?_⟩
    · exact chartFrameRawFiber_ne_zero (I := I) g α hb _
    · intro j hj
      simp at hj
    · exact chartFrameNormFiber_at_zero_norm (I := I) g α hb
  | succ k ih =>
    intro i hi_le
    by_cases hi_lt : i.val ≤ k
    · exact ih i hi_lt
    · -- i.val = k + 1: extract orthonormality on the prefix from the IH.
      have ih_below : ∀ j : Fin (Module.finrank ℝ E), j.val < i.val →
          chartFrameRawFiber (I := I) g α b j ≠ 0 ∧
          (∀ j' : Fin (Module.finrank ℝ E), j'.val < j.val →
            g.inner b
                (chartFrameNormFiber (I := I) g α b j')
                (chartFrameNormFiber (I := I) g α b j) = 0) ∧
          g.inner b
              (chartFrameNormFiber (I := I) g α b j)
              (chartFrameNormFiber (I := I) g α b j) = 1 := by
        intro j hj
        have hj_le : j.val ≤ k := by omega
        exact ih j hj_le
      -- Orthonormality on the prefix {0, …, i.val - 1} (trichotomy on j vs j').
      have h_orth_prefix : ∀ j j' : Fin (Module.finrank ℝ E),
          j.val < i.val → j'.val < i.val →
          g.inner b
              (chartFrameNormFiber (I := I) g α b j)
              (chartFrameNormFiber (I := I) g α b j') =
            if j = j' then 1 else 0 := by
        intro j j' hj_lt hj'_lt
        rcases Nat.lt_trichotomy j.val j'.val with hlt | heq | hgt
        · -- j.val < j'.val: use IH at j'.
          have hzero := (ih_below j' hj'_lt).2.1 j hlt
          have hne : j ≠ j' := fun h => by rw [h] at hlt; omega
          rw [if_neg hne, hzero]
        · -- j = j'.
          have hjj : j = j' := Fin.ext heq
          subst hjj
          rw [if_pos rfl]
          exact (ih_below j hj_lt).2.2
        · -- j.val > j'.val: use IH at j, swap with g.symm.
          have hzero := (ih_below j hj_lt).2.1 j' hgt
          have hne : j ≠ j' := fun h => by rw [h] at hgt; omega
          rw [if_neg hne, g.symm]; exact hzero
      -- Step 2: raw_i ≠ 0 (standalone).
      have hraw_ne := chartFrameRawFiber_ne_zero (I := I) g α hb i
      -- Step 1: ⟨e_j, raw_i⟩ = 0 for j.val < i.val (uses h_orth_prefix).
      have horth_raw := chartFrameRawFiber_orth_to_orthonormal_prefix
        (I := I) g α b i h_orth_prefix
      -- Step 3: orthogonality + unit norm of e_i = (1/√N) • raw_i.
      have hgpos : 0 < g.inner b
          (chartFrameRawFiber (I := I) g α b i)
          (chartFrameRawFiber (I := I) g α b i) :=
        g.pos b (chartFrameRawFiber (I := I) g α b i) hraw_ne
      refine ⟨hraw_ne, ?_, ?_⟩
      · intro j hj_lt
        conv_lhs => rw [show chartFrameNormFiber (I := I) g α b i =
            (Real.sqrt (g.inner b
                (chartFrameRawFiber (I := I) g α b i)
                (chartFrameRawFiber (I := I) g α b i)))⁻¹ •
              chartFrameRawFiber (I := I) g α b i from
          chartFrameNormFiber_eq (I := I) g α b i]
        rw [g_inner_smul_right_normalised (I := I) g b _ _ _]
        rw [horth_raw j hj_lt, mul_zero]
      · rw [chartFrameNormFiber_eq]
        exact g_inner_normalised (I := I) g b
          (chartFrameRawFiber (I := I) g α b i) hgpos

/-- **Math.** **Inductive orthonormality** of `chartFrameNormFiber` on the
trivialization base set. For $b \in \mathrm{baseSet}$ and indices
$i, j$, the inner product
$g.\mathrm{inner}\,b\,(e_i\,b)\,(e_j\,b)$ equals $1$ if $i = j$, and
$0$ otherwise. -/
theorem chartFrameNormFiber_orthonormal
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (chartFrameNormFiber (I := I) g α b i)
        (chartFrameNormFiber (I := I) g α b j) =
      if i = j then 1 else 0 := by
  classical
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · have h := chartFrameNormFiber_orth_strong_aux (I := I) g α hb j.val j (le_refl _)
    have horth := h.2.1 i hlt
    have hne : i ≠ j := fun h_eq => by rw [h_eq] at hlt; omega
    rw [if_neg hne, horth]
  · have hi_eq_j : i = j := Fin.ext heq
    rw [if_pos hi_eq_j, ← hi_eq_j]
    exact (chartFrameNormFiber_orth_strong_aux (I := I) g α hb i.val i (le_refl _)).2.2
  · have h := chartFrameNormFiber_orth_strong_aux (I := I) g α hb i.val i (le_refl _)
    have horth_ji := h.2.1 j hgt
    have hne : i ≠ j := fun h_eq => by rw [h_eq] at hgt; omega
    rw [if_neg hne, g.symm]
    exact horth_ji

/-- **Math.** **Orthonormality** of `chartFrameNorm` (the section form) on the
trivialization base set. -/
theorem chartFrameNorm_orthonormal
    (g : RiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        (chartFrameNorm (I := I) g α i b)
        (chartFrameNorm (I := I) g α j b) =
      if i = j then 1 else 0 :=
  chartFrameNormFiber_orthonormal (I := I) g α hb i j

end Tensor
end Riemannian
