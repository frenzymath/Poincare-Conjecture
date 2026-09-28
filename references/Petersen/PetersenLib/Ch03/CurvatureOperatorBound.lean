import PetersenLib.Ch03.CurvatureOperator
import PetersenLib.Ch03.RiemannConstantCurvature
import PetersenLib.Ch03.RicciSectional
import PetersenLib.Ch03.Exercises

/-!
# Petersen Ch. 3, Exercise 3.4.30 — the curvature operator is bounded by `|sec|`

**Math.** Petersen §3.4, Exercise 3.4.30 (`rem:pet-ch3-ex-30`). Using the
polarization identity of Exercise 3.4.29 (`exercise3_4_29`), the norm of the
curvature operator `𝔯 : Λ²T_pM → Λ²T_pM` is bounded by the largest absolute
sectional curvature at `p`:
`|𝔯|_p ≤ c(n)·|sec|_p`, with `c(n)` depending only on the dimension `n`.

We work in the skew-endomorphism model of `Λ²T_pM` (`PetersenLib.CurvatureOperator`),
where the bivector inner product is `bivectorEndoInner` and the operator is
`curvatureOperator`. The bound is stated in the squared/operator-norm form
`⟨𝔯 A, 𝔯 A⟩ ≤ (c(n)·k)²·⟨A, A⟩` for every skew endomorphism `A`, which is exactly
`|𝔯 A| ≤ c(n)·k·|A|` once `|·|` is `√⟨·,·⟩`.

The explicit constant produced here is `c(n) = 24 n²`.

Proof outline (Petersen's argument, made quantitative):
* Fix a `g`-orthonormal basis `b` of `T_pM` (`exists_metricOrthonormalBasis`).
  For any skew `C`, expanding `C` in wedges of `b`
  (`IsSkewAt.eq_sum_wedgeEndo`) gives the Frobenius formula
  `⟨C, C⟩ = ½·Σ_{ij} g(C bᵢ, bⱼ)²`.
* The matrix entries of `𝔯 A` are
  `g(𝔯A bₖ, bₗ) = ½·Σ_{ij} g(A bᵢ, bⱼ)·R(bₖ,bₗ,bⱼ,bᵢ)`, using self-adjointness
  of `𝔯` and its defining property on wedges.
* Each `R(bₖ,bₗ,bⱼ,bᵢ)` is a sum of 18 diagonal terms `R(a,b,b,a)` by
  polarization (`exercise3_4_29`); each diagonal term is bounded by
  `k·g(a,a)·g(b,b) ≤ 16k`, so `|R(bₖ,bₗ,bⱼ,bᵢ)| ≤ 48k`.
* Cauchy–Schwarz over the `n²` index pairs then gives the operator bound.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.4, Exercise 3.4.30.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

section Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {g : RiemannianMetric I M}

/-- **Math.** Quantitative core of Exercise 3.4.30 in a fixed `g`-orthonormal
basis `b` (indexed by a finite type `ι`): with `K` a uniform bound on the
absolute sectional curvature at `p`, the curvature operator satisfies
`⟨𝔯 A, 𝔯 A⟩ ≤ (24·|ι|²·K)²·⟨A, A⟩` for every skew endomorphism `A`. -/
private theorem curvatureOperator_bound_aux (D : RiemannianConnection I g) (p : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0)
    (K : ℝ) (hK : 0 ≤ K)
    (hsec : ∀ v w : TangentSpace I p, |sectionalCurvature D p v w| ≤ K)
    (A : Module.End ℝ (TangentSpace I p)) (hA : IsSkewAt g p A) :
    bivectorEndoInner g p (curvatureOperator D p A) (curvatureOperator D p A)
      ≤ (24 * (Fintype.card ι : ℝ) ^ 2 * K) ^ 2 * bivectorEndoInner g p A A := by
  classical
  have hAlg := isAlgCurvatureForm_curvatureTensorFourAt D p
  -- Flattening a double `ι` sum to a sum over the product type.
  have flat : ∀ f : ι → ι → ℝ, (∑ i, ∑ j, f i j) = ∑ q : ι × ι, f q.1 q.2 :=
    fun f => (Fintype.sum_prod_type (fun q => f q.1 q.2)).symm
  -- Diagonal bound: `|R(a,b,b,a)| ≤ K·g(a,a)·g(b,b)`.
  have hdiag : ∀ a c : TangentSpace I p,
      |curvatureTensorFourAt D p a c c a|
        ≤ K * (g.metricInner p a a * g.metricInner p c c) := by
    intro a c
    by_cases hind : LinearIndependent ℝ ![c, a]
    · have hpos := bivectorInnerProduct_self_pos g p hind
      have hs := hsec c a
      rw [sectionalCurvature_eq_curvatureTensorFourAt] at hs
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at hs
      refine hs.trans ?_
      apply mul_le_mul_of_nonneg_left _ hK
      rw [bivectorInnerProduct]
      have hcm : g.metricInner p a c = g.metricInner p c a := g.metricInner_comm p a c
      rw [hcm]
      nlinarith [sq_nonneg (g.metricInner p c a)]
    · have hz : curvatureTensorFourAt D p c a c a = 0 :=
        hAlg.diag_eq_zero_of_not_linearIndependent hind
      have hz2 : curvatureTensorFourAt D p a c c a = 0 := by
        rw [hAlg.antisymm₁₂ a c c a, hz, neg_zero]
      rw [hz2, abs_zero]
      exact mul_nonneg hK
        (mul_nonneg (g.metricInner_self_nonneg p a) (g.metricInner_self_nonneg p c))
  -- Entry bound from the diagonal bound with `g(u,u), g(w,w) ≤ 4`.
  have hentry : ∀ u w : TangentSpace I p,
      g.metricInner p u u ≤ 4 → g.metricInner p w w ≤ 4 →
      |curvatureTensorFourAt D p u w w u| ≤ 16 * K := by
    intro u w hu hw
    refine (hdiag u w).trans ?_
    have h1 : g.metricInner p u u * g.metricInner p w w ≤ 4 * 4 :=
      mul_le_mul hu hw (g.metricInner_self_nonneg p w) (by norm_num)
    calc K * (g.metricInner p u u * g.metricInner p w w) ≤ K * (4 * 4) :=
          mul_le_mul_of_nonneg_left h1 hK
      _ = 16 * K := by ring
  -- Norm bounds for single and paired basis vectors.
  have hb1 : ∀ s : ι, g.metricInner p (b s) (b s) ≤ 4 := by
    intro s; rw [hb s s, if_pos rfl]; norm_num
  have hb4 : ∀ s t : ι, g.metricInner p (b s + b t) (b s + b t) ≤ 4 := by
    intro s t
    simp only [g.metricInner_add_left, g.metricInner_add_right, hb]
    split_ifs <;> norm_num
  -- Per-entry curvature bound via polarization (Exercise 3.4.29).
  have hR48 : ∀ i j k l : ι,
      |curvatureTensorFourAt D p (b k) (b l) (b j) (b i)| ≤ 48 * K := by
    intro i j k l
    have heq := exercise3_4_29 hAlg (b k) (b l) (b j) (b i)
    have t1 := hentry (b k + b i) (b l + b j) (hb4 k i) (hb4 l j)
    have t2 := hentry (b k) (b l + b j) (hb1 k) (hb4 l j)
    have t3 := hentry (b i) (b l + b j) (hb1 i) (hb4 l j)
    have t4 := hentry (b k + b i) (b j) (hb4 k i) (hb1 j)
    have t5 := hentry (b k + b i) (b l) (hb4 k i) (hb1 l)
    have t6 := hentry (b k) (b j) (hb1 k) (hb1 j)
    have t7 := hentry (b i) (b j) (hb1 i) (hb1 j)
    have t8 := hentry (b k) (b l) (hb1 k) (hb1 l)
    have t9 := hentry (b i) (b l) (hb1 i) (hb1 l)
    have t10 := hentry (b k + b j) (b l + b i) (hb4 k j) (hb4 l i)
    have t11 := hentry (b k) (b l + b i) (hb1 k) (hb4 l i)
    have t12 := hentry (b j) (b l + b i) (hb1 j) (hb4 l i)
    have t13 := hentry (b k + b j) (b l) (hb4 k j) (hb1 l)
    have t14 := hentry (b k + b j) (b i) (hb4 k j) (hb1 i)
    have t15 := hentry (b k) (b l) (hb1 k) (hb1 l)
    have t16 := hentry (b j) (b l) (hb1 j) (hb1 l)
    have t17 := hentry (b k) (b i) (hb1 k) (hb1 i)
    have t18 := hentry (b j) (b i) (hb1 j) (hb1 i)
    rw [abs_le] at t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 ⊢
    constructor <;>
      linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2,
        t6.1, t6.2, t7.1, t7.2, t8.1, t8.2, t9.1, t9.2, t10.1, t10.2, t11.1, t11.2,
        t12.1, t12.2, t13.1, t13.2, t14.1, t14.2, t15.1, t15.2, t16.1, t16.2,
        t17.1, t17.2, t18.1, t18.2]
  -- Frobenius formula for the bivector inner product of a skew endomorphism.
  have hfrob : ∀ C : Module.End ℝ (TangentSpace I p), IsSkewAt g p C →
      bivectorEndoInner g p C C
        = (1 / 2 : ℝ) * ∑ i, ∑ j, (g.metricInner p (C (b i)) (b j)) ^ 2 := by
    intro C hC
    have hexp := hC.eq_sum_wedgeEndo b hb
    calc bivectorEndoInner g p C C
        = bivectorEndoInner g p C ((1 / 2 : ℝ) • ∑ i, ∑ j,
            g.metricInner p (C (b i)) (b j) • wedgeEndo g p (b i) (b j)) := by
          rw [← hexp]
      _ = (1 / 2 : ℝ) * ∑ i, ∑ j, (g.metricInner p (C (b i)) (b j)) ^ 2 := by
          simp only [bivectorEndoInner_smul_right, bivectorEndoInner_sum_right]
          congr 1
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [bivectorEndoInner_wedgeEndo_right g p hC, pow_two]
  -- Matrix entries of `𝔯 A`.
  have hP : ∀ k l : ι,
      g.metricInner p (curvatureOperator D p A (b k)) (b l)
        = (1 / 2 : ℝ) * ∑ i, ∑ j,
            g.metricInner p (A (b i)) (b j)
              * curvatureTensorFourAt D p (b k) (b l) (b j) (b i) := by
    intro k l
    rw [← bivectorEndoInner_wedgeEndo_right g p
        (isSkewAt_curvatureOperator D p A) (b k) (b l),
      curvatureOperator_isSelfAdjoint D p b hb hA (isSkewAt_wedgeEndo g p (b k) (b l)),
      bivectorEndoInner_comm]
    conv_lhs => rw [hA.eq_sum_wedgeEndo b hb]
    simp only [bivectorEndoInner_smul_right, bivectorEndoInner_sum_right,
      bivectorEndoInner_curvatureOperator_wedge_wedge]
  -- Abbreviate the squared Frobenius norm of `A`.
  have hAA := hfrob A hA
  set SA := ∑ i, ∑ j, (g.metricInner p (A (b i)) (b j)) ^ 2 with hSA
  have hRR := hfrob (curvatureOperator D p A) (isSkewAt_curvatureOperator D p A)
  have hSAnn : 0 ≤ SA := by
    rw [hSA]; exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- Key pointwise bound on the squared matrix entries of `𝔯 A`.
  have hkey : ∀ k l : ι,
      (g.metricInner p (curvatureOperator D p A (b k)) (b l)) ^ 2
        ≤ (1 / 4 : ℝ) * ((Fintype.card ι : ℝ) ^ 2 * (48 * K) ^ 2) * SA := by
    intro k l
    rw [hP k l,
      flat (fun i j => g.metricInner p (A (b i)) (b j)
        * curvatureTensorFourAt D p (b k) (b l) (b j) (b i)),
      mul_pow]
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
      (fun q => g.metricInner p (A (b q.1)) (b q.2))
      (fun q => curvatureTensorFourAt D p (b k) (b l) (b q.2) (b q.1))
    have hRS : (∑ q : ι × ι,
        (curvatureTensorFourAt D p (b k) (b l) (b q.2) (b q.1)) ^ 2)
          ≤ (Fintype.card ι : ℝ) ^ 2 * (48 * K) ^ 2 := by
      have hterm : ∀ q : ι × ι,
          (curvatureTensorFourAt D p (b k) (b l) (b q.2) (b q.1)) ^ 2 ≤ (48 * K) ^ 2 := by
        intro q
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hR48 q.1 q.2 k l) 2
      refine (Finset.sum_le_sum fun q _ => hterm q).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
      push_cast; ring
    have hSAeq : (∑ q : ι × ι, (g.metricInner p (A (b q.1)) (b q.2)) ^ 2) = SA := by
      rw [hSA]; exact (flat (fun i j => (g.metricInner p (A (b i)) (b j)) ^ 2)).symm
    calc (1 / 2 : ℝ) ^ 2
          * (∑ q : ι × ι, g.metricInner p (A (b q.1)) (b q.2)
              * curvatureTensorFourAt D p (b k) (b l) (b q.2) (b q.1)) ^ 2
        ≤ (1 / 2 : ℝ) ^ 2
            * ((∑ q : ι × ι, (g.metricInner p (A (b q.1)) (b q.2)) ^ 2)
              * ∑ q : ι × ι,
                  (curvatureTensorFourAt D p (b k) (b l) (b q.2) (b q.1)) ^ 2) :=
          mul_le_mul_of_nonneg_left hCS (by norm_num)
      _ ≤ (1 / 2 : ℝ) ^ 2 * (SA * ((Fintype.card ι : ℝ) ^ 2 * (48 * K) ^ 2)) := by
          rw [hSAeq]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRS hSAnn) (by norm_num)
      _ = (1 / 4 : ℝ) * ((Fintype.card ι : ℝ) ^ 2 * (48 * K) ^ 2) * SA := by ring
  -- Sum over `k, l` and finish.
  have sumconst : ∀ c : ℝ, (∑ _k : ι, ∑ _l : ι, c) = (Fintype.card ι : ℝ) ^ 2 * c := by
    intro c
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  calc bivectorEndoInner g p (curvatureOperator D p A) (curvatureOperator D p A)
      = (1 / 2 : ℝ) * ∑ k, ∑ l,
          (g.metricInner p (curvatureOperator D p A (b k)) (b l)) ^ 2 := hRR
    _ ≤ (1 / 2 : ℝ) * ∑ _k : ι, ∑ _l : ι,
          (1 / 4 : ℝ) * ((Fintype.card ι : ℝ) ^ 2 * (48 * K) ^ 2) * SA := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hkey k l
    _ = (1 / 2 : ℝ)
          * ((Fintype.card ι : ℝ) ^ 2
            * ((1 / 4 : ℝ) * ((Fintype.card ι : ℝ) ^ 2 * (48 * K) ^ 2) * SA)) := by
        rw [sumconst]
    _ = 576 * (Fintype.card ι : ℝ) ^ 4 * K ^ 2 * ((1 / 2 : ℝ) * SA) := by ring
    _ = (24 * (Fintype.card ι : ℝ) ^ 2 * K) ^ 2 * bivectorEndoInner g p A A := by
        rw [hAA]; ring

end Aux

/-- **Math.** Petersen §3.4, Exercise 3.4.30: the curvature operator `𝔯` on
`Λ²T_pM` is bounded in norm by the largest absolute sectional curvature at `p`,
`|𝔯|_p ≤ c(n)·|sec|_p`, with `c(n) = 24 n²` depending only on the dimension.
Stated in squared form: for every skew endomorphism `A` (a bivector), with `k`
a uniform bound on `|sec|` at `p`,
`⟨𝔯 A, 𝔯 A⟩ ≤ (c(n)·k)²·⟨A, A⟩`. -/
theorem exercise3_4_30 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [LocallyCompactSpace M] {g : RiemannianMetric I M} (D : RiemannianConnection I g) :
    ∃ c : ℕ → ℝ, ∀ (p : M) (k : ℝ), 0 ≤ k →
      (∀ v w : TangentSpace I p, |sectionalCurvature D p v w| ≤ k) →
      ∀ A : Module.End ℝ (TangentSpace I p), IsSkewAt g p A →
        bivectorEndoInner g p (curvatureOperator D p A) (curvatureOperator D p A)
          ≤ (c (Module.finrank ℝ E) * k) ^ 2 * bivectorEndoInner g p A A := by
  classical
  refine ⟨fun m => 24 * (m : ℝ) ^ 2, ?_⟩
  intro p k hk hsec A hA
  obtain ⟨b, hb⟩ := exists_metricOrthonormalBasis g p
  have key := curvatureOperator_bound_aux D p b hb k hk hsec A hA
  rw [Fintype.card_fin] at key
  exact key
