import Topping.RicciFlow.Existence.MetricControl
import Topping.Riemannian.CurvatureMultilinear

/-!
# Tensor evaluation from the pointwise `normAt`

The metric-control argument consumes a quadratic-form estimate for Ricci, while
the source hypothesis is the Hilbert--Schmidt bound `|Ric| <= M`.  This file
supplies the missing finite-dimensional Cauchy--Schwarz bridge.  The constant is
one: the coefficient vector of `x \otimes x` has squared norm
`(g(x,x))^2` in an orthonormal frame.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! A two-index finite sum is the product sum used by the elementary
Cauchy--Schwarz inequality. -/
private theorem sum_fin_two {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (f : (Fin 2 → ι) → R) :
    ∑ v, f v = ∑ a, ∑ b, f ![a, b] := by
  let e : (Fin 2 → ι) ≃ ι × ι :=
    { toFun := fun v => (v 0, v 1)
      invFun := fun x => ![x.1, x.2]
      left_inv := by
        intro v
        funext i
        fin_cases i <;> rfl
      right_inv := by
        intro x
        rcases x with ⟨a, b⟩
        rfl }
  rw [Fintype.sum_equiv e f
    (fun x => f ![x.1, x.2])
    (fun v => congrArg f (e.left_inv v).symm)]
  simp only [Fintype.sum_prod_type]

/-! The finite-dimensional Cauchy--Schwarz calculation for a bilinear form. -/
private theorem abs_bilin_eval_le_of_orthonormalBasis
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x : V) :
    |B x x| ≤ Real.sqrt (∑ i, ∑ j, B (b i) (b j) ^ 2) * inner ℝ x x := by
  classical
  let c : ι → ℝ := fun i => inner ℝ (b i) x
  have hx : x = ∑ i, c i • (b i : V) := by
    simpa only [c] using (b.sum_repr' x).symm
  have hBexp : B x x = ∑ i, ∑ j, c i * c j * B (b i) (b j) := by
    rw [hx]
    simp only [map_sum, map_smul, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hcoeff : (∑ q : ι × ι, (c q.1 * c q.2) ^ 2) =
      (inner ℝ x x) ^ 2 := by
    have hcoeff0 : ∑ i, c i ^ 2 = inner ℝ x x := by
      calc
        ∑ i, c i ^ 2 = ∑ i, inner ℝ x (b i) * inner ℝ (b i) x := by
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [c]
          rw [real_inner_comm (b i) x]
          ring
        _ = inner ℝ x x := b.sum_inner_mul_inner x x
    rw [Fintype.sum_prod_type]
    simp only [mul_pow]
    rw [← Finset.sum_mul_sum, hcoeff0]
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
    (fun q : ι × ι => c q.1 * c q.2)
    (fun q : ι × ι => B (b q.1) (b q.2))
  have hsum : (∑ q : ι × ι, (B (b q.1) (b q.2)) ^ 2) =
      ∑ i, ∑ j, B (b i) (b j) ^ 2 := by
    rw [Fintype.sum_prod_type]
  have hBexp' : B x x =
      ∑ q : ι × ι, c q.1 * c q.2 * B (b q.1) (b q.2) := by
    rw [hBexp, Fintype.sum_prod_type]
  have hsq : (B x x) ^ 2 ≤
      (inner ℝ x x) ^ 2 * (∑ i, ∑ j, B (b i) (b j) ^ 2) := by
    rw [hBexp']
    calc
      (∑ q : ι × ι, c q.1 * c q.2 * B (b q.1) (b q.2)) ^ 2
          ≤ (∑ q : ι × ι, (c q.1 * c q.2) ^ 2) *
              (∑ q : ι × ι, (B (b q.1) (b q.2)) ^ 2) := hCS
      _ = (inner ℝ x x) ^ 2 *
          (∑ i, ∑ j, B (b i) (b j) ^ 2) := by
        rw [hcoeff, hsum]
  have hS : 0 ≤ ∑ i, ∑ j, B (b i) (b j) ^ 2 := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hxx : 0 ≤ inner ℝ x x := real_inner_self_nonneg
  have hroot : 0 ≤ Real.sqrt (∑ i, ∑ j, B (b i) (b j) ^ 2) * inner ℝ x x :=
    mul_nonneg (Real.sqrt_nonneg _) hxx
  have hsq' : |B x x| ^ 2 ≤
      (Real.sqrt (∑ i, ∑ j, B (b i) (b j) ^ 2) * inner ℝ x x) ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt hS]
    nlinarith [hsq]
  nlinarith [hsq']

/-! Reindex the rank-two frame sum and apply the preceding calculation. -/
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem abs_pointwiseValue_two_le_normAt
    (g : RiemannianMetric I M) {A : CovTensorField I M 2} {p : M}
    (hA : IsPointwiseMultilinear A p) (x : TangentSpace I p) :
    |pointwiseValue A p ![x, x]| ≤ normAt g A p * g.metricInner p x x := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  let B := pairBilin hA ![]
  have hnorm : normSqAt g A p =
      ∑ i, ∑ j, B (e i) (e j) ^ 2 := by
    rw [normSqAt_eq_sum_of_frame g hA e, sum_fin_two]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    have harg : (fun q : Fin 2 => e (![i, j] q)) =
        Fin.cons (e i) (Fin.cons (e j) ![]) := by
      funext q
      fin_cases q <;> rfl
    rw [harg]
    rfl
  have hcs := abs_bilin_eval_le_of_orthonormalBasis e B x
  have hpoint : B x x = pointwiseValue A p ![x, x] := by
    change pointwiseValue A p (Fin.cons x (Fin.cons x ![])) = _
    rfl
  have hsqrt : Real.sqrt (∑ i, ∑ j, B (e i) (e j) ^ 2) = normAt g A p := by
    rw [normAt, ← hnorm]
  calc
    |pointwiseValue A p ![x, x]| = |B x x| := by rw [hpoint]
    _ ≤ Real.sqrt (∑ i, ∑ j, B (e i) (e j) ^ 2) * inner ℝ x x := hcs
    _ = normAt g A p * g.metricInner p x x := by
      rw [hsqrt]
      simp only [MorganTianLib.inner_tangentSpace_eq_metricInner]

/-! The source-level Ricci norm hypothesis implies the quadratic estimate used
by the metric-equivalence argument. -/
theorem hasPointwiseRicciQuadraticBoundOn_of_hasRicciNormBoundOn
    (g : ℝ → RiemannianMetric I M) (M0 : ℝ) (J : Set ℝ)
    (hRic : HasRicciNormBoundOn g M0 J) :
    HasPointwiseRicciQuadraticBoundOn g M0 J := by
  intro t ht p x
  have hfield : ricciCovTensorField (g t) = ricciTensorField (g t) := by
    funext Y q
    rfl
  have hA : IsPointwiseMultilinear (ricciCovTensorField (g t)) p := by
    rw [hfield]
    exact isPointwiseMultilinear_ricciTensorField (g t) p
  have hEval := abs_pointwiseValue_two_le_normAt (g t) hA x
  have hEval' : |ricciTensorAt (g t) p x x| ≤
      normAt (g t) (ricciCovTensorField (g t)) p *
        (g t).metricInner p x x := by
    simpa only [pointwiseValue, ricciCovTensorField,
      MorganTianLib.extendVector_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] using hEval
  calc
    |ricciTensorAt (g t) p x x| ≤
      normAt (g t) (ricciCovTensorField (g t)) p *
          (g t).metricInner p x x := hEval'
    _ ≤ M0 * (g t).metricInner p x x := by
      exact mul_le_mul_of_nonneg_right (hRic t ht p)
        ((g t).metricInner_self_nonneg p x)

/-! The source-facing consumer: the Hilbert--Schmidt Ricci bound can now be
fed directly into the metric-equivalence estimate, with no intermediate
target-shaped quadratic-bound hypothesis exposed to callers. -/
theorem metric_equivalence_of_ricci_norm_bound
    [Nonempty M] [CompactSpace M]
    {g : ℝ → RiemannianMetric I M} {s M0 : ℝ}
    (hs : 0 ≤ s) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Icc 0 s))
    (hRic : HasRicciNormBoundOn g M0 (Icc 0 s)) :
    ∀ t ∈ Icc 0 s,
      ScaledMetricLe (Real.exp (-2 * M0 * t)) (g 0) 1 (g t) ∧
        ScaledMetricLe 1 (g t) (Real.exp (2 * M0 * t)) (g 0) := by
  exact metric_equivalence_of_pointwise_ricci_bound hs hM hflow
    (hasPointwiseRicciQuadraticBoundOn_of_hasRicciNormBoundOn g M0
      (Icc 0 s) hRic)

#print axioms abs_pointwiseValue_two_le_normAt
#print axioms hasPointwiseRicciQuadraticBoundOn_of_hasRicciNormBoundOn
#print axioms metric_equivalence_of_ricci_norm_bound

end Topping

end
