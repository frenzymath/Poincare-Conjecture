import MorganTianLib.Ch03.RicciFlow.MetricCoordinateVariation
import Topping.MaximumPrinciple.CurvatureNormEvolutionUniform
import Topping.MaximumPrinciple.CurvatureStarBound
import Topping.RicciFlow.CurvatureEvolutionDerived
import Topping.RicciFlow.CurvatureStarUniform
import Topping.Riemannian.TensorNormChart
import Topping.Riemannian.Variation

/-!
# Curvature-norm variation in a fixed chart

The time derivative of `|Rm|^2` has two sources: the inverse metrics used in
the full contraction and the covariant curvature components themselves.  This
file combines the genuine fixed-chart inverse-metric variation with Topping's
component curvature evolution and records the resulting derivative as an
explicit finite contraction.  No named evolution hypothesis is introduced for
this intermediate expression.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private def finFourArrowEquiv (ι : Type*) :
    (Fin 4 → ι) ≃ ι × ι × ι × ι where
  toFun v := (v 0, v 1, v 2, v 3)
  invFun x := ![x.1, x.2.1, x.2.2.1, x.2.2.2]
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    rcases x with ⟨a, b, c, d⟩
    rfl

private theorem sum_fin_four {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (f : (Fin 4 → ι) → R) :
    ∑ v, f v = ∑ a, ∑ b, ∑ c, ∑ d, f ![a, b, c, d] := by
  rw [Fintype.sum_equiv (finFourArrowEquiv ι) f
    (fun x => f ![x.1, x.2.1, x.2.2.1, x.2.2.2])
    (fun x => congrArg f ((finFourArrowEquiv ι).left_inv x).symm)]
  simp only [Fintype.sum_prod_type]

private def finFiveArrowEquiv (ι : Type*) :
    (Fin 5 → ι) ≃ ι × ι × ι × ι × ι where
  toFun v := (v 0, v 1, v 2, v 3, v 4)
  invFun x := ![x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2]
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    rcases x with ⟨a, b, c, d, e⟩
    rfl

private theorem sum_fin_five {ι R : Type*} [Fintype ι] [AddCommMonoid R]
    (f : (Fin 5 → ι) → R) :
    ∑ v, f v = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f ![a, b, c, d, e] := by
  rw [Fintype.sum_equiv (finFiveArrowEquiv ι) f
    (fun x => f ![x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2])
    (fun x => congrArg f ((finFiveArrowEquiv ι).left_inv x).symm)]
  simp only [Fintype.sum_prod_type]

private def tupleReindex {n : ℕ} {ι : Type*} (σ : Equiv.Perm (Fin n)) :
    (Fin n → ι) ≃ (Fin n → ι) where
  toFun x := x ∘ σ
  invFun x := x ∘ σ.symm
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

private theorem sum_tuple_reindex {n : ℕ} {ι R : Type*} [Fintype ι]
    [AddCommMonoid R] (σ : Equiv.Perm (Fin n)) (f : (Fin n → ι) → R) :
    ∑ x, f (x ∘ σ) = ∑ x, f x :=
  (tupleReindex (ι := ι) σ).sum_comp f

private def permFiveZero : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 2, 0, 1]
  invFun := ![3, 4, 2, 0, 1]
  left_inv := by decide
  right_inv := by decide

private def permFiveOne : Equiv.Perm (Fin 5) where
  toFun := ![3, 4, 0, 1, 2]
  invFun := ![2, 3, 4, 0, 1]
  left_inv := by decide
  right_inv := by decide

private def permFiveTwo : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 4, 2, 3]
  invFun := ![0, 1, 3, 4, 2]
  left_inv := by decide
  right_inv := by decide

/-- **Math.** The entrywise inverse-Gram variation under Ricci flow,
`partial_t g^{cb} = 2 g^{ca} Ric_ad g^{db}`, kept in the product-rule form
supplied by inverse-matrix differentiation. -/
def ricciFlowChartInvGramVariation (g : RiemannianMetric I M) (alpha p : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun c b => - ∑ a, ∑ d,
    Tensor.chartInvGramMatrix (I := I) g alpha p c a
      * (-2 * ricciTensorAt g p
          (Tensor.chartBasisVecFiber (I := I) alpha a p)
          (Tensor.chartBasisVecFiber (I := I) alpha d p))
      * Tensor.chartInvGramMatrix (I := I) g alpha p d b

/-- **Math.** The component derivative `Delta Rm + Q(Rm)` evaluated on the
chosen global extensions of a tuple of tangent vectors at `p`. -/
def curvatureEvolutionComponentAt (g : RiemannianMetric I M) (p : M)
    (w : Fin 4 → TangentSpace I p) : ℝ :=
  let Y := fun i => MorganTianLib.extendVector p (w i)
  roughLaplacian g g.leviCivitaConnection (riemannTensorField g) Y p
    + curvatureEvolutionCorrection g Y p

/-- **Math.** In a fixed orthonormal basis, the two curvature-component terms
in the product rule are exactly twice the intrinsic pairing of `Rm` with its
component evolution `ΔRm + Q(Rm)`. -/
theorem curvatureComponentVariation_eq_tensorInnerAt
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    let v := e.toBasis
    let A := pointwiseMultilinearMap
      (isPointwiseMultilinear_riemannTensorField g p)
    let dA := curvatureEvolutionComponentAt (I := I) g p
    (∑ a, ∑ b, ∑ c, ∑ d,
        dA (basisTuple4 v a b c d) * multilinearComponent4 v A a b c d)
      + (∑ a, ∑ b, ∑ c, ∑ d,
        multilinearComponent4 v A a b c d * dA (basisTuple4 v a b c d)) =
      2 * tensorInnerAt g (riemannTensorField g)
        (fun Y q =>
          roughLaplacian g g.leviCivitaConnection (riemannTensorField g) Y q
            + curvatureEvolutionCorrection g Y q) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  let v := e.toBasis
  let A := pointwiseMultilinearMap
    (isPointwiseMultilinear_riemannTensorField g p)
  let dA := curvatureEvolutionComponentAt (I := I) g p
  let B : CovTensorField I M 4 := fun Y q =>
    roughLaplacian g g.leviCivitaConnection (riemannTensorField g) Y q
      + curvatureEvolutionCorrection g Y q
  change
    (∑ a, ∑ b, ∑ c, ∑ d,
        dA (basisTuple4 v a b c d) * multilinearComponent4 v A a b c d)
      + (∑ a, ∑ b, ∑ c, ∑ d,
        multilinearComponent4 v A a b c d * dA (basisTuple4 v a b c d)) =
      2 * tensorInnerAt g (riemannTensorField g) B p
  have hA (a b c d : Fin (Module.finrank ℝ (TangentSpace I p))) :
      multilinearComponent4 v A a b c d =
        riemannCurvatureAt g p (e a) (e b) (e c) (e d) := by
    simp only [A, multilinearComponent4, pointwiseMultilinearMap,
      MultilinearMap.coe_mk, pointwiseValue, riemannTensorField,
      MorganTianLib.extendVector_apply]
    congr 1
  have htuple (a b c d : Fin (Module.finrank ℝ (TangentSpace I p))) :
      (fun i => MorganTianLib.extendVector p (basisTuple4 v a b c d i)) =
        (fun i => MorganTianLib.extendVector p (e (![a, b, c, d] i))) := by
    funext i
    fin_cases i <;> congr 1
  have hdA (a b c d : Fin (Module.finrank ℝ (TangentSpace I p))) :
      dA (basisTuple4 v a b c d) =
        B (fun i => MorganTianLib.extendVector p (e (![a, b, c, d] i))) p := by
    simp only [dA, curvatureEvolutionComponentAt, B]
    rw [htuple]
  have hRm (a b c d : Fin (Module.finrank ℝ (TangentSpace I p))) :
      riemannTensorField g
          (fun i => MorganTianLib.extendVector p (e (![a, b, c, d] i))) p =
        riemannCurvatureAt g p (e a) (e b) (e c) (e d) := by
    simp only [riemannTensorField, MorganTianLib.extendVector_apply]
    congr 1
  have hleft₁ :
      (∑ a, ∑ b, ∑ c, ∑ d,
          dA (basisTuple4 v a b c d) * multilinearComponent4 v A a b c d) =
        ∑ a, ∑ b, ∑ c, ∑ d,
          riemannCurvatureAt g p (e a) (e b) (e c) (e d) *
            B (fun i => MorganTianLib.extendVector p (e (![a, b, c, d] i))) p := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [hdA, hA, mul_comm]
  have hleft₂ :
      (∑ a, ∑ b, ∑ c, ∑ d,
          multilinearComponent4 v A a b c d * dA (basisTuple4 v a b c d)) =
        ∑ a, ∑ b, ∑ c, ∑ d,
          riemannCurvatureAt g p (e a) (e b) (e c) (e d) *
            B (fun i => MorganTianLib.extendVector p (e (![a, b, c, d] i))) p := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [hdA, hA]
  have hinner :
      tensorInnerAt g (riemannTensorField g) B p =
        ∑ a, ∑ b, ∑ c, ∑ d,
          riemannCurvatureAt g p (e a) (e b) (e c) (e d) *
            B (fun i => MorganTianLib.extendVector p (e (![a, b, c, d] i))) p := by
    rw [tensorInnerAt, sum_fin_four]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [hRm a b c d]
  rw [hleft₁, hleft₂, hinner]
  ring

/-- **Math.** The four inverse-metric slot variations in the squared norm of an
algebraic curvature tensor agree after reindexing the orthonormal-basis sums. -/
private theorem curvatureMetricFlatSlots_eq_four_last
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    let R := riemannCurvatureAt g p
    let Ric := ricciTensorAt g p
    let f₀ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
      (2 * Ric (e (x 0)) (e (x 1))) *
        R (e (x 0)) (e (x 2)) (e (x 3)) (e (x 4)) *
          R (e (x 1)) (e (x 2)) (e (x 3)) (e (x 4))
    let f₁ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
      (2 * Ric (e (x 1)) (e (x 2))) *
        R (e (x 0)) (e (x 1)) (e (x 3)) (e (x 4)) *
          R (e (x 0)) (e (x 2)) (e (x 3)) (e (x 4))
    let f₂ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
      (2 * Ric (e (x 2)) (e (x 3))) *
        R (e (x 0)) (e (x 1)) (e (x 2)) (e (x 4)) *
          R (e (x 0)) (e (x 1)) (e (x 3)) (e (x 4))
    let f₃ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
      (2 * Ric (e (x 3)) (e (x 4))) *
        R (e (x 0)) (e (x 1)) (e (x 2)) (e (x 3)) *
          R (e (x 0)) (e (x 1)) (e (x 2)) (e (x 4))
    (∑ x, f₀ x) + (∑ x, f₁ x) + (∑ x, f₂ x) + (∑ x, f₃ x) =
      4 * ∑ x, f₃ x := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  let R := riemannCurvatureAt g p
  let Ric := ricciTensorAt g p
  let f₀ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
    (2 * Ric (e (x 0)) (e (x 1))) *
      R (e (x 0)) (e (x 2)) (e (x 3)) (e (x 4)) *
        R (e (x 1)) (e (x 2)) (e (x 3)) (e (x 4))
  let f₁ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
    (2 * Ric (e (x 1)) (e (x 2))) *
      R (e (x 0)) (e (x 1)) (e (x 3)) (e (x 4)) *
        R (e (x 0)) (e (x 2)) (e (x 3)) (e (x 4))
  let f₂ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
    (2 * Ric (e (x 2)) (e (x 3))) *
      R (e (x 0)) (e (x 1)) (e (x 2)) (e (x 4)) *
        R (e (x 0)) (e (x 1)) (e (x 3)) (e (x 4))
  let f₃ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
    (2 * Ric (e (x 3)) (e (x 4))) *
      R (e (x 0)) (e (x 1)) (e (x 2)) (e (x 3)) *
        R (e (x 0)) (e (x 1)) (e (x 2)) (e (x 4))
  change (∑ x, f₀ x) + (∑ x, f₁ x) + (∑ x, f₂ x) + (∑ x, f₃ x) =
    4 * ∑ x, f₃ x
  have halg := riemannCurvatureAt_isAlg g p
  have h₀point (x : Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) :
      f₀ x = f₃ (x ∘ permFiveZero) := by
    change
      (2 * Ric (e (x 0)) (e (x 1))) *
          R (e (x 0)) (e (x 2)) (e (x 3)) (e (x 4)) *
            R (e (x 1)) (e (x 2)) (e (x 3)) (e (x 4)) =
        (2 * Ric (e (x 0)) (e (x 1))) *
          R (e (x 3)) (e (x 4)) (e (x 2)) (e (x 0)) *
            R (e (x 3)) (e (x 4)) (e (x 2)) (e (x 1))
    simp only [R]
    rw [halg.pairSwap (e (x 0)) (e (x 2)) (e (x 3)) (e (x 4)),
      halg.pairSwap (e (x 1)) (e (x 2)) (e (x 3)) (e (x 4)),
      halg.antisymm₃₄ (e (x 3)) (e (x 4)) (e (x 0)) (e (x 2)),
      halg.antisymm₃₄ (e (x 3)) (e (x 4)) (e (x 1)) (e (x 2))]
    ring
  have h₁point (x : Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) :
      f₁ x = f₃ (x ∘ permFiveOne) := by
    change
      (2 * Ric (e (x 1)) (e (x 2))) *
          R (e (x 0)) (e (x 1)) (e (x 3)) (e (x 4)) *
            R (e (x 0)) (e (x 2)) (e (x 3)) (e (x 4)) =
        (2 * Ric (e (x 1)) (e (x 2))) *
          R (e (x 3)) (e (x 4)) (e (x 0)) (e (x 1)) *
            R (e (x 3)) (e (x 4)) (e (x 0)) (e (x 2))
    simp only [R]
    rw [halg.pairSwap (e (x 0)) (e (x 1)) (e (x 3)) (e (x 4)),
      halg.pairSwap (e (x 0)) (e (x 2)) (e (x 3)) (e (x 4))]
  have h₂point (x : Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) :
      f₂ x = f₃ (x ∘ permFiveTwo) := by
    change
      (2 * Ric (e (x 2)) (e (x 3))) *
          R (e (x 0)) (e (x 1)) (e (x 2)) (e (x 4)) *
            R (e (x 0)) (e (x 1)) (e (x 3)) (e (x 4)) =
        (2 * Ric (e (x 2)) (e (x 3))) *
          R (e (x 0)) (e (x 1)) (e (x 4)) (e (x 2)) *
            R (e (x 0)) (e (x 1)) (e (x 4)) (e (x 3))
    simp only [R]
    rw [halg.antisymm₃₄ (e (x 0)) (e (x 1)) (e (x 2)) (e (x 4)),
      halg.antisymm₃₄ (e (x 0)) (e (x 1)) (e (x 3)) (e (x 4))]
    ring
  have h₀ : (∑ x, f₀ x) = ∑ x, f₃ x := calc
    ∑ x, f₀ x = ∑ x, f₃ (x ∘ permFiveZero) :=
      Finset.sum_congr rfl fun x _ => h₀point x
    _ = ∑ x, f₃ x := sum_tuple_reindex permFiveZero f₃
  have h₁ : (∑ x, f₁ x) = ∑ x, f₃ x := calc
    ∑ x, f₁ x = ∑ x, f₃ (x ∘ permFiveOne) :=
      Finset.sum_congr rfl fun x _ => h₁point x
    _ = ∑ x, f₃ x := sum_tuple_reindex permFiveOne f₃
  have h₂ : (∑ x, f₂ x) = ∑ x, f₃ x := calc
    ∑ x, f₂ x = ∑ x, f₃ (x ∘ permFiveTwo) :=
      Finset.sum_congr rfl fun x _ => h₂point x
    _ = ∑ x, f₃ x := sum_tuple_reindex permFiveTwo f₃
  rw [h₀, h₁, h₂]
  ring

/-- **Math.** The common inverse-metric slot contribution is twice the
intrinsic pairing of `Rm` with `Ric(Rm(·,·)·,·)`. -/
theorem curvatureMetricLastSlot_eq_tensorInnerAt
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ j,
      (2 * ricciTensorAt g p (e d) (e j)) *
        riemannCurvatureAt g p (e a) (e b) (e c) (e d) *
          riemannCurvatureAt g p (e a) (e b) (e c) (e j)) =
      2 * tensorInnerAt g (riemannTensorField g)
        (contract₂Perm g starPermRic (riemannTensorField g)
          (riemannTensorField g)) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  let C := contract₂Perm g starPermRic (riemannTensorField g)
    (riemannTensorField g)
  change
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ j,
      (2 * ricciTensorAt g p (e d) (e j)) *
        riemannCurvatureAt g p (e a) (e b) (e c) (e d) *
          riemannCurvatureAt g p (e a) (e b) (e c) (e j)) =
      2 * tensorInnerAt g (riemannTensorField g) C p
  have hRm (a b c d : Fin (Module.finrank ℝ (TangentSpace I p))) :
      riemannTensorField g
          (fun i => MorganTianLib.extendVector p (e (![a, b, c, d] i))) p =
        riemannCurvatureAt g p (e a) (e b) (e c) (e d) := by
    simp only [riemannTensorField, MorganTianLib.extendVector_apply]
    congr 1
  have hC (a b c d : Fin (Module.finrank ℝ (TangentSpace I p))) :
      C (fun i => MorganTianLib.extendVector p (e (![a, b, c, d] i))) p =
        ∑ j, riemannCurvatureAt g p (e a) (e b) (e c) (e j) *
          ricciTensorAt g p (e j) (e d) := by
    simp only [C]
    rw [contract₂Perm_starPermRic]
    convert ricciTensorAt_curvatureOperatorAt_expand g p
      (e a) (e b) (e c) (e d) using 1 <;>
        simp only [MorganTianLib.extendVector_apply] <;> congr 1
  have hinner :
      tensorInnerAt g (riemannTensorField g) C p =
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ j,
          riemannCurvatureAt g p (e a) (e b) (e c) (e d) *
            (riemannCurvatureAt g p (e a) (e b) (e c) (e j) *
              ricciTensorAt g p (e j) (e d)) := by
    rw [tensorInnerAt, sum_fin_four]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [hRm a b c d, hC a b c d, Finset.mul_sum]
  rw [hinner]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro j _
  rw [ricciTensorAt_symm g p (e d) (e j)]
  ring

/-- **Math.** The four inverse-metric terms in the fixed-frame product rule
sum to eight times the intrinsic pairing with the Ricci-curvature contraction. -/
theorem curvatureMetricSlotVariation_eq_tensorInnerAt
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    let v := e.toBasis
    let A := pointwiseMultilinearMap
      (isPointwiseMultilinear_riemannTensorField g p)
    let dG : Matrix (Fin (Module.finrank ℝ (TangentSpace I p)))
        (Fin (Module.finrank ℝ (TangentSpace I p))) ℝ := fun a b =>
      2 * ricciTensorAt g p (v a) (v b)
    (∑ a, ∑ b, dG a b * ∑ c, ∑ d, ∑ j,
        multilinearComponent4 v A a c d j * multilinearComponent4 v A b c d j)
      + (∑ a, ∑ b, ∑ c, dG b c * ∑ d, ∑ j,
        multilinearComponent4 v A a b d j * multilinearComponent4 v A a c d j)
      + (∑ a, ∑ b, ∑ c, ∑ d, dG c d * ∑ j,
        multilinearComponent4 v A a b c j * multilinearComponent4 v A a b d j)
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ j, dG d j *
        multilinearComponent4 v A a b c d * multilinearComponent4 v A a b c j) =
      8 * tensorInnerAt g (riemannTensorField g)
        (contract₂Perm g starPermRic (riemannTensorField g)
          (riemannTensorField g)) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  let v := e.toBasis
  let A := pointwiseMultilinearMap
    (isPointwiseMultilinear_riemannTensorField g p)
  let dG : Matrix (Fin (Module.finrank ℝ (TangentSpace I p)))
      (Fin (Module.finrank ℝ (TangentSpace I p))) ℝ := fun a b =>
    2 * ricciTensorAt g p (v a) (v b)
  let R := riemannCurvatureAt g p
  let Ric := ricciTensorAt g p
  let f₀ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
    (2 * Ric (e (x 0)) (e (x 1))) *
      R (e (x 0)) (e (x 2)) (e (x 3)) (e (x 4)) *
        R (e (x 1)) (e (x 2)) (e (x 3)) (e (x 4))
  let f₁ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
    (2 * Ric (e (x 1)) (e (x 2))) *
      R (e (x 0)) (e (x 1)) (e (x 3)) (e (x 4)) *
        R (e (x 0)) (e (x 2)) (e (x 3)) (e (x 4))
  let f₂ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
    (2 * Ric (e (x 2)) (e (x 3))) *
      R (e (x 0)) (e (x 1)) (e (x 2)) (e (x 4)) *
        R (e (x 0)) (e (x 1)) (e (x 3)) (e (x 4))
  let f₃ : (Fin 5 → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun x =>
    (2 * Ric (e (x 3)) (e (x 4))) *
      R (e (x 0)) (e (x 1)) (e (x 2)) (e (x 3)) *
        R (e (x 0)) (e (x 1)) (e (x 2)) (e (x 4))
  change
    (∑ a, ∑ b, dG a b * ∑ c, ∑ d, ∑ j,
        multilinearComponent4 v A a c d j * multilinearComponent4 v A b c d j)
      + (∑ a, ∑ b, ∑ c, dG b c * ∑ d, ∑ j,
        multilinearComponent4 v A a b d j * multilinearComponent4 v A a c d j)
      + (∑ a, ∑ b, ∑ c, ∑ d, dG c d * ∑ j,
        multilinearComponent4 v A a b c j * multilinearComponent4 v A a b d j)
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ j, dG d j *
        multilinearComponent4 v A a b c d * multilinearComponent4 v A a b c j) =
      8 * tensorInnerAt g (riemannTensorField g)
        (contract₂Perm g starPermRic (riemannTensorField g)
          (riemannTensorField g)) p
  have hA (a b c d : Fin (Module.finrank ℝ (TangentSpace I p))) :
      multilinearComponent4 v A a b c d = R (e a) (e b) (e c) (e d) := by
    simp only [A, R, multilinearComponent4, pointwiseMultilinearMap,
      MultilinearMap.coe_mk, pointwiseValue, riemannTensorField,
      MorganTianLib.extendVector_apply]
    congr 1
  have hM₀ :
      (∑ a, ∑ b, dG a b * ∑ c, ∑ d, ∑ j,
        multilinearComponent4 v A a c d j * multilinearComponent4 v A b c d j) =
        ∑ x, f₀ x := by
    calc
      (∑ a, ∑ b, dG a b * ∑ c, ∑ d, ∑ j,
          multilinearComponent4 v A a c d j *
            multilinearComponent4 v A b c d j) =
          ∑ a, ∑ b, ∑ c, ∑ d, ∑ j,
            (2 * Ric (e a) (e b)) * R (e a) (e c) (e d) (e j) *
              R (e b) (e c) (e d) (e j) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro j _
        simp only [dG, v, OrthonormalBasis.coe_toBasis, hA, Ric]
        ring
      _ = ∑ x, f₀ x := by
        rw [sum_fin_five f₀]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro j _
        simp only [f₀]
        congr 1
  have hM₁ :
      (∑ a, ∑ b, ∑ c, dG b c * ∑ d, ∑ j,
        multilinearComponent4 v A a b d j * multilinearComponent4 v A a c d j) =
        ∑ x, f₁ x := by
    calc
      (∑ a, ∑ b, ∑ c, dG b c * ∑ d, ∑ j,
          multilinearComponent4 v A a b d j *
            multilinearComponent4 v A a c d j) =
          ∑ a, ∑ b, ∑ c, ∑ d, ∑ j,
            (2 * Ric (e b) (e c)) * R (e a) (e b) (e d) (e j) *
              R (e a) (e c) (e d) (e j) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro j _
        simp only [dG, v, OrthonormalBasis.coe_toBasis, hA]
        ring
      _ = ∑ x, f₁ x := by
        rw [sum_fin_five f₁]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro j _
        simp only [f₁]
        congr 1
  have hM₂ :
      (∑ a, ∑ b, ∑ c, ∑ d, dG c d * ∑ j,
        multilinearComponent4 v A a b c j * multilinearComponent4 v A a b d j) =
        ∑ x, f₂ x := by
    calc
      (∑ a, ∑ b, ∑ c, ∑ d, dG c d * ∑ j,
          multilinearComponent4 v A a b c j *
            multilinearComponent4 v A a b d j) =
          ∑ a, ∑ b, ∑ c, ∑ d, ∑ j,
            (2 * Ric (e c) (e d)) * R (e a) (e b) (e c) (e j) *
              R (e a) (e b) (e d) (e j) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro j _
        simp only [dG, v, OrthonormalBasis.coe_toBasis, hA]
        ring
      _ = ∑ x, f₂ x := by
        rw [sum_fin_five f₂]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro j _
        simp only [f₂]
        congr 1
  have hM₃ :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ j, dG d j *
        multilinearComponent4 v A a b c d * multilinearComponent4 v A a b c j) =
        ∑ x, f₃ x := by
    calc
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ j, dG d j *
          multilinearComponent4 v A a b c d *
            multilinearComponent4 v A a b c j) =
          ∑ a, ∑ b, ∑ c, ∑ d, ∑ j,
            (2 * Ric (e d) (e j)) * R (e a) (e b) (e c) (e d) *
              R (e a) (e b) (e c) (e j) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro j _
        simp only [dG, v, OrthonormalBasis.coe_toBasis, hA, Ric]
      _ = ∑ x, f₃ x := by
        rw [sum_fin_five f₃]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro j _
        simp only [f₃]
        congr 1
  have hflat :
      (∑ x, f₀ x) + (∑ x, f₁ x) + (∑ x, f₂ x) + (∑ x, f₃ x) =
        4 * ∑ x, f₃ x := by
    simpa only [f₀, f₁, f₂, f₃, R, Ric, e] using
      (curvatureMetricFlatSlots_eq_four_last (I := I) g p)
  have hlast :
      (∑ x, f₃ x) =
        2 * tensorInnerAt g (riemannTensorField g)
          (contract₂Perm g starPermRic (riemannTensorField g)
            (riemannTensorField g)) p := by
    have htuple :
        (∑ x, f₃ x) =
          ∑ a, ∑ b, ∑ c, ∑ d, ∑ j,
            (2 * Ric (e d) (e j)) * R (e a) (e b) (e c) (e d) *
              R (e a) (e b) (e c) (e j) := by
      rw [sum_fin_five f₃]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro j _
      simp only [f₃]
      congr 1
    rw [htuple]
    simpa only [R, Ric, e] using
      (curvatureMetricLastSlot_eq_tensorInnerAt (I := I) g p)
  rw [hM₀, hM₁, hM₂, hM₃, hflat, hlast]
  ring

/-- **Math.** The complete fixed-frame product rule for `|Rm|²` is the named
intrinsic pairing used in the curvature-norm evolution estimate. -/
theorem basisTensorPairVariation_riemann_eq_namedPairing
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    let v := e.toBasis
    let A := pointwiseMultilinearMap
      (isPointwiseMultilinear_riemannTensorField g p)
    let dA := curvatureEvolutionComponentAt (I := I) g p
    basisTensorPairVariation 1
        (fun a b => 2 * ricciTensorAt g p (v a) (v b)) v 4 A dA A dA =
      2 * tensorInnerAt g (riemannTensorField g)
          (roughLaplacian g g.leviCivitaConnection (riemannTensorField g)) p
        + 2 * tensorInnerAt g (riemannTensorField g)
            (curvatureNormEvolutionCorrection g) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  let v := e.toBasis
  let A := pointwiseMultilinearMap
    (isPointwiseMultilinear_riemannTensorField g p)
  let dA := curvatureEvolutionComponentAt (I := I) g p
  let dG : Matrix (Fin (Module.finrank ℝ (TangentSpace I p)))
      (Fin (Module.finrank ℝ (TangentSpace I p))) ℝ := fun a b =>
    2 * ricciTensorAt g p (v a) (v b)
  let C := contract₂Perm g starPermRic (riemannTensorField g)
    (riemannTensorField g)
  change basisTensorPairVariation 1 dG v 4 A dA A dA =
    2 * tensorInnerAt g (riemannTensorField g)
        (roughLaplacian g g.leviCivitaConnection (riemannTensorField g)) p
      + 2 * tensorInnerAt g (riemannTensorField g)
          (curvatureNormEvolutionCorrection g) p
  rw [basisTensorPairVariation_one_four]
  have hmetric :
      (∑ a, ∑ b, dG a b * ∑ c, ∑ d, ∑ j,
          multilinearComponent4 v A a c d j * multilinearComponent4 v A b c d j)
        + (∑ a, ∑ b, ∑ c, dG b c * ∑ d, ∑ j,
          multilinearComponent4 v A a b d j * multilinearComponent4 v A a c d j)
        + (∑ a, ∑ b, ∑ c, ∑ d, dG c d * ∑ j,
          multilinearComponent4 v A a b c j * multilinearComponent4 v A a b d j)
        + (∑ a, ∑ b, ∑ c, ∑ d, ∑ j, dG d j *
          multilinearComponent4 v A a b c d * multilinearComponent4 v A a b c j) =
        8 * tensorInnerAt g (riemannTensorField g) C p := by
    simpa only [dG, C, A, e, v] using
      (curvatureMetricSlotVariation_eq_tensorInnerAt (I := I) g p)
  have hcomp :
      (∑ a, ∑ b, ∑ c, ∑ d,
          dA (basisTuple4 v a b c d) * multilinearComponent4 v A a b c d)
        + (∑ a, ∑ b, ∑ c, ∑ d,
          multilinearComponent4 v A a b c d * dA (basisTuple4 v a b c d)) =
        2 * tensorInnerAt g (riemannTensorField g)
          (fun Y q =>
            roughLaplacian g g.leviCivitaConnection (riemannTensorField g) Y q
              + curvatureEvolutionCorrection g Y q) p := by
    simpa only [dA, A, e, v] using
      (curvatureComponentVariation_eq_tensorInnerAt (I := I) g p)
  have hdecomp :
      8 * tensorInnerAt g (riemannTensorField g) C p
          + 2 * tensorInnerAt g (riemannTensorField g)
            (fun Y q =>
              roughLaplacian g g.leviCivitaConnection (riemannTensorField g) Y q
                + curvatureEvolutionCorrection g Y q) p =
        2 * tensorInnerAt g (riemannTensorField g)
            (roughLaplacian g g.leviCivitaConnection (riemannTensorField g)) p
          + 2 * tensorInnerAt g (riemannTensorField g)
              (curvatureNormEvolutionCorrection g) p := by
    have hadd (B D : CovTensorField I M 4) :
        tensorInnerAt g (riemannTensorField g) (fun Y q => B Y q + D Y q) p =
          tensorInnerAt g (riemannTensorField g) B p +
            tensorInnerAt g (riemannTensorField g) D p := by
      simp only [tensorInnerAt, mul_add, Finset.sum_add_distrib]
    have hscale (B : CovTensorField I M 4) (a : ℝ) :
        tensorInnerAt g (riemannTensorField g) (fun Y q => a * B Y q) p =
          a * tensorInnerAt g (riemannTensorField g) B p := by
      simp only [tensorInnerAt, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    change
      8 * tensorInnerAt g (riemannTensorField g) C p
          + 2 * tensorInnerAt g (riemannTensorField g)
            (fun Y q =>
              roughLaplacian g g.leviCivitaConnection (riemannTensorField g) Y q
                + curvatureEvolutionCorrection g Y q) p =
        2 * tensorInnerAt g (riemannTensorField g)
            (roughLaplacian g g.leviCivitaConnection (riemannTensorField g)) p
          + 2 * tensorInnerAt g (riemannTensorField g)
            (fun Y q => curvatureEvolutionCorrection g Y q + 4 * C Y q) p
    rw [hadd, hadd, hscale]
    ring
  conv_lhs => rw [add_assoc]
  rw [hmetric, hcomp]
  exact hdecomp

/-- **Math.** A Ricci-flow metric equation and the component curvature
evolution genuinely determine the derivative of `|Rm|^2`.  The displayed
derivative is the complete fixed-chart product rule: four inverse-Gram factors
vary by `2 g^{-1} Ric g^{-1}`, and both curvature factors vary by
`Delta Rm + Q(Rm)`.

The intrinsic named-pairing form is obtained below by freezing an orthonormal
basis and applying the algebraic contraction identity proved above. -/
theorem hasDerivWithinAt_riemannNormSq_chart_of_components
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {t : ℝ}
    (hflow : IsRicciFlowOn g J)
    (hcurv : HasCurvatureEvolutionComponentsOn g J)
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (alpha p : M)
    (hp : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet) :
    HasDerivWithinAt (fun s => riemannNormAt (g s) p ^ 2)
      (basisTensorPairVariation
        (Tensor.chartInvGramMatrix (I := I) (g t) alpha p)
        (ricciFlowChartInvGramVariation (I := I) (g t) alpha p)
        (Tensor.chartBasisFamily (I := I) alpha hp) 4
        (pointwiseMultilinearMap
          (isPointwiseMultilinear_riemannTensorField (g t) p))
        (curvatureEvolutionComponentAt (I := I) (g t) p)
        (pointwiseMultilinearMap
          (isPointwiseMultilinear_riemannTensorField (g t) p))
        (curvatureEvolutionComponentAt (I := I) (g t) p)) J t := by
  classical
  have hmetric := isMetricVariationOn_of_isRicciFlowOn hflow
  have hG (c b : Fin (Module.finrank ℝ E)) : HasDerivWithinAt
      (fun s => Tensor.chartInvGramMatrix (I := I) (g s) alpha p c b)
      (ricciFlowChartInvGramVariation (I := I) (g t) alpha p c b) J t := by
    simpa only [ricciFlowChartInvGramVariation] using
      (MorganTianLib.hasDerivWithinAt_chartInvGramMatrix_apply
        hmetric ht hJ alpha p hp c b)
  have hcomp (w : Fin 4 → TangentSpace I p) : HasDerivWithinAt
      (fun s => pointwiseValue (riemannTensorField (g s)) p w)
      (curvatureEvolutionComponentAt (I := I) (g t) p w) J t := by
    simpa only [pointwiseValue, curvatureEvolutionComponentAt] using
      (hcurv t ht (fun i => MorganTianLib.extendVector p (w i)) p)
  have hnorm := hasDerivWithinAt_normSqAt_chart
    (g := g) (A := fun s => riemannTensorField (g s))
    (fun s => isPointwiseMultilinear_riemannTensorField (g s) p) hp
    (ricciFlowChartInvGramVariation (I := I) (g t) alpha p)
    (curvatureEvolutionComponentAt (I := I) (g t) p) hG hcomp
  refine hnorm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    (by rw [riemannNormAt_sq, riemannCovTensorField_eq_riemannTensorField])
  change riemannNormAt (g s) p ^ 2 =
    normSqAt (g s) (riemannTensorField (g s)) p
  rw [riemannNormAt_sq, riemannCovTensorField_eq_riemannTensorField]

/-- **Math.** Freezing a `g(t)`-orthonormal basis makes the same derivative
intrinsic at the target time: every inverse-Gram factor is the identity and its
Ricci-flow derivative is `2 Ric`. -/
theorem hasDerivWithinAt_riemannNormSq_orthonormalBasis_of_components
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {t : ℝ}
    (hflow : IsRicciFlowOn g J)
    (hcurv : HasCurvatureEvolutionComponentsOn g J)
    (ht : t ∈ J) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(g t).toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    let v := e.toBasis
    HasDerivWithinAt (fun s => riemannNormAt (g s) p ^ 2)
      (basisTensorPairVariation 1
        (fun a b => 2 * ricciTensorAt (g t) p (v a) (v b)) v 4
        (pointwiseMultilinearMap
          (isPointwiseMultilinear_riemannTensorField (g t) p))
        (curvatureEvolutionComponentAt (I := I) (g t) p)
        (pointwiseMultilinearMap
          (isPointwiseMultilinear_riemannTensorField (g t) p))
        (curvatureEvolutionComponentAt (I := I) (g t) p)) J t := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  let v := e.toBasis
  let dMetric : Matrix (Fin (Module.finrank ℝ (TangentSpace I p)))
      (Fin (Module.finrank ℝ (TangentSpace I p))) ℝ :=
    fun a b => -2 * ricciTensorAt (g t) p (v a) (v b)
  let dInv : Matrix (Fin (Module.finrank ℝ (TangentSpace I p)))
      (Fin (Module.finrank ℝ (TangentSpace I p))) ℝ :=
    fun a b => 2 * ricciTensorAt (g t) p (v a) (v b)
  have hGramOne : metricGramMatrixInBasis (g t) v = 1 := by
    ext a b
    change (g t).metricInner p (e a) (e b) = _
    rw [Matrix.one_apply]
    exact orthonormal_iff_ite.mp e.orthonormal a b
  have hInvOne : metricInvGramMatrixInBasis (g t) v = 1 := by
    rw [metricInvGramMatrixInBasis, hGramOne, Ring.inverse_one]
  have hMetric (a b : Fin (Module.finrank ℝ (TangentSpace I p))) : HasDerivWithinAt
      (fun s => metricGramMatrixInBasis (g s) v a b) (dMetric a b) J t := by
    simpa only [metricGramMatrixInBasis, dMetric] using hflow t ht p (v a) (v b)
  have hInv (a b : Fin (Module.finrank ℝ (TangentSpace I p))) : HasDerivWithinAt
      (fun s => metricInvGramMatrixInBasis (g s) v a b) (dInv a b) J t := by
    have h := hasDerivWithinAt_metricInvGramMatrixInBasis v dMetric hMetric a b
    simpa only [hInvOne, one_mul, mul_one, dMetric, dInv, neg_mul, neg_neg] using h
  have hcomp (w : Fin 4 → TangentSpace I p) : HasDerivWithinAt
      (fun s => pointwiseValue (riemannTensorField (g s)) p w)
      (curvatureEvolutionComponentAt (I := I) (g t) p w) J t := by
    simpa only [pointwiseValue, curvatureEvolutionComponentAt] using
      (hcurv t ht (fun i => MorganTianLib.extendVector p (w i)) p)
  have hnorm := hasDerivWithinAt_normSqAt_basis
    (g := g) (A := fun s => riemannTensorField (g s)) v
    (fun s => isPointwiseMultilinear_riemannTensorField (g s) p) dInv
    (curvatureEvolutionComponentAt (I := I) (g t) p) hInv hcomp
  simp only [hInvOne] at hnorm
  refine hnorm.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    (by rw [riemannNormAt_sq, riemannCovTensorField_eq_riemannTensorField])
  change riemannNormAt (g s) p ^ 2 =
    normSqAt (g s) (riemannTensorField (g s)) p
  rw [riemannNormAt_sq, riemannCovTensorField_eq_riemannTensorField]

/-- **Math.** The Ricci-flow metric equation and component curvature evolution
give the intrinsic evolution formula for `|Rm|²`, with the full quadratic
correction accounting for both curvature evolution and all four inverse-metric
contractions. -/
theorem hasDerivWithinAt_riemannNormSq_namedPairing_of_components
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {t : ℝ}
    (hflow : IsRicciFlowOn g J)
    (hcurv : HasCurvatureEvolutionComponentsOn g J)
    (ht : t ∈ J) (p : M) :
    HasDerivWithinAt (fun s => riemannNormAt (g s) p ^ 2)
      (2 * tensorInnerAt (g t) (riemannCovTensorField (g t))
          (roughLaplacian (g t) (g t).leviCivitaConnection
            (riemannCovTensorField (g t))) p
        + 2 * tensorInnerAt (g t) (riemannCovTensorField (g t))
            (curvatureNormEvolutionCorrection (g t)) p) J t := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  have h := hasDerivWithinAt_riemannNormSq_orthonormalBasis_of_components
    hflow hcurv ht p
  dsimp only at h
  rw [basisTensorPairVariation_riemann_eq_namedPairing (I := I) (g t) p] at h
  simpa only [riemannCovTensorField_eq_riemannTensorField] using h

/-- **Math.** Hence the existing named-pairing antecedent in the uniform
curvature-norm estimate is genuinely produced by Ricci flow and the component
curvature evolution equation. -/
theorem hasCurvatureNormSqNamedPairingBoundOn_of_isRicciFlowOn_of_components
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J)
    (hcurv : HasCurvatureEvolutionComponentsOn g J)
    (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t) :
    HasCurvatureNormSqNamedPairingBoundOn g J := by
  intro t ht p
  have hderiv := hasDerivWithinAt_riemannNormSq_namedPairing_of_components
    hflow hcurv ht p
  rw [hderiv.derivWithin (hJ t ht)]

/-- **Math.** There is one dimension-only constant for the curvature-norm
evolution inequality of every Ricci flow whose component curvature evolution is
witnessed. -/
theorem exists_uniform_curvatureNormEvolution_const_of_components :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (g : ℝ → RiemannianMetric I M) (J : Set ℝ),
      IsRicciFlowOn g J →
      HasCurvatureEvolutionComponentsOn g J →
      (∀ t ∈ J, UniqueDiffWithinAt ℝ J t) →
      HasCurvatureNormEvolutionInequalityOn g c J := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_curvatureNormEvolution_const (I := I) (M := M)
  refine ⟨c, hc, fun g J hflow hcurv hJ => hbound g J ?_⟩
  exact hasCurvatureNormSqNamedPairingBoundOn_of_isRicciFlowOn_of_components
    hflow hcurv hJ

/-- **Math.** Substituting the derived component evolution records the
conditional compatibility theorem for a supplied Riemann first variation. The
Ricci-flow specialization below now supplies that variation unconditionally on
interior target sets. -/
theorem exists_uniform_curvatureNormEvolution_const_of_variation :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (g : ℝ → RiemannianMetric I M) (J : Set ℝ),
      IsRicciFlowOn g J →
      HasRiemannVariationOn g
        (fun t p (x y : TangentSpace I p) =>
          -2 * ricciTensorAt (g t) p x y) J →
      (∀ t ∈ J, UniqueDiffWithinAt ℝ J t) →
      HasCurvatureNormEvolutionInequalityOn g c J := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_curvatureNormEvolution_const_of_components
      (I := I) (M := M)
  refine ⟨c, hc, fun g J hflow hvar hJ => hbound g J hflow ?_ hJ⟩
  exact hasCurvatureEvolutionComponentsOn_of_variation hvar

/-- **Math.** A Morgan--Tian Ricci flow on `J` supplies Topping's metric
evolution equation on every smaller time set `K ⊆ J`. Restricting the within
derivative is essential when `K` has endpoints. -/
theorem isRicciFlowOn_of_morganTian_isRicciFlowOn_of_subset
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) (hK : K ⊆ J) :
    Topping.IsRicciFlowOn g K := by
  intro t ht p x y
  simpa only [mtRicciTensorAt_eq_ricciTensorAt] using
    (hflow.equation t (hK ht) p x y).mono hK

/-- **Math.** There is a dimension-only curvature-norm evolution constant for
every genuine Ricci flow, on every target time set contained in the interior
of its ambient flow domain. All named analytic antecedents are produced here. -/
theorem exists_uniform_curvatureNormEvolution_const_of_morganTian_isRicciFlowOn :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (g : ℝ → RiemannianMetric I M) (J K : Set ℝ),
        MorganTianLib.IsRicciFlowOn g J →
        K ⊆ interior J →
        (∀ t ∈ K, UniqueDiffWithinAt ℝ K t) →
        HasCurvatureNormEvolutionInequalityOn g c K := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_curvatureNormEvolution_const_of_components
      (I := I) (M := M)
  refine ⟨c, hc, fun g J K hflow hK hunique => ?_⟩
  exact hbound g K
    (isRicciFlowOn_of_morganTian_isRicciFlowOn_of_subset hflow
      (fun t ht => interior_subset (hK ht)))
    (hasCurvatureEvolutionComponentsOn_of_isRicciFlowOn_of_subset_interior
      hflow hK)
    hunique

/-- **Math.** There is the same dimension-only curvature-norm evolution
constant on every target set `K ⊆ J`; the full-set Riemann producer removes the
old interior-buffer requirement. -/
theorem exists_uniform_curvatureNormEvolution_const_of_morganTian_isRicciFlowOn_of_subset :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (g : ℝ → RiemannianMetric I M) (J K : Set ℝ),
        MorganTianLib.IsRicciFlowOn g J →
        K ⊆ J →
        (∀ t ∈ K, UniqueDiffWithinAt ℝ K t) →
        HasCurvatureNormEvolutionInequalityOn g c K := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_curvatureNormEvolution_const_of_components
      (I := I) (M := M)
  refine ⟨c, hc, fun g J K hflow hK hunique => ?_⟩
  exact hbound g K
    (isRicciFlowOn_of_morganTian_isRicciFlowOn_of_subset hflow hK)
    (hasCurvatureEvolutionComponentsOn_of_isRicciFlowOn_of_subset hflow hK)
    hunique

/-- **Math.** The component curvature evolution also feeds the final uniform
curvature bound.  The denominator condition is retained: it is the genuine
lifespan restriction of the comparison ODE. -/
theorem exists_uniform_riemannNormAt_le_of_components [CompactSpace M] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (g : ℝ → RiemannianMetric I M) (m T : ℝ),
      0 ≤ T → 0 < m →
      ContinuousOn (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
        ((Set.univ : Set M) ×ˢ Icc 0 T) →
      IsRicciFlowOn g (Icc 0 T) →
      HasCurvatureEvolutionComponentsOn g (Icc 0 T) →
      (∀ t ∈ Icc 0 T, UniqueDiffWithinAt ℝ (Icc 0 T) t) →
      (∀ t ∈ Icc 0 T, 0 < 1 - c * m * t / 2) →
      (∀ p, riemannNormAt (g 0) p ≤ m) →
      ∀ p t, t ∈ Icc 0 T →
        riemannNormAt (g t) p ≤ m / (1 - c * m * t / 2) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_riemannNormAt_le_of_ingredients (I := I) (M := M)
  refine ⟨c, hc, fun g m T hT hm hcont hflow hcurv hJ hdenom hzero => ?_⟩
  refine hbound g m T hT hm hcont ?_ ?_ hdenom hzero
  · intro p t ht
    have hderiv := hasDerivWithinAt_riemannNormSq_namedPairing_of_components
      hflow hcurv ht p
    simpa only [hderiv.derivWithin (hJ t ht)] using hderiv
  · exact hasCurvatureNormSqNamedPairingBoundOn_of_isRicciFlowOn_of_components
      hflow hcurv hJ

/-- **Math.** The final uniform curvature bound is unconditional for a genuine
Ricci flow defined on an ambient interval whose interior contains `[0,T]`.
The denominator hypothesis is retained verbatim: without it the printed
comparison expression need not be a valid upper bound. -/
theorem exists_uniform_riemannNormAt_le_of_morganTian_isRicciFlowOn
    [CompactSpace M] :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (g : ℝ → RiemannianMetric I M) (J : Set ℝ) (m T : ℝ),
        0 ≤ T → 0 < m →
        ContinuousOn (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
          ((Set.univ : Set M) ×ˢ Icc 0 T) →
        MorganTianLib.IsRicciFlowOn g J →
        Icc 0 T ⊆ interior J →
        (∀ t ∈ Icc 0 T, UniqueDiffWithinAt ℝ (Icc 0 T) t) →
        (∀ t ∈ Icc 0 T, 0 < 1 - c * m * t / 2) →
        (∀ p, riemannNormAt (g 0) p ≤ m) →
        ∀ p t, t ∈ Icc 0 T →
          riemannNormAt (g t) p ≤ m / (1 - c * m * t / 2) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_riemannNormAt_le_of_components (I := I) (M := M)
  refine ⟨c, hc, fun g J m T hT hm hcont hflow hIcc hunique hdenom hzero => ?_⟩
  exact hbound g m T hT hm hcont
    (isRicciFlowOn_of_morganTian_isRicciFlowOn_of_subset hflow
      (fun t ht => interior_subset (hIcc ht)))
    (hasCurvatureEvolutionComponentsOn_of_isRicciFlowOn_of_subset_interior
      hflow hIcc)
    hunique hdenom hzero

/-- **Math.** The final uniform curvature bound only needs the ambient flow to
contain `[0,T]`; the required positive denominator hypothesis is unchanged. -/
theorem exists_uniform_riemannNormAt_le_of_morganTian_isRicciFlowOn_of_subset
    [CompactSpace M] :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (g : ℝ → RiemannianMetric I M) (J : Set ℝ) (m T : ℝ),
        0 ≤ T → 0 < m →
        ContinuousOn (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
          ((Set.univ : Set M) ×ˢ Icc 0 T) →
        MorganTianLib.IsRicciFlowOn g J →
        Icc 0 T ⊆ J →
        (∀ t ∈ Icc 0 T, UniqueDiffWithinAt ℝ (Icc 0 T) t) →
        (∀ t ∈ Icc 0 T, 0 < 1 - c * m * t / 2) →
        (∀ p, riemannNormAt (g 0) p ≤ m) →
        ∀ p t, t ∈ Icc 0 T →
          riemannNormAt (g t) p ≤ m / (1 - c * m * t / 2) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_riemannNormAt_le_of_components (I := I) (M := M)
  refine ⟨c, hc, fun g J m T hT hm hcont hflow hIcc hunique hdenom hzero => ?_⟩
  exact hbound g m T hT hm hcont
    (isRicciFlowOn_of_morganTian_isRicciFlowOn_of_subset hflow hIcc)
    (hasCurvatureEvolutionComponentsOn_of_isRicciFlowOn_of_subset hflow hIcc)
    hunique hdenom hzero

#print axioms Topping.curvatureComponentVariation_eq_tensorInnerAt
#print axioms Topping.curvatureMetricLastSlot_eq_tensorInnerAt
#print axioms Topping.curvatureMetricSlotVariation_eq_tensorInnerAt
#print axioms Topping.basisTensorPairVariation_riemann_eq_namedPairing
#print axioms Topping.hasDerivWithinAt_riemannNormSq_chart_of_components
#print axioms Topping.hasDerivWithinAt_riemannNormSq_orthonormalBasis_of_components
#print axioms Topping.hasDerivWithinAt_riemannNormSq_namedPairing_of_components
#print axioms Topping.hasCurvatureNormSqNamedPairingBoundOn_of_isRicciFlowOn_of_components
#print axioms Topping.exists_uniform_curvatureNormEvolution_const_of_components
#print axioms Topping.exists_uniform_curvatureNormEvolution_const_of_variation
#print axioms Topping.exists_uniform_riemannNormAt_le_of_components
#print axioms Topping.isRicciFlowOn_of_morganTian_isRicciFlowOn_of_subset
#print axioms Topping.exists_uniform_curvatureNormEvolution_const_of_morganTian_isRicciFlowOn
#print axioms Topping.exists_uniform_curvatureNormEvolution_const_of_morganTian_isRicciFlowOn_of_subset
#print axioms Topping.exists_uniform_riemannNormAt_le_of_morganTian_isRicciFlowOn
#print axioms Topping.exists_uniform_riemannNormAt_le_of_morganTian_isRicciFlowOn_of_subset

end Topping

end
