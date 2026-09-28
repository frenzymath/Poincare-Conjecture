import MorganTianLib.Ch04.TensorParallelTransport
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Full contractions of covariant tensors

The full component pairing of two real covariant tensors is independent of
the orthonormal basis used to compute it and is preserved by isometric
transport. This is the algebraic input for the metric tensor inner product.

The rank induction follows the slot-contraction argument in the workspace's
`Topping/Riemannian/TensorNormChart.lean`, using the bilinear trace invariance
already available through the geometric imports. No tensor inner-product
instance is imposed on the existing multilinear operator norm.
-/

noncomputable section

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Math.** The full component pairing of two covariant tensors in an orthonormal basis. -/
def covariantTensorComponentInner {k : ℕ} (b : OrthonormalBasis ι ℝ V)
    (A B : CovariantTensorFiber k V) : ℝ :=
  ∑ a : Fin k → ι, A (fun j => b (a j)) * B (fun j => b (a j))

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
private theorem sum_tensor_tuple_cons {k : ℕ}
    (F K : (Fin (k + 1) → V) → ℝ) (c : ι → V) :
    (∑ q : Fin (k + 1) → ι, F (fun j => c (q j)) * K (fun j => c (q j))) =
      ∑ i : ι, ∑ w : Fin k → ι,
        F (Fin.cons (c i) (fun j => c (w j))) *
          K (Fin.cons (c i) (fun j => c (w j))) := by
  rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => ι)).symm _
    (fun q : ι × (Fin k → ι) =>
      F (Fin.cons (c q.1) (fun j => c (q.2 j))) *
        K (Fin.cons (c q.1) (fun j => c (q.2 j)))) (fun q => by
      simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk]
      have harg : (fun j => c (q j)) =
          Fin.cons (c (q 0)) (fun j => c (Fin.tail q j)) := by
        funext j
        refine Fin.cases ?_ ?_ j <;> simp [Fin.tail]
      rw [harg]), Fintype.sum_prod_type]

/-- **Math.** Contracting all but the first slot leaves a bilinear form in the first slots. -/
private def tensorFirstSlotPair {k : ℕ} (b : OrthonormalBasis ι ℝ V)
    (A B : CovariantTensorFiber (k + 1) V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y => ∑ w : Fin k → ι,
      A (Fin.cons x (fun j => b (w j))) * B (Fin.cons y (fun j => b (w j))))
    (fun x y z => by
      simp only [ContinuousMultilinearMap.cons_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [ContinuousMultilinearMap.cons_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring)
    (fun x y z => by
      simp only [ContinuousMultilinearMap.cons_add, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [ContinuousMultilinearMap.cons_smul, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring)

/-- **Math.** The component pairing may be evaluated by contracting the first slot last. -/
theorem covariantTensorComponentInner_succ {k : ℕ} (b : OrthonormalBasis ι ℝ V)
    (A B : CovariantTensorFiber (k + 1) V) :
    covariantTensorComponentInner b A B =
      ∑ i, covariantTensorComponentInner b (A.curryLeft (b i)) (B.curryLeft (b i)) := by
  simpa only [covariantTensorComponentInner, ContinuousMultilinearMap.curryLeft_apply] using
    sum_tensor_tuple_cons (fun q => A q) (fun q => B q) (fun i => b i)

/-- **Math.** The full pairing of covariant tensors does not depend on the orthonormal basis,
including the choice of finite index type. -/
theorem covariantTensorComponentInner_basis_independent
    (b : OrthonormalBasis ι ℝ V) (c : OrthonormalBasis κ ℝ V)
    {k : ℕ} (A B : CovariantTensorFiber k V) :
    covariantTensorComponentInner b A B = covariantTensorComponentInner c A B := by
  induction k with
  | zero =>
      simp only [covariantTensorComponentInner, Finset.univ_unique, Finset.sum_singleton]
      congr 2 <;> funext i <;> exact i.elim0
  | succ k ih =>
      rw [covariantTensorComponentInner_succ]
      calc
        (∑ i, covariantTensorComponentInner b (A.curryLeft (b i)) (B.curryLeft (b i))) =
            ∑ i, covariantTensorComponentInner c (A.curryLeft (b i)) (B.curryLeft (b i)) :=
          Finset.sum_congr rfl fun i _ => ih (A.curryLeft (b i)) (B.curryLeft (b i))
        _ = ∑ i, covariantTensorComponentInner c (A.curryLeft (c i)) (B.curryLeft (c i)) := by
          exact b.sum_apply_diagonal_invariant c (tensorFirstSlotPair c A B)
        _ = covariantTensorComponentInner c A B :=
          (covariantTensorComponentInner_succ c A B).symm

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **Math.** Isometric transport preserves the component pairing in the transported basis. -/
@[simp] theorem covariantTensorComponentInner_transport_map {k : ℕ}
    (b : OrthonormalBasis ι ℝ V) (e : V ≃ₗᵢ[ℝ] W)
    (A B : CovariantTensorFiber k V) :
    covariantTensorComponentInner (b.map e)
        (covariantTensorTransportEquiv k e A) (covariantTensorTransportEquiv k e B) =
      covariantTensorComponentInner b A B := by
  simp [covariantTensorComponentInner, OrthonormalBasis.map_apply]

/-- **Math.** Isometric transport preserves the full tensor pairing in any orthonormal bases
of the source and target spaces. -/
theorem covariantTensorComponentInner_transport {k : ℕ}
    (b : OrthonormalBasis ι ℝ V) (c : OrthonormalBasis κ ℝ W)
    (e : V ≃ₗᵢ[ℝ] W) (A B : CovariantTensorFiber k V) :
    covariantTensorComponentInner c
        (covariantTensorTransportEquiv k e A) (covariantTensorTransportEquiv k e B) =
      covariantTensorComponentInner b A B := by
  rw [covariantTensorComponentInner_basis_independent c (b.map e)]
  exact covariantTensorComponentInner_transport_map b e A B

end MorganTianLib
