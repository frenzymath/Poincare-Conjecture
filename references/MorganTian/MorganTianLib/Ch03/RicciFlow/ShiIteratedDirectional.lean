import MorganTianLib.Ch03.RicciFlow.ShiGeometricLevels

/-!
# Morgan--Tian Ch. 3 -- iterated directional curvature levels

The covariant-derivative tower inserts derivative directions in its leading
slots.  This file records the corresponding finite directional expansion at
arbitrary order.  It is a static tensor identity: no Ricci-flow or evolution
hypothesis is used.
-/

open scoped ContDiff Manifold Topology Bundle BigOperators
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/-! ## Directional contractions -/

/-- **Math.** The directional contraction of an iterated covariant derivative.

The derivative slots of `iteratedCovTensorDeriv` are the leading slots.  This
definition contracts those slots against the prescribed ordered list and
leaves the original tensor slots free.  Defining the operation by contraction
is important: repeatedly applying `covTensorDerivAlong` would omit the
connection corrections for already-fixed direction fields. -/
def iteratedCovTensorDerivAlong (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k) :
    (n : ℕ) → (Fin n → SmoothVectorField I M) → CovTensorField I M k
  | n, dirs => fun Y p =>
      iteratedCovTensorDeriv nabla A n
        (fun j => Fin.append dirs Y (Fin.cast (Nat.add_comm k n) j)) p

@[simp] theorem iteratedCovTensorDerivAlong_zero
    (nabla : AffineConnection I M) {k : ℕ}
    (A : CovTensorField I M k) (dirs : Fin 0 → SmoothVectorField I M) :
    iteratedCovTensorDerivAlong nabla A 0 dirs = A := by
  funext Y p
  change iteratedCovTensorDeriv nabla A 0
      (fun j => Fin.append dirs Y (Fin.cast (Nat.add_comm k 0) j)) p = A Y p
  have hdirs : dirs = Fin.elim0 := Subsingleton.elim _ _
  subst hdirs
  simp only [iteratedCovTensorDeriv_zero]
  congr 1
  funext j
  let h : k + 0 = 0 + k := Nat.add_comm k 0
  change Fin.addCases Fin.elim0 Y (Fin.cast h j) = Y j
  have hadd (z : Fin (0 + k)) : Fin.addCases (m := 0) (n := k)
      (Fin.elim0 : Fin 0 → SmoothVectorField I M) Y z =
        Y (Fin.cast (Nat.zero_add k) z) := by
    refine Fin.addCases ?_ ?_ z
    · intro i
      exact i.elim0
    · intro i
      rw [Fin.addCases_right]
      congr 1
      apply Fin.ext
      simp [Fin.cast, Fin.natAdd]
  rw [hadd]
  congr 1

theorem iteratedCovTensorDerivAlong_apply
    (nabla : AffineConnection I M) {k n : ℕ}
    (A : CovTensorField I M k)
    (dirs : Fin (n + 1) → SmoothVectorField I M) :
    iteratedCovTensorDerivAlong nabla A (n + 1) dirs =
      fun Y p => iteratedCovTensorDeriv nabla A (n + 1)
        (fun j => Fin.append dirs Y
          (Fin.cast (Nat.add_comm k (n + 1)) j)) p := rfl

/-! ## Pointwise norm expansion -/

section Pointwise

variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

private def appendIndex (k n d : ℕ) :
    (Fin n → Fin d) × (Fin k → Fin d) → (Fin (k + n) → Fin d) :=
  fun q => (Fin.append q.1 q.2) ∘ Fin.cast (Nat.add_comm k n)

private def splitIndex (k n d : ℕ) :
    (Fin (k + n) → Fin d) → (Fin n → Fin d) × (Fin k → Fin d) :=
  fun f =>
    ((fun i => f (Fin.cast (Nat.add_comm n k) (Fin.castAdd k i))),
      (fun j => f (Fin.cast (Nat.add_comm n k) (Fin.natAdd n j))))

private theorem appendIndex_left (k n d : ℕ)
    (q : (Fin n → Fin d) × (Fin k → Fin d)) :
    splitIndex k n d (appendIndex k n d q) = q := by
  rcases q with ⟨u, v⟩
  apply Prod.ext
  · funext i
    simp [splitIndex, appendIndex]
  · funext j
    simp [splitIndex, appendIndex]

private theorem appendIndex_right (k n d : ℕ)
    (f : Fin (k + n) → Fin d) :
    appendIndex k n d (splitIndex k n d f) = f := by
  funext j
  let hkn : k + n = n + k := Nat.add_comm k n
  let f' : Fin (n + k) → Fin d := f ∘ Fin.cast hkn.symm
  have h := Fin.append_castAdd_natAdd (f := f')
  change (Fin.append (fun i => f' (Fin.castAdd k i))
      (fun i => f' (Fin.natAdd n i))) (Fin.cast hkn j) = f j
  rw [h]
  rfl

private def appendIndexEquiv (k n d : ℕ) :
    (Fin n → Fin d) × (Fin k → Fin d) ≃ (Fin (k + n) → Fin d) :=
  { toFun := appendIndex k n d
    invFun := splitIndex k n d
    left_inv := appendIndex_left k n d
    right_inv := appendIndex_right k n d }

private theorem sum_pi_append (k n d : ℕ)
    (f : (Fin (k + n) → Fin d) → ℝ) :
    ∑ s : Fin (k + n) → Fin d, f s =
      ∑ dirs : Fin n → Fin d, ∑ base : Fin k → Fin d,
        f (appendIndex k n d (dirs, base)) := by
  calc
    ∑ s : Fin (k + n) → Fin d, f s =
        ∑ q : (Fin n → Fin d) × (Fin k → Fin d),
          f (appendIndex k n d q) := by
      exact Fintype.sum_equiv (appendIndexEquiv k n d).symm
        (fun s => f s)
        (fun q : (Fin n → Fin d) × (Fin k → Fin d) =>
          f (appendIndex k n d q))
        (fun s => congrArg f (appendIndex_right k n d s).symm)
    _ = ∑ dirs : Fin n → Fin d, ∑ base : Fin k → Fin d,
        f (appendIndex k n d (dirs, base)) := by
      rw [Fintype.sum_prod_type]

/-- **Math.** At arbitrary order, the squared norm of an iterated covariant
derivative is the finite sum of the squared norms of all ordered orthonormal
directional derivatives. -/
theorem covTensorNormSqAt_iteratedCovTensorDerivAlong_eq_sum
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k n : ℕ} (A : CovTensorField I M k) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    covTensorNormSqAt g (iteratedCovTensorDeriv nabla A n) p =
      ∑ dirs : Fin n → Fin (Module.finrank ℝ (TangentSpace I p)),
        covTensorNormSqAt g
          (iteratedCovTensorDerivAlong nabla A n
            (fun i => extendVector p
              (stdOrthonormalBasis ℝ (TangentSpace I p) (dirs i)))) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold covTensorNormSqAt covTensorComponentAt
  rw [sum_pi_append k n (Module.finrank ℝ (TangentSpace I p))]
  refine Finset.sum_congr rfl (fun dirs _ => ?_)
  refine Finset.sum_congr rfl (fun base _ => ?_)
  have hargs :
      (fun i : Fin (k + n) =>
        extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p)
            (appendIndex k n (Module.finrank ℝ (TangentSpace I p))
              (dirs, base) i))) =
      (fun j : Fin (k + n) =>
        Fin.append
          (fun i : Fin n =>
            extendVector p
              (stdOrthonormalBasis ℝ (TangentSpace I p) (dirs i)))
          (fun i : Fin k =>
            extendVector p
              (stdOrthonormalBasis ℝ (TangentSpace I p) (base i)))
          (Fin.cast (Nat.add_comm k n) j)) := by
    funext i
    unfold appendIndex
    let h : k + n = n + k := Nat.add_comm k n
    change extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p)
          (Fin.append dirs base (Fin.cast h i))) =
      (Fin.append
          (fun i : Fin n =>
            extendVector p
              (stdOrthonormalBasis ℝ (TangentSpace I p) (dirs i)))
          (fun i : Fin k =>
            extendVector p
              (stdOrthonormalBasis ℝ (TangentSpace I p) (base i)))
        (Fin.cast h i))
    refine Fin.addCases ?_ ?_ (Fin.cast h i)
    · intro j
      simp
    · intro j
      simp
  simp only [iteratedCovTensorDerivAlong]
  rw [hargs]

end Pointwise

end MorganTianLib

end

#print axioms MorganTianLib.iteratedCovTensorDerivAlong_zero
#print axioms MorganTianLib.iteratedCovTensorDerivAlong_apply
#print axioms MorganTianLib.covTensorNormSqAt_iteratedCovTensorDerivAlong_eq_sum
