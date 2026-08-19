import MorganTianLib.Ch01.InvGramTrace
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Normed
import Topping.Riemannian.FrameTrace

/-!
# Tensor norms in a fixed chart basis

The pointwise tensor norm is defined using an orthonormal basis.  For time
variation, that basis moves with the metric and is therefore unsuitable for
termwise differentiation.  This file rewrites the metric pairing of two
covariant tensors in an arbitrary fixed basis, with one inverse-Gram factor in
each tensor slot.  The chart specialization is the algebraic bridge needed to
differentiate `|Rm|^2` using fixed coordinate components.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace Matrix.Norms.Operator
open Riemannian

noncomputable section

namespace Topping

/-! ### Metric Gram matrices in a fixed basis -/

/-- **Math.** The Gram matrix of an arbitrary basis for a Riemannian metric at
one point.  Unlike `Tensor.chartGramMatrix`, the basis need not arise from a
chart. -/
def metricGramMatrixInBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : RiemannianMetric I M) {p : M} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Module.Basis ι ℝ (TangentSpace I p)) : Matrix ι ι ℝ :=
  fun a b => g.metricInner p (v a) (v b)

/-- **Math.** The inverse of the fixed-basis metric Gram matrix. -/
def metricInvGramMatrixInBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : RiemannianMetric I M) {p : M} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Module.Basis ι ℝ (TangentSpace I p)) : Matrix ι ι ℝ :=
  Ring.inverse (metricGramMatrixInBasis g v)

/-- **Math.** The derivative of inversion for a curve of finite real matrices,
`(G⁻¹)' = -G⁻¹ G' G⁻¹`. -/
theorem hasDerivWithinAt_matrixInverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : ℝ → Matrix ι ι ℝ} {G' : Matrix ι ι ℝ}
    {J : Set ℝ} {t : ℝ}
    (hG : HasDerivWithinAt G G' J t) (hu : IsUnit (G t)) :
    HasDerivWithinAt (fun s => Ring.inverse (G s))
      (-(Ring.inverse (G t) * G' * Ring.inverse (G t))) J t := by
  have hspec : (hu.unit : Matrix ι ι ℝ) = G t := hu.unit_spec
  have hinvu : Ring.inverse (G t) =
      ((hu.unit⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ) := by
    have h' := Ring.inverse_unit hu.unit
    rwa [hspec] at h'
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix ι ι ℝ))
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℝ)
          ((hu.unit⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ)
          ((hu.unit⁻¹ : (Matrix ι ι ℝ)ˣ) : Matrix ι ι ℝ))) (G t) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
    rwa [hspec] at this
  have h := hF.comp_hasDerivWithinAt t hG
  simpa [Function.comp_def, hinvu, ContinuousLinearMap.mulLeftRight_apply,
    mul_assoc] using h

/-! ### Full contractions in an arbitrary basis -/

/-- **Math.** The full metric pairing of two covariant `n`-tensors, written
recursively in a basis `v` with inverse Gram matrix `Ginv`.  Each recursive
step contracts the first remaining slot and contributes one factor
`Ginv a b`. -/
def basisTensorPair
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {ι : Type*} [Fintype ι]
    (Ginv : Matrix ι ι ℝ) (v : Module.Basis ι ℝ V) :
    (n : ℕ) → MultilinearMap ℝ (fun _ : Fin n => V) ℝ →
      MultilinearMap ℝ (fun _ : Fin n => V) ℝ → ℝ
  | 0, A, B => A (fun i => i.elim0) * B (fun i => i.elim0)
  | n + 1, A, B => ∑ a, ∑ b, Ginv a b *
      basisTensorPair Ginv v n (A.curryLeft (v a)) (B.curryLeft (v b))

/-- **Math.** The corresponding pairing computed in an orthonormal basis. -/
private def orthonormalTensorPair
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ V) (n : ℕ)
    (A B : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) : ℝ :=
  ∑ q : Fin n → ι, A (fun j => e (q j)) * B (fun j => e (q j))

/-- **Math.** Peeling the first coordinate of a simultaneous tensor-component pairing. -/
private theorem sum_tuple_peel_mul {V : Type*} {μ : Type*} [Fintype μ] {k : ℕ}
    (F K : (Fin (k + 1) → V) → ℝ) (c : μ → V) :
    (∑ q : Fin (k + 1) → μ, F (fun j => c (q j)) * K (fun j => c (q j))) =
      ∑ i : μ, ∑ w : Fin k → μ,
        F (Fin.cons (c i) (fun j => c (w j))) *
          K (Fin.cons (c i) (fun j => c (w j))) := by
  rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => μ)).symm _
    (fun q : μ × (Fin k → μ) =>
      F (Fin.cons (c q.1) (fun j => c (q.2 j))) *
        K (Fin.cons (c q.1) (fun j => c (q.2 j)))) (fun q => by
      simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk]
      have harg : (fun j => c (q j)) =
          Fin.cons (c (q 0)) (fun j => c (Fin.tail q j)) := by
        funext j
        refine Fin.cases ?_ ?_ j <;> simp [Fin.tail]
      rw [harg]), Fintype.sum_prod_type]

/-- **Math.** The pairing of the two first slots after all tail slots are contracted in
an orthonormal basis. -/
private def firstSlotPair
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] {k : ℕ}
    (e : OrthonormalBasis ι ℝ V)
    (A B : MultilinearMap ℝ (fun _ : Fin (k + 1) => V) ℝ) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y => ∑ w : Fin k → ι,
      A (Fin.cons x (fun j => e (w j))) *
        B (Fin.cons y (fun j => e (w j))))
    (fun x y z => by
      simp only [MultilinearMap.cons_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [MultilinearMap.cons_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring)
    (fun x y z => by
      simp only [MultilinearMap.cons_add, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [MultilinearMap.cons_smul, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring)

@[simp] private theorem firstSlotPair_apply
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] {k : ℕ}
    (e : OrthonormalBasis ι ℝ V)
    (A B : MultilinearMap ℝ (fun _ : Fin (k + 1) => V) ℝ)
    (x y : V) :
    firstSlotPair e A B x y = ∑ w : Fin k → ι,
      A (Fin.cons x (fun j => e (w j))) *
        B (Fin.cons y (fun j => e (w j))) := rfl

/-- **Math.** A full tensor pairing computed in an orthonormal basis equals
the inverse-Gram contraction in any basis.  This is the iterated version of
`sum_orthonormalBasis_diagonal_eq_invGram`. -/
theorem orthonormalTensorPair_eq_basisTensorPair
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ V) (v : Module.Basis ι ℝ V)
    {G Ginv : Matrix ι ι ℝ}
    (hG : ∀ a b, G a b = inner ℝ (v a) (v b))
    (hGinv : G * Ginv = 1) :
    ∀ (n : ℕ) (A B : MultilinearMap ℝ (fun _ : Fin n => V) ℝ),
      orthonormalTensorPair e n A B = basisTensorPair Ginv v n A B := by
  intro n
  induction n with
  | zero =>
      intro A B
      simp only [orthonormalTensorPair, basisTensorPair,
        Finset.univ_unique, Finset.sum_singleton]
      congr 2 <;> funext i <;> exact i.elim0
  | succ n ih =>
      intro A B
      rw [orthonormalTensorPair, sum_tuple_peel_mul
        (fun q => A q) (fun q => B q) (fun i => e i)]
      change (∑ i, firstSlotPair e A B (e i) (e i)) = _
      rw [MorganTianLib.sum_orthonormalBasis_diagonal_eq_invGram
        e v (firstSlotPair e A B) hG hGinv]
      simp only [basisTensorPair, firstSlotPair_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      simpa only [orthonormalTensorPair, MultilinearMap.curryLeft_apply] using
        congrArg (fun x : ℝ => Ginv a b * x)
          (ih (A.curryLeft (v a)) (B.curryLeft (v b)))

/-! ### Differentiating a fixed-basis contraction -/

/-- **Math.** The product-rule variation of `basisTensorPair`.  The matrix
variation contributes once in the first remaining slot; the recursive term
contains the variations of all later inverse-Gram factors and of the two tensor
components. -/
def basisTensorPairVariation
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {ι : Type*} [Fintype ι]
    (G dG : Matrix ι ι ℝ) (v : Module.Basis ι ℝ V) :
    (n : ℕ) → MultilinearMap ℝ (fun _ : Fin n => V) ℝ →
      ((Fin n → V) → ℝ) → MultilinearMap ℝ (fun _ : Fin n => V) ℝ →
      ((Fin n → V) → ℝ) → ℝ
  | 0, A, dA, B, dB =>
      dA (fun i => i.elim0) * B (fun i => i.elim0)
        + A (fun i => i.elim0) * dB (fun i => i.elim0)
  | n + 1, A, dA, B, dB =>
      ∑ a, ∑ b, (
        dG a b * basisTensorPair G v n
            (A.curryLeft (v a)) (B.curryLeft (v b))
          + G a b * basisTensorPairVariation G dG v n
              (A.curryLeft (v a)) (fun w => dA (Fin.cons (v a) w))
              (B.curryLeft (v b)) (fun w => dB (Fin.cons (v b) w)))

/-- **Math.** The rank-four tuple formed by four vectors from a basis. -/
def basisTuple4
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {ι : Type*} [Fintype ι]
    (v : Module.Basis ι ℝ V) (a b c d : ι) : Fin 4 → V :=
  Fin.cons (v a) (Fin.cons (v b) (Fin.cons (v c) (Fin.cons (v d) fun i => i.elim0)))

/-- **Math.** The component of a rank-four multilinear map in four vectors from a basis. -/
def multilinearComponent4
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {ι : Type*} [Fintype ι]
    (v : Module.Basis ι ℝ V)
    (A : MultilinearMap ℝ (fun _ : Fin 4 => V) ℝ)
    (a b c d : ι) : ℝ :=
  A (basisTuple4 v a b c d)

/-- **Math.** At an orthonormal target basis, the rank-four contraction product
rule is the sum of the four inverse-metric slot variations and twice the pairing
against the tensor-component variation. -/
theorem basisTensorPairVariation_one_four
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Module.Basis ι ℝ V) (dG : Matrix ι ι ℝ)
    (A : MultilinearMap ℝ (fun _ : Fin 4 => V) ℝ)
    (dA : (Fin 4 → V) → ℝ) :
    basisTensorPairVariation (1 : Matrix ι ι ℝ) dG v 4 A dA A dA =
      (∑ a, ∑ b, dG a b * ∑ c, ∑ d, ∑ e,
        multilinearComponent4 v A a c d e * multilinearComponent4 v A b c d e)
      + (∑ a, ∑ b, ∑ c, dG b c * ∑ d, ∑ e,
        multilinearComponent4 v A a b d e * multilinearComponent4 v A a c d e)
      + (∑ a, ∑ b, ∑ c, ∑ d, dG c d * ∑ e,
        multilinearComponent4 v A a b c e * multilinearComponent4 v A a b d e)
      + (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, dG d e *
        multilinearComponent4 v A a b c d * multilinearComponent4 v A a b c e)
      + (∑ a, ∑ b, ∑ c, ∑ d,
        dA (basisTuple4 v a b c d) * multilinearComponent4 v A a b c d)
      + (∑ a, ∑ b, ∑ c, ∑ d,
        multilinearComponent4 v A a b c d * dA (basisTuple4 v a b c d)) := by
  classical
  simp only [basisTensorPairVariation, basisTensorPair, multilinearComponent4,
    basisTuple4, Matrix.one_apply]
  simp_rw [Finset.sum_add_distrib]
  simp
  simp_rw [Finset.sum_add_distrib]
  ring

/-- **Math.** A fixed-basis tensor contraction differentiates by the finite
product rule encoded in `basisTensorPairVariation`.  Only scalar component
derivatives are required; the derivative components need not first be packaged
as a multilinear map. -/
theorem hasDerivWithinAt_basisTensorPair
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {ι : Type*} [Fintype ι]
    {G : ℝ → Matrix ι ι ℝ} {dG : Matrix ι ι ℝ}
    (v : Module.Basis ι ℝ V) {J : Set ℝ} {t : ℝ} (n : ℕ)
    (A B : ℝ → MultilinearMap ℝ (fun _ : Fin n => V) ℝ)
    (dA dB : (Fin n → V) → ℝ)
    (hG : ∀ a b, HasDerivWithinAt (fun s => G s a b) (dG a b) J t)
    (hA : ∀ w, HasDerivWithinAt (fun s => A s w) (dA w) J t)
    (hB : ∀ w, HasDerivWithinAt (fun s => B s w) (dB w) J t) :
    HasDerivWithinAt
      (fun s => basisTensorPair (G s) v n (A s) (B s))
      (basisTensorPairVariation (G t) dG v n (A t) dA (B t) dB) J t := by
  induction n with
  | zero =>
      convert (hA (fun i => i.elim0)).mul (hB (fun i => i.elim0)) using 1
      · exact AddCommGroup.ext rfl
      · exact Module.ext rfl
      · funext s
        rfl
      · rfl
  | succ n ih =>
      simp only [basisTensorPair, basisTensorPairVariation]
      exact HasDerivWithinAt.fun_sum fun a _ => HasDerivWithinAt.fun_sum fun b _ =>
        (hG a b).mul
          (ih (fun s => (A s).curryLeft (v a))
            (fun s => (B s).curryLeft (v b))
            (fun w => dA (Fin.cons (v a) w))
            (fun w => dB (Fin.cons (v b) w))
            (fun w => by
              simpa only [MultilinearMap.curryLeft_apply] using
                hA (Fin.cons (v a) w))
            (fun w => by
              simpa only [MultilinearMap.curryLeft_apply] using
                hB (Fin.cons (v b) w)))

/-! ### Covariant tensor fields -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The metric Gram matrix of a basis is positive definite, so its
ring inverse is a right inverse. -/
theorem metricGramMatrixInBasis_mul_metricInvGramMatrixInBasis
    (g : RiemannianMetric I M) {p : M}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Module.Basis ι ℝ (TangentSpace I p)) :
    metricGramMatrixInBasis g v * metricInvGramMatrixInBasis g v = 1 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hGram : metricGramMatrixInBasis g v = Matrix.gram ℝ v := by
    ext a b
    rfl
  have hpos : (metricGramMatrixInBasis g v).PosDef := by
    rw [hGram]
    exact Matrix.posDef_gram_of_linearIndependent v.linearIndependent
  have hdet : IsUnit (metricGramMatrixInBasis g v).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  rw [metricInvGramMatrixInBasis, ← Matrix.nonsing_inv_eq_ringInverse]
  exact Matrix.mul_nonsing_inv _ hdet

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Componentwise metric derivatives in a fixed basis determine the
componentwise derivative of its inverse Gram matrix. -/
theorem hasDerivWithinAt_metricInvGramMatrixInBasis
    {g : ℝ → RiemannianMetric I M} {p : M}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Module.Basis ι ℝ (TangentSpace I p))
    {J : Set ℝ} {t : ℝ} (dG : Matrix ι ι ℝ)
    (hG : ∀ a b, HasDerivWithinAt
      (fun s => metricGramMatrixInBasis (g s) v a b) (dG a b) J t) :
    ∀ a b, HasDerivWithinAt
      (fun s => metricInvGramMatrixInBasis (g s) v a b)
      (-(metricInvGramMatrixInBasis (g t) v * dG *
        metricInvGramMatrixInBasis (g t) v) a b) J t := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  have hGram : metricGramMatrixInBasis (g t) v = Matrix.gram ℝ v := by
    ext a b
    rfl
  have hpos : (metricGramMatrixInBasis (g t) v).PosDef := by
    rw [hGram]
    exact Matrix.posDef_gram_of_linearIndependent v.linearIndependent
  have hu : IsUnit (metricGramMatrixInBasis (g t) v) :=
    (Matrix.isUnit_iff_isUnit_det (metricGramMatrixInBasis (g t) v)).mpr
      (isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos))
  have hGmat : HasDerivWithinAt
      (fun s => metricGramMatrixInBasis (g s) v) dG J t :=
    hasDerivWithinAt_pi.mpr fun a => hasDerivWithinAt_pi.mpr fun b => hG a b
  have hinv := hasDerivWithinAt_matrixInverse hGmat hu
  have hinv' : HasDerivWithinAt
      (fun s => metricInvGramMatrixInBasis (g s) v)
      (-(metricInvGramMatrixInBasis (g t) v * dG *
        metricInvGramMatrixInBasis (g t) v)) J t := by
    simpa only [metricInvGramMatrixInBasis] using hinv
  intro a b
  exact hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp hinv' a) b

/-- **Math.** The honest multilinear map at `p` represented by a pointwise multilinear
covariant tensor field. -/
def pointwiseMultilinearMap {k : ℕ} {A : CovTensorField I M k} {p : M}
    (hA : IsPointwiseMultilinear A p) :
    MultilinearMap ℝ (fun _ : Fin k => TangentSpace I p) ℝ where
  toFun := pointwiseValue A p
  map_update_add' {hDecEq} v i x y := by
    cases Subsingleton.elim hDecEq (instDecidableEqFin k)
    exact hA.add i v x y
  map_update_smul' {hDecEq} v i c x := by
    cases Subsingleton.elim hDecEq (instDecidableEqFin k)
    simpa only [smul_eq_mul] using hA.smul i v c x

omit [CompleteSpace E] in
/-- **Math.** The square norm of a pointwise multilinear covariant tensor is
the inverse-Gram contraction of its components in any basis. -/
theorem normSqAt_eq_basisTensorPair (g : RiemannianMetric I M) {k : ℕ}
    {A : CovTensorField I M k} {p : M} (hA : IsPointwiseMultilinear A p)
    (v : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p))
    {G Ginv : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ}
    (hG : ∀ a b, G a b = g.metricInner p (v a) (v b))
    (hGinv : G * Ginv = 1) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    normSqAt g A p = basisTensorPair Ginv v k
      (pointwiseMultilinearMap hA) (pointwiseMultilinearMap hA) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := orthonormalTensorPair_eq_basisTensorPair
    (stdOrthonormalBasis ℝ (TangentSpace I p)) v hG hGinv k
      (pointwiseMultilinearMap hA) (pointwiseMultilinearMap hA)
  simpa only [normSqAt, orthonormalTensorPair, pointwiseMultilinearMap,
    MultilinearMap.coe_mk, pointwiseValue, pow_two] using h

omit [CompleteSpace E] in
/-- **Math.** The fixed-basis norm formula specialized to the inverse of the
metric Gram matrix. -/
theorem normSqAt_eq_metricInvGramBasisTensorPair
    (g : RiemannianMetric I M) {k : ℕ}
    {A : CovTensorField I M k} {p : M} (hA : IsPointwiseMultilinear A p)
    (v : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    normSqAt g A p = basisTensorPair (metricInvGramMatrixInBasis g v) v k
      (pointwiseMultilinearMap hA) (pointwiseMultilinearMap hA) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact normSqAt_eq_basisTensorPair g hA v (fun _ _ => rfl)
    (metricGramMatrixInBasis_mul_metricInvGramMatrixInBasis g v)

omit [CompleteSpace E] in
/-- **Math.** In a fixed chart frame, `|A|^2` is the full contraction of the
fixed chart components against the inverse chart Gram matrix. -/
theorem normSqAt_eq_chartBasisTensorPair (g : RiemannianMetric I M) {k : ℕ}
    {A : CovTensorField I M k} {p : M} (hA : IsPointwiseMultilinear A p)
    (alpha : M)
    (hp : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    normSqAt g A p =
      basisTensorPair (Tensor.chartInvGramMatrix (I := I) g alpha p)
        (Tensor.chartBasisFamily (I := I) alpha hp) k
        (pointwiseMultilinearMap hA) (pointwiseMultilinearMap hA) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply normSqAt_eq_basisTensorPair g hA
    (Tensor.chartBasisFamily (I := I) alpha hp)
    (G := Tensor.chartGramMatrix (I := I) g alpha p)
    (Ginv := Tensor.chartInvGramMatrix (I := I) g alpha p)
  · intro a b
    rw [Tensor.chartBasisFamily_apply, Tensor.chartBasisFamily_apply]
    rfl
  · exact Tensor.chartGramMatrix_mul_chartInvGramMatrix (I := I) g alpha hp

omit [CompleteSpace E] in
/-- **Math.** In a fixed chart frame, componentwise derivatives of the inverse
Gram matrix and of a covariant tensor determine the derivative of its square
norm.  This is the moving-metric product rule with all finite contractions
made explicit. -/
theorem hasDerivWithinAt_normSqAt_chart
    {g : ℝ → RiemannianMetric I M} {k : ℕ}
    {A : ℝ → CovTensorField I M k} {p alpha : M}
    (hA : ∀ s, IsPointwiseMultilinear (A s) p)
    {J : Set ℝ} {t : ℝ}
    (hp : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet)
    (dG : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (dA : (Fin k → TangentSpace I p) → ℝ)
    (hG : ∀ a b, HasDerivWithinAt
      (fun s => Tensor.chartInvGramMatrix (I := I) (g s) alpha p a b)
      (dG a b) J t)
    (hcomp : ∀ w, HasDerivWithinAt
      (fun s => pointwiseValue (A s) p w) (dA w) J t) :
    HasDerivWithinAt
      (fun s => normSqAt (g s) (A s) p)
      (basisTensorPairVariation
        (Tensor.chartInvGramMatrix (I := I) (g t) alpha p) dG
        (Tensor.chartBasisFamily (I := I) alpha hp) k
        (pointwiseMultilinearMap (hA t)) dA
        (pointwiseMultilinearMap (hA t)) dA) J t := by
  classical
  have hpair := hasDerivWithinAt_basisTensorPair
    (Tensor.chartBasisFamily (I := I) alpha hp) k
    (fun s => pointwiseMultilinearMap (hA s))
    (fun s => pointwiseMultilinearMap (hA s)) dA dA hG
    (fun w => by
      simpa only [pointwiseMultilinearMap, MultilinearMap.coe_mk] using hcomp w)
    (fun w => by
      simpa only [pointwiseMultilinearMap, MultilinearMap.coe_mk] using hcomp w)
  refine hpair.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    (normSqAt_eq_chartBasisTensorPair (g t) (hA t) alpha hp)
  exact normSqAt_eq_chartBasisTensorPair (g s) (hA s) alpha hp

omit [CompleteSpace E] in
/-- **Math.** In any fixed basis, componentwise derivatives of the inverse
Gram matrix and a covariant tensor determine the derivative of its square norm. -/
theorem hasDerivWithinAt_normSqAt_basis
    {g : ℝ → RiemannianMetric I M} {k : ℕ}
    {A : ℝ → CovTensorField I M k} {p : M}
    (v : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p))
    (hA : ∀ s, IsPointwiseMultilinear (A s) p)
    {J : Set ℝ} {t : ℝ}
    (dG : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (dA : (Fin k → TangentSpace I p) → ℝ)
    (hG : ∀ a b, HasDerivWithinAt
      (fun s => metricInvGramMatrixInBasis (g s) v a b) (dG a b) J t)
    (hcomp : ∀ w, HasDerivWithinAt
      (fun s => pointwiseValue (A s) p w) (dA w) J t) :
    HasDerivWithinAt
      (fun s => normSqAt (g s) (A s) p)
      (basisTensorPairVariation (metricInvGramMatrixInBasis (g t) v) dG v k
        (pointwiseMultilinearMap (hA t)) dA
        (pointwiseMultilinearMap (hA t)) dA) J t := by
  classical
  have hpair := hasDerivWithinAt_basisTensorPair v k
    (fun s => pointwiseMultilinearMap (hA s))
    (fun s => pointwiseMultilinearMap (hA s)) dA dA hG
    (fun w => by
      simpa only [pointwiseMultilinearMap, MultilinearMap.coe_mk] using hcomp w)
    (fun w => by
      simpa only [pointwiseMultilinearMap, MultilinearMap.coe_mk] using hcomp w)
  refine hpair.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    (normSqAt_eq_metricInvGramBasisTensorPair (g t) (hA t) v)
  exact normSqAt_eq_metricInvGramBasisTensorPair (g s) (hA s) v

#print axioms Topping.orthonormalTensorPair_eq_basisTensorPair
#print axioms Topping.hasDerivWithinAt_matrixInverse
#print axioms Topping.hasDerivWithinAt_metricInvGramMatrixInBasis
#print axioms Topping.hasDerivWithinAt_basisTensorPair
#print axioms Topping.basisTensorPairVariation_one_four
#print axioms Topping.normSqAt_eq_basisTensorPair
#print axioms Topping.normSqAt_eq_metricInvGramBasisTensorPair
#print axioms Topping.normSqAt_eq_chartBasisTensorPair
#print axioms Topping.hasDerivWithinAt_normSqAt_chart
#print axioms Topping.hasDerivWithinAt_normSqAt_basis

end Topping

end
