import Topping.Riemannian.CurvatureMultilinear

/-!
# Pointwise multilinearity after a metric trace

The tuple representation of a covariant tensor does not itself expose its
pointwise fibre map.  This module supplies the rank-three bridge needed by the
DeTurck one-form: a covariant three-tensor gives a pointwise multilinear
`CovTensorField`, and contracting its first two slots preserves that property.
The final divergence theorem packages the harmless minus sign in Topping's
convention.
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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- A covariant three-tensor is pointwise local in all three slots. -/
theorem covariantTensor3_congr_apply
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      (M → ℝ))
    (hT : IsCovariantTensor3 T)
    {X X' Y Y' Z Z' : SmoothVectorField I M} {p : M}
    (hX : X p = X' p) (hY : Y p = Y' p) (hZ : Z p = Z' p) :
    T X Y Z p = T X' Y' Z' p := by
  have h1 : T X Y Z p = T X' Y Z p :=
    MorganTianLib.tensorial_congr_apply (fun A => T A Y Z)
      (fun A B q => hT.add₁ A B Y Z q)
      (fun f hf A q => hT.smul₁ f hf A Y Z q) hX
  have h2 : T X' Y Z p = T X' Y' Z p :=
    MorganTianLib.tensorial_congr_apply (fun B => T X' B Z)
      (fun A B q => hT.add₂ X' A B Z q)
      (fun f hf A q => hT.smul₂ f hf X' A Z q) hY
  have h3 : T X' Y' Z p = T X' Y' Z' p :=
    MorganTianLib.tensorial_congr_apply (fun C => T X' Y' C)
      (fun A B q => hT.add₃ X' Y' A B q)
      (fun f hf A q => hT.smul₃ f hf X' Y' A q) hZ
  exact h1.trans (h2.trans h3)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- Convert a covariant three-tensor presentation into pointwise multilinearity.
The `hA` equality is only a representation change; all tensoriality comes from
the four-field predicate `hT`. -/
theorem isPointwiseMultilinear_of_isCovariantTensor3
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      (M → ℝ))
    (hT : IsCovariantTensor3 T) (A : CovTensorField I M 3)
    (hA : ∀ (Y : Fin 3 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) (Y 2) q) (p : M) :
    IsPointwiseMultilinear A p := by
  classical
  refine isPointwiseMultilinear_of_pointwise
    (fun v => T (MorganTianLib.extendVector p (v 0))
      (MorganTianLib.extendVector p (v 1))
      (MorganTianLib.extendVector p (v 2)) p) ?_ ?_ ?_
  · intro Y
    rw [hA]
    exact covariantTensor3_congr_apply T hT
      (MorganTianLib.extendVector_apply p (Y 0 p)).symm
      (MorganTianLib.extendVector_apply p (Y 1 p)).symm
      (MorganTianLib.extendVector_apply p (Y 2 p)).symm
  · intro i v x y
    fin_cases i <;> simp
    · have h :
        T (MorganTianLib.extendVector p (x + y))
            (MorganTianLib.extendVector p (v 1))
            (MorganTianLib.extendVector p (v 2)) p =
          T (MorganTianLib.extendVector p x + MorganTianLib.extendVector p y)
            (MorganTianLib.extendVector p (v 1))
            (MorganTianLib.extendVector p (v 2)) p := by
        apply covariantTensor3_congr_apply T hT
        · simp
        · rfl
        · rfl
      rw [h, hT.add₁]
    · have h :
        T (MorganTianLib.extendVector p (v 0))
            (MorganTianLib.extendVector p (x + y))
            (MorganTianLib.extendVector p (v 2)) p =
          T (MorganTianLib.extendVector p (v 0))
            (MorganTianLib.extendVector p x + MorganTianLib.extendVector p y)
            (MorganTianLib.extendVector p (v 2)) p := by
        apply covariantTensor3_congr_apply T hT
        · rfl
        · simp
        · rfl
      rw [h, hT.add₂]
    · have h :
        T (MorganTianLib.extendVector p (v 0))
            (MorganTianLib.extendVector p (v 1))
            (MorganTianLib.extendVector p (x + y)) p =
          T (MorganTianLib.extendVector p (v 0))
            (MorganTianLib.extendVector p (v 1))
            (MorganTianLib.extendVector p x + MorganTianLib.extendVector p y) p := by
        apply covariantTensor3_congr_apply T hT
        · rfl
        · rfl
        · simp
      rw [h, hT.add₃]
  · intro i v c x
    have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
    fin_cases i <;> simp
    · have h :
        T (MorganTianLib.extendVector p (c • x))
            (MorganTianLib.extendVector p (v 1))
            (MorganTianLib.extendVector p (v 2)) p =
          T (SmoothVectorField.smul (fun _ => c) hc
              (MorganTianLib.extendVector p x))
            (MorganTianLib.extendVector p (v 1))
            (MorganTianLib.extendVector p (v 2)) p := by
        apply covariantTensor3_congr_apply T hT
        · simp
        · rfl
        · rfl
      rw [h, hT.smul₁ (fun _ => c) hc]
    · have h :
        T (MorganTianLib.extendVector p (v 0))
            (MorganTianLib.extendVector p (c • x))
            (MorganTianLib.extendVector p (v 2)) p =
          T (MorganTianLib.extendVector p (v 0))
            (SmoothVectorField.smul (fun _ => c) hc
              (MorganTianLib.extendVector p x))
            (MorganTianLib.extendVector p (v 2)) p := by
        apply covariantTensor3_congr_apply T hT
        · rfl
        · simp
        · rfl
      rw [h, hT.smul₂ (fun _ => c) hc]
    · have h :
        T (MorganTianLib.extendVector p (v 0))
            (MorganTianLib.extendVector p (v 1))
            (MorganTianLib.extendVector p (c • x)) p =
          T (MorganTianLib.extendVector p (v 0))
            (MorganTianLib.extendVector p (v 1))
            (SmoothVectorField.smul (fun _ => c) hc
              (MorganTianLib.extendVector p x)) p := by
        apply covariantTensor3_congr_apply T hT
        · rfl
        · rfl
        · simp
      rw [h, hT.smul₃ (fun _ => c) hc]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- Contracting the first two slots of a pointwise multilinear rank-three field
preserves pointwise multilinearity in the remaining slot. -/
theorem isPointwiseMultilinear_traceFirstTwo_rank3
    (g : RiemannianMetric I M) {A : CovTensorField I M 3} {p : M}
    (hA : IsPointwiseMultilinear A p) :
    IsPointwiseMultilinear (traceFirstTwo g A) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  let b : (Fin 1 → TangentSpace I p) → ℝ :=
    fun v => ∑ i, pointwiseValue A p
      (Fin.cons (e i) (Fin.cons (e i) v))
  have hval : ∀ Y : Fin 1 → SmoothVectorField I M,
      traceFirstTwo g A Y p = b (fun j => Y j p) := by
    intro Y
    rw [traceFirstTwo_eq_sum_of_frame g hA Y
      (stdOrthonormalBasis ℝ (TangentSpace I p))]
  exact isPointwiseMultilinear_of_pointwise b hval (by
    intro i v x y
    fin_cases i
    simp only [b, Function.update]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have h := hA.add 2
      (Fin.cons (e j) (Fin.cons (e j) v) : Fin 3 → TangentSpace I p) x y
    simpa using h) (by
    intro i v c x
    fin_cases i
    simp only [b, Function.update]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have h := hA.smul 2
      (Fin.cons (e j) (Fin.cons (e j) v) : Fin 3 → TangentSpace I p) c x
    simpa using h)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- Negation preserves pointwise multilinearity. -/
theorem isPointwiseMultilinear_neg
    {k : ℕ} {A : CovTensorField I M k} {p : M}
    (hA : IsPointwiseMultilinear A p) :
    IsPointwiseMultilinear (fun Y q => - A Y q) p := by
  refine isPointwiseMultilinear_of_pointwise
    (fun v => - pointwiseValue A p v) ?_ ?_ ?_
  · intro Y
    rw [pointwiseValue_eq hA.tensorial Y]
  · intro i v x y
    rw [hA.add]
    ring
  · intro i v c x
    rw [hA.smul]
    ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- The divergence of a covariant two-tensor is pointwise multilinear once its
covariant derivative has the corresponding tensor presentation. -/
theorem isPointwiseMultilinear_divergence_of_covariantDerivative
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {A : CovTensorField I M 2}
    (hA : ∀ p : M, IsPointwiseMultilinear (covDeriv nabla A) p) (p : M) :
    IsPointwiseMultilinear (divergence g nabla A) p := by
  change IsPointwiseMultilinear
    (fun Y q => -traceFirstTwo g (covDeriv nabla A) Y q) p
  exact isPointwiseMultilinear_neg
    (isPointwiseMultilinear_traceFirstTwo_rank3 g (hA p))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- A covariant smooth two-tensor has a pointwise multilinear covariant
derivative, with the derivative direction as the first tuple slot. -/
theorem isPointwiseMultilinear_covDeriv_of_isCovariantTensor2
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor2 T)
    (hsm : ∀ X Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y))
    (A : CovTensorField I M 2)
    (hA : ∀ (Y : Fin 2 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) q) (p : M) :
    IsPointwiseMultilinear (covDeriv nabla A) p := by
  let D : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ) :=
    fun X Y U => nabla.covariantDifferential2 T X Y U
  have hD : IsCovariantTensor3 D :=
    isCovariantTensor3_covariantDifferential2 nabla T hT hsm
  let D' : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ) :=
    fun X Y U => D Y U X
  have hD' : IsCovariantTensor3 D' := {
    add₁ := fun X₁ X₂ Y U q => hD.add₃ Y U X₁ X₂ q
    add₂ := fun X Y₁ Y₂ U q => hD.add₁ Y₁ Y₂ U X q
    add₃ := fun X Y U₁ U₂ q => hD.add₂ Y U₁ U₂ X q
    smul₁ := fun f hf X Y U q => hD.smul₃ f hf Y U X q
    smul₂ := fun f hf X Y U q => hD.smul₁ f hf Y U X q
    smul₃ := fun f hf X Y U q => hD.smul₂ f hf Y U X q }
  have hrep : ∀ (Y : Fin 3 → SmoothVectorField I M) (q : M),
      covDeriv nabla A Y q = D' (Y 0) (Y 1) (Y 2) q := by
    intro Y q
    have hY : Y = Fin.cons (Y 0) (fun i => Y i.succ) := by
      funext i
      refine Fin.cases ?_ (fun j => rfl) i
      rfl
    rw [hY, covDeriv_cons, covDerivAlong_eq_covariantDifferential2
      nabla T A hA (Y 0) (fun i => Y i.succ) q]
    rfl
  exact isPointwiseMultilinear_of_isCovariantTensor3 D' hD'
    (covDeriv nabla A) hrep p

end Topping

end
