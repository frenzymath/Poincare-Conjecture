import MorganTianLib.Ch04.Tensoriality
import MorganTianLib.Ch02.TraceCommutation
import MorganTianLib.Ch01.SecondCov

/-!
# Morgan--Tian Ch. 4 - pointwise tensorial contact

The scalarization of a tensor by a tuple of vector fields has connection
correction terms.  This file proves the pointwise cancellation needed in the
Hamilton maximum-principle argument.  A first-order normal tuple makes the
slot carrying `nabla.cov X (Y j)` vanish at the contact point; tensoriality of
`A` and of its covariant derivative kills all other slots, while the second
covariant-derivative condition cancels the remaining diagonal term.

The result is deliberately stated for the evaluator representation used by
Chapter 3.  It is a conditional algebraic bridge: the first- and second-jet
conditions are explicit hypotheses, while construction of those geometric
jets and the parallel frame remains a separate producer obligation.
-/

open Set Filter Function
open Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### One direction of the contact calculation -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Pointwise second-order contact cancellation in one direction.

For `W j = nabla.cov X (Y j)`, the derivative of the frame correction is
expanded by the definition of `covTensorDerivAlong`.  The derivative-tensor
term vanishes because `W j` is zero at the contact point.  In the remaining
finite sum, all off-diagonal terms have the same zero slot, and the diagonal
term is identified with the correction in the `nabla.cov X X` direction by
the hypothesis `secondCov nabla X X (Y j) p = 0`.

This is the source-faithful local algebraic core of Hamilton's tensor contact
argument. -/
theorem covTensorContactSummand_eq_zero
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M)
    (hA : IsCovariantTensorField A)
    (hD : IsCovariantTensorField (covTensorDerivAlong nabla X A))
    (hfirst : ∀ j : Fin k, (nabla.cov X (Y j)) p = 0)
    (hsecond : ∀ j : Fin k, secondCov nabla X X (Y j) p = 0) :
    covTensorOuterFrameDefect nabla X A Y p -
      (∑ j, covTensorDerivAlong nabla X A
        (Function.update Y j (nabla.cov X (Y j))) p) +
      covTensorFrameCorrection nabla
        (nabla.cov X X) A Y p = 0 := by
  have hAY : ContMDiff I 𝓘(ℝ, ℝ) ∞ (A Y) := hA.contMDiff_eval Y
  have hC : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (covTensorFrameCorrection nabla X A Y) := by
    unfold covTensorFrameCorrection
    exact contMDiff_finsetSum (fun j hj => hA.contMDiff_eval _)
  have houter :
      covTensorOuterFrameDefect nabla X A Y p =
        -X.dir (covTensorFrameCorrection nabla X A Y) p :=
    covTensorOuterFrameDefect_eq_neg_dir_correction nabla X A Y p hAY hC
  have hdirC :
      X.dir (covTensorFrameCorrection nabla X A Y) p =
        ∑ j, X.dir (fun q => A
          (Function.update Y j (nabla.cov X (Y j))) q) p := by
    unfold covTensorFrameCorrection
    rw [dir_sum X]
    intro j hj
    exact hA.contMDiff_eval _
  have hDzero : ∀ j : Fin k, covTensorDerivAlong nabla X A
        (Function.update Y j (nabla.cov X (Y j))) p = 0 := by
    intro j
    exact hD.apply_eq_zero_of_slot_apply_eq_zero
      (Function.update Y j (nabla.cov X (Y j))) j p (by
        simp [hfirst j])
  have hsum : ∀ j : Fin k,
      (∑ l, A (Function.update
          (Function.update Y j (nabla.cov X (Y j))) l
          (nabla.cov X ((Function.update Y j (nabla.cov X (Y j))) l))) p) =
        A (Function.update Y j (nabla.cov (nabla.cov X X) (Y j))) p := by
    intro j
    have hdiag :
        A (Function.update
            (Function.update Y j (nabla.cov X (Y j))) j
            (nabla.cov X ((Function.update Y j (nabla.cov X (Y j))) j))) p =
        A (Function.update Y j (nabla.cov (nabla.cov X X) (Y j))) p := by
      have hUV :
          (nabla.cov X ((Function.update Y j (nabla.cov X (Y j))) j)) p =
            (nabla.cov (nabla.cov X X) (Y j)) p := by
        have hs := hsecond j
        rw [secondCov_apply] at hs
        simpa using (sub_eq_zero.mp hs)
      have hupd :
          Function.update
              (Function.update Y j (nabla.cov X (Y j))) j
              (nabla.cov X ((Function.update Y j (nabla.cov X (Y j))) j)) =
            Function.update Y j
              (nabla.cov X ((Function.update Y j (nabla.cov X (Y j))) j)) := by
        funext l
        by_cases hlj : l = j
        · subst l
          simp
        · simp [Function.update_of_ne hlj]
      rw [hupd]
      exact hA.congr_slot_apply Y j hUV
    calc
      (∑ l, A (Function.update
          (Function.update Y j (nabla.cov X (Y j))) l
          (nabla.cov X ((Function.update Y j (nabla.cov X (Y j))) l))) p) =
          A (Function.update
            (Function.update Y j (nabla.cov X (Y j))) j
            (nabla.cov X ((Function.update Y j (nabla.cov X (Y j))) j))) p := by
              apply Finset.sum_eq_single j (s := Finset.univ)
              · intro l hl hlj
                apply hA.apply_eq_zero_of_slot_apply_eq_zero
                  (Function.update
                    (Function.update Y j (nabla.cov X (Y j))) l
                    (nabla.cov X ((Function.update Y j (nabla.cov X (Y j))) l))) j p
                rw [Function.update_of_ne (Ne.symm hlj)]
                simp [hfirst j]
              · intro hj
                simp at hj
      _ = A (Function.update Y j (nabla.cov (nabla.cov X X) (Y j))) p := hdiag
  rw [houter, hdirC]
  have hexpand : ∀ j : Fin k,
      X.dir (fun q => A
          (Function.update Y j (nabla.cov X (Y j))) q) p =
        covTensorDerivAlong nabla X A
          (Function.update Y j (nabla.cov X (Y j))) p +
        ∑ l, A (Function.update
          (Function.update Y j (nabla.cov X (Y j))) l
          (nabla.cov X ((Function.update Y j (nabla.cov X (Y j))) l))) p := by
    intro j
    rw [covTensorDerivAlong_apply]
    ring
  simp_rw [hexpand, hDzero, zero_add, hsum]
  unfold covTensorFrameCorrection
  simp

/-! ### The traced orthonormal-frame consequence -/

/-- **Math.** The canonical tuple of global vector-field extensions used by the traced
contact defect.  The metric on the tangent bundle is installed locally, just
as it is in `roughLaplacianContactDefect`; packaging the tuple here lets the
pointwise hypotheses be stated with an explicit finite index. -/
def canonicalContactFrame (g : RiemannianMetric I M) (p : M) :
    Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  fun i => extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** A universal-direction adapter for the traced contact defect.
This form is useful when a producer supplies the tensoriality and contact
conditions uniformly for every direction field.  The indexed, non-vacuous
form consumed by the source argument is
`roughLaplacianContactDefect_eq_zero_of_pointwise_normal` below. -/
theorem roughLaplacianContactDefect_eq_zero_of_all_directions
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M)
    (hA : IsCovariantTensorField A)
    (hD : ∀ X : SmoothVectorField I M,
      IsCovariantTensorField (covTensorDerivAlong nabla X A))
    (hfirst : ∀ (X : SmoothVectorField I M) (j : Fin k),
      (nabla.cov X (Y j)) p = 0)
    (hsecond : ∀ (X : SmoothVectorField I M) (j : Fin k),
      secondCov nabla X X (Y j) p = 0) :
    roughLaplacianContactDefect g nabla A Y p = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold roughLaplacianContactDefect
  apply Finset.sum_eq_zero
  intro i hi
  let Xi : SmoothVectorField I M :=
    extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  exact covTensorContactSummand_eq_zero nabla Xi A Y p hA (hD Xi)
    (fun j => hfirst Xi j) (fun j => hsecond Xi j)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Vanishing of the traced contact defect from pointwise normality
and second-order contact of the canonical orthonormal frame.  The hypotheses
are indexed by the actual frame fields used in
`roughLaplacianContactDefect`, and include genuine tensoriality of each
directional derivative. -/
theorem roughLaplacianContactDefect_eq_zero_of_pointwise_normal
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M)
    (hA : IsCovariantTensorField A)
    (hD : ∀ i, IsCovariantTensorField
      (covTensorDerivAlong nabla (canonicalContactFrame g p i) A))
    (hfirst : ∀ i j,
      (nabla.cov (canonicalContactFrame g p i) (Y j)) p = 0)
    (hsecond : ∀ i j, secondCov nabla (canonicalContactFrame g p i)
      (canonicalContactFrame g p i) (Y j) p = 0) :
    roughLaplacianContactDefect g nabla A Y p = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold roughLaplacianContactDefect
  apply Finset.sum_eq_zero
  intro i hi
  let Xi : SmoothVectorField I M :=
    canonicalContactFrame g p i
  exact covTensorContactSummand_eq_zero nabla Xi A Y p hA (hD i)
    (fun j => hfirst i j) (fun j => hsecond i j)

end MorganTianLib
