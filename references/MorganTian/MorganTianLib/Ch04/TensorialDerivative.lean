import MorganTianLib.Ch04.Tensoriality

/-!
# Covariant differentiation preserves tensoriality

The connection's slot Leibniz term cancels the scalar derivative's product
term. Consequently, the Chapter 3 covariant derivative of a smooth tensor
evaluator is again a smooth tensor evaluator of the same rank.

Blueprint: `thm:maximum-principle-tensors-global`, the tensorial contact
calculation for locally parallel extensions.
-/

open Function Riemannian
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem tensorFrameCorrection_add_slot
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (Y : Fin k → SmoothVectorField I M) (i : Fin k)
    (U V : SmoothVectorField I M) (p : M) :
    covTensorFrameCorrection nabla X A (update Y i (U + V)) p =
      covTensorFrameCorrection nabla X A (update Y i U) p +
        covTensorFrameCorrection nabla X A (update Y i V) p := by
  unfold covTensorFrameCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j = i
  · subst j
    simp only [update_self, update_idem, nabla.add_right]
    exact hA.add_slot Y i (nabla.cov X U) (nabla.cov X V) p
  · simp only [update_of_ne hji, update_comm (Ne.symm hji)]
    exact hA.add_slot (update Y j (nabla.cov X (Y j))) i U V p

private theorem tensorFrameCorrection_smul_slot
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (Y : Fin k → SmoothVectorField I M) (i : Fin k)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (U : SmoothVectorField I M) (p : M) :
    covTensorFrameCorrection nabla X A
        (update Y i (SmoothVectorField.smul f hf U)) p =
      f p * covTensorFrameCorrection nabla X A (update Y i U) p +
        X.dir f p * A (update Y i U) p := by
  have hterm : ∀ j : Fin k,
      A (update (update Y i (SmoothVectorField.smul f hf U)) j
        (nabla.cov X ((update Y i (SmoothVectorField.smul f hf U)) j))) p =
      f p * A (update (update Y i U) j (nabla.cov X ((update Y i U) j))) p +
        if j = i then X.dir f p * A (update Y i U) p else 0 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [nabla.cov_smul_right, hA.add_slot, hA.smul_slot]
    · simp only [update_of_ne hji, update_comm (Ne.symm hji), if_neg hji, add_zero]
      exact hA.smul_slot (update Y j (nabla.cov X (Y j))) i f hf U p
  unfold covTensorFrameCorrection
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

/-- **Math.** The covariant derivative in a fixed smooth direction preserves
smoothness and tensoriality in every covariant slot, in arbitrary rank. -/
theorem IsCovariantTensorField.covTensorDerivAlong
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (nabla : AffineConnection I M) (X : SmoothVectorField I M) :
    IsCovariantTensorField (covTensorDerivAlong nabla X A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Y
    exact (X.dir_contMDiff (hA.contMDiff_eval Y)).sub
      (contMDiff_finsetSum (fun j hj => hA.contMDiff_eval _))
  · intro Y i U V p
    have hfun : A (update Y i (U + V)) =
        fun q => A (update Y i U) q + A (update Y i V) q :=
      funext (fun q => hA.add_slot Y i U V q)
    change X.dir (A (update Y i (U + V))) p -
        covTensorFrameCorrection nabla X A (update Y i (U + V)) p = _
    rw [hfun, X.dir_add p
      ((hA.contMDiff_eval _ p).mdifferentiableAt (by simp))
      ((hA.contMDiff_eval _ p).mdifferentiableAt (by simp)),
      tensorFrameCorrection_add_slot nabla X hA]
    simp only [MorganTianLib.covTensorDerivAlong, covTensorFrameCorrection_apply]
    ring
  · intro Y i f hf U p
    have hfun : A (update Y i (SmoothVectorField.smul f hf U)) =
        fun q => f q * A (update Y i U) q :=
      funext (fun q => hA.smul_slot Y i f hf U q)
    change X.dir (A (update Y i (SmoothVectorField.smul f hf U))) p -
        covTensorFrameCorrection nabla X A
          (update Y i (SmoothVectorField.smul f hf U)) p = _
    rw [hfun, X.dir_mul p ((hf p).mdifferentiableAt (by simp))
      ((hA.contMDiff_eval _ p).mdifferentiableAt (by simp)),
      tensorFrameCorrection_smul_slot nabla X hA]
    simp only [MorganTianLib.covTensorDerivAlong, covTensorFrameCorrection_apply]
    ring

end MorganTianLib

#print axioms MorganTianLib.IsCovariantTensorField.covTensorDerivAlong
