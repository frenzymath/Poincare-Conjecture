import MorganTianLib.Ch04.ScalarTensorLaplacian
import MorganTianLib.Ch03.RicciFlow.CurvatureLaplacian

/-!
# Morgan--Tian Ch. 4 - second-order tensor/scalar contact

The rough Laplacian in Chapter 3 is represented by evaluating a covariant
tensor on smooth vector-field extensions.  A scalarization by such a tuple is
not literally the scalar Laplacian: differentiating the tuple produces
connection terms.  This file records the exact pointwise defect, obtained by
expanding the definitions.  It is the load-bearing second-order contact
identity needed before a geometric normal/parallel-frame argument can be
applied.

No parallel-frame or tensoriality certificate is hidden here.  The defect is
explicit, so a later geometric producer can discharge its terms (or identify
the curvature correction) rather than assuming the desired contact equality.
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

/-! ### The explicit first-order frame correction -/

/-- **Math.** The connection correction produced when differentiating a
covariant tensor on a tuple of smooth vector fields.  Keeping this as a
function (rather than only its value at one point) makes the outer directional
derivative in the second-order identity visible. -/
def covTensorFrameCorrection
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) : M → ℝ :=
  fun p => ∑ i, A (Function.update Y i (nabla.cov X (Y i))) p

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem covTensorFrameCorrection_apply
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    covTensorFrameCorrection nabla X A Y p =
      ∑ i, A (Function.update Y i (nabla.cov X (Y i))) p :=
  rfl

/-- **Math.** The outer derivative defect: the difference between differentiating
the corrected first derivative and differentiating only its scalar part. -/
def covTensorOuterFrameDefect
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M) : ℝ :=
  X.dir (fun q => X.dir (A Y) q -
      covTensorFrameCorrection nabla X A Y q) p -
    X.dir (X.dir (A Y)) p

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** If the scalarization and its frame correction are smooth, the
outer defect is exactly the negative directional derivative of that correction.
This is the analytic part of the second-order contact argument; no geometric
parallel-frame assumption is made. -/
theorem covTensorOuterFrameDefect_eq_neg_dir_correction
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M)
    (hAY : ContMDiff I 𝓘(ℝ, ℝ) ∞ (A Y))
    (hC : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (covTensorFrameCorrection nabla X A Y)) :
    covTensorOuterFrameDefect nabla X A Y p =
      -X.dir (covTensorFrameCorrection nabla X A Y) p := by
  unfold covTensorOuterFrameDefect
  have hdirAY : ContMDiff I 𝓘(ℝ, ℝ) ∞ (X.dir (A Y)) :=
    X.dir_contMDiff hAY
  have hdir_add := X.dir_add p
    (hdirAY.mdifferentiableAt (by simp))
    ((hC.neg).mdifferentiableAt (by simp))
  have hneg : X.dir (fun q => -covTensorFrameCorrection nabla X A Y q) p =
      -X.dir (covTensorFrameCorrection nabla X A Y) p := by
    simp only [SmoothVectorField.dir]
    rw [show (fun q => -covTensorFrameCorrection nabla X A Y q) =
      -(covTensorFrameCorrection nabla X A Y) from rfl, mfderiv_neg]
    rfl
  have houter : X.dir (fun q => X.dir (A Y) q -
      covTensorFrameCorrection nabla X A Y q) p =
      X.dir (X.dir (A Y)) p -
        X.dir (covTensorFrameCorrection nabla X A Y) p := by
    rw [show (fun q => X.dir (A Y) q -
        covTensorFrameCorrection nabla X A Y q) =
        (fun q => X.dir (A Y) q +
          (-covTensorFrameCorrection nabla X A Y q)) from by
          funext q; ring]
    rw [hdir_add, hneg]
    ring
  rw [houter]
  ring

/-! ### The second-order contact expansion -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Exact second-order contact expansion.  For an arbitrary
evaluation-level covariant tensor field `A` and tuple `Y`, the corrected second
covariant derivative differs from the scalar Hessian of `A Y` by three
explicit terms: the directional derivative of the first-order frame
correction, the derivative-tensor correction on each differentiated slot, and
the correction in the connection direction `∇_X X`.

This identity is purely definitional and therefore does not assume that `Y` is
parallel or that `A` has already been shown tensorial. -/
theorem secondCovDerivAlong_eq_hessian_sub_contactDefect
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong nabla X X A Y p =
      hessian nabla (fun q => A Y q) X X p
        + covTensorOuterFrameDefect nabla X A Y p
        - ∑ i, covTensorDerivAlong nabla X A
            (Function.update Y i (nabla.cov X (Y i))) p
        + covTensorFrameCorrection nabla (nabla.cov X X) A Y p := by
  unfold secondCovDerivAlong
  rw [covTensorDerivAlong_apply nabla X
    (covTensorDerivAlong nabla X A) Y p]
  have hinner : covTensorDerivAlong nabla X A Y =
      (fun q => X.dir (A Y) q - covTensorFrameCorrection nabla X A Y q) := by
    funext q
    rfl
  rw [hinner]
  rw [covTensorDerivAlong_apply nabla (nabla.cov X X) A Y p]
  unfold hessian covTensorOuterFrameDefect covTensorFrameCorrection
  ring

/-! ### The trace-level rough-Laplacian identity -/

/-- **Math.** The traced second-order contact defect in the metric orthonormal frame.
The first sum is over derivative directions and the inner sum is over the
slots of `A`; retaining both indices is important when the tensor has rank
greater than one. -/
def roughLaplacianContactDefect
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, (
    covTensorOuterFrameDefect nabla
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) A Y p
      - (∑ j, covTensorDerivAlong nabla
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) A
          (Function.update Y j
            (nabla.cov
              (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
              (Y j))) p)
      + covTensorFrameCorrection nabla
          (nabla.cov
            (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
            (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))) A Y p)

omit [CompleteSpace E] in
/-- **Math.** Trace the preceding expansion in the metric orthonormal frame.
The rough Laplacian of `A` evaluated on `Y` equals the scalar Laplacian of the
scalarization `fun q => A Y q` plus the traced contact defect.  The theorem is
an exact bridge: all terms needed by a genuine second-order parallel-frame
producer are displayed rather than postulated. -/
theorem roughLaplacian_apply_eq_laplacianAt_add_contactDefect
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    roughLaplacian g nabla A Y p =
      laplacianAt g nabla (fun q => A Y q) p +
        roughLaplacianContactDefect g nabla A Y p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [roughLaplacian_apply]
  unfold laplacianAt
  simp only [hessianAt_def]
  unfold roughLaplacianContactDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hdir := secondCovDerivAlong_eq_hessian_sub_contactDefect
    nabla (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) A Y p
  rw [hdir]
  ring

/-! ### A transparent zero-defect contact criterion -/

omit [CompleteSpace E] in
/-- **Math.** If the three explicit frame/contact terms vanish in the traced
orthonormal frame, the rough Laplacian agrees with the scalar Laplacian of the
scalarization.  This is intentionally a consequence of the displayed defect
identity; geometric parallel-frame work can use it as its exact target. -/
theorem roughLaplacian_apply_eq_laplacianAt_of_contact
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M)
    (hcontact : roughLaplacianContactDefect g nabla A Y p = 0) :
    roughLaplacian g nabla A Y p = laplacianAt g nabla (fun q => A Y q) p := by
  rw [roughLaplacian_apply_eq_laplacianAt_add_contactDefect g nabla A Y p]
  simp [hcontact]

omit [CompleteSpace E] in
/-- **Math.** At a spatial maximum of a smooth scalarization, a zero contact
defect turns the rough Laplacian into a nonpositive quantity.  This is the
analytic endpoint consumed by the Hamilton support-envelope argument. -/
theorem roughLaplacian_apply_nonpositive_at_max_of_contact
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (A Y))
    (hmax : IsMaxOn (fun q => A Y q) (univ : Set M) p)
    (hcontact : roughLaplacianContactDefect g nabla A Y p = 0) :
    roughLaplacian g nabla A Y p ≤ 0 := by
  rw [roughLaplacian_apply_eq_laplacianAt_of_contact g nabla A Y p hcontact]
  exact (laplacianAt_nonpos_of_isLocalMax g nabla hf
    (isLocalMaxOn_univ_iff.mp hmax.localize)).2

end MorganTianLib
