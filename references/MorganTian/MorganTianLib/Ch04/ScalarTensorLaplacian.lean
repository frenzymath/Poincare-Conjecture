import MorganTianLib.Ch04.HamiltonMaximumLaplacian
import MorganTianLib.Ch03.RicciFlow.CurvatureLaplacian

/-!
# Morgan--Tian Ch. 4 - the rank-zero tensor Laplacian bridge

The Ch. 3 rough Laplacian is represented on tuple-valued covariant tensor
fields.  In rank zero the tuple is empty, so the representation is exactly a
scalar function.  This file proves the resulting operator identity with the
scalar Riemannian Laplacian and records the corresponding maximum inequality.

This is a concrete geometric producer, rather than a certificate for the
arbitrary tensor-bundle maximum principle: higher-rank support scalarizations
still require the spatial parallel-frame and second-order contact arguments.
-/

open Set Filter Function
open Riemannian
open scoped InnerProductSpace Topology ContDiff Manifold Bundle NNReal

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [CompactSpace M] [Nonempty M]

/-- **Math.** The rank-zero covariant tensor represented by a scalar function. -/
def scalarTensorField (f : M → ℝ) : CovTensorField I M 0 :=
  fun _ => f

/-- **Math.** The Ch. 3 rough Laplacian applied to a rank-zero tensor field. -/
def scalarRoughLaplacian (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (f : M → ℝ) (p : M) : ℝ :=
  roughLaplacian g nabla (scalarTensorField f) ![] p

omit [CompleteSpace E] [CompactSpace M] [Nonempty M] in
/-- **Math.** On rank-zero covariant tensors, the rough Laplacian is the
scalar Laplacian defined from the same metric trace of the Hessian. -/
theorem scalarRoughLaplacian_eq_laplacianAt
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (f : M → ℝ) (p : M) :
    scalarRoughLaplacian g nabla f p = laplacianAt g nabla f p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold scalarRoughLaplacian scalarTensorField
  rw [roughLaplacian_apply]
  simp only [laplacianAt]
  apply Finset.sum_congr rfl
  intro i hi
  unfold secondCovDerivAlong covTensorDerivAlong
  simp only [Fin.sum_univ_zero, sub_zero]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] in
/-- **Math.** A constant scalar factor pulls through the Hessian. -/
theorem hessian_const_mul
    (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (c : ℝ)
    (X Y : SmoothVectorField I M) (p : M) :
    hessian nabla (fun q => c * f q) X Y p = c * hessian nabla f X Y p := by
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  have hY : Y.dir (fun q => c * f q) = fun q => c * Y.dir f q := by
    funext q
    rw [Y.dir_mul q (hconst.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
    have hz : Y.dir (fun _ : M => c) q = 0 := by
      change mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => c) q (Y q) = 0
      rw [mfderiv_const]
      rfl
    rw [hz]
    ring
  have hXY : X.dir (Y.dir (fun q => c * f q)) p =
      c * X.dir (Y.dir f) p := by
    rw [hY]
    have h := X.dir_mul p (hconst.mdifferentiableAt (by simp))
      ((Y.dir_contMDiff hf p).mdifferentiableAt (by simp))
    have hz : X.dir (fun _ : M => c) p = 0 := by
      change mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => c) p (X p) = 0
      rw [mfderiv_const]
      rfl
    rw [h, hz]
    ring
  have hC : (nabla.cov X Y).dir (fun q => c * f q) p =
      c * (nabla.cov X Y).dir f p := by
    rw [(nabla.cov X Y).dir_mul p (hconst.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
    have hz : (nabla.cov X Y).dir (fun _ : M => c) p = 0 := by
      change mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => c) p ((nabla.cov X Y) p) = 0
      rw [mfderiv_const]
      rfl
    rw [hz]
    ring
  unfold hessian
  rw [hXY, hC]
  ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [CompactSpace M] [Nonempty M] in
/-- **Math.** A constant scalar factor pulls through the pointwise Hessian. -/
theorem hessianAt_const_mul
    (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (c : ℝ) (p : M)
    (v w : TangentSpace I p) :
    hessianAt nabla (fun q => c * f q) p v w =
      c * hessianAt nabla f p v w := by
  simp only [hessianAt_def]
  exact hessian_const_mul nabla hf c _ _ _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [CompactSpace M] [Nonempty M] in
/-- **Math.** A constant scalar factor pulls through the scalar Laplacian. -/
theorem scalarLaplacianAt_const_mul
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (c : ℝ) (p : M) :
    laplacianAt g nabla (fun q => c * f q) p =
      c * laplacianAt g nabla f p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold laplacianAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact hessianAt_const_mul nabla hf c p _ _

omit [CompleteSpace E] [CompactSpace M] [Nonempty M] in
/-- **Math.** A constant scalar factor pulls through the rank-zero rough
Laplacian. -/
theorem scalarRoughLaplacian_const_mul
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (c : ℝ) (p : M) :
    scalarRoughLaplacian g nabla (fun q => c * f q) p =
      c * scalarRoughLaplacian g nabla f p := by
  rw [scalarRoughLaplacian_eq_laplacianAt,
    scalarRoughLaplacian_eq_laplacianAt]
  exact scalarLaplacianAt_const_mul g nabla hf c p

omit [CompleteSpace E] [CompactSpace M] [Nonempty M] in
/-- **Math.** The rank-zero rough Laplacian is nonpositive at a spatial maximum
of a smooth scalar tensor field. -/
theorem scalarRoughLaplacian_nonpositive_at_max
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hmax : IsMaxOn f (univ : Set M) x) :
    scalarRoughLaplacian g nabla f x ≤ 0 := by
  rw [scalarRoughLaplacian_eq_laplacianAt]
  exact (laplacianAt_nonpos_of_isLocalMax g nabla hf
    (isLocalMaxOn_univ_iff.mp hmax.localize)).2

omit [CompleteSpace E] [CompactSpace M] [Nonempty M] in
/-- **Math.** At a maximum of a scalarization by a fixed real normal, the
rank-zero rough Laplacian has nonpositive pairing with that normal. -/
theorem scalarRoughLaplacian_inner_nonpositive_at_max
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {n : ℝ} {x : M}
    (hmax : IsMaxOn (fun y => ⟪n, f y⟫_ℝ) (univ : Set M) x) :
    ⟪n, scalarRoughLaplacian g nabla f x⟫_ℝ ≤ 0 := by
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => n * f y) :=
    contMDiff_const.mul hf
  have hmax' : IsMaxOn (fun y => n * f y) (univ : Set M) x := by
    intro y hy
    have h := hmax hy
    simpa [real_inner_comm, mul_comm] using h
  have hnon := scalarRoughLaplacian_nonpositive_at_max g nabla hscalar hmax'
  rw [scalarRoughLaplacian_const_mul g nabla hf n x] at hnon
  simpa [real_inner_comm, mul_comm] using hnon

end MorganTianLib
