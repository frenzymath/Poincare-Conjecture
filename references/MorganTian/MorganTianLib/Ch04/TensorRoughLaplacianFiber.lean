import MorganTianLib.Ch04.LocalTensorSupportLaplacian

/-!
# The rough Laplacian as a tangent-fibre tensor

The metric trace of the corrected second derivative determines a continuous
multilinear tensor in each tangent fibre. Its evaluation agrees with the
Chapter 3 rough Laplacian, so the canonical support contraction gives an
intrinsic Hilbert inner-product inequality.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Riemannian
open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The corrected second covariant derivative in two fixed smooth
directions is a smooth tensor in the remaining slots. -/
theorem IsCovariantTensorField.secondCovDerivAlong
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (nabla : AffineConnection I M) (X Y : SmoothVectorField I M) :
    IsCovariantTensorField (secondCovDerivAlong nabla X Y A) := by
  have hXY := (hA.covTensorDerivAlong nabla Y).covTensorDerivAlong nabla X
  have hconn := hA.covTensorDerivAlong nabla (nabla.cov X Y)
  refine ⟨fun Z => (hXY.contMDiff_eval Z).sub (hconn.contMDiff_eval Z), ?_, ?_⟩
  · intro Z i U V p
    simp only [MorganTianLib.secondCovDerivAlong, hXY.add_slot, hconn.add_slot]
    ring
  · intro Z i f hf U p
    simp only [MorganTianLib.secondCovDerivAlong, hXY.smul_slot Z i f hf U p,
      hconn.smul_slot Z i f hf U p]
    ring

variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The pointwise rough Laplacian tensor, obtained by tracing the
second derivative in a metric orthonormal basis at the point. -/
def IsCovariantTensorField.roughLaplacianFiber
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (g : RiemannianMetric I M) (nabla : AffineConnection I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    CovariantTensorFiber k (TangentSpace I p) :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i : Fin (Module.finrank ℝ (TangentSpace I p)),
    (hA.secondCovDerivAlong nabla
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))).toFiber g p

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

/-- **Math.** Evaluating the pointwise trace tensor recovers the intrinsic
rough Laplacian evaluator on any tuple of smooth vector fields. -/
@[simp] theorem IsCovariantTensorField.roughLaplacianFiber_apply
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (g : RiemannianMetric I M) (nabla : AffineConnection I M) (p : M)
    (Y : Fin k → SmoothVectorField I M) :
    hA.roughLaplacianFiber g nabla p (fun j => Y j p) =
      roughLaplacian g nabla A Y p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [roughLaplacian_apply]
  simp [IsCovariantTensorField.roughLaplacianFiber]

/-- **Math.** The same trace tensor with its full Hilbert tensor norm. -/
def IsCovariantTensorField.roughLaplacianHilbertFiber
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (g : RiemannianMetric I M) (nabla : AffineConnection I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    HilbertCovariantTensor k (TangentSpace I p) :=
  WithLp.toLp 2 (hA.roughLaplacianFiber g nabla p)

/-- **Math.** Hilbert realization preserves the rough Laplacian evaluation. -/
@[simp] theorem IsCovariantTensorField.roughLaplacianHilbertFiber_apply
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (g : RiemannianMetric I M) (nabla : AffineConnection I M) (p : M)
    (Y : Fin k → SmoothVectorField I M) :
    (hA.roughLaplacianHilbertFiber g nabla p).ofLp (fun j => Y j p) =
      roughLaplacian g nabla A Y p :=
  hA.roughLaplacianFiber_apply g nabla p Y

/-- **Math.** At an exterior local maximum of distance from a parallel-invariant
closed convex carrier, an active support normal pairs nonpositively with the
actual rough Laplacian tensor. -/
theorem exists_localLeviCivitaTensor_support_roughLaplacianHilbertFiber_nonpos
    (g : RiemannianMetric I M) (p : M)
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x)),
      (Z p).Nonempty → IsClosed (Z p) → Convex ℝ (Z p) →
      parallelInvariantFiberSet Z (leviCivitaCovariantTensorTransports g k) →
      hA.toFiber g p ∉ Z p →
      IsLocalMax (fun x => Metric.infDist (hA.toHilbertFiber g x)
        (hilbertCovariantTensorEquiv ⁻¹' Z x)) p →
      ∃ q : ConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p),
        ⟪q.1.2, hA.toHilbertFiber g p - q.1.1⟫_ℝ =
          Metric.infDist (hA.toHilbertFiber g p) (hilbertCovariantTensorEquiv ⁻¹' Z p) ∧
        ⟪q.1.2, hA.roughLaplacianHilbertFiber g g.leviCivitaConnection p⟫_ℝ ≤ 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z hne hclosed hconv hparallel hout hmax
  obtain ⟨q, Y, hYp, hq, hlap⟩ :=
    exists_localLeviCivitaTensor_support_roughLaplacian_nonpos g p hA Z
      hne hclosed hconv hparallel hout hmax
  refine ⟨q, hq, ?_⟩
  rw [hilbertCovariantTensor_inner_eq (stdOrthonormalBasis ℝ (TangentSpace I p))]
  convert hlap using 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change hA.roughLaplacianFiber g g.leviCivitaConnection p
    (fun j => stdOrthonormalBasis ℝ (TangentSpace I p) (a j)) = _
  have h := hA.roughLaplacianFiber_apply g g.leviCivitaConnection p
    (fun j => Y (a j))
  simpa only [hYp] using h

end MorganTianLib

#print axioms MorganTianLib.IsCovariantTensorField.roughLaplacianFiber_apply
#print axioms MorganTianLib.exists_localLeviCivitaTensor_support_roughLaplacianHilbertFiber_nonpos
