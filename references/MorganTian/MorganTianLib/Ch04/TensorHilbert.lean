import MorganTianLib.Ch04.TensorCoordinates
import MorganTianLib.Ch04.TensorContraction

/-!
# The Hilbert norm on covariant tensor fibres

The full array of components in an orthonormal basis equips covariant tensors
with their Euclidean tensor norm. `WithLp` keeps this norm distinct from the
operator norm of `ContinuousMultilinearMap`. The canonical linear equivalence
back to continuous multilinear forms is a homeomorphism in finite dimension.

This is the tensor-fibre metric needed in the supporting-functional argument
of Morgan--Tian Section 4.3.3.
-/

open scoped InnerProductSpace

noncomputable section

namespace MorganTianLib

/-- **Math.** Covariant tensors with the Hilbert norm on their full component array. -/
abbrev HilbertCovariantTensor (k : ℕ) (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  WithLp 2 (CovariantTensorFiber k V)

variable {k : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- **Math.** Read a tensor in the standard orthonormal basis of the underlying space. -/
def hilbertCovariantTensorCoordinates :
    HilbertCovariantTensor k V ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin k → Fin (Module.finrank ℝ V)) :=
  (WithLp.linearEquiv 2 ℝ (CovariantTensorFiber k V)).trans
    (covariantTensorOrthonormalCoordinates (stdOrthonormalBasis ℝ V))

instance hilbertCovariantTensorNormedAddCommGroup :
    NormedAddCommGroup (HilbertCovariantTensor k V) :=
  NormedAddCommGroup.induced _ _ hilbertCovariantTensorCoordinates
    hilbertCovariantTensorCoordinates.injective

instance hilbertCovariantTensorInnerProductSpace :
    InnerProductSpace ℝ (HilbertCovariantTensor k V) :=
  InnerProductSpace.induced hilbertCovariantTensorCoordinates

instance hilbertCovariantTensorFinite : Module.Finite ℝ (HilbertCovariantTensor k V) :=
  Module.Finite.equiv (WithLp.linearEquiv 2 ℝ (CovariantTensorFiber k V)).symm

/-- **Math.** The Hilbert and operator norms induce the same topology on finite tensors. -/
def hilbertCovariantTensorEquiv :
    HilbertCovariantTensor k V ≃L[ℝ] CovariantTensorFiber k V :=
  (WithLp.linearEquiv 2 ℝ (CovariantTensorFiber k V)).toContinuousLinearEquiv

@[simp] theorem hilbertCovariantTensorEquiv_apply (A : HilbertCovariantTensor k V) :
    hilbertCovariantTensorEquiv A = A.ofLp := rfl

/-- **Math.** The Hilbert pairing is full contraction in any orthonormal basis. -/
theorem hilbertCovariantTensor_inner_eq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : HilbertCovariantTensor k V) :
    ⟪A, B⟫_ℝ = covariantTensorComponentInner b A.ofLp B.ofLp := by
  change ⟪hilbertCovariantTensorCoordinates A,
    hilbertCovariantTensorCoordinates B⟫_ℝ = _
  rw [PiLp.inner_apply]
  have h := covariantTensorComponentInner_basis_independent
    (stdOrthonormalBasis ℝ V) b A.ofLp B.ofLp
  simpa [hilbertCovariantTensorCoordinates, covariantTensorComponentInner,
    mul_comm] using h

/-- **Math.** The squared Hilbert norm is the sum of the squares of all components. -/
theorem hilbertCovariantTensor_norm_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A : HilbertCovariantTensor k V) :
    ‖A‖ ^ 2 = ∑ a : Fin k → ι, (A.ofLp (fun j => b (a j))) ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ), hilbertCovariantTensor_inner_eq b]
  simp [covariantTensorComponentInner, pow_two]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- **Math.** Isometric tangent transport induces an isometry for the Hilbert tensor norm. -/
def hilbertCovariantTensorTransportEquiv (k : ℕ) (e : V ≃ₗᵢ[ℝ] W) :
    HilbertCovariantTensor k V ≃ₗᵢ[ℝ] HilbertCovariantTensor k W :=
  ((WithLp.linearEquiv 2 ℝ (CovariantTensorFiber k V)).trans
      ((covariantTensorTransportEquiv k e).toLinearEquiv.trans
        (WithLp.linearEquiv 2 ℝ (CovariantTensorFiber k W)).symm)).isometryOfInner
    (fun A B => by
      rw [hilbertCovariantTensor_inner_eq (stdOrthonormalBasis ℝ W),
        hilbertCovariantTensor_inner_eq (stdOrthonormalBasis ℝ V)]
      exact covariantTensorComponentInner_transport
        (stdOrthonormalBasis ℝ V) (stdOrthonormalBasis ℝ W) e A.ofLp B.ofLp)

@[simp] theorem hilbertCovariantTensorTransportEquiv_ofLp
    (e : V ≃ₗᵢ[ℝ] W) (A : HilbertCovariantTensor k V) :
    (hilbertCovariantTensorTransportEquiv k e A).ofLp =
      covariantTensorTransportEquiv k e A.ofLp := rfl

section Parallel

open Bundle Manifold Riemannian
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/-- **Math.** Intrinsic Levi--Civita transport along a curve is isometric for the full
tensor Hilbert norm. No regularity in the endpoints is asserted here. -/
def parallelTransportHilbertCovariantTensorEquiv
    (g : RiemannianMetric I M) (k : ℕ) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    HilbertCovariantTensor k (TangentSpace I (c a)) ≃ₗᵢ[ℝ]
      HilbertCovariantTensor k (TangentSpace I (c b)) :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  hilbertCovariantTensorTransportEquiv k (parallelTransportTangentIsometryEquiv g hab hc)

@[simp] theorem parallelTransportHilbertCovariantTensorEquiv_ofLp
    (g : RiemannianMetric I M) (k : ℕ) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ A : HilbertCovariantTensor k (TangentSpace I (c a)),
      (parallelTransportHilbertCovariantTensorEquiv g k hab hc A).ofLp =
        parallelTransportCovariantTensorEquiv g k hab hc A.ofLp := by
  intro A
  rfl

end Parallel

end MorganTianLib
