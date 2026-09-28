import MorganTianLib.Ch04.TensorialApplications
import MorganTianLib.Ch04.TensorHilbert
import MorganTianLib.Ch03.RicciFlow.ShiGeometricLevels

/-!
# Covariant tensor fields as tangent-fibre tensors

A tensorial evaluator on smooth vector fields determines a continuous
multilinear form on each tangent fibre. The construction extends tangent
vectors to global smooth fields and uses tensorial locality to prove that the
result is independent of the extensions. The finite component expansion
supplies continuity. Riemann curvature is a concrete consumer of this bridge.

These constructions assert pointwise fibre identities; they do not assert
smoothness of a tensor-bundle section in local trivializations.
-/

open Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A tensor evaluation depends only on the values of all argument fields
at the evaluation point. -/
theorem IsCovariantTensorField.congr_apply {k : ℕ} {A : CovTensorField I M k}
    (hA : IsCovariantTensorField A) {Y Z : Fin k → SmoothVectorField I M} {p : M}
    (hYZ : ∀ i, Y i p = Z i p) : A Y p = A Z p := by
  classical
  have h : ∀ s : Finset (Fin k), A (s.piecewise Y Z) p = A Z p := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.piecewise_insert]
        calc
          A (Function.update (s.piecewise Y Z) i (Y i)) p =
              A (Function.update (s.piecewise Y Z) i ((s.piecewise Y Z) i)) p :=
            hA.congr_slot_apply _ i (by simpa [Finset.piecewise, hi] using hYZ i)
          _ = A Z p := by simpa using ih
  simpa using h Finset.univ

/-- **Math.** The algebraic covariant tensor induced at a point by a tensorial
evaluator on smooth vector fields. -/
def IsCovariantTensorField.toMultilinearMap {k : ℕ} {A : CovTensorField I M k}
    (hA : IsCovariantTensorField A) (p : M) :
    MultilinearMap ℝ (fun _ : Fin k => TangentSpace I p) ℝ where
  toFun v := A (extendVector p ∘ v) p
  map_update_add' {hDecEq} v i x y := by
    cases Subsingleton.elim hDecEq (instDecidableEqFin k)
    simp only [Function.comp_update]
    calc
      A (Function.update (extendVector p ∘ v) i (extendVector p (x + y))) p =
          A (Function.update (extendVector p ∘ v) i
            (extendVector p x + extendVector p y)) p :=
        hA.congr_slot_apply _ i (by simp)
      _ = _ := hA.add_slot _ i _ _ p
  map_update_smul' {hDecEq} v i c x := by
    cases Subsingleton.elim hDecEq (instDecidableEqFin k)
    simp only [Function.comp_update, smul_eq_mul]
    calc
      A (Function.update (extendVector p ∘ v) i (extendVector p (c • x))) p =
          A (Function.update (extendVector p ∘ v) i
            (SmoothVectorField.smul (fun _ => c) contMDiff_const (extendVector p x))) p :=
        hA.congr_slot_apply _ i (by simp)
      _ = _ := hA.smul_slot _ i _ contMDiff_const _ p

/-- **Math.** Evaluating the induced tangent tensor on vector-field values recovers
the original tensor evaluator. -/
@[simp] theorem IsCovariantTensorField.toMultilinearMap_apply {k : ℕ}
    {A : CovTensorField I M k} (hA : IsCovariantTensorField A) (p : M)
    (Y : Fin k → SmoothVectorField I M) :
    hA.toMultilinearMap p (fun i => Y i p) = A Y p := by
  apply hA.congr_apply
  intro i
  exact extendVector_apply p (Y i p)

private def continuousTensorOfMultilinearMap
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] {k : ℕ} (b : OrthonormalBasis ι ℝ V)
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) : CovariantTensorFiber k V :=
  ∑ a : Fin k → ι, T (fun j => b (a j)) • covariantTensorBasisDual b a

private theorem continuousTensorOfMultilinearMap_toMultilinearMap
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [Fintype ι] {k : ℕ} (b : OrthonormalBasis ι ℝ V)
    (T : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    (continuousTensorOfMultilinearMap b T).toMultilinearMap = T := by
  classical
  apply Module.Basis.ext_multilinear (fun _ : Fin k => b.toBasis)
  intro a
  change continuousTensorOfMultilinearMap b T (fun j => b (a j)) = _
  simp [continuousTensorOfMultilinearMap]

/-- **Math.** A smooth tensorial evaluator gives a continuous covariant tensor on
each tangent fibre, with the norm induced by the Riemannian metric. -/
def IsCovariantTensorField.toFiber {k : ℕ} {A : CovTensorField I M k}
    (hA : IsCovariantTensorField A) (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    CovariantTensorFiber k (TangentSpace I p) :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  continuousTensorOfMultilinearMap (stdOrthonormalBasis ℝ (TangentSpace I p))
    (hA.toMultilinearMap p)

/-- **Math.** The continuous tensor on a tangent fibre recovers the original
evaluator on every tuple of smooth fields. -/
@[simp] theorem IsCovariantTensorField.toFiber_apply {k : ℕ}
    {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (g : RiemannianMetric I M) (p : M) (Y : Fin k → SmoothVectorField I M) :
    hA.toFiber g p (fun i => Y i p) = A Y p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := continuousTensorOfMultilinearMap_toMultilinearMap
    (stdOrthonormalBasis ℝ (TangentSpace I p)) (hA.toMultilinearMap p)
  exact (congrArg (fun T : MultilinearMap ℝ (fun _ : Fin k => TangentSpace I p) ℝ =>
    T (fun i => Y i p)) h).trans (hA.toMultilinearMap_apply p Y)

/-- **Math.** The same pointwise covariant tensor, equipped with the full Hilbert
tensor norm rather than the multilinear operator norm. -/
def IsCovariantTensorField.toHilbertFiber {k : ℕ} {A : CovTensorField I M k}
    (hA : IsCovariantTensorField A) (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    HilbertCovariantTensor k (TangentSpace I p) :=
  WithLp.toLp 2 (hA.toFiber g p)

/-- **Math.** Hilbert fibre evaluation agrees with the original covariant evaluator. -/
@[simp] theorem IsCovariantTensorField.toHilbertFiber_apply {k : ℕ}
    {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (g : RiemannianMetric I M) (p : M) (Y : Fin k → SmoothVectorField I M) :
    (hA.toHilbertFiber g p).ofLp (fun i => Y i p) = A Y p :=
  hA.toFiber_apply g p Y

/-- **Math.** The squared Hilbert norm of the induced fibre tensor is exactly the
component energy used in the Chapter 3 Shi derivative tower. -/
theorem IsCovariantTensorField.toHilbertFiber_norm_sq {k : ℕ}
    {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ‖hA.toHilbertFiber g p‖ ^ 2 = covTensorNormSqAt g A p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [hilbertCovariantTensor_norm_sq (stdOrthonormalBasis ℝ (TangentSpace I p))]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have h := hA.toHilbertFiber_apply g p
    (fun j => extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) (a j)))
  simpa only [extendVector_apply, covTensorComponentAt] using h

variable [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

/-- **Math.** Riemann curvature as a Hilbert covariant four-tensor in each tangent fibre. -/
def riemannHilbertTensor (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    HilbertCovariantTensor 4 (TangentSpace I p) :=
  (riemannTensorField_isCovariantTensorField g).toHilbertFiber g p

/-- **Math.** The Hilbert Riemann tensor evaluates to the intrinsic curvature form. -/
@[simp] theorem riemannHilbertTensor_apply (g : RiemannianMetric I M) (p : M)
    (v : Fin 4 → TangentSpace I p) :
    (riemannHilbertTensor g p).ofLp v =
      g.leviCivitaConnection.curvatureFormAt g p (v 0) (v 1) (v 2) (v 3) := by
  have h := (riemannTensorField_isCovariantTensorField g).toHilbertFiber_apply g p
    (extendVector p ∘ v)
  simpa [riemannHilbertTensor, riemannTensorField, Function.comp_def] using h

/-- **Math.** The Hilbert Riemann tensor norm agrees with the zeroth curvature
energy in the intrinsic Shi tower. -/
theorem riemannHilbertTensor_norm_sq (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ‖riemannHilbertTensor g p‖ ^ 2 = riemannCovDerivNormSqAt g 0 p :=
  (riemannTensorField_isCovariantTensorField g).toHilbertFiber_norm_sq g p

end MorganTianLib
