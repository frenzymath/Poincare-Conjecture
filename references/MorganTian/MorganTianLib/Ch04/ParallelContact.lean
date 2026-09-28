import MorganTianLib.Ch04.HamiltonMaximumRoughLaplacian

/-!
# Morgan--Tian Ch. 4 - parallel tuples and second-order contact

The evaluator-level `CovTensorField` used by the Chapter 3 curvature files is
deliberately a function on tuples of smooth vector fields; its multilinearity
is not part of the type.  This file records the two geometric facts needed to
discharge the explicit contact defect from `HamiltonMaximumRoughLaplacian`:

* every field in the chosen tuple is parallel for the affine connection in
  every smooth direction;
* the evaluator vanishes whenever one of its slots is the zero field (the
  zero-slot consequence of genuine multilinearity).

The zero-slot condition is kept as an explicit hypothesis rather than being
silently inferred from the evaluator alias.  The resulting theorem is a
reusable second-order contact producer and identifies the exact bridge needed
when a geometric tensor bundle is connected to the evaluator representation.
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

/-! ### Explicit geometric predicates -/

/-- **Math.** A tuple of smooth vector fields is globally parallel for `nabla`
if every member has zero covariant derivative in every smooth direction.
Writing the equality at the bundled-field level makes the condition global in
the base point and lets the affine-connection locality API be used directly.
-/
def IsGloballyParallelTuple (nabla : AffineConnection I M)
    {k : ℕ} (Y : Fin k → SmoothVectorField I M) : Prop :=
  ∀ i : Fin k, ∀ X : SmoothVectorField I M,
    nabla.cov X (Y i) = 0

/-- **Math.** An evaluator-level covariant tensor vanishes whenever one input
slot is the zero smooth vector field.  This is the zero-slot consequence of
multilinearity; it is explicit because `CovTensorField` itself is an
evaluator alias and does not carry multilinearity in its type.
-/
def CovTensorFieldVanishesOnZeroSlot {k : ℕ}
    (A : CovTensorField I M k) : Prop :=
  ∀ (W : Fin k → SmoothVectorField I M) (i : Fin k),
    W i = 0 → A W = 0

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem isGloballyParallelTuple_iff
    (nabla : AffineConnection I M) {k : ℕ}
    (Y : Fin k → SmoothVectorField I M) :
    IsGloballyParallelTuple nabla Y ↔
      ∀ i : Fin k, ∀ X : SmoothVectorField I M,
        nabla.cov X (Y i) = 0 :=
  Iff.rfl

/-! ### Zero-slot consequences for one covariant derivative -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private theorem covTensorField_eq_zero_of_slot_eq_zero
    {k : ℕ} (A : CovTensorField I M k)
    (hzero : CovTensorFieldVanishesOnZeroSlot A)
    (W : Fin k → SmoothVectorField I M) (j : Fin k)
    (hWj : W j = 0) :
    A W = 0 := by
  exact hzero W j hWj

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** If a tuple has a zero slot, its covariant derivative is zero
when the evaluator is multilinear in the zero-slot sense.  The proof checks
that the covariant derivative correction terms retain that zero slot, using
the affine connection's zero-field API.
-/
theorem covTensorDerivAlong_eq_zero_of_zeroSlot
    (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {k : ℕ} (A : CovTensorField I M k)
    (hzero : CovTensorFieldVanishesOnZeroSlot A)
    (W : Fin k → SmoothVectorField I M) (j : Fin k)
    (hWj : W j = 0) :
    covTensorDerivAlong nabla X A W = 0 := by
  funext p
  unfold covTensorDerivAlong
  have hAW : A W = 0 := covTensorField_eq_zero_of_slot_eq_zero A hzero W j hWj
  rw [hAW]
  have hcov0 : nabla.cov X (0 : SmoothVectorField I M) = 0 := by
    ext q
    exact nabla.cov_zero_right X q
  have hterm : ∀ i : Fin k,
      A (Function.update W i (nabla.cov X (W i))) p = 0 := by
    intro i
    have hA := covTensorField_eq_zero_of_slot_eq_zero A hzero
      (Function.update W i (nabla.cov X (W i))) j
    by_cases hij : i = j
    · subst i
      have hslot : Function.update W j (nabla.cov X (W j)) j = 0 := by
        rw [Function.update_self, hWj, hcov0]
      exact congrFun (hA hslot) p
    · exact congrFun (hA (by
        rw [Function.update_of_ne (Ne.symm hij)]
        exact hWj)) p
  rw [Finset.sum_eq_zero (fun i hi => hterm i)]
  have hdir_zero : X.dir (0 : M → ℝ) p = 0 := by
    change mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) p (X p) = 0
    rw [mfderiv_const]
    rfl
  simp [hdir_zero]

/-! ### Vanishing of the traced contact defect -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A globally parallel tuple and an evaluator satisfying the
explicit zero-slot tensor law have zero traced second-order contact defect.
Every term in the explicit defect is discharged: frame corrections vanish by
the zero-slot law, outer derivatives of those corrections are derivatives of
the zero function, and each inner covariant derivative vanishes because its
tuple retains a zero slot.
-/
theorem roughLaplacianContactDefect_eq_zero_of_globallyParallelTuple
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M)
    (hparallel : IsGloballyParallelTuple nabla Y)
    (hzero : CovTensorFieldVanishesOnZeroSlot A) (p : M) :
    roughLaplacianContactDefect g nabla A Y p = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold roughLaplacianContactDefect
  apply Finset.sum_eq_zero
  intro i hi
  let Xi : SmoothVectorField I M :=
    extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  have hXi : IsGloballyParallelTuple nabla Y := hparallel
  have hframe : covTensorFrameCorrection nabla Xi A Y = 0 := by
    funext q
    unfold covTensorFrameCorrection
    apply Finset.sum_eq_zero
    intro j hj
    have hA := covTensorField_eq_zero_of_slot_eq_zero A hzero
      (Function.update Y j (nabla.cov Xi (Y j))) j
    exact congrFun (hA (by simp [hXi j Xi])) q
  have houter : covTensorOuterFrameDefect nabla Xi A Y p = 0 := by
    unfold covTensorOuterFrameDefect
    rw [hframe]
    simp
  have hinner : ∀ j : Fin k,
      covTensorDerivAlong nabla Xi A
        (Function.update Y j (nabla.cov Xi (Y j))) p = 0 := by
    intro j
    have hD := covTensorDerivAlong_eq_zero_of_zeroSlot nabla Xi A hzero
      (Function.update Y j (nabla.cov Xi (Y j))) j
    exact congrFun (hD (by simp [hXi j Xi])) p
  have hlast : covTensorFrameCorrection nabla
      (nabla.cov Xi Xi) A Y p = 0 := by
    have hframe' : covTensorFrameCorrection nabla (nabla.cov Xi Xi) A Y = 0 := by
      funext q
      unfold covTensorFrameCorrection
      apply Finset.sum_eq_zero
      intro j hj
      have hA := covTensorField_eq_zero_of_slot_eq_zero A hzero
        (Function.update Y j (nabla.cov (nabla.cov Xi Xi) (Y j))) j
      exact congrFun (hA (by simp [hXi j (nabla.cov Xi Xi)])) q
    exact congrFun hframe' p
  change covTensorOuterFrameDefect nabla Xi A Y p -
      (∑ j, covTensorDerivAlong nabla Xi A
        (Function.update Y j (nabla.cov Xi (Y j))) p) +
      covTensorFrameCorrection nabla (nabla.cov Xi Xi) A Y p = 0
  rw [houter, Finset.sum_eq_zero (fun j hj => hinner j), hlast]
  ring

omit [CompleteSpace E] in
/-- **Math.** At a spatial maximum of a smooth scalarization by a globally
parallel tensor tuple, the rough Laplacian is nonpositive.  The contact
identity is produced internally from parallelism and the explicit zero-slot
tensor law.
-/
theorem roughLaplacian_apply_nonpositive_at_max
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M)
    (hparallel : IsGloballyParallelTuple nabla Y)
    (hzero : CovTensorFieldVanishesOnZeroSlot A)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (A Y))
    (hmax : IsMaxOn (fun q => A Y q) (univ : Set M) p) :
    roughLaplacian g nabla A Y p ≤ 0 := by
  exact roughLaplacian_apply_nonpositive_at_max_of_contact g nabla A Y p hf hmax
    (roughLaplacianContactDefect_eq_zero_of_globallyParallelTuple
      g nabla A Y hparallel hzero p)

end MorganTianLib
