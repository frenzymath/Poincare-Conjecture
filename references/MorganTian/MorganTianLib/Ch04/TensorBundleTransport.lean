import MorganTianLib.Ch04.TensorParallelTransport
import MorganTianLib.Ch04.HamiltonMaximumBundle

/-! 
# Morgan--Tian Ch. 4 - induced tensor-bundle frame transport

For a family of fibre isometries from a dependent vector bundle to one model
space, this module constructs the induced transport on covariant tensor fibres.
It proves the transport laws and pulls closed convex model carriers back to a
fiberwise closed, convex, parallel-invariant family.  The frame family remains
an explicit input: these algebraic statements do not assert a smooth
Levi--Civita trivialisation.

The construction is the finite-rank bundle compatibility needed before the
analytic Hamilton barrier can be applied to an actual tensor bundle.
-/

open Set

noncomputable section

set_option linter.unusedSectionVars false

namespace MorganTianLib

section TensorFrame

variable {X E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : X → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℝ (F x)]

/-- **Math.** A model-space frame induces a covariant-tensor frame in every rank. -/
def covariantTensorFrame (k : ℕ)
    (e : FiberFrame (X := X) (E := E) (F := F)) (x : X) :
    CovariantTensorFiber k (F x) ≃ₗᵢ[ℝ] CovariantTensorFiber k E :=
  covariantTensorTransportEquiv k (e x)

@[simp] theorem covariantTensorFrame_apply
    (k : ℕ) (e : FiberFrame (X := X) (E := E) (F := F)) (x : X)
    (A : CovariantTensorFiber k (F x)) :
    covariantTensorFrame k e x A =
      A.compContinuousLinearMap
        (fun _ : Fin k => (e x).symm.toContinuousLinearEquiv) :=
  rfl

/-- **Math.** Transport a covariant tensor from one fibre to another through the model
frame. -/
def covariantTensorFrameTransport (k : ℕ)
    (e : FiberFrame (X := X) (E := E) (F := F)) (x y : X) :
    CovariantTensorFiber k (F x) ≃ₗᵢ[ℝ] CovariantTensorFiber k (F y) :=
  (covariantTensorFrame k e x).trans (covariantTensorFrame k e y).symm

@[simp] theorem covariantTensorFrameTransport_apply
    (k : ℕ) (e : FiberFrame (X := X) (E := E) (F := F)) (x y : X)
    (A : CovariantTensorFiber k (F x)) :
    covariantTensorFrameTransport k e x y A =
      (covariantTensorFrame k e y).symm (covariantTensorFrame k e x A) := by
  rfl

@[simp] theorem covariantTensorFrameTransport_refl
    (k : ℕ) (e : FiberFrame (X := X) (E := E) (F := F)) (x : X) :
    covariantTensorFrameTransport k e x x =
      LinearIsometryEquiv.refl ℝ (CovariantTensorFiber k (F x)) := by
  ext A v
  simp [covariantTensorFrameTransport]

theorem covariantTensorFrameTransport_trans
    (k : ℕ) (e : FiberFrame (X := X) (E := E) (F := F)) (x y z : X) :
    (covariantTensorFrameTransport k e x y).trans
        (covariantTensorFrameTransport k e y z) =
      covariantTensorFrameTransport k e x z := by
  ext A v
  simp [covariantTensorFrameTransport]

/-- **Math.** Pull a model carrier back to every covariant-tensor fibre. -/
def covariantTensorFrameCarrier (k : ℕ)
    (e : FiberFrame (X := X) (E := E) (F := F))
    (Z₀ : Set (CovariantTensorFiber k E)) :
    FiberSet X (fun x => CovariantTensorFiber k (F x)) :=
  fun x => (covariantTensorFrame k e x) ⁻¹' Z₀

@[simp] theorem mem_covariantTensorFrameCarrier_iff
    (k : ℕ) (e : FiberFrame (X := X) (E := E) (F := F))
    (Z₀ : Set (CovariantTensorFiber k E)) (x : X)
    (A : CovariantTensorFiber k (F x)) :
    A ∈ covariantTensorFrameCarrier k e Z₀ x ↔
      covariantTensorFrame k e x A ∈ Z₀ :=
  Iff.rfl

theorem fiberwiseClosed_covariantTensorFrameCarrier
    (k : ℕ) (e : FiberFrame (X := X) (E := E) (F := F))
    {Z₀ : Set (CovariantTensorFiber k E)} (hZ₀ : IsClosed Z₀) :
    fiberwiseClosed (covariantTensorFrameCarrier k e Z₀) := by
  intro x
  exact hZ₀.preimage (covariantTensorFrame k e x).continuous

theorem fiberwiseConvex_covariantTensorFrameCarrier
    (k : ℕ) (e : FiberFrame (X := X) (E := E) (F := F))
    {Z₀ : Set (CovariantTensorFiber k E)} (hZ₀ : Convex ℝ Z₀) :
    fiberwiseConvex (covariantTensorFrameCarrier k e Z₀) := by
  intro x
  exact hZ₀.linear_preimage (covariantTensorFrame k e x).toLinearMap

/-- **Math.** The pulled-back carrier is invariant under all transports induced by the
same frame family. -/
theorem covariantTensorFrameCarrier_parallelInvariant
    (k : ℕ) (e : FiberFrame (X := X) (E := E) (F := F))
    (Z₀ : Set (CovariantTensorFiber k E)) :
    parallelInvariantFiberSet (covariantTensorFrameCarrier k e Z₀)
      (fun x y => {(covariantTensorFrameTransport k e x y).toLinearEquiv}) := by
  intro x y p hp
  have hp_eq : p = (covariantTensorFrameTransport k e x y).toLinearEquiv := by
    simpa using hp
  rw [hp_eq]
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    change covariantTensorFrame k e y
        (covariantTensorFrameTransport k e x y B) ∈ Z₀
    simp [covariantTensorFrameTransport, mem_covariantTensorFrameCarrier_iff] at hB ⊢
    exact hB
  · intro hA
    refine ⟨(covariantTensorFrameTransport k e x y).symm A, ?_, ?_⟩
    · change covariantTensorFrame k e x
        ((covariantTensorFrameTransport k e x y).symm A) ∈ Z₀
      simpa [covariantTensorFrameTransport,
        mem_covariantTensorFrameCarrier_iff] using hA
    · simp

end TensorFrame

end MorganTianLib
