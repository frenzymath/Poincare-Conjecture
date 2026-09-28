import MorganTianLib.Ch04.TensorParallelTransport
import MorganTianLib.Ch04.TensorCoordinates

/-!
# Morgan--Tian Ch. 4 - spatial tensor transport laws

This module supplies the algebraic and continuity adapter needed after a
spatial family of fibre isometries has been constructed.  The family is kept
as an explicit hypothesis: no smooth Levi--Civita trivialisation is asserted
here.  In particular, the continuity theorem below is a genuine consumer of
such a family, rather than a target-shaped certificate for one.

The transport laws are the identity, reversal, and composition laws for the
covariant tensor pullback from `TensorParallelTransport`.  The final theorem
turns joint continuity of the inverse fibre evaluations into continuity of a
transported tensor section after evaluation on a continuous vector tuple.
This is the scalarized continuity input used by the support-envelope argument.
-/

open scoped Topology

noncomputable section

namespace MorganTianLib

variable {V W U : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-! ### Continuous spatial families -/

/-- **Math.** A family of linear isometries has jointly continuous evaluation
in both directions.  The two evaluations are recorded explicitly because a
pointwise isometry family has no topology on its equivalence-valued codomain
available by default.
-/
def SpatialIsometryFamily {X : Type*} [TopologicalSpace X]
    (P : X → V ≃ₗᵢ[ℝ] W) : Prop :=
  Continuous (fun q : X × V => P q.1 q.2) ∧
    Continuous (fun q : X × W => (P q.1).symm q.2)

/-! ### Tensor transport laws -/

/-- **Math.** Transport through the identity is the identity on covariant
tensors.
-/
@[simp] theorem covariantTensorTransportEquiv_refl (k : ℕ) :
    covariantTensorTransportEquiv k (LinearIsometryEquiv.refl ℝ V) =
      LinearIsometryEquiv.refl ℝ (CovariantTensorFiber k V) := by
  ext A v
  simp

/-- **Math.** Reversing an isometry reverses the induced covariant tensor
transport.
-/
theorem covariantTensorTransportEquiv_symm (k : ℕ) (e : V ≃ₗᵢ[ℝ] W) :
    (covariantTensorTransportEquiv k e).symm =
      covariantTensorTransportEquiv k e.symm := by
  unfold covariantTensorTransportEquiv
  apply LinearIsometryEquiv.ext
  intro A
  change
    ((ContinuousLinearEquiv.continuousMultilinearMapCongrLeft ℝ
      (fun _ : Fin k => e.symm.toContinuousLinearEquiv)).symm A) =
    ContinuousLinearEquiv.continuousMultilinearMapCongrLeft ℝ
      (fun _ : Fin k => e.toContinuousLinearEquiv) A
  rw [ContinuousLinearEquiv.continuousMultilinearMapCongrLeft_symm]
  rfl

/-- **Math.** Consecutive covariant tensor transports compose to the transport
induced by the composite fibre isometry.
-/
theorem covariantTensorTransportEquiv_trans (k : ℕ) (e : V ≃ₗᵢ[ℝ] W)
    (f : W ≃ₗᵢ[ℝ] U) :
    (covariantTensorTransportEquiv k e).trans
        (covariantTensorTransportEquiv k f) =
      covariantTensorTransportEquiv k (e.trans f) := by
  unfold covariantTensorTransportEquiv
  apply LinearIsometryEquiv.ext
  intro A
  change
    (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft ℝ
      (fun _ : Fin k => f.symm.toContinuousLinearEquiv))
      ((ContinuousLinearEquiv.continuousMultilinearMapCongrLeft ℝ
        (fun _ : Fin k => e.symm.toContinuousLinearEquiv)) A) =
      (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft ℝ
        (fun _ : Fin k => (e.trans f).symm.toContinuousLinearEquiv)) A
  apply ContinuousMultilinearMap.ext
  intro v
  simp [ContinuousLinearEquiv.continuousMultilinearMapCongrLeft_apply]

/-! ### Sections and scalarized continuity -/

/-- **Math.** The covariant-tensor section obtained by transporting a section
through a spatial isometry family.
-/
def spatialCovariantTensorTransportSection {X : Type*}
    (k : ℕ) (P : X → V ≃ₗᵢ[ℝ] W)
    (A : X → CovariantTensorFiber k V) : X → CovariantTensorFiber k W :=
  fun x => covariantTensorTransportEquiv k (P x) (A x)

/-- **Math.** Joint continuity of the inverse fibre evaluations and continuity
of the source tensor section imply continuity of every scalar evaluation of the
transported section on a continuous tuple of target vectors.

This is the explicit scalarized regularity adapter used at a support contact;
the hypotheses are the spatial transport and section regularity producers,
not an encoded existence claim for either one.
-/
theorem continuous_spatialCovariantTensorTransportSection_eval
    {X : Type*} [TopologicalSpace X] {k : ℕ}
    {P : X → V ≃ₗᵢ[ℝ] W} (hP : SpatialIsometryFamily P)
    {A : X → CovariantTensorFiber k V} (hA : Continuous A)
    {v : X → Fin k → W} (hv : ∀ i, Continuous (fun x => v x i)) :
    Continuous (fun x =>
      (spatialCovariantTensorTransportSection k P A x) (v x)) := by
  have htuple : Continuous (fun x => fun i => (P x).symm (v x i)) := by
    apply continuous_pi
    intro i
    have hpair : Continuous (fun x : X => (x, v x i)) :=
      continuous_id.prodMk (hv i)
    have hcomp := hP.2.comp hpair
    simpa [SpatialIsometryFamily, Function.comp_def] using hcomp
  have hev : Continuous (fun x => (A x) (fun i => (P x).symm (v x i))) :=
    Continuous.eval hA htuple
  simpa [spatialCovariantTensorTransportSection,
    covariantTensorTransportEquiv_apply_apply] using hev

end MorganTianLib

namespace MorganTianLib

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-! **Math.** A jointly continuous spatial isometry family transports a
continuous covariant-tensor section to a continuous section in the target
fiber.  The proof tests continuity on a finite orthonormal basis of the target
fiber; the resulting basis-coordinate map is a closed embedding, so this is
stronger than continuity of each scalar evaluation alone.

The theorem is an evaluator/transport bridge only.  It does not construct a
smooth family of Levi--Civita frames or identify an arbitrary geometric
trivialization with `P`. -/
theorem continuous_spatialCovariantTensorTransportSection
    {X : Type*} [TopologicalSpace X] {k : ℕ}
    {P : X → V ≃ₗᵢ[ℝ] W} (hP : SpatialIsometryFamily P)
    {A : X → CovariantTensorFiber k V} (hA : Continuous A) :
    Continuous (spatialCovariantTensorTransportSection k P A) := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ W)) ℝ W :=
    stdOrthonormalBasis ℝ W
  let C := covariantTensorBasisEvaluation (k := k) b
  have hCinj : Function.Injective C :=
    covariantTensorBasisEvaluation_injective b
  have hCembed : Topology.IsClosedEmbedding C :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hCinj)
  have hcomp : Continuous
      (C ∘ spatialCovariantTensorTransportSection k P A) := by
    apply continuous_pi
    intro a
    have hv : ∀ i, Continuous (fun _x : X => b (a i)) :=
      fun i => continuous_const
    have he := continuous_spatialCovariantTensorTransportSection_eval
      (k := k) hP hA (v := fun _x i => b (a i)) hv
    simpa [Function.comp_def, C, covariantTensorBasisEvaluation_apply] using he
  exact hCembed.isEmbedding.continuous_iff.mpr hcomp

end MorganTianLib
