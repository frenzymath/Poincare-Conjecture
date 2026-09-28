import DoCarmoLib.Riemannian.Connection.ParallelAlong
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Topology.Algebra.Module.Multilinear.Topology

/-!
# Morgan--Tian Ch. 4 - covariant tensor transport along curves

This module packages the functorial operation that sends a covariant continuous
multilinear form through an isometric equivalence of its underlying vector
spaces.  It then applies that operation to the endpoint map supplied by
DoCarmo's intrinsic Levi--Civita parallel transport.

The resulting transport is **pathwise**: it compares the fibres at the two
endpoints of one `C^1` curve.  It does not assert spatial smoothness of a
family of transports, construct a normal frame, or provide the contact
identity needed by the global Hamilton tensor maximum principle.  Those are
separate geometric and analytic producers.

## Main definitions

* `CovariantTensorFiber` — real covariant continuous multilinear forms of a
  fixed arity on one normed vector space;
* `covariantTensorTransportEquiv` — the norm-preserving pullback of such forms
  along a linear isometry equivalence;
* `parallelTransportTangentIsometryEquiv` — DoCarmo's endpoint parallel
  transport upgraded to the metric-induced norm on tangent fibres;
* `parallelTransportCovariantTensorEquiv` — the induced pathwise transport of
  covariant tensors along a `C^1` curve.

The multilinear pullback uses Mathlib's
`ContinuousLinearEquiv.continuousMultilinearMapCongrLeft`; no duplicate
congruence equivalence is introduced here.
-/

open Bundle Manifold
open scoped Manifold Topology ContDiff
open Riemannian

noncomputable section

namespace MorganTianLib

/-! ### Fixed-fibre covariant tensors -/

/-- **Math.** A real covariant continuous `k`-linear form on a normed vector space.

The domain is indexed by `Fin k`, which is the finite-arity convention used by
Mathlib's `ContinuousMultilinearMap`. -/
abbrev CovariantTensorFiber (k : ℕ) (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin k => V) ℝ

/-- **Math.** Pull a covariant tensor back through a linear isometry equivalence.

If `e : V ≃ₗᵢ[ℝ] W`, the returned equivalence sends `A` to the form
`(w₁, ..., wₖ) ↦ A(e⁻¹ w₁, ..., e⁻¹ wₖ)`.  Its isometry proof uses the
finite-arity norm identity already provided by Mathlib. -/
noncomputable def covariantTensorTransportEquiv
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (k : ℕ)
    (e : V ≃ₗᵢ[ℝ] W) :
    CovariantTensorFiber k V ≃ₗᵢ[ℝ] CovariantTensorFiber k W := by
  let ce : CovariantTensorFiber k V ≃L[ℝ] CovariantTensorFiber k W :=
    ContinuousLinearEquiv.continuousMultilinearMapCongrLeft ℝ
      (fun _ : Fin k => e.symm.toContinuousLinearEquiv)
  refine LinearIsometryEquiv.mk ce.toLinearEquiv ?_
  intro A
  change ‖A.compContinuousLinearMap
      (fun _ : Fin k => (e.symm : W →L[ℝ] V))‖ = ‖A‖
  exact ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv A
    (fun _ : Fin k => e.symm)

@[simp]
theorem covariantTensorTransportEquiv_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (k : ℕ)
    (e : V ≃ₗᵢ[ℝ] W) (A : CovariantTensorFiber k V) :
    covariantTensorTransportEquiv k e A =
      A.compContinuousLinearMap (fun _ : Fin k => (e.symm : W →L[ℝ] V)) := by
  rfl

@[simp]
theorem covariantTensorTransportEquiv_apply_apply
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (k : ℕ)
    (e : V ≃ₗᵢ[ℝ] W) (A : CovariantTensorFiber k V) (v : Fin k → W) :
    covariantTensorTransportEquiv k e A v = A (fun i => e.symm (v i)) := by
  rfl

/-! ### Metric tangent transport -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/-- **Math.** DoCarmo's endpoint parallel transport, viewed as an isometry for the
metric-induced norms on the two tangent fibres.

The `letI` in the result is intentional: tangent fibres have a metric-dependent
inner-product/norm instance, while the metric itself remains explicit data. -/
noncomputable def parallelTransportTangentIsometryEquiv
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    TangentSpace I (c a) ≃ₗᵢ[ℝ] TangentSpace I (c b) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  refine LinearIsometryEquiv.mk (Riemannian.parallelTransportTangentEquiv g hab hc) ?_
  intro v
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  congr 1
  exact Riemannian.metricInner_parallelTransportTangentEquiv g hab hc v v

@[simp]
theorem parallelTransportTangentIsometryEquiv_apply
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    (v : TangentSpace I (c a)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    parallelTransportTangentIsometryEquiv g hab hc v =
      Riemannian.parallelTransportTangentEquiv g hab hc v := by
  rfl

/-! ### The induced pathwise tensor transport -/

/-- **Math.** Transport a covariant tensor between the endpoints of a `C^1` curve.

This is an endpoint construction along one path.  It carries no claim that
the resulting map varies smoothly with the path or with either endpoint. -/
noncomputable def parallelTransportCovariantTensorEquiv
    (g : RiemannianMetric I M) (k : ℕ) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    CovariantTensorFiber k (TangentSpace I (c a)) ≃ₗᵢ[ℝ]
      CovariantTensorFiber k (TangentSpace I (c b)) :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  covariantTensorTransportEquiv k (parallelTransportTangentIsometryEquiv g hab hc)

@[simp]
theorem parallelTransportCovariantTensorEquiv_apply
    (g : RiemannianMetric I M) (k : ℕ) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (A : CovariantTensorFiber k (TangentSpace I (c a)))
      (v : Fin k → TangentSpace I (c b)),
      parallelTransportCovariantTensorEquiv g k hab hc A v =
        A (fun i => (parallelTransportTangentIsometryEquiv g hab hc).symm (v i)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro A v
  rfl

end MorganTianLib
