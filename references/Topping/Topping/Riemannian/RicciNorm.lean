import MorganTianLib.Ch01.TraceRiccati
import Topping.Riemannian.Curvature

/-!
# The square norm of the Ricci tensor

This module identifies the Ricci tensor with its self-adjoint endomorphism and
applies the trace Cauchy--Schwarz inequality.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The trace-free Ricci tensor, evaluated on two tangent vectors. -/
noncomputable def traceFreeRicciAt (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  ricciTensorAt g p v w -
    scalarCurvatureAt g p / (Module.finrank ℝ E : ℝ) * g.metricInner p v w

/-- **Math.** The Ricci tensor is the sum of its trace-free and pure-trace
parts. -/
theorem ricciTensorAt_eq_traceFreeRicciAt_add (g : RiemannianMetric I M)
    (p : M) (v w : TangentSpace I p) :
    ricciTensorAt g p v w = traceFreeRicciAt g p v w +
      scalarCurvatureAt g p / (Module.finrank ℝ E : ℝ) *
        g.metricInner p v w := by
  simp [traceFreeRicciAt]

/-- **Math.** The self-adjoint endomorphism associated to the Ricci tensor by
the metric. -/
noncomputable def ricciEndomorphismAt (g : RiemannianMetric I M) (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p :=
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  LinearMap.toContinuousLinearMap
    ((Riemannian.rieszInvEquiv (TangentSpace I p)).toLinearMap ∘ₗ
      ricciTensorAt g p)

/-- **Math.** The Ricci endomorphism represents the Ricci bilinear form. -/
theorem inner_ricciEndomorphismAt (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
      ⟨g.toRiemannianMetric⟩
    inner ℝ (ricciEndomorphismAt g p v) w = ricciTensorAt g p v w := by
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  change inner ℝ
    (Riemannian.rieszInvEquiv (TangentSpace I p) (ricciTensorAt g p v)) w = _
  exact Riemannian.rieszInvEquiv_inner (ricciTensorAt g p v) w

/-- **Math.** The Ricci endomorphism is self-adjoint. -/
theorem ricciEndomorphismAt_isSymmetric (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
      ⟨g.toRiemannianMetric⟩
    inner ℝ (ricciEndomorphismAt g p v) w =
      inner ℝ v (ricciEndomorphismAt g p w) := by
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  rw [inner_ricciEndomorphismAt, real_inner_comm,
    inner_ricciEndomorphismAt, ricciTensorAt_symm]

/-- **Math.** The square norm `|Ric|^2`, expressed as the trace of the square of
the self-adjoint Ricci endomorphism. -/
noncomputable def ricciNormSqAt (g : RiemannianMetric I M) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  LinearMap.trace ℝ (TangentSpace I p)
    ↑(ricciEndomorphismAt g p ∘L ricciEndomorphismAt g p)

/-- **Math.** The trace of the Ricci endomorphism is scalar curvature. -/
theorem trace_ricciEndomorphismAt_eq_scalarCurvatureAt
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
      ⟨g.toRiemannianMetric⟩
    LinearMap.trace ℝ (TangentSpace I p) ↑(ricciEndomorphismAt g p) =
      scalarCurvatureAt g p := by
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  rw [scalarCurvatureAt_eq_trace]
  rfl

/-- **Math.** Trace decomposition gives `|Ric|^2 ≥ R^2 / n`, where `n` is
the dimension of the manifold. -/
theorem scalarCurvatureAt_sq_div_finrank_le_ricciNormSqAt
    (g : RiemannianMetric I M) (p : M) :
    scalarCurvatureAt g p ^ 2 / (Module.finrank ℝ E : ℝ) ≤
      ricciNormSqAt g p := by
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  have h := MorganTianLib.sq_trace_le_finrank_mul_trace_comp_self
    (A := ricciEndomorphismAt g p) (ricciEndomorphismAt_isSymmetric g p)
  rw [trace_ricciEndomorphismAt_eq_scalarCurvatureAt] at h
  have hnNat : 0 < Module.finrank ℝ E :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by exact_mod_cast hnNat
  rw [div_le_iff₀ hn]
  have h' : scalarCurvatureAt g p ^ 2 ≤
      (Module.finrank ℝ E : ℝ) * ricciNormSqAt g p := by
    convert h using 1
    all_goals first | apply Subsingleton.elim | rfl
  nlinarith

end Topping
