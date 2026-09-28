import MorganTianLib.Ch03.RicciFlow.EvolvingFrame
import MorganTianLib.Ch03.RicciFlow.CurvatureEvolution
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Morgan--Tian Ch. 3 -- curvature components in an evolving frame

This file isolates the finite-arity chain rule used when differentiating
curvature components in the Ricci-dual frame.  The geometric curvature
evolution identity and the existence of the frame are separate inputs; this
module records exactly what the moving-frame differentiation contributes.
-/

noncomputable section

namespace MorganTianLib

open scoped BigOperators ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### The Ricci action of a moving orthonormal frame -/

/-- **Math.** The four-slot contribution of the Ricci endomorphism to a moving
frame component of the curvature form. -/
def evolvingFrameCurvatureRicciAction (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) : ℝ :=
  g.leviCivitaConnection.curvatureFormAt g p
      (ricciEndomorphismAt g p x) y w z
    + g.leviCivitaConnection.curvatureFormAt g p x
        (ricciEndomorphismAt g p y) w z
    + g.leviCivitaConnection.curvatureFormAt g p x y
        (ricciEndomorphismAt g p w) z
    + g.leviCivitaConnection.curvatureFormAt g p x y w
        (ricciEndomorphismAt g p z)

/-- **Math.** Each moving-frame Ricci insertion expands in an orthonormal basis,
so the complete action is the sum of the four Ricci-curvature traces. -/
theorem evolvingFrameCurvatureRicciAction_apply_explicit
    (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    evolvingFrameCurvatureRicciAction g p x y w z =
      ∑ a, g.leviCivitaConnection.curvatureFormAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) y w z *
        ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) a) x
      + ∑ a, g.leviCivitaConnection.curvatureFormAt g p x
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) w z *
        ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) a) y
      + ∑ a, g.leviCivitaConnection.curvatureFormAt g p x y
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) z *
        ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) a) w
      + ∑ a, g.leviCivitaConnection.curvatureFormAt g p x y w
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) *
        ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) a) z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun A B C q => g.koszulDualSection_dual A B C q)
  have halg :=
    g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  have h₁ : g.leviCivitaConnection.curvatureFormAt g p
      (ricciEndomorphismAt g p x) y w z =
      ∑ a, g.leviCivitaConnection.curvatureFormAt g p (e a) y w z *
        ricciTensorAt g p (e a) x := by
    have hexp := sum_inner_smul_stdOrthonormalBasis g p
      (ricciEndomorphismAt g p x)
    conv_lhs => rw [← hexp]
    rw [halg.sum_left Finset.univ
      (fun a ↦ inner ℝ (e a) (ricciEndomorphismAt g p x))
      (fun a ↦ e a) y w z]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [real_inner_comm, inner_ricciEndomorphismAt,
      ricciTensorAt_symm]
    ring
  have h₂ : g.leviCivitaConnection.curvatureFormAt g p x
      (ricciEndomorphismAt g p y) w z =
      ∑ a, g.leviCivitaConnection.curvatureFormAt g p x (e a) w z *
        ricciTensorAt g p (e a) y := by
    have hexp := sum_inner_smul_stdOrthonormalBasis g p
      (ricciEndomorphismAt g p y)
    conv_lhs => rw [← hexp]
    rw [halg.sum_two Finset.univ
      (fun a ↦ inner ℝ (e a) (ricciEndomorphismAt g p y))
      (fun a ↦ e a) x w z]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [real_inner_comm, inner_ricciEndomorphismAt,
      ricciTensorAt_symm]
    ring
  have h₃ : g.leviCivitaConnection.curvatureFormAt g p x y
      (ricciEndomorphismAt g p w) z =
      ∑ a, g.leviCivitaConnection.curvatureFormAt g p x y (e a) z *
        ricciTensorAt g p (e a) w := by
    have hexp := sum_inner_smul_stdOrthonormalBasis g p
      (ricciEndomorphismAt g p w)
    conv_lhs => rw [← hexp]
    rw [halg.sum_three Finset.univ
      (fun a ↦ inner ℝ (e a) (ricciEndomorphismAt g p w))
      (fun a ↦ e a) x y z]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [real_inner_comm, inner_ricciEndomorphismAt,
      ricciTensorAt_symm]
    ring
  have h₄ : g.leviCivitaConnection.curvatureFormAt g p x y w
      (ricciEndomorphismAt g p z) =
      ∑ a, g.leviCivitaConnection.curvatureFormAt g p x y w (e a) *
        ricciTensorAt g p (e a) z := by
    have hexp := sum_inner_smul_stdOrthonormalBasis g p
      (ricciEndomorphismAt g p z)
    conv_lhs => rw [← hexp]
    rw [halg.sum_four Finset.univ
      (fun a ↦ inner ℝ (e a) (ricciEndomorphismAt g p z))
      (fun a ↦ e a) x y w]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [real_inner_comm, inner_ricciEndomorphismAt,
      ricciTensorAt_symm]
    ring
  dsimp [evolvingFrameCurvatureRicciAction]
  rw [h₁, h₂, h₃, h₄]

/-- **Math.** The Ricci action supplied by an evolving orthonormal frame
cancels the four Ricci-curvature traces in the intrinsic curvature correction,
leaving precisely Morgan--Tian's pure quadratic `2 * B` combination. -/
theorem curvatureEvolutionCorrection_add_evolvingFrameCurvatureRicciAction
    (g : RiemannianMetric I M) (X Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    curvatureEvolutionCorrection g ![X, Y, W, Z] p +
        evolvingFrameCurvatureRicciAction g p (X p) (Y p) (W p) (Z p) =
      2 * (curvatureB g p (X p) (Y p) (W p) (Z p)
        - curvatureB g p (X p) (Y p) (Z p) (W p)
        - curvatureB g p (X p) (Z p) (Y p) (W p)
        + curvatureB g p (X p) (W p) (Y p) (Z p)) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have haction := evolvingFrameCurvatureRicciAction_apply_explicit
    g p (X p) (Y p) (W p) (Z p)
  rw [curvatureEvolutionCorrection_apply_explicit]
  dsimp [evolvingFrameCurvatureRicciAction] at haction ⊢
  rw [haction]
  ring

/-! A four-covariant curvature field and its time derivative. -/

structure EvolvingCurvatureData (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V] where
  curvature : ℝ → V [×4]→L[ℝ] ℝ
  curvatureDeriv : ℝ → V [×4]→L[ℝ] ℝ
  curvature_deriv : ∀ t, HasDerivAt curvature (curvatureDeriv t) t

/-- **Math.** The derivative of a curvature component in a moving frame is
the intrinsic curvature derivative plus one term for each moving slot. -/
theorem evolvingFrame_curvatureComponent_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G)
    (C : EvolvingCurvatureData V)
    (slot : Fin 4 → ι) (t : ℝ) :
    HasDerivAt
      (fun s => C.curvature s (fun i => F.frame s (slot i)))
      (C.curvatureDeriv t (fun i => F.frame t (slot i))
        + ∑ i : Fin 4,
            (C.curvature t).toContinuousLinearMap
              (fun j => F.frame t (slot j)) i (F.dualRicci t (F.frame t (slot i)))) t := by
  have hc := (C.curvature_deriv t).hasFDerivAt
  have hf : ∀ i : Fin 4,
      HasFDerivAt (fun s => F.frame s (slot i))
        (ContinuousLinearMap.toSpanSingleton ℝ (F.dualRicci t (F.frame t (slot i)))) t := by
    intro i
    exact (F.frame_deriv t (slot i)).hasFDerivAt
  have h := hc.continuousMultilinearMap_apply hf
  have h' := h.hasDerivAt
  apply h'.congr_deriv
  simp only [add_apply, ContinuousMultilinearMap.apply_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, sum_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply]

end MorganTianLib

end
