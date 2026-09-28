import MorganTianLib.Ch04.IntrinsicCurvatureReaction
import MorganTianLib.Ch03.RicciFlow.CurvatureBOrthonormalBasis
import MorganTianLib.Ch03.RicciFlow.CurvatureEvolvingFrameEquation

/-!
# Morgan--Tian Ch. 4 - cyclic curvature reaction in an evolving frame

This module connects the intrinsic `curvatureB` reaction used by the evolving
Ricci-flow frame equation to the normalized three-dimensional curvature matrix.
The identification is pointwise; the parabolic maximum-principle argument is
handled by the surrounding Chapter 4 modules.
-/

open Matrix Riemannian Set
open scoped BigOperators ComplexOrder ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** In a three-dimensional orthonormal frame, the geometric `2B`
reaction in the evolving-frame curvature equation is one half of the
normalized curvature-operator square-plus-sharp reaction. -/
theorem ricciFlowFrameCurvatureReaction_cyclic_eq_half_matrixReaction
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (e : OrthonormalBasis (Fin 3) ℝ (TangentSpace I p)) (i j : Fin 3),
    ricciFlowFrameCurvatureReaction g p (fun k => e k)
        ![i + 1, i + 2, j + 1, j + 2] =
      (curvatureOperatorSquare ((2 : ℝ) • ((fun a b : Fin 3 =>
          g.leviCivitaConnection.curvatureFormAt g p
            (e (a + 1)) (e (a + 2)) (e (b + 1)) (e (b + 2))) :
          Matrix (Fin 3) (Fin 3) ℝ)) +
        curvatureOperatorSharp normalizedSo3StructureConstants
          ((2 : ℝ) • ((fun a b : Fin 3 =>
          g.leviCivitaConnection.curvatureFormAt g p
            (e (a + 1)) (e (a + 2)) (e (b + 1)) (e (b + 2))) :
          Matrix (Fin 3) (Fin 3) ℝ))) i j / 2 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro e i j
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y Z q => g.koszulDualSection_dual X Y Z q)
  let hB := g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  let R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ :=
    fun a b c d => g.leviCivitaConnection.curvatureFormAt g p
      (e a) (e b) (e c) (e d)
  have hquad (a b c d : Fin 3) :
      curvatureB g p (e a) (e b) (e c) (e d) =
        quadraticCurvatureB R a b c d := by
    rw [curvatureB_eq_sum_orthonormalBasis g p (e a) (e b) (e c) (e d) e]
    rfl
  have hanti₃₄ : ∀ a b c d, R a b c d = -R a b d c := by
    intro a b c d
    exact hB.antisymm₃₄ (e a) (e b) (e c) (e d)
  have hpair : ∀ a b c d, R a b c d = R c d a b := by
    intro a b c d
    exact hB.pairSwap (e a) (e b) (e c) (e d)
  have hbianchi : ∀ a b c d,
      R a b c d + R a c d b + R a d b c = 0 := by
    intro a b c d
    have hbc : R a d b c = R b c a d := by
      dsimp [R]
      rw [hB.pairSwap]
    have hca : R a c d b = R c a b d := by
      dsimp [R]
      rw [hB.pairSwap]
      rw [hB.antisymm₁₂]
      rw [hB.antisymm₃₄]
      rw [hB.pairSwap]
      ring
    have hb := hB.bianchi (e a) (e b) (e c) (e d)
    linarith [hbc, hca]
  have hreaction := curvatureOperatorReactionTensor_eq_shiFrameQuadratic
    R hanti₃₄ hpair hbianchi (i + 1) (i + 2) (j + 1) (j + 2)
  have hcyclic := curvatureOperatorReactionTensor_cyclic_wedgeCurvatureMatrix hB e i j
  have hmatrix : wedgeCurvatureMatrix hB e =
      (fun a b : Fin 3 => R (a + 1) (a + 2) (b + 1) (b + 2)) := by
    ext a b
    simp [wedgeCurvatureMatrix_apply, R]
  rw [hmatrix] at hcyclic
  simp [ricciFlowFrameCurvatureReaction]
  rw [hquad, hquad, hquad, hquad]
  calc
    _ = 2 * (quadraticCurvatureB R (i + 1) (i + 2) (j + 1) (j + 2)
        + quadraticCurvatureB R (i + 1) (j + 1) (i + 2) (j + 2)
        - quadraticCurvatureB R (i + 1) (i + 2) (j + 2) (j + 1)
        - quadraticCurvatureB R (i + 1) (j + 2) (i + 2) (j + 1)) := by ring
    _ = curvatureOperatorReactionTensor R (i + 1) (i + 2) (j + 1) (j + 2) :=
      hreaction.symm
    _ = _ := by
      exact hcyclic

/-! ## The normalized cyclic matrix equation -/

/-- **Math.** The normalized cyclic curvature matrix in a Ricci-dual frame.  Its entries
are twice the curvature components in the cyclic wedge basis. -/
def ricciFlowFrameCurvatureMatrix
    (g : ℝ → RiemannianMetric I M) (p : M)
    (frame : ℝ → Fin 3 → TangentSpace I p) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => 2 * ricciFlowFrameCurvatureComponent (I := I) g p frame
    ![i + 1, i + 2, j + 1, j + 2] t

/-- **Math.** The cyclic matrix whose entries are twice the rough-Laplacian components. -/
def ricciFlowFrameCurvatureLaplacianMatrix
    (g : RiemannianMetric I M) (p : M)
    (frame : Fin 3 → TangentSpace I p) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => 2 * ricciFlowFrameCurvatureLaplacianComponent (I := I) g p frame
    ![i + 1, i + 2, j + 1, j + 2]

/-- **Math.** In a Ricci-dual evolving frame, the normalized cyclic curvature
matrix satisfies the matrix form of the evolving-frame curvature equation.
The reaction term is exposed in its intrinsic normalized form; the preceding
cyclic reaction theorem identifies it with the square-plus-sharp reaction. -/
theorem hasDerivAt_ricciFlowFrameCurvatureMatrix_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hflow : IsRicciFlowOn g J)
    (alpha p : M) (frame : ℝ → Fin 3 → TangentSpace I p) {t : ℝ}
    (hframe : ∀ a, HasDerivAt (fun s ↦ frame s a)
      (ricciEndomorphismAt (g t) p (frame t a)) t)
    (ht : t ∈ interior J) (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt
      (fun s ↦ ricciFlowFrameCurvatureMatrix (I := I) g p frame s)
      (fun i j =>
        2 * ricciFlowFrameCurvatureLaplacianComponent (I := I)
            (g t) p (frame t) ![i + 1, i + 2, j + 1, j + 2]
          + 2 * ricciFlowFrameCurvatureReaction (I := I)
            (g t) p (frame t) ![i + 1, i + 2, j + 1, j + 2]) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hcomponent :=
    hasDerivAt_ricciFlowFrameCurvatureComponent_of_isRicciFlowOn
      (ι := Fin 3) hflow alpha p frame ![i + 1, i + 2, j + 1, j + 2] hframe ht hp
  have hscaled := hcomponent.const_mul (2 : ℝ)
  change HasDerivAt
    (fun s ↦ 2 * ricciFlowFrameCurvatureComponent (I := I) g p frame
      ![i + 1, i + 2, j + 1, j + 2] s)
    (2 * ricciFlowFrameCurvatureLaplacianComponent (I := I)
        (g t) p (frame t) ![i + 1, i + 2, j + 1, j + 2]
      + 2 * ricciFlowFrameCurvatureReaction (I := I)
        (g t) p (frame t) ![i + 1, i + 2, j + 1, j + 2]) t
  simpa only [mul_add] using hscaled

/-! ## Matrix-reaction form -/

/-- **Math.** In dimension three, the normalized cyclic curvature matrix has
the square-plus-sharp Hamilton reaction.  This is the direct matrix consumer
of the evolving-frame component equation; the Laplacian remains componentwise.
-/
theorem hasDerivAt_ricciFlowFrameCurvatureMatrix_eq_matrixReaction_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hflow : IsRicciFlowOn g J)
    (alpha p : M) (frame : ℝ → Fin 3 → TangentSpace I p) {t : ℝ} :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(g t).toRiemannianMetric⟩
    ∀ (e : OrthonormalBasis (Fin 3) ℝ (TangentSpace I p)),
    (∀ a, HasDerivAt (fun s ↦ frame s a)
      (ricciEndomorphismAt (g t) p (frame t a)) t) →
    (∀ a, frame t a = e a) →
    t ∈ interior J → p ∈ (chartAt H alpha).source →
    HasDerivAt
      (fun s ↦ ricciFlowFrameCurvatureMatrix (I := I) g p frame s)
      (fun i j =>
        2 * ricciFlowFrameCurvatureLaplacianComponent (I := I)
            (g t) p (frame t) ![i + 1, i + 2, j + 1, j + 2]
          + (curvatureOperatorSquare
              ((2 : ℝ) • (fun a b : Fin 3 =>
                (g t).leviCivitaConnection.curvatureFormAt (g t) p
                  (frame t (a + 1)) (frame t (a + 2))
                  (frame t (b + 1)) (frame t (b + 2))))
             + curvatureOperatorSharp normalizedSo3StructureConstants
              ((2 : ℝ) • (fun a b : Fin 3 =>
                (g t).leviCivitaConnection.curvatureFormAt (g t) p
                  (frame t (a + 1)) (frame t (a + 2))
                  (frame t (b + 1)) (frame t (b + 2))))) i j) t := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  intro e hframe hframe_t ht hp
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hcomponent :=
    hasDerivAt_ricciFlowFrameCurvatureComponent_of_isRicciFlowOn
      (ι := Fin 3) hflow alpha p frame ![i + 1, i + 2, j + 1, j + 2]
      hframe ht hp
  have hscaled := hcomponent.const_mul (2 : ℝ)
  change HasDerivAt
    (fun s ↦ 2 * ricciFlowFrameCurvatureComponent (I := I) g p frame
      ![i + 1, i + 2, j + 1, j + 2] s)
    (2 * ricciFlowFrameCurvatureLaplacianComponent (I := I)
        (g t) p (frame t) ![i + 1, i + 2, j + 1, j + 2]
      + (curvatureOperatorSquare
          ((2 : ℝ) • (fun a b : Fin 3 =>
            (g t).leviCivitaConnection.curvatureFormAt (g t) p
              (frame t (a + 1)) (frame t (a + 2))
              (frame t (b + 1)) (frame t (b + 2))))
         + curvatureOperatorSharp normalizedSo3StructureConstants
          ((2 : ℝ) • (fun a b : Fin 3 =>
            (g t).leviCivitaConnection.curvatureFormAt (g t) p
              (frame t (a + 1)) (frame t (a + 2))
              (frame t (b + 1)) (frame t (b + 2))))) i j) t
  have hreaction := ricciFlowFrameCurvatureReaction_cyclic_eq_half_matrixReaction
    (g t) p e i j
  have hft : frame t = (fun a => e a) := funext hframe_t
  have hreaction' :
      ricciFlowFrameCurvatureReaction (I := I) (g t) p (frame t)
          ![i + 1, i + 2, j + 1, j + 2] =
        (curvatureOperatorSquare
            ((2 : ℝ) • (fun a b : Fin 3 =>
              (g t).leviCivitaConnection.curvatureFormAt (g t) p
                (frame t (a + 1)) (frame t (a + 2))
                (frame t (b + 1)) (frame t (b + 2))))
           + curvatureOperatorSharp normalizedSo3StructureConstants
            ((2 : ℝ) • (fun a b : Fin 3 =>
              (g t).leviCivitaConnection.curvatureFormAt (g t) p
                (frame t (a + 1)) (frame t (a + 2))
                (frame t (b + 1)) (frame t (b + 2))))) i j / 2 := by
    simpa [hft] using hreaction
  apply hscaled.congr_deriv
  rw [hreaction']
  ring

end MorganTianLib
