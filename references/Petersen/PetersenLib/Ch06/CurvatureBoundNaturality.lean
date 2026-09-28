import PetersenLib.Ch06.CurvatureNaturality
import PetersenLib.Ch06.SecBounds

/-!
# Petersen Ch. 6 -- sectional bounds under a global Riemannian isometry

The pointwise curvature identity from `CurvatureNaturality` becomes useful for
comparison hypotheses once tangent vectors are transported through the
bijective differential.  This file records that pullback step explicitly.
-/

open Bundle Set Function
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

section

variable [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
  [LocallyCompactSpace M] [I'.Boundaryless] [CompleteSpace E'] [SigmaCompactSpace M']
  [T2Space M'] [LocallyCompactSpace M']

private theorem diffeomorph_mfderiv_bijective
    (Φ : Diffeomorph I I' M M' ∞) (p : M) :
    Function.Bijective (mfderiv I I' (Φ : M → M') p) := by
  rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ (by norm_num)]
  exact (Φ.mfderivToContinuousLinearEquiv (by norm_num) p).bijective

/-! A global isometry pulls every sectional lower bound back to its source. -/

theorem hasSecBoundedBelow_of_isometry
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    (Φ : Diffeomorph I I' M M' ∞) (hiso : PreservesMetric g g' Φ)
    {k : ℝ} (hsec : HasSecBoundedBelow g'.leviCivita k) :
    HasSecBoundedBelow g.leviCivita k := by
  intro p u v huv
  let A := mfderiv I I' (Φ : M → M') p
  have hA : Function.Bijective A := diffeomorph_mfderiv_bijective Φ p
  have huv' : LinearIndependent ℝ ![A u, A v] := by
    have hmap := huv.map' A.toLinearMap
      (LinearMap.ker_eq_bot_of_injective hA.1)
    change LinearIndependent ℝ (fun i : Fin 2 => A (![u, v] i)) at hmap
    have hvec : (fun i : Fin 2 => A (![u, v] i)) = ![A u, A v] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec] at hmap
    exact hmap
  have hbound := hsec (Φ p) (A u) (A v) huv'
  rw [sectionalCurvature_isometry Φ hiso p u v] at hbound
  exact hbound

/-! The upper-bound version is identical, with the inequality reversed. -/

theorem hasSecBoundedAbove_of_isometry
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    (Φ : Diffeomorph I I' M M' ∞) (hiso : PreservesMetric g g' Φ)
    {K : ℝ} (hsec : HasSecBoundedAbove g'.leviCivita K) :
    HasSecBoundedAbove g.leviCivita K := by
  intro p u v huv
  let A := mfderiv I I' (Φ : M → M') p
  have hA : Function.Bijective A := diffeomorph_mfderiv_bijective Φ p
  have huv' : LinearIndependent ℝ ![A u, A v] := by
    have hmap := huv.map' A.toLinearMap
      (LinearMap.ker_eq_bot_of_injective hA.1)
    change LinearIndependent ℝ (fun i : Fin 2 => A (![u, v] i)) at hmap
    have hvec : (fun i : Fin 2 => A (![u, v] i)) = ![A u, A v] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec] at hmap
    exact hmap
  have hbound := hsec (Φ p) (A u) (A v) huv'
  rw [sectionalCurvature_isometry Φ hiso p u v] at hbound
  exact hbound

/-! The two-sided pinch packages the two preceding transfers. -/

theorem hasSecIn_of_isometry
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    (Φ : Diffeomorph I I' M M' ∞) (hiso : PreservesMetric g g' Φ)
    {k K : ℝ} (hsec : HasSecIn g'.leviCivita k K) :
    HasSecIn g.leviCivita k K :=
  ⟨hasSecBoundedBelow_of_isometry Φ hiso hsec.1,
    hasSecBoundedAbove_of_isometry Φ hiso hsec.2⟩

end

end PetersenLib

end
