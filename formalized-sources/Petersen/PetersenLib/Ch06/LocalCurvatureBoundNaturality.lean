import PetersenLib.Ch05.LocalIsometry
import PetersenLib.Ch06.SecBounds

/-!
# Petersen Ch. 6 -- sectional bounds under a local Riemannian isometry

These conditional transfer lemmas isolate the pointwise bridge needed for a
local-isometry curvature argument.  The bridge is an explicit sectional
curvature identity hypothesis; no universal-cover or other hidden global
curvature naturality is assumed.
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

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [I'.Boundaryless] [SigmaCompactSpace M'] [T2Space M']

/-! A local isometry pulls a sectional lower bound back whenever the stated
pointwise curvature identity is available. -/

/-- Transfer `sec ≥ k` through a local Riemannian isometry.

The hypothesis `hcurv` is the explicit pointwise curvature bridge.  It is
deliberately not derived from locality, and in particular carries no hidden
universal-cover assumption. -/
theorem hasSecBoundedBelow_of_local_isometry_of_curvature
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'}
    {F : M → M'} (hF : IsLocalRiemannianIsometry gM gN F)
    (hcurv : ∀ (p : M) (u v : TangentSpace I p),
      sectionalCurvature gN.leviCivita (F p)
          (mfderiv I I' F p u) (mfderiv I I' F p v) =
        sectionalCurvature gM.leviCivita p u v)
    {k : ℝ} (hsec : HasSecBoundedBelow gN.leviCivita k) :
    HasSecBoundedBelow gM.leviCivita k := by
  intro p u v huv
  let A := mfderiv I I' F p
  have hA : Function.Bijective A := hF.bijective_mfderiv p
  have huv' : LinearIndependent ℝ ![A u, A v] := by
    have hmap := huv.map' A.toLinearMap
      (LinearMap.ker_eq_bot_of_injective hA.1)
    change LinearIndependent ℝ (fun i : Fin 2 => A (![u, v] i)) at hmap
    have hvec : (fun i : Fin 2 => A (![u, v] i)) = ![A u, A v] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec] at hmap
    exact hmap
  have hbound := hsec (F p) (A u) (A v) huv'
  rw [hcurv p u v] at hbound
  exact hbound

/-! The upper-bound transfer has the same differential argument. -/

/-- Transfer `sec ≤ K` through a local Riemannian isometry, using the explicit
pointwise curvature identity `hcurv`. -/
theorem hasSecBoundedAbove_of_local_isometry_of_curvature
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'}
    {F : M → M'} (hF : IsLocalRiemannianIsometry gM gN F)
    (hcurv : ∀ (p : M) (u v : TangentSpace I p),
      sectionalCurvature gN.leviCivita (F p)
          (mfderiv I I' F p u) (mfderiv I I' F p v) =
        sectionalCurvature gM.leviCivita p u v)
    {K : ℝ} (hsec : HasSecBoundedAbove gN.leviCivita K) :
    HasSecBoundedAbove gM.leviCivita K := by
  intro p u v huv
  let A := mfderiv I I' F p
  have hA : Function.Bijective A := hF.bijective_mfderiv p
  have huv' : LinearIndependent ℝ ![A u, A v] := by
    have hmap := huv.map' A.toLinearMap
      (LinearMap.ker_eq_bot_of_injective hA.1)
    change LinearIndependent ℝ (fun i : Fin 2 => A (![u, v] i)) at hmap
    have hvec : (fun i : Fin 2 => A (![u, v] i)) = ![A u, A v] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec] at hmap
    exact hmap
  have hbound := hsec (F p) (A u) (A v) huv'
  rw [hcurv p u v] at hbound
  exact hbound

/-! Package the two transfers as a two-sided pinch. -/

/-- Transfer `k ≤ sec ≤ K` through a local Riemannian isometry, provided the
pointwise sectional curvature identity is supplied explicitly. -/
theorem hasSecIn_of_local_isometry_of_curvature
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'}
    {F : M → M'} (hF : IsLocalRiemannianIsometry gM gN F)
    (hcurv : ∀ (p : M) (u v : TangentSpace I p),
      sectionalCurvature gN.leviCivita (F p)
          (mfderiv I I' F p u) (mfderiv I I' F p v) =
        sectionalCurvature gM.leviCivita p u v)
    {k K : ℝ} (hsec : HasSecIn gN.leviCivita k K) :
    HasSecIn gM.leviCivita k K :=
  ⟨hasSecBoundedBelow_of_local_isometry_of_curvature hF hcurv hsec.1,
    hasSecBoundedAbove_of_local_isometry_of_curvature hF hcurv hsec.2⟩

end

end PetersenLib

end
