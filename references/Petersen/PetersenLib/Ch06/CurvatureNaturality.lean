import PetersenLib.Ch02.ConnectionNaturality
import PetersenLib.Ch03.SectionalCurvature

/-!
# Petersen Ch. 6 -- curvature under a global Riemannian isometry

The covering arguments in Section 6.2 use deck transformations, which are
global Riemannian isometries of the pulled-back metric.  This file supplies the
curvature part of that bridge from the already proved Ch. 2 naturality of the
Levi-Civita connection.  The local-isometry version still requires a separate
restriction argument; no local hypothesis is silently added here.
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

private theorem pushforward_covField
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    (Φ : Diffeomorph I I' M M' ∞) (hiso : PreservesMetric g g' Φ)
    {X Y : Π p : M, TangentSpace I p}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) :
    pushforwardVF Φ (g.leviCivita.toAffineConnection.covField X Y) =
      g'.leviCivita.toAffineConnection.covField (pushforwardVF Φ X)
        (pushforwardVF Φ Y) := by
  have hnat := exercise2_5_12_naturality (g := g) (g' := g') Φ hiso
    (X := Y) (Y := X) hY hX
  change pushforwardVF Φ (fun p => g.leviCivita.cov p (X p) Y) =
    (fun q => g'.leviCivita.cov q (pushforwardVF Φ X q) (pushforwardVF Φ Y))
  exact hnat

/-- Covariant derivatives of smooth fields commute with pushforward by a global
Riemannian isometry. -/
theorem pushforward_covariantDerivative
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    (Φ : Diffeomorph I I' M M' ∞) (hiso : PreservesMetric g g' Φ)
    {X Y : Π p : M, TangentSpace I p}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) :
    pushforwardVF Φ (fun p => g.leviCivita.toAffineConnection.cov p (X p) Y) =
      fun q => g'.leviCivita.toAffineConnection.cov q
        (pushforwardVF Φ X q) (pushforwardVF Φ Y) := by
  exact pushforward_covField Φ hiso hX hY

/-- The `(1,3)` curvature tensor is natural under a global Riemannian isometry. -/
theorem pushforward_curvatureTensor
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    (Φ : Diffeomorph I I' M M' ∞) (hiso : PreservesMetric g g' Φ)
    {X Y Z : Π p : M, TangentSpace I p}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) :
    pushforwardVF Φ (curvatureTensor g.leviCivita.toAffineConnection X Y Z) =
      curvatureTensor g'.leviCivita.toAffineConnection
        (pushforwardVF Φ X) (pushforwardVF Φ Y) (pushforwardVF Φ Z) := by
  have hX' := pushforwardVF_isSmooth Φ hX
  have hY' := pushforwardVF_isSmooth Φ hY
  have hZ' := pushforwardVF_isSmooth Φ hZ
  have hYZ : IsSmoothVectorField
      (g.leviCivita.toAffineConnection.covField Y Z) :=
    g.leviCivita.toAffineConnection.smooth_cov hY hZ
  have hXZ : IsSmoothVectorField
      (g.leviCivita.toAffineConnection.covField X Z) :=
    g.leviCivita.toAffineConnection.smooth_cov hX hZ
  have hYZpush := pushforward_covField Φ hiso hY hZ
  have hXZpush := pushforward_covField Φ hiso hX hZ
  have hfirst := exercise2_5_12_naturality (g := g) (g' := g') Φ hiso hYZ hX
  have hsecond := exercise2_5_12_naturality (g := g) (g' := g') Φ hiso hXZ hY
  have hbracketSmooth : IsSmoothVectorField (lieDerivativeVectorField I X Y) :=
    hX.lieDerivativeVectorField hY
  have hthird := exercise2_5_12_naturality (g := g) (g' := g') Φ hiso
    (X := Z) (Y := lieDerivativeVectorField I X Y) hZ hbracketSmooth
  have hbracket := pushforwardVF_lieBracket Φ hX hY
  funext q
  obtain ⟨p, rfl⟩ : ∃ p : M, Φ p = q :=
    ⟨Φ.symm q, Φ.apply_symm_apply q⟩
  rw [pushforwardVF_apply]
  rw [curvatureTensor_apply]
  rw [map_sub, map_sub]
  have hfirst_p := congrFun hfirst (Φ p)
  have hsecond_p := congrFun hsecond (Φ p)
  have hthird_p := congrFun hthird (Φ p)
  have hbracket_p := congrFun hbracket (Φ p)
  have hYZ_p := congrFun hYZpush (Φ p)
  have hXZ_p := congrFun hXZpush (Φ p)
  have hfirst_mf := hfirst_p
  have hsecond_mf := hsecond_p
  have hthird_mf := hthird_p
  rw [pushforwardVF_apply] at hfirst_mf hsecond_mf hthird_mf
  have hYZ_arg := congrArg
    (fun V : Π q : M', TangentSpace I' q =>
      g'.leviCivita.cov (Φ p) (pushforwardVF Φ X (Φ p)) V) hYZpush
  have hXZ_arg := congrArg
    (fun V : Π q : M', TangentSpace I' q =>
      g'.leviCivita.cov (Φ p) (pushforwardVF Φ Y (Φ p)) V) hXZpush
  rw [hfirst_mf, hsecond_mf, hthird_mf, hbracket_p, hYZ_arg, hXZ_arg]
  rfl

/-! The `(0,4)` form is the convenient pointwise consequence. -/

theorem pushforward_curvatureTensorFour
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    (Φ : Diffeomorph I I' M M' ∞) (hiso : PreservesMetric g g' Φ)
    {X Y Z W : Π p : M, TangentSpace I p}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (_hW : IsSmoothVectorField W) :
    curvatureTensorFour g'.leviCivita (pushforwardVF Φ X) (pushforwardVF Φ Y)
        (pushforwardVF Φ Z) (pushforwardVF Φ W) =
      (curvatureTensorFour g.leviCivita X Y Z W) ∘ Φ.symm := by
  have hcurv := pushforward_curvatureTensor Φ hiso hX hY hZ
  funext q
  obtain ⟨p, rfl⟩ : ∃ p : M, Φ p = q :=
    ⟨Φ.symm q, Φ.apply_symm_apply q⟩
  simp only [Function.comp_apply, Φ.symm_apply_apply]
  rw [curvatureTensorFour_apply, curvatureTensorFour_apply]
  have hcurv_p := congrFun hcurv (Φ p)
  rw [pushforwardVF_apply] at hcurv_p
  rw [← hcurv_p]
  rw [pushforwardVF_apply]
  exact metricInner_pushforwardVF Φ hiso p _ _

private theorem bivectorInnerProduct_pushforward
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    (Φ : Diffeomorph I I' M M' ∞) (hiso : PreservesMetric g g' Φ)
    (p : M) (u v w z : TangentSpace I p) :
    bivectorInnerProduct g' (Φ p)
        (mfderiv I I' Φ p u) (mfderiv I I' Φ p v)
        (mfderiv I I' Φ p w) (mfderiv I I' Φ p z) =
      bivectorInnerProduct g p u v w z := by
  simp only [bivectorInnerProduct]
  rw [metricInner_pushforwardVF Φ hiso, metricInner_pushforwardVF Φ hiso,
    metricInner_pushforwardVF Φ hiso, metricInner_pushforwardVF Φ hiso]

/-! A pointwise curvature quotient identity, suitable for transferring bounds. -/

theorem sectionalCurvature_isometry
    {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    (Φ : Diffeomorph I I' M M' ∞) (hiso : PreservesMetric g g' Φ)
    (p : M) (u v : TangentSpace I p) :
    sectionalCurvature g'.leviCivita (Φ p)
        (mfderiv I I' Φ p u) (mfderiv I I' Φ p v) =
      sectionalCurvature g.leviCivita p u v := by
  let X := extendTangentVector p u
  let Y := extendTangentVector p v
  have hX : IsSmoothVectorField X := X.smooth
  have hY : IsSmoothVectorField Y := Y.smooth
  have hX' : IsSmoothVectorField (pushforwardVF Φ X) := pushforwardVF_isSmooth Φ hX
  have hY' : IsSmoothVectorField (pushforwardVF Φ Y) := pushforwardVF_isSmooth Φ hY
  have hfour := pushforward_curvatureTensorFour Φ hiso hY hX hX hY
  have hnum := congrFun hfour (Φ p)
  simp only [Function.comp_apply, Φ.symm_apply_apply] at hnum
  have hleftAt := curvatureTensorFourAt_apply (D := g'.leviCivita)
    (X := pushforwardVF Φ Y) (Y := pushforwardVF Φ X)
    (Z := pushforwardVF Φ X) (W := pushforwardVF Φ Y) hY' hX' hX' (Φ p)
  have hrightAt := curvatureTensorFourAt_apply (D := g.leviCivita)
    (X := Y) (Y := X) (Z := X) (W := Y) hY hX hX p
  have hnumAt :
      curvatureTensorFourAt g'.leviCivita (Φ p)
          ((pushforwardVF Φ Y) (Φ p)) ((pushforwardVF Φ X) (Φ p))
          ((pushforwardVF Φ X) (Φ p)) ((pushforwardVF Φ Y) (Φ p)) =
        curvatureTensorFourAt g.leviCivita p (Y p) (X p) (X p) (Y p) := by
    rw [hleftAt, hrightAt]
    exact hnum
  simp only [pushforwardVF_apply, X, Y, extendTangentVector_apply] at hnumAt
  rw [sectionalCurvature_eq_curvatureTensorFourAt,
    sectionalCurvature_eq_curvatureTensorFourAt]
  rw [hnumAt]
  rw [bivectorInnerProduct_pushforward Φ hiso]

end

end PetersenLib

end
