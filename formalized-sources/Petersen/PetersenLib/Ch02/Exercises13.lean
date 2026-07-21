import PetersenLib.Ch03.Exercises
import PetersenLib.Ch03.CurvatureSymmetries
import PetersenLib.Ch02.CovariantAdjoint
import PetersenLib.Ch03.EuclideanCurvature

/-!
# Petersen Ch. 2, Exercise 2.5.13 — affine vector fields

A vector field `X` is **affine** if `L_X ∇ = 0`.  This file proves part (1) of
Exercise 2.5.13: **every Killing field is affine**.

The proof is the curvature-theoretic one (Petersen expects the reader to know
that a Killing field generates a flow by isometries, hence preserves `∇`; the
formalization instead uses the tensor identities that make that fact concrete):

* the bridging identity `L_X∇(U,V) = R(X,U)V + ∇²_{U,V}X`
  (`lieDerivativeConnection_eq_curvature_add_secondCovariantDerivativeField`, §3.4.19);
* **Kostant's formula** `∇²_{U,V}X = -R(X,U)V` for a Killing field, proved here
  from the skew-symmetry of `S = ∇X` (`IsKillingField.metricInner_cov_skew`),
  the Ricci identity (`curvatureTensor_eq_ricci_identity`), and the first Bianchi
  identity (`curvatureTensor_firstBianchi`), via metric non-degeneracy.

Adding the two gives `L_X∇ = R(X,·)· - R(X,·)· = 0`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Exercise 2.5.13.
-/

open Bundle Set Function Finset Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : RiemannianMetric I M}
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [I.Boundaryless] [CompleteSpace E] in
/-- **Math.** For a Killing field `X`, the second covariant derivative of `X` is
antisymmetric in its last two slots after pairing with the metric:
`g(∇²_{U,V}X, W) = -g(∇²_{U,W}X, V)`.  This differentiates the skew-symmetry of
`S = ∇X` along `U`, and is the key metric input to Kostant's formula. -/
private theorem killing_sndCov_skew_pairing (D : RiemannianConnection I g)
    {X U V W : Π x : M, TangentSpace I x} (hKill : IsKillingField g X)
    (hX : IsSmoothVectorField X) (hU : IsSmoothVectorField U)
    (hV : IsSmoothVectorField V) (hW : IsSmoothVectorField W) (p : M) :
    g.metricInner p (secondCovariantDerivativeField D.toAffineConnection U V X p) (W p)
      = -g.metricInner p (secondCovariantDerivativeField D.toAffineConnection U W X p) (V p) := by
  have hVX : IsSmoothVectorField (D.toAffineConnection.covField V X) :=
    D.toAffineConnection.smooth_cov hV hX
  have hWX : IsSmoothVectorField (D.toAffineConnection.covField W X) :=
    D.toAffineConnection.smooth_cov hW hX
  have hUV : IsSmoothVectorField (D.toAffineConnection.covField U V) :=
    D.toAffineConnection.smooth_cov hU hV
  have hUW : IsSmoothVectorField (D.toAffineConnection.covField U W) :=
    D.toAffineConnection.smooth_cov hU hW
  -- the function `q ↦ ⟨∇_V X, W⟩ + ⟨∇_W X, V⟩` is identically `0` (Killing skew)
  have hf0 : (fun q => g.metricInner q (D.toAffineConnection.covField V X q) (W q))
        + (fun q => g.metricInner q (D.toAffineConnection.covField W X q) (V q))
      = (fun _ => (0 : ℝ)) := by
    funext q
    simp only [Pi.add_apply]
    have hsk := IsKillingField.metricInner_cov_skew D hKill hX hV hW q
    simp only [AffineConnection.covField_apply]
    rw [hsk]; ring
  -- differentiate along `U`: metric compatibility splits each pairing
  have hmc1 := D.metric_compat hVX hW p (U p)
  have hmc2 := D.metric_compat hWX hV p (U p)
  rw [dirTangent_eq_directionalDerivative] at hmc1 hmc2
  have hmdf1 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun q => g.metricInner q (D.toAffineConnection.covField V X q) (W q)) p :=
    g.metricInner_raw_mdifferentiableAt (hVX.mdifferentiableAt (by simp))
      (hW.mdifferentiableAt (by simp))
  have hmdf2 : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun q => g.metricInner q (D.toAffineConnection.covField W X q) (V q)) p :=
    g.metricInner_raw_mdifferentiableAt (hWX.mdifferentiableAt (by simp))
      (hV.mdifferentiableAt (by simp))
  have hd : directionalDerivative U
        (fun q => g.metricInner q (D.toAffineConnection.covField V X q) (W q)) p
      + directionalDerivative U
        (fun q => g.metricInner q (D.toAffineConnection.covField W X q) (V q)) p = 0 := by
    rw [← directionalDerivative_add hmdf1 hmdf2 U, hf0]
    exact directionalDerivative_const U 0 p
  rw [hmc1, hmc2] at hd
  -- expand `∇²` and cancel the `∇_{∇_U V}X` terms via Killing skew
  have hskUV := IsKillingField.metricInner_cov_skew D hKill hX hUV hW p
  have hskUW := IsKillingField.metricInner_cov_skew D hKill hX hUW hV p
  rw [secondCovariantDerivativeField_apply, secondCovariantDerivativeField_apply,
    g.metricInner_sub_left, g.metricInner_sub_left]
  simp only [AffineConnection.covField_apply] at hd hskUV hskUW ⊢
  linarith [hd, hskUV, hskUW]

/-- **Math.** **Kostant's formula** for a Killing field `X`: the second covariant
derivative of `X` is minus the curvature, `∇²_{U,V}X = -R(X,U)V`.  Proved from the
last-two-slot antisymmetry of `∇²X` (`killing_sndCov_skew_pairing`), the Ricci
identity, and the first Bianchi identity, closed by metric non-degeneracy. -/
theorem IsKillingField.secondCovariantDerivativeField_eq_neg_curvature
    (D : RiemannianConnection I g)
    {X U V : Π x : M, TangentSpace I x} (hKill : IsKillingField g X)
    (hX : IsSmoothVectorField X) (hU : IsSmoothVectorField U) (hV : IsSmoothVectorField V)
    (p : M) :
    secondCovariantDerivativeField D.toAffineConnection U V X p
      = -curvatureTensor D.toAffineConnection X U V p := by
  rw [← g.metricInner_eq_iff_eq p]
  intro z
  obtain ⟨Wsm, hWp⟩ := exists_smoothVectorField_eq (I := I) p z
  have hW : IsSmoothVectorField (fun q => Wsm q) := Wsm.smooth
  have hWpp : (fun q => Wsm q) p = z := hWp
  rw [← hWpp, g.metricInner_neg_left, ← curvatureTensorFour_apply]
  set W : Π q : M, TangentSpace I q := fun q => Wsm q
  -- the Ricci identity in the three cyclic slots, paired with the free field
  have ii1 : curvatureTensorFour D U V X W p
      = g.metricInner p (secondCovariantDerivativeField D.toAffineConnection U V X p) (W p)
        - g.metricInner p (secondCovariantDerivativeField D.toAffineConnection V U X p) (W p) := by
    rw [curvatureTensorFour_apply, curvatureTensor_eq_ricci_identity D hU hV X p,
      g.metricInner_sub_left]
  have ii2 : curvatureTensorFour D V W X U p
      = g.metricInner p (secondCovariantDerivativeField D.toAffineConnection V W X p) (U p)
        - g.metricInner p (secondCovariantDerivativeField D.toAffineConnection W V X p) (U p) := by
    rw [curvatureTensorFour_apply, curvatureTensor_eq_ricci_identity D hV hW X p,
      g.metricInner_sub_left]
  have ii3 : curvatureTensorFour D W U X V p
      = g.metricInner p (secondCovariantDerivativeField D.toAffineConnection W U X p) (V p)
        - g.metricInner p (secondCovariantDerivativeField D.toAffineConnection U W X p) (V p) := by
    rw [curvatureTensorFour_apply, curvatureTensor_eq_ricci_identity D hW hU X p,
      g.metricInner_sub_left]
  -- the last-two-slot antisymmetry in the three cyclic slots
  have i1 := killing_sndCov_skew_pairing D hKill hX hU hV hW p
  have i2 := killing_sndCov_skew_pairing D hKill hX hV hW hU p
  have i3 := killing_sndCov_skew_pairing D hKill hX hW hU hV p
  -- the algebraic curvature identity `∑cyc ⟨R(·,·)X,·⟩ = -2⟨R(X,U)V,W⟩`
  have hS : curvatureTensorFour D X W U V p + curvatureTensorFour D X V W U p
      + curvatureTensorFour D X U V W p = 0 := by
    have b := curvatureTensorFour_firstBianchi D hU hV hW X p
    have a1 := curvatureTensorFour_antisymm_right D hU hV hX hW p
    have a2 := curvatureTensorFour_antisymm_right D hW hU hX hV p
    have a3 := curvatureTensorFour_antisymm_right D hV hW hX hU p
    have q1 := curvatureTensorFour_pairSwap D hX hW hU hV p
    have q2 := curvatureTensorFour_pairSwap D hX hV hW hU p
    have q3 := curvatureTensorFour_pairSwap D hX hU hV hW p
    linarith [b, a1, a2, a3, q1, q2, q3]
  have need : curvatureTensorFour D U V X W p - curvatureTensorFour D V W X U p
      + curvatureTensorFour D W U X V p = -2 * curvatureTensorFour D X U V W p := by
    have p1 := curvatureTensorFour_pairSwap D hU hV hX hW p
    have p2 := curvatureTensorFour_pairSwap D hV hW hX hU p
    have p3 := curvatureTensorFour_pairSwap D hW hU hX hV p
    linarith [hS, p1, p2, p3]
  linarith [ii1, ii2, ii3, i1, i2, i3, need]

/-- **Math.** Exercise 2.5.13(1): **a Killing field is affine**, `L_X∇ = 0`.
Combine Kostant's formula for the Killing field with the bridging identity
`L_X∇(U,V) = R(X,U)V + ∇²_{U,V}X`. -/
theorem IsKillingField.lieDerivativeConnection_eq_zero (D : RiemannianConnection I g)
    {X : Π x : M, TangentSpace I x} (hKill : IsKillingField g X) (hX : IsSmoothVectorField X)
    {U V : Π x : M, TangentSpace I x} (hU : IsSmoothVectorField U) (hV : IsSmoothVectorField V)
    (p : M) :
    lieDerivativeConnection D.toAffineConnection X U V p = 0 := by
  rw [lieDerivativeConnection_eq_curvature_add_secondCovariantDerivativeField D hX hU hV p,
    IsKillingField.secondCovariantDerivativeField_eq_neg_curvature D hKill hX hU hV p,
    add_neg_cancel]

/-- **Exercise 2.5.13(1).** Killing fields are affine: for a Killing field `X`,
the Lie derivative of the Levi-Civita connection vanishes, `L_X∇ = 0`. -/
theorem exercise2_5_13 (D : RiemannianConnection I g)
    {X : Π x : M, TangentSpace I x} (hKill : IsKillingField g X) (hX : IsSmoothVectorField X)
    (U V : Π x : M, TangentSpace I x) (hU : IsSmoothVectorField U) (hV : IsSmoothVectorField V)
    (p : M) :
    lieDerivativeConnection D.toAffineConnection X U V p = 0 :=
  IsKillingField.lieDerivativeConnection_eq_zero D hKill hX hU hV p

/-! ## Exercise 2.5.13(2) — an affine field on `ℝⁿ` that is not Killing -/

section EuclideanExample

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F]

/-- **Math.** Exercise 2.5.13(2): the **radial field** `X(x) = x` on Euclidean
space is affine but not Killing.  Its Levi-Civita covariant derivative is the
identity, `∇_V X = V`, so `∇²X = 0`; since Euclidean space is flat this gives
`L_X∇ = R(X,·)· + ∇²X = 0` (affine).  But `(L_X g)(v, v) = 2⟨v,v⟩ ≠ 0`, so `X`
is not Killing. -/
theorem exercise2_5_13_affine_not_killing :
    (∀ (U V : Π x : F, TangentSpace 𝓘(ℝ, F) x),
        IsSmoothVectorField U → IsSmoothVectorField V → ∀ p : F,
        lieDerivativeConnection ((innerProductSpaceMetric F).leviCivita).toAffineConnection
          (fun x => x) U V p = 0)
      ∧ ¬ IsKillingField (innerProductSpaceMetric F) (fun x => x) := by
  have hXsm : IsSmoothVectorField (I := 𝓘(ℝ, F)) (fun x : F => x) :=
    isSmoothVectorField_iff_contDiff.2 contDiff_id
  -- `∇_V X = V` for the radial field `X(x) = x`
  have hcovX : ∀ (V : Π x : F, TangentSpace 𝓘(ℝ, F) x), IsSmoothVectorField V →
      ((innerProductSpaceMetric F).leviCivita).covField V (fun x => x) = V := by
    intro V hV
    funext q
    rw [AffineConnection.covField_apply, leviCivita_cov_eq_euclidean hV hXsm q]
    simp [covariantDerivativeEuclidean_apply, fderiv_id']
  refine ⟨fun U V hU hV p => ?_, ?_⟩
  · -- affine: `L_X∇ = R + ∇²X = 0 + 0`
    have hUV : IsSmoothVectorField (((innerProductSpaceMetric F).leviCivita).covField U V) :=
      ((innerProductSpaceMetric F).leviCivita).smooth_cov hU hV
    have hsnd : secondCovariantDerivativeField
        ((innerProductSpaceMetric F).leviCivita).toAffineConnection U V (fun x => x) p = 0 := by
      rw [secondCovariantDerivativeField_apply, hcovX V hV]
      have h2 : ((innerProductSpaceMetric F).leviCivita).cov p
          (((innerProductSpaceMetric F).leviCivita).covField U V p) (fun x => x)
          = ((innerProductSpaceMetric F).leviCivita).covField U V p := by
        rw [leviCivita_cov_eq_euclidean hUV hXsm p]
        simp [covariantDerivativeEuclidean_apply, fderiv_id']
      rw [h2, ← AffineConnection.covField_apply, sub_self]
    rw [lieDerivativeConnection_eq_curvature_add_secondCovariantDerivativeField _ hXsm hU hV p,
      euclideanSpace_curvature_eq_zero hXsm hU hV p, hsnd, add_zero]
  · -- not Killing: `(L_X g)(v,v) = 2⟨v,v⟩ ≠ 0`
    intro hkill
    rw [killingField_euclidean_characterization] at hkill
    obtain ⟨v, hv⟩ := exists_ne (0 : F)
    have h := hkill 0 v v
    simp only [fderiv_id', ContinuousLinearMap.id_apply] at h
    have hpos := real_inner_self_pos.mpr hv
    linarith

end EuclideanExample

end PetersenLib
