import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import OpenGALib.Riemannian.Manifold.DoCarmoCh1
import OpenGALib.Riemannian.Manifold.DoCarmoCh6ConstantCurvature

/-!
# The flat Euclidean model: ℝⁿ as ambient Riemannian manifold

do Carmo's ambient space for the classical examples of Chapter 6 (the sphere
`Sⁿ ⊂ ℝⁿ⁺¹` of Example 2.8, hypersurfaces of Example 2.4, the Theorema
Egregium of Remark 2.7) is `ℝⁿ` with its canonical metric and connection. This
file provides that model on an arbitrary real inner-product space `F`, viewed
as a manifold over itself (`𝓘(ℝ, F)`):

* `SmoothVectorField.contDiff` — on the vector-space model, smoothness of a
  bundled tangent section is plain smoothness of the raw function `F → F`;
* `DCLieBracket_eq_fderiv` — the manifold Lie bracket is the classical
  `fderiv` commutator `[X, Y] = dY(X) − dX(Y)`;
* `euclideanConnection` — the flat connection `∇_X Y = dY(X)`;
* `euclideanConnection_isLeviCivita` — it is the Levi-Civita connection of the
  Euclidean metric `DCEuclideanMetric` (do Carmo Ch. 2, Example after
  Def. 2.2: the usual derivative is the Riemannian connection of `ℝⁿ`);
* `euclideanConnection_curvature` — its curvature tensor vanishes
  (do Carmo Ch. 4, Example 4.1: `R ≡ 0` for `ℝⁿ`), by symmetry of the second
  derivative;
* `euclideanConnection_isConstantCurvature_zero` — `ℝⁿ` has constant sectional
  curvature `0` in the sense of `AffineConnection.IsConstantCurvature`, the
  form used by the Ch. 6 fundamental equations.

Reference: do Carmo, *Riemannian Geometry*, Ch. 2 §2, Ch. 4 §2, Ch. 6 §2.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace Riemannian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

omit [CompleteSpace F] in
/-- **Math.** On the vector-space model `M = F`, a smooth tangent section *is*
a smooth map `F → F`: the tangent bundle is canonically trivial. -/
theorem SmoothVectorField.contDiff (X : SmoothVectorField 𝓘(ℝ, F) F) :
    ContDiff ℝ ∞ (⇑X : F → F) :=
  contMDiff_vectorSpace_iff_contDiff.mp X.smooth

omit [CompleteSpace F] in
/-- **Math.** Differentiability of the raw function of a smooth field on the
vector-space model. -/
theorem SmoothVectorField.differentiable (X : SmoothVectorField 𝓘(ℝ, F) F) :
    Differentiable ℝ (⇑X : F → F) :=
  X.contDiff.differentiable (by simp)

omit [CompleteSpace F] in
/-- **Math.** On the vector-space model the manifold Lie bracket is the
classical commutator of derivations: `[X, Y](p) = dY_p(X(p)) − dX_p(Y(p))`. -/
theorem DCLieBracket_eq_fderiv (X Y : SmoothVectorField 𝓘(ℝ, F) F) (p : F) :
    DCLieBracket X Y p = fderiv ℝ (⇑Y : F → F) p (X p) - fderiv ℝ (⇑X : F → F) p (Y p) := by
  have h : VectorField.mlieBracket 𝓘(ℝ, F) (⇑X) (⇑Y) = VectorField.lieBracket ℝ (⇑X) (⇑Y) := by
    rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracketWithin_univ]
  show VectorField.mlieBracket 𝓘(ℝ, F) (⇑X) (⇑Y) p = _
  rw [h]
  with_unfolding_all rfl

/-! ## The flat connection `∇_X Y = dY(X)` -/

/-- **Math.** The **flat covariant derivative** of Euclidean space:
`(∇_X Y)(p) = dY_p(X(p))`, the ordinary directional derivative of the field
`Y` along `X`. -/
def euclideanCov (X Y : SmoothVectorField 𝓘(ℝ, F) F) :
    SmoothVectorField 𝓘(ℝ, F) F where
  toFun := fun p => fderiv ℝ (⇑Y : F → F) p (X p)
  smooth := by
    rw [contMDiff_vectorSpace_iff_contDiff]
    exact (Y.contDiff.fderiv_right (by simp)).clm_apply X.contDiff

omit [CompleteSpace F] in
@[simp] theorem euclideanCov_apply (X Y : SmoothVectorField 𝓘(ℝ, F) F) (p : F) :
    euclideanCov X Y p = fderiv ℝ (⇑Y : F → F) p (X p) := rfl

/-- **Math.** do Carmo Ch. 2 §2: the **flat (Euclidean) connection** on `ℝⁿ` —
`∇_X Y = dY(X)`. Additivity and `𝒟`-homogeneity in the direction slot are the
linearity of `dY_p`; additivity and the Leibniz rule in the derived slot are
the sum and product rules for the derivative. -/
def euclideanConnection : AffineConnection 𝓘(ℝ, F) F where
  cov := euclideanCov
  add_left := by
    intro X Y Z
    ext p
    simp only [euclideanCov_apply, SmoothVectorField.add_apply]
    exact (fderiv ℝ (⇑Z : F → F) p).map_add _ _
  smul_left := by
    intro f hf X Z
    ext p
    simp only [euclideanCov_apply, SmoothVectorField.smul_apply]
    exact (fderiv ℝ (⇑Z : F → F) p).map_smul _ _
  add_right := by
    intro X Y Z
    ext p
    have h : fderiv ℝ (fun q => Y q + Z q : F → F) p = fderiv ℝ (⇑Y : F → F) p + fderiv ℝ (⇑Z : F → F) p :=
      fderiv_add (Y.differentiable p) (Z.differentiable p)
    simp only [euclideanCov_apply, SmoothVectorField.add_apply]
    show fderiv ℝ (fun q => Y q + Z q : F → F) p (X p) = _
    rw [h]
    rfl
  leibniz := by
    intro f hf X Y p
    have hfd : DifferentiableAt ℝ f p :=
      ((contMDiff_iff_contDiff.mp hf).differentiable (by simp)) p
    have h : fderiv ℝ (fun q => f q • Y q : F → F) p
        = f p • fderiv ℝ (⇑Y : F → F) p + (fderiv ℝ f p).smulRight (show F from Y p) :=
      fderiv_smul hfd (Y.differentiable p)
    show fderiv ℝ (fun q => f q • Y q : F → F) p (X p) = _
    rw [h]
    have hdir : SmoothVectorField.dir X f p = fderiv ℝ f p (X p) := by
      show mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f p (X p) = fderiv ℝ f p (X p)
      rw [mfderiv_eq_fderiv]
      rfl
    rw [hdir]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.smulRight_apply]
    rfl

omit [CompleteSpace F] in
@[simp] theorem euclideanConnection_cov_apply (X Y : SmoothVectorField 𝓘(ℝ, F) F)
    (p : F) :
    (euclideanConnection (F := F)).cov X Y p = fderiv ℝ (⇑Y : F → F) p (X p) := rfl

/-! ## Levi-Civita for the Euclidean metric -/

/-- **Math.** The flat connection is **symmetric**:
`∇_X Y − ∇_Y X = dY(X) − dX(Y) = [X, Y]`. -/
theorem euclideanConnection_isSymmetric :
    (euclideanConnection (F := F)).IsSymmetric := by
  intro X Y p
  rw [euclideanConnection_cov_apply, euclideanConnection_cov_apply,
    DCLieBracket_eq_fderiv]
  rfl

omit [CompleteSpace F] in
/-- **Math.** The flat connection is **compatible with the Euclidean metric**:
`X⟨Y, Z⟩ = ⟨dY(X), Z⟩ + ⟨Y, dZ(X)⟩`, the product rule for the inner product. -/
theorem euclideanConnection_isMetricCompatible :
    (euclideanConnection (F := F)).IsMetricCompatible (DCEuclideanMetric (F := F)) := by
  intro X Y Z p
  have hinner : fderiv ℝ (fun q => ⟪Y q, Z q⟫) p (X p)
      = ⟪Y p, fderiv ℝ (⇑Z : F → F) p (X p)⟫ + ⟪fderiv ℝ (⇑Y : F → F) p (X p), Z p⟫ :=
    fderiv_inner_apply (𝕜 := ℝ) (Y.differentiable p) (Z.differentiable p) (X p)
  have hdir : SmoothVectorField.dir X (fun q =>
      (DCEuclideanMetric (F := F)).metricInner q (Y q) (Z q)) p
      = fderiv ℝ (fun q => ⟪Y q, Z q⟫) p (X p) := by
    show mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) _ p (X p) = _
    rw [mfderiv_eq_fderiv]
    rfl
  rw [hdir, hinner]
  show ⟪Y p, fderiv ℝ (⇑Z : F → F) p (X p)⟫ + ⟪fderiv ℝ (⇑Y : F → F) p (X p), Z p⟫
    = ⟪fderiv ℝ (⇑Y : F → F) p (X p), Z p⟫ + ⟪Y p, fderiv ℝ (⇑Z : F → F) p (X p)⟫
  ring

/-- **Math.** do Carmo Ch. 2 §2: the usual derivative is the **Levi-Civita
connection of Euclidean space**. -/
theorem euclideanConnection_isLeviCivita :
    (euclideanConnection (F := F)).IsLeviCivita (DCEuclideanMetric (F := F)) :=
  ⟨euclideanConnection_isSymmetric, euclideanConnection_isMetricCompatible⟩

/-! ## Flatness: the curvature tensor of ℝⁿ vanishes -/

/-- **Math.** do Carmo Ch. 4, Example 4.1: the curvature of `ℝⁿ` **vanishes**,
`R(X, Y)Z = ∇_Y∇_X Z − ∇_X∇_Y Z + ∇_{[X,Y]}Z = 0`. The second-order terms
cancel by symmetry of the second derivative (Schwarz), the first-order terms
against the bracket term. -/
theorem euclideanConnection_curvature (X Y Z : SmoothVectorField 𝓘(ℝ, F) F) :
    (euclideanConnection (F := F)).curvature X Y Z = 0 := by
  ext p
  rw [AffineConnection.curvature_apply, SmoothVectorField.zero_apply]
  have hZ' : DifferentiableAt ℝ (fderiv ℝ (⇑Z : F → F)) p :=
    ((contDiff_infty_iff_fderiv.mp Z.contDiff).2.differentiable (by simp)) p
  -- second covariant derivatives via the product rule for `q ↦ dZ_q(V q)`
  have hsecond : ∀ V W : SmoothVectorField 𝓘(ℝ, F) F,
      (euclideanConnection (F := F)).cov W ((euclideanConnection (F := F)).cov V Z) p
        = fderiv ℝ (fderiv ℝ (⇑Z : F → F)) p (W p) (V p)
          + fderiv ℝ (⇑Z : F → F) p (fderiv ℝ (⇑V : F → F) p (W p)) := by
    intro V W
    rw [euclideanConnection_cov_apply]
    have hcong : fderiv ℝ (⇑((euclideanConnection (F := F)).cov V Z) : F → F) p
        = fderiv ℝ (fun q => fderiv ℝ (⇑Z : F → F) q (V q) : F → F) p := rfl
    rw [hcong, fderiv_clm_apply hZ' (V.differentiable p)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply]
    exact add_comm _ _
  rw [hsecond X Y, hsecond Y X, euclideanConnection_cov_apply,
    bracketField_apply, DCLieBracket_eq_fderiv]
  have hschwarz : fderiv ℝ (fderiv ℝ (⇑Z : F → F)) p (Y p) (X p)
      = fderiv ℝ (fderiv ℝ (⇑Z : F → F)) p (X p) (Y p) :=
    (Z.contDiff.contDiffAt.isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.mpr le_top)) (Y p) (X p)
  rw [hschwarz, map_sub]
  abel

/-- **Math.** `ℝⁿ` has **constant sectional curvature `0`** in the four-field
form used by the Ch. 6 fundamental equations
(`AffineConnection.IsConstantCurvature`). -/
theorem euclideanConnection_isConstantCurvature_zero :
    (euclideanConnection (F := F)).IsConstantCurvature (DCEuclideanMetric (F := F)) 0 := by
  intro X Y Z W p
  rw [euclideanConnection_curvature X Y Z, SmoothVectorField.zero_apply]
  rw [(DCEuclideanMetric (F := F)).metricInner_zero_left]
  ring

end Riemannian
