import OpenGALib.Riemannian.Manifold.EuclideanOpens
import OpenGALib.Riemannian.Manifold.DoCarmoCh6Gauss
import OpenGALib.Riemannian.Manifold.DoCarmoCh6Pointwise

/-!
# do Carmo Chapter 6, Example 2.8 — the sphere `Sⁿ ⊂ ℝⁿ⁺¹` has curvature 1

do Carmo's Example 2.8: the unit sphere `Sⁿ ⊂ ℝⁿ⁺¹`, oriented by the inward
unit normal `N(x) = −x`, has shape operator `S_N = id` (the Gauss map is `−i`,
every tangent vector an eigenvector of eigenvalue `1`), hence constant
sectional curvature `1` by Gauss' theorem.

In the immersed-patch rendering the ambient manifold is the punctured space
`F ∖ {0}` (`punctured F`, an open subset of the Euclidean `F = ℝⁿ⁺¹`; no
constant-rank distribution extends over the origin), and the sphere through
`p` is the leaf of the **concentric-sphere foliation**: the tangent
distribution is `T_pS = (ℝ∙p)^⊥` (`sphereTang`), with orthogonal projection
`v ↦ v − (⟨p,v⟩/⟨p,p⟩) p` (`sphereProj`/`spherePatch`). At points of the unit
sphere `‖p‖ = 1` this is exactly do Carmo's picture of `Sⁿ ⊂ ℝⁿ⁺¹`.

* `spherePatch_secondFundForm_apply` — for `Y` tangent,
  `B(X, Y)(p) = −(⟨X_p, Y_p⟩/⟨p,p⟩) p`: differentiate the tangency identity
  `⟨x, Y(x)⟩ ≡ 0` along `X` (`inner_fderiv_extendZero_of_inner_eq_zero`);
* `spherePatch_secondFundScalarAt` / `spherePatch_shapeOperatorAt` — at
  `‖p‖ = 1`, with inward unit normal `η = −p`: `H_η(x, y) = ⟨x, y⟩` and
  `S_η = id` on `T_pS` — do Carmo's "all eigenvalues equal to 1";
* `spherePatch_inducedCurvature_inner` — for tangent fields orthonormal at
  `p`, `⟨R(X,Y)X, Y⟩(p) = ⟨p,p⟩⁻¹ = 1/‖p‖²` (the sphere of radius `r` has
  curvature `1/r²`), by Gauss' theorem (`thm:dc-ch6-2-5`) against the flat
  ambient;
* `sphere_sectionalCurvature_one` — at `‖p‖ = 1` the sectional curvature is
  constant equal to `1`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 6 §2, Example 2.8.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open TopologicalSpace

/- The whole file works through the canonical identification
`TangentSpace 𝓘(ℝ, F) q = F` on the open submanifold; permit that
definitional abuse globally (as mathlib does where it exploits it). -/
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Riemannian

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Math.** The **punctured space** `F ∖ {0}`, the ambient open submanifold
of Euclidean space carrying the concentric-sphere foliation. -/
def punctured : Opens F :=
  ⟨{x | x ≠ 0}, isOpen_ne⟩

variable {F}

/- On the vector-space model the tangent fibers *are* `F`; expose `F`'s normed
inner-product structure on them so that `ᗮ`-membership and `⟪·,·⟫` elaborate
on fibers. Local to this file (mathlib deliberately puts no canonical norm on
tangent fibers, but here the metric IS the restricted ambient inner product). -/
noncomputable local instance (q : ↥(punctured F)) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ, F) q) :=
  inferInstanceAs (NormedAddCommGroup F)

noncomputable local instance (q : ↥(punctured F)) :
    InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, F) q) :=
  inferInstanceAs (InnerProductSpace ℝ F)

omit [InnerProductSpace ℝ F] in
@[simp] theorem punctured_ne_zero (q : ↥(punctured F)) : (q : F) ≠ 0 := q.2

theorem punctured_inner_self_ne_zero (q : ↥(punctured F)) :
    ⟪(q : F), (q : F)⟫ ≠ 0 :=
  ne_of_gt (real_inner_self_pos.mpr q.2)

/-- **Math.** The tangent space of the concentric sphere through `p`: the
orthogonal complement `(ℝ∙p)^⊥` of the radial line. -/
def sphereTang (p : ↥(punctured F)) : Submodule ℝ F :=
  (ℝ ∙ (p : F))ᗮ

theorem inner_val_eq_zero_of_mem_sphereTang {p : ↥(punctured F)}
    {v : F} (hv : v ∈ sphereTang p) : ⟪(p : F), v⟫ = 0 :=
  (Submodule.mem_orthogonal _ _).mp hv (p : F)
    (Submodule.mem_span_singleton_self _)

/-! ## Differentiating the tangency identity

For a field tangent to the spheres, `⟨x, Y(x)⟩ ≡ 0`; differentiating along `v`
gives `⟨p, dŶ_p(v)⟩ = −⟨v, Y(p)⟩` — the computational heart of do Carmo's
Weingarten identity for the sphere. -/

/-- **Math.** Differentiated tangency: if `⟨x, Y(x)⟩ = 0` on the punctured
space then `⟨p, dŶ_p(v)⟩ = −⟨v, Y(p)⟩`. -/
theorem inner_fderiv_extendZero_of_inner_eq_zero
    {Y : SmoothVectorField 𝓘(ℝ, F) ↥(punctured F)}
    (hYt : ∀ q : ↥(punctured F), ⟪(q : F), Y q⟫ = 0)
    (p : ↥(punctured F)) (v : F) :
    ⟪(p : F), fderiv ℝ ((punctured F).extendZero ⇑Y) p.val v⟫
      = -⟪v, (punctured F).extendZero ⇑Y p.val⟫ := by
  have hYd : DifferentiableAt ℝ ((punctured F).extendZero ⇑Y) p.val :=
    (Y.contDiffAt_extendZero p).differentiableAt (by simp)
  -- the scalar `x ↦ ⟨x, Ŷ(x)⟩` vanishes near `p`
  have hev : (fun x : F => ⟪x, (punctured F).extendZero ⇑Y x⟫)
      =ᶠ[𝓝 p.val] (fun _ => (0 : ℝ)) := by
    filter_upwards [(punctured F).isOpen.mem_nhds p.2] with x hx
    rw [(punctured F).extendZero_apply_of_mem _ hx]
    exact hYt ⟨x, hx⟩
  have hfd : fderiv ℝ (fun x : F => ⟪x, (punctured F).extendZero ⇑Y x⟫)
      p.val = 0 := by
    rw [hev.fderiv_eq]
    exact fderiv_const_apply 0
  have hid : DifferentiableAt ℝ (fun x : F => x) p.val := differentiableAt_id
  have hprod := fderiv_inner_apply (𝕜 := ℝ) hid hYd v
  rw [hfd, fderiv_id'] at hprod
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_id',
    id_eq] at hprod
  linarith [hprod]

/-! ## The radial-orthogonal projection and the foliation patch -/

section Patch

variable [FiniteDimensional ℝ F]

/-- **Math.** The **radial-orthogonal projection** of a field on the punctured
space: `Xᵀ(q) = X(q) − (⟨q, X_q⟩/⟨q,q⟩) q`, the pointwise orthogonal
projection onto `(ℝ∙q)^⊥`, smooth since `⟨q,q⟩ ≠ 0` off the origin. -/
def sphereProj (X : SmoothVectorField 𝓘(ℝ, F) ↥(punctured F)) :
    SmoothVectorField 𝓘(ℝ, F) ↥(punctured F) :=
  SmoothVectorField.ofOpens
    (fun q => (punctured F).extendZero ⇑X q.val
      - (⟪(q : F), (punctured F).extendZero ⇑X q.val⟫ / ⟪(q : F), (q : F)⟫)
        • (q : F))
    (by
      refine contMDiff_opens_of_contDiffAt
        (φ := fun x : F => (punctured F).extendZero ⇑X x
          - (⟪x, (punctured F).extendZero ⇑X x⟫ / ⟪x, x⟫) • x)
        (fun q => rfl) (fun q => ?_)
      have hX : ContDiffAt ℝ ∞ ((punctured F).extendZero ⇑X) q.val :=
        X.contDiffAt_extendZero q
      have hid : ContDiffAt ℝ ∞ (fun x : F => x) q.val := contDiffAt_id
      have hnum : ContDiffAt ℝ ∞
          (fun x : F => ⟪x, (punctured F).extendZero ⇑X x⟫) q.val :=
        hid.inner (𝕜 := ℝ) hX
      have hden : ContDiffAt ℝ ∞ (fun x : F => ⟪x, x⟫) q.val :=
        hid.inner (𝕜 := ℝ) hid
      have hquot : ContDiffAt ℝ ∞
          (fun x : F => ⟪x, (punctured F).extendZero ⇑X x⟫ / ⟪x, x⟫) q.val :=
        hnum.div hden (punctured_inner_self_ne_zero q)
      exact hX.sub (hquot.smul hid))

omit [FiniteDimensional ℝ F] in
/-- **Math.** The value of the radial-orthogonal projection. -/
theorem sphereProj_apply (X : SmoothVectorField 𝓘(ℝ, F) ↥(punctured F))
    (q : ↥(punctured F)) :
    (sphereProj X q : F)
      = (punctured F).extendZero ⇑X q.val
        - (⟪(q : F), (punctured F).extendZero ⇑X q.val⟫ / ⟪(q : F), (q : F)⟫)
          • (q : F) := rfl

omit [FiniteDimensional ℝ F] in
/-- **Math.** The projected field is tangent to the spheres. -/
theorem sphereProj_mem (X : SmoothVectorField 𝓘(ℝ, F) ↥(punctured F))
    (p : ↥(punctured F)) : (sphereProj X p : F) ∈ sphereTang p := by
  refine (Submodule.mem_orthogonal (𝕜 := ℝ) (E := F) _ _).mpr fun u hu => ?_
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [sphereProj_apply, inner_sub_right, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_right,
    div_mul_cancel₀ _ (punctured_inner_self_ne_zero p)]
  ring

omit [FiniteDimensional ℝ F] in
/-- **Math.** The complement `X − Xᵀ` is radial, hence orthogonal to the
sphere: `⟨v, X(p) − Xᵀ(p)⟩ = 0` for `v` tangent at `p`. -/
theorem metricInner_sub_sphereProj (X : SmoothVectorField 𝓘(ℝ, F) ↥(punctured F))
    (p : ↥(punctured F)) {v : TangentSpace 𝓘(ℝ, F) p}
    (hv : (v : F) ∈ sphereTang p) :
    (opensEuclideanMetric (punctured F)).metricInner p v (X p - sphereProj X p)
      = 0 := by
  have hvp : ⟪(p : F), (v : F)⟫ = 0 := inner_val_eq_zero_of_mem_sphereTang hv
  have hvp' : @inner ℝ F _ v ((p : F)) = 0 := by
    rw [real_inner_comm]
    exact hvp
  rw [(opensEuclideanMetric (punctured F)).metricInner_sub_right]
  have h1 : (opensEuclideanMetric (punctured F)).metricInner p v (X p)
      = @inner ℝ F _ v ((punctured F).extendZero ⇑X p.val) := by
    rw [(punctured F).extendZero_val]
    rfl
  have h2 : (opensEuclideanMetric (punctured F)).metricInner p v (sphereProj X p)
      = @inner ℝ F _ v ((punctured F).extendZero ⇑X p.val)
        - (⟪(p : F), (punctured F).extendZero ⇑X p.val⟫ / ⟪(p : F), (p : F)⟫)
          * @inner ℝ F _ v ((p : F)) := by
    show @inner ℝ F _ v ((punctured F).extendZero ⇑X p.val
      - (⟪(p : F), (punctured F).extendZero ⇑X p.val⟫ / ⟪(p : F), (p : F)⟫)
        • (p : F)) = _
    rw [inner_sub_right, real_inner_smul_right]
  rw [h1, h2, hvp']
  ring

/-- **Math.** do Carmo Ch. 6, Ex. 2.8, the identified picture of
`Sⁿ ⊂ ℝⁿ⁺¹`: the **concentric-sphere foliation patch** on the punctured space.
The tangent space of the sphere through `p` is `T_pS = (ℝ∙p)^⊥`, the
orthogonal projection is the radial one, and tangency of brackets follows by
differentiating the tangency identity `⟨x, X(x)⟩ ≡ 0`. -/
def spherePatch : DCImmersedPatch 𝓘(ℝ, F) ↥(punctured F)
    (opensEuclideanMetric (punctured F)) where
  dim := Module.finrank ℝ F - 1
  tang p := sphereTang p
  finrank_tang p := by
    have hspan : Module.finrank ℝ (ℝ ∙ (p : F)) = 1 :=
      finrank_span_singleton p.2
    have hsum := Submodule.finrank_add_finrank_orthogonal (K := ℝ ∙ (p : F))
    rw [hspan] at hsum
    show Module.finrank ℝ ↥((ℝ ∙ (p : F))ᗮ) = Module.finrank ℝ F - 1
    omega
  tangentProj := sphereProj
  tangentProj_mem X p := sphereProj_mem X p
  inner_tangentProj_sub X p v hv := metricInner_sub_sphereProj X p hv
  lieBracket_mem X Y hX hY p := by
    show (DCLieBracket X Y p : F) ∈ (ℝ ∙ (p : F))ᗮ
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hXt : ∀ q : ↥(punctured F), ⟪(q : F), X q⟫ = 0 := fun q =>
      inner_val_eq_zero_of_mem_sphereTang (hX q)
    have hYt : ∀ q : ↥(punctured F), ⟪(q : F), Y q⟫ = 0 := fun q =>
      inner_val_eq_zero_of_mem_sphereTang (hY q)
    have hbr : (DCLieBracket X Y p : F)
        = fderiv ℝ ((punctured F).extendZero ⇑Y) p.val (X p)
          - fderiv ℝ ((punctured F).extendZero ⇑X) p.val (Y p) :=
      DCLieBracket_opens_eq_fderiv X Y p
    have hY' := inner_fderiv_extendZero_of_inner_eq_zero hYt p (X p)
    have hX' := inner_fderiv_extendZero_of_inner_eq_zero hXt p (Y p)
    rw [(punctured F).extendZero_val] at hY' hX'
    rw [hbr, real_inner_smul_left, inner_sub_right, hY', hX',
      real_inner_comm (X p : F) (Y p : F)]
    ring

end Patch

/-! ## The second fundamental form of the sphere -/

section SecondFundForm

variable [FiniteDimensional ℝ F]

/-- **Math.** do Carmo Ch. 6, Ex. 2.8 — the **second fundamental form of the
concentric-sphere foliation**: for `Y` tangent,

`B(X, Y)(p) = −(⟨X_p, Y_p⟩/⟨p,p⟩) p`,

the radial vector weighted by the inner product of the arguments. Obtained by
projecting `∇̄_X Y = dŶ(X)` radially and differentiating the tangency identity
`⟨x, Y(x)⟩ ≡ 0`. -/
theorem spherePatch_secondFundForm_apply
    {Y : SmoothVectorField 𝓘(ℝ, F) ↥(punctured F)}
    (hY : (spherePatch (F := F)).IsTangentField Y)
    (X : SmoothVectorField 𝓘(ℝ, F) ↥(punctured F)) (p : ↥(punctured F)) :
    ((spherePatch (F := F)).secondFundForm opensEuclideanConnection X Y p : F)
      = -(((opensEuclideanMetric (punctured F)).metricInner p (X p) (Y p)
          / ⟪(p : F), (p : F)⟫) • (p : F)) := by
  have hYt : ∀ q : ↥(punctured F), ⟪(q : F), Y q⟫ = 0 := fun q =>
    inner_val_eq_zero_of_mem_sphereTang (hY q)
  -- `B(X,Y)(p) = ∇̄_X Y (p) − (∇̄_X Y)ᵀ(p)`, the radial part of `dŶ(X_p)`
  show (opensEuclideanConnection.cov X Y p : F)
    - (sphereProj (opensEuclideanConnection.cov X Y) p : F) = _
  rw [sphereProj_apply]
  have hcovval : (punctured F).extendZero ⇑(opensEuclideanConnection.cov X Y)
      p.val = fderiv ℝ ((punctured F).extendZero ⇑Y) p.val (X p) := by
    rw [(punctured F).extendZero_val]
    rfl
  have hcov : (opensEuclideanConnection.cov X Y p : F)
      = fderiv ℝ ((punctured F).extendZero ⇑Y) p.val (X p) := rfl
  rw [hcovval, hcov, inner_fderiv_extendZero_of_inner_eq_zero hYt p (X p)]
  have hXY : ⟪(X p : F), (punctured F).extendZero ⇑Y p.val⟫
      = (opensEuclideanMetric (punctured F)).metricInner p (X p) (Y p) := by
    rw [(punctured F).extendZero_val]
    rfl
  rw [hXY, neg_div, neg_smul]
  module

end SecondFundForm

/-! ## Curvature of the spheres: Gauss' theorem against the flat ambient -/

section Curvature

variable [FiniteDimensional ℝ F]

/-- **Math.** do Carmo Ch. 6, Ex. 2.8 (general radius): for tangent fields
`X, Y` orthonormal at `p`, the sectional-curvature numerator of the sphere
through `p` is

`⟨R(X,Y)X, Y⟩(p) = ⟨p,p⟩⁻¹ = 1/‖p‖²`

— the sphere of radius `r` has constant sectional curvature `1/r²`. By Gauss'
theorem (`thm:dc-ch6-2-5`): the ambient is flat, `B(X,X) = B(Y,Y) = −p/⟨p,p⟩`
and `B(X,Y) = 0`, so `K = ⟨B(X,X), B(Y,Y)⟩ − |B(X,Y)|² = ⟨p,p⟩⁻¹`. -/
theorem spherePatch_inducedCurvature_inner
    {X Y : SmoothVectorField 𝓘(ℝ, F) ↥(punctured F)}
    (hX : (spherePatch (F := F)).IsTangentField X)
    (hY : (spherePatch (F := F)).IsTangentField Y)
    (p : ↥(punctured F))
    (hXX : (opensEuclideanMetric (punctured F)).metricInner p (X p) (X p) = 1)
    (hYY : (opensEuclideanMetric (punctured F)).metricInner p (Y p) (Y p) = 1)
    (hXY : (opensEuclideanMetric (punctured F)).metricInner p (X p) (Y p) = 0) :
    (opensEuclideanMetric (punctured F)).metricInner p
        ((spherePatch (F := F)).inducedCurvature opensEuclideanConnection
          X Y X p) (Y p)
      = ⟪(p : F), (p : F)⟫⁻¹ := by
  have hne := punctured_inner_self_ne_zero p
  have hdiff := (spherePatch (F := F)).inducedCurvature_inner_sub_curvature_inner
    opensEuclideanConnection opensEuclideanConnection_isLeviCivita hX hY p
  -- the ambient curvature term vanishes: flat Euclidean ambient
  have hflat : (opensEuclideanMetric (punctured F)).metricInner p
      (opensEuclideanConnection.curvature X Y X p) (Y p) = 0 := by
    rw [opensEuclideanConnection_curvature, SmoothVectorField.zero_apply,
      (opensEuclideanMetric (punctured F)).metricInner_zero_left]
  -- the three second-fundamental-form values
  have hBXX := spherePatch_secondFundForm_apply hX X p
  have hBYY := spherePatch_secondFundForm_apply hY Y p
  have hBXY := spherePatch_secondFundForm_apply hY X p
  rw [hXX] at hBXX
  rw [hYY] at hBYY
  rw [hXY] at hBXY
  -- ⟨B(X,X), B(Y,Y)⟩ = ⟨p,p⟩⁻¹, ⟨B(X,Y), B(X,Y)⟩ = 0
  have h1 : (opensEuclideanMetric (punctured F)).metricInner p
      ((spherePatch (F := F)).secondFundForm opensEuclideanConnection X X p)
      ((spherePatch (F := F)).secondFundForm opensEuclideanConnection Y Y p)
      = ⟪(p : F), (p : F)⟫⁻¹ := by
    show @inner ℝ F _
      ((spherePatch (F := F)).secondFundForm opensEuclideanConnection X X p)
      ((spherePatch (F := F)).secondFundForm opensEuclideanConnection Y Y p)
      = _
    rw [hBXX, hBYY, inner_neg_neg, real_inner_smul_left, real_inner_smul_right]
    field_simp
  have h2 : (opensEuclideanMetric (punctured F)).metricInner p
      ((spherePatch (F := F)).secondFundForm opensEuclideanConnection X Y p)
      ((spherePatch (F := F)).secondFundForm opensEuclideanConnection X Y p)
      = 0 := by
    show @inner ℝ F _
      ((spherePatch (F := F)).secondFundForm opensEuclideanConnection X Y p)
      ((spherePatch (F := F)).secondFundForm opensEuclideanConnection X Y p)
      = _
    rw [hBXY]
    simp
  rw [hflat, sub_zero, h1, h2, sub_zero] at hdiff
  exact hdiff

/-- **Math.** do Carmo Ch. 6, **Example 2.8**: the unit sphere
`Sⁿ ⊂ ℝⁿ⁺¹` has **constant sectional curvature 1** — at every point `p` of
the unit sphere and for every pair of tangent fields orthonormal at `p`,
`⟨R(X,Y)X, Y⟩(p) = 1` (with orthonormal arguments the sectional-curvature
normalization is `1`). -/
theorem sphere_sectionalCurvature_one
    {X Y : SmoothVectorField 𝓘(ℝ, F) ↥(punctured F)}
    (hX : (spherePatch (F := F)).IsTangentField X)
    (hY : (spherePatch (F := F)).IsTangentField Y)
    (p : ↥(punctured F)) (hp : ‖(p : F)‖ = 1)
    (hXX : (opensEuclideanMetric (punctured F)).metricInner p (X p) (X p) = 1)
    (hYY : (opensEuclideanMetric (punctured F)).metricInner p (Y p) (Y p) = 1)
    (hXY : (opensEuclideanMetric (punctured F)).metricInner p (X p) (Y p) = 0) :
    (opensEuclideanMetric (punctured F)).metricInner p
        ((spherePatch (F := F)).inducedCurvature opensEuclideanConnection
          X Y X p) (Y p)
      = 1 := by
  rw [spherePatch_inducedCurvature_inner hX hY p hXX hYY hXY,
    real_inner_self_eq_norm_mul_norm, hp, one_mul, inv_one]

end Curvature

/-! ## The shape operator: do Carmo's "all eigenvalues equal 1"

Orient the unit sphere by the inward unit normal `η = −p`. The scalar second
fundamental form is `H_η(x, y) = ⟨x, y⟩` and the associated self-adjoint
operator is the identity: every `v ∈ T_pSⁿ` is an eigenvector of eigenvalue
`1` — do Carmo's statement that the Gauss map is `−i`. -/

section ShapeOperator

variable [FiniteDimensional ℝ F]

instance : LocallyCompactSpace ↥(punctured F) :=
  (punctured F).isOpen.locallyCompactSpace

/-- **Math.** The inward radial vector `−p` is normal to the sphere at `p`. -/
theorem neg_val_mem_normalSpace (p : ↥(punctured F)) :
    -(p : F) ∈ (spherePatch (F := F)).normalSpace p := by
  intro w hw
  have hwp : ⟪(p : F), (w : F)⟫ = 0 :=
    inner_val_eq_zero_of_mem_sphereTang hw
  show @inner ℝ F _ w (-(p : F)) = 0
  have hwp' : @inner ℝ F _ w ((p : F)) = 0 := by
    rw [real_inner_comm]; exact hwp
  rw [inner_neg_right, hwp', neg_zero]

/-- **Math.** do Carmo Ch. 6, Ex. 2.8: on the unit sphere with inward unit
normal `η = −p`, the scalar second fundamental form is the restricted inner
product, `H_η(x, y) = ⟨x, y⟩` for `y` tangent. -/
theorem spherePatch_secondFundScalarAt (p : ↥(punctured F))
    (hp : ⟪(p : F), (p : F)⟫ = 1) (x : TangentSpace 𝓘(ℝ, F) p)
    {y : TangentSpace 𝓘(ℝ, F) p} (hy : y ∈ (spherePatch (F := F)).tang p) :
    (spherePatch (F := F)).secondFundScalarAt opensEuclideanConnection p
        (-(p : F)) x y
      = (opensEuclideanMetric (punctured F)).metricInner p x y := by
  -- the pointwise `B` through the canonical extensions
  have hB : ((spherePatch (F := F)).secondFundFormAt opensEuclideanConnection
      p x y : F)
      = -(((opensEuclideanMetric (punctured F)).metricInner p x y
          / ⟪(p : F), (p : F)⟫) • (p : F)) := by
    show ((spherePatch (F := F)).secondFundForm opensEuclideanConnection
      (vectorFieldExtension p x)
      ((spherePatch (F := F)).tangentExtension p y) p : F) = _
    rw [spherePatch_secondFundForm_apply
      ((spherePatch (F := F)).isTangentField_tangentExtension p y)
      (vectorFieldExtension p x) p]
    rw [vectorFieldExtension_apply_self,
      (spherePatch (F := F)).tangentExtension_apply_self hy]
  show (opensEuclideanMetric (punctured F)).metricInner p
    ((spherePatch (F := F)).secondFundFormAt opensEuclideanConnection p x y)
    (-(p : F)) = _
  have hswap : (opensEuclideanMetric (punctured F)).metricInner p
      ((spherePatch (F := F)).secondFundFormAt opensEuclideanConnection p x y)
      (-(p : F))
      = @inner ℝ F _
        ((spherePatch (F := F)).secondFundFormAt opensEuclideanConnection p x y)
        (-(p : F)) := rfl
  rw [hswap, hB, inner_neg_neg, real_inner_smul_left, hp, div_one, mul_one]

/-- **Math.** do Carmo Ch. 6, Ex. 2.8: on the unit sphere with inward unit
normal `η = −p`, the **shape operator is the identity** on the tangent space —
every tangent vector is an eigenvector of `S_η` with eigenvalue `1`, so "the
self-adjoint operator associated to `H_η` has all eigenvalues equal to `1`"
(equivalently, the Gauss spherical map is `−i`). -/
theorem spherePatch_shapeOperatorAt (p : ↥(punctured F))
    (hp : ⟪(p : F), (p : F)⟫ = 1) {x : TangentSpace 𝓘(ℝ, F) p}
    (hx : x ∈ (spherePatch (F := F)).tang p) :
    (spherePatch (F := F)).shapeOperatorAt opensEuclideanConnection p
      (-(p : F)) x = x := by
  refine (spherePatch (F := F)).eq_of_inner_eq_of_mem_tang
    ((spherePatch (F := F)).shapeOperatorAt_mem opensEuclideanConnection p
      (-(p : F)) x) hx fun w hw => ?_
  rw [(spherePatch (F := F)).inner_shapeOperatorAt opensEuclideanConnection
    opensEuclideanConnection_isLeviCivita.2 (neg_val_mem_normalSpace p) hw x]
  exact spherePatch_secondFundScalarAt p hp x hw

end ShapeOperator

end Riemannian
