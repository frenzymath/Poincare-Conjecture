/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Jacobi/CovariantCurvatureAlong.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Curvature commutation for families of curves (manifold-free layer)

Ported into DoCarmoLib from the Morgan–Tian / Poincaré Ch.1 spray-linearization
development; this is do Carmo Ch.4 Lemma 4.1 / Ch.5 Prop. 2.2 in local coordinates,
feeding the exponential-differential ↔ Jacobi bridge `cor:dc-ch5-2-5`.

Morgan–Tian derive the Jacobi equation by differentiating the geodesic
equation of a one-parameter family of geodesics and interchanging the two
covariant derivatives, the failure of commutation being exactly the curvature
term (`lem:exponential-differential-jacobi`, and the discussion of families of
geodesics in §1.2). In local coordinates all of this is first-year calculus
for an arbitrary **connection-coefficient map**
`Γ : E → E →L[ℝ] E →L[ℝ] E` (the bilinear Christoffel contraction as a
function of the chart point), with no manifold in sight. This file provides
that manifold-free layer:

* `covDerivAlong Γ u V d p` — the covariant derivative
  `∇_d V = ∂_d V + Γ(∂_d u, V) ∘ u` of a field `V : P → E` along a map
  `u : P → E` of the parameter space `P`, in the direction `d : P`;
* `christoffelCurvature Γ x X Y Z` — the curvature
  `R(X,Y)Z = (∂_XΓ)(Y,Z) − (∂_YΓ)(X,Z) + Γ(X,Γ(Y,Z)) − Γ(Y,Γ(X,Z))`
  of the coefficients `Γ` at `x` (for coordinate fields this is the classical
  `R^l_{ijk} = ∂_iΓ^l_{jk} − ∂_jΓ^l_{ik} + Γ^m_{jk}Γ^l_{im} − Γ^m_{ik}Γ^l_{jm}`,
  in Morgan–Tian's convention `R(X,Y) = ∇_X∇_Y − ∇_Y∇_X` on commuting fields);
* `covDerivAlong_comm` — **curvature commutation**: for `C²` data,
  `∇_{d₁}∇_{d₂}V − ∇_{d₂}∇_{d₁}V = R(∂_{d₁}u, ∂_{d₂}u)V`;
* `covDerivAlong_fderiv_symm` — **torsion-freeness along the family**: for
  symmetric `Γ`, `∇_{d₁}(∂_{d₂}u) = ∇_{d₂}(∂_{d₁}u)`;
* `covDerivAlong_geodesic_family_jacobi` — the **Jacobi equation**: if the
  `t`-lines of a two-parameter family are geodesics (`∇_t ∂_t u = 0` near
  `p`), the variation field `Y = ∂_s u` satisfies
  `∇_t∇_t Y + R(Y, ∂_t u)∂_t u = 0`.

Blueprint: `lem:covariant-commutation-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2
(families of geodesics and Jacobi fields); do Carmo, *Riemannian Geometry*,
Ch. 4, Lemma 4.1 and Ch. 5, Prop. 2.2.
-/

open Set Filter
open scoped Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib.Jacobi

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The covariant derivative along a map and the coefficient curvature -/

/-- **Math.** The **covariant derivative** of the field `V : P → E` along the
map `u : P → E` in the direction `d : P`, with respect to the
connection-coefficient map `Γ` (the chart Christoffel contraction, as a
bilinear continuous map depending on the chart point):
`(∇_d V)(p) = (∂_d V)(p) + Γ_{u(p)}((∂_d u)(p), V(p))`.
For `P = ℝ`, `d = 1` this is the classical coordinate covariant derivative
`DV/dt = V̇ + Γ(u̇, V)(u)` along the curve `u`. -/
def covDerivAlong (Γ : E → E →L[ℝ] E →L[ℝ] E) (u V : P → E) (d : P) (p : P) : E :=
  fderiv ℝ V p d + Γ (u p) (fderiv ℝ u p d) (V p)

theorem covDerivAlong_def (Γ : E → E →L[ℝ] E →L[ℝ] E) (u V : P → E) (d p : P) :
    covDerivAlong Γ u V d p
      = fderiv ℝ V p d + Γ (u p) (fderiv ℝ u p d) (V p) := rfl

/-- **Math.** The **curvature of the connection coefficients** `Γ` at the
point `x`:
`R(X,Y)Z = (∂_XΓ)(Y,Z) − (∂_YΓ)(X,Z) + Γ(X,Γ(Y,Z)) − Γ(Y,Γ(X,Z))`.
For coordinate vector fields this is the classical Christoffel formula
`R^l_{ijk} = ∂_iΓ^l_{jk} − ∂_jΓ^l_{ik} + Γ^m_{jk}Γ^l_{im} − Γ^m_{ik}Γ^l_{jm}`,
i.e. Morgan–Tian's `ℛ(X,Y) = ∇_X∇_Y − ∇_Y∇_X` on commuting fields
(`def:riemann-curvature-tensor`). -/
def christoffelCurvature (Γ : E → E →L[ℝ] E →L[ℝ] E) (x : E) (X Y Z : E) : E :=
  fderiv ℝ Γ x X Y Z - fderiv ℝ Γ x Y X Z + Γ x X (Γ x Y Z) - Γ x Y (Γ x X Z)

/-- **Math.** The covariant derivative at `p` only depends on the germ of the
field at `p`. -/
theorem covDerivAlong_congr (Γ : E → E →L[ℝ] E →L[ℝ] E) (u : P → E)
    {V W : P → E} {p : P} (h : V =ᶠ[𝓝 p] W) (d : P) :
    covDerivAlong Γ u V d p = covDerivAlong Γ u W d p := by
  rw [covDerivAlong_def, covDerivAlong_def, h.fderiv_eq, h.eq_of_nhds]

/-- **Math.** The covariant derivative of the zero field vanishes. -/
theorem covDerivAlong_zero (Γ : E → E →L[ℝ] E →L[ℝ] E) (u : P → E) (d p : P) :
    covDerivAlong Γ u (fun _ => (0 : E)) d p = 0 := by
  rw [covDerivAlong_def]
  simp

/-! ### The first-order expansion of the covariant derivative field -/

/-- **Math.** Directional derivative of the covariant-derivative field: for
`C²` data,
`∂_e(∇_d V) = ∂_e∂_d V + (∂_{∂_e u}Γ)(∂_d u, V) + Γ(∂_e∂_d u, V) + Γ(∂_d u, ∂_e V)`
(chain rule and product rule on `∇_d V = ∂_d V + Γ_u(∂_d u, V)`). -/
theorem fderiv_covDerivAlong_apply {Γ : E → E →L[ℝ] E →L[ℝ] E} {u V : P → E}
    {p : P} (hu : ContDiffAt ℝ 2 u p) (hV : ContDiffAt ℝ 2 V p)
    (hΓ : DifferentiableAt ℝ Γ (u p)) (d e : P) :
    fderiv ℝ (covDerivAlong Γ u V d) p e
      = fderiv ℝ (fderiv ℝ V) p e d
        + fderiv ℝ Γ (u p) (fderiv ℝ u p e) (fderiv ℝ u p d) (V p)
        + Γ (u p) (fderiv ℝ (fderiv ℝ u) p e d) (V p)
        + Γ (u p) (fderiv ℝ u p d) (fderiv ℝ V p e) := by
  have h21 : ((1 : ℕ∞ω) + 1 : ℕ∞ω) ≤ 2 := by norm_num
  have hu1 : DifferentiableAt ℝ u p := hu.differentiableAt (by norm_num)
  have hV1 : DifferentiableAt ℝ V p := hV.differentiableAt (by norm_num)
  have hD2u : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) p) p :=
    ((hu.fderiv_right h21).differentiableAt (by norm_num)).hasFDerivAt
  have hD2V : HasFDerivAt (fderiv ℝ V) (fderiv ℝ (fderiv ℝ V) p) p :=
    ((hV.fderiv_right h21).differentiableAt (by norm_num)).hasFDerivAt
  -- the two directional-derivative fields
  have happV : HasFDerivAt (fun q => fderiv ℝ V q d)
      ((fderiv ℝ (fderiv ℝ V) p).flip d) p := by
    have h := hD2V.clm_apply (hasFDerivAt_const d p)
    simpa using h
  have happu : HasFDerivAt (fun q => fderiv ℝ u q d)
      ((fderiv ℝ (fderiv ℝ u) p).flip d) p := by
    have h := hD2u.clm_apply (hasFDerivAt_const d p)
    simpa using h
  -- the coefficient field along u
  have hΓu : HasFDerivAt (fun q => Γ (u q))
      ((fderiv ℝ Γ (u p)).comp (fderiv ℝ u p)) p := by
    simpa [Function.comp_def] using
      HasFDerivAt.comp (x := p) (g := Γ) (f := u) hΓ.hasFDerivAt hu1.hasFDerivAt
  -- the Christoffel term, by two applications of the CLM product rule
  have hA : HasFDerivAt (fun q => Γ (u q) (fderiv ℝ u q d))
      ((Γ (u p)).comp ((fderiv ℝ (fderiv ℝ u) p).flip d)
        + ((fderiv ℝ Γ (u p)).comp (fderiv ℝ u p)).flip (fderiv ℝ u p d)) p :=
    hΓu.clm_apply happu
  have hG := hA.clm_apply hV1.hasFDerivAt
  have htot : HasFDerivAt (covDerivAlong Γ u V d)
      (((fderiv ℝ (fderiv ℝ V) p).flip d)
        + ((Γ (u p) (fderiv ℝ u p d)).comp (fderiv ℝ V p)
          + ((Γ (u p)).comp ((fderiv ℝ (fderiv ℝ u) p).flip d)
            + ((fderiv ℝ Γ (u p)).comp (fderiv ℝ u p)).flip
                (fderiv ℝ u p d)).flip (V p))) p := by
    exact happV.add hG
  rw [htot.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.flip_apply]
  abel

/-! ### Curvature commutation -/

/-- **Math.** **Curvature commutation for families of curves**: for `C²` data
along a map `u : P → E` of the parameter space,
`∇_{d₁}∇_{d₂}V − ∇_{d₂}∇_{d₁}V = R(∂_{d₁}u, ∂_{d₂}u)V`,
where `R = christoffelCurvature Γ` — the mixed second partials of `V` and `u`
cancel by Schwarz symmetry, leaving exactly the curvature of the connection
coefficients. This is the local-coordinate identity behind Morgan–Tian's
interchange `∇_{Ỹ}∇_{X̃}X̃ → ∇_{X̃}∇_{X̃}Ỹ + ℛ` in the derivation of the
Jacobi equation. Blueprint: `lem:covariant-commutation-jacobi`. -/
theorem covDerivAlong_comm {Γ : E → E →L[ℝ] E →L[ℝ] E} {u V : P → E} {p : P}
    (hu : ContDiffAt ℝ 2 u p) (hV : ContDiffAt ℝ 2 V p)
    (hΓ : DifferentiableAt ℝ Γ (u p)) (d₁ d₂ : P) :
    covDerivAlong Γ u (covDerivAlong Γ u V d₂) d₁ p
      - covDerivAlong Γ u (covDerivAlong Γ u V d₁) d₂ p
      = christoffelCurvature Γ (u p) (fderiv ℝ u p d₁) (fderiv ℝ u p d₂) (V p) := by
  have h1 := fderiv_covDerivAlong_apply hu hV hΓ d₂ d₁
  have h2 := fderiv_covDerivAlong_apply hu hV hΓ d₁ d₂
  have hVs := (hV.isSymmSndFDerivAt (by simp)).eq d₂ d₁
  have hus := (hu.isSymmSndFDerivAt (by simp)).eq d₂ d₁
  rw [covDerivAlong_def Γ u (covDerivAlong Γ u V d₂) d₁ p,
    covDerivAlong_def Γ u (covDerivAlong Γ u V d₁) d₂ p, h1, h2,
    covDerivAlong_def Γ u V d₂ p, covDerivAlong_def Γ u V d₁ p]
  simp only [map_add, christoffelCurvature]
  rw [hVs, hus]
  abel

/-! ### Torsion-freeness: symmetry of the mixed covariant derivative -/

/-- **Math.** For symmetric connection coefficients the mixed covariant
derivatives of the family itself commute: `∇_{d₁}(∂_{d₂}u) = ∇_{d₂}(∂_{d₁}u)`
(Schwarz symmetry of `∂²u` plus symmetry of `Γ`). This is Morgan–Tian's
`∇_{X̃}Ỹ = ∇_{Ỹ}X̃` for the coordinate fields of a family of curves.
Blueprint: `lem:covariant-commutation-jacobi`. -/
theorem covDerivAlong_fderiv_symm {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : P → E}
    {p : P} (hu : ContDiffAt ℝ 2 u p)
    (hΓsymm : ∀ X Y, Γ (u p) X Y = Γ (u p) Y X) (d₁ d₂ : P) :
    covDerivAlong Γ u (fun q => fderiv ℝ u q d₂) d₁ p
      = covDerivAlong Γ u (fun q => fderiv ℝ u q d₁) d₂ p := by
  have h21 : ((1 : ℕ∞ω) + 1 : ℕ∞ω) ≤ 2 := by norm_num
  have hD2u : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) p) p :=
    ((hu.fderiv_right h21).differentiableAt (by norm_num)).hasFDerivAt
  have happ : ∀ d : P, fderiv ℝ (fun q => fderiv ℝ u q d) p
      = (fderiv ℝ (fderiv ℝ u) p).flip d := by
    intro d
    have h := hD2u.clm_apply (hasFDerivAt_const d p)
    have h' : HasFDerivAt (fun q => fderiv ℝ u q d)
        ((fderiv ℝ (fderiv ℝ u) p).flip d) p := by simpa using h
    exact h'.fderiv
  rw [covDerivAlong_def, covDerivAlong_def, happ d₁, happ d₂]
  simp only [ContinuousLinearMap.flip_apply]
  rw [(hu.isSymmSndFDerivAt (by simp)).eq d₁ d₂,
    hΓsymm (fderiv ℝ u p d₁) (fderiv ℝ u p d₂)]

/-! ### The Jacobi equation for a family of geodesics -/

/-- **Math.** **The Jacobi equation.** Let `u : P → E` be a `C³` family of
curves (in the two-parameter case `P = ℝ × ℝ`, `dt` and `ds` the coordinate
directions) whose `t`-lines are geodesics near `p` (`∇_t ∂_t u = 0`), with
symmetric connection coefficients `Γ` differentiable at `u p`. Then the
variation field `Y = ∂_s u` satisfies the Jacobi equation
`∇_t∇_t Y + R(Y, ∂_t u)∂_t u = 0` at `p`:
differentiating `∇_t ∂_t u = 0` in the `s`-direction, commuting the covariant
derivatives (`covDerivAlong_comm`, picking up the curvature term) and using
torsion-freeness `∇_s ∂_t u = ∇_t ∂_s u` (`covDerivAlong_fderiv_symm`).
Blueprint: `lem:covariant-commutation-jacobi`. -/
theorem covDerivAlong_geodesic_family_jacobi {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {u : P → E} {p : P} {ds dt : P}
    (hu : ContDiffAt ℝ 3 u p) (hΓ : DifferentiableAt ℝ Γ (u p))
    (hΓsymm : ∀ x X Y, Γ x X Y = Γ x Y X)
    (hgeo : ∀ᶠ q in 𝓝 p, covDerivAlong Γ u (fun r => fderiv ℝ u r dt) dt q = 0) :
    covDerivAlong Γ u (covDerivAlong Γ u (fun r => fderiv ℝ u r ds) dt) dt p
      + christoffelCurvature Γ (u p) (fderiv ℝ u p ds) (fderiv ℝ u p dt)
          (fderiv ℝ u p dt)
      = 0 := by
  have hu2 : ContDiffAt ℝ 2 u p := hu.of_le (by norm_num)
  -- the velocity field of the t-lines is C²
  have hT2 : ContDiffAt ℝ 2 (fun r => fderiv ℝ u r dt) p :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  -- curvature commutation applied to the velocity field
  have hcomm := covDerivAlong_comm hu2 hT2 hΓ ds dt
  -- the family is geodesic in t near p, so ∇_s (∇_t ∂_t u) = 0
  have hzero : covDerivAlong Γ u
      (covDerivAlong Γ u (fun r => fderiv ℝ u r dt) dt) ds p = 0 := by
    rw [covDerivAlong_congr Γ u (W := fun _ => (0 : E)) hgeo ds,
      covDerivAlong_zero]
  -- torsion-freeness near p: ∇_t ∂_s u = ∇_s ∂_t u
  have hu_ev : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 u q :=
    (hu.eventually (by simp)).mono fun q hq => hq.of_le (by norm_num)
  have hsymm : covDerivAlong Γ u (fun r => fderiv ℝ u r ds) dt
      =ᶠ[𝓝 p] covDerivAlong Γ u (fun r => fderiv ℝ u r dt) ds := by
    filter_upwards [hu_ev] with q hq
    exact covDerivAlong_fderiv_symm hq (fun X Y => hΓsymm (u q) X Y) dt ds
  rw [covDerivAlong_congr Γ u hsymm dt]
  rw [hzero, zero_sub, neg_eq_iff_eq_neg] at hcomm
  rw [hcomm]
  exact neg_add_cancel _

end PetersenLib.Jacobi

end
