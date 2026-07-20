import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap
import Mathlib.Analysis.Calculus.Conformal.NormedSpace
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Conformal

/-!
# Conformal transformations of `ℝⁿ` (do Carmo Ch. 8 §5)

This file formalizes the notion of a *conformal transformation* of Euclidean
space and do Carmo's Example 5.1: isometries, dilatations and inversions are
conformal, with the coefficients of conformality he records.

do Carmo (Ch. 8 §5, eq. (3)) calls a map `f : U ⊂ ℝⁿ → ℝⁿ` conformal at `p`
with *coefficient of conformality* `λ(p) > 0` when

$$\langle df_p(v_1), df_p(v_2)\rangle = \lambda^2(p)\,\langle v_1, v_2\rangle
  \qquad\text{for all }v_1, v_2.$$

We package this pointwise condition as `Riemannian.IsConformalWithCoeff`. It is
exactly mathlib's `IsConformalMap (fderiv ℝ f p)` with a named positive square
root of the conformal factor (`IsConformalWithCoeff.isConformalMap`,
`IsConformalWithCoeff.conformalAt`), so it is angle-preserving in do Carmo's
sense.

**Example 5.1** (`ex:dc-ch8-5-1`):

* `isConformalWithCoeff_isometry` — a Euclidean isometry (orthogonal linear map
  followed by a translation) is conformal with `λ ≡ 1`;
* `isConformalWithCoeff_dilatation` — the dilatation `f(p) = c • p`, `c > 0`, is
  conformal with `λ ≡ c`;
* `isConformalWithCoeff_inversion` — the inversion `f(p) = (p - p₀)/|p - p₀|² + p₀`
  in the unit sphere about `p₀` is conformal with `λ = 1/|p - p₀|²`.

The inversion computation reuses mathlib's
`EuclideanGeometry.hasFDerivAt_inversion`, whose derivative is
`(R/|x - c|)² • (reflection in `(x - c)^⊥`)`; the reflection is a linear
isometry, so the coefficient of conformality is `(R/|x - c|)²`, i.e. `1/|x - p₀|²`
when `R = 1` as in do Carmo's inversion `(5)`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8 §5, Example 5.1.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Riemannian

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **do Carmo Ch. 8 §5, eq. (3).** A map `f : F → F` is *conformal at `x` with
coefficient of conformality `lam`* when `lam > 0`, `f` is differentiable at `x`,
and its differential rescales all inner products by `lam²`:
`⟨df_x u, df_x v⟩ = lam² ⟨u, v⟩`. This is do Carmo's definition of a conformal
map together with a named positive coefficient of conformality. -/
def IsConformalWithCoeff (f : F → F) (x : F) (lam : ℝ) : Prop :=
  0 < lam ∧ ∃ f' : F →L[ℝ] F, HasFDerivAt f f' x ∧
    ∀ u v : F, ⟪f' u, f' v⟫ = lam ^ 2 * ⟪u, v⟫

namespace IsConformalWithCoeff

variable {f : F → F} {x : F} {lam : ℝ}

theorem pos (h : IsConformalWithCoeff f x lam) : 0 < lam := h.1

/-- The differential of a conformal map, as a mathlib conformal linear map:
angle preservation is exactly `IsConformalMap`. -/
theorem isConformalMap (h : IsConformalWithCoeff f x lam) :
    IsConformalMap (fderiv ℝ f x) := by
  obtain ⟨hlam, f', hf', hscale⟩ := h
  have hfd : fderiv ℝ f x = f' := hf'.fderiv
  rw [isConformalMap_iff]
  refine ⟨lam ^ 2, by positivity, fun u v => ?_⟩
  rw [hfd]; exact hscale u v

/-- A conformal map (with coefficient) is conformal at `x` in mathlib's sense,
hence preserves (non-oriented) angles. -/
theorem conformalAt (h : IsConformalWithCoeff f x lam) : ConformalAt f x :=
  conformalAt_iff_isConformalMap_fderiv.mpr h.isConformalMap

/-- **do Carmo Ch. 8 §5, eq. before (4).** The differential of a conformal map
rescales *norms* by the coefficient of conformality: `|df_x(v)| = lam · |v|`.
(do Carmo writes this as `|df_p(v)|² = λ²(p)|v|²`.) This is the analytic step from
his condition (3) on inner products to the angle statement (4). -/
theorem norm_fderiv_eq (h : IsConformalWithCoeff f x lam) (v : F) :
    ‖fderiv ℝ f x v‖ = lam * ‖v‖ := by
  obtain ⟨hlam, f', hf', hscale⟩ := h
  have hf2 : ‖f' v‖ ^ 2 = lam ^ 2 * ‖v‖ ^ 2 := by
    have := hscale v v
    rwa [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
  have hnn : (0 : ℝ) ≤ lam * ‖v‖ := mul_nonneg hlam.le (norm_nonneg v)
  rw [hf'.fderiv, ← Real.sqrt_sq (norm_nonneg (f' v)), hf2, ← mul_pow, Real.sqrt_sq hnn]

/-- **do Carmo Ch. 8 §5, eq. (4).** A conformal map preserves (non-oriented)
angles: the differential sends the angle between `u` and `v` to the same angle.
This is do Carmo's equation (4), obtained from (3) by dividing out the common
factor `lam²`. It is the wrapper of mathlib's
`InnerProductGeometry.IsConformalMap.preserves_angle` through the conformal-map
bridge `IsConformalWithCoeff.isConformalMap`. -/
theorem angle_fderiv_eq (h : IsConformalWithCoeff f x lam) (u v : F) :
    InnerProductGeometry.angle (fderiv ℝ f x u) (fderiv ℝ f x v)
      = InnerProductGeometry.angle u v :=
  InnerProductGeometry.IsConformalMap.preserves_angle h.isConformalMap u v

/-- **do Carmo Ch. 8 §5.** The composition of two conformal maps is conformal, and
the coefficients of conformality multiply: if `f` is conformal at `x` with
coefficient `lam` and `g` is conformal at `f x` with coefficient `mu`, then
`g ∘ f` is conformal at `x` with coefficient `mu · lam`. This closure under
composition is what makes the Liouville decomposition
"isometry ∘ dilatation ∘ inversion" (Theorem 5.2) a conformal map, and it is used
in Theorem 5.3 to form `h = g⁻¹ ∘ f`. -/
theorem comp {g : F → F} {mu : ℝ}
    (hg : IsConformalWithCoeff g (f x) mu) (hf : IsConformalWithCoeff f x lam) :
    IsConformalWithCoeff (g ∘ f) x (mu * lam) := by
  obtain ⟨hlam, f', hf', hfscale⟩ := hf
  obtain ⟨hmu, g', hg', hgscale⟩ := hg
  refine ⟨mul_pos hmu hlam, g'.comp f', hg'.comp x hf', fun u v => ?_⟩
  calc ⟪(g'.comp f') u, (g'.comp f') v⟫
      = ⟪g' (f' u), g' (f' v)⟫ := rfl
    _ = mu ^ 2 * ⟪f' u, f' v⟫ := hgscale _ _
    _ = mu ^ 2 * (lam ^ 2 * ⟪u, v⟫) := by rw [hfscale]
    _ = (mu * lam) ^ 2 * ⟪u, v⟫ := by ring

end IsConformalWithCoeff

/-- **do Carmo Ch. 8 §5.** The identity map is conformal with coefficient of
conformality `1` (the degenerate isometry/dilatation). -/
theorem isConformalWithCoeff_id (x : F) : IsConformalWithCoeff (id : F → F) x 1 := by
  refine ⟨one_pos, ContinuousLinearMap.id ℝ F, hasFDerivAt_id x, fun u v => ?_⟩
  simp

/-! ## Example 5.1: isometries, dilatations, inversions -/

/-- **do Carmo Ch. 8 §5, Example 5.1 (isometry).** A Euclidean isometry — an
orthogonal linear transformation `A` followed by a translation by `b` — is a
conformal transformation with coefficient of conformality `λ ≡ 1`. -/
theorem isConformalWithCoeff_isometry (A : F ≃ₗᵢ[ℝ] F) (b : F) (x : F) :
    IsConformalWithCoeff (fun p => A p + b) x 1 := by
  refine ⟨one_pos, (A : F →L[ℝ] F), ?_, fun u v => ?_⟩
  · exact (A.toContinuousLinearEquiv.hasFDerivAt).add_const b
  · simp only [ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, A.inner_map_map]
    ring

/-- **do Carmo Ch. 8 §5, Example 5.1 (dilatation).** The dilatation `f(p) = c·p`
with `c = const. > 0` is conformal with coefficient of conformality `λ ≡ c`. -/
theorem isConformalWithCoeff_dilatation {c : ℝ} (hc : 0 < c) (x : F) :
    IsConformalWithCoeff (fun p => c • p) x c := by
  refine ⟨hc, c • ContinuousLinearMap.id ℝ F, ?_, fun u v => ?_⟩
  · exact (hasFDerivAt_id x).const_smul c
  · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    ring

/-- **do Carmo Ch. 8 §5, Example 5.1 (inversion).** The inversion in the unit
sphere centered at `p₀`,
`f(p) = (p - p₀)/|p - p₀|² + p₀ = EuclideanGeometry.inversion p₀ 1 p`, is a
conformal transformation with coefficient of conformality `λ = 1/|p - p₀|²`.

The differential (mathlib's `hasFDerivAt_inversion`) is
`(1/|x - p₀|)² • reflection` in the hyperplane `(x - p₀)^⊥`; the reflection is a
linear isometry, so `⟨df_x u, df_x v⟩ = (1/|x - p₀|²)² ⟨u, v⟩`, giving the
coefficient `λ = 1/|x - p₀|²`. -/
theorem isConformalWithCoeff_inversion [CompleteSpace F] (p₀ : F) {x : F}
    (hx : x ≠ p₀) :
    IsConformalWithCoeff (EuclideanGeometry.inversion p₀ 1) x
      (1 / dist x p₀ ^ 2) := by
  have hdist : 0 < dist x p₀ := dist_pos.mpr hx
  refine ⟨by positivity, _, EuclideanGeometry.hasFDerivAt_inversion (R := 1) hx,
    fun u v => ?_⟩
  simp only [ContinuousLinearMap.smul_apply, one_div,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    LinearIsometryEquiv.inner_map_map]
  have hne : dist x p₀ ≠ 0 := ne_of_gt hdist
  field_simp

end Riemannian
