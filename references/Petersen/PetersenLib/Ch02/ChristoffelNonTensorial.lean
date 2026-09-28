import PetersenLib.Ch02.Exercises22
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Petersen Ch. 2, §2.4 — Christoffel symbols are not tensorial (polar counterexample)

The Christoffel symbols of a metric may vanish in one coordinate system yet be
nonzero in another, so they cannot be the components of a tensor (a tensor that
vanishes in one frame vanishes in all).  Petersen's example is the flat plane:
the first-kind Christoffel symbols vanish in Cartesian coordinates but not in
polar coordinates, where
`Γ_{θθ,r} = ½(∂_θ g_{θr} + ∂_θ g_{θr} − ∂_r g_{θθ}) = −½ ∂_r(r²) = −r`
(since `g_{θθ} = r²` and `g_{θr} = 0`).

We realize both coordinate systems as *parametrizations of the same ambient flat
plane* `ℝ²`, using the induced-metric infrastructure of Exercise 2.5.22
(`inducedMetric`, `inducedChristoffelFirst`, `inducedChristoffelFirst_eq`): a map
`u : ℝ×ℝ → EuclideanSpace ℝ (Fin 2)` pulls the ambient inner product back to the
metric `g_x(v,w) = ⟪Du_x v, Du_x w⟫`, whose first-kind Christoffel symbol is
`inducedChristoffelFirst u`.

* `cartChart p = (p₁, p₂)` is the identity chart; its induced metric is the
  constant flat metric `⟪v,w⟫`, so every first-kind Christoffel symbol vanishes
  (`inducedChristoffelFirst cartChart ≡ 0`).
* `polarChart (r,θ) = (r cos θ, r sin θ)` is the polar chart; its induced metric
  is `dr² + r² dθ²` (`polarChart_inducedMetric_*`), and
  `inducedChristoffelFirst polarChart (r,θ) e_θ e_θ e_r = −r`
  (`polarChart_christoffel_θθr`), nonzero away from the origin.

`christoffelSymbols_not_tensorial` bundles the two computations: the same flat
metric has vanishing Christoffel symbols in Cartesian coordinates and nonvanishing
ones in polar coordinates, which is impossible for a tensor.

The directions are `e_r = (1,0)` (radial) and `e_θ = (0,1)` (angular) in the
`(r,θ)` chart domain `ℝ × ℝ`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.4, p. 85.
-/

open scoped RealInnerProductSpace ContDiff

namespace PetersenLib

/-- **Math.** The Cartesian identity chart of the plane, `(x, y) ↦ (x, y)` as an
element of the ambient inner-product space `ℝ²`. -/
noncomputable def cartChart : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun p => !₂[p.1, p.2]

/-- **Math.** The polar chart of the plane, `(r, θ) ↦ (r cos θ, r sin θ)`. -/
noncomputable def polarChart : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun p => !₂[p.1 * Real.cos p.2, p.1 * Real.sin p.2]

/-- **Eng.** A component of the differential of a map into `ℝ²` is the differential
of that component: `(Du_x v) i = D(u^i)_x v`. -/
theorem fderiv_euclidean_apply {f : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) (i : Fin 2) (v : ℝ × ℝ) :
    (fderiv ℝ f x v) i = fderiv ℝ (fun q => f q i) x v := by
  have h : HasFDerivAt (fun q => f q i) ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ f x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hf.hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply]
  rfl

/-- **Eng.** The real inner product of two vectors in `ℝ²` in components. -/
theorem euclidean_inner_two (a b : EuclideanSpace ℝ (Fin 2)) :
    ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  congr 1 <;> exact mul_comm _ _

section Derivatives

variable (y : ℝ × ℝ)

theorem d_rcos_er : fderiv ℝ (fun q : ℝ × ℝ => q.1 * Real.cos q.2) y (1, 0) = Real.cos y.2 := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => q.1 * Real.cos q.2) _ y :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := y)).mul
      ((Real.hasDerivAt_cos y.2).comp_hasFDerivAt y hasFDerivAt_snd)
  rw [h.fderiv]; simp

theorem d_rcos_eθ : fderiv ℝ (fun q : ℝ × ℝ => q.1 * Real.cos q.2) y (0, 1) = -(y.1 * Real.sin y.2) := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => q.1 * Real.cos q.2) _ y :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := y)).mul
      ((Real.hasDerivAt_cos y.2).comp_hasFDerivAt y hasFDerivAt_snd)
  rw [h.fderiv]; simp

theorem d_rsin_er : fderiv ℝ (fun q : ℝ × ℝ => q.1 * Real.sin q.2) y (1, 0) = Real.sin y.2 := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => q.1 * Real.sin q.2) _ y :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := y)).mul
      ((Real.hasDerivAt_sin y.2).comp_hasFDerivAt y hasFDerivAt_snd)
  rw [h.fderiv]; simp

theorem d_rsin_eθ : fderiv ℝ (fun q : ℝ × ℝ => q.1 * Real.sin q.2) y (0, 1) = y.1 * Real.cos y.2 := by
  have h : HasFDerivAt (fun q : ℝ × ℝ => q.1 * Real.sin q.2) _ y :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := y)).mul
      ((Real.hasDerivAt_sin y.2).comp_hasFDerivAt y hasFDerivAt_snd)
  rw [h.fderiv]; simp

end Derivatives

theorem polarChart_smooth : ContDiff ℝ ∞ polarChart := by
  rw [show polarChart = fun p : ℝ × ℝ => !₂[p.1 * Real.cos p.2, p.1 * Real.sin p.2] from rfl,
    contDiff_euclidean]
  intro i
  fin_cases i
  · show ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 * Real.cos p.2)
    exact contDiff_fst.mul (Real.contDiff_cos.comp contDiff_snd)
  · show ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 * Real.sin p.2)
    exact contDiff_fst.mul (Real.contDiff_sin.comp contDiff_snd)

theorem cartChart_smooth : ContDiff ℝ ∞ cartChart := by
  rw [show cartChart = fun p : ℝ × ℝ => !₂[p.1, p.2] from rfl, contDiff_euclidean]
  intro i
  fin_cases i
  · exact contDiff_fst
  · exact contDiff_snd

theorem polarChart_diff (y : ℝ × ℝ) : DifferentiableAt ℝ polarChart y :=
  (polarChart_smooth.differentiable (by norm_cast)).differentiableAt

theorem cartChart_diff (y : ℝ × ℝ) : DifferentiableAt ℝ cartChart y :=
  (cartChart_smooth.differentiable (by norm_cast)).differentiableAt

/-- The components of `polarChart` as scalar functions of the chart point. -/
theorem polarChart_apply_zero : (fun q => polarChart q 0) = fun q : ℝ × ℝ => q.1 * Real.cos q.2 := by
  funext q; simp [polarChart]

theorem polarChart_apply_one : (fun q => polarChart q 1) = fun q : ℝ × ℝ => q.1 * Real.sin q.2 := by
  funext q; simp [polarChart]

theorem cartChart_apply_zero : (fun q => cartChart q 0) = fun q : ℝ × ℝ => q.1 := by
  funext q; simp [cartChart]

theorem cartChart_apply_one : (fun q => cartChart q 1) = fun q : ℝ × ℝ => q.2 := by
  funext q; simp [cartChart]

/-- **Math.** The polar metric off-diagonal component vanishes: `g_{θr} = 0`. -/
theorem polarChart_inducedMetric_θr (y : ℝ × ℝ) :
    inducedMetric polarChart y (0, 1) (1, 0) = 0 := by
  rw [inducedMetric, euclidean_inner_two,
    fderiv_euclidean_apply (polarChart_diff y) 0, fderiv_euclidean_apply (polarChart_diff y) 1,
    fderiv_euclidean_apply (polarChart_diff y) 0, fderiv_euclidean_apply (polarChart_diff y) 1,
    polarChart_apply_zero, polarChart_apply_one,
    d_rcos_eθ, d_rcos_er, d_rsin_eθ, d_rsin_er]
  ring

/-- **Math.** The polar metric angular component: `g_{θθ} = r²`. -/
theorem polarChart_inducedMetric_θθ (y : ℝ × ℝ) :
    inducedMetric polarChart y (0, 1) (0, 1) = (y.1) ^ 2 := by
  rw [inducedMetric, euclidean_inner_two,
    fderiv_euclidean_apply (polarChart_diff y) 0, fderiv_euclidean_apply (polarChart_diff y) 1,
    polarChart_apply_zero, polarChart_apply_one, d_rcos_eθ, d_rsin_eθ]
  have h := Real.sin_sq_add_cos_sq y.2
  nlinarith [Real.sin_sq_add_cos_sq y.2]

/-- **Math.** The polar metric radial component: `g_{rr} = 1`. -/
theorem polarChart_inducedMetric_rr (y : ℝ × ℝ) :
    inducedMetric polarChart y (1, 0) (1, 0) = 1 := by
  rw [inducedMetric, euclidean_inner_two,
    fderiv_euclidean_apply (polarChart_diff y) 0, fderiv_euclidean_apply (polarChart_diff y) 1,
    polarChart_apply_zero, polarChart_apply_one, d_rcos_er, d_rsin_er]
  nlinarith [Real.sin_sq_add_cos_sq y.2]

/-- **Math.** The Cartesian (identity-chart) induced metric is the constant flat
metric `g(v,w) = v₁w₁ + v₂w₂`, independent of the point. -/
theorem cartChart_inducedMetric (y v w : ℝ × ℝ) :
    inducedMetric cartChart y v w = v.1 * w.1 + v.2 * w.2 := by
  rw [inducedMetric, euclidean_inner_two,
    fderiv_euclidean_apply (cartChart_diff y) 0, fderiv_euclidean_apply (cartChart_diff y) 1,
    fderiv_euclidean_apply (cartChart_diff y) 0, fderiv_euclidean_apply (cartChart_diff y) 1,
    cartChart_apply_zero, cartChart_apply_one]
  simp [fderiv_fst, fderiv_snd]

/-- **Math.** In polar coordinates the first-kind Christoffel symbol
`Γ_{θθ,r} = −r`, computed from `g_{θθ} = r²`, `g_{θr} = 0` via
`Γ_{θθ,r} = ½(2 ∂_θ g_{θr} − ∂_r g_{θθ}) = −½ ∂_r(r²) = −r`. -/
theorem polarChart_christoffel_θθr (y : ℝ × ℝ) :
    inducedChristoffelFirst polarChart y (0, 1) (0, 1) (1, 0) = -y.1 := by
  rw [inducedChristoffelFirst]
  -- the two `g_{θr}` derivatives vanish, the `g_{θθ}` derivative is `∂_r r² = 2r`
  have hθr : (fun z => inducedMetric polarChart z (0, 1) (1, 0)) = fun _ => (0 : ℝ) := by
    funext z; exact polarChart_inducedMetric_θr z
  have hθθ : (fun z => inducedMetric polarChart z (0, 1) (0, 1)) = fun z : ℝ × ℝ => (z.1) ^ 2 := by
    funext z; exact polarChart_inducedMetric_θθ z
  have hd : fderiv ℝ (fun z : ℝ × ℝ => (z.1) ^ 2) y (1, 0) = 2 * y.1 := by
    have h : HasFDerivAt (fun z : ℝ × ℝ => (z.1) ^ 2) _ y :=
      (hasFDerivAt_fst (𝕜 := ℝ) (p := y)).pow 2
    rw [h.fderiv]; simp
  rw [hθr, hθθ, hd]
  simp

/-- **Math.** In Cartesian (identity-chart) coordinates every first-kind Christoffel
symbol of the flat metric vanishes, because the induced metric is constant. -/
theorem cartChart_christoffel_zero (x v w z : ℝ × ℝ) :
    inducedChristoffelFirst cartChart x v w z = 0 := by
  rw [inducedChristoffelFirst]
  have h1 : (fun y => inducedMetric cartChart y w z) = fun _ => w.1 * z.1 + w.2 * z.2 := by
    funext y; exact cartChart_inducedMetric y w z
  have h2 : (fun y => inducedMetric cartChart y v z) = fun _ => v.1 * z.1 + v.2 * z.2 := by
    funext y; exact cartChart_inducedMetric y v z
  have h3 : (fun y => inducedMetric cartChart y v w) = fun _ => v.1 * w.1 + v.2 * w.2 := by
    funext y; exact cartChart_inducedMetric y v w
  rw [h1, h2, h3]
  simp

/-- **Math.** Christoffel symbols are not tensorial.  For the flat metric on the
plane, realized as the ambient inner product pulled back through a chart:

1. in Cartesian coordinates (`cartChart`) every first-kind Christoffel symbol is
   zero;
2. in polar coordinates (`polarChart`) the same flat metric has
   `Γ_{θθ,r}(r,θ) = −r`;
3. so `Γ_{θθ,r} ≠ 0` at, e.g., `r = 1`.

A tensor vanishing in one coordinate system vanishes in all, so the Christoffel
symbols cannot form a tensor. -/
theorem christoffelSymbols_not_tensorial :
    (∀ x v w z : ℝ × ℝ, inducedChristoffelFirst cartChart x v w z = 0) ∧
      (∀ r θ : ℝ, inducedChristoffelFirst polarChart (r, θ) (0, 1) (0, 1) (1, 0) = -r) ∧
      ∃ x : ℝ × ℝ, inducedChristoffelFirst polarChart x (0, 1) (0, 1) (1, 0) ≠ 0 := by
  refine ⟨cartChart_christoffel_zero, fun r θ => polarChart_christoffel_θθr (r, θ), ⟨(1, 0), ?_⟩⟩
  rw [polarChart_christoffel_θθr (1, 0)]
  norm_num

end PetersenLib
