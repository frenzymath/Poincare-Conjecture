import PetersenLib.Ch03.DistanceFunctions
import PetersenLib.Ch03.EuclideanCurvature
import PetersenLib.Ch02.HessianEuclidean
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Petersen Ch. 3, §3.2 — Example 3.2.9: vanishing shape operator ⟺ hyperplane

**Example 3.2.9** (Petersen §3.2, `ex:pet-ch3-zero-shape-operator-hyperplane`).
For an orientable hypersurface `H ⊂ ℝⁿ` with unit normal `N` and shape operator
`S(v) = ∇_v N`, the condition `S ≡ 0` on `H` forces `N` to be a constant vector
field and `H` to be open in a fixed hyperplane through any of its points.

## Formalization

Absent a Riemannian-submanifold layer (see the design note in
`SecondFundamentalForm.lean`), the hypersurface `H` is represented — exactly as
throughout the Ch. 3 distance-function API — implicitly, as the level sets of a
distance function `r` on an ambient open set `U ⊆ F`. The unit normal is the
radial field `∂_r = ∇r` and the shape operator is `S = ∇∂_r = hessianOperator`.
"`H` is open in a hyperplane" is captured as "`r` is affine on `U`", i.e.
`r p = ⟪N₀, p⟫ + c`: then each level set `{p ∈ U | r p = t}` equals
`U ∩ {p | ⟪N₀, p⟫ = t − c}`, an open piece of a hyperplane.

The theorem is the iff `S ≡ 0 ⟺ ∇r ≡ N₀ constant and r affine`. On Euclidean
space the shape operator `∇_v∇r` is the ordinary Fréchet derivative
`fderiv ℝ (∇r) · v` of the gradient field (`leviCivita_cov_eq_euclidean`), so:

* `⟸` if `∇r` is constant on `U`, its Fréchet derivative vanishes there;
* `⟹` if `fderiv ℝ (∇r) ≡ 0` on the preconnected open `U`, then `∇r` is constant
  (`IsOpen.exists_is_const_of_fderiv_eq_zero`), and integrating once more
  (`IsOpen.exists_eq_add_of_fderiv_eq`, using `∇r = N₀` and the Riesz identity
  `fderiv ℝ r = ⟪∇r, ·⟫`) gives `r p = ⟪N₀, p⟫ + c`.

This drops only the illustrative curve-based converse construction of the text,
not the theorem's mathematical content.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.2, Example 3.2.9.
-/

open Bundle Set Function
open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace PetersenLib

section ZeroShapeOperator

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F]

/-- **Eng.** On Euclidean space, the shape operator `S(v) = ∇_v∇r`
(`hessianOperator` of the Levi-Civita connection) is the ordinary Fréchet
derivative of the gradient field `∇r`, evaluated in the direction `v`:
`hessianOperator D g r p v = fderiv ℝ (∇r) p v`. This is
`leviCivita_cov_eq_euclidean` applied to the constant direction field. -/
private theorem shapeOperator_eq_fderiv {r : F → ℝ}
    (hrsmooth : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ r) (p v : F) :
    hessianOperator ((innerProductSpaceMetric F).leviCivita).toAffineConnection
        (innerProductSpaceMetric F) r p v
      = fderiv ℝ (gradient (innerProductSpaceMetric F) r) p v := by
  have hgrad : IsSmoothVectorField (gradient (innerProductSpaceMetric F) r) :=
    gradient_isSmoothVectorField (innerProductSpaceMetric F) hrsmooth
  have h := leviCivita_cov_eq_euclidean (isSmoothVectorField_const v) hgrad p
  simpa [hessianOperator, covariantDerivativeEuclidean] using h

/-- **Math.** **Example 3.2.9** (Petersen §3.2,
`ex:pet-ch3-zero-shape-operator-hyperplane`): for a distance function `r` on a
preconnected open set `U ⊆ F` of Euclidean space, the shape operator
`S = ∇∂_r` vanishes on `U` **iff** the radial field `∂_r = ∇r` is a constant
vector `N₀` on `U` and `r` is affine, `r p = ⟪N₀, p⟫ + c`. In the hypersurface
picture this says the vanishing of the second fundamental form is equivalent to
the level sets of `r` being open pieces of the fixed hyperplanes
`{p | ⟪N₀, p⟫ = t − c}`. -/
theorem zeroShapeOperator_iff_hyperplane
    {U : Set F} (hU : IsOpen U) (hUconn : IsPreconnected U)
    {r : F → ℝ} (hrsmooth : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ r)
    (hr : IsDistanceFunction (innerProductSpaceMetric F) U r) :
    (∀ p ∈ U, ∀ v : F,
        hessianOperator ((innerProductSpaceMetric F).leviCivita).toAffineConnection
          (innerProductSpaceMetric F) r p v = 0)
      ↔ ∃ (N₀ : F) (c : ℝ),
          (∀ p ∈ U, gradient (innerProductSpaceMetric F) r p = N₀)
          ∧ ∀ p ∈ U, r p = @inner ℝ F _ N₀ p + c := by
  have hgrad : IsSmoothVectorField (gradient (innerProductSpaceMetric F) r) :=
    gradient_isSmoothVectorField (innerProductSpaceMetric F) hrsmooth
  constructor
  · -- `S ≡ 0` ⟹ `∇r` constant and `r` affine.
    intro hS
    -- `fderiv ℝ (∇r) ≡ 0` on `U`.
    have hfderiv0 : U.EqOn (fderiv ℝ (gradient (innerProductSpaceMetric F) r)) 0 := by
      intro x hx
      ext v
      have h := hS x hx v
      rw [shapeOperator_eq_fderiv hrsmooth x v] at h
      simpa using h
    have hGdiffOn : DifferentiableOn ℝ (gradient (innerProductSpaceMetric F) r) U :=
      fun x _ => (hgrad.differentiableAt x).differentiableWithinAt
    -- Constancy of `∇r` on the preconnected open set `U`.
    obtain ⟨N₀, hN₀⟩ := hU.exists_is_const_of_fderiv_eq_zero hUconn hGdiffOn hfderiv0
    -- Now integrate once more: `fderiv ℝ r = ⟪N₀, ·⟫` on `U`, so `r` is affine.
    have hrdiff : Differentiable ℝ r :=
      (contMDiff_iff_contDiff.1 hrsmooth).differentiable (by decide)
    have hφdiff : Differentiable ℝ (fun q : F => @inner ℝ F _ N₀ q) := by
      simpa using (innerSL ℝ N₀).differentiable
    have hEq : U.EqOn (fderiv ℝ r) (fderiv ℝ (fun q : F => @inner ℝ F _ N₀ q)) := by
      intro x hx
      have hg := gradient_innerProductSpaceMetric r x
      have h1 : fderiv ℝ r x
          = InnerProductSpace.toDual ℝ F (gradient (innerProductSpaceMetric F) r x) := by
        rw [hg]; simp
      rw [hN₀ x hx] at h1
      have hφfd : HasFDerivAt (fun q : F => @inner ℝ F _ N₀ q) (innerSL ℝ N₀) x := by
        simpa using (innerSL ℝ N₀).hasFDerivAt
      rw [h1, hφfd.fderiv]
      ext y
      simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
    obtain ⟨c, hc⟩ :=
      hU.exists_eq_add_of_fderiv_eq hUconn hrdiff.differentiableOn hφdiff.differentiableOn hEq
    exact ⟨N₀, c, hN₀, fun p hp => hc hp⟩
  · -- `∇r` constant ⟹ `S ≡ 0` (the affine data is not needed for this direction).
    rintro ⟨N₀, c, hgradN₀, -⟩ p hp v
    rw [shapeOperator_eq_fderiv hrsmooth p v]
    have hev : gradient (innerProductSpaceMetric F) r =ᶠ[nhds p] (fun _ => N₀) := by
      filter_upwards [hU.mem_nhds hp] with y hy using hgradN₀ y hy
    rw [hev.fderiv_eq]
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply]

end ZeroShapeOperator

end PetersenLib
