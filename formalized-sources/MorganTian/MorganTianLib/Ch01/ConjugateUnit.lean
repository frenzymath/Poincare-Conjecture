import MorganTianLib.Ch01.JacobiInterior
import MorganTianLib.Ch01.FrameRadialBridge
import MorganTianLib.Ch01.ConjugateDifferential

/-!
# Poincaré Ch. 1, §1.4 — no conjugate point ⟹ the matrix Jacobi field is invertible

`sectional_curvature_comparison` (`thm:sectional-curvature-comparison`) and
`ricci_curvature_comparison` (`thm:ricci-curvature-comparison`) both deliver their conclusions
only under the hypothesis

  `∀ r ∈ (0, r₀), IsUnit (𝒥 r)`

on the **matrix Jacobi field** `𝒥` that they themselves produce existentially. That hypothesis
is the algebraic shadow of "`γ` has no conjugate point of `γ(0)` before `r₀`": the shape
operator `A = 𝒥'𝒥⁻¹` of the geodesic spheres, which drives the Riccati comparison, is defined
only where `𝒥` is invertible.

Until now it could not be discharged. It is a statement about the *existentially bound* `𝒥`, so
no caller could supply it from outside, and no geometric criterion for it existed — the module
docstrings of both comparison theorems say as much ("Morgan–Tian derive it from *minimality* of
`γ` via `prop:minimal-geodesic-no-conjugate`; that node is not yet formalized, so it is carried
here as an explicit hypothesis"). Both flagship theorems were therefore vacuous in practice.

This file supplies the criterion:

  **`isUnit_of_not_isConjugatePointAt`** — if `γ(r)` is not conjugate to `γ(0)` along `γ`, then
  `𝒥 r` is invertible.

## The argument

`𝔼` is finite-dimensional, so `IsUnit (𝒥 r)` reduces to injectivity of `𝒥 r`
(`ContinuousLinearMap.isUnit_iff_bijective` plus `LinearMap.injective_iff_surjective`). Suppose
then that `𝒥 r x = 0` with `x ≠ 0`. Transport `x` into the tangent space along the frame,
`w = frameLift 0 x`, which is nonzero because `frameLift` is a `g`-isometry, and let `J` be the
Jacobi field on `[a, b]` with

  `J 0 = 0`,  `∇J 0 = w`.

*This is exactly the field that `exists_isJacobiFieldAlongOn` cannot build* — its data is pinned
at the interior time `0`, not at the left endpoint `a` — which is why this file rests on
`exists_isJacobiFieldAlongOn_mem`.

The column clause of the radial datum then reads `frameVec J t = 𝒥 t (frameVec ∇J 0)`, and the
round trip `frameVec ∘ frameLift = id` (`frameVec_frameLift`) identifies `frameVec ∇J 0` with
`x`. Hence `frameVec J r = 𝒥 r x = 0`, so `J r = 0` (`frameVec` is a `g`-isometry). Moreover `J`
does not vanish identically on `[0, r]`: if it did, `deriv_eq_zero_of_forall_eq_zero` would force
`∇J 0 = w = 0`. So `J` is a nontrivial Jacobi field vanishing at both `0` and `r` — that is, `r`
*is* a conjugate point, contradicting the hypothesis.

Blueprint: `def:conjugate-point`, `thm:sectional-curvature-comparison`,
`thm:ricci-curvature-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Module
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-! ### The frame coordinate map is a bijection -/

/-- **Math.** **The lift is a right inverse of the coefficient map**: reading the frame lift of
`x` back in the frame returns `x`.

Both maps are `g`-isometries onto their images (`metricInner_frameLift`,
`metricInner_eq_inner_frameVec`); this says they are mutually inverse. Coordinatewise,
`⟪bᵢ, frameVec (frameLift x)⟫ = ⟨frameLift x, Eᵢ⟩_g = ⟪bᵢ, x⟫` by orthonormality of the frame. -/
theorem frameVec_frameLift {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {t : ℝ}
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0)
    (x : 𝔼) (V : ℝ → E) (hV : (V t : TangentSpace I (γ t)) = frameLift (I := I) g γ e t x) :
    frameVec (I := I) g γ e V t = x := by
  classical
  refine InnerProductSpace.ext_inner_left_basis
    (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis (fun i => ?_)
  rw [OrthonormalBasis.coe_toBasis]
  rw [inner_basisFun_frameVec (I := I) g γ e V t i]
  -- `frameCoeff V i t = ⟨V t, Eᵢ(t)⟩_g = ⟪bᵢ, x⟫`, by expanding the lift in the frame and using
  -- orthonormality.  (The expansion goes through `metricInner_sum_smul_left`, the same helper
  -- `metricInner_frameLift` uses: `E` carries two `NormedSpace ℝ E` instances here, so a bare
  -- `rw [metricInner_smul_left]` would not match the `•` of `frameLift`.)
  show g.metricInner (γ t) (V t : TangentSpace I (γ t)) (e i t) = _
  rw [hV]
  -- expand the lift in the frame; stated against `frameLift` (which the goal contains
  -- syntactically) and proved by definitional unfolding, so no `•` instance has to be matched
  have hexp : g.metricInner (γ t) (frameLift (I := I) g γ e t x) (e i t)
      = ∑ j, ⟪(𝔟 j : 𝔼), x⟫ * g.metricInner (γ t) (e j t : TangentSpace I (γ t)) (e i t) :=
    metricInner_sum_smul_left (I := I) g (γ t) Finset.univ (fun j => ⟪(𝔟 j : 𝔼), x⟫)
      (fun j => (e j t : TangentSpace I (γ t))) (e i t)
  rw [hexp]
  simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- **Math.** The coefficient map is injective: a field whose frame coordinates vanish at `t`
vanishes at `t`, since `frameVec` is a `g`-isometry and `g` is positive definite. -/
theorem eq_zero_of_frameVec_eq_zero {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {V : ℝ → E} {t : ℝ}
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0)
    (hV : frameVec (I := I) g γ e V t = 0) : V t = 0 := by
  by_contra hne
  have hpos : 0 < g.metricInner (γ t) (V t : TangentSpace I (γ t)) (V t) :=
    g.metricInner_self_pos (γ t) (V t) hne
  rw [metricInner_eq_inner_frameVec (I := I) horth V V, hV] at hpos
  simp at hpos

/-! ### The criterion -/

/-- **Math.** **No conjugate point at `r` ⟹ the matrix Jacobi field is invertible at `r`.**

This is the geometric criterion that discharges the standing `IsUnit (𝒥 r)` hypothesis of
`sectional_curvature_comparison` and `ricci_curvature_comparison`. The hypotheses `hcol`,
`horth` are exactly the clauses those theorems (and
`exists_isRadialJacobi_of_geodesic_velocity`) hand out, so the criterion plugs straight into
them.

Note the direction of the interval hypotheses: the Jacobi field must be produced on the *large*
interval `[a, b]` with `a < 0 < b`, since that is what `hcol` quantifies over — hence
`exists_isJacobiFieldAlongOn_mem`, not `exists_isJacobiFieldAlongOn`.

Blueprint: `def:conjugate-point`. -/
theorem isUnit_of_not_isConjugatePointAt {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {𝒥 : ℝ → 𝔼 →L[ℝ] 𝔼} {a b B r : ℝ}
    (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
    (hcol : ∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b → J 0 = 0 →
      ∀ t ∈ Icc (0 : ℝ) B,
        frameVec (I := I) g γ e J t = 𝒥 t (frameVec (I := I) g γ e DJ 0))
    (ha : a < 0) (hBb : B < b) (hr0 : 0 < r) (hrB : r ≤ B)
    (hnc : ¬ IsConjugatePointAt (I := I) g γ r) :
    IsUnit (𝒥 r) := by
  classical
  have h0ab : (0 : ℝ) ∈ Icc a b := ⟨ha.le, (hr0.trans_le (hrB.trans hBb.le)).le⟩
  have hrab : Icc (0 : ℝ) r ⊆ Icc a b :=
    Icc_subset_Icc ha.le (hrB.trans hBb.le)
  -- in finite dimension, invertibility is injectivity
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  -- the kernel of `𝒥 r` is trivial
  have key : ∀ x : 𝔼, 𝒥 r x = 0 → x = 0 := by
    intro x hx
    by_contra hxne
    -- the tangent vector represented by `x` in the frame at the centre
    set w : E := frameLift (I := I) g γ e 0 x with hw
    have horth0 := horth 0 h0ab
    have hwne : w ≠ 0 := by
      intro h
      have hxx : g.metricInner (γ 0) (w : TangentSpace I (γ 0)) w = ⟪x, x⟫ :=
        metricInner_frameLift (I := I) horth0 x x
      have hxx0 : (⟪x, x⟫ : ℝ) = 0 := by
        rw [← hxx, h]
        exact g.metricInner_zero_left (γ 0) 0
      exact hxne (inner_self_eq_zero.1 hxx0)
    -- the Jacobi field with `J 0 = 0`, `∇J 0 = w` — data at the *interior* time `0`
    obtain ⟨J, DJ, hJac, hJ0, hDJ0⟩ :=
      exists_isJacobiFieldAlongOn_mem (I := I) hab hgeo hγc h0ab 0 w
    -- its initial covariant derivative reads back as `x`
    have hDJx : frameVec (I := I) g γ e DJ 0 = x :=
      frameVec_frameLift (I := I) horth0 x DJ (by rw [hDJ0])
    -- hence `frameVec J r = 𝒥 r x = 0`, so `J r = 0`
    have hJr0 : J r = 0 := by
      refine eq_zero_of_frameVec_eq_zero (I := I) (horth r (hrab (right_mem_Icc.2 hr0.le))) ?_
      rw [hcol J DJ hJac hJ0 r ⟨hr0.le, hrB⟩, hDJx, hx]
    -- `J` is not identically zero on `[0, r]`: otherwise `∇J 0 = w = 0`
    have hne : ∃ t ∈ Icc (0 : ℝ) r, J t ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hwne (hDJ0 ▸ IsJacobiFieldAlongOn.deriv_eq_zero_of_forall_eq_zero
        hr0 (hJac.mono ha.le hr0 (hrB.trans hBb.le)) hall)
    -- so `r` is a conjugate point of `γ 0` along `γ` — contradiction
    exact hnc ⟨J, DJ, hJac.mono ha.le hr0 (hrB.trans hBb.le), hne, hJ0, hJr0⟩
  have hinj : Function.Injective (𝒥 r) := by
    intro u v huv
    have h0 : 𝒥 r (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.1 (key _ h0)
  -- injective endomorphism of a finite-dimensional space, hence bijective
  have hinjL : Function.Injective ((𝒥 r).toLinearMap) := hinj
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinjL⟩

end MorganTianLib

end
