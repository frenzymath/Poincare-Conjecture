import DoCarmoLib.Riemannian.Manifold.DoCarmoCh8HyperbolicGeodesic
import DoCarmoLib.Riemannian.Geodesic.IntrinsicUniqueness
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Classification of the geodesics of `Hⁿ` (do Carmo Ch. 8 §3, Prop. 3.1, converse)

The forward direction of do Carmo's Proposition 3.1 — that the vertical lines and the
semicircles perpendicular to `∂Hⁿ = {xₑ = 0}` with centre on `∂Hⁿ` are geodesics of
`Hⁿ` — is `hyperbolic_vertical_isGeodesic` and `hyperbolic_semicircle_isGeodesic`.

This file proves the **converse**: these are *all* the geodesics. Concretely,
`hyperbolic_geodesic_classification` shows that every geodesic `γ` of `Hⁿ` is (the trace
of) a vertical line `s ↦ c + a·eᴮˢ·1ₑ` or a semicircle
`s ↦ m + r·tanh(σs+s₀)·û + r·sech(σs+s₀)·1ₑ`.

The proof is do Carmo's existence/uniqueness argument. Through every point `p₀` and
chart velocity `v₀` there passes a member of the stated family: if `v₀` is vertical
(its horizontal part vanishes) we take the vertical line, otherwise the semicircle in
the plane spanned by `1ₑ` and the horizontal part of `v₀`. The family member is a
geodesic (an affine reparametrisation of the forward families), and it matches `γ` in
position and chart velocity at `s = 0`, so `IsGeodesicOn.eqOn_of_deriv_chartReading_eq`
(uniqueness of intrinsic geodesics, do Carmo Ch. 3 Thm 2.2) forces `γ` to coincide with
it. The semicircle parameters are made explicit through `Real.arsinh`, so no
`exp`/normal-neighbourhood machinery is needed.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8 §3, Prop. 3.1.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix RealInnerProductSpace

namespace Riemannian.Hyperbolic

open Riemannian Riemannian.Geodesic

variable {n : ℕ} [NeZero n]

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ## Reading a curve of `Hⁿ` through the inclusion chart -/

/-- **Math.** For the open half-space, the chart reading of any curve at any basepoint
is literally the ambient Euclidean coordinate `s ↦ (γ s).val`. -/
theorem chartReading_upperHalfSpace (e : Fin n) (β : ↥(upperHalfSpace e))
    (γ : ℝ → ↥(upperHalfSpace e)) :
    chartReading (I := 𝓘(ℝ, E)) β γ = fun s => (γ s : E) := by
  funext s
  simp only [chartReading_def, extChartAt_opens_coe]

/-- **Math.** The Euclidean chart velocity of a geodesic of `Hⁿ` exists: reading the
geodesic through the inclusion chart, `s ↦ (γ s).val` is differentiable, with a
derivative supplied by the geodesic equation. -/
theorem hyperbolic_geodesic_hasDerivAt_val (e : Fin n) {γ : ℝ → ↥(upperHalfSpace e)}
    (hγ : IsGeodesic (I := 𝓘(ℝ, E)) (hyperbolicMetric e) γ) (t : ℝ) :
    ∃ v : E, HasDerivAt (fun s => (γ s : E)) v t := by
  obtain ⟨v, _, hv, _, _, _⟩ := hγ t
  refine ⟨v, ?_⟩
  have hclc : chartLocalCurve (I := 𝓘(ℝ, E)) γ t = fun s => (γ s : E) := by
    funext s; simp only [chartLocalCurve_def, extChartAt_opens_coe]
  rwa [hclc] at hv

/-! ## The ambient derivative of the base semicircle curve -/

/-- **Math.** The ambient Euclidean derivative of the base semicircle curve
`t ↦ m + (r·sinh t/cosh t)·û + (r/cosh t)·1ₑ` (the content of the first step of
`hyperbolic_semicircle_isGeodesic`, exposed as a reusable `HasDerivAt`). -/
theorem semicircle_ambient_hasDerivAt (e : Fin n) (m u : E) (r s : ℝ) :
    HasDerivAt
      (fun t => m + ((r * Real.sinh t / Real.cosh t) • u
        + (r / Real.cosh t) • EuclideanSpace.single e (1 : ℝ)))
      ((r / (Real.cosh s) ^ 2) • u
        + (-(r * Real.sinh s) / (Real.cosh s) ^ 2) • EuclideanSpace.single e (1 : ℝ)) s := by
  have hc : Real.cosh s ≠ 0 := (Real.cosh_pos s).ne'
  have hA : HasDerivAt (fun t => r * Real.sinh t / Real.cosh t) (r / (Real.cosh s) ^ 2) s := by
    have h := ((Real.hasDerivAt_sinh s).const_mul r).div (Real.hasDerivAt_cosh s) hc
    convert h using 2
    linear_combination -r * Real.cosh_sq_sub_sinh_sq s
  have hB : HasDerivAt (fun t => r / Real.cosh t) (-(r * Real.sinh s) / (Real.cosh s) ^ 2) s := by
    have h := (hasDerivAt_const s r).div (Real.hasDerivAt_cosh s) hc
    convert h using 1; field_simp; ring
  exact ((hA.smul_const u).add (hB.smul_const _)).const_add m

/-! ## The classification: every geodesic of `Hⁿ` is a vertical line or a semicircle -/

/-- **Math.** do Carmo Ch. 8 §3, Prop. 3.1 (converse). **Every geodesic of `Hⁿ` is a
vertical line or a semicircle perpendicular to `∂Hⁿ`.** Precisely, a geodesic `γ`
either traces a vertical line `s ↦ c + a·eᴮˢ·1ₑ` (base `c` on `∂Hⁿ`, `a > 0`) or a
semicircle `s ↦ m + r·tanh(σs+s₀)·û + r·sech(σs+s₀)·1ₑ` (centre `m` on `∂Hⁿ`, unit
horizontal `û`, radius `r > 0`). Together with the forward families
(`hyperbolic_vertical_isGeodesic`, `hyperbolic_semicircle_isGeodesic`) this is the full
statement of Proposition 3.1. The proof is do Carmo's existence/uniqueness argument:
the stated family member through the point and chart velocity of `γ` at `s = 0` is a
geodesic agreeing with `γ` there, so intrinsic geodesic uniqueness
(`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) forces equality. -/
theorem hyperbolic_geodesic_classification (e : Fin n) {γ : ℝ → ↥(upperHalfSpace e)}
    (hγ : IsGeodesic (I := 𝓘(ℝ, E)) (hyperbolicMetric e) γ) (hγc : Continuous γ) :
    (∃ (c : E) (a B : ℝ), c e = 0 ∧ 0 < a ∧
        ∀ s, (γ s : E) = c + (a * Real.exp (B * s)) • EuclideanSpace.single e (1 : ℝ))
    ∨ (∃ (m u : E) (r σ s₀ : ℝ), m e = 0 ∧ u e = 0 ∧ (⟪u, u⟫ : ℝ) = 1 ∧ 0 < r ∧
        ∀ s, (γ s : E) = m + (r * Real.sinh (σ * s + s₀) / Real.cosh (σ * s + s₀)) • u
              + (r / Real.cosh (σ * s + s₀)) • EuclideanSpace.single e (1 : ℝ)) := by
  classical
  obtain ⟨v₀, hv₀⟩ := hyperbolic_geodesic_hasDerivAt_val e hγ 0
  have hone : (EuclideanSpace.single e (1 : ℝ)) e = 1 := by simp
  have hh₀ : 0 < (γ 0 : E) e := coord_pos e (γ 0)
  set p₀ : E := (γ 0 : E) with hp₀def
  set h₀ : ℝ := p₀ e with hh₀def
  have hh0ne : h₀ ≠ 0 := ne_of_gt hh₀
  by_cases hvh : v₀ - (v₀ e) • EuclideanSpace.single e (1 : ℝ) = 0
  · -- **Vertical case:** the chart velocity is a multiple of `1ₑ`.
    left
    have hv₀vert : v₀ = (v₀ e) • EuclideanSpace.single e (1 : ℝ) := sub_eq_zero.mp hvh
    set c : E := p₀ - h₀ • EuclideanSpace.single e (1 : ℝ) with hc_def
    have hce : c e = 0 := by
      rw [hc_def]; simp only [PiLp.sub_apply, PiLp.smul_apply, hone, smul_eq_mul, mul_one]
      rw [← hh₀def]; ring
    set B : ℝ := (v₀ e) / h₀ with hB_def
    set η : ℝ → ↥(upperHalfSpace e) :=
      fun s => (⟨c + (h₀ * Real.exp (B * s)) • EuclideanSpace.single e (1 : ℝ),
        vertical_mem e c hce hh₀ (B * s)⟩ : ↥(upperHalfSpace e)) with hη_def
    have hgeoη : IsGeodesic (I := 𝓘(ℝ, E)) (hyperbolicMetric e) η :=
      isGeodesic_comp_mul_left (hyperbolic_vertical_isGeodesic e c hce hh₀) B
    have hηc : Continuous η := by
      apply Continuous.subtype_mk
      fun_prop
    have h0eq : γ 0 = η 0 := by
      apply Subtype.ext
      show p₀ = c + (h₀ * Real.exp (B * 0)) • EuclideanSpace.single e (1 : ℝ)
      rw [mul_zero, Real.exp_zero, mul_one, hc_def]; abel
    have hderiv_η : HasDerivAt (fun s => (η s : E)) ((h₀ * B) • EuclideanSpace.single e (1 : ℝ)) 0 := by
      have hexp : HasDerivAt (fun s => h₀ * Real.exp (B * s)) (h₀ * B) 0 := by
        have hinner : HasDerivAt (fun s : ℝ => B * s) B 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_mul B
        have hcomp : HasDerivAt (fun s => Real.exp (B * s)) (Real.exp (B * 0) * B) 0 :=
          (Real.hasDerivAt_exp (B * 0)).comp 0 hinner
        have := hcomp.const_mul h₀
        simpa [mul_zero, Real.exp_zero, mul_comm, mul_left_comm] using this
      have := (hexp.smul_const (EuclideanSpace.single e (1 : ℝ))).const_add c
      exact this
    have hhB : h₀ * B = v₀ e := by rw [hB_def]; field_simp
    have heqOn : Set.EqOn γ η Set.univ :=
      IsGeodesicOn.eqOn_of_deriv_chartReading_eq (β := γ 0) isOpen_univ isPreconnected_univ
        (hγ.isGeodesicOn _) (hgeoη.isGeodesicOn _) hγc.continuousOn hηc.continuousOn
        (mem_univ 0) h0eq (mem_chart_source _ _) (by
          rw [chartReading_upperHalfSpace, chartReading_upperHalfSpace, hv₀.deriv, hderiv_η.deriv,
            hhB, ← hv₀vert])
    refine ⟨c, h₀, B, hce, hh₀, fun s => ?_⟩
    have hs := heqOn (mem_univ s)
    rw [hs]
  · -- **Semicircle case:** the chart velocity has nonzero horizontal part.
    right
    set ve : ℝ := v₀ e with hve_def
    set vh : E := v₀ - ve • EuclideanSpace.single e (1 : ℝ) with hvh_def
    have hvh_ne : vh ≠ 0 := hvh
    set va : ℝ := ‖vh‖ with hva_def
    have hva_pos : 0 < va := by rw [hva_def]; exact norm_pos_iff.mpr hvh_ne
    have hva_ne : va ≠ 0 := ne_of_gt hva_pos
    set u : E := va⁻¹ • vh with hu_def
    set s₀ : ℝ := Real.arsinh (-ve / va) with hs₀_def
    have hS : Real.sinh s₀ = -ve / va := by rw [hs₀_def, Real.sinh_arsinh]
    set C : ℝ := Real.cosh s₀ with hC_def
    have hC_pos : 0 < C := by rw [hC_def]; exact Real.cosh_pos s₀
    have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    set r : ℝ := h₀ * C with hr_def
    have hr_pos : 0 < r := by rw [hr_def]; exact mul_pos hh₀ hC_pos
    set σ : ℝ := va * C / h₀ with hσ_def
    set m : E := (p₀ - h₀ • EuclideanSpace.single e (1 : ℝ)) + (h₀ * ve / va) • u with hm_def
    -- coordinate facts
    have hvh_e : vh e = 0 := by
      rw [hvh_def]
      simp only [PiLp.sub_apply, PiLp.smul_apply, hone, smul_eq_mul, mul_one]
      rw [← hve_def]; ring
    have hu_e : u e = 0 := by
      rw [hu_def]; simp only [PiLp.smul_apply, hvh_e, smul_eq_mul, mul_zero]
    have hm_e : m e = 0 := by
      rw [hm_def]
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, hone, hu_e, smul_eq_mul,
        mul_one, mul_zero, add_zero]
      rw [← hh₀def]; ring
    have hunorm : (⟪u, u⟫ : ℝ) = 1 := by
      rw [hu_def, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
        ← hva_def]
      field_simp
    -- the base semicircle geodesic and its affine reparametrisation `η s = base (σs+s₀)`
    have hbase : IsGeodesic (I := 𝓘(ℝ, E)) (hyperbolicMetric e)
        (fun t => (⟨m + ((r * Real.sinh t / Real.cosh t) • u
              + (r / Real.cosh t) • EuclideanSpace.single e (1 : ℝ)),
            semicircle_mem e m u hm_e hu_e hr_pos t⟩ : ↥(upperHalfSpace e))) :=
      hyperbolic_semicircle_isGeodesic e m u hm_e hu_e hunorm hr_pos
    set η : ℝ → ↥(upperHalfSpace e) :=
      fun s => (⟨m + ((r * Real.sinh (σ * s + s₀) / Real.cosh (σ * s + s₀)) • u
            + (r / Real.cosh (σ * s + s₀)) • EuclideanSpace.single e (1 : ℝ)),
          semicircle_mem e m u hm_e hu_e hr_pos (σ * s + s₀)⟩ : ↥(upperHalfSpace e)) with hη_def
    have hgeoη : IsGeodesic (I := 𝓘(ℝ, E)) (hyperbolicMetric e) η :=
      isGeodesic_comp_mul_left (isGeodesic_comp_add hbase s₀) σ
    have hηc : Continuous η := by
      apply Continuous.subtype_mk
      apply Continuous.add continuous_const
      apply Continuous.add
      · exact (Continuous.div (by fun_prop) (by fun_prop)
          (fun s => (Real.cosh_pos _).ne')).smul continuous_const
      · exact (Continuous.div continuous_const (by fun_prop)
          (fun s => (Real.cosh_pos _).ne')).smul continuous_const
    -- `v₀` in the `(u, 1ₑ)` frame: `v₀ = va·u + ve·1ₑ`
    have hvhu : va • u = vh := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hva_ne, one_smul]
    have hv₀_eq : v₀ = va • u + ve • EuclideanSpace.single e (1 : ℝ) := by
      rw [hvhu, hvh_def]; abel
    -- position match: `η 0 = γ 0`
    have h0eq : γ 0 = η 0 := by
      apply Subtype.ext
      show p₀ = m + ((r * Real.sinh (σ * 0 + s₀) / Real.cosh (σ * 0 + s₀)) • u
          + (r / Real.cosh (σ * 0 + s₀)) • EuclideanSpace.single e (1 : ℝ))
      rw [mul_zero, zero_add, ← hC_def, hS, hr_def, hm_def]
      match_scalars <;> field_simp <;> ring
    -- chart-velocity match: `d(η.val)/ds (0) = v₀`
    have hDval : σ • ((r / (Real.cosh s₀) ^ 2) • u
        + (-(r * Real.sinh s₀) / (Real.cosh s₀) ^ 2) • EuclideanSpace.single e (1 : ℝ)) = v₀ := by
      rw [← hC_def, hS, hr_def, hσ_def, hv₀_eq]
      match_scalars <;> field_simp
    have hderiv_η : HasDerivAt (fun s => (η s : E)) v₀ 0 := by
      have hbaseD := semicircle_ambient_hasDerivAt e m u r (σ * 0 + s₀)
      have hinner : HasDerivAt (fun s : ℝ => σ * s + s₀) σ 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul σ).add_const s₀
      have hcomp := hbaseD.scomp (0 : ℝ) hinner
      simp only [mul_zero, zero_add] at hcomp
      rw [← hDval]
      exact hcomp
    -- uniqueness forces `γ = η`
    have heqOn : Set.EqOn γ η Set.univ :=
      IsGeodesicOn.eqOn_of_deriv_chartReading_eq (β := γ 0) isOpen_univ isPreconnected_univ
        (hγ.isGeodesicOn _) (hgeoη.isGeodesicOn _) hγc.continuousOn hηc.continuousOn
        (mem_univ 0) h0eq (mem_chart_source _ _) (by
          rw [chartReading_upperHalfSpace, chartReading_upperHalfSpace, hv₀.deriv, hderiv_η.deriv])
    refine ⟨m, u, r, σ, s₀, hm_e, hu_e, hunorm, hr_pos, fun s => ?_⟩
    have hs := heqOn (mem_univ s)
    rw [hs]
    exact (add_assoc _ _ _).symm

end Riemannian.Hyperbolic
