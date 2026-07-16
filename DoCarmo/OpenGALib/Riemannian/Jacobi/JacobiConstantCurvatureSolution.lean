import OpenGALib.Riemannian.Jacobi.JacobiConstantCurvature
import OpenGALib.Riemannian.Jacobi.PairJacobiField
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# do Carmo Ch. 5, §2, Example 2.3 — the explicit constant-curvature Jacobi solutions

`OpenGALib/Riemannian/Jacobi/JacobiConstantCurvature.lean` proves the **curvature reduction**
`R(γ', J)γ' = K₀ J` (do Carmo's equation (2)) for a Jacobi field `J` normal to a unit-speed
geodesic on a manifold of constant sectional curvature `K₀`.  This file closes the remaining
step of do Carmo Example 2.3: the **explicit solutions** of the resulting scalar Jacobi
equation `D²J/dt² + K₀ J = 0`.

do Carmo writes: *"Let `w(t)` be a parallel field along `γ` with `⟨γ'(t), w(t)⟩ = 0` and
`|w(t)| = 1`.  It is easy to verify that*

```
        ⎧ sin(t√K)/√K · w(t),   K > 0,
J(t) =  ⎨ t · w(t),             K = 0,
        ⎩ sinh(t√−K)/√−K · w(t), K < 0,
```

*is a solution of (2) with initial conditions `J(0) = 0`, `J'(0) = w(0)`."*

## Structure

* `isJacobiFieldOn_of_constantCurvature` — **the general reduction to a scalar ODE.**  Given a
  parallel field `w` that is unit and normal to the unit-speed velocity along a chart curve `u`
  (read in the fixed chart at `p`), and any scalar solution `h` of `h'' + K₀ h = 0` (encoded by
  the first- and second-derivative facts `hd1`, `hd2`), the pair `(h · w, h' · w)` is a chart
  Jacobi field (`IsJacobiFieldOn`).  This is the content of do Carmo's *"it is easy to verify"*:
  `D²(h w)/dt² = h'' w` because `w` is parallel, and `R(γ', h w)γ' = h K₀ w` by the curvature
  reduction, so the equation collapses to `(h'' + K₀ h) w = 0`.

* `hasDerivAt_constCurvatureSol_*` / `hasDerivAt_constCurvatureSolDeriv_*` — the three explicit
  scalars `sin(t√K)/√K`, `t`, `sinh(t√−K)/√−K` solve `h'' + K₀ h = 0` with `h(0) = 0`,
  `h'(0) = 1`, so the induced Jacobi field vanishes at `t = 0` with initial covariant derivative
  `w(0)` — do Carmo's `J(0) = 0`, `J'(0) = w(0)`.

* `isJacobiFieldOn_constCurvatureSol_pos` / `_zero` / `_neg` — the three explicit Jacobi fields.

Blueprint: `ex:dc-ch5-2-3` (explicit constant-curvature solutions).

Reference: do Carmo, *Riemannian Geometry*, Ch. 5, Example 2.3.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### The general reduction: `h · w` is a Jacobi field when `h'' + K₀ h = 0` -/

/-- **Math.** **do Carmo Ch. 5, Example 2.3.**  On a manifold of constant sectional curvature
`K₀`, let `u` be the fixed-chart reading (at `p`) of a unit-speed geodesic and `w` a **parallel**
field along `u` that is **unit** and **normal** to the velocity:

* `hunit`: `⟨u̇, u̇⟩ = 1` (unit speed);
* `hperp`: `⟨w, u̇⟩ = 0` (normal);
* `hw_par`: `w' = −Γ(u̇, w)(u)`, i.e. `∇w = 0` (parallel).

Then for any scalar `h` solving the Jacobi equation `h'' + K₀ h = 0` (given by the derivative
facts `hd1 : h' = Dh`, `hd2 : Dh' = −K₀ h`), the pair `(h · w, Dh · w)` is a Jacobi field along
`u`: `D²(h w)/dt² + R(u̇, h w)u̇ = 0`.

Proof of *"it is easy to verify"*: since `w` is parallel, `D(h w)/dt = h' w` and
`D(Dh · w)/dt = Dh' · w = −K₀ h · w`; and by the curvature reduction
(`chartCurvatureOp_isConstantCurvature`, `chartCurvature g p (u t) w u̇ u̇ = K₀ w`) plus
homogeneity, `R(u̇, h w)u̇ = h · K₀ · w`, so `∇(Dh · w) = −R(u̇, h w)u̇`. -/
theorem isJacobiFieldOn_of_constantCurvature (g : RiemannianMetric I M) {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀) (p : M) (u w : ℝ → E) (h Dh : ℝ → ℝ)
    {a b : ℝ}
    (hu_tgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I p).target)
    (hunit : ∀ t ∈ Icc a b, chartMetricInner (I := I) g p (u t) (deriv u t) (deriv u t) = 1)
    (hperp : ∀ t ∈ Icc a b, chartMetricInner (I := I) g p (u t) (w t) (deriv u t) = 0)
    (hw_par : ∀ t ∈ Icc a b, HasDerivWithinAt w
      (-Geodesic.chartChristoffelContraction (I := I) g p (deriv u t) (w t) (u t)) (Icc a b) t)
    (hd1 : ∀ t, HasDerivAt h (Dh t) t)
    (hd2 : ∀ t, HasDerivAt Dh (-K₀ * h t) t) :
    IsJacobiFieldOn (I := I) g p u (fun t => h t • w t) (fun t => Dh t • w t) a b := by
  -- the constant-curvature identity `R(u̇, w)u̇ = K₀ w`, read pointwise along the interval
  have hcc : ∀ t ∈ Icc a b,
      chartCurvature (I := I) g p (u t) (w t) (deriv u t) (deriv u t) = K₀ • w t := by
    intro t ht
    have htgt := hu_tgt t ht
    have hq : (extChartAt I p).symm (u t) ∈ (chartAt H p).source := by
      have := (extChartAt I p).map_target htgt
      rwa [extChartAt_source] at this
    have hu' : u t = extChartAt I p ((extChartAt I p).symm (u t)) :=
      ((extChartAt I p).right_inv htgt).symm
    have hy_int : u t ∈ interior (extChartAt I p).target := by
      rw [(isOpen_extChartAt_target (I := I) p).interior_eq]; exact htgt
    have hop := chartCurvatureOp_isConstantCurvature (I := I) g hK p u t (w t)
      hq hu' (hunit t ht) (hperp t ht)
    rwa [chartCurvatureOp_eq_chartCurvature (I := I) g p u t (w t) hy_int] at hop
  refine ⟨?_, ?_⟩
  · -- `∇(h w) = Dh w`: first pair equation
    intro t ht
    have hprod := ((hd1 t).hasDerivWithinAt (s := Icc a b)).smul (hw_par t ht)
    have hval : Dh t • w t
          - Geodesic.chartChristoffelContraction (I := I) g p (deriv u t) (h t • w t) (u t)
        = h t • (-Geodesic.chartChristoffelContraction (I := I) g p (deriv u t) (w t) (u t))
          + Dh t • w t := by
      rw [Geodesic.chartChristoffelContraction_smul_right, smul_neg]; abel
    rw [hval]; exact hprod
  · -- `∇(Dh w) = −R(u̇, h w)u̇`: second pair equation
    intro t ht
    have hprod := ((hd2 t).hasDerivWithinAt (s := Icc a b)).smul (hw_par t ht)
    have hval :
        (-(chartCurvature (I := I) g p (u t) (h t • w t) (deriv u t) (deriv u t))
          - Geodesic.chartChristoffelContraction (I := I) g p (deriv u t) (Dh t • w t) (u t))
        = Dh t • (-Geodesic.chartChristoffelContraction (I := I) g p (deriv u t) (w t) (u t))
          + (-K₀ * h t) • w t := by
      rw [chartCurvature_smul_left, hcc t ht,
        Geodesic.chartChristoffelContraction_smul_right]
      module
    rw [hval]; exact hprod

/-! ### The three explicit scalar solutions of `h'' + K₀ h = 0`, `h(0) = 0`, `h'(0) = 1` -/

/-- **Math.** `K₀ > 0`: `h(t) = sin(t√K₀)/√K₀` has derivative `Dh(t) = cos(t√K₀)`. -/
theorem hasDerivAt_constCurvatureSol_pos {K₀ : ℝ} (hK : 0 < K₀) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (Real.sqrt K₀ * t) / Real.sqrt K₀)
      (Real.cos (Real.sqrt K₀ * t)) t := by
  have hω : Real.sqrt K₀ ≠ 0 := Real.sqrt_ne_zero'.mpr hK
  have h1 : HasDerivAt (fun t : ℝ => Real.sqrt K₀ * t) (Real.sqrt K₀) t := by
    simpa using (hasDerivAt_id t).const_mul (Real.sqrt K₀)
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (Real.sqrt K₀ * t))
      (Real.cos (Real.sqrt K₀ * t) * Real.sqrt K₀) t := (Real.hasDerivAt_sin _).comp t h1
  have h3 := h2.div_const (Real.sqrt K₀)
  convert h3 using 1
  field_simp

/-- **Math.** `K₀ > 0`: `Dh(t) = cos(t√K₀)` has derivative `−K₀ · (sin(t√K₀)/√K₀)`, i.e. the
scalar Jacobi equation `Dh' = −K₀ h`. -/
theorem hasDerivAt_constCurvatureSolDeriv_pos {K₀ : ℝ} (hK : 0 < K₀) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cos (Real.sqrt K₀ * t))
      (-K₀ * (Real.sin (Real.sqrt K₀ * t) / Real.sqrt K₀)) t := by
  have hω : Real.sqrt K₀ ≠ 0 := Real.sqrt_ne_zero'.mpr hK
  have h1 : HasDerivAt (fun t : ℝ => Real.sqrt K₀ * t) (Real.sqrt K₀) t := by
    simpa using (hasDerivAt_id t).const_mul (Real.sqrt K₀)
  have h2 : HasDerivAt (fun t : ℝ => Real.cos (Real.sqrt K₀ * t))
      (-Real.sin (Real.sqrt K₀ * t) * Real.sqrt K₀) t := (Real.hasDerivAt_cos _).comp t h1
  convert h2 using 1
  field_simp
  rw [Real.sq_sqrt hK.le]

/-- **Math.** `K₀ = 0`: `h(t) = t` has derivative `Dh(t) = 1`. -/
theorem hasDerivAt_constCurvatureSol_zero (t : ℝ) :
    HasDerivAt (fun t : ℝ => t) (1 : ℝ) t := hasDerivAt_id t

/-- **Math.** `K₀ = 0`: `Dh(t) = 1` has derivative `0 = −0 · t`, the scalar Jacobi equation
`Dh' = −K₀ h` at `K₀ = 0`. -/
theorem hasDerivAt_constCurvatureSolDeriv_zero (t : ℝ) :
    HasDerivAt (fun _ : ℝ => (1 : ℝ)) (-(0 : ℝ) * t) t := by
  simpa using hasDerivAt_const t (1 : ℝ)

/-- **Math.** `K₀ < 0`: `h(t) = sinh(t√(−K₀))/√(−K₀)` has derivative `Dh(t) = cosh(t√(−K₀))`. -/
theorem hasDerivAt_constCurvatureSol_neg {K₀ : ℝ} (hK : K₀ < 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sinh (Real.sqrt (-K₀) * t) / Real.sqrt (-K₀))
      (Real.cosh (Real.sqrt (-K₀) * t)) t := by
  have hpos : (0 : ℝ) < -K₀ := by linarith
  have hω : Real.sqrt (-K₀) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have h1 : HasDerivAt (fun t : ℝ => Real.sqrt (-K₀) * t) (Real.sqrt (-K₀)) t := by
    simpa using (hasDerivAt_id t).const_mul (Real.sqrt (-K₀))
  have h2 : HasDerivAt (fun t : ℝ => Real.sinh (Real.sqrt (-K₀) * t))
      (Real.cosh (Real.sqrt (-K₀) * t) * Real.sqrt (-K₀)) t := (Real.hasDerivAt_sinh _).comp t h1
  have h3 := h2.div_const (Real.sqrt (-K₀))
  convert h3 using 1
  field_simp

/-- **Math.** `K₀ < 0`: `Dh(t) = cosh(t√(−K₀))` has derivative `−K₀ · (sinh(t√(−K₀))/√(−K₀))`,
the scalar Jacobi equation `Dh' = −K₀ h`. -/
theorem hasDerivAt_constCurvatureSolDeriv_neg {K₀ : ℝ} (hK : K₀ < 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cosh (Real.sqrt (-K₀) * t))
      (-K₀ * (Real.sinh (Real.sqrt (-K₀) * t) / Real.sqrt (-K₀))) t := by
  have hpos : (0 : ℝ) < -K₀ := by linarith
  have hω : Real.sqrt (-K₀) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have h1 : HasDerivAt (fun t : ℝ => Real.sqrt (-K₀) * t) (Real.sqrt (-K₀)) t := by
    simpa using (hasDerivAt_id t).const_mul (Real.sqrt (-K₀))
  have h2 : HasDerivAt (fun t : ℝ => Real.cosh (Real.sqrt (-K₀) * t))
      (Real.sinh (Real.sqrt (-K₀) * t) * Real.sqrt (-K₀)) t := (Real.hasDerivAt_cosh _).comp t h1
  convert h2 using 1
  field_simp
  rw [Real.sq_sqrt hpos.le]
  ring

/-! ### The three explicit constant-curvature Jacobi fields -/

/-- **Math.** **do Carmo Ex. 2.3, `K₀ > 0`.**  On a manifold of constant curvature `K₀ > 0`,
`J(t) = (sin(t√K₀)/√K₀) · w(t)` is a Jacobi field along the unit geodesic, with `J(0) = 0` and
initial covariant derivative `w(0)`. -/
theorem isJacobiFieldOn_constCurvatureSol_pos (g : RiemannianMetric I M) {K₀ : ℝ} (hKpos : 0 < K₀)
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀) (p : M) (u w : ℝ → E) {a b : ℝ}
    (hu_tgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I p).target)
    (hunit : ∀ t ∈ Icc a b, chartMetricInner (I := I) g p (u t) (deriv u t) (deriv u t) = 1)
    (hperp : ∀ t ∈ Icc a b, chartMetricInner (I := I) g p (u t) (w t) (deriv u t) = 0)
    (hw_par : ∀ t ∈ Icc a b, HasDerivWithinAt w
      (-Geodesic.chartChristoffelContraction (I := I) g p (deriv u t) (w t) (u t)) (Icc a b) t) :
    IsJacobiFieldOn (I := I) g p u
      (fun t => (Real.sin (Real.sqrt K₀ * t) / Real.sqrt K₀) • w t)
      (fun t => Real.cos (Real.sqrt K₀ * t) • w t) a b
    ∧ (Real.sin (Real.sqrt K₀ * 0) / Real.sqrt K₀) • w 0 = 0
    ∧ Real.cos (Real.sqrt K₀ * 0) • w 0 = w 0 :=
  ⟨isJacobiFieldOn_of_constantCurvature (I := I) g hK p u w _ _ hu_tgt hunit hperp hw_par
      (hasDerivAt_constCurvatureSol_pos hKpos) (hasDerivAt_constCurvatureSolDeriv_pos hKpos),
    by simp, by simp⟩

/-- **Math.** **do Carmo Ex. 2.3, `K₀ = 0`.**  On a flat manifold, `J(t) = t · w(t)` is a Jacobi
field along the unit geodesic, with `J(0) = 0` and initial covariant derivative `w(0)`. -/
theorem isJacobiFieldOn_constCurvatureSol_zero (g : RiemannianMetric I M)
    (hK : g.leviCivitaConnection.IsConstantCurvature g 0) (p : M) (u w : ℝ → E) {a b : ℝ}
    (hu_tgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I p).target)
    (hunit : ∀ t ∈ Icc a b, chartMetricInner (I := I) g p (u t) (deriv u t) (deriv u t) = 1)
    (hperp : ∀ t ∈ Icc a b, chartMetricInner (I := I) g p (u t) (w t) (deriv u t) = 0)
    (hw_par : ∀ t ∈ Icc a b, HasDerivWithinAt w
      (-Geodesic.chartChristoffelContraction (I := I) g p (deriv u t) (w t) (u t)) (Icc a b) t) :
    IsJacobiFieldOn (I := I) g p u (fun t => t • w t) (fun t => (1 : ℝ) • w t) a b
    ∧ (0 : ℝ) • w 0 = 0 ∧ (1 : ℝ) • w 0 = w 0 :=
  ⟨isJacobiFieldOn_of_constantCurvature (I := I) g hK p u w _ _ hu_tgt hunit hperp hw_par
      hasDerivAt_constCurvatureSol_zero hasDerivAt_constCurvatureSolDeriv_zero,
    by simp, by simp⟩

/-- **Math.** **do Carmo Ex. 2.3, `K₀ < 0`.**  On a manifold of constant curvature `K₀ < 0`,
`J(t) = (sinh(t√(−K₀))/√(−K₀)) · w(t)` is a Jacobi field along the unit geodesic, with `J(0) = 0`
and initial covariant derivative `w(0)`. -/
theorem isJacobiFieldOn_constCurvatureSol_neg (g : RiemannianMetric I M) {K₀ : ℝ} (hKneg : K₀ < 0)
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀) (p : M) (u w : ℝ → E) {a b : ℝ}
    (hu_tgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I p).target)
    (hunit : ∀ t ∈ Icc a b, chartMetricInner (I := I) g p (u t) (deriv u t) (deriv u t) = 1)
    (hperp : ∀ t ∈ Icc a b, chartMetricInner (I := I) g p (u t) (w t) (deriv u t) = 0)
    (hw_par : ∀ t ∈ Icc a b, HasDerivWithinAt w
      (-Geodesic.chartChristoffelContraction (I := I) g p (deriv u t) (w t) (u t)) (Icc a b) t) :
    IsJacobiFieldOn (I := I) g p u
      (fun t => (Real.sinh (Real.sqrt (-K₀) * t) / Real.sqrt (-K₀)) • w t)
      (fun t => Real.cosh (Real.sqrt (-K₀) * t) • w t) a b
    ∧ (Real.sinh (Real.sqrt (-K₀) * 0) / Real.sqrt (-K₀)) • w 0 = 0
    ∧ Real.cosh (Real.sqrt (-K₀) * 0) • w 0 = w 0 :=
  ⟨isJacobiFieldOn_of_constantCurvature (I := I) g hK p u w _ _ hu_tgt hunit hperp hw_par
      (hasDerivAt_constCurvatureSol_neg hKneg) (hasDerivAt_constCurvatureSolDeriv_neg hKneg),
    by simp, by simp⟩

end Riemannian.Jacobi

end
