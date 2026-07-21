import DoCarmoLib.Riemannian.Variation.CovariantField

/-!
# The first variation of energy: the integration-by-parts core

do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.4 (`prop:dc-ch9-2-4`) and
Prop. 2.5 (`prop:dc-ch9-2-5`).

do Carmo's first variation formula reads
$$
\frac{1}{2}E'(0)
  = -\int_0^a \Big\langle V, \frac{D}{dt}\frac{dc}{dt}\Big\rangle dt
    - \sum_i \Big\langle V(t_i), \frac{dc}{dt}(t_i^+) - \frac{dc}{dt}(t_i^-)\Big\rangle
    - \Big\langle V(0), \frac{dc}{dt}(0)\Big\rangle
    + \Big\langle V(a), \frac{dc}{dt}(a)\Big\rangle. \qquad (1)
$$

Its proof has two halves, and **they are independent**:

1. *the surface half* — differentiate `E(s) = ∫ ⟨∂f/∂t, ∂f/∂t⟩ dt` under the integral
   sign and exchange `D/∂s ∂f/∂t = D/∂t ∂f/∂s` (the symmetry of the connection), to
   reach `½E'(0) = ∫₀^a ⟨DV, dc/dt⟩ dt`;
2. *the intrinsic half* — integrate `∫₀^a ⟨DV, dc/dt⟩ dt` by parts, using metric
   compatibility `d/dt⟨V, W⟩ = ⟨DV, W⟩ + ⟨V, DW⟩`, to reach the right-hand side of (1).

This file supplies **half 2**, and half 2 alone already *is* formula (1) once the
identification `½E'(0) = ∫₀^a ⟨DV, dc/dt⟩ dt` is granted. The point worth recording is
that half 2 needs **no parametrized surface at all**: it is a statement about a curve
`γ` and two covariant-derivative pairs `(V, DV)`, `(W, DW)` along it, in the language
`def:dc-ch9-2-covariant-pair` (`IsCovariantDerivFieldAlongOn`) already provides. Half 1
is where the two-parameter surface — still chart-only — is needed.

That split is what makes this file possible today: the surface `D/∂s`, `D/∂t` operators
exist only in a fixed chart (`Jacobi/SurfaceCurvatureCommutation.lean`), whereas
`IsCovariantDerivFieldAlongOn` is chart-free, so the conclusion here holds for a curve
that leaves every chart.

## Contents

* `IsCovariantDerivFieldAlongOn.integral_metricInner_add` — the Leibniz rule
  `d/dt⟨V, W⟩ = ⟨DV, W⟩ + ⟨V, DW⟩` integrated over `[a, b]`: the fundamental theorem of
  calculus applied to `IsCovariantDerivFieldAlongOn.hasDerivAt_metricInner`.
* `IsCovariantDerivFieldAlongOn.integral_metricInner_covariantDeriv_left` —
  **integration by parts**, the intrinsic half of formula (1).
* `IsCovariantDerivFieldAlongOn.integral_metricInner_eq_neg_integral_of_proper` —
  formula (1) for a *proper* variation: the boundary terms drop.
* `IsCovariantDerivFieldAlongOn.integral_metricInner_covariantDeriv_eq_zero_of_geodesic`
  — `prop:dc-ch9-2-5`, the direction *geodesic ⇒ critical point*.

## Scope and what is not claimed

`hasDerivAt_metricInner` produces a derivative at **interior** times only, so the FTC
used here is `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, which asks for
continuity on the closed `[a, b]` and differentiability on the open `(a, b)`. The
closed-interval continuity is **derived**, not hypothesised
(`IsCovariantDerivFieldAlongOn.continuousOn_metricInner`): differentiability degrades at
the endpoints, continuity does not, because `IsCovariantDerivSolOn` demands
`HasDerivWithinAt` over the *closed* chart window.

Interval-integrability of the two pairings **is** hypothesised, and that one is not
removable at this generality. do Carmo's curves are only *piecewise* differentiable, so
their velocity jumps at the breakpoints — which is precisely why (1) carries the jump sum
`∑_i ⟨V(t_i), Δ(dc/dt)(t_i)⟩`. These results are stated on one segment; the jump terms of
(1) arise by summing them over the subdivision, where the boundary terms at the interior
breakpoints telescope into the differences `dc/dt(t_i^+) - dc/dt(t_i^-)`.

The velocity is carried as an abstract pair `(W, DW)` rather than as `DCVelocity γ`, so
that nothing in the type forces `DW` to be the covariant derivative of `W` — that is
supplied at each call site by an `IsCovariantDerivFieldAlongOn` hypothesis. Taking
`W = dc/dt` and `DW = D/dt(dc/dt)` specializes to do Carmo's statement. This is **not**
the convention `indexForm` (`rem:dc-ch9-2-10`) uses for the velocity: `indexForm` names
the velocity concretely, as `DCVelocity γ`, and takes a free pair only for the
*variational* field. Joining the two will require identifying an abstract `(W, DW)` with
`DCVelocity γ` and its covariant derivative; no such bridge exists yet.

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.4 and Prop. 2.5;
the Leibniz rule used throughout is Ch. 2, Prop. 3.2.
-/

open Set Riemannian Filter MeasureTheory
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-! ### The Leibniz rule, integrated -/

/-- **Math.** do Carmo Ch. 2, Prop. 3.2, integrated over `[a, b]`.  For two
covariant-derivative pairs `(V, DV)`, `(W, DW)` along `γ`,
$$\int_a^b \Big(\Big\langle\frac{DV}{dt}, W\Big\rangle
  + \Big\langle V, \frac{DW}{dt}\Big\rangle\Big) dt
  = \langle V(b), W(b)\rangle - \langle V(a), W(a)\rangle .$$

This is the fundamental theorem of calculus applied to
`IsCovariantDerivFieldAlongOn.hasDerivAt_metricInner`, which supplies the derivative at
interior times; `IsCovariantDerivFieldAlongOn.continuousOn_metricInner` supplies the
continuity on the closed interval that the endpoint values need. -/
theorem IsCovariantDerivFieldAlongOn.integral_metricInner_add
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV W DW : ℝ → E} {a b : ℝ}
    (hV : IsCovariantDerivFieldAlongOn (I := I) g γ V DV a b)
    (hW : IsCovariantDerivFieldAlongOn (I := I) g γ W DW a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hab : a ≤ b)
    (hint : IntervalIntegrable
      (fun t => g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (W t)
        + g.metricInner (γ t) (V t : TangentSpace I (γ t)) (DW t)) volume a b) :
    ∫ t in a..b, (g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (W t)
        + g.metricInner (γ t) (V t : TangentSpace I (γ t)) (DW t))
      = g.metricInner (γ b) (V b : TangentSpace I (γ b)) (W b)
        - g.metricInner (γ a) (V a : TangentSpace I (γ a)) (W a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (hV.continuousOn_metricInner hW hdiff hγc) ?_ hint
  intro x hx
  exact (hV.hasDerivAt_metricInner hW hdiff hγc hx).hasDerivWithinAt

/-! ### Integration by parts: the intrinsic half of formula (1) -/

/-- **Math.** do Carmo Ch. 9, `prop:dc-ch9-2-4`, **the intrinsic half**: integration by
parts along `γ`,
$$\int_a^b \Big\langle\frac{DV}{dt}, W\Big\rangle dt
  = \langle V(b), W(b)\rangle - \langle V(a), W(a)\rangle
    - \int_a^b \Big\langle V, \frac{DW}{dt}\Big\rangle dt .$$

Taking `W = dc/dt` and `DW = D/dt(dc/dt)`, and granting the surface half
`½E'(0) = ∫_a^b ⟨DV, dc/dt⟩ dt`, this *is* do Carmo's formula (1) on a segment carrying
no breakpoint: the two boundary terms are his `-⟨V(0), dc/dt(0)⟩ + ⟨V(a), dc/dt(a)⟩`, and
the remaining integral is his `-∫₀^a ⟨V, D/dt(dc/dt)⟩ dt`.  Summing over the segments
`[t_i, t_{i+1}]` of do Carmo's subdivision, the boundary terms at the interior
breakpoints telescope into his jump sum `-∑_i ⟨V(t_i), dc/dt(t_i^+) - dc/dt(t_i^-)⟩`. -/
theorem IsCovariantDerivFieldAlongOn.integral_metricInner_covariantDeriv_left
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV W DW : ℝ → E} {a b : ℝ}
    (hV : IsCovariantDerivFieldAlongOn (I := I) g γ V DV a b)
    (hW : IsCovariantDerivFieldAlongOn (I := I) g γ W DW a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hab : a ≤ b)
    (hint₁ : IntervalIntegrable
      (fun t => g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (W t)) volume a b)
    (hint₂ : IntervalIntegrable
      (fun t => g.metricInner (γ t) (V t : TangentSpace I (γ t)) (DW t)) volume a b) :
    ∫ t in a..b, g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (W t)
      = (g.metricInner (γ b) (V b : TangentSpace I (γ b)) (W b)
          - g.metricInner (γ a) (V a : TangentSpace I (γ a)) (W a))
        - ∫ t in a..b, g.metricInner (γ t) (V t : TangentSpace I (γ t)) (DW t) := by
  have hsum := hV.integral_metricInner_add hW hdiff hγc hab (hint₁.add hint₂)
  rw [intervalIntegral.integral_add hint₁ hint₂] at hsum
  linarith

/-! ### Proper variations, and geodesics as critical points -/

/-- **Math.** do Carmo Ch. 9, formula (1) for a **proper** variation on a segment: when
`V` vanishes at both endpoints the boundary terms drop and
$$\int_a^b \Big\langle\frac{DV}{dt}, W\Big\rangle dt
  = -\int_a^b \Big\langle V, \frac{DW}{dt}\Big\rangle dt .$$

`V(a) = V(b) = 0` is do Carmo's properness condition `V(0) = V(a) = 0`
(`def:dc-ch9-2-1`). -/
theorem IsCovariantDerivFieldAlongOn.integral_metricInner_eq_neg_integral_of_proper
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV W DW : ℝ → E} {a b : ℝ}
    (hV : IsCovariantDerivFieldAlongOn (I := I) g γ V DV a b)
    (hW : IsCovariantDerivFieldAlongOn (I := I) g γ W DW a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hab : a ≤ b)
    (hint₁ : IntervalIntegrable
      (fun t => g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (W t)) volume a b)
    (hint₂ : IntervalIntegrable
      (fun t => g.metricInner (γ t) (V t : TangentSpace I (γ t)) (DW t)) volume a b)
    (hVa : V a = 0) (hVb : V b = 0) :
    ∫ t in a..b, g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (W t)
      = -∫ t in a..b, g.metricInner (γ t) (V t : TangentSpace I (γ t)) (DW t) := by
  have h := hV.integral_metricInner_covariantDeriv_left hW hdiff hγc hab hint₁ hint₂
  -- the two boundary terms die because the variation is proper.  `rw` cannot close these:
  -- the `0` left by `hVa`/`hVb` is `(0 : E)`, while `metricInner_zero_left`'s is
  -- `(0 : TangentSpace I (γ a))` — defeq but not syntactically equal, so `exact` is needed.
  have hba : g.metricInner (γ a) (V a : TangentSpace I (γ a)) (W a) = 0 := by
    rw [hVa]; exact g.metricInner_zero_left _ _
  have hbb : g.metricInner (γ b) (V b : TangentSpace I (γ b)) (W b) = 0 := by
    rw [hVb]; exact g.metricInner_zero_left _ _
  rw [h, hba, hbb]
  ring

/-- **Math.** do Carmo Ch. 9, `prop:dc-ch9-2-5`, **the direction *geodesic ⇒ critical
point***.  If `γ` is a geodesic — `D/dt(dc/dt) = 0`, here the hypothesis that the
velocity pair is `(W, 0)` — and the variation is proper (`V(a) = V(b) = 0`), then
$$\int_a^b \Big\langle\frac{DV}{dt}, \frac{dc}{dt}\Big\rangle dt = 0,$$
i.e. `½E'(0) = 0`: *all terms of (1) are zero*, in do Carmo's words.  The integral term
dies because `D/dt(dc/dt) = 0`, and the boundary terms because the variation is proper.

This is the easy direction of `prop:dc-ch9-2-5`.  The converse — a critical point of the
energy for *every* proper variation is a geodesic — additionally needs
`prop:dc-ch9-2-2` (a variation realizing a prescribed variational field `V`), applied to
the two special fields `V = g·D/dt(dc/dt)` and `V̄` matching the velocity jumps; it is
not proved here. -/
theorem IsCovariantDerivFieldAlongOn.integral_metricInner_covariantDeriv_eq_zero_of_geodesic
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV W : ℝ → E} {a b : ℝ}
    (hV : IsCovariantDerivFieldAlongOn (I := I) g γ V DV a b)
    (hW : IsCovariantDerivFieldAlongOn (I := I) g γ W (fun _ => 0) a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hab : a ≤ b)
    (hint₁ : IntervalIntegrable
      (fun t => g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (W t)) volume a b)
    (hVa : V a = 0) (hVb : V b = 0) :
    ∫ t in a..b, g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (W t) = 0 := by
  have hzero : ∀ t, g.metricInner (γ t) (V t : TangentSpace I (γ t)) ((fun _ : ℝ => (0 : E)) t)
      = 0 := fun t => g.metricInner_zero_right _ _
  have hint₂ : IntervalIntegrable
      (fun t => g.metricInner (γ t) (V t : TangentSpace I (γ t)) ((fun _ : ℝ => (0 : E)) t))
      volume a b := by
    simp only [hzero]
    exact intervalIntegrable_const
  have h := hV.integral_metricInner_eq_neg_integral_of_proper hW hdiff hγc hab hint₁
    hint₂ hVa hVb
  simpa only [hzero, intervalIntegral.integral_zero, neg_zero] using h

end Riemannian.Variation
