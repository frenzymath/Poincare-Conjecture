import Mathlib.Analysis.Calculus.DerivativeTest
import DoCarmoLib.Riemannian.Exponential.GaussLemma
import DoCarmoLib.Riemannian.Exponential.LocalDiffeo
import DoCarmoLib.Riemannian.Exponential.Ray

set_option linter.unusedSectionVars false

/-!
# Convex neighborhoods: the second-derivative kernel (do Carmo Ch. 3, §4)

do Carmo's proof that small geodesic balls are strongly convex (Ch. 3, §4, Lemma
4.1 and Prop. 4.2) studies, for a geodesic `γ(t)` tangent to the geodesic sphere
`S_r(p)`, the squared radial distance read in normal coordinates at `p`,

`F(t) = |u(t)|²_p,     u(t) = exp_p⁻¹(γ(t)),`

and its first two time-derivatives
`∂F/∂t = 2⟨∂u/∂t, u⟩_p`,
`∂²F/∂t² = 2⟨∂²u/∂t², u⟩_p + 2|∂u/∂t|²_p`
(do Carmo's displayed formulas). At `q = p` the geodesic is the radial ray, so
`u(t) = t v` and `∂²F/∂t²(0, p, v) = 2|v|²_p = 2 > 0` for unit `v` — the strict
minimum that forces the tangent geodesic to stay outside `B_r(p)`.

This file isolates the *pointwise-in-`t`* analytic kernel of that argument, all
for the **fixed** chart Gram inner product `⟨·,·⟩_p = chartMetricInner g p (φ_p p)`
at the reference point `p`:

* `hasDerivAt_chartMetricInner` — the product rule for the fixed bilinear form
  along two curves: `d/dt ⟨f(t), h(t)⟩_p = ⟨f'(t), h(t)⟩_p + ⟨f(t), h'(t)⟩_p`.
* `hasDerivAt_chartMetricInner_diag` — do Carmo's `∂F/∂t = 2⟨u', u⟩_p`.
* `hasDerivAt_deriv_chartMetricInner_diag` — do Carmo's
  `∂²F/∂t² = 2⟨u'', u⟩_p + 2|u'|²_p` (the derivative of `∂F/∂t`).
* `hasDerivAt_secondDeriv_chartMetricInner_smul` — the center specialization
  `u(t) = t v`, giving `∂²F/∂t²(0) = 2⟨v, v⟩_p`.
* `expMap_inv_smul_eq` — along the radial ray the normal coordinate is `t v`
  itself: `exp_p⁻¹(exp_p(t v)) = t v` on the injectivity ball, so `F` is literally
  the fixed-form quadratic `t ↦ ⟨t v, t v⟩_p = t² ⟨v, v⟩_p`.
* `eventually_ge_of_deriv_deriv_pos` — the strict-minimum mechanism: a curve with
  `F'(0) = 0` and `F''(0) > 0` satisfies `F(t) ≥ F(0)` near `0`, i.e. the tangent
  geodesic never re-enters the open ball whose boundary sphere it touches.

The **residual** for the full `lem:dc-ch3-4-1` is the joint continuity of
`∂²F/∂t²(0, q, v)` in the moving base point `q` (needed to propagate the strict
positivity from `q = p` to a neighborhood). That requires packaging the moving-base
geodesic family (`exists_totallyNormal_neighborhood`) and the `C²` exponential
inverse (`exists_c2_local_diffeomorphism_expMap`) into a single object that is
`C²` in `t` with `(q, v)`-continuous second time-derivative — no such joint object
exists in the tree yet. This file supplies the fibrewise (fixed-`(q,v)`) calculus
on which that assembly will rest.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

section BilinearDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **Product rule for the fixed chart Gram inner product.** For the
*fixed* base point `y` (the metric `⟨·,·⟩_y` does not vary), two curves
`f, h : ℝ → E` differentiable at `t` satisfy
`d/dt ⟨f(t), h(t)⟩_y = ⟨f'(t), h(t)⟩_y + ⟨f(t), h'(t)⟩_y`.
This is the Leibniz rule for the symmetric bilinear form `chartMetricInner g α y`,
proved by differentiating the finite double sum
`∑_{i,j} G_{ij}(y)\, f^i(t)\, h^j(t)` termwise (each chart coordinate is a
continuous linear functional). -/
theorem hasDerivAt_chartMetricInner (g : RiemannianMetric I M) (α : M) (y : E)
    {f h : ℝ → E} {f' h' : E} {t : ℝ}
    (hf : HasDerivAt f f' t) (hh : HasDerivAt h h' t) :
    HasDerivAt (fun s : ℝ => chartMetricInner (I := I) g α y (f s) (h s))
      (chartMetricInner (I := I) g α y f' (h t)
        + chartMetricInner (I := I) g α y (f t) h') t := by
  classical
  -- coordinate derivatives, via the continuous linear functionals `chartCoordFunctional`
  have hcf : ∀ i, HasDerivAt (fun s : ℝ => Geodesic.chartCoord (E := E) i (f s))
      (Geodesic.chartCoord (E := E) i f') t := by
    intro i
    have := (Geodesic.chartCoordFunctional (E := E) i).hasFDerivAt.comp_hasDerivAt t hf
    simpa only [Geodesic.chartCoordFunctional_apply] using this
  have hch : ∀ j, HasDerivAt (fun s : ℝ => Geodesic.chartCoord (E := E) j (h s))
      (Geodesic.chartCoord (E := E) j h') t := by
    intro j
    have := (Geodesic.chartCoordFunctional (E := E) j).hasFDerivAt.comp_hasDerivAt t hh
    simpa only [Geodesic.chartCoordFunctional_apply] using this
  -- differentiate the double sum termwise, working with function-level sums so
  -- `HasDerivAt.sum` unifies against `∑ i ∈ univ, A i`
  have hsum : HasDerivAt
      (∑ i, ∑ j, fun s : ℝ => chartGramOnE (I := I) g α i j y
        * Geodesic.chartCoord (E := E) i (f s) * Geodesic.chartCoord (E := E) j (h s))
      (∑ i, ∑ j,
        ((chartGramOnE (I := I) g α i j y * Geodesic.chartCoord (E := E) i f')
            * Geodesic.chartCoord (E := E) j (h t)
          + (chartGramOnE (I := I) g α i j y * Geodesic.chartCoord (E := E) i (f t))
            * Geodesic.chartCoord (E := E) j h')) t := by
    refine HasDerivAt.sum (fun i _ => ?_)
    refine HasDerivAt.sum (fun j _ => ?_)
    exact ((hcf i).const_mul (chartGramOnE (I := I) g α i j y)).mul (hch j)
  -- the summed function is `s ↦ ⟨f s, h s⟩`, and the derivative value is the split
  have hfun : (∑ i, ∑ j, fun s : ℝ => chartGramOnE (I := I) g α i j y
        * Geodesic.chartCoord (E := E) i (f s) * Geodesic.chartCoord (E := E) j (h s))
      = fun s : ℝ => chartMetricInner (I := I) g α y (f s) (h s) := by
    funext s
    simp only [Finset.sum_apply, chartMetricInner_def]
  have hval : chartMetricInner (I := I) g α y f' (h t)
        + chartMetricInner (I := I) g α y (f t) h'
      = ∑ i, ∑ j,
          ((chartGramOnE (I := I) g α i j y * Geodesic.chartCoord (E := E) i f')
              * Geodesic.chartCoord (E := E) j (h t)
            + (chartGramOnE (I := I) g α i j y * Geodesic.chartCoord (E := E) i (f t))
              * Geodesic.chartCoord (E := E) j h') := by
    rw [chartMetricInner_def, chartMetricInner_def, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
  rw [hfun] at hsum
  rw [hval]
  exact hsum

/-- **Math.** **do Carmo's `∂F/∂t = 2⟨u', u⟩_p`.** For a curve `u` differentiable
at `t`, the squared norm `F(s) = ⟨u(s), u(s)⟩_y` in the fixed chart Gram inner
product has derivative `2⟨u'(t), u(t)⟩_y` at `t`. -/
theorem hasDerivAt_chartMetricInner_diag (g : RiemannianMetric I M) (α : M) (y : E)
    {u : ℝ → E} {u' : E} {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s : ℝ => chartMetricInner (I := I) g α y (u s) (u s))
      (2 * chartMetricInner (I := I) g α y u' (u t)) t := by
  have h := hasDerivAt_chartMetricInner (I := I) g α y hu hu
  rw [chartMetricInner_symm (I := I) g α y (u t) u'] at h
  rw [two_mul]
  exact h

/-- **Math.** **do Carmo's `∂²F/∂t² = 2⟨u'', u⟩_p + 2|u'|²_p`.** If a curve `u` has
first derivative `u' s` for every `s` (near `t`) and `u'` is differentiable at `t`
with second derivative `u''`, then the first derivative of `F`, namely
`s ↦ 2⟨u'(s), u(s)⟩_y`, is itself differentiable at `t` with derivative
`2⟨u'', u(t)⟩_y + 2⟨u'(t), u'(t)⟩_y`. Together with
`hasDerivAt_chartMetricInner_diag` this is do Carmo's displayed second
time-derivative of `F(t) = |u(t)|²_p`. -/
theorem hasDerivAt_deriv_chartMetricInner_diag (g : RiemannianMetric I M) (α : M)
    (y : E) {u u' : ℝ → E} {u'' : E} {t : ℝ}
    (hu : HasDerivAt u (u' t) t) (hu' : HasDerivAt u' u'' t) :
    HasDerivAt (fun s : ℝ => 2 * chartMetricInner (I := I) g α y (u' s) (u s))
      (2 * (chartMetricInner (I := I) g α y u'' (u t)
        + chartMetricInner (I := I) g α y (u' t) (u' t))) t :=
  (hasDerivAt_chartMetricInner (I := I) g α y hu' hu).const_mul 2

/-- **Math.** **Center Hessian, abstract form.** For the radial curve `u(s) = s • v`
the first-derivative field `s ↦ 2⟨v, s • v⟩_y` of `F(s) = ⟨s v, s v⟩_y = s²⟨v, v⟩_y`
has derivative `2⟨v, v⟩_y` at `0`. This is do Carmo's `∂²F/∂t²(0, p, v) = 2|v|²_p`
(with `u' = v` constant, `u'' = 0`). -/
theorem hasDerivAt_secondDeriv_chartMetricInner_smul (g : RiemannianMetric I M)
    (α : M) (y : E) (v : E) :
    HasDerivAt (fun s : ℝ => 2 * chartMetricInner (I := I) g α y v (s • v))
      (2 * chartMetricInner (I := I) g α y v v) 0 := by
  have hrw : (fun s : ℝ => 2 * chartMetricInner (I := I) g α y v (s • v))
      = fun s : ℝ => (2 * chartMetricInner (I := I) g α y v v) * s := by
    funext s
    rw [chartMetricInner_smul_right]
    ring
  rw [hrw]
  simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * chartMetricInner (I := I) g α y v v)

end BilinearDerivative

section StrictMinimum

/-- **Math.** **The strict-minimum mechanism.** A twice-differentiable curve `F`
with `F'(0) = 0` and `F''(0) > 0` has `F(0) ≤ F(t)` for all `t` near `0`. In
do Carmo's §4 argument, with `F(t) = |exp_p⁻¹(γ(t))|²_p` and `F(0) = r²`, this says
the geodesic tangent to `S_r(p)` at `γ(0)` keeps `|exp_p⁻¹(γ(t))|² ≥ r²`, i.e. it
does not re-enter the open geodesic ball `B_r(p)`. -/
theorem eventually_ge_of_deriv_deriv_pos {F : ℝ → ℝ}
    (hF'' : deriv (deriv F) 0 > 0) (hF' : deriv F 0 = 0) (hFc : ContinuousAt F 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), F 0 ≤ F t :=
  (isLocalMin_of_deriv_deriv_pos hF'' hF' hFc :)

end StrictMinimum

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The normal coordinate along the radial ray is the ray itself.**
There is `ε > 0` and a local inverse `finv` of `φ_p ∘ exp_p` on `B_ε(0)` such that
for every `v` and every `t` with `‖t • v‖ < ε`,
`exp_p⁻¹(exp_p(t v)) = t v` (read in the chart at `p`). Hence along the radial ray
do Carmo's `u(t) = exp_p⁻¹(γ(t, p, v))` is literally `t v`, and
`F(t) = |u(t)|²_p = t²|v|²_p`. -/
theorem exists_expMap_inv_smul_eq (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ finv : E → E,
      (∀ w : E, ‖w‖ < ε →
        finv (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) ∧
      ∀ (v : E) (t : ℝ), ‖t • v‖ < ε →
        finv (extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
          = t • v := by
  obtain ⟨ε, hε, _hdom, _hsrc, _hinj, _hopen, _hcd, finv, hfinvL, _hfinvC⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  exact ⟨ε, hε, finv, hfinvL, fun v t ht => hfinvL (t • v) ht⟩

/-- **Math.** **do Carmo's center Hessian `∂²F/∂t²(0, p, v) = 2|v|²_p`** (Ch. 3, §4,
Lemma 4.1, the case `q = p`). Along the radial geodesic `t ↦ exp_p(t v)` the normal
coordinate is `u(t) = t v` (`exists_expMap_inv_smul_eq`), so the squared radial
distance `F(t) = |u(t)|²_p` has first-derivative field `s ↦ 2⟨v, s v⟩_p` with second
derivative `2⟨v, v⟩_p = 2|v|²_p` at `t = 0`. In particular, for a `g_p`-unit vector
`v`, `∂²F/∂t²(0, p, v) = 2 > 0`, the strict minimum that seeds strong convexity. -/
theorem hasDerivAt_secondDeriv_expMap_inv_sqNorm_radial (g : RiemannianMetric I M)
    (p : M) (v : E) :
    HasDerivAt
      (fun s : ℝ => 2 * chartMetricInner (I := I) g p (extChartAt I p p) v (s • v))
      (2 * chartMetricInner (I := I) g p (extChartAt I p p) v v) 0 :=
  hasDerivAt_secondDeriv_chartMetricInner_smul (I := I) g p (extChartAt I p p) v

/-- **Math.** **The metric at `p` is positive definite in normal coordinates.** For
`v ≠ 0`, `|v|²_p = ⟨v, v⟩_p > 0`. Combined with
`hasDerivAt_secondDeriv_expMap_inv_sqNorm_radial`, the center Hessian
`∂²F/∂t²(0, p, v) = 2|v|²_p` is then strictly positive — do Carmo's strict
minimum at `q = p`. -/
theorem chartMetricInner_extChartAt_self_pos (g : RiemannianMetric I M) (p : M)
    {v : E} (hv : v ≠ 0) :
    0 < chartMetricInner (I := I) g p (extChartAt I p p) v v := by
  have h := chartMetricInner_extChartAt_eq_metricInner (I := I) g p
    (mem_chart_source H p) v v
  rw [h]
  simp only [trivializationAt_symm_self]
  exact g.metricInner_self_pos p v hv

end Exponential

end Riemannian

end
