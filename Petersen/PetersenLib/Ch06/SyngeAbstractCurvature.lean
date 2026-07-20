import PetersenLib.Ch06.SecondVariationSynge
import PetersenLib.Ch06.CurvatureChartBridgeMoving
import PetersenLib.Ch05.ChartTransition

/-!
# Petersen Ch. 6, §6.1 — Synge's second variation with Petersen's **abstract** curvature

`Ch06/SecondVariationSynge.lean` proves Thm. 6.1.4 with the curvature left as the vendored
coordinate contraction `Jacobi.chartCurvatureContraction2`, and records — in the docstring of
`hasDerivAt_chartPairing_transversalAccel_of_geodesic_curvatureTensorAt` and in the file
header — that the bridge to Ch. 3's Koszul `curvatureTensorAt` is **diagonal**, so the
abstract form is only available at the single point where the chart is centred at the foot.
An integral over `t` needs one chart for the whole curve, so the abstract form could not go
under the integral.

`Ch06/CurvatureChartBridgeMoving.lean` removed that obstruction: its
`chartCurvatureContraction2_eq_neg_curvatureTensorAt_of_mem` is the **off-diagonal** bridge,
valid at every `x ∈ (chartAt H α).source`, at the price of the transport
`Φ := tangentCoordChange I α x x`.  `Ch05/ChartTransition.lean`'s `chartMetricInner_eq_inner`
is the matching off-diagonal statement for the metric pairing.  Composing the two, the whole
curvature term of Thm. 6.1.4 converts at a **moving** foot:
$$\big\langle R^{\text{chart}}(X,Y)Z,\;W\big\rangle_\alpha^{\varphi_\alpha x}
  = -\,g_x\big(R(\Phi X,\Phi Y)\Phi Z,\;\Phi W\big).$$

This file carries that conversion through the pointwise integrand identity and then under the
integral, landing Petersen's Thm. 6.1.4 in the form
`thm:pet-ch6-synge-second-variation` actually states.

## What supersedes what

* `hasDerivAt_chartPairing_transversalAccel_of_geodesic_curvatureTensorAt_of_mem` supersedes
  `…_curvatureTensorAt` (`SecondVariationSynge.lean:487`): the hypothesis
  `hbase : c (s₀,t₀) = extChartAt I α α` is replaced by "`x` is *any* point of the chart at
  `α` whose chart image is the foot".  Taking `x = α` recovers the old statement.
* `secondVariationEnergy_chart_curvatureTensorAt` supersedes `secondVariationEnergy_chart`
  (`SecondVariationSynge.lean:635`): same equation, curvature term rewritten at the moving
  foot `(extChartAt I α).symm (c (0,t))`.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ### The curvature pairing at a moving foot -/

/-- **Math.** **The curvature term of Thm. 6.1.4 converts off the diagonal.**  For `x`
anywhere in the chart at `α`, the chart pairing of the vendored coordinate curvature
contraction against a fourth `α`-reading is the *negative* of the manifold metric pairing of
Ch. 3's Koszul `curvatureTensorAt` against the transported readings:
$$\big\langle R^{\text{chart}}_\alpha(X,Y)Z,\;W\big\rangle_\alpha^{\varphi_\alpha x}
  = -\,g_x\big(R(\Phi X,\Phi Y)\Phi Z,\;\Phi W\big),\qquad
  \Phi = \texttt{tangentCoordChange I α x x}.$$

`chartMetricInner_eq_inner` moves the pairing to `g_x` (it is already off-diagonal), and
`chartCurvatureContraction2_eq_neg_curvatureTensorAt_of_mem` moves the curvature; the sign is
do Carmo's convention against Petersen's.  This is the single lemma that the docstrings of
`hasDerivAt_chartPairing_transversalAccel_of_geodesic_curvatureTensorAt` and
`Ch06/CurvatureChartBridge.lean` declare unavailable away from the chart centre. -/
theorem chartMetricInner_chartCurvatureContraction2_eq_neg_inner_curvatureTensorAt
    (g : RiemannianMetric I M) {α x : M} (hx : x ∈ (chartAt H α).source) (X Y Z W : E) :
    chartMetricInner (I := I) g α (extChartAt I α x)
        (Jacobi.chartCurvatureContraction2 (I := I) g α X Y Z (extChartAt I α x)) W
      = -g.inner x
          (curvatureTensorAt (g.leviCivita).toAffineConnection x
            (tangentCoordChange I α x x X) (tangentCoordChange I α x x Y)
            (tangentCoordChange I α x x Z))
          (tangentCoordChange I α x x W) := by
  have hxE : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  rw [chartMetricInner_eq_inner (I := I) g hxE,
    chartCurvatureContraction2_eq_neg_curvatureTensorAt_of_mem (I := I) g hx]
  simp

/-! ### The integrand identity, off the diagonal -/

/-- **Math.** Petersen Thm. 6.1.4, **the integrand identity in Petersen's own curvature
tensor, at a moving foot**.  Along a geodesic `t ↦ c(s₀,t)` read in a *fixed* chart `α`, with
`x` the manifold point whose chart image is the foot `c(s₀,t₀)`,
$$\frac{\partial}{\partial t}\Big\langle \frac{D}{\partial s}\frac{\partial c}{\partial s},
    \frac{\partial c}{\partial t}\Big\rangle_\alpha
  = \Big\langle \frac{D}{\partial s}\frac{D}{\partial s}\frac{\partial c}{\partial t},
      \frac{\partial c}{\partial t}\Big\rangle_\alpha
    - g_x\Big(R\big(\Phi\partial_s c, \Phi\partial_t c\big)\Phi\partial_s c,
        \Phi\partial_t c\Big),\qquad \Phi = \texttt{tangentCoordChange I α x x},$$
with `R` Ch. 3's Koszul `curvatureTensorAt` — exactly the identity Petersen's proof of
Thm. 6.1.4 displays.

This is the **off-diagonal** strengthening of
`hasDerivAt_chartPairing_transversalAccel_of_geodesic_curvatureTensorAt`, whose hypothesis
`hbase : c (s₀,t₀) = extChartAt I α α` pinned the chart centre to the foot.  Here `α` is free
and `x` ranges over the whole chart source, so the identity is available at *every* `t` along
a curve read in one fixed chart — which is what putting `R` under the integral of Thm. 6.1.4
requires.  Taking `x = α` and `hbase.symm` recovers the old statement (`Φ` collapses to the
identity by `tangentCoordChange_self`).

**Proof.** `hasDerivAt_chartPairing_transversalAccel_of_geodesic` — already off-diagonal —
supplies the chart-level identity; the curvature summand is converted by
`chartMetricInner_chartCurvatureContraction2_eq_neg_inner_curvatureTensorAt`. -/
theorem hasDerivAt_chartPairing_transversalAccel_of_geodesic_curvatureTensorAt_of_mem
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t₀ : ℝ} {x : M} (hc : ContDiffAt ℝ 3 c (s₀, t₀))
    (hx : x ∈ (chartAt H α).source) (hbase : extChartAt I α x = c (s₀, t₀))
    (hgeo : mixedPartialCoord (I := I) g α c (s₀, t₀)
      ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) = 0) :
    HasDerivAt (fun t : ℝ => chartMetricInner (I := I) g α (c (s₀, t))
        (mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
        (fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ)))
      (chartMetricInner (I := I) g α (c (s₀, t₀))
          (covariantDerivCoord (I := I) g α (fun s => c (s, t₀))
            (fun s => mixedPartialCoord (I := I) g α c (s, t₀)
              ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) s₀)
          (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))
        - g.inner x
            (curvatureTensorAt (g.leviCivita).toAffineConnection x
              (tangentCoordChange I α x x (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ)))
              (tangentCoordChange I α x x (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ)))
              (tangentCoordChange I α x x (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ))))
            (tangentCoordChange I α x x (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ)))) t₀ := by
  have hxE : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hmem : c (s₀, t₀) ∈ interior (extChartAt I α).target := by
    rw [← hbase]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxE)
  have h := hasDerivAt_chartPairing_transversalAccel_of_geodesic (I := I) g α hc hmem hgeo
  refine h.congr_deriv ?_
  have hkey : chartMetricInner (I := I) g α (c (s₀, t₀))
      (Jacobi.chartCurvatureContraction2 (I := I) g α
        (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ)) (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ)) (c (s₀, t₀)))
      (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))
      = -g.inner x
          (curvatureTensorAt (g.leviCivita).toAffineConnection x
            (tangentCoordChange I α x x (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ)))
            (tangentCoordChange I α x x (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ)))
            (tangentCoordChange I α x x (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ))))
          (tangentCoordChange I α x x (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))) := by
    rw [← hbase]
    exact chartMetricInner_chartCurvatureContraction2_eq_neg_inner_curvatureTensorAt
      (I := I) g hx _ _ _ _
  rw [hkey]
  ring

/-! ### Theorem 6.1.4 with `R` under the integral -/

/-- **Math.** **Petersen Theorem 6.1.4** (`thm:pet-ch6-synge-second-variation`, pp. 255–256),
**Synge's second variation of energy**, with Petersen's **abstract curvature tensor under the
integral**.  For a variation `c(s,t)` read in a fixed chart `α`, whose central curve
`t ↦ c(0,t)` is a geodesic, writing `x_t := \varphi_\alpha^{-1}(c(0,t))` for the foot at time
`t` and `Φ_t := tangentCoordChange I α x_t x_t` for the transport of `α`-readings into
`T_{x_t}M`,
$$\frac{d^2E}{ds^2}\Big|_{0}
  = \Big[\Big\langle \frac{D}{\partial s}\frac{\partial c}{\partial s},
      \frac{\partial c}{\partial t}\Big\rangle_\alpha\Big]_{t_1}^{t_2}
    + \int_{t_1}^{t_2}\Big(\Big|\frac{D}{\partial s}\frac{\partial c}{\partial t}\Big|_\alpha^2
      + g_{x_t}\big(R(\Phi_t\partial_s c, \Phi_t\partial_t c)\Phi_t\partial_s c,
        \Phi_t\partial_t c\big)\Big)\,dt ,$$
with `R` Ch. 3's Koszul `curvatureTensorAt`.

**This is Petersen's `−g(R(V,\dot c)\dot c, V)`**: the slot order here is
`g(R(V,\dot c)V,\dot c)`, which is its negative by the antisymmetry of `R` in the last pair.
The two sign flips — do Carmo's convention (`chartCurvatureContraction2 = −curvatureTensorAt`)
against the `−` already carried by `secondVariationEnergy_chart`'s integrand — cancel, leaving
the `+` displayed above.

**Why this was previously out of reach.**  `secondVariationEnergy_chart`'s docstring records
that "`chartCurvatureContraction2` stays in the chart deliberately, since the bridge to Ch. 3's
`curvatureTensorAt` is diagonal while the foot `c(0,t)` moves along the curve".  With
`Ch06/CurvatureChartBridgeMoving.lean` the bridge fires at *every* point of the chart, so the
two integrands agree at every `t ∈ [t_1,t_2]` and `intervalIntegral.integral_congr` transports
the identity under the integral.  The chart `α` is still a single fixed chart for the whole
curve — nothing about the analysis changes; only the curvature term is re-read.

**Proof.** `secondVariationEnergy_chart` supplies the equation; at each `t ∈ [t_1,t_2]` the
foot lies in `(extChartAt I α).target`, so its preimage `x_t` lies in `(chartAt H α).source`
and `chartMetricInner_chartCurvatureContraction2_eq_neg_inner_curvatureTensorAt` rewrites the
integrand pointwise. -/
theorem secondVariationEnergy_chart_curvatureTensorAt (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {δ a b t₁ t₂ : ℝ} (hδ : 0 < δ) (h12 : t₁ < t₂)
    (hsub : Icc t₁ t₂ ⊆ Ioo a b)
    (hc : ContDiffOn ℝ ∞ c (Ioo (-δ) δ ×ˢ Ioo a b))
    (hmem : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b, c p ∈ (extChartAt I α).target)
    (hgeo : ∀ t ∈ Icc t₁ t₂,
      mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) = 0) :
    deriv (deriv (fun s : ℝ => ∫ t in t₁..t₂, (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t))) 0
      = chartMetricInner (I := I) g α (c (0, t₂))
          (mixedPartialCoord (I := I) g α c (0, t₂) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
          (fderiv ℝ c (0, t₂) ((0, 1) : ℝ × ℝ))
        - chartMetricInner (I := I) g α (c (0, t₁))
            (mixedPartialCoord (I := I) g α c (0, t₁) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
            (fderiv ℝ c (0, t₁) ((0, 1) : ℝ × ℝ))
        + ∫ t in t₁..t₂, (chartMetricInner (I := I) g α (c (0, t))
              (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
              (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
            + g.inner ((extChartAt I α).symm (c (0, t)))
                (curvatureTensorAt (g.leviCivita).toAffineConnection
                  ((extChartAt I α).symm (c (0, t)))
                  (tangentCoordChange I α ((extChartAt I α).symm (c (0, t)))
                    ((extChartAt I α).symm (c (0, t))) (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)))
                  (tangentCoordChange I α ((extChartAt I α).symm (c (0, t)))
                    ((extChartAt I α).symm (c (0, t))) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)))
                  (tangentCoordChange I α ((extChartAt I α).symm (c (0, t)))
                    ((extChartAt I α).symm (c (0, t))) (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ))))
                (tangentCoordChange I α ((extChartAt I α).symm (c (0, t)))
                  ((extChartAt I α).symm (c (0, t))) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)))) := by
  classical
  rw [secondVariationEnergy_chart (I := I) g α hδ h12 hsub hc hmem hgeo]
  congr 1
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le h12.le] at ht
  have hline : ((0 : ℝ), t) ∈ Ioo (-δ) δ ×ˢ Ioo a b := ⟨⟨neg_lt_zero.mpr hδ, hδ⟩, hsub ht⟩
  have hmT : c (0, t) ∈ (extChartAt I α).target := hmem _ hline
  have hxs : (extChartAt I α).symm (c (0, t)) ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hmT
  have hxc : (extChartAt I α).symm (c (0, t)) ∈ (chartAt H α).source := by
    rwa [extChartAt_source] at hxs
  have hbase : extChartAt I α ((extChartAt I α).symm (c (0, t))) = c (0, t) :=
    (extChartAt I α).right_inv hmT
  have hkey : chartMetricInner (I := I) g α (c (0, t))
      (Jacobi.chartCurvatureContraction2 (I := I) g α
        (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (c (0, t)))
      (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
      = -g.inner ((extChartAt I α).symm (c (0, t)))
          (curvatureTensorAt (g.leviCivita).toAffineConnection
            ((extChartAt I α).symm (c (0, t)))
            (tangentCoordChange I α ((extChartAt I α).symm (c (0, t)))
              ((extChartAt I α).symm (c (0, t))) (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)))
            (tangentCoordChange I α ((extChartAt I α).symm (c (0, t)))
              ((extChartAt I α).symm (c (0, t))) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)))
            (tangentCoordChange I α ((extChartAt I α).symm (c (0, t)))
              ((extChartAt I α).symm (c (0, t))) (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ))))
          (tangentCoordChange I α ((extChartAt I α).symm (c (0, t)))
            ((extChartAt I α).symm (c (0, t))) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))) := by
    conv_lhs => rw [← hbase]
    exact chartMetricInner_chartCurvatureContraction2_eq_neg_inner_curvatureTensorAt
      (I := I) g hxc _ _ _ _
  rw [hkey]
  ring

end PetersenLib

end
