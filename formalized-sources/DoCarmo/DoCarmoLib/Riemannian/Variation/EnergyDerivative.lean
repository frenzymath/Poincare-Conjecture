import DoCarmoLib.Riemannian.Variation.SurfaceSymmetry
import DoCarmoLib.Riemannian.Variation.FirstVariation

/-!
# The `s`-derivative of the energy density: the surface half of the first variation

do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.4 (`prop:dc-ch9-2-4`).

do Carmo's proof of the first variation formula opens by differentiating
`E(s) = ∫ ⟨∂f/∂t, ∂f/∂t⟩ dt` **under the integral sign** and, at the decisive step,
"using the symmetry of the Riemannian connection":
$$
\frac{\partial}{\partial s}\Big\langle\frac{\partial f}{\partial t},\frac{\partial f}{\partial t}\Big\rangle
  = 2\Big\langle\frac{D}{\partial s}\frac{\partial f}{\partial t},\frac{\partial f}{\partial t}\Big\rangle
  = 2\Big\langle\frac{D}{\partial t}\frac{\partial f}{\partial s},\frac{\partial f}{\partial t}\Big\rangle .
$$

That chain is **pointwise**: it says nothing about integrals, and it is the entire
geometric content of do Carmo's step.  This file proves it.  Together with
`Variation/FirstVariation.lean` — which supplies the *intrinsic* half, the integration
by parts turning `∫ ⟨D/∂t ∂f/∂s, ∂f/∂t⟩ dt` into do Carmo's right-hand side — the two
halves of `prop:dc-ch9-2-4` are in place.

They do **not** yet compose, and the gap is wider than one lemma: the two halves are not
even stated in the same language.  This half concludes in *chart* objects
(`chartMetricInner`, `f : ℝ × ℝ → E`, a chart selector `α : M`); the intrinsic half
concludes in *manifold* objects (`g.metricInner (γ t) …`, `TangentSpace I (γ t)`).  See
`## Residual` below for the enumeration — deliberately an enumeration, because naming a
single "the" residual has repeatedly proved to be an understatement in this chapter.

## The two ingredients, and why the pointwise chain is *only* two lines

Both were already in DoCarmoLib and had never been composed:

* `hasDerivAt_chartMetricInner_along` (`Geodesic/CovariantDerivative.lean`) — metric
  compatibility in a chart, `d/dσ⟨V, W⟩ = ⟨D_uV, W⟩ + ⟨V, D_uW⟩`.  At `V = W = ∂f/∂t`
  its two terms coincide (the chart pairing is symmetric,
  `chartMetricInner_symm`), giving the factor `2`.
* `surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst`
  (`Variation/SurfaceSymmetry.lean`) — the symmetry lemma in operator form,
  `D/∂s ∂f/∂t = D/∂t ∂f/∂s`, which rewrites the first factor.

No curvature appears, and no Ricci identity is used: this is do Carmo Ch. 3 Lemma 3.4,
not Ch. 4 `lem:dc-ch4-4-1`.  The second variation `prop:dc-ch9-2-8` is where curvature
enters, by differentiating this identity a second time.

## Scope

**Chart level**, inherited from both ingredients and not reducible below them: `f : ℝ × ℝ → E`
is the reading of the surface in the fixed chart at `α : M`, and `∂f/∂s`, `∂f/∂t`,
`D/∂s`, `D/∂t` are all that chart's.  `α` is a chart selector, not a point of the
surface.  This is *not* a chart-independent statement about a surface in `M`: no
chart-free two-parameter surface exists in the formalization yet.  That is *one* of the
things keeping `prop:dc-ch9-2-4` from being tagged as a whole, not the only one — see
`## Residual` for the enumeration.

Following its ingredients, the regularity hypotheses are `HasFDerivAt`-style with `Df`,
`D2f` supplied explicitly rather than a `ContDiff ℝ 2 f`: `Df` is a *function* and
`D2f` a single continuous linear map at the base point.

## Residual

`prop:dc-ch9-2-4` is **not** closed by this file plus `FirstVariation.lean`, and is
deliberately left untagged.  At least three things are missing, and none is geometric:

1. **Differentiation under the integral sign** — the analytic exchange
   $$E'(s_0) = \int_0^a \frac{\partial}{\partial s}\Big\langle\frac{\partial f}{\partial t},\frac{\partial f}{\partial t}\Big\rangle\Big|_{s_0} dt,$$
   via `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
2. **Chart-to-manifold glue** — identifying the chart pairing used here with `DCEnergy`'s
   integrand, and the chart operators `D/∂s`, `D/∂t` with the chart-free `D/dt` of
   `IsCovariantDerivFieldAlongOn` that the intrinsic half is stated in.  Without this the
   two halves cannot meet at all, whatever is done about (1).
3. **A chart-free two-parameter surface** — this file, and every surface operator it
   rests on, is chart-fixed; do Carmo's `c : [0,a] → M` need not lie in one chart.

The list is offered as a lower bound, not as *the* residual: the accounting is what has
repeatedly turned out to be optimistic in this chapter, while the Lean itself held up.

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.4; the symmetry lemma is
Ch. 3, Lemma 3.4 and metric compatibility is Ch. 2, Prop. 3.2.
-/

open Set Riemannian Filter
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

/-! ### `∂/∂s ⟨∂f/∂t, ∂f/∂t⟩ = 2⟨D/∂s ∂f/∂t, ∂f/∂t⟩` -/

/-- **Math.** Metric compatibility applied to the energy density.  Along the `s`-slice
through `(s₀, t₀)`, the derivative of `⟨∂f/∂t, ∂f/∂t⟩` is twice the pairing of `∂f/∂t`
with its own covariant `s`-derivative:
$$\frac{\partial}{\partial s}\Big\langle\frac{\partial f}{\partial t},\frac{\partial f}{\partial t}\Big\rangle
  = 2\Big\langle\frac{D}{\partial s}\frac{\partial f}{\partial t},\frac{\partial f}{\partial t}\Big\rangle .$$

This is `hasDerivAt_chartMetricInner_along` at `V = W = ∂f/∂t`; the factor `2` is the
symmetry of the chart pairing (`chartMetricInner_symm`), which collapses the Leibniz
rule's two terms into one. -/
theorem hasDerivAt_chartEnergyDensity_slice
    (g : RiemannianMetric I M) (α : M) (f : ℝ × ℝ → E)
    (Df : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E)) (D2f : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E)
    (s₀ t₀ : ℝ)
    (hf : ∀ᶠ p in nhds (s₀, t₀), HasFDerivAt f (Df p) p)
    (hf2 : HasFDerivAt Df D2f (s₀, t₀))
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (f (s₀, t₀)))
    (hbase : (extChartAt I α).symm (f (s₀, t₀))
      ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    HasDerivAt
      (fun σ => chartMetricInner (I := I) g α (f (σ, t₀)) (Df (σ, t₀) (0, 1))
        (Df (σ, t₀) (0, 1)))
      (2 * chartMetricInner (I := I) g α (f (s₀, t₀))
        (surfaceCovariantDerivS (I := I) g α f (fun p => Df p (0, 1)) (s₀, t₀))
        (Df (s₀, t₀) (0, 1))) s₀ := by
  have hfs : HasFDerivAt f (Df (s₀, t₀)) (s₀, t₀) := hf.self_of_nhds
  -- the chart curve of the slice `σ ↦ f (σ, t₀)` is differentiable at `s₀`
  have hu : DifferentiableAt ℝ (fun σ => f (σ, t₀)) s₀ :=
    (hasDerivAt_comp_fst hfs).differentiableAt
  -- and so is the field `σ ↦ ∂f/∂t (σ, t₀)`, by the mixed partial `D²f(1,0)(0,1)`
  have hDFs : HasDerivAt (fun σ => Df (σ, t₀)) (D2f (1, 0)) s₀ := hasDerivAt_comp_fst hf2
  have hV : DifferentiableAt ℝ (fun σ => Df (σ, t₀) (0, 1)) s₀ :=
    (HasFDerivAt.comp_hasDerivAt (x := s₀)
      (hl := (ContinuousLinearMap.apply ℝ E ((0, 1) : ℝ × ℝ)).hasFDerivAt)
      (hf := hDFs)).differentiableAt
  have h := hasDerivAt_chartMetricInner_along (I := I) g α (fun σ => f (σ, t₀))
    (fun σ => Df (σ, t₀) (0, 1)) (fun σ => Df (σ, t₀) (0, 1)) hu hV hV hG hbase
  -- the Leibniz rule's two terms are equal by symmetry of the chart pairing, giving `2 * _`
  have hsymm : chartMetricInner (I := I) g α (f (s₀, t₀)) (Df (s₀, t₀) (0, 1))
      (covariantDerivCoord (I := I) g α (fun σ => f (σ, t₀))
        (fun σ => Df (σ, t₀) (0, 1)) s₀)
      = chartMetricInner (I := I) g α (f (s₀, t₀))
        (covariantDerivCoord (I := I) g α (fun σ => f (σ, t₀))
          (fun σ => Df (σ, t₀) (0, 1)) s₀) (Df (s₀, t₀) (0, 1)) :=
    chartMetricInner_symm (I := I) g α _ _ _
  rw [hsymm] at h
  -- `covariantDerivCoord` along the `s`-slice *is* `surfaceCovariantDerivS`, by definition
  have hop : covariantDerivCoord (I := I) g α (fun σ => f (σ, t₀))
      (fun σ => Df (σ, t₀) (0, 1)) s₀
      = surfaceCovariantDerivS (I := I) g α f (fun p => Df p (0, 1)) (s₀, t₀) := rfl
  rw [hop] at h
  convert h using 1
  ring

/-! ### The full pointwise chain, with the symmetry lemma applied -/

/-- **Math.** do Carmo Ch. 9, `prop:dc-ch9-2-4`, **the surface half**, pointwise:
$$\frac{\partial}{\partial s}\Big\langle\frac{\partial f}{\partial t},\frac{\partial f}{\partial t}\Big\rangle
  = 2\Big\langle\frac{D}{\partial t}\frac{\partial f}{\partial s},\frac{\partial f}{\partial t}\Big\rangle .$$

This is do Carmo's step "differentiating under the integral sign and using the symmetry
of the Riemannian connection", with the differentiation under the integral sign removed:
what remains is exactly the pointwise identity the integrand satisfies.

The right-hand side is the one that integrates by parts: at `s = 0` the field `∂f/∂s`
restricts to the variational field `V` of `def:dc-ch9-2-1`, `D/∂t ∂f/∂s` to its covariant
derivative `DV`, and `∂f/∂t` to the velocity `dc/dt`, so the integral of the right-hand
side is `2∫ ⟨DV, dc/dt⟩ dt` — that is, **twice** the left-hand side of
`IsCovariantDerivFieldAlongOn.integral_metricInner_covariantDeriv_left`, which converts
`∫ ⟨DV, dc/dt⟩ dt` into do Carmo's formula (1).  The factor `2` is the one do Carmo
divides out when he states formula (1) for `½E'(0)` rather than `E'(0)`.

Obtained from `hasDerivAt_chartEnergyDensity_slice` by rewriting with
`surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst` — the symmetry of the
connection, and the only geometric input. -/
theorem hasDerivAt_chartEnergyDensity_slice_symm
    (g : RiemannianMetric I M) (α : M) (f : ℝ × ℝ → E)
    (Df : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E)) (D2f : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E)
    (s₀ t₀ : ℝ)
    (hf : ∀ᶠ p in nhds (s₀, t₀), HasFDerivAt f (Df p) p)
    (hf2 : HasFDerivAt Df D2f (s₀, t₀))
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (f (s₀, t₀)))
    (hbase : (extChartAt I α).symm (f (s₀, t₀))
      ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    HasDerivAt
      (fun σ => chartMetricInner (I := I) g α (f (σ, t₀)) (Df (σ, t₀) (0, 1))
        (Df (σ, t₀) (0, 1)))
      (2 * chartMetricInner (I := I) g α (f (s₀, t₀))
        (surfaceCovariantDerivT (I := I) g α f (fun p => Df p (1, 0)) (s₀, t₀))
        (Df (s₀, t₀) (0, 1))) s₀ := by
  have h := hasDerivAt_chartEnergyDensity_slice (I := I) g α f Df D2f s₀ t₀ hf hf2 hG hbase
  rwa [surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst (I := I) g α f Df D2f s₀ t₀
    hf hf2] at h

end Riemannian.Variation
