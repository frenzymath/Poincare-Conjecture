import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import DoCarmoLib.Riemannian.Variation.EnergyFirstDeriv

/-!
# `E''(s)` by differentiating the first variation once more — chart-free

do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.8 (`prop:dc-ch9-2-8`), the analytic
core: differentiating the energy of a variation a **second** time in `s`.

`Variation/EnergyFirstDeriv.lean` proved the first variation
$$E'(s_0) = 2\int_a^b \Big\langle\frac{D}{\partial s}\frac{\partial f}{\partial t},
  \frac{\partial f}{\partial t}\Big\rangle\Big|_{s_0} dt$$
(`hasDerivAt_dcEnergy_of_dominated`).  Differentiating that expression once more in `s`,
and using metric compatibility along each transversal a second time, gives
$$\tfrac12 E''(s_0) = \int_a^b\Big\{\Big\langle\frac{D}{\partial s}\frac{D}{\partial s}\frac{\partial f}{\partial t},
  \frac{\partial f}{\partial t}\Big\rangle
  + \Big\langle\frac{D}{\partial s}\frac{\partial f}{\partial t},\frac{D}{\partial s}\frac{\partial f}{\partial t}\Big\rangle\Big\}\,dt .$$
This is do Carmo's step "taking the derivative of (2)" with the curvature substitution
(symmetry of the connection + the Ricci identity `lem:dc-ch4-4-1`) **not yet performed**:
what remains, at `s = 0` with `γ` a geodesic, is to rewrite the integrand into
`⟨V', V'⟩ - ⟨R(γ', V)γ', V⟩` — the index form (`rem:dc-ch9-2-10`) — which is the *geometric*
content of `prop:dc-ch9-2-8`, deferred to a later node.

## The two ingredients

* **The `E'` engine on a neighbourhood.** `hasDerivAt_dcEnergy_of_dominated` is applied not
  just at `s₀` but at every `σ` near `s₀`, giving `deriv E = 2∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩` on a
  neighbourhood of `s₀`; this is taken as the hypothesis `hE'` (the engine *provides* it).
* **A second differentiation under the integral sign.**  The `σ`-derivative of
  `∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩ dt` is `∫[⟨D/∂s D/∂s ∂f/∂t, ∂f/∂t⟩ + ⟨D/∂s ∂f/∂t, D/∂s ∂f/∂t⟩] dt`,
  by the same DCT lemma with pointwise input the manifold Leibniz rule
  `IsCovariantDerivFieldAlongOn.hasDerivAt_metricInner` (do Carmo Ch. 2, Prop. 3.2) applied
  to the pairs `(D/∂s ∂f/∂t, D/∂s D/∂s ∂f/∂t)` and `(∂f/∂t, D/∂s ∂f/∂t)` along each
  transversal.

Finally `deriv E =ᶠ 2∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩` and `HasDerivAt.congr_of_eventuallyEq` transfer
the derivative of the second expression back onto `deriv E`, i.e. onto `E''`.

## Fields, in the `D/∂s`-as-a-second-field discipline

`T = ∂f/∂t`; `DsT = D/∂s ∂f/∂t`, carried as the covariant pair `(T, DsT)` along each
transversal `σ ↦ f(σ, t)` (`hslice`); `DsDsT = D/∂s D/∂s ∂f/∂t`, the covariant `s`-derivative
of `DsT`, carried as the pair `(DsT, DsDsT)` along each transversal (`hslice2`).  This is the
same discipline as `Variation/CovariantField.lean` and `Variation/EnergyFirstDeriv.lean`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.8; metric compatibility is
Ch. 2, Prop. 3.2.
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

/-! ### The second differentiation under the integral sign

`d/ds ∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩ dt = ∫[⟨D/∂s D/∂s ∂f/∂t, ∂f/∂t⟩ + ⟨D/∂s ∂f/∂t, D/∂s ∂f/∂t⟩] dt`.
The pointwise input is the manifold Leibniz rule along each transversal, applied to the
pairs `(DsT, DsDsT)` and `(T, DsT)`; the exchange with `∫` is the same DCT lemma the first
variation used. -/

/-- **Math.** do Carmo Ch. 9, `prop:dc-ch9-2-8`, **the second differentiation under the
integral sign**, chart-free:
$$\frac{d}{ds}\int_a^b\Big\langle\frac{D}{\partial s}\frac{\partial f}{\partial t},
  \frac{\partial f}{\partial t}\Big\rangle dt\Big|_{s_0}
  = \int_a^b\Big\{\Big\langle\frac{D}{\partial s}\frac{D}{\partial s}\frac{\partial f}{\partial t},
    \frac{\partial f}{\partial t}\Big\rangle
    + \Big\langle\frac{D}{\partial s}\frac{\partial f}{\partial t},\frac{D}{\partial s}\frac{\partial f}{\partial t}\Big\rangle\Big\}\,dt .$$

`T`, `DsT`, `DsDsT` are `∂f/∂t`, `D/∂s ∂f/∂t`, `D/∂s D/∂s ∂f/∂t`, presented as the covariant
pairs `(T, DsT)` (`hslice`) and `(DsT, DsDsT)` (`hslice2`) along each transversal
`σ ↦ f(σ, t)`.  The pointwise derivative is `IsCovariantDerivFieldAlongOn.hasDerivAt_metricInner`;
the exchange is `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, whose
domination hypothesis is discharged by the caller via `bound`. -/
theorem hasDerivAt_dcPairing_of_dominated
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {T DsT DsDsT : ℝ × ℝ → E}
    {s₀ a b ε : ℝ} {bound : ℝ → ℝ}
    (hε : 0 < ε)
    (hslice : ∀ t ∈ uIoc a b, IsCovariantDerivFieldAlongOn (I := I) g
      (fun σ => f (σ, t)) (fun σ => T (σ, t)) (fun σ => DsT (σ, t)) (s₀ - ε) (s₀ + ε))
    (hslice2 : ∀ t ∈ uIoc a b, IsCovariantDerivFieldAlongOn (I := I) g
      (fun σ => f (σ, t)) (fun σ => DsT (σ, t)) (fun σ => DsDsT (σ, t)) (s₀ - ε) (s₀ + ε))
    (hsdiff : ∀ t ∈ uIoc a b, IsChartDifferentiableOn (I := I)
      (fun σ => f (σ, t)) (s₀ - ε) (s₀ + ε))
    (hscont : ∀ t ∈ uIoc a b, ∀ σ ∈ Icc (s₀ - ε) (s₀ + ε),
      ContinuousAt (fun σ' => f (σ', t)) σ)
    (hF_meas : ∀ᶠ σ in nhds s₀, AEStronglyMeasurable
      (fun t => g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t)))
      (volume.restrict (uIoc a b)))
    (hF_int : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hF'_meas : AEStronglyMeasurable
      (fun t => g.metricInner (f (s₀, t))
          (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        + g.metricInner (f (s₀, t))
          (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      (volume.restrict (uIoc a b)))
    (h_bound : ∀ t ∈ uIoc a b, ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      ‖g.metricInner (f (σ, t)) (DsDsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))
        + g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (DsT (σ, t))‖
        ≤ bound t)
    (hbound_int : IntervalIntegrable bound volume a b) :
    HasDerivAt
      (fun σ => ∫ t in a..b, g.metricInner (f (σ, t))
        (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t)))
      (∫ t in a..b, (g.metricInner (f (s₀, t))
          (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        + g.metricInner (f (s₀, t))
          (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))) s₀ := by
  have hmem : Ioo (s₀ - ε) (s₀ + ε) ∈ nhds s₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hderiv : ∀ᵐ t, t ∈ uIoc a b → ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      HasDerivAt (fun σ' => g.metricInner (f (σ', t))
          (DsT (σ', t) : TangentSpace I (f (σ', t))) (T (σ', t)))
        (g.metricInner (f (σ, t)) (DsDsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))
          + g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (DsT (σ, t))) σ := by
    filter_upwards with t ht σ hσ
    have hγc : ∀ σ' ∈ Icc (s₀ - ε) (s₀ + ε), ContinuousAt (fun σ'' => f (σ'', t)) σ' :=
      fun σ' hσ' => hscont t ht σ' hσ'
    exact (hslice2 t ht).hasDerivAt_metricInner (hslice t ht) (hsdiff t ht) hγc hσ
  have hbd : ∀ᵐ t, t ∈ uIoc a b → ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      ‖g.metricInner (f (σ, t)) (DsDsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))
        + g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (DsT (σ, t))‖
        ≤ bound t := by
    filter_upwards with t ht σ hσ using h_bound t ht σ hσ
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hmem hF_meas hF_int hF'_meas hbd hbound_int hderiv).2

/-! ### The second variation `E''(s₀)`

`E''(s₀) = 2∫[⟨D/∂s D/∂s ∂f/∂t, ∂f/∂t⟩ + ⟨D/∂s ∂f/∂t, D/∂s ∂f/∂t⟩] dt`, obtained by
differentiating `deriv E`.  The `E'` engine of `Variation/EnergyFirstDeriv.lean`
supplies `deriv E = 2∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩` on a whole neighbourhood of `s₀` — taken here
as `hE'` — and `hasDerivAt_dcPairing_of_dominated` differentiates the right-hand side. -/

/-- **Math.** do Carmo Ch. 9, `prop:dc-ch9-2-8`, **the second variation of the energy**,
chart-free, before the curvature substitution:
$$\tfrac12 E''(s_0)
  = \int_a^b\Big\{\Big\langle\frac{D}{\partial s}\frac{D}{\partial s}\frac{\partial f}{\partial t},
    \frac{\partial f}{\partial t}\Big\rangle
    + \Big\langle\frac{D}{\partial s}\frac{\partial f}{\partial t},\frac{D}{\partial s}\frac{\partial f}{\partial t}\Big\rangle\Big\}\,dt .$$

`hE'` is do Carmo's first variation `E'(σ) = 2∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩` (formula (2) with the
symmetry substitution), supplied on a neighbourhood of `s₀` by
`hasDerivAt_dcEnergy_of_dominated` — the `E'` engine provides exactly this at every base
parameter.  On that neighbourhood `deriv E` *is* `2∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩`, so differentiating
that expression (`hasDerivAt_dcPairing_of_dominated`) and transferring along the eventual
equality (`HasDerivAt.congr_of_eventuallyEq`) yields `E''`.

This is do Carmo's step "taking the derivative of (2)" with the *curvature* substitution —
symmetry of the connection plus the Ricci identity `lem:dc-ch4-4-1`, which turns the
integrand into the index form `⟨V', V'⟩ - ⟨R(γ', V)γ', V⟩` at `s = 0` for a geodesic — still
to be applied. -/
theorem hasDerivAt_deriv_dcEnergy_second_variation
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {T DsT DsDsT : ℝ × ℝ → E}
    {s₀ a b ε : ℝ} {bound : ℝ → ℝ}
    (hε : 0 < ε)
    (hE' : ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      HasDerivAt (fun σ' => DCEnergy (I := I) g (fun t => f (σ', t)) a b)
        (2 * ∫ t in a..b, g.metricInner (f (σ, t))
          (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))) σ)
    (hslice : ∀ t ∈ uIoc a b, IsCovariantDerivFieldAlongOn (I := I) g
      (fun σ => f (σ, t)) (fun σ => T (σ, t)) (fun σ => DsT (σ, t)) (s₀ - ε) (s₀ + ε))
    (hslice2 : ∀ t ∈ uIoc a b, IsCovariantDerivFieldAlongOn (I := I) g
      (fun σ => f (σ, t)) (fun σ => DsT (σ, t)) (fun σ => DsDsT (σ, t)) (s₀ - ε) (s₀ + ε))
    (hsdiff : ∀ t ∈ uIoc a b, IsChartDifferentiableOn (I := I)
      (fun σ => f (σ, t)) (s₀ - ε) (s₀ + ε))
    (hscont : ∀ t ∈ uIoc a b, ∀ σ ∈ Icc (s₀ - ε) (s₀ + ε),
      ContinuousAt (fun σ' => f (σ', t)) σ)
    (hF_meas : ∀ᶠ σ in nhds s₀, AEStronglyMeasurable
      (fun t => g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t)))
      (volume.restrict (uIoc a b)))
    (hF_int : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hF'_meas : AEStronglyMeasurable
      (fun t => g.metricInner (f (s₀, t))
          (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        + g.metricInner (f (s₀, t))
          (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      (volume.restrict (uIoc a b)))
    (h_bound : ∀ t ∈ uIoc a b, ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      ‖g.metricInner (f (σ, t)) (DsDsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))
        + g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (DsT (σ, t))‖
        ≤ bound t)
    (hbound_int : IntervalIntegrable bound volume a b) :
    HasDerivAt (deriv (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b))
      (2 * ∫ t in a..b, (g.metricInner (f (s₀, t))
          (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        + g.metricInner (f (s₀, t))
          (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))) s₀ := by
  -- `deriv E` agrees on `Ioo (s₀-ε) (s₀+ε)` with the first variation `2∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩`
  have hEq : deriv (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b)
      =ᶠ[𝓝 s₀] fun σ => 2 * ∫ t in a..b, g.metricInner (f (σ, t))
        (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t)) := by
    refine Filter.eventuallyEq_of_mem (s := Ioo (s₀ - ε) (s₀ + ε))
      (Ioo_mem_nhds (by linarith) (by linarith)) ?_
    intro σ hσ
    exact (hE' σ hσ).deriv
  -- differentiate that expression once more, and transfer along the eventual equality
  have hΦ := (hasDerivAt_dcPairing_of_dominated (I := I) (g := g) (f := f) (T := T) (DsT := DsT)
    (DsDsT := DsDsT) (bound := bound) hε hslice hslice2 hsdiff hscont hF_meas hF_int hF'_meas
    h_bound hbound_int).const_mul 2
  exact hΦ.congr_of_eventuallyEq hEq

end Riemannian.Variation
