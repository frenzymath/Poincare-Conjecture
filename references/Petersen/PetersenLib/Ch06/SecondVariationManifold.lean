import PetersenLib.Ch06.SyngeAbstractCurvature
import PetersenLib.Ch06.JacobiChartBridge
import PetersenLib.Ch06.VariationTransfers
import PetersenLib.Ch06.WindowEnergyChartFree
import PetersenLib.Ch05.EnergyMinimizers

/-!
# Petersen Ch. 6, §6.1 — Synge's second variation with a chart-free conclusion

`Ch06/SyngeAbstractCurvature.lean` proves Petersen's Thm. 6.1.4
(`thm:pet-ch6-synge-second-variation`, pp. 255–256) as
`secondVariationEnergy_chart_curvatureTensorAt`: a statement about a *chart reading*
`c : ℝ × ℝ → E` of a variation, whose **conclusion still mentions the chart** — the energy is
the `α`-read integral, the boundary terms are `chartMetricInner`s, and the curvature's
arguments are wrapped in `tangentCoordChange`.

This file removes the chart from the **conclusion**.  It keeps, as a *hypothesis*, that the
variation lies in one chart (`hsrc`), and lands

$$\frac{d}{ds}\Big[\frac{dE(c_s)}{ds}\Big]_{s=0}
  = g\Big(\frac{\partial^2\bar c}{\partial s^2},\frac{\partial\bar c}{\partial t}\Big)\Big|_{t_1}^{t_2}
  + \int_{t_1}^{t_2}\Big(\big|\dot V\big|^2
      - g\big(R(V,T)T,V\big)\Big)\,dt ,$$

stated entirely in Ch. 5/6's chart-free vocabulary: `energyFunctional`, `transversalAccel`,
`variationField`, `curveVelocity`, `derivAlongCurve`, `curvatureTensorAt`.

## Why this is the right intermediate, and what it is NOT

This is the **exact Ch. 6 sibling of Ch. 5's `hasDerivAt_windowEnergy`**
(`Ch05/FirstVariation.lean:750`), which likewise assumes the slab lies in one chart `α` and
likewise concludes without mentioning `α`.  (Do not confuse it with
`hasDerivAt_windowEnergy_chart` at `:380`, whose conclusion *is* chart-read.)  That asymmetry
is the house's deliberate design:
because the conclusion omits the chart, *adjacent windows with different chart centres glue*.
Ch. 5 then covers a compact slab by finitely many such windows (a Lebesgue-number argument)
and telescopes, in `hasDerivAt_pieceEnergy` (`Ch05/FirstVariation.lean:1102`).

**This file does not do that cover.**  Consequently it does **not** prove Petersen's
Thm. 6.1.4, whose variation ranges over a compact `[a,b]` and therefore leaves every single
chart.  `PetersenLib.secondVariationEnergy` — the name the blueprint's `\lean{...}` list wants
and the node's `\leanok` waits on — is still absent, deliberately.  The remaining gap is
exactly the Lebesgue chart cover; see the module docstring's "What remains" below.

## What is here

* `hasDerivAt_deriv_of_eventuallyEq` — the transfer that lets a `HasDerivAt (deriv ·)` claim
  move along an `EventuallyEq` of the *underlying* function.  `Filter.EventuallyEq.deriv_eq`
  alone is not enough: it equates derivatives at a *point*, whereas differentiating `deriv E`
  needs them equal on a *neighbourhood*.  `EventuallyEq.eventuallyEq_nhds` supplies that.
  This is why the recorded lesson "`deriv ∘ deriv` does not sum over pieces" does not bite
  here: we never form `deriv (deriv ·)`, we carry `HasDerivAt (deriv ·)` throughout.
* `hasDerivAt_deriv_windowEnergy_chart_curvatureTensorAt` — Thm. 6.1.4's chart form restated
  as a `HasDerivAt`, which is the shape a piecewise sum can consume.  It is *derived* from the
  two existing theorems rather than reproved: the `E''` engine
  (`hasDerivAt_deriv_windowEnergy_chart`) already has `HasDerivAt` shape, and
  `secondVariationEnergy_chart_curvatureTensorAt` pins the same `deriv (deriv ·) 0` to Synge's
  right-hand side; so the two right-hand sides are equal and may be substituted.

## What remains for `PetersenLib.secondVariationEnergy`

The Lebesgue chart cover, a bounded copy of `Ch05/FirstVariation.lean:1102-1233`: chart windows
at every time, `lebesgue_number_lemma_of_metric isCompact_Icc`, a uniform partition, then
telescoping the (chart-free!) boundary terms.  Every lever is already in tree.  Note also that
`hasDerivAt_pieceEnergy_shift` (`Ch06/SecondVariation.lean:180`) already supplies, at manifold
level with no chart hypothesis, the `HasDerivAt Eⱼ` at every nearby `s₀` that such a cover needs.
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

/-! ### Differentiating `deriv` along an eventual equality -/

/-- **Math.** If `E₁` and `W` agree near `x`, then a `HasDerivAt (deriv W) v x` claim transfers
to `E₁`.  The point is that `deriv E₁` and `deriv W` must agree on a *neighbourhood* of `x` —
not merely at `x` — for the outer derivative to see them as the same function;
`Filter.EventuallyEq.eventuallyEq_nhds` upgrades the hypothesis to exactly that. -/
theorem hasDerivAt_deriv_of_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E₁ W : ℝ → F} {v : F} {x : ℝ} (h : E₁ =ᶠ[𝓝 x] W)
    (hW : HasDerivAt (deriv W) v x) : HasDerivAt (deriv E₁) v x := by
  refine hW.congr_of_eventuallyEq ?_
  filter_upwards [h.eventuallyEq_nhds] with s hs using hs.deriv_eq

/-! ### Thm. 6.1.4 in the chart, in `HasDerivAt` shape -/

/-- **Math.** Petersen Thm. 6.1.4 in one fixed chart, restated as a `HasDerivAt` for `deriv E`
rather than as a value of `deriv (deriv E)`.

This is the shape that composes.  A value statement `deriv (deriv E) 0 = v` cannot be summed
over the pieces of a partition — `deriv` of a sum is the sum of `deriv`s only where each
summand is differentiable on a *neighbourhood*, which a bare value at `0` does not record.
The `HasDerivAt` form carries that information.

**Proof.**  No new mathematics: the `E''` engine `hasDerivAt_deriv_windowEnergy_chart` already
concludes `HasDerivAt (deriv E) engineRHS 0`, and `secondVariationEnergy_chart_curvatureTensorAt`
concludes `deriv (deriv E) 0 = syngeRHS`.  Since the engine's `.deriv` computes the same
`deriv (deriv E) 0` as `engineRHS`, the two right-hand sides are equal, and substituting gives
the claim. -/
theorem hasDerivAt_deriv_windowEnergy_chart_curvatureTensorAt (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {δ a b t₁ t₂ : ℝ} (hδ : 0 < δ) (h12 : t₁ < t₂)
    (hsub : Icc t₁ t₂ ⊆ Ioo a b)
    (hc : ContDiffOn ℝ ∞ c (Ioo (-δ) δ ×ˢ Ioo a b))
    (hmem : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b, c p ∈ (extChartAt I α).target)
    (hgeo : ∀ t ∈ Icc t₁ t₂,
      mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) = 0) :
    HasDerivAt (deriv (fun s : ℝ => ∫ t in t₁..t₂, (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)))
      (chartMetricInner (I := I) g α (c (0, t₂))
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
                  ((extChartAt I α).symm (c (0, t))) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))))) 0 := by
  classical
  have hE := hasDerivAt_deriv_windowEnergy_chart (I := I) g α hδ h12
    (hc.mono (Set.prod_mono subset_rfl hsub))
    (fun p hp => hmem p ⟨hp.1, hsub hp.2⟩)
  have heq := secondVariationEnergy_chart_curvatureTensorAt (I := I) g α hδ h12 hsub hc hmem hgeo
  rw [hE.deriv] at heq
  exact heq ▸ hE

/-! ### The variation field's chart reading, and its covariant derivative -/

/-- **Math.** Petersen §6.1: **the chart-`α` reading of the variation field `V = ∂c̄/∂s` is the
`s`-partial of the chart reading of `c̄`.**

`variationField` is defined at the *moving foot*: `V(τ) = d/ds|₀ φ_{c̄(0,τ)}(c̄(s,τ))`, read in
the chart at `c̄(0,τ)`, which is where `T_{c̄(0,τ)}M` is coordinatised.  `chartFieldRep` pushes
that reading into one *fixed* chart `α`.  The claim is that the result is simply
`d/ds|₀ φ_α(c̄(s,τ))` — the naive `s`-derivative of the `α`-reading.

**Proof.** This is `tangentCoordChange_deriv_chartReading` applied to the ***`s`-slice curve***
`s ↦ c̄(s,τ)` at `s = 0`, with `β := c̄(0,τ)` its own foot.  No round trip through the foot chart
has to be collapsed by hand: the general lemma already changes the chart of a chart-reading's
derivative, and the `s`-slice is a curve like any other.  Recognising the `s`-slice as a curve is
the whole content. -/
theorem chartFieldRep_variationField (α : M) (f : ℝ → ℝ → M) {τ : ℝ}
    (hc : ContinuousAt (fun s => f s τ) 0)
    (hα : f 0 τ ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun s => extChartAt I (f 0 τ) (f s τ)) 0) :
    chartFieldRep (I := I) (f 0) α (variationField (I := I) f) τ
      = deriv (fun s => extChartAt I α (f s τ)) 0 :=
  tangentCoordChange_deriv_chartReading (I := I) (f 0 τ) α hc (mem_chart_source H _) hα hu

/-- **Math.** Petersen §6.1: **`V̇ = D_tV` of the variation field, read in a fixed chart, is the
mixed partial `∂²c̄/∂s∂t`** — the identity that lets Thm. 6.1.4's `|D_tV|²` integrand be stated
without a chart.

$$\dot V(t) \;=\; \Phi\Big(\tfrac{\partial^2 c}{\partial s\,\partial t}(0,t)\Big),
\qquad \Phi=\texttt{tangentCoordChange I α (f 0 t) (f 0 t)} .$$

**Proof.**  `derivAlongCurve_eq_transfer` computes `V̇` from the fixed chart `α` instead of the
moving foot, leaving `covariantDerivCoord` of `chartFieldRep`.  `chartFieldRep_variationField`
identifies that field, *near `t`* — an eventual equality is exactly what
`covariantDerivCoord_congr` consumes, since `covariantDerivCoord` is local in the field (it sees
only `V t` and `deriv V t`).  Then the vendored slice lemma reads the result as a
`mixedPartialCoord` in slots `(0,1)(1,0)`, i.e. `D_t∂_sc`, and `mixedPartialCoord_symm` swaps to
the chart theorem's `(1,0)(0,1)`, i.e. `D_s∂_tc`.  That last swap is the symmetry of second
partials and does **not** hold by `rfl`. -/
theorem derivAlongCurve_variationField_eq_transfer (g : RiemannianMetric I M) (α : M)
    {f : ℝ → ℝ → M} {δ a b t : ℝ} (hδ : 0 < δ) (ht : t ∈ Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Ioo a b))
    (hsrc : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b, Function.uncurry f p ∈ (extChartAt I α).source) :
    derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t
      = tangentCoordChange I α (f 0 t) (f 0 t)
          (mixedPartialCoord (I := I) g α
            (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, t)
            ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) := by
  classical
  set S : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Ioo a b with hS_def
  have hSopen : IsOpen S := isOpen_Ioo.prod isOpen_Ioo
  set c : ℝ × ℝ → E := fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2) with hc_def
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hmemS : ∀ {p : ℝ × ℝ}, p ∈ S → Function.uncurry f p ∈ (extChartAt I α).source :=
    fun {p} hp => hsrc p hp
  -- the chart reading is smooth on the open slab
  have hcS : ContDiffOn ℝ ∞ c S := contDiffOn_extChartAt_comp₂ (I := I) hf hsrc
  have hcAt : ∀ {p : ℝ × ℝ}, p ∈ S → ContDiffAt ℝ ∞ c p := fun {p} hp =>
    (hcS.contDiffAt (hSopen.mem_nhds hp))
  -- the central curve and its chart data at `t`
  have htS : ((0 : ℝ), t) ∈ S := ⟨h0mem, ht⟩
  have hfoot : f 0 t ∈ (extChartAt I α).source := hmemS htS
  have hfootH : f 0 t ∈ (chartAt H α).source := by rwa [extChartAt_source] at hfoot
  have hcont0 : ContinuousAt (f 0) t := by
    have : ContinuousOn (fun τ => c (0, τ)) (Ioo a b) :=
      hcS.continuousOn.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun τ hτ => ⟨h0mem, hτ⟩)
    -- continuity of `f 0` at `t` comes from `f` itself, not its chart reading
    have hmd : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (0, t) :=
      hf.contMDiffAt (hSopen.mem_nhds htS)
    have := hmd.continuousAt.comp (x := t)
      ((continuous_const.prodMk continuous_id).continuousAt)
    exact this
  -- `u = φ_α ∘ f 0` is differentiable at `t`
  have hu : DifferentiableAt ℝ (fun τ => extChartAt I α (f 0 τ)) t := by
    have hd : DifferentiableAt ℝ c (0, t) := (hcAt htS).differentiableAt (by norm_num)
    exact (Jacobi.hasDerivAt_comp_snd hd.hasFDerivAt).differentiableAt
  -- the germ identity: the chart reading of `V` is `∂ₛc`, near `t`
  have hrep : chartFieldRep (I := I) (f 0) α (variationField (I := I) f)
      =ᶠ[𝓝 t] fun τ => fderiv ℝ c (0, τ) ((1, 0) : ℝ × ℝ) := by
    have hnhds : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
    filter_upwards [hnhds] with τ hτ
    have hτS : ((0 : ℝ), τ) ∈ S := ⟨h0mem, hτ⟩
    have hfootτ : f 0 τ ∈ (extChartAt I α).source := hmemS hτS
    have hfootτH : f 0 τ ∈ (chartAt H α).source := by rwa [extChartAt_source] at hfootτ
    -- the `s`-slice at `τ` is a curve; its chart reading is differentiable at `0`
    have hslice : ContinuousAt (fun s => f s τ) 0 := by
      have hmd : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (0, τ) :=
        hf.contMDiffAt (hSopen.mem_nhds hτS)
      exact hmd.continuousAt.comp (x := (0 : ℝ))
        (continuousAt_id.prodMk continuousAt_const)
    have hslice_d : DifferentiableAt ℝ (fun s => extChartAt I (f 0 τ) (f s τ)) 0 := by
      have hev : ∀ᶠ s in 𝓝 (0 : ℝ), f s τ ∈ (extChartAt I (f 0 τ)).source :=
        hslice.eventually_mem ((isOpen_extChartAt_source (I := I) (f 0 τ)).mem_nhds
          (mem_extChartAt_source (I := I) (f 0 τ)))
      have hevα : ∀ᶠ s in 𝓝 (0 : ℝ), f s τ ∈ (extChartAt I α).source :=
        hslice.eventually_mem ((isOpen_extChartAt_source (I := I) α).mem_nhds hfootτ)
      -- differentiate the α-reading, then move to the foot chart by the transition
      have hd : DifferentiableAt ℝ c (0, τ) := (hcAt hτS).differentiableAt (by norm_num)
      have hsl0 : HasDerivAt (fun s => c (s, τ)) (fderiv ℝ c (0, τ) ((1, 0) : ℝ × ℝ)) 0 :=
        Jacobi.hasDerivAt_comp_fst hd.hasFDerivAt
      have hfd : HasFDerivAt (chartTransition (M := M) I α (f 0 τ))
          (tangentCoordChange I α (f 0 τ) (f 0 τ)) (extChartAt I α (f 0 τ)) :=
        hasFDerivAt_chartTransition hfootτ (mem_extChartAt_source (I := I) (f 0 τ))
      have hcomp : HasDerivAt (fun s => chartTransition (M := M) I α (f 0 τ) (c (s, τ)))
          (tangentCoordChange I α (f 0 τ) (f 0 τ) (fderiv ℝ c (0, τ) ((1, 0) : ℝ × ℝ))) 0 :=
        hfd.comp_hasDerivAt_of_eq 0 hsl0 rfl
      refine (hcomp.differentiableAt).congr_of_eventuallyEq ?_
      filter_upwards [hevα] with s hs
      exact (chartTransition_extChartAt (I := I) (β := f 0 τ) hs).symm
    have hkey := chartFieldRep_variationField (I := I) α f hslice hfootτH hslice_d
    -- `deriv` of the `s`-slice of `c` is `fderiv c ((1,0))`
    have hd : DifferentiableAt ℝ c (0, τ) := (hcAt hτS).differentiableAt (by norm_num)
    have hsl : HasDerivAt (fun s => c (s, τ)) (fderiv ℝ c (0, τ) ((1, 0) : ℝ × ℝ)) 0 :=
      Jacobi.hasDerivAt_comp_fst hd.hasFDerivAt
    rw [hkey, hsl.deriv]
  -- transfer `V̇` to the fixed chart `α`
  have hV : DifferentiableAt ℝ (chartFieldRep (I := I) (f 0) α (variationField (I := I) f)) t := by
    have hFD : ContDiffOn ℝ ∞ (fderiv ℝ c) S :=
      hcS.fderiv_of_isOpen hSopen (by simp)
    have hFDat : DifferentiableAt ℝ (fun p => fderiv ℝ c p ((1, 0) : ℝ × ℝ)) (0, t) :=
      ((hFD.clm_apply contDiffOn_const).contDiffAt
        (hSopen.mem_nhds htS)).differentiableAt (by norm_num)
    have hcomp : DifferentiableAt ℝ (fun τ => fderiv ℝ c (0, τ) ((1, 0) : ℝ × ℝ)) t :=
      (Jacobi.hasDerivAt_comp_snd hFDat.hasFDerivAt).differentiableAt
    exact hcomp.congr_of_eventuallyEq hrep
  rw [derivAlongCurve_eq_transfer (I := I) g α hcont0 hfootH hu hV]
  -- swap in the clean field, read it as a mixed partial, and symmetrise the slots
  rw [covariantDerivCoord_congr (I := I) g α (fun τ => extChartAt I α (f 0 τ)) hrep]
  have hc2 : ContDiffAt ℝ 2 c (0, t) := (hcAt htS).of_le (by decide)
  rw [show (fun τ => extChartAt I α (f 0 τ)) = (fun τ => c (0, τ)) from rfl,
    covariantDerivCoord_snd_slice_eq_mixedPartialCoord_gen (I := I) g α
      ((1, 0) : ℝ × ℝ) hc2,
    mixedPartialCoord_symm (I := I) g α hc2]

/-! ### Thm. 6.1.4 with a chart-free conclusion -/

/-- **Math.** Petersen Thm. 6.1.4 (`thm:pet-ch6-synge-second-variation`, pp. 255–256), **Synge's
second variation of energy**, with a **chart-free conclusion**: for a smooth variation `f` of a
**geodesic** `f 0` whose slab lies in one chart,

$$\frac{d}{ds}\Big[\frac{dE(f_s)}{ds}\Big]_{s=0}
  = g\big(\nabla_{\partial_s}\partial_s f,\ \dot{\bar c}\big)\Big|_{t_1}^{t_2}
  + \int_{t_1}^{t_2}\Big(\big|\dot V\big|^2 - g\big(R(V,T)T,\,V\big)\Big)\,dt ,$$

with `V = ∂f/∂s` the variation field, `T = ċ̄` the geodesic's velocity, `V̇ = D_tV`, and `R` the
Levi-Civita curvature tensor.  Every term is stated in Ch. 5/6's chart-free vocabulary —
`energyFunctional`, `transversalAccel`, `variationField`, `curveVelocity`, `derivAlongCurve`,
`curvatureTensorAt`.  **The chart `α` survives only as a hypothesis** (`hsrc`: the whole slab
lies in `(extChartAt I α).source`); it appears nowhere in the conclusion.

This is the **exact Ch. 6 sibling of Ch. 5's `hasDerivAt_windowEnergy`**
(`Ch05/FirstVariation.lean:750`), which likewise assumes a single chart via `hsrc` and likewise
concludes without mentioning it, and whose statement style this mirrors.  That asymmetry is the
point: **because the chart is absent from the conclusion, adjacent windows glue.**  Two abutting
windows may be read in charts centred at different points, yet their boundary pairings are the
same chart-free `g.inner`s and therefore telescope — exactly as Ch. 5 exploits in
`hasDerivAt_pieceEnergy` (`Ch05/FirstVariation.lean:1102`).

**This is therefore NOT yet Petersen's Thm. 6.1.4.**  His variation ranges over a compact
`[a,b]`, which in general leaves every single chart, so no `hsrc` is available; `PetersenLib.
secondVariationEnergy` remains absent.  The one remaining step is the **Lebesgue chart cover**:
chart windows at every time, `lebesgue_number_lemma_of_metric isCompact_Icc`, a uniform
partition, then telescoping these (chart-free!) boundary terms.

**Proof.**  No new mathematics; this is a change of vocabulary on an already-proven theorem.
`energyFunctional_eventuallyEq_windowEnergy_chart` identifies the chart-free energy with the
fixed-chart window integral near `s = 0`, and `hasDerivAt_deriv_of_eventuallyEq` transports the
chart engine's `HasDerivAt (deriv ·)` along that germ — note we never form `deriv (deriv ·)`, so
the "`deriv ∘ deriv` does not sum over pieces" obstruction never arises.  The geodesic
hypothesis passes into the engine's coordinate form by
`mixedPartialCoord_snd_snd_eq_zero_of_isGeodesic`, and the resulting right-hand side is
translated term by term by `Ch06/VariationTransfers.lean`'s dictionary, the metric bridge
`chartMetricInner_eq_inner`, and `(extChartAt I α).left_inv` to move the curvature's foot from
`φ_α⁻¹(c(0,t))` back to `f 0 t`.  On the *open* slab the integrand identity holds at **every**
`t ∈ [t_1,t_2]`, so `intervalIntegral.integral_congr` suffices — no null-set dance.

**The sign.**  The engine produces `+ g(R(V,T)V, T)` while Synge's formula carries
`- g(R(V,T)T, V)`.  These agree: they differ by antisymmetry of the `(0,4)`-curvature form in its
**last pair** (`isAlgCurvatureForm_curvatureTensorFourAt … |>.antisymm₃₄` at `(V,T,V,T)`), which
applies at bare tangent vectors because `metricInner_apply` is `rfl`.  The engine's `+` is not an
error. -/
theorem hasDerivAt_deriv_windowEnergy (g : RiemannianMetric I M) (α : M)
    {f : ℝ → ℝ → M} {δ a b t₁ t₂ : ℝ} (hδ : 0 < δ) (h12 : t₁ < t₂)
    (hsub : Icc t₁ t₂ ⊆ Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Ioo a b))
    (hsrc : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b, Function.uncurry f p ∈ (extChartAt I α).source)
    (hgeo : ∀ t ∈ Icc t₁ t₂, curveAcceleration (I := I) g (f 0) t = 0) :
    HasDerivAt (deriv (fun s : ℝ => energyFunctional (I := I) g (f s) t₁ t₂))
      (g.inner (f 0 t₂) (transversalAccel (I := I) g f t₂) (curveVelocity (I := I) (f 0) t₂)
        - g.inner (f 0 t₁) (transversalAccel (I := I) g f t₁) (curveVelocity (I := I) (f 0) t₁)
        + ∫ t in t₁..t₂,
            (g.inner (f 0 t) (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
                              (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
             - g.inner (f 0 t)
                 (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
                   (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
                   (curveVelocity (I := I) (f 0) t))
                 (variationField (I := I) f t))) 0 := by
  classical
  set c : ℝ × ℝ → E := fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2) with hcdef
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hSopen : IsOpen (Ioo (-δ) δ ×ˢ Ioo a b) := isOpen_Ioo.prod isOpen_Ioo
  have hc : ContDiffOn ℝ ∞ c (Ioo (-δ) δ ×ˢ Ioo a b) := contDiffOn_extChartAt_comp₂ hf hsrc
  have hc2 : ContDiffOn ℝ 2 c (Ioo (-δ) δ ×ˢ Ioo a b) := hc.of_le (by decide)
  have hmem : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b, c p ∈ (extChartAt I α).target :=
    fun p hp => (extChartAt I α).map_source (hsrc p hp)
  have hgeo' : ∀ t ∈ Icc t₁ t₂,
      mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) = 0 :=
    fun t ht => mixedPartialCoord_snd_snd_eq_zero_of_isGeodesic (I := I) g α hδ (hsub ht)
      hcdef hc2 hsrc (hgeo t ht)
  have hchart := hasDerivAt_deriv_windowEnergy_chart_curvatureTensorAt (I := I) g α hδ h12
    hsub hc hmem hgeo'
  have heq := energyFunctional_eventuallyEq_windowEnergy_chart (I := I) g α hδ h12
    (hf.mono (Set.prod_mono subset_rfl hsub))
    (fun p hp => hsrc p ⟨hp.1, hsub hp.2⟩)
  have htrans := hasDerivAt_deriv_of_eventuallyEq heq hchart
  -- pointwise dictionary on the open time window
  have hc0 : ∀ τ : ℝ, c (0, τ) = extChartAt I α (f 0 τ) := fun _ => rfl
  have hx : ∀ τ ∈ Ioo a b, f 0 τ ∈ (extChartAt I α).source :=
    fun τ hτ => hsrc (0, τ) ⟨h0mem, hτ⟩
  have hd : ∀ τ ∈ Ioo a b, DifferentiableAt ℝ c (0, τ) := fun τ hτ =>
    ((hc.contDiffAt (hSopen.mem_nhds ⟨h0mem, hτ⟩)).differentiableAt (by norm_num))
  have ht₁ : t₁ ∈ Ioo a b := hsub (left_mem_Icc.mpr h12.le)
  have ht₂ : t₂ ∈ Ioo a b := hsub (right_mem_Icc.mpr h12.le)
  apply htrans.congr_deriv
  congr 1
  · -- the boundary pairings
    rw [transversalAccel_eq_tangentCoordChange_mixedPartialCoord (I := I) g α hδ ht₂
        hcdef hc2 hsrc,
      curveVelocity_eq_tangentCoordChange (I := I) α hδ ht₂ hcdef (hd t₂ ht₂) hsrc,
      transversalAccel_eq_tangentCoordChange_mixedPartialCoord (I := I) g α hδ ht₁
        hcdef hc2 hsrc,
      curveVelocity_eq_tangentCoordChange (I := I) α hδ ht₁ hcdef (hd t₁ ht₁) hsrc,
      hc0 t₂, hc0 t₁, chartMetricInner_eq_inner (I := I) g (hx t₂ ht₂),
      chartMetricInner_eq_inner (I := I) g (hx t₁ ht₁)]
  · -- the integrand, at every time of the window
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le h12.le] at ht
    have htab : t ∈ Ioo a b := hsub ht
    have hfoot : (extChartAt I α).symm (c (0, t)) = f 0 t :=
      (extChartAt I α).left_inv (hx t htab)
    rw [derivAlongCurve_variationField_eq_transfer (I := I) g α hδ htab hf hsrc,
      variationField_eq_tangentCoordChange (I := I) α hδ htab hcdef (hd t htab) hsrc,
      curveVelocity_eq_tangentCoordChange (I := I) α hδ htab hcdef (hd t htab) hsrc,
      hfoot, hc0 t, chartMetricInner_eq_inner (I := I) g (hx t htab), ← hcdef]
    -- Synge's sign: `⟨R(V,T)V, T⟩ = -⟨R(V,T)T, V⟩` is antisymmetry in the last pair
    have hanti := (isAlgCurvatureForm_curvatureTensorFourAt (g.leviCivita) (f 0 t)).antisymm₃₄
      (tangentCoordChange I α (f 0 t) (f 0 t) (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)))
      (tangentCoordChange I α (f 0 t) (f 0 t) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)))
      (tangentCoordChange I α (f 0 t) (f 0 t) (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)))
      (tangentCoordChange I α (f 0 t) (f 0 t) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)))
    simp only [curvatureTensorFourAt, RiemannianMetric.metricInner_apply] at hanti
    rw [hanti]
    ring

end PetersenLib

end
