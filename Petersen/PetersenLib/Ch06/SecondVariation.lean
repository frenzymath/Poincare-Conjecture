import PetersenLib.Ch06.JacobiFields
import PetersenLib.Ch05.FirstVariation
import PetersenLib.Ch05.EnergyMinimizers

/-!
# Petersen Ch. 6, §6.1 — towards Synge's second variation formula (GTM 171, 3rd ed.)

Petersen's Thm. 6.1.4 (`thm:pet-ch6-synge-second-variation`, pp. 255–256) differentiates
the **first** variation of energy a second time in `s`.  This file assembles the pieces
that weld Ch. 5's energy/first-variation layer to Ch. 6's connection-along-a-curve layer,
so that the second differentiation can be carried out in Ch. 6's chart-free vocabulary.

## What is here

* `derivAlongCurve_curveVelocity` — **the glue lemma** `D_t(ċ) = c̈`: Ch. 6's covariant
  derivative of the velocity field *is* Ch. 5's `curveAcceleration`.  The two layers were
  built independently and turn out to speak the same language: both read at the *moving
  foot* `c t`.  Without this, Thm. 6.1.4's geodesic hypothesis (`c̈ = 0`, in Ch. 5's
  words) cannot meet the Jacobi/curvature machinery (in Ch. 6's words).
* `hasDerivAt_pieceEnergy_shift` — **the shift lemma**: the first variation of energy at an
  *arbitrary* parameter `s₀`, not just at `0`.  Petersen's proof of Thm. 6.1.4
  differentiates `E'(s)` in `s`, so it needs `E'` as a *function* of `s`;
  `firstVariationOfEnergy` is the `s = 0` special case only.  `hasDerivAt_pieceEnergy`
  takes a raw `f` and re-bases, which is exactly what makes the shift possible.
* `variationField`, `transversalAccel` — Petersen's `∂c̄/∂s(0,·)` and `∂²c̄/∂s²(0,·)`,
  named in Ch. 6's chart-free vocabulary.
* `hasDerivAt_chartPairing_slice_ss` — **the `s`-slice lemma**: the second differentiation
  of the energy's integrand.  See below.
* `hasDerivAt_windowEnergy_chart_preByParts_shift` — the *pre*-by-parts first variation at an
  **arbitrary** `s₀`.  `hasDerivAt_windowEnergy_chart`'s third conjunct gives it at `s = 0`
  only; differentiating once more in `s` needs it as a *function* of `s`.
* `hasDerivAt_integral_chartPairing_ss` — the `s`-slice lemma **carried under the integral**
  by dominated convergence, i.e. `d/ds ∫ₐᵇ ⟨D_s∂ₜc, ∂ₜc⟩ dt` at `s = 0`.

Composing the last two gives `d²E(c_s)/ds²|₀ = ∫ₐᵇ ⟨D_sD_s∂ₜc, ∂ₜc⟩ dt + ∫ₐᵇ |D_s∂ₜc|² dt`,
the display in Thm. 6.1.4's formalized proof.  What then remains of Thm. 6.1.4 is the
*identification* of the first integral: Lemma 6.1.2 pointwise, the geodesic hypothesis, and
one integration by parts at `s = 0`.

## The second differentiation, and why it happens *before* the by-parts

Petersen differentiates the first variation *after* integrating it by parts.  That route
is closed to us: the post-by-parts formula's boundary terms live in the *moving foot chart*
`extChartAt I (c̄ s t)`, whose `s`-dependence no calculus lemma reaches.  Instead we
differentiate the *pre*-by-parts first variation
`dE(c_s)/ds = ∫ₐᵇ ⟨D_s∂ₜc, ∂ₜc⟩ dt` — a pure integral with **no boundary term** — so the
second differentiation is plain differentiation under the integral, and the by-parts
happens once, at the end, at `s = 0`, where `∂ₜ²c = 0` already.

`hasDerivAt_chartPairing_slice_ss` is that second differentiation's integrand step:
`∂/∂s ⟨D_s∂ₜc, ∂ₜc⟩ = ⟨D_sD_s∂ₜc, ∂ₜc⟩ + |D_s∂ₜc|²`.  It is metric compatibility
(`hasDerivAt_chartMetricInner_along`) applied with a **second-order** field in the first
slot; `mixedPartialCoord_productRule` is the same statement one order lower, and does not
cover it.  The one genuinely hard side condition — that `s ↦ D_s∂ₜc` is differentiable at
all — is `hasDerivAt_mixedPartialCoord_fst_slice`, whose Christoffel half is the vendored
`Jacobi.hasDerivAt_chartChristoffelContraction_along`.

## The moving-foot convention, and why the two layers agree

`derivAlongCurve g c V t` reads `V` in the chart at `c t` — the *moving* foot — and
`curveAcceleration g γ t` does the same.  The glue lemma's proof turns on the
`fix-α := c t` direction: one shows the fixed-chart reading `chartFieldRep c (c t) ċ`
agrees *eventually near `t`* with the naive reading `deriv (φ_{c t} ∘ c)`, using
`chartReading_acceleration_transfer` to move between the chart at `c τ` and the chart at
`c t`.  Going the other way — trying to compare the moving charts directly — does not
work, since there is no single chart containing the whole curve.
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
  [I.Boundaryless]

section Glue

variable [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** Petersen §6.1: the covariant derivative of a curve's own velocity field is
its acceleration, `D_t(ċ) = c̈`.  Ch. 6's `derivAlongCurve` applied to Ch. 6's
`curveVelocity` is Ch. 5's `curveAcceleration`.

**Proof.** Both sides read at the moving foot `c t`, so the Christoffel terms agree
definitionally; what needs proof is that the two `deriv`s agree, i.e. that the fixed-chart
field reading `chartFieldRep c (c t) ċ` coincides *eventually near `t`* with the naive
fixed-chart reading `deriv (φ_{c t} ∘ c)`.  At a nearby `τ` the field value `ċ τ` is
coordinatised at `c τ`, so transporting it to the chart at `c t` is exactly what
`chartReading_acceleration_transfer` computes; the two coordinate changes then compose to
the identity (`tangentCoordChange_comp`, `tangentCoordChange_self`).  Since the two
functions of `τ` agree on a neighbourhood of `t`, their derivatives at `t` agree. -/
theorem derivAlongCurve_curveVelocity (g : RiemannianMetric I M) (c : ℝ → M) (t : ℝ)
    (hc : ContinuousAt c t)
    (hu1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I (c t) (c s'))
      (deriv (fun s' => extChartAt I (c t) (c s')) s) s)
    (hu2 : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (deriv (fun s' => extChartAt I (c t) (c s'))) s) :
    derivAlongCurve (I := I) g c (curveVelocity (I := I) c) t
      = curveAcceleration (I := I) g c t := by
  classical
  have hev : ∀ᶠ s in 𝓝 t, c s ∈ (extChartAt I (c t)).source :=
    hc.eventually_mem ((isOpen_extChartAt_source (I := I) (c t)).mem_nhds
      (mem_extChartAt_source (I := I) (c t)))
  have hkey : chartFieldRep (I := I) c (c t) (curveVelocity (I := I) c)
      =ᶠ[𝓝 t] deriv (fun s' => extChartAt I (c t) (c s')) := by
    filter_upwards [eventually_eventually_nhds.mpr hev, eventually_eventually_nhds.mpr hu1,
      hu2, hev] with τ hτev hτu1 hτu2 hτsrc
    -- `c` is continuous at `τ`: it is `φ⁻¹` of its (differentiable) fixed-chart reading
    have hcτ : ContinuousAt c τ := by
      have hread : ContinuousAt (fun s' => extChartAt I (c t) (c s')) τ :=
        hτu1.self_of_nhds.differentiableAt.continuousAt
      have hcomp : ContinuousAt ((extChartAt I (c t)).symm ∘
          fun s' => extChartAt I (c t) (c s')) τ :=
        ContinuousAt.comp (g := (extChartAt I (c t)).symm)
          (f := fun s' => extChartAt I (c t) (c s'))
          (continuousAt_extChartAt_symm'' ((extChartAt I (c t)).map_source hτsrc)) hread
      refine hcomp.congr ?_
      filter_upwards [hτev] with s hs
      exact (extChartAt I (c t)).left_inv hs
    have hevτ : ∀ᶠ s in 𝓝 τ, c s ∈ (extChartAt I (c t)).source ∩
        (extChartAt I (c τ)).source := by
      filter_upwards [hτev, hcτ.eventually_mem ((isOpen_extChartAt_source (I := I) (c τ)).mem_nhds
        (mem_extChartAt_source (I := I) (c τ)))] with s h1 h2 using ⟨h1, h2⟩
    have h1 := (chartReading_acceleration_transfer (I := I) g (α := c t) (β := c τ)
      hevτ hτu1 hτu2.hasDerivAt).1
    show tangentCoordChange I (c τ) (c t) (c τ) (curveVelocity (I := I) c τ) = _
    have hvel : curveVelocity (I := I) c τ
        = (deriv (fun s' => extChartAt I (c τ) (c s')) τ : E) := rfl
    rw [hvel, h1, tangentCoordChange_comp
      ⟨⟨hτsrc, mem_extChartAt_source (I := I) (c τ)⟩, hτsrc⟩]
    exact tangentCoordChange_self (I := I) hτsrc
  rw [derivAlongCurve_def, curveAcceleration_def, hkey.deriv_eq]
  rfl

end Glue

/-! ### Petersen's variation vocabulary, chart-free -/

/-- **Math.** Petersen §6.1: the **variation field** `V(t) = ∂c̄/∂s(0,t)` of a variation
`c̄`, as a vector field along the base curve `c̄(0,·)`.  This is `curveVelocity` of the
transversal curve `σ ↦ c̄(σ,t)` at `σ = 0`; it is *definitionally* the object Ch. 5's
`firstVariationOfEnergy` already integrates against. -/
def variationField (f : ℝ → ℝ → M) (t : ℝ) : TangentSpace I (f 0 t) :=
  curveVelocity (I := I) (fun σ => f σ t) 0

/-- **Math.** The variation field is the chart-derivative Ch. 5's first-variation formula
uses — the two chapters' vocabularies agree definitionally, with no bridge lemma. -/
theorem variationField_eq (f : ℝ → ℝ → M) (t : ℝ) :
    variationField (I := I) f t = (deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E) := rfl

/-- **Math.** Petersen §6.1: `∂²c̄/∂s²(0,t)`, the **transversal acceleration** — the
acceleration of the curve `σ ↦ c̄(σ,t)` at `σ = 0`.  This is what carries the boundary
term of Thm. 6.1.4; it vanishes when the transversal curves are geodesics. -/
def transversalAccel (g : RiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ) :
    TangentSpace I (f 0 t) :=
  curveAcceleration (I := I) g (fun σ => f σ t) 0

/-! ### The first variation at an arbitrary parameter -/

/-- **Math.** Petersen §6.1 (p. 255), the input to Thm. 6.1.4: the **first variation of
energy at an arbitrary parameter `s₀`**, not merely at `s₀ = 0`.

Petersen's proof of the second variation formula differentiates `dE(c_s)/ds` in `s`, so it
needs the first variation as a *function of `s`* on a neighbourhood of `0`;
`firstVariationOfEnergy` gives only the value at `s = 0`.

**Proof.** Re-base: `hasDerivAt_pieceEnergy` accepts a *raw* variation, so apply it to the
shifted variation `f'(σ,t) = f(s₀+σ, t)` on the shrunken slab `Ioo (-δ') δ' ×ˢ Icc p₁ p₂`
with `δ' = δ - |s₀|`, which the triangle inequality keeps inside the original slab.  Then
undo the shift by composing with `s ↦ s - s₀` (`HasDerivAt.comp`, inner derivative `1`). -/
theorem hasDerivAt_pieceEnergy_shift (g : RiemannianMetric I M)
    {f : ℝ → ℝ → M} {δ p₁ p₂ s₀ : ℝ} (hδ : |s₀| < δ) (h12 : p₁ < p₂)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Icc p₁ p₂)) :
    HasDerivAt (fun s : ℝ => energyFunctional (I := I) g (f s) p₁ p₂)
      (g.inner (f s₀ p₂)
          ((deriv (fun σ => extChartAt I (f s₀ p₂) (f (s₀ + σ) p₂)) 0 : E))
          ((derivWithin (fun t => extChartAt I (f s₀ p₂) (f s₀ t)) (Icc p₁ p₂) p₂ : E))
        - g.inner (f s₀ p₁)
            ((deriv (fun σ => extChartAt I (f s₀ p₁) (f (s₀ + σ) p₁)) 0 : E))
            ((derivWithin (fun t => extChartAt I (f s₀ p₁) (f s₀ t)) (Icc p₁ p₂) p₁ : E))
        - ∫ t in p₁..p₂, g.inner (f s₀ t)
            ((deriv (fun σ => extChartAt I (f s₀ t) (f (s₀ + σ) t)) 0 : E))
            (curveAcceleration (I := I) g (f s₀) t)) s₀ := by
  classical
  set δ' : ℝ := δ - |s₀| with hδ'
  have hδ'pos : 0 < δ' := by simp only [hδ']; linarith
  set f' : ℝ → ℝ → M := fun σ t => f (s₀ + σ) t with hf'
  -- the shifted variation is smooth on the shrunken slab
  have hsm : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f')
      (Ioo (-δ') δ' ×ˢ Icc p₁ p₂) := by
    have hshift : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
        (fun p : ℝ × ℝ => (s₀ + p.1, p.2)) := by
      apply ContDiff.contMDiff
      exact (contDiff_const.add (contDiff_fst)).prodMk contDiff_snd
    have hmaps : MapsTo (fun p : ℝ × ℝ => (s₀ + p.1, p.2))
        (Ioo (-δ') δ' ×ˢ Icc p₁ p₂) (Ioo (-δ) δ ×ˢ Icc p₁ p₂) := by
      rintro ⟨σ, t⟩ ⟨hσ, ht⟩
      refine ⟨?_, ht⟩
      simp only [mem_Ioo] at hσ
      have hσabs : |σ| < δ' := abs_lt.mpr hσ
      have hsum : |s₀ + σ| < δ := by
        calc |s₀ + σ| ≤ |s₀| + |σ| := abs_add_le s₀ σ
          _ < |s₀| + δ' := by linarith
          _ = δ := by simp only [hδ']; ring
      exact mem_Ioo.mpr (abs_lt.mp hsum)
    exact hf.comp hshift.contMDiffOn hmaps
  have hpiece := (hasDerivAt_pieceEnergy (I := I) g (f := f') hδ'pos h12 hsm).2
  -- undo the shift: `E(f s) = (E ∘ f') (s - s₀)`
  have hinner : HasDerivAt (fun s : ℝ => s - s₀) 1 s₀ := (hasDerivAt_id s₀).sub_const s₀
  have hcomp := HasDerivAt.comp (h := fun s : ℝ => s - s₀) s₀
    (by simp only [sub_self]; exact hpiece) hinner
  have hfun : ((fun σ : ℝ => energyFunctional (I := I) g (f' σ) p₁ p₂) ∘ fun s : ℝ => s - s₀)
      = fun s : ℝ => energyFunctional (I := I) g (f s) p₁ p₂ := by
    funext s
    simp only [Function.comp_apply, hf']
    norm_num
  rw [hfun, mul_one] at hcomp
  have hff : f' 0 = f s₀ := by
    funext t; show f (s₀ + 0) t = f s₀ t; rw [add_zero]
  rw [hff] at hcomp
  simpa only [hf'] using hcomp

/-! ### The `s`-slice product rule: the second differentiation under the integral -/

/-- **Math.** The covariant `s`-derivative of the field `∂ₜc` along an `s`-slice **is** the
coordinate mixed partial `∂²c/∂s∂t`.

This is the bookkeeping identity that turns the metric product rule's second term
`⟨V, D_s∂ₜc⟩` into `|D_s∂ₜc|²`: the two chapters spell the same object differently, Ch. 5
as `mixedPartialCoord` (a Γ-corrected second derivative of the two-variable map) and the
vendored connection layer as `covariantDerivCoord` (a Γ-corrected `deriv` along a curve).
Unfolding both, the claim is exactly that the slice derivatives
`deriv (fun s => c (s, t))` and `deriv (fun s => Dc (s,t)·∂ₜ)` are the corresponding
partials of `c` — two applications of `Jacobi.hasDerivAt_comp_fst`. -/
theorem covariantDerivCoord_fst_slice_eq_mixedPartialCoord
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t : ℝ} (hc : ContDiffAt ℝ 2 c (s₀, t)) :
    covariantDerivCoord (I := I) g α (fun s => c (s, t))
        (fun s => fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ)) s₀
      = mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
  have hfd2 : ContDiffAt ℝ 1 (fderiv ℝ c) (s₀, t) := hc.fderiv_right (m := 1) (by norm_num)
  have hgw : DifferentiableAt ℝ (fun y => fderiv ℝ c y ((0, 1) : ℝ × ℝ)) (s₀, t) :=
    (hfd2.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hu : HasDerivAt (fun s => c (s, t)) (fderiv ℝ c (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hW : HasDerivAt (fun s => fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ))
      (fderiv ℝ (fun y => fderiv ℝ c y ((0, 1) : ℝ × ℝ)) (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst hgw.hasFDerivAt
  rw [covariantDerivCoord_def, mixedPartialCoord_def, hu.deriv, hW.deriv]

/-- **Math.** The mixed partial `∂²c/∂s∂t` is **differentiable along the `s`-slice**, with
its derivative split into the pure third-derivative term and the three Christoffel terms
(two vector-slot derivatives plus the base-directional derivative).

This is the one genuinely hard side condition of `hasDerivAt_chartPairing_slice_ss`: the
metric product-rule engine needs `s ↦ D_s∂ₜc` to be differentiable at all, and `D_s∂ₜc`
carries a Christoffel contraction whose base point `c (s, t)` *moves* with `s`.  The
vendored `Jacobi.hasDerivAt_chartChristoffelContraction_along` is exactly the Leibniz rule
for that moving-base contraction; the pure-derivative half needs `c` to be `C³` (the
Christoffel half needs only `C²`, so order 3 is what the *first* summand costs, and it is
tight — nothing to spare). -/
theorem hasDerivAt_mixedPartialCoord_fst_slice (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t : ℝ} (hc : ContDiffAt ℝ 3 c (s₀, t))
    (hmem : c (s₀, t) ∈ interior (extChartAt I α).target) :
    HasDerivAt
      (fun s : ℝ => mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
      (fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ c z ((0, 1) : ℝ × ℝ)) y
            ((1, 0) : ℝ × ℝ)) (s₀, t) ((1, 0) : ℝ × ℝ)
        + (Geodesic.chartChristoffelContraction (I := I) g α
              (fderiv ℝ (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ)) (s₀, t) ((1, 0) : ℝ × ℝ))
              (fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ)) (c (s₀, t))
            + Geodesic.chartChristoffelContraction (I := I) g α
              (fderiv ℝ c (s₀, t) ((1, 0) : ℝ × ℝ))
              (fderiv ℝ (fun y => fderiv ℝ c y ((0, 1) : ℝ × ℝ)) (s₀, t) ((1, 0) : ℝ × ℝ))
              (c (s₀, t))
            + Jacobi.baseDerivChristoffelContraction (I := I) g α
              (fderiv ℝ c (s₀, t) ((1, 0) : ℝ × ℝ)) (fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ))
              (fderiv ℝ c (s₀, t) ((1, 0) : ℝ × ℝ)) (c (s₀, t)))) s₀ := by
  -- regularity of the first and second derivatives of `c` at the base point
  have hfd2 : ContDiffAt ℝ 2 (fderiv ℝ c) (s₀, t) := hc.fderiv_right (m := 2) (by norm_num)
  have hga : ContDiffAt ℝ 2 (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ)) (s₀, t) :=
    hfd2.clm_apply contDiffAt_const
  have hgb : ContDiffAt ℝ 2 (fun y => fderiv ℝ c y ((0, 1) : ℝ × ℝ)) (s₀, t) :=
    hfd2.clm_apply contDiffAt_const
  have hH : DifferentiableAt ℝ
      (fun y => fderiv ℝ (fun z => fderiv ℝ c z ((0, 1) : ℝ × ℝ)) y ((1, 0) : ℝ × ℝ))
      (s₀, t) :=
    (((hgb.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)).differentiableAt
      (by norm_num)
  -- the three slice curves
  have hu : HasDerivAt (fun s => c (s, t)) (fderiv ℝ c (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst (hc.differentiableAt (by norm_num)).hasFDerivAt
  have ha : HasDerivAt (fun s => fderiv ℝ c (s, t) ((1, 0) : ℝ × ℝ))
      (fderiv ℝ (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ)) (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst (hga.differentiableAt (by norm_num)).hasFDerivAt
  have hb : HasDerivAt (fun s => fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ))
      (fderiv ℝ (fun y => fderiv ℝ c y ((0, 1) : ℝ × ℝ)) (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst (hgb.differentiableAt (by norm_num)).hasFDerivAt
  -- the pure second-derivative summand
  have hfirst : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun y => fderiv ℝ c y ((0, 1) : ℝ × ℝ)) (s, t) ((1, 0) : ℝ × ℝ))
      (fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ c z ((0, 1) : ℝ × ℝ)) y
        ((1, 0) : ℝ × ℝ)) (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst hH.hasFDerivAt
  -- the Christoffel summand
  have hsecond := Jacobi.hasDerivAt_chartChristoffelContraction_along (I := I) g α
    (fun s => fderiv ℝ c (s, t) ((1, 0) : ℝ × ℝ))
    (fun s => fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ))
    (fun s => c (s, t)) _ _ _ ha hb hu hmem
  simpa only [mixedPartialCoord_def] using hfirst.add hsecond

/-- **Math.** Petersen Thm. 6.1.4 (`thm:pet-ch6-synge-second-variation`), the **second
differentiation under the integral**:
$$\frac{\partial}{\partial s}\Big\langle \frac{D}{\partial s}\frac{\partial c}{\partial t},
  \frac{\partial c}{\partial t}\Big\rangle
  = \Big\langle \frac{D}{\partial s}\frac{D}{\partial s}\frac{\partial c}{\partial t},
    \frac{\partial c}{\partial t}\Big\rangle
  + \Big|\frac{D}{\partial s}\frac{\partial c}{\partial t}\Big|^2 ,$$
read in the fixed chart at `α`.

This is metric compatibility with the **second-order** field `D_s∂ₜc` in the first slot —
the step `mixedPartialCoord_productRule` cannot supply, since it pairs *first*-order fields
only.  Applying `hasDerivAt_chartMetricInner_along` gives `⟨D_sV, W⟩ + ⟨V, D_sW⟩` with
`V = D_s∂ₜc` and `W = ∂ₜc`; `covariantDerivCoord_fst_slice_eq_mixedPartialCoord` identifies
`D_sW = V`, collapsing the second term to `|D_s∂ₜc|²`. -/
theorem hasDerivAt_chartPairing_slice_ss (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t : ℝ} (hc : ContDiffAt ℝ 3 c (s₀, t))
    (hmem : c (s₀, t) ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => chartMetricInner (I := I) g α (c (s, t))
        (mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ)))
      (chartMetricInner (I := I) g α (c (s₀, t))
          (covariantDerivCoord (I := I) g α (fun s => c (s, t))
            (fun s => mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
            s₀)
          (fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ))
        + chartMetricInner (I := I) g α (c (s₀, t))
            (mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
            (mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))) s₀ := by
  classical
  have hmem' : c (s₀, t) ∈ (extChartAt I α).target := interior_subset hmem
  have hc2 : ContDiffAt ℝ 2 c (s₀, t) := hc.of_le (by norm_num)
  have hfd2 : ContDiffAt ℝ 1 (fderiv ℝ c) (s₀, t) := hc2.fderiv_right (m := 1) (by norm_num)
  -- the three curves along the `s`-slice
  have hu : HasDerivAt (fun s => c (s, t)) (fderiv ℝ c (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hW : HasDerivAt (fun s => fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ))
      (fderiv ℝ (fun y => fderiv ℝ c y ((0, 1) : ℝ × ℝ)) (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst
      ((hfd2.clm_apply contDiffAt_const).differentiableAt (by norm_num)).hasFDerivAt
  have hV := hasDerivAt_mixedPartialCoord_fst_slice (I := I) g α hc hmem
  -- side conditions at the base point, from chart-target membership
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (c (s₀, t)) := fun i j =>
    ((chartGramOnE_contDiffOn (I := I) g α i j).contDiffAt
      (extChartAt_target_mem_nhds' (I := I) hmem')).differentiableAt (by norm_num)
  have hbase : (extChartAt I α).symm (c (s₀, t))
      ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I α).map_target hmem'
  -- the metric-compatibility engine
  have key := hasDerivAt_chartMetricInner_along (I := I) g α
    (fun s => c (s, t))
    (fun s => mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
    (fun s => fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ)) (t := s₀)
    hu.differentiableAt hV.differentiableAt hW.differentiableAt hG hbase
  refine key.congr_deriv ?_
  rw [covariantDerivCoord_fst_slice_eq_mixedPartialCoord (I := I) g α hc2]


/-- **Math.** Translating the argument of a two-variable chart map translates its
Γ-corrected mixed second partial: `∂²(c ∘ (a + ·))/∂v∂w (y) = ∂²c/∂v∂w (a + y)`.

This is unconditional — no differentiability hypothesis — because `p ↦ a + p` is a
translation, so `mathlib`'s `fderiv_comp_add_left` transports the `fderiv`s in both
directions (junk values included), and the Christoffel contraction only sees the
first derivatives and the basepoint `c (a + y)`. -/
theorem mixedPartialCoord_comp_const_add (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} (a : ℝ × ℝ) (y v w : ℝ × ℝ) :
    mixedPartialCoord (I := I) g α (fun p : ℝ × ℝ => c (a + p)) y v w
      = mixedPartialCoord (I := I) g α c (a + y) v w := by
  simp only [mixedPartialCoord_def, fderiv_comp_add_left]
  rw [fderiv_comp_add_left (f := fun z : ℝ × ℝ => fderiv ℝ c z w) (x := y) a]

/-- **Math.** Petersen §6.1, the input to Thm. 6.1.4: the **pre-by-parts first variation
of energy at an arbitrary parameter `s₀`**, not merely at `s₀ = 0`.

`hasDerivAt_windowEnergy_chart`'s third conjunct gives
`dE(c_s)/ds = ∫ ⟨D_s∂ₜc, ∂ₜc⟩ dt` only at `s = 0`; differentiating it once more in `s`
needs it as a *function* of `s` on a neighbourhood of the base parameter.

**Proof.** Re-base, exactly as `hasDerivAt_pieceEnergy_shift` does for the post-by-parts
form: apply the third conjunct to the translated map `c' = c ∘ ((s₀, 0) + ·)` on the
shrunken slab `Ioo (-δ') δ' ×ˢ Icc t₁ t₂` with `δ' = δ - |s₀|`, which the triangle
inequality keeps inside the original slab, then undo the shift by composing with
`s ↦ s - s₀` (`HasDerivAt.comp`, inner derivative `1`).  The translated map's partials
are `c`'s, by `fderiv_comp_add_left` and `mixedPartialCoord_comp_const_add`. -/
theorem hasDerivAt_windowEnergy_chart_preByParts_shift (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {δ t₁ t₂ s₀ : ℝ} (hs₀ : |s₀| < δ) (h12 : t₁ < t₂)
    (hc : ContDiffOn ℝ ∞ c (Ioo (-δ) δ ×ˢ Icc t₁ t₂))
    (hmem : ∀ p ∈ Ioo (-δ) δ ×ˢ Icc t₁ t₂, c p ∈ (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => ∫ t in t₁..t₂, (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t))
      (∫ t in t₁..t₂, chartMetricInner (I := I) g α (c (s₀, t))
        (mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ))) s₀ := by
  classical
  set δ' : ℝ := δ - |s₀| with hδ'
  have hδ'pos : 0 < δ' := by simp only [hδ']; linarith
  set a : ℝ × ℝ := (s₀, 0) with ha
  set c' : ℝ × ℝ → E := fun p => c (a + p) with hc'def
  have hmaps : MapsTo (fun p : ℝ × ℝ => a + p) (Ioo (-δ') δ' ×ˢ Icc t₁ t₂)
      (Ioo (-δ) δ ×ˢ Icc t₁ t₂) := by
    rintro ⟨σ, t⟩ ⟨hσ, ht⟩
    simp only [ha, Prod.mk_add_mk, zero_add, mem_prod]
    refine ⟨?_, ht⟩
    simp only [mem_Ioo] at hσ
    have hσabs : |σ| < δ' := abs_lt.mpr hσ
    have hsum : |s₀ + σ| < δ := by
      calc |s₀ + σ| ≤ |s₀| + |σ| := abs_add_le s₀ σ
        _ < |s₀| + δ' := by linarith
        _ = δ := by simp only [hδ']; ring
    exact mem_Ioo.mpr (abs_lt.mp hsum)
  have hcd : ContDiffOn ℝ ∞ c' (Ioo (-δ') δ' ×ˢ Icc t₁ t₂) :=
    hc.comp (contDiff_const.add contDiff_id).contDiffOn hmaps
  have hmem' : ∀ p ∈ Ioo (-δ') δ' ×ˢ Icc t₁ t₂, c' p ∈ (extChartAt I α).target :=
    fun p hp => hmem _ (hmaps hp)
  have H := (hasDerivAt_windowEnergy_chart (I := I) g α (c := c') hδ'pos h12 hcd hmem').2.2
  have hinner : HasDerivAt (fun s : ℝ => s - s₀) 1 s₀ := (hasDerivAt_id s₀).sub_const s₀
  have hcomp := HasDerivAt.comp (h := fun s : ℝ => s - s₀) s₀
    (by simp only [sub_self]; exact H) hinner
  rw [mul_one] at hcomp
  have hfun : ((fun s : ℝ => ∫ t in t₁..t₂, (1 / 2) * chartMetricInner (I := I) g α (c' (s, t))
        (derivWithin (fun t' => c' (s, t')) (Icc t₁ t₂) t)
        (derivWithin (fun t' => c' (s, t')) (Icc t₁ t₂) t)) ∘ fun s : ℝ => s - s₀)
      = fun s : ℝ => ∫ t in t₁..t₂, (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t) := by
    funext s
    simp only [Function.comp_apply, hc'def, ha, Prod.mk_add_mk, zero_add, add_sub_cancel]
  rw [hfun] at hcomp
  have hval : (∫ t in t₁..t₂, chartMetricInner (I := I) g α (c' (0, t))
        (mixedPartialCoord (I := I) g α c' (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c' (0, t) ((0, 1) : ℝ × ℝ)))
      = ∫ t in t₁..t₂, chartMetricInner (I := I) g α (c (s₀, t))
        (mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ)) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [hc'def, mixedPartialCoord_comp_const_add (I := I) g α a (0, t),
      fderiv_comp_add_left (f := c) (x := (0, t)) a]
    simp only [ha, Prod.mk_add_mk, add_zero, zero_add]
  rw [hval] at hcomp
  exact hcomp


/-- `C^n` version of `continuousOn_chartChristoffelContraction_comp`. -/
theorem contDiffOn_chartChristoffelContraction_comp {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (g : RiemannianMetric I M) (α : M) {n : WithTop ℕ∞} (hn : n ≤ (∞ : WithTop ℕ∞))
    {y u v : X → E} {S : Set X}
    (hy : ContDiffOn ℝ n y S) (hu : ContDiffOn ℝ n u S) (hv : ContDiffOn ℝ n v S)
    (hmem : ∀ x ∈ S, y x ∈ (extChartAt I α).target) :
    ContDiffOn ℝ n (fun x =>
      Geodesic.chartChristoffelContraction (I := I) g α (u x) (v x) (y x)) S := by
  classical
  simp only [Geodesic.chartChristoffelContraction_def]
  refine ContDiffOn.sum fun k _ => ContDiffOn.smul ?_ contDiffOn_const
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
  have hmaps : MapsTo y S (interior (extChartAt I α).target) := fun x hx =>
    extChartAt_target_subset_interior_of_boundaryless (I := I) α (hmem x hx)
  have hcoord : ∀ (k' : Fin (Module.finrank ℝ E)) (w : X → E), ContDiffOn ℝ n w S →
      ContDiffOn ℝ n (fun x => Geodesic.chartCoord (E := E) k' (w x)) S := by
    intro k' w hw
    have := (Geodesic.chartCoordFunctional (E := E) k').contDiff.comp_contDiffOn hw
    simpa using this
  have hΓ0 : ContDiffOn ℝ n (chartChristoffel (I := I) g α i j k ∘ y) S :=
    ContDiffOn.comp ((chartChristoffel_contDiffOn_interior (I := I) g α i j k).of_le hn)
      hy hmaps
  have hΓ : ContDiffOn ℝ n (fun x => chartChristoffel (I := I) g α i j k (y x)) S := by
    simpa only [Function.comp_def] using hΓ0
  exact (hΓ.mul (hcoord i u hu)).mul (hcoord j v hv)


/-- **Track 2**: differentiation under the integral for the pre-by-parts first variation. -/
theorem hasDerivAt_integral_chartPairing_ss (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {δ t₁ t₂ : ℝ} (hδ : 0 < δ) (h12 : t₁ < t₂)
    (hc : ContDiffOn ℝ ∞ c (Ioo (-δ) δ ×ˢ Icc t₁ t₂))
    (hmem : ∀ p ∈ Ioo (-δ) δ ×ˢ Icc t₁ t₂, c p ∈ (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => ∫ t in t₁..t₂, chartMetricInner (I := I) g α (c (s, t))
        (mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ)))
      (∫ t in t₁..t₂, (chartMetricInner (I := I) g α (c (0, t))
          (covariantDerivCoord (I := I) g α (fun s => c (s, t))
            (fun s => mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) 0)
          (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
        + chartMetricInner (I := I) g α (c (0, t))
            (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
            (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)))) 0 := by
  classical
  set S : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Icc t₁ t₂ with hS_def
  have hSuniq : UniqueDiffOn ℝ S := isOpen_Ioo.uniqueDiffOn.prod (uniqueDiffOn_Icc h12)
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hint_nhds : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ → S ∈ 𝓝 (s, t) := by
    intro s t hs ht
    refine Filter.mem_of_superset
      ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hs, ht⟩) ?_
    exact Set.prod_mono subset_rfl Ioo_subset_Icc_self
  have hCAt : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ → ContDiffAt ℝ 3 c (s, t) := by
    intro s t hs ht
    exact ((hc (s, t) ⟨hs, Ioo_subset_Icc_self ht⟩).contDiffAt
      (hint_nhds hs ht)).of_le (by norm_cast)
  -- the within derivative fields
  have hD1 : ContDiffOn ℝ 2 (fderivWithin ℝ c S) S := hc.fderivWithin hSuniq (by norm_cast)
  have hD1cont : ContinuousOn (fderivWithin ℝ c S) S := hD1.continuousOn
  have hD2 : ContDiffOn ℝ 1 (fderivWithin ℝ (fderivWithin ℝ c S) S) S :=
    hD1.fderivWithin hSuniq (by norm_cast)
  have hD1_int : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ →
      fderivWithin ℝ c S (s, t) = fderiv ℝ c (s, t) := by
    intro s t hs ht
    exact fderivWithin_of_mem_nhds (hint_nhds hs ht)
  have hD1_ev : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ →
      fderivWithin ℝ c S =ᶠ[𝓝 (s, t)] fderiv ℝ c := by
    intro s t hs ht
    filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).eventually_mem
      (⟨hs, ht⟩ : (s, t) ∈ Ioo (-δ) δ ×ˢ Ioo t₁ t₂)] with p hp
    exact fderivWithin_of_mem_nhds (hint_nhds hp.1 hp.2)
  have hD2_int : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ → ∀ v w : ℝ × ℝ,
      fderivWithin ℝ (fderivWithin ℝ c S) S (s, t) v w
        = fderiv ℝ (fun q => fderiv ℝ c q w) (s, t) v := by
    intro s t hs ht v w
    have hfd : DifferentiableAt ℝ (fderiv ℝ c) (s, t) :=
      (((hCAt hs ht).of_le (by norm_num : (2:WithTop ℕ∞) ≤ 3)).fderiv_right
        (m := 1) (by norm_num)).differentiableAt (by norm_num)
    rw [fderivWithin_of_mem_nhds (hint_nhds hs ht), (hD1_ev hs ht).fderiv_eq,
      fderiv_fderiv_apply hfd w v]
  have hderiv_s : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Icc t₁ t₂ →
      deriv (fun s' => c (s', t)) s = fderivWithin ℝ c S (s, t) ((1, 0) : ℝ × ℝ) := by
    intro s t hs ht
    have hdw : DifferentiableWithinAt ℝ c S (s, t) :=
      (hc (s, t) ⟨hs, ht⟩).differentiableWithinAt (by norm_num)
    have hline : HasDerivAt (fun s' : ℝ => ((s', t) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) s := by
      simpa using (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
    have hcomp : HasDerivWithinAt (fun s' : ℝ => c (s', t))
        (fderivWithin ℝ c S (s, t) ((1, 0) : ℝ × ℝ)) (Ioo (-δ) δ) s :=
      hdw.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq s
        (hline.hasDerivWithinAt (s := Ioo (-δ) δ)) (fun s' hs' => ⟨hs', ht⟩) rfl
    exact (hcomp.hasDerivAt (Ioo_mem_nhds hs.1 hs.2)).deriv
  -- the within mixed partial `∂ₛ∂ₜ`
  set MPst : ℝ × ℝ → E := fun p =>
    fderivWithin ℝ (fderivWithin ℝ c S) S p ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
      + Geodesic.chartChristoffelContraction (I := I) g α
          (fderivWithin ℝ c S p ((1, 0) : ℝ × ℝ))
          (fderivWithin ℝ c S p ((0, 1) : ℝ × ℝ)) (c p) with hMPst_def
  have hMP_int : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ →
      MPst (s, t)
        = mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
    intro s t hs ht
    simp only [hMPst_def]
    rw [hD2_int hs ht ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ), hD1_int hs ht, mixedPartialCoord_def]
  -- `MPst` is `C¹` on the slab
  have hD1v : ∀ v : ℝ × ℝ, ContDiffOn ℝ 1 (fun p => fderivWithin ℝ c S p v) S :=
    fun v => (hD1.of_le (by norm_cast)).clm_apply contDiffOn_const
  have hD2vw : ∀ v w : ℝ × ℝ,
      ContDiffOn ℝ 1 (fun p => fderivWithin ℝ (fderivWithin ℝ c S) S p v w) S :=
    fun v w => (hD2.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hMPst_cd : ContDiffOn ℝ 1 MPst S := by
    rw [hMPst_def]
    exact (hD2vw ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)).add
      (contDiffOn_chartChristoffelContraction_comp (I := I) g α (by norm_cast)
        (hc.of_le (by norm_cast)) (hD1v ((1, 0) : ℝ × ℝ)) (hD1v ((0, 1) : ℝ × ℝ)) hmem)
  -- `D_s` of the mixed partial, in within form, and the covariant `s`-derivative field
  set DsMP : ℝ × ℝ → E := fun p => fderivWithin ℝ MPst S p ((1, 0) : ℝ × ℝ) with hDsMP_def
  have hDsMP_cont : ContinuousOn DsMP S := by
    rw [hDsMP_def]
    exact (hMPst_cd.continuousOn_fderivWithin hSuniq le_rfl).clm_apply continuousOn_const
  set Tw : ℝ × ℝ → E := fun p => DsMP p
      + Geodesic.chartChristoffelContraction (I := I) g α
          (fderivWithin ℝ c S p ((1, 0) : ℝ × ℝ)) (MPst p) (c p) with hTw_def
  have hMPst_cont : ContinuousOn MPst S := hMPst_cd.continuousOn
  have hD1vc : ∀ v : ℝ × ℝ, ContinuousOn (fun p => fderivWithin ℝ c S p v) S :=
    fun v => (hD1v v).continuousOn
  have hTw_cont : ContinuousOn Tw S := by
    rw [hTw_def]
    exact hDsMP_cont.add (continuousOn_chartChristoffelContraction_comp (I := I) g α
      hc.continuousOn (hD1vc ((1, 0) : ℝ × ℝ)) hMPst_cont hmem)
  -- the within form of the target integrand
  set F'w : ℝ × ℝ → ℝ := fun p =>
    chartMetricInner (I := I) g α (c p) (Tw p) (fderivWithin ℝ c S p ((0, 1) : ℝ × ℝ))
      + chartMetricInner (I := I) g α (c p) (MPst p) (MPst p) with hF'w_def
  have hF'w_cont : ContinuousOn F'w S := by
    rw [hF'w_def]
    exact (continuousOn_chartMetricInner_comp (I := I) g α hc.continuousOn hTw_cont
        (hD1vc ((0, 1) : ℝ × ℝ)) hmem).add
      (continuousOn_chartMetricInner_comp (I := I) g α hc.continuousOn hMPst_cont
        hMPst_cont hmem)
  set Fw : ℝ × ℝ → ℝ := fun p =>
    chartMetricInner (I := I) g α (c p) (MPst p) (fderivWithin ℝ c S p ((0, 1) : ℝ × ℝ))
    with hFw_def
  have hFw_cont : ContinuousOn Fw S := by
    rw [hFw_def]
    exact continuousOn_chartMetricInner_comp (I := I) g α hc.continuousOn hMPst_cont
      (hD1vc ((0, 1) : ℝ × ℝ)) hmem
  -- the covariant `s`-derivative of `∂ₛ∂ₜc` in within form, at interior points
  have hCov_int : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ →
      covariantDerivCoord (I := I) g α (fun s' => c (s', t))
          (fun s' => mixedPartialCoord (I := I) g α c (s', t)
            ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) s
        = Tw (s, t) := by
    intro s t hs ht
    have hev : MPst =ᶠ[𝓝 (s, t)]
        (fun p => mixedPartialCoord (I := I) g α c p ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) := by
      filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).eventually_mem
        (⟨hs, ht⟩ : (s, t) ∈ Ioo (-δ) δ ×ˢ Ioo t₁ t₂)] with p hp
      exact hMP_int hp.1 hp.2
    have hdiff : DifferentiableAt ℝ MPst (s, t) :=
      ((hMPst_cd.differentiableOn (by norm_num)) (s, t)
        ⟨hs, Ioo_subset_Icc_self ht⟩).differentiableAt (hint_nhds hs ht)
    have hdiffM : DifferentiableAt ℝ
        (fun p => mixedPartialCoord (I := I) g α c p ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        (s, t) := hdiff.congr_of_eventuallyEq hev.symm
    have hslice : deriv (fun s' => mixedPartialCoord (I := I) g α c (s', t)
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) s = DsMP (s, t) := by
      rw [(Jacobi.hasDerivAt_comp_fst hdiffM.hasFDerivAt).deriv, hDsMP_def]
      simp only []
      rw [fderivWithin_of_mem_nhds (hint_nhds hs ht), hev.fderiv_eq]
    rw [covariantDerivCoord_def, hslice, hderiv_s hs (Ioo_subset_Icc_self ht),
      ← hMP_int hs ht]
  -- the integrand family and its `s`-derivative
  set F : ℝ → ℝ → ℝ := fun s t => chartMetricInner (I := I) g α (c (s, t))
      (mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
      (fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ)) with hF_def
  set F' : ℝ → ℝ → ℝ := fun s t => chartMetricInner (I := I) g α (c (s, t))
      (covariantDerivCoord (I := I) g α (fun s' => c (s', t))
        (fun s' => mixedPartialCoord (I := I) g α c (s', t)
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) s)
      (fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ))
    + chartMetricInner (I := I) g α (c (s, t))
        (mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        (mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
    with hF'_def
  have hF_eq : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ → F s t = Fw (s, t) := by
    intro s t hs ht
    simp only [hF_def, hFw_def]
    rw [hMP_int hs ht, hD1_int hs ht]
  have hF'_eq : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ → F' s t = F'w (s, t) := by
    intro s t hs ht
    simp only [hF'_def, hF'w_def]
    rw [hCov_int hs ht, hMP_int hs ht, hD1_int hs ht]
  -- lines and compactness bookkeeping
  have hline : ∀ s : ℝ, ContinuousOn (fun t : ℝ => ((s, t) : ℝ × ℝ)) (Icc t₁ t₂) :=
    fun s => (continuous_const.prodMk continuous_id).continuousOn
  have hmaps : ∀ {s : ℝ}, s ∈ Ioo (-δ) δ →
      MapsTo (fun t : ℝ => ((s, t) : ℝ × ℝ)) (Icc t₁ t₂) S := fun hs t ht => ⟨hs, ht⟩
  have hnull : volume ({t₁, t₂} : Set ℝ) = 0 := (Set.toFinite _).measure_zero volume
  have hIoc_mem : ∀ {t : ℝ}, t ∈ Ι t₁ t₂ → t ∉ ({t₁, t₂} : Set ℝ) → t ∈ Ioo t₁ t₂ := by
    intro t htI htbad
    rw [Set.uIoc_of_le h12.le, Set.mem_Ioc] at htI
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at htbad
    exact ⟨htI.1, lt_of_le_of_ne htI.2 htbad.2⟩
  -- measurability and integrability of the family
  have hF_meas : ∀ᶠ s in 𝓝 (0 : ℝ), AEStronglyMeasurable (F s)
      (volume.restrict (Ι t₁ t₂)) := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
    have hcline : ContinuousOn (fun t : ℝ => Fw (s, t)) (Icc t₁ t₂) :=
      hFw_cont.comp (hline s) (hmaps hs)
    have hbase : AEStronglyMeasurable (fun t : ℝ => Fw (s, t))
        (volume.restrict (Ι t₁ t₂)) := by
      rw [Set.uIoc_of_le h12.le]
      exact (hcline.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    refine hbase.congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI
    exact (hF_eq hs (hIoc_mem htI htbad)).symm
  have hF_int : IntervalIntegrable (F 0) volume t₁ t₂ := by
    have hcline : ContinuousOn (fun t : ℝ => Fw (0, t)) (Icc t₁ t₂) :=
      hFw_cont.comp (hline 0) (hmaps h0mem)
    refine (hcline.intervalIntegrable_of_Icc h12.le).congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI
    exact (hF_eq h0mem (hIoc_mem htI htbad)).symm
  have hF'_meas : AEStronglyMeasurable (F' 0) (volume.restrict (Ι t₁ t₂)) := by
    have hcline : ContinuousOn (fun t : ℝ => F'w (0, t)) (Icc t₁ t₂) :=
      hF'w_cont.comp (hline 0) (hmaps h0mem)
    have hbase : AEStronglyMeasurable (fun t : ℝ => F'w (0, t))
        (volume.restrict (Ι t₁ t₂)) := by
      rw [Set.uIoc_of_le h12.le]
      exact (hcline.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    refine hbase.congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI
    exact (hF'_eq h0mem (hIoc_mem htI htbad)).symm
  -- the uniform majorant on the compact half-width slab
  have hhalf : Icc (-(δ / 2)) (δ / 2) ×ˢ Icc t₁ t₂ ⊆ S := by
    refine Set.prod_mono ?_ subset_rfl
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hKcomp : IsCompact (Icc (-(δ / 2)) (δ / 2) ×ˢ Icc t₁ t₂) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hKcomp.exists_bound_of_continuousOn (hF'w_cont.mono hhalf)
  have hδ2pos : 0 < δ / 2 := by positivity
  have hsnhds : Ioo (-(δ / 2)) (δ / 2) ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ2pos
  have hIoo_half : Ioo (-(δ / 2)) (δ / 2) ⊆ Ioo (-δ) δ := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι t₁ t₂ →
      ∀ s ∈ Ioo (-(δ / 2)) (δ / 2), ‖F' s t‖ ≤ C := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI s hs
    have ht : t ∈ Ioo t₁ t₂ := hIoc_mem htI htbad
    rw [hF'_eq (hIoo_half hs) ht]
    exact hC (s, t) ⟨⟨hs.1.le, hs.2.le⟩, Ioo_subset_Icc_self ht⟩
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι t₁ t₂ →
      ∀ s ∈ Ioo (-(δ / 2)) (δ / 2), HasDerivAt (fun s' => F s' t) (F' s t) s := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI s hs
    have ht : t ∈ Ioo t₁ t₂ := hIoc_mem htI htbad
    have hs' : s ∈ Ioo (-δ) δ := hIoo_half hs
    exact hasDerivAt_chartPairing_slice_ss (I := I) g α (hCAt hs' ht)
      (extChartAt_target_subset_interior_of_boundaryless (I := I) α
        (hmem _ ⟨hs', Ioo_subset_Icc_self ht⟩))
  obtain ⟨-, hmain⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hsnhds hF_meas hF_int hF'_meas h_bound intervalIntegrable_const h_diff
  exact hmain



/-! ### The second variation of energy, in chart form -/

/-- **Math.** Petersen Thm 6.1.4 (Synge), the second variation of energy in a fixed chart:
writing `E s` for the windowed energy of the `s`-th longitudinal curve, its *second*
derivative at `0` is
`∫ ⟨D_s∂ₜc, ∂ₜc⟩ + ⟨D_s∂ₜc, D_s∂ₜc⟩`.
This is the composition of the two halves proved in `Ch06/SecondVariation.lean`: energy is
differentiated twice in `s`, with the first variation differentiated **before** any
integration by parts.

**Proof.** `hasDerivAt_windowEnergy_chart_preByParts_shift` gives `HasDerivAt E (Φ s₀) s₀`
for *every* `s₀` in the open window `Ioo (-δ) δ`, where `Φ` is precisely the function
`hasDerivAt_integral_chartPairing_ss` differentiates.  Hence `deriv E` and `Φ` agree on that
open window, so `deriv E =ᶠ[𝓝 0] Φ`; transferring the DCT lemma's `HasDerivAt Φ _ 0` along
that eventual equality with `HasDerivAt.congr_of_eventuallyEq` gives the claim. -/
theorem hasDerivAt_deriv_windowEnergy_chart (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {δ t₁ t₂ : ℝ} (hδ : 0 < δ) (h12 : t₁ < t₂)
    (hc : ContDiffOn ℝ ∞ c (Ioo (-δ) δ ×ˢ Icc t₁ t₂))
    (hmem : ∀ p ∈ Ioo (-δ) δ ×ˢ Icc t₁ t₂, c p ∈ (extChartAt I α).target) :
    HasDerivAt (deriv (fun s : ℝ => ∫ t in t₁..t₂, (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)))
      (∫ t in t₁..t₂, (chartMetricInner (I := I) g α (c (0, t))
          (covariantDerivCoord (I := I) g α (fun s => c (s, t))
            (fun s => mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) 0)
          (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
        + chartMetricInner (I := I) g α (c (0, t))
            (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
            (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)))) 0 := by
  classical
  -- `Φ` is the pre-by-parts first variation, read at an arbitrary base parameter `s`.
  set Φ : ℝ → ℝ := fun s : ℝ => ∫ t in t₁..t₂, chartMetricInner (I := I) g α (c (s, t))
      (mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
      (fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ)) with hΦ
  -- The shift lemma pins `deriv E` to `Φ` at every point of the open window `Ioo (-δ) δ`,
  -- which is a neighbourhood of `0`.
  have hEq : deriv (fun s : ℝ => ∫ t in t₁..t₂, (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
      (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)
      (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)) =ᶠ[𝓝 0] Φ := by
    refine Filter.eventuallyEq_of_mem (s := Ioo (-δ) δ)
      (Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ) (fun s₀ hs₀ => ?_)
    exact (hasDerivAt_windowEnergy_chart_preByParts_shift (I := I) g α
      (abs_lt.mpr (mem_Ioo.mp hs₀)) h12 hc hmem).deriv
  -- The DCT lemma differentiates `Φ` at `0`; transfer along the eventual equality.
  exact (hasDerivAt_integral_chartPairing_ss (I := I) g α hδ h12 hc hmem).congr_of_eventuallyEq hEq

/-- The second variation of energy (`hasDerivAt_deriv_windowEnergy_chart`) restated as a value
of `iteratedDeriv 2`, i.e. literally `E'' 0`. -/
theorem iteratedDeriv_two_windowEnergy_chart (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {δ t₁ t₂ : ℝ} (hδ : 0 < δ) (h12 : t₁ < t₂)
    (hc : ContDiffOn ℝ ∞ c (Ioo (-δ) δ ×ˢ Icc t₁ t₂))
    (hmem : ∀ p ∈ Ioo (-δ) δ ×ˢ Icc t₁ t₂, c p ∈ (extChartAt I α).target) :
    iteratedDeriv 2 (fun s : ℝ => ∫ t in t₁..t₂, (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)) 0
      = ∫ t in t₁..t₂, (chartMetricInner (I := I) g α (c (0, t))
          (covariantDerivCoord (I := I) g α (fun s => c (s, t))
            (fun s => mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) 0)
          (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
        + chartMetricInner (I := I) g α (c (0, t))
            (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
            (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  exact (hasDerivAt_deriv_windowEnergy_chart (I := I) g α hδ h12 hc hmem).deriv


end PetersenLib

end
