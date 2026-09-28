import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Topping.MaximumPrinciple.ScalarConsequences

/-!
# The volume is weakly decreasing under nonnegative scalar curvature (Topping, Cor. 3.2.6)

Topping's Corollary 3.2.6: if a Ricci flow on a closed manifold has `R ≥ 0` at
`t = 0`, its volume is weakly decreasing. His proof is two steps:

1. `R ≥ 0` is *preserved*, by the weak minimum principle — Corollary 3.2.3;
2. the volume form evolves by `∂_t dV = -R\,dV` (Ricci flow substitutes
   `\tr h = -2R` into `∂_tdV = ½(\tr h)dV`), so
   `V'(t) = -∫_\M R\,dV_t ≤ 0`.

Step 1 is the maximum-principle content and is **proved** here, from
`scalarCurvature_nonneg_of_initial_nonneg`. Step 2 has an analytic half that this
project does not have — differentiating `t ↦ ∫_\M dV_t` under the integral sign,
and the pointwise variation of the density — so it enters as the named hypothesis
`HasVolumeDerivativeOn`, which says exactly `V'(t) = -∫R\,dV_t` and nothing more.
`HasVolumeFormVariationOn` in `Riemannian/Variation.lean` is its pointwise
counterpart at the level of the density; wiring the two together is the missing
integration step.

So Corollary 3.2.6 below is an implication with one named open antecedent. What it
is *not* is a restatement: the passage from "`R ≥ 0` initially" to "`R ≥ 0`
throughout", which is the only place the maximum principle is used, is discharged
rather than assumed, and the sign that makes the conclusion come out is the one
`HasVolumeDerivativeOn` records.

The measures `μ t` stand for the Riemannian volume measures of `g t`
(`MorganTianLib.riemannianMeasure` builds these); nothing below needs them to be
*that* family, only that `V'` is the negative `μ t`-integral of `R`, which is
where the geometry lives.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian MeasureTheory Filter

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [MeasurableSpace M]

/-- **Math.** `V'(t) = -∫_\M R\,dV_t`: the volume of a Ricci flow differentiates to
minus the total scalar curvature. This is the integrated form of
`∂_tdV = ½(\tr h)dV` with `\tr h = -2R`, i.e. `∂_tdV = -R\,dV`, together with
differentiation under the integral sign.

Stated as a hypothesis on `(V, μ)`: `V` is the volume function and `μ t` the volume
measure of `g t`. Both analytic ingredients — the density variation and the
interchange of `∂_t` with `∫` — are inside this predicate; nothing else in this
module assumes anything about `V` or `μ`. -/
def HasVolumeDerivativeOn (g : ℝ → RiemannianMetric I M) (V : ℝ → ℝ)
    (μ : ℝ → Measure M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, HasDerivWithinAt V (-∫ p, scalarCurvatureAt (g t) p ∂(μ t)) J t

set_option linter.unusedSectionVars false in
/-- **Math.** A dominated pointwise density evolution integrates to the total
volume evolution `V' = -∫ R dμ`.

Here `ρ_t` is a nonnegative density with respect to a fixed reference measure
`ν`, `μ_t = ρ_t ν`, and `V(t) = ∫ ρ_t dν`.  If `∂ₜρ = -Rρ` on an open
neighborhood `U` of the target time set `K`, and the derivatives admit one
integrable dominating function, differentiation under the integral sign gives
`HasVolumeDerivativeOn` on all of `K`, including its endpoints.

This is the analytic bridge from the pointwise volume-form producer to the
global producer. Applying it to the canonical Riemannian measure still requires
a global density representation and the stated domination bound. -/
theorem hasVolumeDerivativeOn_of_weightedDensity
    {g : ℝ → RiemannianMetric I M} (ν : Measure M)
    (ρ : ℝ → M → NNReal) {K U : Set ℝ} (hU : IsOpen U) (hKU : K ⊆ U)
    (hρmeas : ∀ t ∈ U, Measurable (ρ t))
    (hρint : ∀ t ∈ U, Integrable (fun p => (ρ t p : ℝ)) ν)
    (hderiv : ∀ t ∈ U, ∀ p,
      HasDerivAt (fun s => (ρ s p : ℝ))
        (-scalarCurvatureAt (g t) p * (ρ t p : ℝ)) t)
    (hderivMeas : ∀ t ∈ U,
      AEStronglyMeasurable
        (fun p => -scalarCurvatureAt (g t) p * (ρ t p : ℝ)) ν)
    (bound : M → ℝ) (hboundInt : Integrable bound ν)
    (hbound : ∀ᵐ p ∂ν, ∀ t ∈ U,
      ‖-scalarCurvatureAt (g t) p * (ρ t p : ℝ)‖ ≤ bound p) :
    HasVolumeDerivativeOn g
      (fun t => ∫ p, (ρ t p : ℝ) ∂ν)
      (fun t => ν.withDensity (fun p => (ρ t p : ENNReal))) K := by
  intro t ht
  have htU := hKU ht
  have hFmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun p => (ρ s p : ℝ)) ν := by
    filter_upwards [hU.mem_nhds htU] with s hs
    exact (hρint s hs).aestronglyMeasurable
  have hparam :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := ν) (F := fun s p => (ρ s p : ℝ))
      (F' := fun s p => -scalarCurvatureAt (g s) p * (ρ s p : ℝ))
      (x₀ := t) (s := U) (bound := bound)
      (hU.mem_nhds htU) hFmeas
      (hρint t htU) (hderivMeas t htU) hbound hboundInt
      (Filter.Eventually.of_forall fun p s hs => hderiv s hs p)
  have hweighted :
      (∫ p, scalarCurvatureAt (g t) p
          ∂(ν.withDensity (fun p => (ρ t p : ENNReal)))) =
        ∫ p, (ρ t p : ℝ) * scalarCurvatureAt (g t) p ∂ν := by
    rw [integral_withDensity_eq_integral_smul (hρmeas t htU)]
    congr 1
  have htarget :
      (∫ p, -scalarCurvatureAt (g t) p * (ρ t p : ℝ) ∂ν) =
        -(∫ p, scalarCurvatureAt (g t) p
          ∂(ν.withDensity (fun p => (ρ t p : ENNReal)))) := by
    rw [hweighted, ← integral_neg]
    congr 1
    funext p
    ring
  rw [htarget] at hparam
  exact hparam.2.hasDerivWithinAt

set_option linter.unusedSectionVars false in
/-- **Math.** Differentiation under an integral on a convex time set.

The within-set slope formulation is what permits endpoint times: the pointwise
derivative is only required along `K`, and the convex mean-value estimate gives
an integrable majorant for the difference quotients. -/
theorem hasDerivWithinAt_integral_of_dominated_of_derivWithin_le
    (ν : Measure M) {F F' : ℝ → M → ℝ} {K : Set ℝ}
    (hK : Convex ℝ K)
    (hFint : ∀ s ∈ K, Integrable (F s) ν)
    (hderiv : ∀ s ∈ K, ∀ p,
      HasDerivWithinAt (fun r => F r p) (F' s p) K s)
    (bound : M → ℝ) (hboundInt : Integrable bound ν)
    (hbound : ∀ᵐ p ∂ν, ∀ s ∈ K, ‖F' s p‖ ≤ bound p)
    {t : ℝ} (ht : t ∈ K) :
    HasDerivWithinAt (fun s => ∫ p, F s p ∂ν)
      (∫ p, F' t p ∂ν) K t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hparam :
      Tendsto
        (fun s => ∫ p, slope (fun r => F r p) t s ∂ν)
        (𝓝[K \ {t}] t) (𝓝 (∫ p, F' t p ∂ν)) := by
    apply tendsto_integral_filter_of_dominated_convergence bound
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      have hsK : s ∈ K := hs.1
      have hnum := (hFint s hsK).aestronglyMeasurable.sub
        (hFint t ht).aestronglyMeasurable
      have hmeas := hnum.div₀
        (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _ : M => s - t) ν)
      have hmeas' : AEStronglyMeasurable
          (fun p => (F s p - F t p) / (s - t)) ν := by
        apply hmeas.congr
        exact Filter.Eventually.of_forall fun p => by
          simp only [Pi.div_apply, Pi.sub_apply]
      simpa only [slope_def_field] using hmeas'
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      filter_upwards [hbound] with p hp
      have hlip : ‖F s p - F t p‖ ≤ bound p * ‖s - t‖ :=
        hK.norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun u hu => hderiv u hu p)
          (fun u hu => hp u hu) ht hs.1
      have hne : s - t ≠ 0 := sub_ne_zero.mpr (by simpa using hs.2)
      rw [slope_def_field, norm_div,
        div_le_iff₀ (norm_pos_iff.mpr hne)]
      exact hlip
    · exact hboundInt
    · exact Filter.Eventually.of_forall fun p =>
        (hasDerivWithinAt_iff_tendsto_slope.mp (hderiv t ht p))
  refine hparam.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  have hsK : s ∈ K := hs.1
  simp only [slope_def_field]
  rw [integral_div, integral_sub (hFint s hsK) (hFint t ht)]

set_option linter.unusedSectionVars false in
/-- **Math.** A dominated within-set evolution of a nonnegative density produces
the canonical volume derivative, including endpoint times. -/
theorem hasVolumeDerivativeOn_of_weightedDensityWithin
    {g : ℝ → RiemannianMetric I M} (ν : Measure M)
    (ρ : ℝ → M → NNReal) {K : Set ℝ} (hK : Convex ℝ K)
    (hρmeas : ∀ t ∈ K, Measurable (ρ t))
    (hρint : ∀ t ∈ K, Integrable (fun p => (ρ t p : ℝ)) ν)
    (hderiv : ∀ t ∈ K, ∀ p,
      HasDerivWithinAt (fun s => (ρ s p : ℝ))
        (-scalarCurvatureAt (g t) p * (ρ t p : ℝ)) K t)
    (bound : M → ℝ) (hboundInt : Integrable bound ν)
    (hbound : ∀ᵐ p ∂ν, ∀ t ∈ K,
      ‖-scalarCurvatureAt (g t) p * (ρ t p : ℝ)‖ ≤ bound p) :
    HasVolumeDerivativeOn g
      (fun t => ∫ p, (ρ t p : ℝ) ∂ν)
      (fun t => ν.withDensity (fun p => (ρ t p : ENNReal))) K := by
  intro t ht
  have hparam :=
    hasDerivWithinAt_integral_of_dominated_of_derivWithin_le
      (ν := ν) (F := fun s p => (ρ s p : ℝ))
      (F' := fun s p =>
        -scalarCurvatureAt (g s) p * (ρ s p : ℝ))
      (K := K) hK hρint hderiv bound hboundInt hbound ht
  have hweighted :
      (∫ p, scalarCurvatureAt (g t) p
          ∂(ν.withDensity (fun p => (ρ t p : ENNReal)))) =
        ∫ p, (ρ t p : ℝ) * scalarCurvatureAt (g t) p ∂ν := by
    rw [integral_withDensity_eq_integral_smul (hρmeas t ht)]
    congr 1
  have htarget :
      (∫ p, -scalarCurvatureAt (g t) p * (ρ t p : ℝ) ∂ν) =
        -(∫ p, scalarCurvatureAt (g t) p
          ∂(ν.withDensity (fun p => (ρ t p : ENNReal)))) := by
    rw [hweighted, ← integral_neg]
    congr 1
    funext p
    ring
  rw [htarget] at hparam
  exact hparam

#print axioms Topping.hasVolumeDerivativeOn_of_weightedDensity
#print axioms Topping.hasDerivWithinAt_integral_of_dominated_of_derivWithin_le
#print axioms Topping.hasVolumeDerivativeOn_of_weightedDensityWithin

section

variable [CompactSpace M]

set_option linter.unusedSectionVars false in
/-- **Math.** With nonnegative scalar curvature at every time of `J`, the volume
has nonpositive derivative: the integrand of `V' = -∫R\,dV` is nonnegative, so the
integral is, so `V' ≤ 0`.

Isolated from the corollary because it is the only place the integral appears, and
it needs no Ricci flow — just the sign of `R`. -/
theorem derivWithin_volume_nonpos_of_scalarCurvature_nonneg
    {g : ℝ → RiemannianMetric I M} {V : ℝ → ℝ} {μ : ℝ → Measure M} {J : Set ℝ}
    (hV : HasVolumeDerivativeOn g V μ J)
    (hR : ∀ t ∈ J, ∀ p, 0 ≤ scalarCurvatureAt (g t) p)
    {t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) :
    derivWithin V J t ≤ 0 := by
  rw [(hV t ht).derivWithin hJ]
  have hint : 0 ≤ ∫ p, scalarCurvatureAt (g t) p ∂(μ t) :=
    integral_nonneg (fun p => hR t ht p)
  linarith

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Corollary 3.2.6.** For a Ricci flow on a closed manifold
with `R ≥ 0` at `t = 0`, the volume is weakly decreasing on `[0,T]`.

The nonnegativity of `R` at *later* times is not assumed: it is proved from the
initial hypothesis by the weak minimum principle
(`scalarCurvature_nonneg_of_initial_nonneg`, Cor. 3.2.3), which is the step the
book's proof also makes. The remaining input is `HasVolumeDerivativeOn`, the
identity `V' = -∫R\,dV`.

Monotonicity is concluded from the sign of the derivative on the interior of
`[0,T]` together with continuity on all of it, both supplied by
`HasVolumeDerivativeOn`. -/
theorem volume_antitoneOn_of_scalarCurvature_initial_nonneg
    {g : ℝ → RiemannianMetric I M} {V : ℝ → ℝ} {μ : ℝ → Measure M} {T : ℝ}
    (hT : 0 < T)
    (hRsmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T))
    (hzero : ∀ p, 0 ≤ scalarCurvatureAt (g 0) p)
    (hV : HasVolumeDerivativeOn g V μ (Icc 0 T)) :
    AntitoneOn V (Icc 0 T) := by
  -- Step 1: the maximum principle propagates `R ≥ 0` to every time.
  have hR : ∀ t ∈ Icc 0 T, ∀ p, 0 ≤ scalarCurvatureAt (g t) p := by
    intro t ht p
    exact scalarCurvature_nonneg_of_initial_nonneg hT hRsmooth hevolution hzero p t ht
  -- Step 2: `V' = -∫R dV ≤ 0`, so `V` is antitone.
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
    (fun t ht => (hV t ht).continuousWithinAt)
    (f' := fun t => -∫ p, scalarCurvatureAt (g t) p ∂(μ t))
    (fun t ht => ?_) (fun t ht => ?_)
  · exact (hV t (interior_subset ht)).mono interior_subset
  · have hint : 0 ≤ ∫ p, scalarCurvatureAt (g t) p ∂(μ t) :=
      integral_nonneg (fun p => hR t (interior_subset ht) p)
    linarith

end

end Topping

end
