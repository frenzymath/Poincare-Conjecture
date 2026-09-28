import PetersenLib.Ch06.BonnetSyngeVariation

/-!
# Petersen Ch. 6, §6.3 — Myers' theorem (Thm. 6.3.3): the Ricci second variation

Theorem 6.3.3 (`thm:pet-ch6-myers-ricci-diameter`, Myers 1941) strengthens the Bonnet–Synge
hypothesis `sec ≥ k > 0` (Lemma 6.3.1) to the **Ricci** bound `Ric ≥ (n-1)k > 0`, and still
concludes that a geodesic of length `> π/√k` is not locally minimizing — whence the same
diameter bound `diam ≤ π/√k` and finiteness of `π₁`.

Petersen's proof differs from 6.3.1 only in the curvature bookkeeping.  Instead of a single
perpendicular parallel field `E`, extend a `g`-orthonormal frame `ċ(0)=E₁,E₂,…,E_n` of
`T_{c(0)}M` by parallel translation and use the `m = n-1` fields `Vᵢ(t)=sin(π t/l)Eᵢ(t)`,
`i=2,…,n`.  Summing Synge's second-variation formula over the perpendicular directions and
using the **trace identity** `Ric(ċ,ċ) = ∑ᵢ sec(Eᵢ,ċ)` (`ricciCurvature_eq_sum_sectionalCurvature`
in `Ch03/RicciSectional.lean`, valid for the orthonormal frame) gives

$$\sum_{i=2}^n\frac{d^2E}{ds^2}\Big|_0
  = (n-1)\Big(\frac\pi l\Big)^2\frac l2 - \int_0^l\sin^2\!\Big(\frac\pi lt\Big)\operatorname{Ric}(\dot c,\dot c)\,dt
  < (n-1)\frac l2\Big(\big(\tfrac\pi l\big)^2 - k\Big) < 0 ,$$

so **at least one** `Vᵢ` yields a strictly negative second variation.

## Contents

* `bonnetSynge_secondVariation_eq` — the per-field **value** of the second variation of energy
  for the Bonnet–Synge field `V = sin(π·/l) E`, extracted from the 6.3.1 computation:
  `d²E/ds²|₀ = (π/l)²·(l/2) − ∫₀ˡ sin²(π·/l)·sec(E,ċ)`.  (6.3.1 only needed its sign; Myers
  needs the value, to sum over the frame.)
* `myers_index_core` — the **summed scalar index inequality**: for `m ≥ 1` weights `κᵢ` whose
  pointwise sum is `≥ m·k` on `[0,l]`, the sum of the `m` index expressions
  `(π/l)²(l/2) − ∫₀ˡ sin²·κᵢ` is strictly negative (pure analysis; the Ricci trace enters as
  `∑ᵢ κᵢ = Ric`).
* `myersRicci_secondVariation_neg` — **Myers' second-variation core** (the honest analytic
  content of Thm. 6.3.3): given the parallel orthonormal frame data and the Ricci lower bound
  in frame-sum form, some perpendicular field gives a strictly negative second variation.

## Honest scope

As with Lemma 6.3.1 (`bonnetSynge_longGeodesicsNotMinimizing`), the variations and their joint
slab-smoothness, the frame's parallelism/orthonormality, and integrability all enter as
hypotheses; what is *proven* is Petersen's curvature computation feeding the scalar core.  The
Ricci lower bound is carried in its frame-sum form `(n-1)k ≤ ∑ᵢ sec(Eᵢ,ċ)`, which equals
`Ric(ċ,ċ) ≥ (n-1)k` for the orthonormal frame by `ricciCurvature_eq_sum_sectionalCurvature`.
The passage from "some second variation is negative" through non-minimality to the diameter
bound is supplied in `Ch06/DiameterBound.lean`.  The topological implication from a compact
simply connected cover to finite `π₁` is supplied in `Ch06/MyersFundamentalGroup.lean`;
constructing that universal Riemannian cover and transferring the geometric hypotheses remain
separate open inputs.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval Real

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** The **value** of the second variation of energy for the Bonnet–Synge field
`V(t) = sin(π t/l) E(t)` (`E` a unit parallel field ⟂ the unit-speed geodesic base):

$$\frac{d^2E}{ds^2}\Big|_0
  = \Big(\frac\pi l\Big)^2\frac l2 - \int_0^l\sin^2\!\Big(\frac\pi lt\Big)\sec(E,\dot c)\,dt .$$

This is the computation of Lemma 6.3.1 (`bonnetSynge_longGeodesicsNotMinimizing`) stopped one
step early — before the sign is read off — so Myers' theorem can sum it over a frame.  Same
honest hypotheses as 6.3.1 (see that theorem / the module docstring). -/
theorem bonnetSynge_secondVariation_eq
    (g : RiemannianMetric I M) {l : ℝ} (hl : 0 < l)
    {f : ℝ → ℝ → M} {δ a b : ℝ} (hδ : 0 < δ)
    (hsub : Set.Icc (0 : ℝ) l ⊆ Set.Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b))
    (hgeo : ∀ t ∈ Set.Icc (0 : ℝ) l, curveAcceleration (I := I) g (f 0) t = 0)
    (hfix₀ : ∀ s, f s 0 = f 0 0) (hfixl : ∀ s, f s l = f 0 l)
    {Efield : ∀ t, TangentSpace I (f 0 t)}
    (hEpar : IsParallelAlong (I := I) g (f 0) Efield)
    (hEdiff : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) (f 0) (f 0 t) Efield) t)
    (hEunit : ∀ t, g.metricInner (f 0 t) (Efield t) (Efield t) = 1)
    (hEperp : ∀ t, g.metricInner (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t) = 0)
    (hspeed : ∀ t, g.metricInner (f 0 t) (curveVelocity (I := I) (f 0) t)
      (curveVelocity (I := I) (f 0) t) = 1)
    (hVfield : variationField (I := I) f = fun t => Real.sin (π / l * t) • Efield t)
    (hint : IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 *
        sectionalCurvature (g.leviCivita) (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t))
        volume 0 l) :
    deriv (deriv (fun s : ℝ => energyFunctional (I := I) g (f s) 0 l)) 0
      = (π / l) ^ 2 * (l / 2)
        - ∫ t in (0:ℝ)..l, Real.sin (π / l * t) ^ 2 *
            sectionalCurvature (g.leviCivita) (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t) := by
  have hHD := secondVariationEnergy_properVariation (I := I) g hδ hl hsub hf hgeo hfix₀ hfixl
  rw [hHD.deriv]
  rw [intervalIntegral.integral_congr
      (fun t _ => bonnetSynge_variation_integrand g hEpar hEdiff hEunit hEperp hspeed hVfield t)]
  have hcos_int : IntervalIntegrable
      (fun t => (π / l) ^ 2 * Real.cos (π / l * t) ^ 2) volume 0 l :=
    (by fun_prop : Continuous fun t => (π / l) ^ 2 * Real.cos (π / l * t) ^ 2).intervalIntegrable 0 l
  rw [intervalIntegral.integral_sub hcos_int hint, intervalIntegral.integral_const_mul,
    integral_cos_sq_window hl]

/-- **Math.** Segment-local form of `bonnetSynge_secondVariation_eq`.
Parallelism, regularity, orthonormality, perpendicularity, and unit speed are
needed only on the interval of integration.  This is the natural interface for
a parallel field constructed on an open neighborhood of `[0,l]`. -/
theorem bonnetSynge_secondVariation_eq_on_segment
    (g : RiemannianMetric I M) {l : ℝ} (hl : 0 < l)
    {f : ℝ → ℝ → M} {δ a b : ℝ} (hδ : 0 < δ)
    (hsub : Set.Icc (0 : ℝ) l ⊆ Set.Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b))
    (hgeo : ∀ t ∈ Set.Icc (0 : ℝ) l, curveAcceleration (I := I) g (f 0) t = 0)
    (hfix₀ : ∀ s, f s 0 = f 0 0) (hfixl : ∀ s, f s l = f 0 l)
    {Efield : ∀ t, TangentSpace I (f 0 t)}
    (hEpar : ∀ t ∈ Set.Icc (0 : ℝ) l,
      derivAlongCurve (I := I) g (f 0) Efield t = 0)
    (hEdiff : ∀ t ∈ Set.Icc (0 : ℝ) l,
      DifferentiableAt ℝ (chartFieldRep (I := I) (f 0) (f 0 t) Efield) t)
    (hEunit : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (Efield t) (Efield t) = 1)
    (hEperp : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t) = 0)
    (hspeed : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (curveVelocity (I := I) (f 0) t)
        (curveVelocity (I := I) (f 0) t) = 1)
    (hVfield : variationField (I := I) f = fun t => Real.sin (π / l * t) • Efield t)
    (hint : IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 *
        sectionalCurvature (g.leviCivita) (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t))
        volume 0 l) :
    deriv (deriv (fun s : ℝ => energyFunctional (I := I) g (f s) 0 l)) 0
      = (π / l) ^ 2 * (l / 2)
        - ∫ t in (0 : ℝ)..l, Real.sin (π / l * t) ^ 2 *
            sectionalCurvature (g.leviCivita) (f 0 t) (Efield t)
              (curveVelocity (I := I) (f 0) t) := by
  have hHD := secondVariationEnergy_properVariation (I := I) g hδ hl hsub hf hgeo hfix₀ hfixl
  rw [hHD.deriv]
  have hcongr : (∫ t in (0 : ℝ)..l,
      (g.inner (f 0 t) (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
          (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
        - g.inner (f 0 t)
            (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
              (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
              (curveVelocity (I := I) (f 0) t))
            (variationField (I := I) f t))) =
      ∫ t in (0 : ℝ)..l, ((π / l) ^ 2 * Real.cos (π / l * t) ^ 2
        - Real.sin (π / l * t) ^ 2 *
            sectionalCurvature (g.leviCivita) (f 0 t) (Efield t)
              (curveVelocity (I := I) (f 0) t)) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have ht' : t ∈ Set.Icc (0 : ℝ) l := by
      simpa only [Set.uIcc_of_le hl.le] using ht
    exact bonnetSynge_variation_integrand_at g hVfield t (hEpar t ht') (hEdiff t ht')
      (hEunit t ht') (hEperp t ht') (hspeed t ht')
  rw [hcongr]
  have hcos_int : IntervalIntegrable
      (fun t => (π / l) ^ 2 * Real.cos (π / l * t) ^ 2) volume 0 l :=
    (by fun_prop : Continuous fun t => (π / l) ^ 2 * Real.cos (π / l * t) ^ 2).intervalIntegrable 0 l
  rw [intervalIntegral.integral_sub hcos_int hint, intervalIntegral.integral_const_mul,
    integral_cos_sq_window hl]

/-- **Math.** **The Myers index inequality (summed scalar core).**  For `k > 0`, `l > π/√k`,
a nonempty finite family of weights `κᵢ` (`i ∈ s`) with `sin²(π·/l)·κᵢ` integrable, whose
pointwise sum satisfies `∑ᵢ κᵢ(t) ≥ (#s)·k` on `[0,l]`,

$$\sum_{i\in s}\Big[\Big(\frac\pi l\Big)^2\frac l2 - \int_0^l\sin^2\!\Big(\frac\pi lt\Big)\kappa_i\Big] < 0 .$$

In Myers' theorem `∑ᵢ κᵢ = Ric(ċ,ċ) ≥ (n-1)k` and `#s = n-1`.

**Proof.**  Sum splits as `(#s)(π/l)²(l/2) − ∑ᵢ∫sin²κᵢ`; pulling the finite sum inside the
integral and bounding `∑ᵢκᵢ ≥ (#s)k` gives `∑ᵢ∫sin²κᵢ ≥ (#s)k·(l/2)`; with `(π/l)² < k` and
`#s > 0` the whole thing is `< (#s)(l/2)((π/l)² − k) ≤ 0`. -/
theorem myers_index_core {l k : ℝ} (hl : 0 < l) (hk : 0 < k)
    (hlk : π / Real.sqrt k < l) {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {κ : ι → ℝ → ℝ}
    (hint : ∀ i ∈ s, IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 * κ i t) volume 0 l)
    (hsum : ∀ t ∈ Set.Icc (0:ℝ) l, (s.card : ℝ) * k ≤ ∑ i ∈ s, κ i t) :
    ∑ i ∈ s, ((π / l) ^ 2 * (l / 2)
        - ∫ t in (0:ℝ)..l, Real.sin (π / l * t) ^ 2 * κ i t) < 0 := by
  have hpisq : (π / l) ^ 2 < k := sq_pi_div_lt_of_pi_div_sqrt_lt hl hk hlk
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  -- Sum splits into the constant part minus the sum of integrals.
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  -- ∑ᵢ ∫ sin²κᵢ = ∫ sin²(∑ᵢκᵢ)
  have hswap : ∑ i ∈ s, (∫ t in (0:ℝ)..l, Real.sin (π / l * t) ^ 2 * κ i t)
      = ∫ t in (0:ℝ)..l, ∑ i ∈ s, Real.sin (π / l * t) ^ 2 * κ i t :=
    (intervalIntegral.integral_finsetSum hint).symm
  rw [hswap]
  -- lower bound the integrand by `sin² · (#s)·k`
  have hint_sum : IntervalIntegrable
      (fun t => ∑ i ∈ s, Real.sin (π / l * t) ^ 2 * κ i t) volume 0 l := by
    have h := IntervalIntegrable.sum s hint
    have heq : (∑ i ∈ s, fun t => Real.sin (π / l * t) ^ 2 * κ i t)
        = fun t => ∑ i ∈ s, Real.sin (π / l * t) ^ 2 * κ i t := by
      funext t; simp only [Finset.sum_apply]
    rwa [heq] at h
  have hlow_int : IntervalIntegrable
      (fun t => Real.sin (π / l * t) ^ 2 * ((s.card : ℝ) * k)) volume 0 l :=
    (by fun_prop : Continuous fun t => Real.sin (π / l * t) ^ 2 * ((s.card : ℝ) * k)).intervalIntegrable 0 l
  have hmono : (∫ t in (0:ℝ)..l, Real.sin (π / l * t) ^ 2 * ((s.card : ℝ) * k))
      ≤ ∫ t in (0:ℝ)..l, ∑ i ∈ s, Real.sin (π / l * t) ^ 2 * κ i t := by
    apply intervalIntegral.integral_mono_on hl.le hlow_int hint_sum
    intro t ht
    rw [← Finset.mul_sum]
    have hs2 : 0 ≤ Real.sin (π / l * t) ^ 2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_left (hsum t ht) hs2
  have hval : (∫ t in (0:ℝ)..l, Real.sin (π / l * t) ^ 2 * ((s.card : ℝ) * k))
      = (s.card : ℝ) * (k * (l / 2)) := by
    rw [intervalIntegral.integral_mul_const, integral_sin_sq_window hl]; ring
  rw [hval] at hmono
  have hstep : (s.card : ℝ) * ((π / l) ^ 2 * (l / 2)) < (s.card : ℝ) * (k * (l / 2)) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hpisq (by linarith : (0:ℝ) < l / 2)) hcard
  linarith [hmono, hstep]

/-- **Math.** Petersen §6.3, **Myers' theorem 6.3.3** (Myers 1941), analytic core: under the
Ricci bound `Ric(ċ,ċ) ≥ (n-1)k > 0` and `l > π/√k`, some perpendicular parallel field gives a
**strictly negative second variation** of energy — so the geodesic `c` is not locally
minimizing.

Petersen's proof: extend `ċ(0)=E₁` to a `g`-orthonormal frame and take the `m = n-1`
perpendicular fields `Vᵢ(t)=sin(π t/l)Eᵢ(t)`.  Each has second variation
`(π/l)²(l/2) − ∫sin²·sec(Eᵢ,ċ)` (`bonnetSynge_secondVariation_eq`); summing and using
`∑ᵢ sec(Eᵢ,ċ) = Ric(ċ,ċ) ≥ (n-1)k` (`ricciCurvature_eq_sum_sectionalCurvature`, valid for the
orthonormal frame) makes the total `< 0` (`myers_index_core`), so at least one `Vᵢ` is `< 0`.

The Ricci bound is carried in its frame-sum form `(m)k ≤ ∑ᵢ sec(Eᵢ,ċ)` with `m = n-1`; this
equals `Ric(ċ,ċ) ≥ (n-1)k` for the orthonormal frame.  As in Lemma 6.3.1, the variations, their
slab-smoothness, the frame's parallelism/orthonormality, and the integrability are hypotheses;
the passage to the *diameter* bound / finite `π₁` needs the same not-minimizing bridge that
gates Cor. 6.3.2.  See the module docstring. -/
theorem myersRicci_secondVariation_neg
    (g : RiemannianMetric I M) {l k : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hk : 0 < k) (hlk : π / Real.sqrt k < l)
    (V : Fin m → ℝ → ℝ → M) {δ a b : ℝ} (hδ : 0 < δ)
    (hsub : Set.Icc (0 : ℝ) l ⊆ Set.Ioo a b)
    (hf : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry (V i))
      (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b))
    (hgeo : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) l, curveAcceleration (I := I) g (V i 0) t = 0)
    (hfix₀ : ∀ i, ∀ s, V i s 0 = V i 0 0) (hfixl : ∀ i, ∀ s, V i s l = V i 0 l)
    (Efield : ∀ i : Fin m, ∀ t, TangentSpace I (V i 0 t))
    (hEpar : ∀ i, IsParallelAlong (I := I) g (V i 0) (Efield i))
    (hEdiff : ∀ i, ∀ t,
      DifferentiableAt ℝ (chartFieldRep (I := I) (V i 0) (V i 0 t) (Efield i)) t)
    (hEunit : ∀ i, ∀ t, g.metricInner (V i 0 t) (Efield i t) (Efield i t) = 1)
    (hEperp : ∀ i, ∀ t,
      g.metricInner (V i 0 t) (Efield i t) (curveVelocity (I := I) (V i 0) t) = 0)
    (hspeed : ∀ i, ∀ t, g.metricInner (V i 0 t) (curveVelocity (I := I) (V i 0) t)
      (curveVelocity (I := I) (V i 0) t) = 1)
    (hVfield : ∀ i, variationField (I := I) (V i) = fun t => Real.sin (π / l * t) • Efield i t)
    (hint : ∀ i, IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 *
        sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t)
          (curveVelocity (I := I) (V i 0) t)) volume 0 l)
    (hRic : ∀ t ∈ Set.Icc (0:ℝ) l, (m : ℝ) * k ≤
        ∑ i, sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t)
          (curveVelocity (I := I) (V i 0) t)) :
    ∃ i : Fin m, deriv (deriv (fun s : ℝ => energyFunctional (I := I) g (V i s) 0 l)) 0 < 0 := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hl : 0 < l := lt_trans (div_pos Real.pi_pos hsk) hlk
  -- the per-direction second-variation value
  have hval : ∀ i, deriv (deriv (fun s : ℝ => energyFunctional (I := I) g (V i s) 0 l)) 0
      = (π / l) ^ 2 * (l / 2)
        - ∫ t in (0:ℝ)..l, Real.sin (π / l * t) ^ 2 *
            sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t)
              (curveVelocity (I := I) (V i 0) t) := fun i =>
    bonnetSynge_secondVariation_eq g hl hδ hsub (hf i) (hgeo i) (hfix₀ i) (hfixl i)
      (hEpar i) (hEdiff i) (hEunit i) (hEperp i) (hspeed i) (hVfield i) (hint i)
  -- the total second variation over the frame is strictly negative
  have hcard : (Finset.univ : Finset (Fin m)).card = m := by simp
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; omega)
  have hsum_neg :
      ∑ i, deriv (deriv (fun s : ℝ => energyFunctional (I := I) g (V i s) 0 l)) 0 < 0 := by
    have hEq : ∑ i, deriv (deriv (fun s : ℝ => energyFunctional (I := I) g (V i s) 0 l)) 0
        = ∑ i : Fin m, ((π / l) ^ 2 * (l / 2)
            - ∫ t in (0:ℝ)..l, Real.sin (π / l * t) ^ 2 *
                sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t)
                  (curveVelocity (I := I) (V i 0) t)) :=
      Finset.sum_congr rfl fun i _ => hval i
    rw [hEq]
    refine myers_index_core hl hk hlk Finset.univ hne (fun i _ => hint i) ?_
    intro t ht
    rw [hcard]
    exact hRic t ht
  -- hence some direction has a negative second variation
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have hnonneg : 0 ≤ ∑ i, deriv (deriv (fun s : ℝ => energyFunctional (I := I) g (V i s) 0 l)) 0 :=
    Finset.sum_nonneg fun i _ => hcon i
  linarith

end PetersenLib
