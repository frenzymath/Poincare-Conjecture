import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge
import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
# Norm-expanding maps expand length (do Carmo Ch. 7, §3, Lemma 3.3, metric core)

do Carmo's proof of Lemma 3.3 (a local diffeomorphism `f : M → N` out of a
complete manifold with `|df_p(v)| ≥ |v|` everywhere is a covering map) rests on
one metric estimate, displayed in the proof:
$$
  \ell_{0,t}(c)=\int_0^t\Big|\frac{dc}{dt}\Big|\,dt
      =\int_0^t\Big|df_{\bar c(t)}\Big(\frac{d\bar c}{dt}\Big)\Big|\,dt
      \ \ge\ \int_0^t\Big|\frac{d\bar c}{dt}\Big|\,dt\ \ge\ d(\bar c(t),\bar c(0)).
$$
Reading it forward (for `c = f ∘ \bar c`): a map whose differential never
shrinks a tangent vector never shrinks the length of a curve, and the length of
the *source* curve dominates the source distance between its endpoints. This is
the estimate that, in the covering-map argument, keeps the lifted points
`\bar c(t_n)` inside a bounded — hence (by Hopf–Rinow) relatively compact — set.

This file isolates that estimate as reusable infrastructure:

* `DCExpandsMetric gM gN f` — the hypothesis `|df_p(v)| ≥ |v|` in squared form
  `⟨v,v⟩_{gM} ≤ ⟨df_p v, df_p v⟩_{gN}`.
* `DCExpandsMetric.enorm_mfderiv_le` — its pointwise fibre-enorm reading
  `‖v‖ₑ ≤ ‖df_p v‖ₑ`.
* `DCExpandsMetric.pathELength_le` — length expansion:
  `ℓ(c) ≤ ℓ(f ∘ c)` for every `C¹` curve `c`.
* `DCExpandsMetric.riemannianEDist_le_pathELength_comp` — the full displayed
  chain: `d(c a, c b) ≤ ℓ(f ∘ c)`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §3, proof of Lemma 3.3.
-/

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** do Carmo Ch. 7, Lemma 3.3 hypothesis: `f : M → M'` **expands the
metric**, i.e. `|df_p(v)| ≥ |v|` for all `p` and `v`. Stated in squared form
`⟨v, v⟩_{gM} ≤ ⟨df_p v, df_p v⟩_{gN}`, which is equivalent (both sides are
non-negative) and avoids square roots. A local isometry (`DCPreservesMetric`)
is in particular a metric-expander. -/
def DCExpandsMetric (gM : RiemannianMetric I M) (gN : RiemannianMetric I' M')
    (f : M → M') : Prop :=
  ∀ (p : M) (v : TangentSpace I p),
    gM.metricInner p v v ≤
      gN.metricInner (f p) (mfderiv I I' f p v) (mfderiv I I' f p v)

/-- **Math.** A metric-preserving map (do Carmo Def. 2.2) is in particular a
metric-expander: equality of the inner products implies `≤`. -/
theorem DCPreservesMetric.dcExpandsMetric {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {f : M → M'} (h : DCPreservesMetric gM gN f) :
    DCExpandsMetric gM gN f :=
  fun p v => (h p v v).le

/-- **Math.** The pointwise fibre-enorm reading of `DCExpandsMetric`: under the
Riemannian-bundle instances of `gM` and `gN`, `‖v‖ₑ ≤ ‖df_p v‖ₑ`. This is do
Carmo's `|df_p(v)| ≥ |v|` in the language `Manifold.pathELength` integrates. -/
theorem DCExpandsMetric.enorm_mfderiv_le {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {f : M → M'} (hexp : DCExpandsMetric gM gN f)
    (p : M) (v : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨gM.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
      ⟨gN.toRiemannianMetric⟩
    ‖v‖ₑ ≤ ‖mfderiv I I' f p v‖ₑ := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨gM.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  rw [enorm_tangent_eq_sqrt_metricInner gM p v,
    enorm_tangent_eq_sqrt_metricInner gN (f p) (mfderiv I I' f p v)]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hexp p v))

/-- **Math.** **Length expansion** (do Carmo Ch. 7, proof of Lemma 3.3). If `f`
expands the metric and `c : [a, b] → M` is `C¹`, then the length of `c` is at
most the length of `f ∘ c`:
`ℓ(c) ≤ ℓ(f ∘ c)`. Reading `c` as the *lift* `\bar c` and `f ∘ c` as the base
curve, this is `ℓ(f∘\bar c) ≥ ℓ(\bar c)`. Proof: both lengths are the tangent
integrals `∫ ‖γ'‖ₑ`; the integrands are compared pointwise by the chain rule
`(f∘c)' = df(c')` and the expansion bound `‖c'‖ₑ ≤ ‖df(c')‖ₑ`
(`enorm_mfderiv_le`), and `∫⁻` is monotone. -/
theorem DCExpandsMetric.pathELength_le {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {f : M → M'} (hexp : DCExpandsMetric gM gN f)
    (hf : MDifferentiable I I' f) {c : ℝ → M} {a b : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b)) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨gM.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
      ⟨gN.toRiemannianMetric⟩
    Manifold.pathELength I c a b ≤ Manifold.pathELength I' (f ∘ c) a b := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨gM.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  refine MeasureTheory.lintegral_mono_ae ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall fun t ht => ?_)
  -- differentiability of `c` at the interior time `t`
  have hct : MDifferentiableAt 𝓘(ℝ, ℝ) I c t :=
    ((hc t (Ioo_subset_Icc_self ht)).contMDiffAt
      (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  -- chain rule: the velocity of `f ∘ c` is `df` of the velocity of `c`
  have hchain : mfderiv 𝓘(ℝ, ℝ) I' (f ∘ c) t 1
      = mfderiv I I' f (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1) :=
    DCVelocity_comp t (hf (c t)) hct
  rw [hchain]
  exact hexp.enorm_mfderiv_le (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1)

/-- **Math.** **The displayed estimate** of do Carmo Ch. 7, Lemma 3.3 proof, in
full: for a `C¹` curve `c : [a, b] → M` and a metric-expander `f`, the *source*
Riemannian distance between the endpoints is bounded by the length of the image
curve `f ∘ c`:
`d(c a, c b) ≤ ℓ(f ∘ c)`. This is the inequality
`d(\bar c(t), \bar c(0)) ≤ \ell_{0,t}(c)` that forces a lift with bounded image.
Proof: `d(c a, c b) ≤ ℓ(c) ≤ ℓ(f ∘ c)`, the first step
`riemannianEDist_le_pathELength` and the second `pathELength_le`. -/
theorem DCExpandsMetric.riemannianEDist_le_pathELength_comp
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hf : MDifferentiable I I' f)
    {c : ℝ → M} {a b : ℝ} (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b)) (hab : a ≤ b) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨gM.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
      ⟨gN.toRiemannianMetric⟩
    Manifold.riemannianEDist I (c a) (c b) ≤ Manifold.pathELength I' (f ∘ c) a b := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨gM.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  exact le_trans (Manifold.riemannianEDist_le_pathELength hc rfl rfl hab)
    (hexp.pathELength_le hf hc)

end Riemannian
