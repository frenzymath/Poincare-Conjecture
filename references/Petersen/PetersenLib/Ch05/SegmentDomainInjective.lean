import PetersenLib.Ch05.SegmentDomain
import PetersenLib.Ch05.EnergyMinimizers
import PetersenLib.Ch05.MetricTopology
import PetersenLib.Ch05.PiecewiseArclength
import PetersenLib.Riemannian.Exponential.RayGeodesic
import PetersenLib.Riemannian.Geodesic.IntrinsicUniqueness

/-!
# Petersen Ch. 5, §5.7.3 — `exp_p` is injective on the star interior `seg⁰(p)`

Petersen's Proposition 5.7.7 (`prop:pet-ch5-segment-domain-injective`): a point of
`exp_p(seg⁰(p))` is joined to `p` by a *unique* segment; in particular `exp_p` is
injective on `seg⁰(p)`.

This file provides, in the order the argument needs them:

* `IsSegment.comp_mul_of_pos` — a segment on `[0, b]`, `b > 0`, normalizes to a
  segment on `[0, 1]` under `t ↦ b t`.  This is what makes "unique segment"
  independent of the parameter interval.
* `segmentDomainStarInterior_subset_segmentDomain` — `seg⁰(p) ⊆ seg(p)`, i.e. every
  star-interior vector `v` has `t ↦ exp_p(t v)` a segment on `[0, 1]` (EXISTENCE of
  the joining segment).  The proof is the triangle squeeze
  `k = |p σ(1)| ≤ |p σ(s)| + |σ(s) σ(1)| ≤ k s + (k - k s) = k`.
* `eq_of_expMap_ray_eqOn` — two exponential rays from `p` that agree on `[0, 1]`
  have the same initial velocity.
* `segment_eq_expMap_ray_of_mem_segmentDomainStarInterior` — UNIQUENESS on `[0, 1]`:
  *every* segment `τ` on `[0, 1]` from `p` to `exp_p(v)`, `v ∈ seg⁰(p)`, is the ray
  `t ↦ exp_p(t v)`.
* `segment_eq_expMap_ray_of_mem_segmentDomainStarInterior'` — UNIQUENESS on an
  arbitrary `[0, b]`, the form matching Petersen's own proof (which glues a
  competitor defined on a shorter interval).
* `expMap_injectiveOnSegmentDomainStarInterior` — the headline `Set.InjOn`.

The argument never differentiates `exp_p` away from `0`: this is why 5.7.7 lands
while its siblings do not.  It does NOT provide Lemma 5.7.8 (nonsingularity of
`D exp_p` on `seg⁰(p)`, which needs a Hessian/Jacobi layer that does not exist in
`PetersenLib/Ch05`), Lemma 5.7.9 (the cut-locus characterization, which needs a
global `D exp_p` and a "every segment is an exponential ray" velocity bridge),
Prop. 5.7.10 (openness of `seg⁰(p)`) or Cor. 5.7.11 (smoothness of `r` up to the
cut point) — all three are downstream of 5.7.8/5.7.9.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

open PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]
  [T2Space M] [ConnectedSpace M]

variable {g : RiemannianMetric I M} {p : M}

/-! ## Normalizing a segment's parameter interval to `[0, 1]` -/

/-- **Math.** A segment on `[0, b]`, `b > 0`, affinely reparametrized to `[0, 1]` by
`t ↦ b t`, is again a segment: piecewise smoothness, the length–distance equality
and the proportional-to-arclength clause are all invariant, the speed constant
scaling from `k` to `k b`.

This is what makes "the segment from `p` to `x` is unique" independent of the
choice of parameter interval: every segment from `p` to `x`, on whatever `[0, b]`,
normalizes to one on `[0, 1]`. -/
theorem IsSegment.comp_mul_of_pos {γ : ℝ → M} {b : ℝ} (hb : 0 < b)
    (hγ : IsSegment (I := I) g γ 0 b) :
    IsSegment (I := I) g (fun t : ℝ => γ (b * t)) 0 1 := by
  obtain ⟨hpw, hLd, k, hk, hprop⟩ := hγ
  have hEq : ∀ x ∈ Icc (0:ℝ) 1, (fun t : ℝ => γ (b * t)) x = (fun r : ℝ => γ (b * r + 0)) x := by
    intro x _
    show γ (b * x) = γ (b * x + 0)
    rw [add_zero]
  have hpw0 : IsPiecewiseSmoothCurve (I := I) (fun r : ℝ => γ (b * r + 0)) 0 1 := by
    refine isPiecewiseSmoothCurve_comp_mul_add (I := I) hb ?_
    simpa using hpw
  have hpw' : IsPiecewiseSmoothCurve (I := I) (fun t : ℝ => γ (b * t)) 0 1 := hpw0.congr hEq
  have hlen : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      curveLength (I := I) g (fun t : ℝ => γ (b * t)) 0 t
        = curveLength (I := I) g γ 0 (b * t) := by
    intro t ht0 ht1
    rw [curveLength_congr_Icc (I := I) g (a := 0) (b := 1) hEq ⟨le_rfl, zero_le_one⟩ ⟨ht0, ht1⟩,
      curveLength_comp_mul_add (I := I) g γ hb.le 0 0 t]
    simp only [mul_zero, add_zero]
  refine ⟨hpw', ?_, k * b, by positivity, fun t ht => ?_⟩
  · rw [hlen 1 zero_le_one le_rfl, mul_one]
    show curveLength (I := I) g γ 0 b
      = riemannianDistance (I := I) g (γ (b * 0)) (γ (b * 1))
    rw [mul_zero, mul_one]
    exact hLd
  · rw [hlen t ht.1 ht.2,
      hprop (b * t) ⟨mul_nonneg hb.le ht.1, by nlinarith [ht.2, hb]⟩]
    ring

/-! ## The star interior sits inside the segment domain -/

/-- **Math.** Petersen Ch. 5, Prop. 5.7.7 (the triangle squeeze).  If `w ∈ seg(p)`
and `s ∈ [0, 1)`, the *initial sub-ray* of `σ(t) = exp_p(t w)` up to time `s` is
already minimizing: `|p exp_p(s w)| = L(σ)|₀ˢ`.

This is the heart of the proposition.  Writing `k` for `σ`'s speed, the affine
reparametrizations `σ(s ⬝)` and `σ((1-s) ⬝ + s)` are competitors joining `p` to
`σ(s)` and `σ(s)` to `σ(1)`, of lengths `k s` and `k - k s`.  The triangle
inequality then squeezes
`k = |p σ(1)| ≤ |p σ(s)| + |σ(s) σ(1)| ≤ k s + (k - k s) = k`,
so both inequalities are equalities and in particular `|p σ(s)| = k s = L(σ)|₀ˢ`. -/
private theorem riemannianDistance_expMap_smul_eq_curveLength {w : TangentSpace I p}
    (hw : w ∈ segmentDomain (I := I) g p) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    riemannianDistance (I := I) g p (expMap (I := I) g p (s • w))
      = curveLength (I := I) g (fun t => expMap (I := I) g p (t • w)) 0 s := by
  obtain ⟨hpw, hLd, k, hk, hprop⟩ := hw
  set σ : ℝ → M := fun t => expMap (I := I) g p (t • w) with hσ
  have hσ0 : σ 0 = p := by
    show expMap (I := I) g p ((0:ℝ) • w) = p
    rw [zero_smul]; exact expMap_zero g p
  show riemannianDistance (I := I) g p (σ s) = curveLength (I := I) g σ 0 s
  rw [hprop s ⟨hs0, hs1.le⟩]
  have hleftpw : IsPiecewiseSmoothCurve (I := I) (fun r : ℝ => σ (s * r + 0)) 0 1 := by
    rcases hs0.eq_or_lt with rfl | hspos
    · refine (isPiecewiseSmoothCurve_const (I := I) (σ 0) zero_le_one).congr ?_
      intro r _; norm_num
    · refine isPiecewiseSmoothCurve_comp_mul_add (I := I) hspos ?_
      simpa using hpw.mono (I := I) le_rfl hs0 hs1.le
  have hlen_left : curveLength (I := I) g (fun r : ℝ => σ (s * r + 0)) 0 1 = k * s := by
    rw [curveLength_comp_mul_add (I := I) g σ hs0 0 0 1]
    simp only [mul_zero, add_zero, mul_one]
    rw [hprop s ⟨hs0, hs1.le⟩]; ring
  have hrightpw : IsPiecewiseSmoothCurve (I := I) (fun r : ℝ => σ ((1 - s) * r + s)) 0 1 := by
    refine isPiecewiseSmoothCurve_comp_mul_add (I := I) (by linarith : (0:ℝ) < 1 - s) ?_
    simpa using hpw.mono (I := I) hs0 hs1.le le_rfl
  have hlen_right : curveLength (I := I) g (fun r : ℝ => σ ((1 - s) * r + s)) 0 1
      = k - k * s := by
    rw [curveLength_comp_mul_add (I := I) g σ (by linarith : (0:ℝ) ≤ 1 - s) s 0 1]
    simp only [mul_zero, zero_add, mul_one]
    have hsplit := hpw.curveLength_add (I := I) g hs0 hs1.le
    have h1 := hprop 1 (by norm_num)
    have h2 := hprop s ⟨hs0, hs1.le⟩
    have he : (1 : ℝ) - s + s = 1 := by ring
    rw [he]
    rw [h1] at hsplit; rw [h2] at hsplit
    linarith [hsplit]
  have hk1 : curveLength (I := I) g σ 0 1 = k := by rw [hprop 1 (by norm_num)]; ring
  have hd1 : riemannianDistance (I := I) g p (σ 1) = k := by rw [← hσ0, ← hLd, hk1]
  have hdle_left : riemannianDistance (I := I) g p (σ s) ≤ k * s := by
    have := riemannianDistance_le_curveLength (I := I) g (p := p) (q := σ s) hleftpw
      (by show σ (s * 0 + 0) = p; rw [mul_zero, add_zero]; exact hσ0)
      (by show σ (s * 1 + 0) = σ s; rw [mul_one, add_zero])
    rwa [hlen_left] at this
  have hdle_right : riemannianDistance (I := I) g (σ s) (σ 1) ≤ k - k * s := by
    have := riemannianDistance_le_curveLength (I := I) g (p := σ s) (q := σ 1) hrightpw
      (by show σ ((1 - s) * 0 + s) = σ s; rw [mul_zero, zero_add])
      (by show σ ((1 - s) * 1 + s) = σ 1; rw [mul_one]; ring_nf)
    rwa [hlen_right] at this
  have htri := riemannianDistance_triangle (I := I) g p (σ s) (σ 1)
    ⟨fun r : ℝ => σ (s * r + 0), hleftpw,
      (by show σ (s * 0 + 0) = p; rw [mul_zero, add_zero]; exact hσ0),
      (by show σ (s * 1 + 0) = σ s; rw [mul_one, add_zero])⟩
    ⟨fun r : ℝ => σ ((1 - s) * r + s), hrightpw,
      (by show σ ((1 - s) * 0 + s) = σ s; rw [mul_zero, zero_add]),
      (by show σ ((1 - s) * 1 + s) = σ 1; rw [mul_one]; ring_nf)⟩
  rw [hd1] at htri
  linarith

/-- **Math.** Petersen Ch. 5, Prop. 5.7.7 (existence clause): the star interior is
contained in the segment domain, `seg⁰(p) ⊆ seg(p)`.  Unwinding
`mem_segmentDomain_iff`, this says every `v = s w` with `s ∈ [0, 1)` and
`w ∈ seg(p)` has its own exponential ray `t ↦ exp_p(t v)` a segment on `[0, 1]`
from `p` to `exp_p(v)` — so every point of `exp_p(seg⁰(p))` *is* joined to `p` by
a segment.

The ray at `s w` is the affine reparametrization `σ(s ⬝)` of the ray at `w`; it is
piecewise smooth, has length `k s` proportional to time, and realizes
`|p σ(s)|` by `riemannianDistance_expMap_smul_eq_curveLength`. -/
theorem segmentDomainStarInterior_subset_segmentDomain :
    segmentDomainStarInterior (I := I) g p ⊆ segmentDomain (I := I) g p := by
  rintro v ⟨s, ⟨hs0, hs1⟩, w, hw, rfl⟩
  have hwseg := hw
  have hdps₀ := riemannianDistance_expMap_smul_eq_curveLength (I := I) hwseg hs0 hs1
  obtain ⟨hpw, hLd, k, hk, hprop⟩ := hw
  set σ : ℝ → M := fun t => expMap (I := I) g p (t • w) with hσ
  have hσ0 : σ 0 = p := by
    show expMap (I := I) g p ((0:ℝ) • w) = p
    rw [zero_smul]; exact expMap_zero g p
  have hcurve : (fun t : ℝ => expMap (I := I) g p (t • (s • w))) = fun t : ℝ => σ (s * t + 0) := by
    funext t; rw [hσ]; simp only [add_zero, smul_smul]; rw [mul_comm t s]
  show IsSegment (I := I) g (fun t : ℝ => expMap (I := I) g p (t • (s • w))) 0 1
  rw [hcurve]
  have hleftpw : IsPiecewiseSmoothCurve (I := I) (fun r : ℝ => σ (s * r + 0)) 0 1 := by
    rcases hs0.eq_or_lt with rfl | hspos
    · refine (isPiecewiseSmoothCurve_const (I := I) (σ 0) zero_le_one).congr ?_
      intro r _; norm_num
    · refine isPiecewiseSmoothCurve_comp_mul_add (I := I) hspos ?_
      simpa using hpw.mono (I := I) le_rfl hs0 hs1.le
  have hlen_left : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      curveLength (I := I) g (fun r : ℝ => σ (s * r + 0)) 0 t = k * (s * t) := by
    intro t ht0 ht1
    rw [curveLength_comp_mul_add (I := I) g σ hs0 0 0 t]
    simp only [mul_zero, add_zero]
    have := hprop (s * t) ⟨by positivity, by nlinarith⟩
    rw [this]; ring
  have hdeq : riemannianDistance (I := I) g p (σ s) = k * s := by
    show riemannianDistance (I := I) g p (σ s) = k * s
    rw [hdps₀, hprop s ⟨hs0, hs1.le⟩]; ring
  refine ⟨hleftpw, ?_, k * s, by positivity, fun t ht => ?_⟩
  · rw [hlen_left 1 zero_le_one le_rfl]
    have h0 : (fun r : ℝ => σ (s * r + 0)) 0 = p := by
      show σ (s * 0 + 0) = p; rw [mul_zero, add_zero]; exact hσ0
    have h1 : (fun r : ℝ => σ (s * r + 0)) 1 = σ s := by
      show σ (s * 1 + 0) = σ s; rw [mul_one, add_zero]
    rw [h0, h1, hdeq]; ring
  · rw [hlen_left t ht.1 ht.2]; ring

/-! ## Exponential rays are determined by their initial velocity -/

/-- **Math.** Two exponential rays from `p` that agree on `[0, 1]` have the same
initial velocity: `t ↦ exp_p(t v)` has derivative `v` at `t = 0` (read in the
chart at `p`), and the derivative within `[0, 1]` at `0` is unique.

The rays are first rescaled by a `δ > 0` small enough to put `δ v₁, δ v₂` inside
the ball on which `exists_isGeodesicOn_expMap_ray` supplies the derivative;
homogeneity `t • (δ • v) = (t δ) • v` transports the hypothesis, and
`smul_right_injective` removes `δ` at the end. -/
theorem eq_of_expMap_ray_eqOn (g : RiemannianMetric I M) (p : M) {v₁ v₂ : E}
    (h : ∀ t ∈ Icc (0 : ℝ) 1,
      expMap (I := I) g p ((t • v₁ : E) : TangentSpace I p)
        = expMap (I := I) g p ((t • v₂ : E) : TangentSpace I p)) :
    v₁ = v₂ := by
  obtain ⟨ρ, b, hρ, hb, -, hray⟩ := Exponential.exists_isGeodesicOn_expMap_ray (I := I) g p
  set K : ℝ := ‖v₁‖ + ‖v₂‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  set δ : ℝ := min 1 (ρ / (2 * K)) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hbound : ∀ w : E, ‖w‖ ≤ K → ‖δ • w‖ < ρ := by
    intro w hw
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ0]
    calc δ * ‖w‖ ≤ (ρ / (2 * K)) * K :=
          mul_le_mul (min_le_right _ _) hw (norm_nonneg w) (by positivity)
      _ = ρ / 2 := by field_simp
      _ < ρ := by linarith
  have hδ₁ : ‖δ • v₁‖ < ρ := hbound v₁ (by simp only [hK]; nlinarith [norm_nonneg v₂])
  have hδ₂ : ‖δ • v₂‖ < ρ := hbound v₂ (by simp only [hK]; nlinarith [norm_nonneg v₁])
  have hd₁ := (hray (δ • v₁) hδ₁).2.1
  have hd₂ := (hray (δ • v₂) hδ₂).2.1
  have hagree : ∀ t ∈ Icc (0 : ℝ) 1,
      (fun t : ℝ => extChartAt I p (expMap (I := I) g p ((t • (δ • v₁) : E) : TangentSpace I p))) t
        = (fun t : ℝ => extChartAt I p
            (expMap (I := I) g p ((t • (δ • v₂) : E) : TangentSpace I p))) t := by
    intro t ht
    have hsm : ∀ w : E, (t • (δ • w) : E) = ((t * δ) • w : E) := fun w => by
      rw [smul_smul]
    simp only [hsm]
    rw [h (t * δ) ⟨by nlinarith [ht.1, hδ0.le], by nlinarith [ht.1, ht.2, hδ0.le]⟩]
  have hw₁ : HasDerivWithinAt
      (fun t : ℝ => extChartAt I p (expMap (I := I) g p ((t • (δ • v₁) : E) : TangentSpace I p)))
      (δ • v₁) (Icc (0:ℝ) 1) 0 := hd₁.hasDerivWithinAt
  have hw₂ : HasDerivWithinAt
      (fun t : ℝ => extChartAt I p (expMap (I := I) g p ((t • (δ • v₁) : E) : TangentSpace I p)))
      (δ • v₂) (Icc (0:ℝ) 1) 0 :=
    (hd₂.hasDerivWithinAt).congr hagree (hagree 0 (by norm_num))
  have huniq : UniqueDiffWithinAt ℝ (Icc (0:ℝ) 1) 0 :=
    uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1) 0 (by norm_num)
  have hEq : δ • v₁ = δ • v₂ := huniq.eq_deriv _ hw₁ hw₂
  exact smul_right_injective E hδ0.ne' hEq

/-! ## Uniqueness of the segment to a point of `exp_p(seg⁰(p))` -/

/-- **Math.** Petersen Ch. 5, Prop. 5.7.7 (uniqueness clause): if `v ∈ seg⁰(p)`,
then *every* segment `τ : [0, 1] → M` from `p` to `exp_p(v)` is the exponential
ray `t ↦ exp_p(t v)`.  Quantified over all competitors `τ`; no witness is
self-supplied.

**Proof (Petersen).**  Write `v = s w` with `s ∈ [0, 1)` and `w ∈ seg(p)`, and let
`σ(t) = exp_p(t w)` be the ambient segment, of speed `k`; it extends strictly past
`x = exp_p(v) = σ(s)`.  By the squeeze, `|p σ(s)| = k s`, so `τ` has speed `k s`.
Glue the competitor to the tail of `σ` *at time* `s`:
`c(t) = τ(t/s)` for `t ≤ s`, `c(t) = σ(t)` for `t > s`.
Then `L(c)|₀ᵗ = k t` throughout and `L(c)|₀¹ = k = |p σ(1)| = |c(0) c(1)|`, so `c`
is itself a segment, hence (Cor. 5.4.3) a geodesic on `(0, 1)`.  Now `c` and `σ`
agree on the open set `(s, 1)`, so they share position and chart velocity at
`a = (s+1)/2`; uniqueness of geodesics on the *preconnected* `(0, 1)` propagates
the agreement back across the corner at `s`, giving `EqOn c σ (0, 1)`.  Reading
this at `s t` gives `τ(t) = σ(s t) = exp_p(t v)`.  Note the corner of `c` is never
inspected — the preconnectedness of `(0,1)` does that work. -/
theorem segment_eq_expMap_ray_of_mem_segmentDomainStarInterior
    (g : RiemannianMetric I M) (p : M) {v : TangentSpace I p}
    (hv : v ∈ segmentDomainStarInterior (I := I) g p)
    {τ : ℝ → M} (hτ : IsSegment (I := I) g τ 0 1) (hτ0 : τ 0 = p)
    (hτ1 : τ 1 = expMap (I := I) g p v) :
    ∀ t ∈ Icc (0 : ℝ) 1, τ t = expMap (I := I) g p (t • v) := by
  obtain ⟨s, ⟨hs0, hs1⟩, w, hw, rfl⟩ := hv
  have hwseg := hw
  have hdps₀ := riemannianDistance_expMap_smul_eq_curveLength (I := I) hwseg hs0 hs1
  obtain ⟨hpw, hLd, k, hk, hprop⟩ := hw
  obtain ⟨hτpw, hτLd, kτ, hkτ, hτprop⟩ := hτ
  set σ : ℝ → M := fun t => expMap (I := I) g p (t • w) with hσ
  have hσ0 : σ 0 = p := by
    show expMap (I := I) g p ((0:ℝ) • w) = p
    rw [zero_smul]; exact expMap_zero g p
  have hray : ∀ t : ℝ, expMap (I := I) g p (t • (s • w)) = σ (s * t) := by
    intro t
    rw [hσ]
    show expMap (I := I) g p (t • (s • w)) = expMap (I := I) g p ((s * t) • w)
    rw [smul_smul, mul_comm t s]
  have hτ1' : τ 1 = σ s := by rw [hσ]; exact hτ1
  have hdps : riemannianDistance (I := I) g p (σ s) = k * s := by
    rw [hdps₀, hprop s ⟨hs0, hs1.le⟩]; ring
  -- the competitor's speed constant is forced to be `k s`
  have hkτeq : kτ = k * s := by
    have h1 := hτprop 1 (by norm_num)
    rw [hτLd, hτ0, hτ1', hdps] at h1
    linarith
  have hd1 : riemannianDistance (I := I) g p (σ 1) = k := by
    rw [← hσ0, ← hLd, hprop 1 (by norm_num)]; ring
  rcases hs0.eq_or_lt with rfl | hspos
  · -- `s = 0`: then `v = 0`, the competitor has zero length, so it is constant at `p`
    intro t ht
    have hv0 : ((t : ℝ) • (((0:ℝ) • w : TangentSpace I p)) : TangentSpace I p) = 0 := by
      rw [zero_smul, smul_zero]
    rw [hv0, expMap_zero]
    rcases ht.1.eq_or_lt with rfl | htpos
    · exact hτ0
    · have hlen0 : curveLength (I := I) g τ 0 t = 0 := by
        rw [hτprop t ht, hkτeq]; ring
      have hrep : IsPiecewiseSmoothCurve (I := I) (fun r : ℝ => τ (t * r + 0)) 0 1 := by
        refine isPiecewiseSmoothCurve_comp_mul_add (I := I) htpos ?_
        simpa using hτpw.mono (I := I) le_rfl ht.1 ht.2
      have hdle : riemannianDistance (I := I) g p (τ t) ≤ 0 := by
        have := riemannianDistance_le_curveLength (I := I) g (p := p) (q := τ t) hrep
          (by show τ (t * 0 + 0) = p; rw [mul_zero, add_zero]; exact hτ0)
          (by show τ (t * 1 + 0) = τ t; rw [mul_one, add_zero])
        rw [curveLength_comp_mul_add (I := I) g τ ht.1 0 0 1] at this
        simp only [mul_zero, add_zero, mul_one] at this
        rwa [hlen0] at this
      have hzero : riemannianDistance (I := I) g p (τ t) = 0 :=
        le_antisymm hdle (riemannianDistance_nonneg (I := I) g p (τ t))
      exact (eq_of_riemannianDistance_eq_zero (I := I) g hzero).symm
  · -- `0 < s`: glue the competitor to the tail of `σ` at time `s`
    have hsne : s ≠ 0 := hspos.ne'
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ → M, c = fun t => if t ≤ s then τ (t / s) else σ t := ⟨_, rfl⟩
    have hcval_le : ∀ t : ℝ, t ≤ s → c t = τ (t / s) := by
      intro t ht; rw [hcdef]; simp only; rw [if_pos ht]
    have hcval_gt : ∀ t : ℝ, s < t → c t = σ t := by
      intro t ht; rw [hcdef]; simp only; rw [if_neg (not_le.mpr ht)]
    have hc0 : c 0 = p := by rw [hcval_le 0 hs0, zero_div, hτ0]
    have hcs : c s = σ s := by rw [hcval_le s le_rfl, div_self hsne, hτ1']
    have hc1 : c 1 = σ 1 := hcval_gt 1 hs1
    -- the glued curve agrees with the tail of `σ` on `[s, 1]`
    have hcEq_right : ∀ x ∈ Icc s 1, c x = σ x := by
      intro x hx
      rcases hx.1.eq_or_lt with rfl | hxgt
      · exact hcs
      · exact hcval_gt x hxgt
    -- piecewise smoothness of the glue
    have hcleft : IsPiecewiseSmoothCurve (I := I) c 0 s := by
      have hbase : IsPiecewiseSmoothCurve (I := I) (fun r : ℝ => τ (1 / s * r + 0)) 0 s := by
        refine isPiecewiseSmoothCurve_comp_mul_add (I := I) (by positivity) ?_
        have e0 : 1 / s * 0 + 0 = 0 := by ring
        have e1 : 1 / s * s + 0 = 1 := by rw [add_zero]; field_simp
        rw [e0, e1]; exact hτpw
      refine hbase.congr ?_
      intro t ht
      show c t = τ (1 / s * t + 0)
      rw [hcval_le t ht.2]
      congr 1
      rw [add_zero, one_div, inv_mul_eq_div]
    have hcright : IsPiecewiseSmoothCurve (I := I) c s 1 :=
      (hpw.mono (I := I) hs0 hs1.le le_rfl).congr hcEq_right
    have hcpw : IsPiecewiseSmoothCurve (I := I) c 0 1 := hcleft.trans hcright
    -- the glued curve has speed `k` throughout
    have hclen_le : ∀ t : ℝ, 0 ≤ t → t ≤ s → curveLength (I := I) g c 0 t = k * t := by
      intro t ht0 hts
      have hcongr : curveLength (I := I) g c 0 t
          = curveLength (I := I) g (fun r : ℝ => τ (1 / s * r + 0)) 0 t := by
        refine curveLength_congr_Icc (I := I) g (a := 0) (b := s) ?_ ⟨le_rfl, hs0⟩ ⟨ht0, hts⟩
        intro x hx
        show c x = τ (1 / s * x + 0)
        rw [hcval_le x hx.2]
        congr 1
        rw [add_zero, one_div, inv_mul_eq_div]
      rw [hcongr, curveLength_comp_mul_add (I := I) g τ (by positivity : (0:ℝ) ≤ 1 / s) 0 0 t]
      simp only [mul_zero, add_zero]
      have hmem : 1 / s * t ∈ Icc (0:ℝ) 1 := by
        refine ⟨by positivity, ?_⟩
        rw [div_mul_eq_mul_div, one_mul, div_le_one hspos]
        exact hts
      rw [hτprop _ hmem, hkτeq]
      field_simp
      ring
    have hclen_gt : ∀ t : ℝ, s ≤ t → t ≤ 1 → curveLength (I := I) g c 0 t = k * t := by
      intro t hst ht1
      have hsplit := (hcpw.mono (I := I) le_rfl (hs0.trans hst) ht1).curveLength_add
        (I := I) g hs0 hst
      have hcsg : curveLength (I := I) g c s t = curveLength (I := I) g σ s t :=
        curveLength_congr_Icc (I := I) g (a := s) (b := 1) hcEq_right ⟨le_rfl, hs1.le⟩ ⟨hst, ht1⟩
      have hsplitσ := (hpw.mono (I := I) le_rfl (hs0.trans hst) ht1).curveLength_add
        (I := I) g hs0 hst
      rw [hprop t ⟨hs0.trans hst, ht1⟩, hprop s ⟨hs0, hs1.le⟩] at hsplitσ
      rw [hsplit, hclen_le s hs0 le_rfl, hcsg]
      linarith
    have hclen : ∀ t ∈ Icc (0:ℝ) 1, curveLength (I := I) g c 0 t = k * (t - 0) := by
      intro t ht
      rcases le_or_gt t s with h | h
      · rw [hclen_le t ht.1 h]; ring
      · rw [hclen_gt t h.le ht.2]; ring
    -- so the glued curve is itself a segment, hence a geodesic on `(0, 1)`
    have hcseg : IsSegment (I := I) g c 0 1 := by
      refine ⟨hcpw, ?_, k, hk, hclen⟩
      rw [hclen 1 (by norm_num), hc0, hc1, hd1]; ring
    have hcgeo := segment_isGeodesic (I := I) g hcseg
    have hσgeo : Geodesic.IsGeodesicOn (I := I) g σ (Ioo 0 1) := segment_isGeodesic (I := I) g hwseg
    -- the two geodesics agree near `a = (s+1)/2`, hence on all of `(0, 1)`
    have ha1 : (s + 1) / 2 ∈ Ioo s 1 := ⟨by linarith, by linarith⟩
    have ha01 : (s + 1) / 2 ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    have hev : c =ᶠ[𝓝 ((s + 1) / 2)] σ := by
      filter_upwards [Ioo_mem_nhds ha1.1 ha1.2] with x hx
      exact hcval_gt x hx.1
    have hpos_eq : c ((s + 1) / 2) = σ ((s + 1) / 2) := hev.eq_of_nhds
    have hderiv : deriv (Geodesic.chartReading (I := I) (σ ((s + 1) / 2)) c) ((s + 1) / 2)
        = deriv (Geodesic.chartReading (I := I) (σ ((s + 1) / 2)) σ) ((s + 1) / 2) := by
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [hev] with x hx
      show extChartAt I (σ ((s + 1) / 2)) (c x) = extChartAt I (σ ((s + 1) / 2)) (σ x)
      rw [hx]
    have heqon : Set.EqOn c σ (Ioo 0 1) :=
      Geodesic.IsGeodesicOn.eqOn_of_deriv_chartReading_eq isOpen_Ioo isPreconnected_Ioo
        hcgeo hσgeo (hcpw.1.mono Ioo_subset_Icc_self) (hpw.1.mono Ioo_subset_Icc_self)
        ha01 hpos_eq (by rw [hpos_eq]; exact mem_chart_source H (σ ((s + 1) / 2))) hderiv
    -- read the agreement at time `s t`
    intro t ht
    rcases ht.1.eq_or_lt with rfl | htpos
    · rw [hτ0, zero_smul]
      exact (expMap_zero g p).symm
    · rcases ht.2.eq_or_lt with rfl | htlt
      · rw [one_smul]; exact hτ1
      · have hst_mem : s * t ∈ Ioo (0:ℝ) 1 := ⟨mul_pos hspos htpos, by nlinarith⟩
        have hst_le : s * t ≤ s := by nlinarith
        have h1 : c (s * t) = τ t := by
          rw [hcval_le _ hst_le]
          congr 1
          field_simp
        have h2 := heqon hst_mem
        rw [hray t, ← h2, h1]

/-- **Math.** Petersen Ch. 5, Prop. 5.7.7 (uniqueness clause, arbitrary parameter
interval): if `v ∈ seg⁰(p)` then *every* segment `τ : [0, b] → M` from `p` to
`x = exp_p(v)`, on *any* parameter interval `[0, b]` with `b > 0`, is the
exponential ray at `v` up to the affine normalization `t ↦ b t`.

This is the form matching Petersen's own proof, which glues a competitor
`σ̃ : [0, t₀] → M` defined on a shorter interval.  Since a segment is only
determined up to its parameter interval, this is the honest reading of "`x` is
joined to `p` by a **unique** segment": normalize by
`IsSegment.comp_mul_of_pos` and apply the `[0, 1]` form. -/
theorem segment_eq_expMap_ray_of_mem_segmentDomainStarInterior'
    (g : RiemannianMetric I M) (p : M) {v : TangentSpace I p}
    (hv : v ∈ segmentDomainStarInterior (I := I) g p)
    {τ : ℝ → M} {b : ℝ} (hb : 0 < b) (hτ : IsSegment (I := I) g τ 0 b) (hτ0 : τ 0 = p)
    (hτb : τ b = expMap (I := I) g p v) :
    ∀ t ∈ Icc (0 : ℝ) 1, τ (b * t) = expMap (I := I) g p (t • v) := by
  intro t ht
  exact segment_eq_expMap_ray_of_mem_segmentDomainStarInterior (I := I) g p hv
    (hτ.comp_mul_of_pos (I := I) hb)
    (by show τ (b * 0) = p; rw [mul_zero]; exact hτ0)
    (by show τ (b * 1) = expMap (I := I) g p v; rw [mul_one]; exact hτb) t ht

/-! ## `exp_p` is injective on the star interior -/

/-- **Math.** Petersen Ch. 5, Prop. 5.7.7
(`prop:pet-ch5-segment-domain-injective`): `exp_p` is injective on the star
interior `seg⁰(p)` of the segment domain.

Given `v₁, v₂ ∈ seg⁰(p)` with `exp_p(v₁) = exp_p(v₂)`, the ray `τ(t) = exp_p(t v₂)`
is a segment from `p` to `exp_p(v₂)` (because `seg⁰(p) ⊆ seg(p)`), hence a segment
from `p` to `exp_p(v₁)`; by the uniqueness clause applied with `v := v₁` it must be
the ray at `v₁`, so the two rays agree on `[0, 1]` and their initial velocities
coincide. -/
theorem expMap_injectiveOnSegmentDomainStarInterior (g : RiemannianMetric I M) (p : M) :
    Set.InjOn (expMap (I := I) g p) (segmentDomainStarInterior (I := I) g p) := by
  intro v₁ h₁ v₂ h₂ heq
  have h₂' : v₂ ∈ segmentDomain (I := I) g p :=
    segmentDomainStarInterior_subset_segmentDomain (I := I) h₂
  have hτ : IsSegment (I := I) g (fun t : ℝ => expMap (I := I) g p (t • v₂)) 0 1 := h₂'
  have hτ0 : (fun t : ℝ => expMap (I := I) g p (t • v₂)) 0 = p := by
    show expMap (I := I) g p ((0:ℝ) • v₂) = p
    rw [zero_smul]; exact expMap_zero g p
  have hτ1 : (fun t : ℝ => expMap (I := I) g p (t • v₂)) 1 = expMap (I := I) g p v₁ := by
    show expMap (I := I) g p ((1:ℝ) • v₂) = expMap (I := I) g p v₁
    rw [one_smul]; exact heq.symm
  have key := segment_eq_expMap_ray_of_mem_segmentDomainStarInterior (I := I) g p h₁ hτ hτ0 hτ1
  refine (eq_of_expMap_ray_eqOn (I := I) g p (v₁ := v₂) (v₂ := v₁) ?_).symm
  intro t ht
  exact key t ht

end PetersenLib

end
