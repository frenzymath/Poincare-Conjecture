import PetersenLib.Ch05.SegmentDomainInjective
import PetersenLib.Ch05.RadialSmooth

/-!
# Petersen Ch. 5, §5.7.4 — the injectivity radius and the cut locus

Petersen's remark (`rem:pet-ch5-injectivity-radius-cut-locus`): on a complete
manifold, `inj(p)` equals `|v|` for `v` the closest point of the cut locus
`seg(p) − seg⁰(p)` to the origin of `T_pM`.

## What this file proves, and what it does *not*

The remark, read against the on-disk `PetersenLib.injectivityRadius` and
`PetersenLib.cutLocus`, is **false** — see the discussion below.  What is true and
proved here is the "`≤`" half, in the sharp form that only needs Prop. 5.7.7
(`expMap_injectiveOnSegmentDomainStarInterior`):

* `cutLocusRadius g p` — the distance from the origin of `T_pM` to the cut locus,
  measured in the Riemannian inner product `g_p`, as an `ℝ≥0∞`-valued infimum (so
  an empty cut locus gives `⊤`, matching `inj(p) = ∞` on `ℝⁿ`).
* `gBall_subset_segmentDomainStarInterior` — the `g_p`-ball of radius `δ` is
  contained in `seg⁰(p)` as soon as it is contained in `seg(p)`; the point is that
  a `g_p`-ball is *open* and star-shaped, so every one of its vectors `v` is a
  proper radial scaling `s·(s⁻¹v)`, `s < 1`, of another vector of the same ball.
* `ofReal_le_injectivityRadius_of_gBall_subset_segmentDomain` and
  `ofReal_le_cutLocusRadius_of_gBall_subset_segmentDomain` — a `g_p`-ball inside
  `seg(p)` (and inside the exponential domain) bounds **both** `inj(p)` and the
  cut-locus radius from below by its radius.  For `inj(p)` this is Prop. 5.7.7:
  `exp_p` is injective on `seg⁰(p)`, hence on the ball.  For the cut-locus radius
  it is `cutLocus ∩ seg⁰ = ∅`.
* `cutLocusRadius_le_injectivityRadius` — the half of the remark that is true:
  `d(0, cut(p)) ≤ inj(p)`, under the hypothesis `hcov` that every `g_p`-ball of
  radius strictly below `d(0, cut(p))` lies in the exponential domain and in
  `seg(p)`.

`hcov` is exactly Petersen's use of Hopf–Rinow (`M = exp_p(seg(p))` and `seg(p)`
closed and star-shaped) and is *not* available on-disk; it is not a bookkeeping
hypothesis but the missing mathematics.

## Why the remark is false at the on-disk definitions

`injectivityRadius` is built from `expDomain`, which is built from
`geodesicVectorFieldChart g p` — the geodesic field of the **single chart at `p`**,
identically `0` off `(chartAt H p).source`.  So `expDomain g p` is bounded by the
reach of that one chart, while `IsSegment` (hence `segmentDomain`, hence
`cutLocus`) is chart-free: it asks for minimization in the *whole* of `M`.

Take `M = E` flat, but presented with an atlas whose chart at each point has
source a unit ball.  Then `expDomain g p` is the unit ball of `T_pM`, every
straight ray of length `< 1` minimizes in `M`, so `seg(p)` is that same unit ball;
being open and star-shaped it satisfies `seg(p) = seg⁰(p)`, so `cut(p) = ∅` and
`cutLocusRadius g p = ⊤`.  But `inj(p) = 1`, since no `g_p`-ball of radius `> 1`
lies in `expDomain g p`.  Hence `inj(p) = 1 ≠ ⊤ = d(0, cut(p))`, and this `M` is
geodesically complete in the intrinsic sense (`IsGeodesicallyComplete`, which is
stated with the moving-chart `HasGeodesicEquationAt`), so adding Petersen's
completeness hypothesis does not repair it.  The failure is one-sided and in the
direction *not* proved here: `inj(p) ≤ d(0, cut(p))` is what breaks.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]
  [T2Space M] [ConnectedSpace M]

variable {g : RiemannianMetric I M} {p : M}

/-! ## The `g_p`-norm and the cut-locus radius -/

/-- **Math.** The Riemannian length `|v|_g = √(g_p(v, v))` of a tangent vector at
`p`, the quantity in which both `injectivityRadius` and Petersen's "closest point
of the cut locus to the origin" are measured. -/
def metricNorm (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) : ℝ :=
  Real.sqrt (g.metricInner p v v)

lemma metricNorm_nonneg (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    0 ≤ metricNorm (I := I) g p v := Real.sqrt_nonneg _

lemma metricNorm_sq (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    metricNorm (I := I) g p v ^ 2 = g.metricInner p v v :=
  Real.sq_sqrt (g.metricInner_self_nonneg p v)

/-- **Math.** Petersen Ch. 5 (`rem:pet-ch5-injectivity-radius-cut-locus`): the
distance from the origin of `T_pM` to the cut locus, measured in `g_p`.  The
infimum is taken in `ℝ≥0∞`, so an empty cut locus gives `⊤` — the right value on
`ℝⁿ`, where `inj(p) = ∞`. -/
def cutLocusRadius (g : RiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  ⨅ v ∈ cutLocus (I := I) g p, ENNReal.ofReal (metricNorm (I := I) g p v)

/-! ## The origin is never a cut vector -/

/-- **Math.** The zero vector lies in the segment domain: the constant curve at `p`
is a segment (Thm. 5.5.4, at `v = 0`). -/
theorem zero_mem_segmentDomain (g : RiemannianMetric I M) (p : M) :
    (0 : TangentSpace I p) ∈ segmentDomain (I := I) g p := by
  obtain ⟨ε, hε, hseg⟩ := exists_expMap_isSegment (I := I) g p
  have h := hseg (0 : E) (by simpa using hε)
  simpa using h

/-- **Math.** The zero vector lies in the star interior `seg⁰(p)` (take `s = 0`). -/
theorem zero_mem_segmentDomainStarInterior (g : RiemannianMetric I M) (p : M) :
    (0 : TangentSpace I p) ∈ segmentDomainStarInterior (I := I) g p :=
  ⟨0, ⟨le_rfl, zero_lt_one⟩, 0, zero_mem_segmentDomain (I := I) g p,
    (zero_smul _ _).symm⟩

/-- **Math.** The origin is never a cut vector. -/
theorem zero_notMem_cutLocus (g : RiemannianMetric I M) (p : M) :
    (0 : TangentSpace I p) ∉ cutLocus (I := I) g p := fun h =>
  h.2 (zero_mem_segmentDomainStarInterior (I := I) g p)

/-- **Math.** Every cut vector has positive Riemannian length. -/
theorem metricNorm_pos_of_mem_cutLocus {v : TangentSpace I p}
    (hv : v ∈ cutLocus (I := I) g p) : 0 < metricNorm (I := I) g p v := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact zero_notMem_cutLocus (I := I) g p hv
  exact Real.sqrt_pos.2 (g.metricInner_self_pos p v hv0)

/-! ## A `g_p`-ball inside `seg(p)` is inside `seg⁰(p)` -/

/-- **Math.** If the open `g_p`-ball of radius `δ` is contained in the segment
domain, it is contained in the **star interior** `seg⁰(p)`.

The ball is open and star-shaped about `0`, so a vector `v` of the ball is the
proper radial scaling `v = s·(s⁻¹ v)` of the vector `s⁻¹ v`, which is still in the
ball for `s` chosen strictly between `|v|_g / δ` and `1`. -/
theorem gBall_subset_segmentDomainStarInterior (g : RiemannianMetric I M) (p : M)
    {δ : ℝ} (hδ : 0 < δ)
    (hseg : ∀ v : TangentSpace I p, g.metricInner p v v < δ ^ 2 →
      v ∈ segmentDomain (I := I) g p) :
    {v : TangentSpace I p | g.metricInner p v v < δ ^ 2}
      ⊆ segmentDomainStarInterior (I := I) g p := by
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  set a : ℝ := metricNorm (I := I) g p v with ha
  have ha0 : 0 ≤ a := metricNorm_nonneg (I := I) g p v
  have haδ : a < δ := by
    have hsq : a ^ 2 < δ ^ 2 := by rw [ha, metricNorm_sq]; exact hv
    nlinarith
  set s : ℝ := (a + δ) / (2 * δ) with hs
  have hs0 : 0 < s := by
    rw [hs]; positivity
  have hs1 : s < 1 := by
    rw [hs, div_lt_one (by linarith)]; linarith
  have hkey : a / s < δ := by
    rw [div_lt_iff₀ hs0, hs]
    field_simp
    nlinarith
  refine ⟨s, ⟨hs0.le, hs1⟩, s⁻¹ • v, hseg _ ?_, ?_⟩
  · have hgram : g.metricInner p (s⁻¹ • v) (s⁻¹ • v) = (s⁻¹ * s⁻¹) * g.metricInner p v v := by
      rw [g.metricInner_smul_left, g.metricInner_smul_right, ← mul_assoc]
    rw [hgram, ← metricNorm_sq (I := I) g p v, ← ha]
    have : (s⁻¹ * s⁻¹) * a ^ 2 = (a / s) ^ 2 := by
      field_simp
    rw [this]
    have hd0 : 0 ≤ a / s := div_nonneg ha0 hs0.le
    nlinarith
  · rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]

/-! ## Lower bounds on both sides of the remark -/

/-- **Math.** Petersen Ch. 5, Prop. 5.7.7 in radius form: if the open `g_p`-ball of
radius `δ` lies in the exponential domain and in the segment domain, then
`δ ≤ inj(p)`.  Indeed the ball then lies in `seg⁰(p)`, on which `exp_p` is
injective. -/
theorem ofReal_le_injectivityRadius_of_gBall_subset_segmentDomain
    (g : RiemannianMetric I M) (p : M) {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ v : TangentSpace I p, g.metricInner p v v < δ ^ 2 →
      v ∈ expDomain (I := I) g p)
    (hseg : ∀ v : TangentSpace I p, g.metricInner p v v < δ ^ 2 →
      v ∈ segmentDomain (I := I) g p) :
    ENNReal.ofReal δ ≤ injectivityRadius (I := I) g p := by
  refine le_sSup ⟨δ, hδ, rfl, hdom, ?_⟩
  exact (expMap_injectiveOnSegmentDomainStarInterior (I := I) g p).mono
    (gBall_subset_segmentDomainStarInterior (I := I) g p hδ hseg)

/-- **Math.** The same hypothesis bounds the cut-locus radius below: a `g_p`-ball
inside `seg(p)` lies in `seg⁰(p)`, which is disjoint from the cut locus, so every
cut vector has `|v|_g ≥ δ`. -/
theorem ofReal_le_cutLocusRadius_of_gBall_subset_segmentDomain
    (g : RiemannianMetric I M) (p : M) {δ : ℝ} (hδ : 0 < δ)
    (hseg : ∀ v : TangentSpace I p, g.metricInner p v v < δ ^ 2 →
      v ∈ segmentDomain (I := I) g p) :
    ENNReal.ofReal δ ≤ cutLocusRadius (I := I) g p := by
  refine le_iInf₂ fun v hv => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  by_contra hlt
  push_neg at hlt
  have hball : g.metricInner p v v < δ ^ 2 := by
    rw [← metricNorm_sq (I := I) g p v]
    nlinarith [metricNorm_nonneg (I := I) g p v]
  exact hv.2 (gBall_subset_segmentDomainStarInterior (I := I) g p hδ hseg hball)

/-! ## The half of the remark that is true -/

/-- **Math.** Petersen Ch. 5 (`rem:pet-ch5-injectivity-radius-cut-locus`), the
inequality `d(0, cut(p)) ≤ inj(p)`.

The hypothesis `hcov` — every `g_p`-ball of radius strictly below the cut-locus
radius lies in the exponential domain and in `seg(p)` — is Petersen's use of
Hopf–Rinow (`M = exp_p(seg(p))`, with `seg(p)` closed and star-shaped) and is not
available against the on-disk chart-anchored `expMap`.  Given it, the conclusion is
Prop. 5.7.7 alone.

The reverse inequality `inj(p) ≤ d(0, cut(p))` is **false** at these definitions;
see the module docstring. -/
theorem cutLocusRadius_le_injectivityRadius (g : RiemannianMetric I M) (p : M)
    (hcov : ∀ δ : ℝ, 0 < δ → ENNReal.ofReal δ < cutLocusRadius (I := I) g p →
      ∀ v : TangentSpace I p, g.metricInner p v v < δ ^ 2 →
        v ∈ expDomain (I := I) g p ∧ v ∈ segmentDomain (I := I) g p) :
    cutLocusRadius (I := I) g p ≤ injectivityRadius (I := I) g p := by
  refine le_of_forall_lt fun a ha => ?_
  obtain ⟨b, hab, hbR⟩ := exists_between ha
  have hb0 : 0 < b := lt_of_le_of_lt zero_le hab
  have hbtop : b ≠ ⊤ := hbR.ne_top
  set δ : ℝ := b.toReal with hδdef
  have hδ0 : 0 < δ := ENNReal.toReal_pos hb0.ne' hbtop
  have hbδ : ENNReal.ofReal δ = b := ENNReal.ofReal_toReal hbtop
  have hcov' := hcov δ hδ0 (by rw [hbδ]; exact hbR)
  have := ofReal_le_injectivityRadius_of_gBall_subset_segmentDomain (I := I) g p hδ0
    (fun v hv => (hcov' v hv).1) (fun v hv => (hcov' v hv).2)
  rw [hbδ] at this
  exact lt_of_lt_of_le hab this

end PetersenLib

end
