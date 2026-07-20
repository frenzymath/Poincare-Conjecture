import DoCarmoLib.Riemannian.Geodesic.HopfRinow.ConstantSpeed
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1

/-!
# The energy of a curve and the Schwarz inequality `L(c)² ≤ a·E(c)` (do Carmo Ch. 9 §2)

do Carmo Ch. 9 §2 introduces, alongside the arc length

  `L(c) = ∫₀ᵃ |dc/dt| dt`   (already in the library as `Riemannian.DCArcLength`,
                             do Carmo Ch. 1 Def. 2.9),

the **energy**

  `E(c) = ∫₀ᵃ |dc/dt|² dt`,

and derives from the Schwarz inequality the comparison

  `L(c)² ≤ a · E(c)`,  with equality iff `|dc/dt|` is constant,
                       i.e. iff `t` is proportional to arc length.

This comparison is the whole reason Ch. 9 works with `E` rather than `L`: it is what
turns "`γ` minimizes length" into "`γ` minimizes energy" in `lem:dc-ch9-2-3`, and it is
used again at the very end of the Synge–Weinstein proof (`thm:dc-ch9-3-7`).

## Contents

* `Riemannian.dcSpeed` — the speed `|dc/dt| = ⟨dc/dt, dc/dt⟩^{1/2}`, the common
  integrand: `DCArcLength = ∫ dcSpeed` and `DCEnergy = ∫ dcSpeed²`.
* `Riemannian.DCEnergy` — do Carmo's `E(c)`, in the idiom of `DCArcLength`.
* `Riemannian.sq_integral_le_sub_mul_integral_sq` — the underlying real-analysis
  inequality `(∫ₐᵇ f)² ≤ (b−a)·∫ₐᵇ f²`, and
  `Riemannian.sq_integral_eq_iff_ae_eq_const` — its equality case.
* `Riemannian.dcArcLength_sq_le_mul_dcEnergy` — **do Carmo's `L(c)² ≤ a·E(c)`**.
* `Riemannian.dcArcLength_sq_eq_iff` — equality iff the speed is a.e. constant.
* `Riemannian.dcSpeed_eq_sqrt_speedSq`, `Riemannian.dcEnergy_eq_integral_speedSq` — the
  bridges to `Riemannian.Geodesic.speedSq`, the library's pre-existing squared speed
  (`Geodesic/HopfRinow/ConstantSpeed.lean`), to which `dcSpeed`/`DCEnergy` are
  definitionally equal.  In particular `Geodesic.IsGeodesicOn.speedSq_eq` ("a geodesic
  has constant speed") is do Carmo's equality case for the curves Ch. 9 cares about.

## The proof of the Schwarz step

do Carmo puts `f ≡ 1`, `g = |dc/dt|` in `(∫ f g)² ≤ ∫ f² · ∫ g²`.  Mathlib has no
packaged interval Cauchy–Schwarz `(∫ f g)² ≤ (∫ f²)(∫ g²)` and — more importantly — no
equality case for it, so quoting do Carmo literally is not available.  We use instead the
elementary completion of the square: with `m = (∫ₐᵇ f)/(b−a)` the mean of `f`,

  `0 ≤ ∫ₐᵇ (f − m)² = ∫ₐᵇ f² − 2m∫ₐᵇ f + m²(b−a) = E − L²/(b−a)`,

which gives the inequality, and gives the equality case for free: equality holds iff
`∫ₐᵇ (f − m)² = 0`, and a nonnegative integrand has vanishing integral iff it vanishes
a.e. (`intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae`), i.e. iff `f = m` a.e.
This is do Carmo's "equality iff `g` is constant, that is, iff `t` is proportional to arc
length".

## Regularity

The hypotheses are **integrability** of the speed and of its square — which is all the
proof uses, and which is what do Carmo leaves implicit when he writes down `L(c)` and
`E(c)` at all.  Note that this is deliberately *not* continuity of the speed: do Carmo's
curves here are only *piecewise* differentiable (`def:dc-ch9-2-1`(b) allows a subdivision
`0 = t₀ < ⋯ < t_{k+1} = a`), so `|dc/dt|` may **jump** at the corners, and assuming a
continuous speed would exclude exactly the curve class Ch. 9 works with.  Continuous-speed
convenience versions are provided as `..._of_continuousOn` corollaries.

Reference: do Carmo, *Riemannian Geometry*, Ch. 9 §2 (the paragraph after
`prop:dc-ch9-2-2`), and Ch. 1 Def. 2.9 for `L`.
-/

open MeasureTheory intervalIntegral Set
open scoped Manifold Topology ContDiff

noncomputable section

namespace Riemannian

/-! ### The real-analysis core -/

section RealCore

variable {f : ℝ → ℝ} {a b : ℝ}

/-- **Math.** The expansion `∫ₐᵇ (f − m)² = ∫ₐᵇ f² − 2m∫ₐᵇ f + m²(b−a)`, the one computation behind
both the Schwarz inequality and its equality case. -/
private theorem integral_sub_const_sq (m : ℝ)
    (hfi : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) volume a b) :
    (∫ t in a..b, (f t - m) ^ 2)
      = (∫ t in a..b, (f t) ^ 2) - 2 * m * (∫ t in a..b, f t) + m ^ 2 * (b - a) := by
  have hpt : ∀ t, (f t - m) ^ 2 = ((f t) ^ 2 - 2 * m * f t) + m ^ 2 := by intro t; ring
  have hint1 : IntervalIntegrable (fun t => (f t) ^ 2 - 2 * m * f t) volume a b :=
    hf2.sub (hfi.const_mul (2 * m))
  have hint2 : IntervalIntegrable (fun _ : ℝ => m ^ 2) volume a b :=
    _root_.intervalIntegrable_const
  calc (∫ t in a..b, (f t - m) ^ 2)
      = ∫ t in a..b, (((f t) ^ 2 - 2 * m * f t) + m ^ 2) := by simp_rw [hpt]
    _ = (∫ t in a..b, ((f t) ^ 2 - 2 * m * f t)) + ∫ _t in a..b, m ^ 2 :=
        intervalIntegral.integral_add hint1 hint2
    _ = ((∫ t in a..b, (f t) ^ 2) - ∫ t in a..b, 2 * m * f t) + m ^ 2 * (b - a) := by
        rw [intervalIntegral.integral_sub hf2 (hfi.const_mul (2 * m)),
          intervalIntegral.integral_const]
        simp [smul_eq_mul]; ring
    _ = (∫ t in a..b, (f t) ^ 2) - 2 * m * (∫ t in a..b, f t) + m ^ 2 * (b - a) := by
        rw [intervalIntegral.integral_const_mul]

/-- **Math.** Integrability of `(f − m)²`, from that of `f` and `f²`. -/
private theorem intervalIntegrable_sub_const_sq (m : ℝ)
    (hfi : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) volume a b) :
    IntervalIntegrable (fun t => (f t - m) ^ 2) volume a b := by
  have hpt : (fun t => (f t - m) ^ 2) = fun t => ((f t) ^ 2 - 2 * m * f t) + m ^ 2 := by
    funext t; ring
  rw [hpt]
  exact (hf2.sub (hfi.const_mul (2 * m))).add _root_.intervalIntegrable_const

/-- **Math.** The Schwarz inequality of do Carmo Ch. 9 §2 in the form he uses it
(`f ≡ 1`, `g = |dc/dt|`): `(∫ₐᵇ f)² ≤ (b−a)·∫ₐᵇ f²`.

Proved by completing the square: `0 ≤ ∫ₐᵇ (f − m)²` for `m` the mean of `f`.  Only
integrability is assumed, so this applies to the *piecewise* differentiable curves of
`def:dc-ch9-2-1`, whose speed jumps at the corners. -/
theorem sq_integral_le_sub_mul_integral_sq (hab : a ≤ b)
    (hfi : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  have hba : (0:ℝ) < b - a := by linarith
  set L := ∫ t in a..b, f t with hL
  set m := L / (b - a) with hm
  have hexp := integral_sub_const_sq (f := f) (a := a) (b := b) m hfi hf2
  have hnn : 0 ≤ ∫ t in a..b, (f t - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
  rw [hexp] at hnn
  have hmL : m * (b - a) = L := by rw [hm]; field_simp
  nlinarith [hnn, hmL, hba]

/-- **Math.** The equality case of `sq_integral_le_sub_mul_integral_sq`: equality holds iff
`f` is a.e. equal to its mean on `(a,b]`.  This is do Carmo's "with equality if and only
if `g` is constant, that is, if and only if `t` is proportional to arc length". -/
theorem sq_integral_eq_iff_ae_eq_const (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) volume a b) :
    ((∫ t in a..b, f t) ^ 2 = (b - a) * ∫ t in a..b, (f t) ^ 2) ↔
      f =ᵐ[volume.restrict (Ioc a b)] Function.const ℝ ((∫ t in a..b, f t) / (b - a)) := by
  have hab' : a ≤ b := hab.le
  have hba : (0:ℝ) < b - a := by linarith
  set L := ∫ t in a..b, f t with hL
  set E := ∫ t in a..b, (f t) ^ 2 with hE
  set m := L / (b - a) with hm
  have hint : IntervalIntegrable (fun t => (f t - m) ^ 2) volume a b :=
    intervalIntegrable_sub_const_sq (f := f) (a := a) (b := b) m hfi hf2
  have hexp := integral_sub_const_sq (f := f) (a := a) (b := b) m hfi hf2
  have hmL : m * (b - a) = L := by rw [hm]; field_simp
  have hiff : (L ^ 2 = (b - a) * E) ↔ (∫ t in a..b, (f t - m) ^ 2) = 0 := by
    rw [hexp]; constructor <;> intro h <;> nlinarith [h, hmL, hba]
  rw [hiff, intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab'
      (Filter.Eventually.of_forall (fun t => by positivity)) hint]
  constructor
  · intro h
    filter_upwards [h] with t ht
    have h0 : (f t - m) ^ 2 = 0 := ht
    simpa [Function.const, hm] using sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)
  · intro h
    filter_upwards [h] with t ht
    have : f t = m := by simpa [Function.const, hm] using ht
    simp [this]

/-- **Math.** `sq_integral_le_sub_mul_integral_sq` under the convenience hypothesis that `f`
is continuous on `[a,b]` (which gives both integrability assumptions). -/
theorem sq_integral_le_sub_mul_integral_sq_of_continuousOn (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 :=
  sq_integral_le_sub_mul_integral_sq hab (hf.intervalIntegrable_of_Icc hab)
    ((hf.pow 2).intervalIntegrable_of_Icc hab)

end RealCore

/-! ### The energy of a curve -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The **speed** `|dc/dt| = ⟨dc/dt, dc/dt⟩^{1/2}` of a curve, the integrand of
do Carmo's arc length (`DCArcLength`, Ch. 1 Def. 2.9).  Isolating it makes the Ch. 9
comparison `L(c)² ≤ a·E(c)` a statement about the single function `dcSpeed g c`. -/
def dcSpeed (g : RiemannianMetric I M) (c : ℝ → M) (t : ℝ) : ℝ :=
  Real.sqrt (g.metricInner (c t) (DCVelocity c t) (DCVelocity c t))

/-- **Math.** `DCArcLength` is the integral of the speed — definitionally. -/
theorem dcArcLength_eq_integral_dcSpeed (g : RiemannianMetric I M) (c : ℝ → M) (a b : ℝ) :
    DCArcLength g c a b = ∫ t in a..b, dcSpeed g c t := rfl

/-- **Math.** The speed is non-negative. -/
theorem dcSpeed_nonneg (g : RiemannianMetric I M) (c : ℝ → M) (t : ℝ) : 0 ≤ dcSpeed g c t :=
  Real.sqrt_nonneg _

/-- **Math.** The speed squared is the metric square of the velocity — the bridge making
`DCEnergy = ∫ (dcSpeed)²`. -/
theorem dcSpeed_sq (g : RiemannianMetric I M) (c : ℝ → M) (t : ℝ) :
    (dcSpeed g c t) ^ 2 = g.metricInner (c t) (DCVelocity c t) (DCVelocity c t) :=
  Real.sq_sqrt (g.metricInner_self_nonneg _ _)

/-- **Math.** do Carmo Ch. 9 §2: the **energy** of the segment `c|[a,b]`,
`E(c) = ∫ₐᵇ |dc/dt|² dt`.  Companion of `DCArcLength` (do Carmo Ch. 1 Def. 2.9); do Carmo
prefers `E` to `L` because it is a smooth function of a variation parameter, while `L` is
not (the square root is not differentiable at a zero of the velocity). -/
def DCEnergy (g : RiemannianMetric I M) (c : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, g.metricInner (c t) (DCVelocity c t) (DCVelocity c t)

/-- **Math.** The energy is the integral of the squared speed. -/
theorem dcEnergy_eq_integral_dcSpeed_sq (g : RiemannianMetric I M) (c : ℝ → M) (a b : ℝ) :
    DCEnergy g c a b = ∫ t in a..b, (dcSpeed g c t) ^ 2 := by
  simp_rw [DCEnergy, dcSpeed_sq]

/-- **Math.** do Carmo Ch. 9 §2, the **Schwarz inequality** `L(c)² ≤ a·E(c)`
(here `L(c)² ≤ (b−a)·E(c)` on `[a,b]`; do Carmo's `a` is the length `b − a` of the
parameter interval).

This is the inequality that lets Ch. 9 replace length by energy: see `lem:dc-ch9-2-3`.
Only integrability of the speed and of its square is assumed, so this covers do Carmo's
piecewise differentiable curves, whose speed jumps at the corners. -/
theorem dcArcLength_sq_le_mul_dcEnergy (g : RiemannianMetric I M) (c : ℝ → M) {a b : ℝ}
    (hab : a ≤ b) (hs : IntervalIntegrable (dcSpeed g c) volume a b)
    (hs2 : IntervalIntegrable (fun t => (dcSpeed g c t) ^ 2) volume a b) :
    (DCArcLength g c a b) ^ 2 ≤ (b - a) * DCEnergy g c a b := by
  rw [dcArcLength_eq_integral_dcSpeed, dcEnergy_eq_integral_dcSpeed_sq]
  exact sq_integral_le_sub_mul_integral_sq hab hs hs2

/-- **Math.** do Carmo Ch. 9 §2: equality in `L(c)² ≤ a·E(c)` holds **iff** the speed
`|dc/dt|` is (a.e.) constant — do Carmo's "iff `t` is proportional to arc length". -/
theorem dcArcLength_sq_eq_iff (g : RiemannianMetric I M) (c : ℝ → M) {a b : ℝ}
    (hab : a < b) (hs : IntervalIntegrable (dcSpeed g c) volume a b)
    (hs2 : IntervalIntegrable (fun t => (dcSpeed g c t) ^ 2) volume a b) :
    ((DCArcLength g c a b) ^ 2 = (b - a) * DCEnergy g c a b) ↔
      dcSpeed g c =ᵐ[volume.restrict (Ioc a b)]
        Function.const ℝ (DCArcLength g c a b / (b - a)) := by
  rw [dcArcLength_eq_integral_dcSpeed, dcEnergy_eq_integral_dcSpeed_sq]
  exact sq_integral_eq_iff_ae_eq_const hab hs hs2

/-- **Math.** `dcArcLength_sq_le_mul_dcEnergy` under the convenience hypothesis that the
speed is continuous on `[a,b]` (a genuine restriction: it rules out the corners that
`def:dc-ch9-2-1`(b) permits). -/
theorem dcArcLength_sq_le_mul_dcEnergy_of_continuousOn (g : RiemannianMetric I M)
    (c : ℝ → M) {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn (dcSpeed g c) (Icc a b)) :
    (DCArcLength g c a b) ^ 2 ≤ (b - a) * DCEnergy g c a b :=
  dcArcLength_sq_le_mul_dcEnergy g c hab (hc.intervalIntegrable_of_Icc hab)
    ((hc.pow 2).intervalIntegrable_of_Icc hab)

/-! ### Bridge to the library's pre-existing squared speed -/

section SpeedSq

/-- **Math.** `dcSpeed` is the square root of the library's `Geodesic.speedSq`
(`Geodesic/HopfRinow/ConstantSpeed.lean`) — definitionally, since
`DCVelocity c t = mfderiv 𝓘(ℝ,ℝ) I c t 1`. -/
theorem dcSpeed_eq_sqrt_speedSq (g : RiemannianMetric I M) (c : ℝ → M) (t : ℝ) :
    dcSpeed g c t = Real.sqrt (Geodesic.speedSq (I := I) g c t) := rfl

/-- **Math.** `DCEnergy` is the integral of the library's `Geodesic.speedSq` — so do Carmo's
Ch. 9 energy is the pre-existing squared speed integrated, not a new object.  In particular
`Geodesic.IsGeodesicOn.speedSq_eq` ("a geodesic has constant speed") supplies do Carmo's
equality case for geodesics. -/
theorem dcEnergy_eq_integral_speedSq (g : RiemannianMetric I M) (c : ℝ → M) (a b : ℝ) :
    DCEnergy g c a b = ∫ t in a..b, Geodesic.speedSq (I := I) g c t := rfl

end SpeedSq

end Riemannian
