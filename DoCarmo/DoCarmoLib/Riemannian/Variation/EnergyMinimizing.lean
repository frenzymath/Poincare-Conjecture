import DoCarmoLib.Riemannian.Variation.Energy
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.ConstantSpeed

/-!
# Minimizing geodesics minimize energy (do Carmo Ch. 9, §2, Lemma 2.3)

do Carmo, *Riemannian Geometry*, Ch. 9, §2, `lem:dc-ch9-2-3`: if `γ : [0,a] → M` is a
minimizing geodesic joining `p` to `q`, then `E(γ) ≤ E(c)` for every curve
`c : [0,a] → M` joining `p` to `q`, with equality iff `c` is a minimizing geodesic.

His proof is the three-step chain

  `a·E(γ) = L(γ)² ≤ L(c)² ≤ a·E(c)`,

whose steps are: (i) `γ` is a geodesic, hence has constant speed, hence realizes
*equality* in the Schwarz comparison `lem:dc-ch9-2-2-schwarz`; (ii) `γ` is minimizing,
so `L(γ) ≤ L(c)`; (iii) the Schwarz comparison for `c`.

## What this file proves, and the shape of the minimality hypothesis

Steps (i) and (iii) are `dcArcLength_sq_eq_mul_dcEnergy_of_isGeodesicOn` and the
library's `dcArcLength_sq_le_mul_dcEnergy`; the chain is `dcEnergy_le_of_dcArcLength_le`.

Minimality enters **only** through step (ii), and only as the inequality
`L(γ) ≤ L(c)` — so that is the hypothesis taken here, rather than a metric
("`d(p,q) = L(γ)`") formulation.  This is not a shortcut but a scope decision worth
recording, because it is what makes the lemma usable at all today:

* DoCarmoLib has **no `IsMinimizingGeodesic` predicate**.  Minimality is spelled out
  inline, and in two mutually non-interchangeable idioms — `edist (γ a) (γ b) =
  ENNReal.ofReal (ℓ * (b - a))` (`Exponential/MinimizingGeodesic.lean`) and
  `∀ s t ∈ Icc 0 1, dist (γ s) (γ t) = |s - t| * dist x y`
  (`Geodesic.exists_minimizing_geodesic`).
* Both of those, and all of Ch. 3/Ch. 7, measure length with `Manifold.pathELength`
  (an `ℝ≥0∞` lintegral), whereas `DCArcLength` (do Carmo Ch. 1 Def. 2.9, and what
  `Energy.lean` is written in) is an `ℝ` Bochner integral.  The two are joined by
  `Variation/ArcLengthBridge.lean` (`ofReal_dcArcLength_eq_pathELength`), and in
  particular `dcArcLength_le_of_pathELength_le` there converts a `pathELength`
  minimality comparison into the `L(γ) ≤ L(c)` this file consumes.

Taking `L(γ) ≤ L(c)` keeps the lemma exactly as strong as its proof, and leaves the
conversion from a metric minimality statement as a *separate* obligation at the call
site (discharged by `ArcLengthBridge.lean`, which this file deliberately does not
import) rather than baking it in.  See the `## Residual` section below.

## The equality case

do Carmo's equality case ("equality iff `c` is a minimizing geodesic") splits into
the two conclusions his proof actually extracts, both of which are proved here:

* `dcSpeed_ae_const_of_dcEnergy_eq` — equality forces the speed of `c` to be a.e.
  constant, i.e. do Carmo's "the parameter of `c` is proportional to arc length";
* `dcArcLength_eq_of_dcEnergy_eq` — equality forces `L(c) = L(γ)`, i.e. `c` is
  minimizing too.

Those two are what do Carmo *feeds* to `cor:dc-ch3-3-9` ("a curve whose length
realizes the distance and which is parametrized proportionally to arc length is a
geodesic") to conclude that `c` is a geodesic.  They are **not** literally that
corollary's hypotheses, and the difference is exactly the residual below: the
corollary wants proportional arc length *pointwise* and minimality against *every*
competitor, while these give a.e.-constancy and `L(c) = L(γ)` for the single `c` at
hand.  That final application is *not* performed here.

## Residual

`lem:dc-ch9-2-3` is **not** closed, by exactly one step:

**`a.e.-constant speed ⟹ pointwise proportional arc length.**  `cor:dc-ch3-3-9`
*assumes* `∀ t ∈ Icc, pathELength I c (τ 0) t = ofReal (ℓ * (t - τ 0))` pointwise,
which is strictly stronger than the a.e.-constant speed the equality case yields.
Upgrading should now be tractable — an integral does not see the null set, so
a.e.-constant speed does give the length identity at *every* `t`, and
`ofReal_dcArcLength_eq_pathELength` (`Variation/ArcLengthBridge.lean`) converts that
to `pathELength`.  A second mismatch to expect at that call site: the corollary's
minimality is quantified over all competitors `σ`, whereas
`dcArcLength_eq_of_dcEnergy_eq` gives `L(γ) = L(c)` for one `c`.  Filed as **I-0355**.

Consequently `lem:dc-ch9-2-3` is **not** tagged `\leanok`: the sub-nodes proved here
are tagged individually, and the full `iff` awaits the bridge.

## Regularity

`Geodesic.IsGeodesicOn.speedSq_eq` (constant speed) requires an **open**, preconnected
set, so the geodesic hypothesis is stated on `Ioo a b` and never on `Icc a b`.  That
costs nothing: the Schwarz equality case `dcArcLength_sq_eq_iff` only needs the speed
to be a.e. constant on `Ioc a b`, and `Ioc a b \ Ioo a b = {b}` is null.  This mirrors
`cor:dc-ch3-3-9`, whose conclusion is likewise `IsGeodesicOn ... (Ioo ...)` only.

Integrability of the speed and of its square is assumed, exactly as in `Energy.lean`,
and for the same reason: do Carmo's curves here are only *piecewise* differentiable, so
the speed may jump at the corners and a continuity hypothesis would exclude the very
curve class the chapter is about.

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, §2, Lemma 2.3; the Schwarz step is
Ch. 9 §2 (`lem:dc-ch9-2-2-schwarz`); `cor:dc-ch3-3-9` is Ch. 3, Cor. 3.9.
-/

open MeasureTheory intervalIntegral Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### A geodesic has constant speed -/

/-- **Math.** do Carmo Ch. 3: a **geodesic has constant speed**, in the `dcSpeed`
idiom of Ch. 9.  This is `Geodesic.IsGeodesicOn.speedSq_eq` under the definitional
bridge `dcSpeed = √ speedSq` (`dcSpeed_eq_sqrt_speedSq`).

The set must be **open** and preconnected — the underlying statement is proved by
"derivative zero on a connected open set", so it says nothing at an endpoint. -/
theorem dcSpeed_eq_of_isGeodesicOn {g : RiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ s) (hs : IsOpen s)
    (hconn : IsPreconnected s) (hcont : ContinuousOn γ s)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ s) (h₂ : t₂ ∈ s) :
    dcSpeed g γ t₁ = dcSpeed g γ t₂ := by
  rw [dcSpeed_eq_sqrt_speedSq, dcSpeed_eq_sqrt_speedSq, hγ.speedSq_eq hs hconn hcont h₁ h₂]

/-! ### A geodesic realizes equality in the Schwarz comparison -/

/-- **Math.** do Carmo Ch. 9, §2, the first step of `lem:dc-ch9-2-3`: a **geodesic
attains equality** in the Schwarz comparison,
$$L(\gamma)^2 = (b-a)\,E(\gamma).$$

do Carmo writes this as `a E(γ) = (L(γ))²` and justifies it by "the parameter of a
geodesic is proportional to arc length" — i.e. the equality case of
`lem:dc-ch9-2-2-schwarz` (`dcArcLength_sq_eq_iff`) together with constant speed
(`dcSpeed_eq_of_isGeodesicOn`).

The geodesic hypothesis lives on the **open** interval `Ioo a b`, which is all that
constant speed is available on; the equality case needs the speed to be constant only
*almost everywhere* on `Ioc a b`, and `Ioc a b \ Ioo a b = {b}` is null. -/
theorem dcArcLength_sq_eq_mul_dcEnergy_of_isGeodesicOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ (Ioo a b))
    (hcont : ContinuousOn γ (Ioo a b))
    (hs : IntervalIntegrable (dcSpeed g γ) volume a b)
    (hs2 : IntervalIntegrable (fun t => (dcSpeed g γ t) ^ 2) volume a b) :
    (DCArcLength g γ a b) ^ 2 = (b - a) * DCEnergy g γ a b := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  set k := dcSpeed g γ ((a + b) / 2) with hk
  -- constant speed on the open interval
  have hconst : ∀ t ∈ Ioo a b, dcSpeed g γ t = k := fun t ht =>
    dcSpeed_eq_of_isGeodesicOn hγ isOpen_Ioo isPreconnected_Ioo hcont ht hmid
  -- `{b}` is null, so the speed is a.e. `k` on the half-open interval
  have hb_ne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton b)] with t ht using ht
  -- the arc length is `k · (b − a)`
  have hL : DCArcLength g γ a b = k * (b - a) := by
    rw [dcArcLength_eq_integral_dcSpeed]
    have hcongr : ∫ t in a..b, dcSpeed g γ t = ∫ _t in a..b, k := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hb_ne] with t ht htmem
      rw [uIoc_of_le hab.le] at htmem
      exact hconst t ⟨htmem.1, lt_of_le_of_ne htmem.2 ht⟩
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
    ring
  -- the speed is a.e. constant on `Ioc a b`
  have hrestrict : (volume : Measure ℝ).restrict (Ioc a b)
      = (volume : Measure ℝ).restrict (Ioo a b) :=
    (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
  have hae : dcSpeed g γ =ᵐ[(volume : Measure ℝ).restrict (Ioc a b)] Function.const ℝ k := by
    rw [hrestrict]
    exact ae_restrict_of_forall_mem measurableSet_Ioo hconst
  rw [dcArcLength_sq_eq_iff g γ hab hs hs2, hL]
  have hdiv : k * (b - a) / (b - a) = k := by field_simp
  rw [hdiv]
  exact hae

/-! ### Minimizing geodesics minimize energy -/

/-- **Math.** do Carmo Ch. 9, §2, `lem:dc-ch9-2-3` (the inequality).  **A minimizing
geodesic minimizes energy:** if `γ` is a geodesic on `(a,b)` which is no longer than a
competitor `c`, then
$$E(\gamma) \le E(c).$$

This is do Carmo's chain verbatim:
$$(b-a)\,E(\gamma) = L(\gamma)^2 \le L(c)^2 \le (b-a)\,E(c),$$
the outer steps being `dcArcLength_sq_eq_mul_dcEnergy_of_isGeodesicOn` (equality for
the geodesic) and `dcArcLength_sq_le_mul_dcEnergy` (`lem:dc-ch9-2-2-schwarz`, the
Schwarz comparison for `c`), and the middle step the minimality hypothesis.

Minimality is taken as `L(γ) ≤ L(c)` — the only consequence of "γ is minimizing" the
proof uses.  To derive that from a metric hypothesis (`d(p,q) = L(γ)`), compose with
`dcArcLength_le_of_pathELength_le` (`Variation/ArcLengthBridge.lean`). -/
theorem dcEnergy_le_of_dcArcLength_le
    {g : RiemannianMetric I M} {γ c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ (Ioo a b))
    (hcont : ContinuousOn γ (Ioo a b))
    (hmin : DCArcLength g γ a b ≤ DCArcLength g c a b)
    (hγs : IntervalIntegrable (dcSpeed g γ) volume a b)
    (hγs2 : IntervalIntegrable (fun t => (dcSpeed g γ t) ^ 2) volume a b)
    (hcs : IntervalIntegrable (dcSpeed g c) volume a b)
    (hcs2 : IntervalIntegrable (fun t => (dcSpeed g c t) ^ 2) volume a b) :
    DCEnergy g γ a b ≤ DCEnergy g c a b := by
  have hba : (0 : ℝ) < b - a := by linarith
  have heq : (DCArcLength g γ a b) ^ 2 = (b - a) * DCEnergy g γ a b :=
    dcArcLength_sq_eq_mul_dcEnergy_of_isGeodesicOn hab hγ hcont hγs hγs2
  have hle : (DCArcLength g c a b) ^ 2 ≤ (b - a) * DCEnergy g c a b :=
    dcArcLength_sq_le_mul_dcEnergy g c hab.le hcs hcs2
  have hnn : 0 ≤ DCArcLength g γ a b := by
    rw [dcArcLength_eq_integral_dcSpeed]
    exact intervalIntegral.integral_nonneg hab.le fun t _ => dcSpeed_nonneg g γ t
  have hsq : (DCArcLength g γ a b) ^ 2 ≤ (DCArcLength g c a b) ^ 2 := by
    have := mul_self_le_mul_self hnn hmin
    nlinarith [this]
  nlinarith [heq, hle, hsq, hba]

/-! ### The equality case

do Carmo: "If equality holds, then `(L(c))² = aE(c)`, so the parameter of `c` is
proportional to arc length, and `L(γ) = L(c)`, so `c` is a minimizing geodesic (see
`cor:dc-ch3-3-9`)."  The two conclusions he extracts before invoking `cor:dc-ch3-3-9`
are the two lemmas below. -/

/-- **Math.** do Carmo Ch. 9, §2, `lem:dc-ch9-2-3` (equality case, first conclusion).
If a competitor `c` attains the minimal energy, its **parameter is proportional to arc
length**: the speed `|dc/dt|` is a.e. constant.

do Carmo's "if equality holds, then `(L(c))² = aE(c)`, so the parameter of `c` is
proportional to arc length".  This is what he feeds to `cor:dc-ch3-3-9`; note it is
weaker than that corollary's hypothesis, which wants proportional arc length
*pointwise* rather than almost everywhere (the residual, **I-0355**). -/
theorem dcSpeed_ae_const_of_dcEnergy_eq
    {g : RiemannianMetric I M} {γ c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ (Ioo a b))
    (hcont : ContinuousOn γ (Ioo a b))
    (hmin : DCArcLength g γ a b ≤ DCArcLength g c a b)
    (hγs : IntervalIntegrable (dcSpeed g γ) volume a b)
    (hγs2 : IntervalIntegrable (fun t => (dcSpeed g γ t) ^ 2) volume a b)
    (hcs : IntervalIntegrable (dcSpeed g c) volume a b)
    (hcs2 : IntervalIntegrable (fun t => (dcSpeed g c t) ^ 2) volume a b)
    (hE : DCEnergy g γ a b = DCEnergy g c a b) :
    dcSpeed g c =ᵐ[(volume : Measure ℝ).restrict (Ioc a b)]
      Function.const ℝ (DCArcLength g c a b / (b - a)) := by
  have hba : (0 : ℝ) < b - a := by linarith
  have heq : (DCArcLength g γ a b) ^ 2 = (b - a) * DCEnergy g γ a b :=
    dcArcLength_sq_eq_mul_dcEnergy_of_isGeodesicOn hab hγ hcont hγs hγs2
  have hle : (DCArcLength g c a b) ^ 2 ≤ (b - a) * DCEnergy g c a b :=
    dcArcLength_sq_le_mul_dcEnergy g c hab.le hcs hcs2
  have hnn : 0 ≤ DCArcLength g γ a b := by
    rw [dcArcLength_eq_integral_dcSpeed]
    exact intervalIntegral.integral_nonneg hab.le fun t _ => dcSpeed_nonneg g γ t
  have hsq : (DCArcLength g γ a b) ^ 2 ≤ (DCArcLength g c a b) ^ 2 := by
    have := mul_self_le_mul_self hnn hmin
    nlinarith [this]
  -- the chain collapses: every inequality in it is an equality
  have hceq : (DCArcLength g c a b) ^ 2 = (b - a) * DCEnergy g c a b := by
    nlinarith [heq, hle, hsq, hba, hE]
  exact (dcArcLength_sq_eq_iff g c hab hcs hcs2).1 hceq

/-- **Math.** do Carmo Ch. 9, §2, `lem:dc-ch9-2-3` (equality case, second conclusion).
If a competitor `c` attains the minimal energy, then `L(γ) = L(c)`: **`c` is minimizing
too**.

do Carmo's "and `L(γ) = L(c)`, so `c` is a minimizing geodesic".  This is the other
fact he feeds to `cor:dc-ch3-3-9`; note it is weaker than that corollary's minimality
hypothesis, which is quantified over *every* competitor, not just this one `c`. -/
theorem dcArcLength_eq_of_dcEnergy_eq
    {g : RiemannianMetric I M} {γ c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ (Ioo a b))
    (hcont : ContinuousOn γ (Ioo a b))
    (hmin : DCArcLength g γ a b ≤ DCArcLength g c a b)
    (hγs : IntervalIntegrable (dcSpeed g γ) volume a b)
    (hγs2 : IntervalIntegrable (fun t => (dcSpeed g γ t) ^ 2) volume a b)
    (hcs : IntervalIntegrable (dcSpeed g c) volume a b)
    (hcs2 : IntervalIntegrable (fun t => (dcSpeed g c t) ^ 2) volume a b)
    (hE : DCEnergy g γ a b = DCEnergy g c a b) :
    DCArcLength g γ a b = DCArcLength g c a b := by
  have hba : (0 : ℝ) < b - a := by linarith
  have heq : (DCArcLength g γ a b) ^ 2 = (b - a) * DCEnergy g γ a b :=
    dcArcLength_sq_eq_mul_dcEnergy_of_isGeodesicOn hab hγ hcont hγs hγs2
  have hle : (DCArcLength g c a b) ^ 2 ≤ (b - a) * DCEnergy g c a b :=
    dcArcLength_sq_le_mul_dcEnergy g c hab.le hcs hcs2
  have hnn : 0 ≤ DCArcLength g γ a b := by
    rw [dcArcLength_eq_integral_dcSpeed]
    exact intervalIntegral.integral_nonneg hab.le fun t _ => dcSpeed_nonneg g γ t
  have hnnc : 0 ≤ DCArcLength g c a b := le_trans hnn hmin
  have hsq : (DCArcLength g γ a b) ^ 2 ≤ (DCArcLength g c a b) ^ 2 := by
    have := mul_self_le_mul_self hnn hmin
    nlinarith [this]
  -- the chain collapses, so the two squares agree; both lengths are non-negative
  have hsq_eq : (DCArcLength g γ a b) ^ 2 = (DCArcLength g c a b) ^ 2 := by
    nlinarith [heq, hle, hsq, hba, hE]
  nlinarith [hsq_eq, hnn, hnnc, hmin]

end Riemannian
