import DoCarmoLib.Riemannian.Variation.Energy
import DoCarmoLib.Riemannian.Variation.ArcLengthBridge
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.ConstantSpeed
import DoCarmoLib.Riemannian.Exponential.MinimizingGeodesic
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3

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

## Core comparison and minimizing-segment assembly

Steps (i) and (iii) are `dcArcLength_sq_eq_mul_dcEnergy_of_isGeodesicOn` and the
library's `dcArcLength_sq_le_mul_dcEnergy`; the chain is `dcEnergy_le_of_dcArcLength_le`.

The reusable core takes step (ii) directly as `L(γ) ≤ L(c)`.  The library's literal
predicate `Geodesic.IsMinimizingGeodesicSegment` instead quantifies over every
piecewise-`C¹` competitor using `Manifold.pathELength`, an `ℝ≥0∞` lower integral.
`DCArcLength` is an `ℝ` Bochner integral, so `ArcLengthBridge.lean` supplies the exact
conversion between the two length idioms.

On the canonical interval `[0,1]`,
`Geodesic.IsMinimizingGeodesicSegment.dcEnergy_le` packages the universal minimizing
hypothesis with that bridge and the core comparison.  This normalization matches the
project's minimizing-segment predicate and loses no mathematical content under the
standard affine reparametrization.

## The equality case

do Carmo's equality case ("equality iff `c` is a minimizing geodesic") splits into
three analytic conclusions, all of which are proved here:

* `dcSpeed_ae_const_of_dcEnergy_eq` — equality forces the speed of `c` to be a.e.
  constant, i.e. do Carmo's "the parameter of `c` is proportional to arc length";
* `pathELength_eq_of_dcEnergy_eq` — the a.e. statement integrates on every subinterval,
  giving the pointwise proportional-path-length identity used by `cor:dc-ch3-3-9`;
* `dcArcLength_eq_of_dcEnergy_eq` — equality forces `L(c) = L(γ)`, i.e. `c` is
  minimizing too.

These are what do Carmo feeds to `cor:dc-ch3-3-9` ("a curve whose length realizes the
distance and which is parametrized proportionally to arc length is a geodesic").
`Geodesic.IsMinimizingGeodesicSegment.geodesicOn_and_minimizing_of_dcEnergy_eq`
performs that final application: equality transfers the reference curve's universal
length bound to `c`, and the pointwise path-length identity makes `c` a geodesic on
the open interval.  The theorem returns both conclusions explicitly.

Finally,
`Geodesic.IsMinimizingGeodesicSegment.dcEnergy_eq_iff_geodesicOn_and_minimizing`
packages the full equality iff.  Its converse assumes the reference geodesic is also
presented as a piecewise-`C¹` curve, because the minimizing-segment predicate itself
stores continuity and the geodesic equation but not that separate presentation.

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
`cor:dc-ch3-3-9`)."  The analytic consequences he extracts before invoking
`cor:dc-ch3-3-9` are proved below. -/

/-- **Math.** do Carmo Ch. 9, §2, `lem:dc-ch9-2-3` (equality case, first conclusion).
If a competitor `c` attains the minimal energy, its **parameter is proportional to arc
length**: the speed `|dc/dt|` is a.e. constant.

do Carmo's "if equality holds, then `(L(c))² = aE(c)`, so the parameter of `c` is
proportional to arc length".  This is what he feeds to `cor:dc-ch3-3-9`; note it is
initially an almost-everywhere statement; `pathELength_eq_of_dcEnergy_eq` upgrades it
to the pointwise path-length identity. -/
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

/-! ### A.e.-constant speed gives pointwise proportional path length -/

/-- **Math.** If the speed is a.e. equal to `ℓ` on `(a,b]`, then the accumulated real
arc length on every subinterval `[a,t]` is `ℓ * (t - a)`. -/
theorem dcArcLength_eq_of_dcSpeed_ae_const
    (g : RiemannianMetric I M) (c : ℝ → M) {a b ℓ : ℝ}
    (hae : dcSpeed g c =ᵐ[(volume : Measure ℝ).restrict (Ioc a b)]
      Function.const ℝ ℓ) :
    ∀ t ∈ Icc a b, DCArcLength g c a t = ℓ * (t - a) := by
  have hae' : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc a b → dcSpeed g c s = ℓ := by
    have h := (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ioc).1 hae
    simpa only [Function.const_apply] using h
  intro t ht
  rw [dcArcLength_eq_integral_dcSpeed]
  have hcongr : (∫ s in a..t, dcSpeed g c s) = (∫ _s in a..t, ℓ) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le ht.1]
    filter_upwards [hae'] with s hs' hst'
    exact hs' ⟨hst'.1, hst'.2.trans ht.2⟩
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Math.** An a.e.-constant speed has the expected pointwise accumulated length.

The equality case of do Carmo's energy lemma first yields an a.e. statement on `Ioc a b`.
This theorem upgrades it to every endpoint `t ∈ Icc a b`: the interval integral ignores the
null exceptional set, and `ofReal_dcArcLength_eq_pathELength` then changes the real arc-length
integral into the `ENNReal` path length used by the minimizing-geodesic theorems. -/
theorem pathELength_eq_of_dcSpeed_ae_const
    (g : RiemannianMetric I M) (c : ℝ → M) {a b ℓ : ℝ} (hab : a ≤ b)
    (hs : IntervalIntegrable (dcSpeed g c) volume a b)
    (hae : dcSpeed g c =ᵐ[(volume : Measure ℝ).restrict (Ioc a b)]
      Function.const ℝ ℓ) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : ∀ x : M, NormedAddCommGroup (TangentSpace I x) :=
      fun x =>
        Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
    letI : ∀ x : M, ContinuousENorm (TangentSpace I x) :=
      fun _x => SeminormedAddGroup.toContinuousENorm
    ∀ t ∈ Icc a b,
      Manifold.pathELength I c a t = ENNReal.ofReal (ℓ * (t - a)) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  letI : ∀ x : M, NormedAddCommGroup (TangentSpace I x) :=
    fun x =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  letI : ∀ x : M, ContinuousENorm (TangentSpace I x) :=
    fun _x => SeminormedAddGroup.toContinuousENorm
  intro t ht
  have hst : IntervalIntegrable (dcSpeed g c) volume a t := by
    apply hs.mono_set
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  calc
    Manifold.pathELength I c a t = ENNReal.ofReal (DCArcLength g c a t) :=
      (ofReal_dcArcLength_eq_pathELength (I := I) g c ht.1 hst).symm
    _ = ENNReal.ofReal (ℓ * (t - a)) :=
      congrArg ENNReal.ofReal (dcArcLength_eq_of_dcSpeed_ae_const g c hae t ht)

/-- **Math.** Equality in the energy comparison makes the competitor pointwise
arc-length-proportional, with speed `L(c) / (b - a)`.  This is the exact parameter
hypothesis needed by the minimizing-curves-are-geodesics theorem. -/
theorem pathELength_eq_of_dcEnergy_eq
    {g : RiemannianMetric I M} {γ c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ (Ioo a b))
    (hcont : ContinuousOn γ (Ioo a b))
    (hmin : DCArcLength g γ a b ≤ DCArcLength g c a b)
    (hγs : IntervalIntegrable (dcSpeed g γ) volume a b)
    (hγs2 : IntervalIntegrable (fun t => (dcSpeed g γ t) ^ 2) volume a b)
    (hcs : IntervalIntegrable (dcSpeed g c) volume a b)
    (hcs2 : IntervalIntegrable (fun t => (dcSpeed g c t) ^ 2) volume a b)
    (hE : DCEnergy g γ a b = DCEnergy g c a b) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : ∀ x : M, NormedAddCommGroup (TangentSpace I x) :=
      fun x =>
        Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
    letI : ∀ x : M, ContinuousENorm (TangentSpace I x) :=
      fun _x => SeminormedAddGroup.toContinuousENorm
    ∀ t ∈ Icc a b, Manifold.pathELength I c a t =
      ENNReal.ofReal ((DCArcLength g c a b / (b - a)) * (t - a)) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  letI : ∀ x : M, NormedAddCommGroup (TangentSpace I x) :=
    fun x =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  letI : ∀ x : M, ContinuousENorm (TangentSpace I x) :=
    fun _x => SeminormedAddGroup.toContinuousENorm
  exact pathELength_eq_of_dcSpeed_ae_const g c hab.le hcs
    (dcSpeed_ae_const_of_dcEnergy_eq hab hγ hcont hmin hγs hγs2 hcs hcs2 hE)

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

/-! ### Assembly with the minimizing-geodesic predicate -/

/-- **Math.** On the canonical interval `[0,1]`, a minimizing geodesic has no more
energy than any piecewise-`C¹` competitor with the same endpoints.  This packages
`dcEnergy_le_of_dcArcLength_le` with the literal universal length comparison in
`Geodesic.IsMinimizingGeodesicSegment`. -/
theorem Geodesic.IsMinimizingGeodesicSegment.dcEnergy_le
    {g : RiemannianMetric I M} {γ c : ℝ → M}
    (hγmin : Geodesic.IsMinimizingGeodesicSegment (I := I) g γ 0 1)
    (hc : Geodesic.IsPiecewiseDifferentiableCurve (I := I) c 0 1)
    (hc0 : c 0 = γ 0) (hc1 : c 1 = γ 1)
    (hγs : IntervalIntegrable (dcSpeed g γ) volume 0 1)
    (hγs2 : IntervalIntegrable (fun t => (dcSpeed g γ t) ^ 2) volume 0 1)
    (hcs : IntervalIntegrable (dcSpeed g c) volume 0 1)
    (hcs2 : IntervalIntegrable (fun t => (dcSpeed g c t) ^ 2) volume 0 1) :
    DCEnergy g γ 0 1 ≤ DCEnergy g c 0 1 := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : ∀ x : M, NormedAddCommGroup (TangentSpace I x) :=
    fun x =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  letI : ∀ x : M, ContinuousENorm (TangentSpace I x) :=
    fun _x => SeminormedAddGroup.toContinuousENorm
  have hγgeo : Geodesic.IsGeodesicOn (I := I) g γ (Ioo 0 1) :=
    hγmin.2.1.2.mono Ioo_subset_Icc_self
  have hγcont : ContinuousOn γ (Ioo 0 1) :=
    hγmin.2.1.1.mono Ioo_subset_Icc_self
  have hγcPath : Manifold.pathELength I γ 0 1 ≤ Manifold.pathELength I c 0 1 :=
    hγmin.2.2 c hc hc0 hc1
  have hγc : DCArcLength g γ 0 1 ≤ DCArcLength g c 0 1 :=
    dcArcLength_le_of_pathELength_le g γ c zero_le_one hγs hcs hγcPath
  exact dcEnergy_le_of_dcArcLength_le zero_lt_one hγgeo hγcont hγc
    hγs hγs2 hcs hcs2

section MinimizingGeodesicEquality

variable [CompleteSpace E]
variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [T2Space (TangentBundle I M')]

/-- **Math.** Equality against a minimizing geodesic forces the competitor to be a
geodesic on the open interval and to minimize length against every piecewise-`C¹`
competitor.  This is the forward equality case of do Carmo Ch. 9, §2, Lemma 2.3,
including the final application of Ch. 3, Corollary 3.9. -/
theorem Geodesic.IsMinimizingGeodesicSegment.geodesicOn_and_minimizing_of_dcEnergy_eq
    (g : RiemannianMetric I M') (hg : g.IsRiemannianDist) {γ c : ℝ → M'}
    (hγmin : Geodesic.IsMinimizingGeodesicSegment (I := I) g γ 0 1)
    (hc : Geodesic.IsPiecewiseDifferentiableCurve (I := I) c 0 1)
    (hc0 : c 0 = γ 0) (hc1 : c 1 = γ 1)
    (hγs : IntervalIntegrable (dcSpeed g γ) volume 0 1)
    (hγs2 : IntervalIntegrable (fun t => (dcSpeed g γ t) ^ 2) volume 0 1)
    (hcs : IntervalIntegrable (dcSpeed g c) volume 0 1)
    (hcs2 : IntervalIntegrable (fun t => (dcSpeed g c t) ^ 2) volume 0 1)
    (hE : DCEnergy g γ 0 1 = DCEnergy g c 0 1) :
    Geodesic.IsGeodesicOn (I := I) g c (Ioo 0 1) ∧
      (letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
          ⟨g.toRiemannianMetric⟩
       letI : ∀ x : M', NormedAddCommGroup (TangentSpace I x) :=
         fun x =>
           Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
       letI : ∀ x : M', ContinuousENorm (TangentSpace I x) :=
         fun _x => SeminormedAddGroup.toContinuousENorm
       ∀ σ : ℝ → M', Geodesic.IsPiecewiseDifferentiableCurve (I := I) σ 0 1 →
         σ 0 = c 0 → σ 1 = c 1 →
           Manifold.pathELength I c 0 1 ≤ Manifold.pathELength I σ 0 1) := by
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : ∀ x : M', NormedAddCommGroup (TangentSpace I x) :=
    fun x =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  letI : ∀ x : M', ContinuousENorm (TangentSpace I x) :=
    fun _x => SeminormedAddGroup.toContinuousENorm
  have hγgeo : Geodesic.IsGeodesicOn (I := I) g γ (Ioo 0 1) :=
    hγmin.2.1.2.mono Ioo_subset_Icc_self
  have hγcont : ContinuousOn γ (Ioo 0 1) :=
    hγmin.2.1.1.mono Ioo_subset_Icc_self
  have hγcPath : Manifold.pathELength I γ 0 1 ≤ Manifold.pathELength I c 0 1 :=
    hγmin.2.2 c hc hc0 hc1
  have hγc : DCArcLength g γ 0 1 ≤ DCArcLength g c 0 1 :=
    dcArcLength_le_of_pathELength_le g γ c zero_le_one hγs hcs hγcPath
  have hL : DCArcLength g γ 0 1 = DCArcLength g c 0 1 :=
    dcArcLength_eq_of_dcEnergy_eq zero_lt_one hγgeo hγcont hγc
      hγs hγs2 hcs hcs2 hE
  have hpath : Manifold.pathELength I c 0 1 = Manifold.pathELength I γ 0 1 := by
    calc
      Manifold.pathELength I c 0 1 = ENNReal.ofReal (DCArcLength g c 0 1) :=
        (ofReal_dcArcLength_eq_pathELength (I := I) g c zero_le_one hcs).symm
      _ = ENNReal.ofReal (DCArcLength g γ 0 1) := congrArg ENNReal.ofReal hL.symm
      _ = Manifold.pathELength I γ 0 1 :=
        ofReal_dcArcLength_eq_pathELength (I := I) g γ zero_le_one hγs
  have hminC1 :
      ∀ σ : ℝ → M', ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) →
        σ 0 = c 0 → σ 1 = c 1 →
          Manifold.pathELength I c 0 1 ≤ Manifold.pathELength I σ 0 1 := by
    intro σ hσ hσ0 hσ1
    have hσpw : Geodesic.IsPiecewiseDifferentiableCurve (I := I) σ 0 1 := by
      refine ⟨hσ.continuousOn, ⟨1, (fun i : ℕ => (i : ℝ)), Nat.zero_lt_one,
        by norm_num, by norm_num, ?_, ?_⟩⟩
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        norm_num
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        simpa using hσ
    calc
      Manifold.pathELength I c 0 1 = Manifold.pathELength I γ 0 1 := hpath
      _ ≤ Manifold.pathELength I σ 0 1 :=
        hγmin.2.2 σ hσpw (hσ0.trans hc0) (hσ1.trans hc1)
  rcases hc with ⟨_, n, τ, _, hτ0, hτn, hτstrict, hpieces⟩
  have hLnonneg : 0 ≤ DCArcLength g c 0 1 := by
    rw [dcArcLength_eq_integral_dcSpeed]
    exact intervalIntegral.integral_nonneg zero_le_one fun t _ => dcSpeed_nonneg g c t
  have harc :=
    pathELength_eq_of_dcEnergy_eq zero_lt_one hγgeo hγcont hγc
      hγs hγs2 hcs hcs2 hE
  have hgeo : Geodesic.IsGeodesicOn (I := I) g c (Ioo 0 1) := by
    have h := Exponential.isGeodesicOn_piecewise_of_arclength_forall_le
      (I := I) (ℓ := DCArcLength g c 0 1 / (1 - 0)) g hg
      (div_nonneg hLnonneg (by norm_num))
      (fun i hi => (hτstrict i hi).le) hpieces
      (by simpa [hτ0, hτn] using harc)
      (by simpa [hτ0, hτn] using hminC1)
    simpa [hτ0, hτn] using h
  refine ⟨hgeo, ?_⟩
  intro σ hσ hσ0 hσ1
  calc
    Manifold.pathELength I c 0 1 = Manifold.pathELength I γ 0 1 := hpath
    _ ≤ Manifold.pathELength I σ 0 1 :=
      hγmin.2.2 σ hσ (hσ0.trans hc0) (hσ1.trans hc1)

/-- **Math.** The complete equality characterization in do Carmo Ch. 9, §2,
Lemma 2.3, on `[0,1]`: equality of energies is equivalent to the competitor being
an interior geodesic which minimizes length among all piecewise-`C¹` curves with the
same endpoints. -/
theorem Geodesic.IsMinimizingGeodesicSegment.dcEnergy_eq_iff_geodesicOn_and_minimizing
    (g : RiemannianMetric I M') (hg : g.IsRiemannianDist) {γ c : ℝ → M'}
    (hγmin : Geodesic.IsMinimizingGeodesicSegment (I := I) g γ 0 1)
    (hγpw : Geodesic.IsPiecewiseDifferentiableCurve (I := I) γ 0 1)
    (hc : Geodesic.IsPiecewiseDifferentiableCurve (I := I) c 0 1)
    (hc0 : c 0 = γ 0) (hc1 : c 1 = γ 1)
    (hγs : IntervalIntegrable (dcSpeed g γ) volume 0 1)
    (hγs2 : IntervalIntegrable (fun t => (dcSpeed g γ t) ^ 2) volume 0 1)
    (hcs : IntervalIntegrable (dcSpeed g c) volume 0 1)
    (hcs2 : IntervalIntegrable (fun t => (dcSpeed g c t) ^ 2) volume 0 1) :
    DCEnergy g γ 0 1 = DCEnergy g c 0 1 ↔
      Geodesic.IsGeodesicOn (I := I) g c (Ioo 0 1) ∧
        (letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
            ⟨g.toRiemannianMetric⟩
         letI : ∀ x : M', NormedAddCommGroup (TangentSpace I x) :=
           fun x =>
             Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
         letI : ∀ x : M', ContinuousENorm (TangentSpace I x) :=
           fun _x => SeminormedAddGroup.toContinuousENorm
         ∀ σ : ℝ → M', Geodesic.IsPiecewiseDifferentiableCurve (I := I) σ 0 1 →
           σ 0 = c 0 → σ 1 = c 1 →
             Manifold.pathELength I c 0 1 ≤ Manifold.pathELength I σ 0 1) := by
  constructor
  · intro hE
    exact hγmin.geodesicOn_and_minimizing_of_dcEnergy_eq g hg hc hc0 hc1
      hγs hγs2 hcs hcs2 hE
  · rintro ⟨hcgeo, hcmin⟩
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : ∀ x : M', NormedAddCommGroup (TangentSpace I x) :=
      fun x =>
        Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
    letI : ∀ x : M', ContinuousENorm (TangentSpace I x) :=
      fun _x => SeminormedAddGroup.toContinuousENorm
    have hγgeo : Geodesic.IsGeodesicOn (I := I) g γ (Ioo 0 1) :=
      hγmin.2.1.2.mono Ioo_subset_Icc_self
    have hγcont : ContinuousOn γ (Ioo 0 1) :=
      hγmin.2.1.1.mono Ioo_subset_Icc_self
    have hccont : ContinuousOn c (Ioo 0 1) :=
      hc.1.mono Ioo_subset_Icc_self
    have hγcPath : Manifold.pathELength I γ 0 1 ≤ Manifold.pathELength I c 0 1 :=
      hγmin.2.2 c hc hc0 hc1
    have hcγPath : Manifold.pathELength I c 0 1 ≤ Manifold.pathELength I γ 0 1 :=
      hcmin γ hγpw hc0.symm hc1.symm
    have hγc : DCArcLength g γ 0 1 ≤ DCArcLength g c 0 1 :=
      dcArcLength_le_of_pathELength_le g γ c zero_le_one hγs hcs hγcPath
    have hcγ : DCArcLength g c 0 1 ≤ DCArcLength g γ 0 1 :=
      dcArcLength_le_of_pathELength_le g c γ zero_le_one hcs hγs hcγPath
    have hL : DCArcLength g γ 0 1 = DCArcLength g c 0 1 :=
      le_antisymm hγc hcγ
    have hγE : (DCArcLength g γ 0 1) ^ 2 = DCEnergy g γ 0 1 := by
      simpa using dcArcLength_sq_eq_mul_dcEnergy_of_isGeodesicOn
        zero_lt_one hγgeo hγcont hγs hγs2
    have hcE : (DCArcLength g c 0 1) ^ 2 = DCEnergy g c 0 1 := by
      simpa using dcArcLength_sq_eq_mul_dcEnergy_of_isGeodesicOn
        zero_lt_one hcgeo hccont hcs hcs2
    rw [hL] at hγE
    exact hγE.symm.trans hcE

end MinimizingGeodesicEquality

end Riemannian
