/-
Copyright (c) 2026 Archon Horizon. All rights reserved.
Released under Apache 2.0 license.
-/
import PoincareLib.Ch01.GeodesicSpeed
import PoincareLib.Ch01.GlobalExp
import OpenGALib.Riemannian.Exponential.MinimizingGeodesic
import OpenGALib.Riemannian.Exponential.UniformSegmentLength
import OpenGALib.Riemannian.Geodesic.IntrinsicUniqueness

/-!
# Poincaré Ch. 1 — the minimal restriction of a minimal geodesic is *unique*

This file closes **Part 1** of Morgan–Tian's `prop:minimal-geodesic-no-conjugate`:

> if `γ : [0,1] → M` is a minimal geodesic and `0 < t₀ < 1`, then `γ|[0,t₀]` is the **unique**
> minimal geodesic between its endpoints.

Together with Part 2 (`not_isConjugatePointAt_of_minimizing`,
`Ch01/MinimalGeodesicNoConjugate.lean`, landed in run 0118) this completes the proposition.

## Deviation from Morgan–Tian: no first variation with a corner

Morgan–Tian argue by the **first variation of energy at a corner**: if a second minimal geodesic
`μ` existed, the concatenation `c = μ ⋆ γ|[t₀,1]` would have a corner `Δ = γ′(t₀) − μ′(t₀) ≠ 0`,
and a variation with `Y(t₀) = Δ` would give `E′(0) = −|Δ|² < 0`, contradicting that `c` minimizes
energy.

We take a **shorter and strictly stronger route**, which reuses machinery already in OpenGALib and
needs no variation at all:

* `c` is piecewise `C¹`, parameterized proportionally to arclength, and realizes the distance
  between its endpoints (its length is `ℓ = ℓ(μ) + ℓ(γ|[t₀,1]) = d(γ 0, γ 1)`);
* therefore **`c` has no corner**: do Carmo's Cor. 3.9, formalized as
  `Riemannian.Exponential.isGeodesicOn_piecewise_of_arclength_edist`, says a minimizing
  piecewise-`C¹` arclength curve satisfies the geodesic equation at *every interior time* —
  **including the partition vertex `t₀`**.  (Under the hood this is exactly the corner-rigidity
  argument `eq_neg_of_forall_edist_expMap_eq`: two unit legs leaving `x` whose concatenation
  realizes `d = 2η` must leave in opposite directions.)
* so `c` is a genuine geodesic on `(0,1)`; it agrees with `γ` on `(t₀, 1)`, hence in position *and*
  chart velocity at any interior time there, so **ODE uniqueness**
  (`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) forces `c = γ` on all of `(0,1)`.  On `(0, t₀)`
  that reads `μ = γ`, and continuity closes the endpoints.

The first-variation route would have required generalising `exists_brokenVariationData` from a
*single geodesic* base curve to a *piecewise geodesic* one — a substantial refactor of the
broken-chart-variation machinery.  The corner-rigidity route sidesteps it entirely.  The
mathematical content is the same theorem of do Carmo that Morgan–Tian's first-variation argument
is a proof of; see the blueprint remark `rem:part1-corner-rigidity-route`.

## Hypothesis shape — and the one reduction that is *not* formalized here

Both geodesics are asked for on an **open time window with room at the ends** (`Ioo a b ⊇ [0,1]`
for `γ`, `Ioo a' b' ⊇ [0,t₀]` for `μ`); this is the same shape as
`not_isConjugatePointAt_of_minimizing`.  Morgan–Tian instead hand you a competitor
`μ : [0,t₀] → M` on the *closed* interval.  Bridging the two is a **routine but genuinely
unformalized** reduction, and it is stated here rather than buried:

* **Extension.**  A geodesic on `[0,t₀]` extends to `(-ε, t₀+ε)` by *local* ODE existence at the
  two endpoints — solve the geodesic equation from `(μ 0, μ′ 0)` backwards and from
  `(μ t₀, μ′ t₀)` forwards.  This needs **no completeness of `M`** (and note this file assumes
  only `[CompleteSpace E]`, completeness of the *model space*, which is not geodesic completeness
  of `M`; `globalGeodesic` is therefore *not* the discharge here).
* **Reparameterization.**  A competitor presented on `[0,1]` must be affinely rescaled to
  `[0,t₀]`; `globalGeodesic_smul` is the workspace's tool for that.

Neither bridge is proved in this file, so a caller supplying an arbitrary closed-interval `μ` must
do the reduction itself.

**But the caller that matters does not have to.**  The consumer of Part 1 is the injectivity clause
of `prop:exponential-diffeomorphism-cut-locus`, whose competitors are *radial* geodesics
`γ_v = globalGeodesic p v` — already defined on all of `ℝ`.  For those the extension hypothesis is
free, and `globalGeodesic_eqOn_of_minimizing` (bottom of this file) is stated with **no time-window
hypotheses at all**.  That is the form to reach for.

Blueprint: `prop:minimal-geodesic-no-conjugate` (Part 1).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.3;
do Carmo, *Riemannian Geometry*, Ch. 3, Cor. 3.9.
-/

open Set Filter Riemannian Riemannian.Geodesic Riemannian.Exponential
-- `open scoped Bundle` is **load-bearing**: mathlib's instance
-- `RiemannianBundle → NormedAddCommGroup (E b)` is *scoped to the `Bundle` namespace*
-- (`Mathlib/Topology/VectorBundle/Riemannian.lean`, priority 80).  Without it, synthesis of the
-- `ENorm (TangentSpace I x)` that `Manifold.pathELength` measures with falls back to the
-- **model-space** norm — a genuinely different (non-defeq) instance from the one baked into the
-- OpenGALib lemma statements, and every `rw` across the two fails.
open scoped Bundle ContDiff Manifold Topology ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ### The concatenation of two curves at a time -/

/-- **Math.** The **concatenation** of `μ` and `γ` at the time `t₀`: follow `μ` up to `t₀`, then
`γ`.  It is a genuine (continuous) curve exactly when `μ t₀ = γ t₀`. -/
def concatAt (t₀ : ℝ) (μ γ : ℝ → M) : ℝ → M := fun t => if t ≤ t₀ then μ t else γ t

/-- **Math.** Before the junction, the concatenation is `μ`. -/
theorem concatAt_eqOn_left (t₀ : ℝ) (μ γ : ℝ → M) : EqOn (concatAt t₀ μ γ) μ (Iic t₀) := by
  intro t ht
  simp only [concatAt, if_pos (mem_Iic.mp ht)]

/-- **Math.** After the junction, the concatenation is `γ` — *including at the junction itself*,
where the matching hypothesis `μ t₀ = γ t₀` is what makes the two readings agree. -/
theorem concatAt_eqOn_right {t₀ : ℝ} {μ γ : ℝ → M} (hmatch : μ t₀ = γ t₀) :
    EqOn (concatAt t₀ μ γ) γ (Ici t₀) := by
  intro t ht
  rcases eq_or_lt_of_le (mem_Ici.mp ht) with heq | hlt
  · simp only [concatAt, ← heq, if_pos le_rfl, hmatch]
  · simp only [concatAt, if_neg (not_le.mpr hlt)]

/-- **Math.** The three-point partition `0 < t₀ < 1` through the junction. -/
def cornerPartition (t₀ : ℝ) : ℕ → ℝ := fun i => if i = 0 then 0 else if i = 1 then t₀ else 1

@[simp] theorem cornerPartition_zero (t₀ : ℝ) : cornerPartition t₀ 0 = 0 := rfl
@[simp] theorem cornerPartition_one (t₀ : ℝ) : cornerPartition t₀ 1 = t₀ := rfl
@[simp] theorem cornerPartition_two (t₀ : ℝ) : cornerPartition t₀ 2 = 1 := rfl

/-! ### Clause 1 of Part 1: every restriction of a minimal geodesic is itself minimal -/

/-- **Math.** **`γ|[0,t]` is minimal, for every `t ∈ [0,1]`** — the *first* assertion of Part 1 of
`prop:minimal-geodesic-no-conjugate` ("the restriction of `γ` to `[0,t]` is **the unique minimal
geodesic** between its endpoints": this lemma is the *minimal*, `minimalGeodesic_restrict_unique`
the *unique*).

If `γ` is a geodesic on an open window `(a,b) ⊇ [0,1]` which is minimizing on `[0,1]` — its speed
`ℓ = √⟨γ′,γ′⟩`, which for a unit-time geodesic *is* its length, is at most `d(γ 0, γ 1)` — then for
every `t ∈ [0,1]`

`d(γ 0, γ t) = ℓ · t`,

i.e. the length `ℓ · t` of `γ|[0,t]` equals the distance between its endpoints.

*Proof.*  Morgan–Tian cut the competitor argument short with the triangle inequality, and so do we.
Minimality gives `d(γ 0, γ 1) = ℓ` (`dist_eq_sqrt_speedSq_of_minimizing`).  A geodesic is Lipschitz
with constant its speed (`IsGeodesicOn.dist_le`), and its speed is constant
(`IsGeodesicOn.speedSq_eq`), so `d(γ 0, γ t) ≤ ℓ t` and `d(γ t, γ 1) ≤ ℓ (1 - t)`.  Then

`ℓ = d(γ 0, γ 1) ≤ d(γ 0, γ t) + d(γ t, γ 1) ≤ d(γ 0, γ t) + ℓ (1 - t)`,

so `d(γ 0, γ t) ≥ ℓ t`, and the two bounds meet. ∎  (No competitor curve `σ` is ever produced: the
triangle inequality *is* the "shortcut then continue" argument, since `d` is already an infimum over
all curves.)

Blueprint: `prop:minimal-geodesic-no-conjugate` (Part 1, first assertion). -/
theorem dist_eq_speed_mul_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ : ℝ → M} {a b : ℝ}
    (ha : a < 0) (hb : 1 < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo a b)) (hγc : ContinuousOn γ (Ioo a b))
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (γ 0) (γ t) = Real.sqrt (speedSq (I := I) g γ 0) * t := by
  set ℓ : ℝ := Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g γ 0) with hℓdef
  have hIcc01 : Icc (0 : ℝ) 1 ⊆ Ioo a b := fun s hs =>
    ⟨lt_of_lt_of_le ha hs.1, lt_of_le_of_lt hs.2 hb⟩
  have h0 : (0 : ℝ) ∈ Ioo a b := hIcc01 ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Ioo a b := hIcc01 ⟨zero_le_one, le_rfl⟩
  have htab : t ∈ Ioo a b := hIcc01 ht
  have hd01 : dist (γ 0) (γ 1) = ℓ :=
    dist_eq_sqrt_speedSq_of_minimizing g hg hgeo isOpen_Ioo isPreconnected_Ioo hγc hIcc01 hmin
  have hℓt : Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g γ t) = ℓ := by
    rw [hℓdef]
    congr 1
    exact IsGeodesicOn.speedSq_eq (I := I) hgeo isOpen_Ioo isPreconnected_Ioo hγc htab h0
  have hdA : dist (γ 0) (γ t) ≤ ℓ * t := by
    have h := IsGeodesicOn.dist_le (I := I) g hg hgeo isOpen_Ioo isPreconnected_Ioo hγc
      h0 htab ht.1
    rwa [sub_zero] at h
  have hdB : dist (γ t) (γ 1) ≤ ℓ * (1 - t) := by
    have h := IsGeodesicOn.dist_le (I := I) g hg hgeo isOpen_Ioo isPreconnected_Ioo hγc
      htab h1 ht.2
    rwa [hℓt] at h
  refine le_antisymm hdA ?_
  have htri : dist (γ 0) (γ 1) ≤ dist (γ 0) (γ t) + dist (γ t) (γ 1) := dist_triangle _ _ _
  have hexp : ℓ * (1 - t) = ℓ - ℓ * t := by ring
  rw [hd01] at htri
  rw [hexp] at hdB
  linarith

/-! ### Clause 2 of Part 1: that minimal restriction is the *only* one

**A note on the `ENorm (TangentSpace I x)` instance — read this before touching `pathELength`.**
`Manifold.pathELength` measures with an `ENorm` on the tangent spaces, and *which* `ENorm` is not
automatic.  The norm induced by the Riemannian metric reaches `TangentSpace I x` through mathlib's
`RiemannianBundle → NormedAddCommGroup (E b)` instance, which is **`scoped` to the `Bundle`
namespace** (`Mathlib/Topology/VectorBundle/Riemannian.lean`, priority 80).  Every OpenGALib file
that states a `pathELength` lemma has `open Bundle` in force, so that is the instance baked into
their statements.  A file *without* `open scoped Bundle` synthesizes the **model-space** norm
instead — a genuinely different, **non-defeq** instance (a `show` between the two fails).  A
`letI : Bundle.RiemannianBundle …` does *not* repair this: it supplies the bundle, but the
`NormedAddCommGroup` step off it is still the scoped instance.

Symptom: `rw [Manifold.pathELength_congr …]` reports "did not find an occurrence of the pattern
`Manifold.pathELength I c 0 t`" in a goal that displays as exactly that.  Cure: `open scoped Bundle`
(done at the top of this file).  This is the sharp form of the warning `Ch01/BrokenEnergy.lean`
records as "stating them by hand picks a different route to the tangent `ENorm`". -/

set_option maxHeartbeats 1000000 in
/-- **Math.** **Part 1 of `prop:minimal-geodesic-no-conjugate`: the minimal restriction of a
minimal geodesic is unique.**

Let `γ` be a geodesic on an open window `(a, b) ⊇ [0, 1]` whose restriction to `[0, 1]` is
**minimizing** — in the workspace's normalisation (`Ch01/GeodesicSpeed.lean`), its speed, which for
a unit-time geodesic *is* its length, is at most `d(γ 0, γ 1)`.  Fix `0 < t₀ < 1` and let `μ` be
*any* geodesic on an open window `(a', b') ⊇ [0, t₀]` with the same endpoints as `γ|[0,t₀]` and
which is minimizing on `[0, t₀]` (its length `√⟨μ′,μ′⟩ · t₀` is at most `d(μ 0, μ t₀)`).  Then

`μ = γ` on `[0, t₀]`.

*Proof.*  Write `ℓ = √⟨γ′,γ′⟩`.  Minimality of `γ` gives `d(γ 0, γ 1) = ℓ`
(`dist_eq_sqrt_speedSq_of_minimizing`), and the triangle inequality against the Lipschitz bound
`IsGeodesicOn.dist_le` upgrades this to sub-arc minimality, `d(γ 0, γ t₀) = ℓ · t₀`.  The same
Lipschitz bound and the minimality of `μ` then pin `μ`'s speed: `√⟨μ′,μ′⟩ = ℓ`.

Let `c = concatAt t₀ μ γ`.  It is piecewise `C¹` for the partition `0 < t₀ < 1`, its
`Manifold.pathELength` from `0` to `t` is `ℓ · t` throughout `[0, 1]` (each leg is a geodesic of
speed `ℓ`; `IsGeodesicOn.pathELength_eq` and `pathELength_add`), and it realizes the distance
between its endpoints (`edist (c 0) (c 1) = ofReal ℓ`).  So `c` is a minimizing, arclength
piecewise-`C¹` curve, and **do Carmo's Cor. 3.9** — `isGeodesicOn_piecewise_of_arclength_edist` —
says it satisfies the geodesic equation on the *open* interval `(0, 1)`, **including at the
vertex `t₀`**: a minimizing broken geodesic has no corner.

Finally `c = γ` on `(t₀, 1)`, so `c` and `γ` agree in position and chart velocity at, say,
`t₁ = (t₀+1)/2`.  Both are geodesics on the open preconnected `(0, 1)`, so uniqueness of geodesics
(`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) gives `c = γ` on all of `(0, 1)`; on `(0, t₀)` that
is `μ = γ`, and the two endpoints are the matching hypotheses. ∎

Blueprint: `prop:minimal-geodesic-no-conjugate` (Part 1). -/
theorem eqOn_of_minimizing_geodesic_of_minimizing_geodesic
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ μ : ℝ → M} {a b a' b' t₀ : ℝ}
    (ha : a < 0) (hb : 1 < b) (ha' : a' < 0) (hb' : t₀ < b')
    (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo a b)) (hγc : ContinuousOn γ (Ioo a b))
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1))
    (hμgeo : IsGeodesicOn (I := I) g μ (Ioo a' b')) (hμc : ContinuousOn μ (Ioo a' b'))
    (hμ0 : μ 0 = γ 0) (hμt₀ : μ t₀ = γ t₀)
    (hμmin : Real.sqrt (speedSq (I := I) g μ 0) * t₀ ≤ dist (μ 0) (μ t₀)) :
    EqOn μ γ (Icc 0 t₀) := by
  classical
  -- The `ENorm` on the tangent spaces that `Manifold.pathELength` measures with must be the one
  -- the Riemannian bundle induces, not the model-space norm; installing the instance makes the
  -- rewrites below synthesize the same term the OpenGALib goals carry.
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- `PoincareLib.speedSq` is a *reducible abbreviation* of `Riemannian.Geodesic.speedSq`; the
  -- OpenGALib lemmas below produce the latter head symbol, so `rw` cannot cross the two.  Pin the
  -- hypotheses to the underlying name once (definitional, hence `exact`-able) and work there.
  have hminG : Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1) := hmin
  have hμminG : Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g μ 0) * t₀
      ≤ dist (μ 0) (μ t₀) := hμmin
  set ℓ : ℝ := Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g γ 0) with hℓdef
  have hℓ0 : 0 ≤ ℓ := Real.sqrt_nonneg _
  -- ### the time windows
  have hIcc01 : Icc (0 : ℝ) 1 ⊆ Ioo a b := fun t ht =>
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have h0 : (0 : ℝ) ∈ Ioo a b := hIcc01 ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Ioo a b := hIcc01 ⟨zero_le_one, le_rfl⟩
  have ht₀ab : t₀ ∈ Ioo a b := hIcc01 ⟨ht₀.le, ht₁.le⟩
  have hIcc0t : Icc (0 : ℝ) t₀ ⊆ Ioo a' b' := fun t ht =>
    ⟨lt_of_lt_of_le ha' ht.1, lt_of_le_of_lt ht.2 hb'⟩
  have h0' : (0 : ℝ) ∈ Ioo a' b' := hIcc0t ⟨le_rfl, ht₀.le⟩
  have ht₀' : t₀ ∈ Ioo a' b' := hIcc0t ⟨ht₀.le, le_rfl⟩
  -- ### `γ`: its length is the distance, and it is sub-arc minimizing
  have hd01 : dist (γ 0) (γ 1) = ℓ :=
    dist_eq_sqrt_speedSq_of_minimizing g hg hgeo isOpen_Ioo isPreconnected_Ioo hγc hIcc01 hmin
  -- the speed at the junction is the speed at `0` (geodesics have constant speed)
  have hℓt : Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g γ t₀) = ℓ := by
    rw [hℓdef]
    congr 1
    exact IsGeodesicOn.speedSq_eq (I := I) hgeo isOpen_Ioo isPreconnected_Ioo hγc ht₀ab h0
  -- **Clause 1**: `γ|[0,t₀]` is itself minimal — its length `ℓ t₀` *is* the endpoint distance
  have hdA' : dist (γ 0) (γ t₀) = ℓ * t₀ :=
    dist_eq_speed_mul_of_minimizing g hg ha hb hgeo hγc hmin ⟨ht₀.le, ht₁.le⟩
  -- ### `μ` has the same speed as `γ`
  have hdμ : dist (μ 0) (μ t₀) ≤ Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g μ 0) * t₀ := by
    have h := IsGeodesicOn.dist_le (I := I) g hg hμgeo isOpen_Ioo isPreconnected_Ioo hμc
      h0' ht₀' ht₀.le
    rwa [sub_zero] at h
  have hdμ' : dist (μ 0) (μ t₀) = ℓ * t₀ := by rw [hμ0, hμt₀, hdA']
  have hℓμ : Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g μ 0) = ℓ := by
    rw [hdμ'] at hdμ hμminG
    exact mul_right_cancel₀ (ne_of_gt ht₀) (le_antisymm hμminG hdμ)
  -- ### the concatenated broken path
  set c : ℝ → M := concatAt t₀ μ γ with hcdef
  have hcL : EqOn c μ (Iic t₀) := concatAt_eqOn_left t₀ μ γ
  have hcR : EqOn c γ (Ici t₀) := concatAt_eqOn_right hμt₀
  have hc0 : c 0 = γ 0 := by rw [hcL (mem_Iic.mpr ht₀.le), hμ0]
  have hc1 : c 1 = γ 1 := hcR (mem_Ici.mpr ht₁.le)
  -- the two legs are `C¹`
  have hγC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Ioo a b) :=
    IsGeodesicOn.contMDiffOn (I := I) hgeo isOpen_Ioo hγc
  have hμC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 μ (Ioo a' b') :=
    IsGeodesicOn.contMDiffOn (I := I) hμgeo isOpen_Ioo hμc
  have hcC1L : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc 0 t₀) :=
    (hμC1.mono hIcc0t).congr fun t ht => hcL (mem_Iic.mpr ht.2)
  have hcC1R : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc t₀ 1) :=
    (hγC1.mono fun t ht => hIcc01 ⟨ht₀.le.trans ht.1, ht.2⟩).congr
      fun t ht => hcR (mem_Ici.mpr ht.1)
  -- ### the partition `0 < t₀ < 1`
  have hτmono : ∀ i < 2, cornerPartition t₀ i ≤ cornerPartition t₀ (i + 1) := by
    intro i hi
    interval_cases i
    · simpa using ht₀.le
    · simpa using ht₁.le
  have hcpiece : ∀ i < 2,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc (cornerPartition t₀ i) (cornerPartition t₀ (i + 1))) := by
    intro i hi
    interval_cases i
    · simpa using hcC1L
    · simpa using hcC1R
  -- ### **do Carmo Cor. 3.9**: a minimizing broken geodesic has no corner
  have hcgeo : IsGeodesicOn (I := I) g c (Ioo (cornerPartition t₀ 0) (cornerPartition t₀ 2)) := by
    refine isGeodesicOn_piecewise_of_arclength_edist (I := I) (n := 2) (τ := cornerPartition t₀)
      g hg hℓ0 hτmono hcpiece ?_ ?_
    · -- **arclength.**  The goal carries the library's own `RiemannianBundle` instance; only
      -- instance-polymorphic rewrites and OpenGALib lemmas are used, never a hand-written type.
      intro t ht
      simp only [cornerPartition_zero, cornerPartition_two, sub_zero] at ht ⊢
      rcases le_or_gt t t₀ with hle | hgt
      · -- below the junction the broken path *is* `μ`
        rw [Manifold.pathELength_congr
              (show EqOn c μ (Icc 0 t) from fun s hs => hcL (mem_Iic.mpr (hs.2.trans hle))),
          IsGeodesicOn.pathELength_eq (I := I) hμgeo isOpen_Ioo isPreconnected_Ioo hμc h0'
            (hIcc0t ⟨ht.1, hle⟩), hℓμ, sub_zero]
      · -- above the junction: split the run at `t₀`, one geodesic leg on each side
        rw [← Manifold.pathELength_add (I := I) (γ := c) ht₀.le hgt.le,
          Manifold.pathELength_congr
            (show EqOn c μ (Icc 0 t₀) from fun s hs => hcL (mem_Iic.mpr hs.2)),
          Manifold.pathELength_congr
            (show EqOn c γ (Icc t₀ t) from fun s hs => hcR (mem_Ici.mpr hs.1)),
          IsGeodesicOn.pathELength_eq (I := I) (b := t₀) hμgeo isOpen_Ioo isPreconnected_Ioo hμc
            h0' ht₀',
          IsGeodesicOn.pathELength_eq (I := I) (b := t) hgeo isOpen_Ioo isPreconnected_Ioo hγc
            ht₀ab (hIcc01 ⟨ht₀.le.trans hgt.le, ht.2⟩),
          hℓμ, hℓt, sub_zero,
          ← ENNReal.ofReal_add (mul_nonneg hℓ0 ht₀.le) (mul_nonneg hℓ0 (by linarith))]
        congr 1
        ring
    · -- the broken path realizes the distance between its endpoints
      simp only [cornerPartition_zero, cornerPartition_two, sub_zero, mul_one]
      rw [hc0, hc1, edist_dist, hd01]
  simp only [cornerPartition_zero, cornerPartition_two] at hcgeo
  -- ### `c` and `γ` are both geodesics on `(0, 1)`
  have hIoo01 : Ioo (0 : ℝ) 1 ⊆ Ioo a b := fun t ht =>
    hIcc01 ⟨ht.1.le, ht.2.le⟩
  have hγgeo01 : IsGeodesicOn (I := I) g γ (Ioo 0 1) := hgeo.mono hIoo01
  have hγc01 : ContinuousOn γ (Ioo (0 : ℝ) 1) := hγc.mono hIoo01
  have hcc01 : ContinuousOn c (Ioo (0 : ℝ) 1) := by
    refine ContinuousOn.mono ?_ Ioo_subset_Icc_self
    rw [show Icc (0 : ℝ) 1 = Icc 0 t₀ ∪ Icc t₀ 1 from (Icc_union_Icc_eq_Icc ht₀.le ht₁.le).symm]
    exact hcC1L.continuousOn.union_of_isClosed hcC1R.continuousOn isClosed_Icc isClosed_Icc
  -- ### `c = γ` near `t₁ = (t₀ + 1)/2`, hence in position and chart velocity there
  set t₁ : ℝ := (t₀ + 1) / 2 with ht₁def
  have ht₁L : t₀ < t₁ := by rw [ht₁def]; linarith
  have ht₁R : t₁ < 1 := by rw [ht₁def]; linarith
  have hnhds : Ioo t₀ 1 ∈ 𝓝 t₁ := Ioo_mem_nhds ht₁L ht₁R
  have hpos : c t₁ = γ t₁ := hcR (mem_Ici.mpr ht₁L.le)
  have hchart : deriv (chartReading (I := I) (γ t₁) c) t₁
      = deriv (chartReading (I := I) (γ t₁) γ) t₁ := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hnhds] with s hs
    simp only [chartReading_def, hcR (mem_Ici.mpr hs.1.le)]
  have hβ : c t₁ ∈ (chartAt H (γ t₁)).source := by
    rw [hpos]; exact mem_chart_source H (γ t₁)
  have ht₁mem : t₁ ∈ Ioo (0 : ℝ) 1 := ⟨lt_trans ht₀ ht₁L, ht₁R⟩
  -- ### uniqueness of geodesics on the open preconnected `(0, 1)`
  have heqOn : EqOn c γ (Ioo (0 : ℝ) 1) :=
    IsGeodesicOn.eqOn_of_deriv_chartReading_eq (I := I) (β := γ t₁) isOpen_Ioo isPreconnected_Ioo
      hcgeo hγgeo01 hcc01 hγc01 ht₁mem hpos hβ hchart
  -- ### read off `μ = γ` on `[0, t₀]`
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0eq | h0lt
  · rw [← h0eq]; exact hμ0
  rcases eq_or_lt_of_le ht.2 with hteq | htlt
  · rw [hteq]; exact hμt₀
  · have htIoo : t ∈ Ioo (0 : ℝ) 1 := ⟨h0lt, htlt.trans ht₁⟩
    rw [← hcL (mem_Iic.mpr htlt.le)]
    exact heqOn htIoo

/-! ### The proposition, in Morgan–Tian's phrasing -/

/-- **Math.** **`prop:minimal-geodesic-no-conjugate`, Part 1, as Morgan–Tian state it.**

If `γ` is a minimal geodesic on `[0, 1]` and `t₀ < 1`, then the restriction `γ|[0,t₀]` is *the*
minimal geodesic between its endpoints: any minimal geodesic `μ` from `γ 0` to `γ t₀`,
parameterized by `[0, t₀]`, coincides with it.

This is `eqOn_of_minimizing_geodesic_of_minimizing_geodesic` with its hypotheses named the way the
text does.  The minimality of `μ` is written as `ℓ(μ) ≤ d(μ 0, μ t₀)` with
`ℓ(μ) = √⟨μ′, μ′⟩ · t₀` the length of a constant-speed curve on `[0, t₀]` — the same normalisation
as `γ`'s (`Ch01/GeodesicSpeed.lean`). -/
theorem minimalGeodesic_restrict_unique
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ μ : ℝ → M} {a b a' b' t₀ : ℝ}
    (ha : a < 0) (hb : 1 < b) (ha' : a' < 0) (hb' : t₀ < b')
    (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo a b)) (hγc : ContinuousOn γ (Ioo a b))
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1))
    (hμgeo : IsGeodesicOn (I := I) g μ (Ioo a' b')) (hμc : ContinuousOn μ (Ioo a' b'))
    (hμ0 : μ 0 = γ 0) (hμt₀ : μ t₀ = γ t₀)
    (hμmin : Real.sqrt (speedSq (I := I) g μ 0) * t₀ ≤ dist (μ 0) (μ t₀))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) :
    μ t = γ t :=
  eqOn_of_minimizing_geodesic_of_minimizing_geodesic g hg ha hb ha' hb' ht₀ ht₁ hgeo hγc hmin
    hμgeo hμc hμ0 hμt₀ hμmin ht

/-! ### The form the cut locus consumes: two *global* geodesics from `p` -/

/-- **Math.** **Part 1 for radial geodesics: two minimal `globalGeodesic`s from `p` reaching the
same point at time `t₀ < 1` coincide up to `t₀`.**

This is the shape `prop:exponential-diffeomorphism-cut-locus` actually consumes (condition (i) of
`def:cut-locus` is exactly "`γ_w` is the *unique* minimal geodesic from `p` to `exp_p w`"), and it
carries **no extension hypothesis at all**: `globalGeodesic` is defined on all of `ℝ` and is a
geodesic there (`isGeodesic_globalGeodesic`, `continuous_globalGeodesic`), so the open time windows
of `eqOn_of_minimizing_geodesic_of_minimizing_geodesic` are free — take `(-1, 2)` and `(-1, t₀+1)`.

`γ = globalGeodesic p v` is assumed minimizing on `[0, 1]` and `μ = globalGeodesic p w` minimizing
on `[0, t₀]`; both start at `p` (`globalGeodesic_zero`), and they are assumed to meet at `t₀`.  Then
they agree on all of `[0, t₀]`.

Blueprint: `prop:minimal-geodesic-no-conjugate` (Part 1); `prop:exponential-diffeomorphism-cut-locus`
(the injectivity clause). -/
theorem globalGeodesic_eqOn_of_minimizing [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {p : M}
    (v w : TangentSpace I p) {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
    (hmin : Real.sqrt (speedSq (I := I) g (globalGeodesic (I := I) g hg p v) 0)
      ≤ dist p (globalGeodesic (I := I) g hg p v 1))
    (hwmin : Real.sqrt (speedSq (I := I) g (globalGeodesic (I := I) g hg p w) 0) * t₀
      ≤ dist p (globalGeodesic (I := I) g hg p w t₀))
    (hmeet : globalGeodesic (I := I) g hg p w t₀ = globalGeodesic (I := I) g hg p v t₀) :
    EqOn (globalGeodesic (I := I) g hg p w) (globalGeodesic (I := I) g hg p v) (Icc 0 t₀) := by
  have hγ0 : globalGeodesic (I := I) g hg p v 0 = p := globalGeodesic_zero g hg p v
  have hμ0 : globalGeodesic (I := I) g hg p w 0 = p := globalGeodesic_zero g hg p w
  refine eqOn_of_minimizing_geodesic_of_minimizing_geodesic (I := I) g hg
    (a := -1) (b := 2) (a' := -1) (b' := t₀ + 1)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) ht₀ ht₁
    ((isGeodesic_globalGeodesic g hg p v).isGeodesicOn _)
    (continuous_globalGeodesic g hg p v).continuousOn
    (by rw [hγ0]; exact hmin)
    ((isGeodesic_globalGeodesic g hg p w).isGeodesicOn _)
    (continuous_globalGeodesic g hg p w).continuousOn
    (by rw [hγ0, hμ0]) hmeet
    (by rw [hμ0]; exact hwmin)

end PoincareLib

end

#print axioms PoincareLib.dist_eq_speed_mul_of_minimizing
#print axioms PoincareLib.concatAt_eqOn_left
#print axioms PoincareLib.concatAt_eqOn_right
#print axioms PoincareLib.eqOn_of_minimizing_geodesic_of_minimizing_geodesic
#print axioms PoincareLib.minimalGeodesic_restrict_unique
#print axioms PoincareLib.globalGeodesic_eqOn_of_minimizing
