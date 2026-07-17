import PoincareLib.Ch01.ExpBallDiffeo

/-!
# Morgan–Tian Ch. 1, §1.5 — the cut locus and the injectivity radius

`prop:injectivity-radius-volume` and `thm:volume-injectivity-radius` — the result Morgan–Tian
call "the more important, indeed crucial, result for our purposes" — are statements about the
**injectivity radius**. Neither could be *stated* in this workspace: `expMapGlobal` is defined on
all of `T_pM` (Hopf–Rinow), with no cut-time cutoff, and no cut locus, injectivity radius,
segment domain or star-shaped domain existed in Lean. This file supplies them.

## The definitions

Along the geodesic `γ_v(t) = exp_p(t·v)`, "minimizing up to `t`" is the *metric* statement

  `d(p, γ_v(t)) = t · |v|_g`   (`IsMinimizingUpTo`),

and never an assertion about conjugate points — that equivalence is a theorem, not a definition.
The set of such `t` is an interval containing `0` (`IsMinimizingUpTo.mono`, the only real content
here: it is the triangle inequality squeezed against the constant-speed length bound). Its
supremum is the **cut time** `cutTime g p v`, taken in `ℝ≥0∞` because it is genuinely `⊤` on
`ℝⁿ` and on `H^n_k`.

* `cutTime g hg p v : ℝ≥0∞` — the cut time in direction `v`.
* `cutLocus g hg p : Set M` — the images `γ_v(cutTime v)` over the unit directions with finite cut
  time. Morgan–Tian's `C_p`.
* `injectivityRadius g hg p : ℝ≥0∞` — the infimum of the cut time over unit directions.
* `segmentDomain g hg p : Set (TangentSpace I p)` — the open star-shaped domain `U_p` of vectors
  strictly inside their cut time, on which `exp_p` is injective.

`segmentDomain` is star-shaped by construction (`segmentDomain_smul_mem`), which is the property
the volume argument actually consumes: it lets the polar decomposition of `PolarIntegral.lean` be
run on it.

## Scope

These are the definitions plus the facts that make them well-formed and non-vacuous. The deep
theorems about them — `exp_p : U_p → M ∖ C_p` is a diffeomorphism
(`prop:exponential-diffeomorphism-cut-locus`), the cut locus is null, and
`inj(p) > 0` — are *not* proved here; they are the next pieces, and each of them now at least has
a statable subject.

Blueprint: `def:cut-locus`, `def:injectivity-radius`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.5.
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]

/-! ## The constant-speed length bound along a radial geodesic -/

/-- **Math.** The radial geodesic has constant speed `|v|_g`, so it moves at most
`|v|_g · (t − s)` in metric distance between times `s ≤ t`. -/
theorem dist_globalGeodesic_le (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) {s t : ℝ} (hst : s ≤ t) :
    dist (globalGeodesic (I := I) g hg p v s) (globalGeodesic (I := I) g hg p v t)
      ≤ Real.sqrt (g.metricInner p v v) * (t - s) := by
  have hgeo : IsGeodesicOn (I := I) g (globalGeodesic (I := I) g hg p v) univ :=
    (isGeodesic_globalGeodesic g hg p v).isGeodesicOn univ
  have hcont : Continuous (globalGeodesic (I := I) g hg p v) :=
    continuous_globalGeodesic g hg p v
  have hspeed : speedSq (I := I) g (globalGeodesic (I := I) g hg p v) s
      = speedSq (I := I) g (globalGeodesic (I := I) g hg p v) 0 :=
    hgeo.speedSq_eq isOpen_univ isPreconnected_univ hcont.continuousOn (mem_univ s) (mem_univ 0)
  have h := hgeo.dist_le g hg isOpen_univ isPreconnected_univ hcont.continuousOn
    (mem_univ s) (mem_univ t) hst
  rwa [hspeed, speedSq_globalGeodesic g hg p v] at h

/-- **Math.** `d(p, γ_v(t)) ≤ t·|v|_g` for `t ≥ 0`: the radial geodesic from `p` to `γ_v(t)` has
length `t·|v|_g`, and the distance is at most the length of *some* path. -/
theorem dist_globalGeodesic_zero_le (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) {t : ℝ} (ht : 0 ≤ t) :
    dist p (globalGeodesic (I := I) g hg p v t) ≤ Real.sqrt (g.metricInner p v v) * t := by
  have h := dist_globalGeodesic_le (I := I) g hg p v ht
  rwa [globalGeodesic_zero g hg p v, sub_zero] at h

/-! ## Minimizing times and the cut time -/

/-- **Math.** The radial geodesic `γ_v` is **minimizing up to time `t`**: the geodesic from `p` to
`γ_v(t)` realises the distance, `d(p, γ_v(t)) = t·|v|_g`.

This is a purely metric condition. The equivalent characterisations (no conjugate point before
`t`, uniqueness of the minimizing geodesic) are theorems about it, not its definition. -/
def IsMinimizingUpTo (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) (t : ℝ) : Prop :=
  dist p (globalGeodesic (I := I) g hg p v t) = Real.sqrt (g.metricInner p v v) * t

theorem isMinimizingUpTo_zero (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) : IsMinimizingUpTo (I := I) g hg p v 0 := by
  simp [IsMinimizingUpTo, globalGeodesic_zero g hg p v]

/-- **Math.** **Minimizing is downward closed**: if `γ_v` is minimizing up to `t`, it is minimizing
up to every `s ∈ [0,t]`. This is the only real content of the file, and it is the triangle
inequality squeezed against the length bound:
`t|v| = d(p,γ(t)) ≤ d(p,γ(s)) + d(γ(s),γ(t)) ≤ s|v| + (t−s)|v| = t|v|`,
so both inequalities are equalities. It is what makes the set of minimizing times an interval and
hence its supremum a genuine *cut* time. -/
theorem IsMinimizingUpTo.mono (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) {s t : ℝ} (ht : IsMinimizingUpTo (I := I) g hg p v t)
    (hs : 0 ≤ s) (hst : s ≤ t) : IsMinimizingUpTo (I := I) g hg p v s := by
  set ℓ : ℝ := Real.sqrt (g.metricInner p v v) with hℓ
  have h1 : dist p (globalGeodesic (I := I) g hg p v s) ≤ ℓ * s :=
    dist_globalGeodesic_zero_le (I := I) g hg p v hs
  have h2 : dist (globalGeodesic (I := I) g hg p v s) (globalGeodesic (I := I) g hg p v t)
      ≤ ℓ * (t - s) := dist_globalGeodesic_le (I := I) g hg p v hst
  have htri : dist p (globalGeodesic (I := I) g hg p v t)
      ≤ dist p (globalGeodesic (I := I) g hg p v s)
        + dist (globalGeodesic (I := I) g hg p v s) (globalGeodesic (I := I) g hg p v t) :=
    dist_triangle _ _ _
  rw [IsMinimizingUpTo] at ht ⊢
  -- `ℓ*t ≤ d(p,γ s) + ℓ*(t−s)`, so `ℓ*s ≤ d(p,γ s)`; with `h1` this forces equality.
  have hlow : ℓ * s ≤ dist p (globalGeodesic (I := I) g hg p v s) := by nlinarith [ht, htri, h2]
  linarith [h1, hlow]

/-- **Math.** The set of times up to which the radial geodesic `γ_v` is minimizing. By
`IsMinimizingUpTo.mono` it is an interval containing `0`. -/
def minimizingTimes (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ IsMinimizingUpTo (I := I) g hg p v t}

theorem zero_mem_minimizingTimes (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) : (0 : ℝ) ∈ minimizingTimes (I := I) g hg p v :=
  ⟨le_refl 0, isMinimizingUpTo_zero (I := I) g hg p v⟩

theorem minimizingTimes_ordConnected (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) : (minimizingTimes (I := I) g hg p v).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ⟨le_trans hx.1 hz.1, ?_⟩⟩
  exact IsMinimizingUpTo.mono (I := I) g hg p v hy.2 (le_trans hx.1 hz.1) hz.2

/-- **Math.** The **cut time** of `p` in the direction `v`: the supremum of the times up to which
the radial geodesic `γ_v` is minimizing. Taken in `ℝ≥0∞` because it is genuinely `⊤` in the
directions of `ℝⁿ` and of `H^n_k`, where geodesics minimize forever.

Blueprint: `def:cut-locus`. -/
def cutTime (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) : ℝ≥0∞ :=
  ⨆ t ∈ minimizingTimes (I := I) g hg p v, ENNReal.ofReal t

/-- **Math.** The cut time dominates every minimizing time — the elimination rule for the
supremum. -/
theorem le_cutTime (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) {t : ℝ} (ht : t ∈ minimizingTimes (I := I) g hg p v) :
    ENNReal.ofReal t ≤ cutTime (I := I) g hg p v :=
  le_iSup₂ (f := fun t (_ : t ∈ minimizingTimes (I := I) g hg p v) => ENNReal.ofReal t) t ht

/-! ## The cut locus, the injectivity radius, and the segment domain -/

/-- **Math.** The **cut locus** `C_p` of `p`: the set of cut points `γ_v(cutTime v)` over the unit
directions `v` whose cut time is finite.

Blueprint: `def:cut-locus`. -/
def cutLocus (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) : Set M :=
  {x : M | ∃ v : TangentSpace I p, g.metricInner p v v = 1 ∧
    ∃ c : ℝ, 0 ≤ c ∧ cutTime (I := I) g hg p v = ENNReal.ofReal c ∧
      x = globalGeodesic (I := I) g hg p v c}

/-- **Math.** The **injectivity radius** at `p`: the infimum of the cut time over the unit
directions. `exp_p` is injective on the ball of this radius — a theorem, not part of the
definition.

Blueprint: `def:injectivity-radius`. -/
def injectivityRadius (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) : ℝ≥0∞ :=
  ⨅ v : {v : TangentSpace I p // g.metricInner p v v = 1}, cutTime (I := I) g hg p (v : TangentSpace I p)

theorem injectivityRadius_le_cutTime (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {v : TangentSpace I p} (hv : g.metricInner p v v = 1) :
    injectivityRadius (I := I) g hg p ≤ cutTime (I := I) g hg p v :=
  iInf_le (fun w : {w : TangentSpace I p // g.metricInner p w w = 1} =>
    cutTime (I := I) g hg p (w : TangentSpace I p)) ⟨v, hv⟩

/-- **Math.** The **segment domain** `U_p ⊆ T_pM`: the vectors `v` lying strictly inside their own
cut time, i.e. `1 < cutTime(v)` in the sense that `γ_v` is still minimizing past parameter `1`.
Equivalently `U_p = {t·w : |w|_g = 1, 0 ≤ t < cutTime(w)}`. This is the domain on which `exp_p` is
injective, and it is star-shaped about the origin by construction.

Blueprint: `def:cut-locus` (the domain `U_p` of `prop:exponential-diffeomorphism-cut-locus`). -/
def segmentDomain (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    Set (TangentSpace I p) :=
  {v : TangentSpace I p | 1 < cutTime (I := I) g hg p v}

/-- **Math.** Rescaling the direction reparameterises the minimizing condition: `γ_{c·v}` is
minimizing up to `t` exactly when `γ_v` is minimizing up to `c·t`. Both sides say the same
geodesic segment realises the distance; only the parameter is stretched. -/
theorem isMinimizingUpTo_smul (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    IsMinimizingUpTo (I := I) g hg p (c • v) t ↔ IsMinimizingUpTo (I := I) g hg p v (c * t) := by
  have hgeo : globalGeodesic (I := I) g hg p (c • v) t
      = globalGeodesic (I := I) g hg p v (c * t) := by
    rw [globalGeodesic_smul g hg p v c]
  have hnorm : Real.sqrt (g.metricInner p (c • v) (c • v))
      = c * Real.sqrt (g.metricInner p v v) := by
    rw [g.metricInner_smul_left, g.metricInner_smul_right,
      show c * (c * g.metricInner p v v) = c ^ 2 * g.metricInner p v v by ring,
      Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  rw [IsMinimizingUpTo, IsMinimizingUpTo, hgeo, hnorm]
  constructor
  · intro h; rw [h]; ring
  · intro h; rw [h]; ring

/-- **Math.** `U_p` is **star-shaped** about the origin: if `v ∈ U_p` and `0 < c ≤ 1` then
`c·v ∈ U_p`. This is the property the polar decomposition of the volume integral consumes.

The cut time rescales as `cutTime(c·v) = cutTime(v)/c`; shrinking `c` can only push the cut
farther out in the rescaled parameter, so `1 < cutTime(v)` survives. -/
theorem segmentDomain_smul_mem (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {v : TangentSpace I p} (hv : v ∈ segmentDomain (I := I) g hg p) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1) : (c • v : TangentSpace I p) ∈ segmentDomain (I := I) g hg p := by
  rw [segmentDomain, mem_setOf_eq, cutTime, lt_iSup_iff] at hv
  obtain ⟨t, hlt⟩ := hv
  rw [lt_iSup_iff] at hlt
  obtain ⟨ht, h1t⟩ := hlt
  -- `t` is a minimizing time for `v` with `t > 1`; then `t/c ≥ t > 1` is one for `c·v`
  have ht1 : (1 : ℝ) < t := by
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd h1t (not_lt.mpr (by
      simpa using ENNReal.ofReal_le_ofReal hcon))
  have htc : t / c ∈ minimizingTimes (I := I) g hg p (c • v) := by
    refine ⟨by positivity, ?_⟩
    rw [isMinimizingUpTo_smul (I := I) g hg p v hc0]
    rw [mul_div_cancel₀ t (ne_of_gt hc0)]
    exact ht.2
  refine lt_of_lt_of_le ?_ (le_cutTime (I := I) g hg p (c • v) htc)
  have : (1 : ℝ) < t / c := lt_of_lt_of_le ht1 (le_div_self (by linarith) hc0 hc1)
  simpa using ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr this

end PoincareLib
