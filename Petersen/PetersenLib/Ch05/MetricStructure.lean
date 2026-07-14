import PetersenLib.Ch05.SpeedIntegrable

/-!
# Petersen Ch. 5, §5.3 — the metric structure of a Riemannian manifold

The definitional layer of Petersen §5.3: piecewise `C^∞` curves, the length of
a curve, the Riemannian distance `d(p, q) = |pq|` as the infimum of lengths of
piecewise smooth curves joining `p` and `q`, metric balls and set distance,
and segments (curves realizing the distance between their endpoints,
parametrized proportionally to arc length).

* `IsPiecewiseSmoothCurve γ a b` (`def:pet-ch5-piecewise-smooth-curve`) — `γ`
  is continuous on `Icc a b` and there is a finite partition
  `a = u 0 < u 1 < ⋯ < u n = b` on each closed piece of which `γ` is `C^∞` as
  a manifold map.
* `curveLength g γ a b` (`def:pet-ch5-curve-length`) — `∫ₐᵇ |ċ(t)| dt` where
  the speed `|ċ(t)|` is read via `curveSpeedSq` (`PetersenLib/Ch05/GeodesicSpeed.lean`).
* `riemannianDistance g p q` (`def:pet-ch5-distance`) — the infimum of
  `curveLength g γ 0 1` over piecewise smooth `γ : [0, 1] → M` from `p` to
  `q`, Petersen's `Ω_{p,q}`. The junk value on a non-path-connected manifold
  (where `Ω_{p,q} = ∅`) is `Real.sInf ∅ = 0`.
* `metricBall`, `metricClosedBall`, `setDistance` (`def:pet-ch5-metric-balls`)
  — the metric ball, closed metric ball, and the distance between two sets.
* `IsSegment g γ a b`, `segmentNotation g p q` (`def:pet-ch5-segment`) — a
  curve realizing the distance between its endpoints and parametrized
  proportionally to arc length, and the notation `\overline{pq}` for a chosen
  segment on `[0, |pq|]`; junk value `fun _ => p` when no such segment exists.

## Conventions

Petersen implicitly takes `a < b` in the definition of a piecewise `C^∞`
curve; the degenerate case `a ≤ b` (including `a = b`) is allowed here for
definitional convenience (e.g. constant curves), without affecting any of the
mathematical content: for `a = b` the single-point partition `n = 0` always
witnesses the property for a curve continuous at `a`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Piecewise smooth curves -/

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-piecewise-smooth-curve`): a curve
`γ : ℝ → M` is **piecewise `C^∞`** on `[a, b]` if it is continuous on `Icc a b`
and there is a finite partition `a = u 0 < u 1 < ⋯ < u n = b` (encoded as a
monotone `u : Fin (n + 1) → ℝ`) such that `γ` restricted to each closed piece
`Icc (u i) (u (i + 1))` is `C^∞` as a manifold map. -/
def IsPiecewiseSmoothCurve (γ : ℝ → M) (a b : ℝ) : Prop :=
  ContinuousOn γ (Icc a b) ∧
    ∃ (n : ℕ) (u : Fin (n + 1) → ℝ), Monotone u ∧ u 0 = a ∧ u (Fin.last n) = b ∧
      ∀ i : Fin n, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (u i.castSucc) (u i.succ))

/-- **Math.** A constant curve is piecewise smooth on any `[a, b]` with
`a ≤ b`: take the trivial one-piece partition with endpoints `a` and `b`. -/
theorem isPiecewiseSmoothCurve_const (p : M) {a b : ℝ} (hab : a ≤ b) :
    IsPiecewiseSmoothCurve (I := I) (fun _ : ℝ => p) a b := by
  refine ⟨continuousOn_const, 1, ![a, b], ?_, ?_, ?_, ?_⟩
  · exact Fin.monotone_iff_le_succ.2 (fun i => by fin_cases i; simpa using hab)
  · simp
  · simp
  · intro i
    fin_cases i
    simpa using contMDiffOn_const

/-- **Math.** A function agreeing on `[a, b]` with a piecewise smooth curve is
piecewise smooth on `[a, b]`: continuity and piecewise smoothness only read
the curve on `[a, b]`, and every partition piece lies inside `[a, b]`. -/
theorem IsPiecewiseSmoothCurve.congr {γ γ' : ℝ → M} {a b : ℝ}
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b) (h : ∀ s ∈ Icc a b, γ' s = γ s) :
    IsPiecewiseSmoothCurve (I := I) γ' a b := by
  obtain ⟨hcont, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  refine ⟨hcont.congr h, n, u, hmono, hu0, hun, ?_⟩
  intro i
  refine (hsmooth i).congr ?_
  intro s hs
  refine h s ⟨?_, ?_⟩
  · calc a = u 0 := hu0.symm
      _ ≤ u i.castSucc := hmono (Fin.zero_le _)
      _ ≤ s := hs.1
  · calc s ≤ u i.succ := hs.2
      _ ≤ u (Fin.last n) := hmono (Fin.le_last _)
      _ = b := hun

/-- **Math.** Appending one further smooth piece `[m, b]` to a piecewise smooth
curve on `[a, m]` yields a piecewise smooth curve on `[a, b]`, with the
partition extended by the new endpoint (`Fin.snoc`). -/
theorem IsPiecewiseSmoothCurve.snoc {γ : ℝ → M} {a m b : ℝ}
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a m) (hmb : m ≤ b)
    (hcont : ContinuousOn γ (Icc a b))
    (hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc m b)) :
    IsPiecewiseSmoothCurve (I := I) γ a b := by
  obtain ⟨_, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  refine ⟨hcont, n + 1, Fin.snoc u b, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      induction i using Fin.lastCases with
      | last => simp
      | cast k =>
        rw [Fin.snoc_castSucc]
        calc u k ≤ u (Fin.last n) := hmono (Fin.le_last _)
          _ = m := hun
          _ ≤ b := hmb
    | cast k =>
      induction i using Fin.lastCases with
      | last =>
        exfalso
        simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hij
        omega
      | cast l =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hmono (Fin.castSucc_le_castSucc_iff.mp hij)
  · rw [← Fin.castSucc_zero, Fin.snoc_castSucc]
    exact hu0
  · rw [Fin.snoc_last]
  · intro i
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hun]
      exact hsm
    | cast j =>
      rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
      exact hsmooth j

private theorem trans_aux {γ : ℝ → M} {a c : ℝ}
    (hac : IsPiecewiseSmoothCurve (I := I) γ a c) :
    ∀ (n₂ : ℕ) (b : ℝ) (v : Fin (n₂ + 1) → ℝ), Monotone v → v 0 = c → v (Fin.last n₂) = b →
    (∀ i : Fin n₂, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (v i.castSucc) (v i.succ))) →
    ContinuousOn γ (Icc a b) →
    IsPiecewiseSmoothCurve (I := I) γ a b := by
  intro n₂
  induction n₂ with
  | zero =>
    intro b v _hv_mono hv0 hvlast _hv_smooth _hcont
    rw [Fin.last_zero] at hvlast
    have hb : b = c := hvlast.symm.trans hv0
    subst hb
    exact hac
  | succ n₂ ih =>
    intro b v hv_mono hv0 hvlast hv_smooth hcont
    have hc'b : v (Fin.castSucc (Fin.last n₂)) ≤ b := by
      rw [← hvlast]
      exact hv_mono (Fin.le_last _)
    have step1 : IsPiecewiseSmoothCurve (I := I) γ a (v (Fin.castSucc (Fin.last n₂))) := by
      refine ih (v (Fin.castSucc (Fin.last n₂))) (v ∘ Fin.castSucc) ?_ ?_ rfl ?_ ?_
      · intro i j hij
        exact hv_mono (Fin.castSucc_le_castSucc_iff.mpr hij)
      · exact hv0
      · intro i
        exact hv_smooth (Fin.castSucc i)
      · exact hcont.mono (Icc_subset_Icc_right hc'b)
    refine step1.snoc hc'b hcont ?_
    have hlast := hv_smooth (Fin.last n₂)
    rwa [Fin.succ_last, hvlast] at hlast

/-- **Math.** **Concatenation**: a curve piecewise smooth on `[a, c]` and on
`[c, b]` is piecewise smooth on `[a, b]` — concatenate the partitions and glue
continuity on the closed pieces. -/
theorem IsPiecewiseSmoothCurve.trans {γ : ℝ → M} {a c b : ℝ}
    (hac : IsPiecewiseSmoothCurve (I := I) γ a c)
    (hcb : IsPiecewiseSmoothCurve (I := I) γ c b) :
    IsPiecewiseSmoothCurve (I := I) γ a b := by
  obtain ⟨hcont1, n1, u, hu_mono, hu0, hulast, hu_smooth⟩ := hac
  obtain ⟨hcont2, n2, v, hv_mono, hv0, hvlast, hv_smooth⟩ := hcb
  have hac' : a ≤ c := by rw [← hu0, ← hulast]; exact hu_mono (Fin.zero_le _)
  have hcb' : c ≤ b := by rw [← hv0, ← hvlast]; exact hv_mono (Fin.zero_le _)
  have hcontab : ContinuousOn γ (Icc a b) := by
    rw [← Set.Icc_union_Icc_eq_Icc hac' hcb']
    exact hcont1.union_of_isClosed hcont2 isClosed_Icc isClosed_Icc
  exact trans_aux ⟨hcont1, n1, u, hu_mono, hu0, hulast, hu_smooth⟩ n2 b v hv_mono hv0 hvlast
    hv_smooth hcontab

/-! ## The length of a curve -/

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-curve-length`): the **length** of a
curve `γ : ℝ → M` on `[a, b]`, `L(γ) = ∫ₐᵇ |ċ(t)| dt = ∫ₐᵇ √(g(ċ(t), ċ(t))) dt`,
the speed being read via `curveSpeedSq`
(`PetersenLib/Ch05/GeodesicSpeed.lean`). -/
def curveLength (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sqrt (curveSpeedSq (I := I) g γ t)

@[simp] lemma curveLength_def (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    curveLength (I := I) g γ a b =
      ∫ t in a..b, Real.sqrt (curveSpeedSq (I := I) g γ t) := rfl

/-- **Math.** The length of `γ|_{[a,b]}` is nonnegative for `a ≤ b`: the
integrand `√(g(ċ, ċ))` is nonnegative. -/
theorem curveLength_nonneg (g : RiemannianMetric I M) (γ : ℝ → M) {a b : ℝ}
    (hab : a ≤ b) :
    0 ≤ curveLength (I := I) g γ a b :=
  intervalIntegral.integral_nonneg hab (fun _ _ => Real.sqrt_nonneg _)

/-- **Math.** A degenerate curve `γ|_{[a,a]}` has zero length. -/
@[simp] theorem curveLength_self (g : RiemannianMetric I M) (γ : ℝ → M) (a : ℝ) :
    curveLength (I := I) g γ a a = 0 :=
  intervalIntegral.integral_same

/-- **Math.** The squared speed of a constant curve vanishes: the chart-local
reading is constant, so its derivative is `0`, and the metric pairing of `0`
with itself is `0`. -/
@[simp] theorem curveSpeedSq_const (g : RiemannianMetric I M) (p : M) (t : ℝ) :
    curveSpeedSq (I := I) g (fun _ : ℝ => p) t = 0 := by
  have hconst : Geodesic.chartLocalCurve (I := I) (fun _ : ℝ => p) t =
      fun _ : ℝ => extChartAt I p p := rfl
  have hderiv : deriv (Geodesic.chartLocalCurve (I := I) (fun _ : ℝ => p) t) t = 0 := by
    rw [hconst]; exact deriv_const t (extChartAt I p p)
  rw [curveSpeedSq_def, hderiv]
  exact map_zero _

/-- **Math.** A constant curve has zero length on any `[a, b]`. -/
@[simp] theorem curveLength_const (g : RiemannianMetric I M) (p : M) (a b : ℝ) :
    curveLength (I := I) g (fun _ : ℝ => p) a b = 0 := by
  have h0 : (fun t : ℝ => Real.sqrt (curveSpeedSq (I := I) g (fun _ : ℝ => p) t))
      = fun _ : ℝ => (0 : ℝ) := by
    funext t
    rw [curveSpeedSq_const]
    exact Real.sqrt_zero
  show (∫ t in a..b, Real.sqrt (curveSpeedSq (I := I) g (fun _ : ℝ => p) t)) = 0
  rw [h0]
  simp

/-- **Math.** **Additivity of length**: for a curve `γ` and any three times
`a, c, b`, if `γ`'s speed is interval-integrable on `[a,c]` and on `[c,b]`,
then `L(γ)|_a^b = L(γ)|_a^c + L(γ)|_c^b`. (Petersen implicitly restricts to
`a ≤ c ≤ b`, but the identity holds unconditionally given integrability, by
the general interval-integral splitting rule.) -/
theorem curveLength_additive (g : RiemannianMetric I M) (γ : ℝ → M) {a c b : ℝ}
    (hac : IntervalIntegrable (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t))
      MeasureTheory.volume a c)
    (hcb : IntervalIntegrable (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t))
      MeasureTheory.volume c b) :
    curveLength (I := I) g γ a b =
      curveLength (I := I) g γ a c + curveLength (I := I) g γ c b :=
  (intervalIntegral.integral_add_adjacent_intervals hac hcb).symm

/-! ## Riemannian distance -/

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-distance`): the **Riemannian
distance** `d(p, q) = |pq|` between `p, q ∈ M`, the infimum of the lengths of
piecewise `C^∞` curves `γ : [0, 1] → M` with `γ 0 = p`, `γ 1 = q` — Petersen's
`Ω_{p,q}`. When no such curve exists (`Ω_{p,q} = ∅`, e.g. on a manifold that is
not path-connected), the junk value is `Real.sInf ∅ = 0`. -/
def riemannianDistance (g : RiemannianMetric I M) (p q : M) : ℝ :=
  sInf {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
    γ 0 = p ∧ γ 1 = q ∧ L = curveLength (I := I) g γ 0 1}

/-- **Math.** Every length in the distance-defining set is nonnegative: a
convenient restatement of `curveLength_nonneg` for the `Ω_{p,q}` set. -/
theorem forall_mem_riemannianDistanceSet_nonneg (g : RiemannianMetric I M) (p q : M) :
    ∀ L ∈ {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
      γ 0 = p ∧ γ 1 = q ∧ L = curveLength (I := I) g γ 0 1}, 0 ≤ L := by
  rintro L ⟨γ, -, -, -, rfl⟩
  exact curveLength_nonneg (I := I) g γ zero_le_one

/-- **Math.** The Riemannian distance is nonnegative: every candidate curve
length is nonnegative, and `Real.sInf` of a set of nonnegative reals is
nonnegative (regardless of emptiness, by the junk convention `sInf ∅ = 0`). -/
theorem riemannianDistance_nonneg (g : RiemannianMetric I M) (p q : M) :
    0 ≤ riemannianDistance (I := I) g p q :=
  Real.sInf_nonneg (forall_mem_riemannianDistanceSet_nonneg (I := I) g p q)

/-- **Math.** The Riemannian distance from a point to itself vanishes: the
constant curve at `p` is a piecewise smooth curve from `p` to `p` of length
`0`, and every length is nonnegative, so `0` is the infimum. -/
@[simp] theorem riemannianDistance_self (g : RiemannianMetric I M) (p : M) :
    riemannianDistance (I := I) g p p = 0 := by
  have hmem : (0 : ℝ) ∈ {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
      γ 0 = p ∧ γ 1 = p ∧ L = curveLength (I := I) g γ 0 1} :=
    ⟨fun _ => p, isPiecewiseSmoothCurve_const (I := I) p zero_le_one, rfl, rfl,
      (curveLength_const (I := I) g p 0 1).symm⟩
  have hbdd : BddBelow {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
      γ 0 = p ∧ γ 1 = p ∧ L = curveLength (I := I) g γ 0 1} :=
    ⟨0, forall_mem_riemannianDistanceSet_nonneg (I := I) g p p⟩
  exact le_antisymm (csInf_le hbdd hmem) (riemannianDistance_nonneg (I := I) g p p)

/-! ## Symmetry of the distance, via curve reversal -/

/-- **Math.** The squared speed of the **time-reversed** curve `s ↦ γ (a + b - s)`
at `t` equals the squared speed of `γ` at the mirrored time `a + b - t`: the
chart-local reading is precomposed with the reflection `s ↦ a + b - s`, whose
derivative negates the velocity without changing the (quadratic) metric
pairing `g(-v, -v) = g(v, v)`. -/
theorem curveSpeedSq_comp_const_sub (g : RiemannianMetric I M) (γ : ℝ → M)
    (a b t : ℝ) :
    curveSpeedSq (I := I) g (fun s => γ (a + b - s)) t =
      curveSpeedSq (I := I) g γ (a + b - t) := by
  have hcurve : Geodesic.chartLocalCurve (I := I) (fun s => γ (a + b - s)) t =
      fun s => Geodesic.chartLocalCurve (I := I) γ (a + b - t) (a + b - s) := rfl
  have hderiv : deriv (Geodesic.chartLocalCurve (I := I) (fun s => γ (a + b - s)) t) t
      = - deriv (Geodesic.chartLocalCurve (I := I) γ (a + b - t)) (a + b - t) := by
    rw [hcurve]
    exact deriv_comp_const_sub (Geodesic.chartLocalCurve (I := I) γ (a + b - t)) (a + b) t
  rw [curveSpeedSq_def, hderiv, curveSpeedSq_def]
  set v := deriv (Geodesic.chartLocalCurve (I := I) γ (a + b - t)) (a + b - t) with hv_def
  show g.inner (γ (a + b - t)) (-v) (-v) = g.inner (γ (a + b - t)) v v
  calc g.inner (γ (a + b - t)) (-v) (-v)
      = -(g.inner (γ (a + b - t)) v (-v)) :=
        ContinuousLinearMap.map_neg₂ (g.inner (γ (a + b - t))) v (-v)
    _ = -(-(g.inner (γ (a + b - t)) v v)) :=
        congrArg Neg.neg (map_neg (g.inner (γ (a + b - t)) v) v)
    _ = g.inner (γ (a + b - t)) v v := neg_neg _

/-- **Math.** The time-reversal of a piecewise `C^∞` curve on `[a, b]` is
again piecewise `C^∞` on `[a, b]`: the reversed partition
`u' i = a + b - u (\mathrm{rev}\ i)` is monotone with the same endpoints, and
each piece is the composite of `γ` (smooth on the mirrored piece) with the
smooth reflection `s ↦ a + b - s`. -/
theorem isPiecewiseSmoothCurve_comp_const_sub {γ : ℝ → M} {a b : ℝ}
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b) :
    IsPiecewiseSmoothCurve (I := I) (fun s => γ (a + b - s)) a b := by
  obtain ⟨hcont, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  have hreflect_cont : ContinuousOn (fun t : ℝ => a + b - t) (Icc a b) :=
    (continuous_const.sub continuous_id).continuousOn
  have hreflect_maps : MapsTo (fun t : ℝ => a + b - t) (Icc a b) (Icc a b) := by
    rintro t ⟨ht1, ht2⟩
    exact ⟨by linarith, by linarith⟩
  refine ⟨hcont.comp hreflect_cont hreflect_maps, n, fun i => a + b - u (Fin.rev i),
    ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h := hmono (Fin.rev_le_rev.mpr hij)
    dsimp only
    linarith
  · show a + b - u (Fin.rev 0) = a
    rw [Fin.rev_zero, hun]; ring
  · show a + b - u (Fin.rev (Fin.last n)) = b
    rw [Fin.rev_last, hu0]; ring
  · intro i
    have hpiece := hsmooth (Fin.rev i)
    have hidx1 : a + b - u (Fin.rev i.castSucc) = a + b - u (Fin.rev i).succ := by
      rw [Fin.rev_castSucc]
    have hidx2 : a + b - u (Fin.rev i.succ) = a + b - u (Fin.rev i).castSucc := by
      rw [Fin.rev_succ]
    show ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun s => γ (a + b - s))
      (Icc (a + b - u (Fin.rev i.castSucc)) (a + b - u (Fin.rev i.succ)))
    rw [hidx1, hidx2]
    have hrefl_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => a + b - t)
        (Icc (a + b - u (Fin.rev i).succ) (a + b - u (Fin.rev i).castSucc)) :=
      ((contDiff_const.sub contDiff_id).contMDiff).contMDiffOn
    have hmaps' : MapsTo (fun t : ℝ => a + b - t)
        (Icc (a + b - u (Fin.rev i).succ) (a + b - u (Fin.rev i).castSucc))
        (Icc (u (Fin.rev i).castSucc) (u (Fin.rev i).succ)) := by
      rintro t ⟨ht1, ht2⟩
      exact ⟨by linarith, by linarith⟩
    exact hpiece.comp hrefl_smooth hmaps'

/-- **Math.** Length is invariant under time reversal: `L(γ ∘ (a+b-\cdot))|_a^b
= L(γ)|_a^b`, by the substitution `s = a + b - t` in the length integral. -/
theorem curveLength_comp_const_sub (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    curveLength (I := I) g (fun s => γ (a + b - s)) a b = curveLength (I := I) g γ a b := by
  have hcongr : (fun t : ℝ => Real.sqrt (curveSpeedSq (I := I) g (fun s => γ (a + b - s)) t))
      = fun t => Real.sqrt (curveSpeedSq (I := I) g γ (a + b - t)) := by
    funext t; rw [curveSpeedSq_comp_const_sub]
  show (∫ t in a..b, Real.sqrt (curveSpeedSq (I := I) g (fun s => γ (a + b - s)) t))
      = ∫ t in a..b, Real.sqrt (curveSpeedSq (I := I) g γ t)
  rw [hcongr, intervalIntegral.integral_comp_sub_left
    (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t)) (a + b),
    show a + b - b = a by ring, show a + b - a = b by ring]

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-distance`, symmetry clause):
**the Riemannian distance is symmetric**, `|pq| = |qp|`. Time-reversal
`γ ↦ (s ↦ γ (1 - s))` is a length-preserving bijection between the piecewise
smooth curves from `p` to `q` and those from `q` to `p`, so the two
infimum-defining sets coincide. -/
theorem riemannianDistance_comm (g : RiemannianMetric I M) (p q : M) :
    riemannianDistance (I := I) g p q = riemannianDistance (I := I) g q p := by
  have hset : {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
        γ 0 = p ∧ γ 1 = q ∧ L = curveLength (I := I) g γ 0 1} =
      {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
        γ 0 = q ∧ γ 1 = p ∧ L = curveLength (I := I) g γ 0 1} := by
    ext L
    constructor
    · rintro ⟨γ, hγ, hp, hq, rfl⟩
      refine ⟨fun s => γ (0 + 1 - s), ?_, ?_, ?_, ?_⟩
      · simpa using isPiecewiseSmoothCurve_comp_const_sub (I := I) hγ
      · simpa using hq
      · simpa using hp
      · simpa using (curveLength_comp_const_sub (I := I) g γ 0 1).symm
    · rintro ⟨γ, hγ, hq, hp, rfl⟩
      refine ⟨fun s => γ (0 + 1 - s), ?_, ?_, ?_, ?_⟩
      · simpa using isPiecewiseSmoothCurve_comp_const_sub (I := I) hγ
      · simpa using hp
      · simpa using hq
      · simpa using (curveLength_comp_const_sub (I := I) g γ 0 1).symm
  exact congrArg sInf hset

/-! ## Metric balls and set distance -/

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-metric-balls`): the **open metric
ball** `B(p, r) = {x ∈ M | |px| < r}`. -/
def metricBall (g : RiemannianMetric I M) (p : M) (r : ℝ) : Set M :=
  {x : M | riemannianDistance (I := I) g p x < r}

/-- **Math.** The **closed metric ball** `B̄(p, r) = {x ∈ M | |px| ≤ r}`. -/
def metricClosedBall (g : RiemannianMetric I M) (p : M) (r : ℝ) : Set M :=
  {x : M | riemannianDistance (I := I) g p x ≤ r}

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-metric-balls`): the **distance
between two sets** `A, B ⊂ M`, `d(A, B) = |AB| = inf{|pq| : p ∈ A, q ∈ B}`. -/
def setDistance (g : RiemannianMetric I M) (A B : Set M) : ℝ :=
  sInf {L : ℝ | ∃ p ∈ A, ∃ q ∈ B, L = riemannianDistance (I := I) g p q}

/-! ## Functional distance -/

/-- The differential of a real-valued function on `M` applied to a tangent
vector, read as a real number (`TangentSpace 𝓘(ℝ, ℝ) y` is a non-reducible
synonym of `ℝ`, so the retyping must happen through a definition). -/
def mfderivReal (f : M → ℝ) (x : M) (v : TangentSpace I x) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f x v

@[simp] lemma mfderivReal_def (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    mfderivReal (I := I) f x v = mfderiv I 𝓘(ℝ, ℝ) f x v := rfl

/-- **Math.** A smooth function `f : M → ℝ` has **gradient bounded by one**
if `(df_x(v))² ≤ g_x(v, v)` for every tangent vector — the dual reading of
`|∇f| ≤ 1`, with no musical isomorphism needed. -/
def HasGradientLeOne (g : RiemannianMetric I M) (f : M → ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace I x),
    mfderivReal (I := I) f x v ^ 2 ≤ g.metricInner x v v

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-functional-distance`): the
**functional distance**
`d_F(p, q) = sup{|f(p) − f(q)| : f : M → ℝ smooth, |∇f| ≤ 1 on M}`.
Always `d_F ≤ d`, and `d_F` generates the manifold topology as well; once
smooth distance functions are available the two distances agree locally. -/
def functionalDistance (g : RiemannianMetric I M) (p q : M) : ℝ :=
  sSup {r : ℝ | ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
    HasGradientLeOne (I := I) g f ∧ r = |f p - f q|}

/-- **Math.** The functional distance is nonnegative: every competitor value
`|f(p) − f(q)|` is nonnegative. -/
theorem functionalDistance_nonneg (g : RiemannianMetric I M) (p q : M) :
    0 ≤ functionalDistance (I := I) g p q := by
  unfold functionalDistance
  refine Real.sSup_nonneg ?_
  rintro r ⟨f, -, -, rfl⟩
  exact abs_nonneg _

/-! ## Segments -/

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-segment`): a piecewise `C^∞` curve
`σ : [a, b] → M` is a **segment** if its length realizes the distance between
its endpoints, `L(σ)|_a^b = |σ(a)σ(b)|`, and it is parametrized proportionally
to arc length: `L(σ)|_a^t = k (t - a)` for all `t ∈ [a, b]`, for some constant
`k ≥ 0` (`k = 1` exactly when `b - a = |σ(a)σ(b)|`, i.e. when `σ` is
parametrized by arc length itself). -/
def IsSegment (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : Prop :=
  IsPiecewiseSmoothCurve (I := I) γ a b ∧
    curveLength (I := I) g γ a b = riemannianDistance (I := I) g (γ a) (γ b) ∧
    ∃ k : ℝ, 0 ≤ k ∧ ∀ t ∈ Icc a b, curveLength (I := I) g γ a t = k * (t - a)

open Classical in
/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-segment`): the notation
`\overline{pq}`, a chosen segment from `p` to `q` on `[0, |pq|]` — junk value
`fun _ => p` (the constant curve at `p`) when no segment from `p` to `q`
exists. -/
noncomputable def segmentNotation (g : RiemannianMetric I M) (p q : M) : ℝ → M :=
  if h : ∃ γ : ℝ → M, IsSegment (I := I) g γ 0 (riemannianDistance (I := I) g p q) ∧
      γ 0 = p ∧ γ (riemannianDistance (I := I) g p q) = q
  then h.choose else fun _ => p

/-! ## Affine reparametrization

Length is invariant under orientation-preserving affine reparametrization
`s ↦ c s + d` (`c ≥ 0`): the speed scales by `c²` (chain rule), so the speed
scales by `c`, and the substitution rule for the length integral cancels the
factor. This is the affine case of the reparametrization invariance asserted
in `def:pet-ch5-curve-length`, and the workhorse for concatenating curves in
the triangle inequality for `riemannianDistance`. -/

/-- **Math.** Unconditional affine chain rule for `deriv` on the real line:
`(f (c ⬝ + d))' (t) = c • f' (c t + d)`, with no differentiability hypothesis —
if `f` is not differentiable at `c t + d` (and `c ≠ 0`) both sides are the junk
value `0`, since precomposition with the affine bijection `s ↦ c s + d`
preserves (non-)differentiability. -/
theorem deriv_comp_mul_add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (c d t : ℝ) :
    deriv (fun s => f (c * s + d)) t = c • deriv f (c * t + d) := by
  have h := deriv_comp_mul_left c (fun y => f (y + d)) t
  simpa [deriv_comp_add_const] using h

/-- **Math.** The squared speed of the affinely reparametrized curve
`s ↦ γ (c s + d)` at `t` is `c²` times the squared speed of `γ` at `c t + d`:
the chart-local reading is precomposed with the affine map, whose derivative
scales the velocity by `c`, and the metric pairing is quadratic. -/
theorem curveSpeedSq_comp_mul_add (g : RiemannianMetric I M) (γ : ℝ → M)
    (c d t : ℝ) :
    curveSpeedSq (I := I) g (fun s => γ (c * s + d)) t =
      c ^ 2 * curveSpeedSq (I := I) g γ (c * t + d) := by
  have hcurve : Geodesic.chartLocalCurve (I := I) (fun s => γ (c * s + d)) t =
      fun s => Geodesic.chartLocalCurve (I := I) γ (c * t + d) (c * s + d) := rfl
  have hderiv : deriv (Geodesic.chartLocalCurve (I := I) (fun s => γ (c * s + d)) t) t
      = c • deriv (Geodesic.chartLocalCurve (I := I) γ (c * t + d)) (c * t + d) := by
    rw [hcurve]
    exact deriv_comp_mul_add (Geodesic.chartLocalCurve (I := I) γ (c * t + d)) c d t
  rw [curveSpeedSq_def, hderiv, curveSpeedSq_def]
  set v := deriv (Geodesic.chartLocalCurve (I := I) γ (c * t + d)) (c * t + d) with hv
  show g.inner (γ (c * t + d)) (c • v) (c • v) = c ^ 2 * g.inner (γ (c * t + d)) v v
  calc g.inner (γ (c * t + d)) (c • v) (c • v)
      = c • g.inner (γ (c * t + d)) v (c • v) :=
        ContinuousLinearMap.map_smul₂ (g.inner (γ (c * t + d))) c v (c • v)
    _ = c • (c • g.inner (γ (c * t + d)) v v) :=
        congrArg (c • ·) ((g.inner (γ (c * t + d)) v).map_smul c v)
    _ = c ^ 2 * g.inner (γ (c * t + d)) v v := by
        rw [smul_eq_mul, smul_eq_mul]; ring

/-- **Math.** An orientation-preserving affine reparametrization of a piecewise
`C^∞` curve is piecewise `C^∞`: if `γ` is piecewise smooth on
`[c a + d, c b + d]` with `c > 0`, then `s ↦ γ (c s + d)` is piecewise smooth
on `[a, b]`, with the pulled-back partition `uᵢ ↦ (uᵢ - d) / c`. -/
theorem isPiecewiseSmoothCurve_comp_mul_add {γ : ℝ → M} {c : ℝ} (hc : 0 < c)
    {d a b : ℝ} (hγ : IsPiecewiseSmoothCurve (I := I) γ (c * a + d) (c * b + d)) :
    IsPiecewiseSmoothCurve (I := I) (fun s => γ (c * s + d)) a b := by
  obtain ⟨hcont, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  have haff_cont : ContinuousOn (fun t : ℝ => c * t + d) (Icc a b) :=
    ((continuous_const.mul continuous_id).add continuous_const).continuousOn
  have hmaps : MapsTo (fun t : ℝ => c * t + d) (Icc a b) (Icc (c * a + d) (c * b + d)) := by
    rintro t ⟨ht1, ht2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  refine ⟨hcont.comp haff_cont hmaps, n, fun i => (u i - d) / c, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h := hmono hij
    dsimp only
    gcongr
  · show (u 0 - d) / c = a
    rw [hu0]; field_simp [hc.ne']; ring
  · show (u (Fin.last n) - d) / c = b
    rw [hun]; field_simp [hc.ne']; ring
  · intro i
    have hpiece := hsmooth i
    have haff_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => c * t + d)
        (Icc ((u i.castSucc - d) / c) ((u i.succ - d) / c)) :=
      (((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff).contMDiffOn
    have hmaps' : MapsTo (fun t : ℝ => c * t + d)
        (Icc ((u i.castSucc - d) / c) ((u i.succ - d) / c))
        (Icc (u i.castSucc) (u i.succ)) := by
      rintro t ⟨ht1, ht2⟩
      have h1 := (div_le_iff₀ hc).mp ht1
      have h2 := (le_div_iff₀ hc).mp ht2
      exact ⟨by nlinarith, by nlinarith⟩
    exact hpiece.comp haff_smooth hmaps'

/-- **Math.** Length is invariant under orientation-preserving affine
reparametrization: `L(γ (c ⬝ + d))|_a^b = L(γ)|_{c a + d}^{c b + d}` for
`c ≥ 0`, by the chain rule for the speed and the substitution rule for the
integral. -/
theorem curveLength_comp_mul_add (g : RiemannianMetric I M) (γ : ℝ → M) {c : ℝ}
    (hc : 0 ≤ c) (d a b : ℝ) :
    curveLength (I := I) g (fun s => γ (c * s + d)) a b =
      curveLength (I := I) g γ (c * a + d) (c * b + d) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp only [zero_mul, zero_add]
    rw [curveLength_const, curveLength_self]
  have hsq : (fun t => Real.sqrt (curveSpeedSq (I := I) g (fun s => γ (c * s + d)) t))
      = fun t => c * Real.sqrt (curveSpeedSq (I := I) g γ (c * t + d)) := by
    funext t
    rw [curveSpeedSq_comp_mul_add, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  show (∫ t in a..b, Real.sqrt (curveSpeedSq (I := I) g (fun s => γ (c * s + d)) t))
      = ∫ t in (c * a + d)..(c * b + d), Real.sqrt (curveSpeedSq (I := I) g γ t)
  rw [hsq]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_add
      (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t)) hc.ne' d,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-! ## The distance is bounded by the length of any connecting curve -/

/-- **Math.** For any piecewise `C^∞` curve `γ : [0,1] → M` from `p` to `q`,
`|pq| ≤ L(γ)`: the distance is the infimum over exactly such lengths. -/
theorem riemannianDistance_le_curveLength (g : RiemannianMetric I M) {γ : ℝ → M}
    {p q : M} (hγ : IsPiecewiseSmoothCurve (I := I) γ 0 1) (h0 : γ 0 = p)
    (h1 : γ 1 = q) :
    riemannianDistance (I := I) g p q ≤ curveLength (I := I) g γ 0 1 :=
  csInf_le ⟨0, forall_mem_riemannianDistanceSet_nonneg (I := I) g p q⟩
    ⟨γ, hγ, h0, h1, rfl⟩

/-! ## Concatenation of curves and the triangle inequality -/

/-- **Math.** The **concatenation** of two curves `γ₁, γ₂ : [0, 1] → M` at
double speed: traverses `γ₁ (2t)` for `t ≤ 1/2`, then `γ₂ (2t - 1)`.  When
`γ₁ 1 = γ₂ 0` this is the usual concatenation of paths. -/
def curveConcat (γ₁ γ₂ : ℝ → M) : ℝ → M :=
  fun t => if t ≤ 1 / 2 then γ₁ (2 * t) else γ₂ (2 * t - 1)

@[simp] lemma curveConcat_zero (γ₁ γ₂ : ℝ → M) : curveConcat γ₁ γ₂ 0 = γ₁ 0 := by
  norm_num [curveConcat]

@[simp] lemma curveConcat_one (γ₁ γ₂ : ℝ → M) : curveConcat γ₁ γ₂ 1 = γ₂ 1 := by
  norm_num [curveConcat]

/-- **Math.** On `[0, 1/2]` the concatenation traverses `γ₁ (2t)`. -/
lemma curveConcat_eq_left (γ₁ γ₂ : ℝ → M) {t : ℝ} (ht : t ≤ 1 / 2) :
    curveConcat γ₁ γ₂ t = γ₁ (2 * t) := if_pos ht

/-- **Math.** On `[1/2, 1]` the concatenation traverses `γ₂ (2t - 1)` — at the
junction `t = 1/2` this uses the matching condition `γ₁ 1 = γ₂ 0`. -/
lemma curveConcat_eq_right {γ₁ γ₂ : ℝ → M} (hglue : γ₁ 1 = γ₂ 0) {t : ℝ}
    (ht : 1 / 2 ≤ t) :
    curveConcat γ₁ γ₂ t = γ₂ (2 * t - 1) := by
  rcases ht.eq_or_lt with rfl | hlt
  · rw [curveConcat, if_pos le_rfl]
    norm_num [hglue]
  · exact if_neg (not_le.mpr hlt)

/-- **Math.** The concatenation of two piecewise `C^∞` curves `[0,1] → M` with
matching endpoints is piecewise `C^∞` on `[0, 1]`: each half is an affine
reparametrization, and the halves glue at `1/2`. -/
theorem isPiecewiseSmoothCurve_curveConcat {γ₁ γ₂ : ℝ → M}
    (h₁ : IsPiecewiseSmoothCurve (I := I) γ₁ 0 1)
    (h₂ : IsPiecewiseSmoothCurve (I := I) γ₂ 0 1) (hglue : γ₁ 1 = γ₂ 0) :
    IsPiecewiseSmoothCurve (I := I) (curveConcat γ₁ γ₂) 0 1 := by
  have hleft : IsPiecewiseSmoothCurve (I := I) (curveConcat γ₁ γ₂) 0 (1 / 2) := by
    have h₁' : IsPiecewiseSmoothCurve (I := I) γ₁ (2 * 0 + 0) (2 * (1 / 2) + 0) := by
      norm_num
      exact h₁
    refine (isPiecewiseSmoothCurve_comp_mul_add (I := I) two_pos h₁').congr ?_
    intro s hs
    show curveConcat γ₁ γ₂ s = γ₁ (2 * s + 0)
    rw [add_zero]
    exact curveConcat_eq_left γ₁ γ₂ hs.2
  have hright : IsPiecewiseSmoothCurve (I := I) (curveConcat γ₁ γ₂) (1 / 2) 1 := by
    have h₂' : IsPiecewiseSmoothCurve (I := I) γ₂ (2 * (1 / 2) + -1) (2 * 1 + -1) := by
      norm_num
      exact h₂
    refine (isPiecewiseSmoothCurve_comp_mul_add (I := I) two_pos h₂').congr ?_
    intro s hs
    show curveConcat γ₁ γ₂ s = γ₂ (2 * s + -1)
    rw [← sub_eq_add_neg]
    exact curveConcat_eq_right hglue hs.1
  exact hleft.trans hright

section Boundaryless

variable [I.Boundaryless]

/-- **Math.** The speed `√(g(ċ, ċ))` of a piecewise `C^∞` curve on `[a, b]` is
interval-integrable on `[a, b]`: it is integrable on each smooth piece
(`ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq`), and adjacent pieces
chain.  In particular the length of a piecewise smooth curve is a well-defined
finite number (`def:pet-ch5-curve-length`). -/
theorem IsPiecewiseSmoothCurve.intervalIntegrable_sqrt_curveSpeedSq
    {γ : ℝ → M} {a b : ℝ} (hγ : IsPiecewiseSmoothCurve (I := I) γ a b)
    (g : RiemannianMetric I M) :
    IntervalIntegrable (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t))
      MeasureTheory.volume a b := by
  obtain ⟨-, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  have key : ∀ k : ℕ, ∀ hk : k < n + 1,
      IntervalIntegrable (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t))
        MeasureTheory.volume (u 0) (u ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk; exact IntervalIntegrable.refl
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      refine (ih (by omega)).trans ?_
      have hle : u (Fin.castSucc ⟨k, hkn⟩) ≤ u (Fin.succ ⟨k, hkn⟩) :=
        hmono Fin.castSucc_lt_succ.le
      exact ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq (I := I) g hle
        (hsmooth ⟨k, hkn⟩)
  rw [← hu0, ← hun]
  exact key n n.lt_succ_self

/-- **Math.** **Additivity of length along a piecewise smooth curve**: for
`a ≤ c ≤ b`, `L(γ)|_a^b = L(γ)|_a^c + L(γ)|_c^b` — the integrability needed by
`curveLength_additive` is automatic. -/
theorem IsPiecewiseSmoothCurve.curveLength_add {γ : ℝ → M} {a c b : ℝ}
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b) (g : RiemannianMetric I M)
    (hac : a ≤ c) (hcb : c ≤ b) :
    curveLength (I := I) g γ a b =
      curveLength (I := I) g γ a c + curveLength (I := I) g γ c b := by
  have hInt := hγ.intervalIntegrable_sqrt_curveSpeedSq g
  refine curveLength_additive (I := I) g γ (hInt.mono_set ?_) (hInt.mono_set ?_)
  · rw [uIcc_of_le hac, uIcc_of_le (hac.trans hcb)]
    exact Icc_subset_Icc_right hcb
  · rw [uIcc_of_le hcb, uIcc_of_le (hac.trans hcb)]
    exact Icc_subset_Icc_left hac

/-- **Math.** **Length is additive under concatenation**:
`L(γ₁ * γ₂) = L(γ₁) + L(γ₂)`.  Split the length at `1/2`; on each half the
concatenation agrees near every interior time with the affine reparametrization
of the corresponding curve, so the speeds agree a.e. and the substitution rule
gives the lengths of `γ₁` and `γ₂`. -/
theorem curveLength_curveConcat (g : RiemannianMetric I M) {γ₁ γ₂ : ℝ → M}
    (h₁ : IsPiecewiseSmoothCurve (I := I) γ₁ 0 1)
    (h₂ : IsPiecewiseSmoothCurve (I := I) γ₂ 0 1) (hglue : γ₁ 1 = γ₂ 0) :
    curveLength (I := I) g (curveConcat γ₁ γ₂) 0 1 =
      curveLength (I := I) g γ₁ 0 1 + curveLength (I := I) g γ₂ 0 1 := by
  have hconcat := isPiecewiseSmoothCurve_curveConcat (I := I) h₁ h₂ hglue
  have hsplit := hconcat.curveLength_add (I := I) g (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 ≤ 1)
  have hleft : curveLength (I := I) g (curveConcat γ₁ γ₂) 0 (1/2) =
      curveLength (I := I) g γ₁ 0 1 := by
    have hae : curveLength (I := I) g (curveConcat γ₁ γ₂) 0 (1/2) =
        curveLength (I := I) g (fun s => γ₁ (2 * s + 0)) 0 (1/2) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
        (MeasureTheory.measure_singleton ((1:ℝ)/2))] with t ht hmem
      have hne : t ≠ 1/2 := by simpa using ht
      have hmem' : t ∈ Ioc (0:ℝ) (1/2) := by
        rwa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at hmem
      have hlt : t < 1/2 := lt_of_le_of_ne hmem'.2 hne
      refine congrArg Real.sqrt ?_
      refine curveSpeedSq_congr_nhds (I := I) g ?_
      filter_upwards [Iio_mem_nhds hlt] with r hr
      show curveConcat γ₁ γ₂ r = γ₁ (2 * r + 0)
      rw [add_zero]
      exact curveConcat_eq_left γ₁ γ₂ hr.le
    rw [hae, curveLength_comp_mul_add (I := I) g γ₁ (by norm_num : (0:ℝ) ≤ 2) 0 0 (1/2)]
    norm_num
  have hright : curveLength (I := I) g (curveConcat γ₁ γ₂) (1/2) 1 =
      curveLength (I := I) g γ₂ 0 1 := by
    have hae : curveLength (I := I) g (curveConcat γ₁ γ₂) (1/2) 1 =
        curveLength (I := I) g (fun s => γ₂ (2 * s + -1)) (1/2) 1 := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro t hmem
      have hmem' : t ∈ Ioc ((1:ℝ)/2) 1 := by
        rwa [Set.uIoc_of_le (by norm_num : (1:ℝ)/2 ≤ 1)] at hmem
      refine congrArg Real.sqrt ?_
      refine curveSpeedSq_congr_nhds (I := I) g ?_
      filter_upwards [Ioi_mem_nhds hmem'.1] with r hr
      show curveConcat γ₁ γ₂ r = γ₂ (2 * r + -1)
      rw [← sub_eq_add_neg]
      exact curveConcat_eq_right hglue (le_of_lt hr)
    rw [hae, curveLength_comp_mul_add (I := I) g γ₂ (by norm_num : (0:ℝ) ≤ 2) (-1) (1/2) 1]
    norm_num
  rw [hsplit, hleft, hright]

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-distance`, triangle-inequality
clause): `|pr| ≤ |pq| + |qr|`, provided `p, q` and `q, r` are joined by
piecewise smooth curves (automatic on a connected manifold).  Concatenating an
`ε/2`-almost-minimizing curve from `p` to `q` with one from `q` to `r` gives a
curve from `p` to `r` of length at most `|pq| + |qr| + ε`. -/
theorem riemannianDistance_triangle (g : RiemannianMetric I M) (p q r : M)
    (hpq : ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧ γ 0 = p ∧ γ 1 = q)
    (hqr : ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧ γ 0 = q ∧ γ 1 = r) :
    riemannianDistance (I := I) g p r ≤
      riemannianDistance (I := I) g p q + riemannianDistance (I := I) g q r := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hne₁ : {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
      γ 0 = p ∧ γ 1 = q ∧ L = curveLength (I := I) g γ 0 1}.Nonempty := by
    obtain ⟨γ, hγ, h0, h1⟩ := hpq
    exact ⟨curveLength (I := I) g γ 0 1, γ, hγ, h0, h1, rfl⟩
  have hne₂ : {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
      γ 0 = q ∧ γ 1 = r ∧ L = curveLength (I := I) g γ 0 1}.Nonempty := by
    obtain ⟨γ, hγ, h0, h1⟩ := hqr
    exact ⟨curveLength (I := I) g γ 0 1, γ, hγ, h0, h1, rfl⟩
  obtain ⟨L₁, hL₁mem, hL₁lt⟩ := exists_lt_of_csInf_lt hne₁
    (lt_add_of_pos_right (riemannianDistance (I := I) g p q) (by linarith : (0:ℝ) < ε/2))
  obtain ⟨L₂, hL₂mem, hL₂lt⟩ := exists_lt_of_csInf_lt hne₂
    (lt_add_of_pos_right (riemannianDistance (I := I) g q r) (by linarith : (0:ℝ) < ε/2))
  obtain ⟨γ₁, hγ₁, hp₁, hq₁, rfl⟩ := hL₁mem
  obtain ⟨γ₂, hγ₂, hq₂, hr₂, rfl⟩ := hL₂mem
  have hglue : γ₁ 1 = γ₂ 0 := by rw [hq₁, hq₂]
  have hd : riemannianDistance (I := I) g p r ≤
      curveLength (I := I) g (curveConcat γ₁ γ₂) 0 1 :=
    riemannianDistance_le_curveLength (I := I) g
      (isPiecewiseSmoothCurve_curveConcat (I := I) hγ₁ hγ₂ hglue)
      (by rw [curveConcat_zero]; exact hp₁)
      (by rw [curveConcat_one]; exact hr₂)
  rw [curveLength_curveConcat (I := I) g hγ₁ hγ₂ hglue] at hd
  linarith

end Boundaryless

end PetersenLib
