import OpenGALib.Riemannian.Exponential.MinimizingEquality
import OpenGALib.Riemannian.Exponential.MinimizingPiecewise
import OpenGALib.Riemannian.Exponential.MinimizingEqualityManifold
import OpenGALib.Riemannian.Exponential.MinimizingPathPiecewise

/-!
# The equality case of the minimizing property, piecewise competitors
(do Carmo Ch. 3, Prop. 3.6, equality analysis, piecewise-`C¹` stage)

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 3.6, equality clause for
**piecewise differentiable** competitors: if a piecewise-`C¹` curve
`σ : [0,1] → M` from `p` to `exp_p v` realizes the length `√⟨v,v⟩_p` of the
radial geodesic, then `σ` is a monotone reparametrization of the radial
geodesic; in particular `σ([0,1]) = exp_p([0,1]·v)` — do Carmo's
`c([0,1]) = γ([0,1])` in its literal regularity class.

The polar stage extends the `C¹` equality analysis of
`MinimizingEquality.lean` in two steps:

* `exists_gauss_equality_ray_interval` — the ray identification on a
  **general interval** `[a,b]`, with **no anchoring** `w a = 0`: a `C¹`
  polar competitor realizing the radius gain `r(b) − r(a)` with equality
  traces the ray of its endpoint, `w(t) = (r(t)/r(b))·w(b)`, with monotone
  radius.  Before the last vanishing time of the radius the monotone radius
  forces `w = 0` (so the identity holds trivially), and past it the
  normalized lift has vanishing derivative exactly as in the anchored case;
  the anchored lemma `exists_gauss_equality_ray_ball` is the case `a = 0`,
  `w 0 = 0`.
* `exists_gauss_equality_ray_piecewise` — the piecewise version on a
  partition `τ 0 ≤ ⋯ ≤ τ n`: total equality forces equality on **every
  piece** (the per-piece radius comparison telescopes, and a sum of
  nonnegative deficits vanishing forces each to vanish), each piece traces
  the ray of its right endpoint, and a backward induction over the pieces
  glues the per-piece rays into the single ray of `w (τ n)` — the scalar
  algebra `(r t / r (τ (i+1))) · (r (τ (i+1)) / r (τ n)) = r t / r (τ n)`
  needs no direction gluing, the degenerate case `r (τ (i+1)) = 0` being
  absorbed by monotonicity of the radius.

The monotone gluing helper `monotoneOn_of_partition` is generic.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

/-- **Math.** A function monotone on every piece of a partition is monotone
on the whole span. -/
theorem monotoneOn_of_partition {α : Type*} [Preorder α] {r : ℝ → α} :
    ∀ {n : ℕ} {τ : ℕ → ℝ}, (∀ i < n, τ i ≤ τ (i + 1)) →
      (∀ i < n, MonotoneOn r (Icc (τ i) (τ (i + 1)))) →
      MonotoneOn r (Icc (τ 0) (τ n))
  | 0, τ, _, _ => by
    intro x hx y hy _
    have hx' : x = τ 0 := le_antisymm hx.2 hx.1
    have hy' : y = τ 0 := le_antisymm hy.2 hy.1
    rw [hx', hy']
  | (n + 1), τ, hτ, h => by
    have hτ' : ∀ i < n, τ i ≤ τ (i + 1) := fun i hi => hτ i (hi.trans n.lt_succ_self)
    have h' : ∀ i < n, MonotoneOn r (Icc (τ i) (τ (i + 1))) := fun i hi =>
      h i (hi.trans n.lt_succ_self)
    have hmid : MonotoneOn r (Icc (τ 0) (τ n)) := monotoneOn_of_partition hτ' h'
    have hlast : MonotoneOn r (Icc (τ n) (τ (n + 1))) := h n n.lt_succ_self
    have hτ0n : τ 0 ≤ τ n := partition_le hτ' (Nat.zero_le n) le_rfl
    have hτn1 : τ n ≤ τ (n + 1) := hτ n n.lt_succ_self
    intro x hx y hy hxy
    rcases le_total y (τ n) with h1 | h1
    · exact hmid ⟨hx.1, hxy.trans h1⟩ ⟨hy.1, h1⟩ hxy
    · rcases le_total (τ n) x with h2 | h2
      · exact hlast ⟨h2, hx.2⟩ ⟨h1, hy.2⟩ hxy
      · exact (hmid ⟨hx.1, h2⟩ ⟨hτ0n, le_rfl⟩ h2).trans
          (hlast ⟨le_rfl, hτn1⟩ ⟨h1, hy.2⟩ h1)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The equality case in polar form on a general interval: the
competitor runs along the ray of its endpoint** (do Carmo Ch. 3, Prop. 3.6,
equality analysis, global stage, polar form, **without anchoring**). There is
`ρ > 0` (a Gauss ball for `exp_p`) such that every `C¹` polar competitor
`w : [a,b] → B_ρ(0)` that realizes the radius comparison with **equality**
has monotone radius `r(t) = |w(t)|_p` and satisfies, for every `t ∈ [a,b]`,
$$w(t) = \frac{r(t)}{r(b)}\,w(b).$$
Unlike `exists_gauss_equality_ray_ball` the lift is **not** required to start
at the origin: on `[a, t_*]`, with `t_*` the last vanishing time of the
radius, the monotone radius forces `w = 0` and the identity holds trivially;
past `t_*` (or on all of `[a,b]` if the radius never vanishes) the
normalized lift `w/|w|_p` has vanishing derivative, hence is constant. -/
theorem exists_gauss_equality_ray_interval (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : E, ‖u‖ < ρ → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ρ →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ (w w' : ℝ → E) (a b : ℝ), a < b →
        ContinuousOn w (Icc a b) →
        (∀ t ∈ Ioo a b, HasDerivAt w (w' t) t) →
        ContinuousOn w' (Icc a b) →
        (∀ t ∈ Icc a b, ‖w t‖ < ρ) →
        (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w b) (w b))
            - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w a) (w a))
          = ∫ t in a..b, Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' t))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' t)))) →
        MonotoneOn (fun t => Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p p) (w t) (w t))) (Icc a b) ∧
        ∀ t ∈ Icc a b,
          w t = (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w t) (w t))
              / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w b) (w b))) • w b) := by
  classical
  obtain ⟨ρ, hρ, hdom, hsrc, hkey⟩ := exists_gauss_equality_radial_ball (I := I) g p
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  have hgram0 : ∀ z : E,
      ‖z‖ ^ 2 ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) z z :=
    fun z => hgramV _ (mem_of_mem_nhds hVc) z
  have hQnonneg : ∀ z : E,
      0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) z z := fun z =>
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p
      (mem_extChartAt_target p) z
  have hQzero : ∀ z : E,
      chartMetricInner (I := I) g p (extChartAt I p p) z z = 0 → z = 0 := by
    intro z hz
    have h1 := hgram0 z
    rw [hz, mul_zero] at h1
    have h2 : ‖z‖ = 0 := by nlinarith [norm_nonneg z, sq_nonneg ‖z‖]
    exact norm_eq_zero.mp h2
  refine ⟨ρ, hρ, hdom, hsrc, ?_⟩
  intro w w' a b hab hw_cont hw hw' hwball heq
  obtain ⟨hderiv, hrad⟩ :=
    hkey w w' a b hab hw_cont hw hw' hwball heq
  set r : ℝ → ℝ := fun t =>
    Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t))
    with hrdef
  have hr_nonneg : ∀ t, 0 ≤ r t := fun t => Real.sqrt_nonneg _
  have hrsq : ∀ t, chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t)
      = r t ^ 2 := fun t => (Real.sq_sqrt (hQnonneg (w t))).symm
  have hrzero_w : ∀ t, r t = 0 → w t = 0 := by
    intro t ht
    refine hQzero (w t) ?_
    rw [hrsq t, ht]
    norm_num
  -- continuity of the radius
  have hr_cont : ContinuousOn r (Icc a b) := by
    refine Real.continuous_sqrt.comp_continuousOn ?_
    exact continuousOn_chartMetricInner_along (I := I) g p
      continuousOn_const hw_cont hw_cont
      (fun t _ => mem_extChartAt_target p)
  -- monotonicity of the radius: its derivative is a square root
  have hrmono : MonotoneOn r (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hr_cont ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x hx).deriv]
      exact Real.sqrt_nonneg _
  refine ⟨hrmono, ?_⟩
  -- the normalized lift and its vanishing derivative where the radius is
  -- positive
  set eta : ℝ → E := fun t => (r t)⁻¹ • w t with hetadef
  have heta_deriv : ∀ x ∈ Ioo a b, 0 < r x → HasDerivAt eta 0 x := by
    intro x hx hrx
    have hQx : 0 < chartMetricInner (I := I) g p (extChartAt I p p)
        (w x) (w x) := by
      rw [hrsq x]
      positivity
    have hwx0 : w x ≠ 0 := by
      intro h0
      rw [h0, chartMetricInner_zero_left] at hQx
      exact lt_irrefl 0 hQx
    obtain ⟨hnonneg, hradx⟩ := hrad x hx hwx0
    -- derivative of the squared radius
    have hQd : HasDerivAt (fun s => chartMetricInner (I := I) g p
        (extChartAt I p p) (w s) (w s))
        (2 * chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w' x))
        x := by
      have h := hasDerivAt_chartMetricInner_const_base (I := I) g p
        (extChartAt I p p) (hw x hx) (hw x hx)
      have hsymm : chartMetricInner (I := I) g p (extChartAt I p p)
          (w' x) (w x)
          = chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w' x) :=
        chartMetricInner_symm (I := I) g p _ _ _
      rw [hsymm] at h
      convert h using 1
      ring
    have hrd : HasDerivAt r
        (2 * chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w' x)
          / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w x) (w x)))) x := hQd.sqrt hQx.ne'
    have hrinv : HasDerivAt (fun s => (r s)⁻¹)
        (-(2 * chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w' x)
          / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w x) (w x)))) / r x ^ 2) x := hrd.inv hrx.ne'
    have heta : HasDerivAt eta
        ((r x)⁻¹ • w' x
          + (-(2 * chartMetricInner (I := I) g p (extChartAt I p p)
              (w x) (w' x)
            / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w x) (w x)))) / r x ^ 2) • w x) x :=
      hrinv.smul (hw x hx)
    -- the derivative vanishes: substitute the radial velocity
    have hscalar : (r x)⁻¹ * (chartMetricInner (I := I) g p (extChartAt I p p)
            (w x) (w' x)
          / chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w x))
        + (-(2 * chartMetricInner (I := I) g p (extChartAt I p p)
            (w x) (w' x)
          / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w x) (w x)))) / r x ^ 2) = 0 := by
      rw [hrsq x, Real.sqrt_sq (hr_nonneg x)]
      field_simp
      ring
    have hsub : (r x)⁻¹ • w' x
        = ((r x)⁻¹ * (chartMetricInner (I := I) g p (extChartAt I p p)
            (w x) (w' x)
          / chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w x)))
          • w x := by
      conv_lhs => rw [hradx]
      rw [smul_smul]
    have hzero : (r x)⁻¹ • w' x
        + (-(2 * chartMetricInner (I := I) g p (extChartAt I p p)
            (w x) (w' x)
          / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w x) (w x)))) / r x ^ 2) • w x = 0 := by
      rw [hsub, ← add_smul, hscalar, zero_smul]
    rw [hzero] at heta
    exact heta
  -- constancy of the normalized lift on right subintervals where the radius
  -- is positive
  have heta_const : ∀ t, a < t → t ≤ b → (∀ s, t ≤ s → s ≤ b → 0 < r s) →
      eta t = eta b := by
    intro t hat htb hpos
    rcases eq_or_lt_of_le htb with rfl | htb'
    · rfl
    · have hconst := constant_of_has_deriv_right_zero
        (f := eta) (a := t) (b := b)
        (by
          refine ((hr_cont.mono (Icc_subset_Icc hat.le le_rfl)).inv₀ ?_).smul
            (hw_cont.mono (Icc_subset_Icc hat.le le_rfl))
          intro s hs
          exact (hpos s hs.1 hs.2).ne')
        (fun x hx => (heta_deriv x ⟨hat.trans_le hx.1, hx.2⟩
          (hpos x hx.1 hx.2.le)).hasDerivWithinAt)
      exact (hconst b (right_mem_Icc.mpr htb'.le)).symm
  -- assembly of the ray identity for positive-radius right intervals
  have hpos_case : ∀ t, a < t → t ≤ b → (∀ s, t ≤ s → s ≤ b → 0 < r s) →
      w t = (r t / r b) • w b := by
    intro t hat htb hpos
    have h1 : eta t = eta b := heta_const t hat htb hpos
    have hrt : 0 < r t := hpos t le_rfl htb
    have hwt : w t = r t • eta t := by
      rw [hetadef]
      simp only
      rw [smul_smul, mul_inv_cancel₀ hrt.ne', one_smul]
    rw [hwt, h1, hetadef]
    simp only
    rw [smul_smul, div_eq_mul_inv]
  by_cases hS : ∃ s ∈ Icc a b, r s = 0
  · -- the last vanishing time of the radius
    set S : Set ℝ := Icc a b ∩ r ⁻¹' {0} with hSdef
    have hS_closed : IsClosed S :=
      hr_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hS_ne : S.Nonempty := by
      obtain ⟨s, hs, hrs⟩ := hS
      exact ⟨s, hs, hrs⟩
    have hS_bdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
    set tstar : ℝ := sSup S with htstardef
    have htstarS : tstar ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
    have htstarab : tstar ∈ Icc a b := htstarS.1
    have hrtstar : r tstar = 0 := htstarS.2
    -- past the last vanishing time the radius is positive
    have hrpos : ∀ t, tstar < t → t ≤ b → 0 < r t := by
      intro t htl htu
      rcases eq_or_lt_of_le (hr_nonneg t) with h | h
      · exact absurd (le_csSup hS_bdd
          ⟨⟨htstarab.1.trans htl.le, htu⟩, h.symm⟩) (not_le.mpr htl)
      · exact h
    intro t ht
    rcases le_or_gt t tstar with htle | htgt
    · -- before the last vanishing time the lift is at the origin
      have hrt : r t = 0 :=
        le_antisymm (hrtstar ▸ hrmono ht htstarab htle) (hr_nonneg t)
      rw [hrzero_w t hrt, chartMetricInner_zero_left, Real.sqrt_zero, zero_div,
        zero_smul]
    · -- past it, the constancy of the direction gives the ray identity
      exact hpos_case t (htstarab.1.trans_lt htgt) ht.2
        (fun s hs1 hs2 => hrpos s (htgt.trans_le hs1) hs2)
  · -- the radius never vanishes: constancy on the whole interval, with a
    -- continuity glue at the left endpoint
    have hS' : ∀ s ∈ Icc a b, r s ≠ 0 := fun s hs h0 => hS ⟨s, hs, h0⟩
    have hrpos : ∀ s ∈ Icc a b, 0 < r s := fun s hs =>
      lt_of_le_of_ne (hr_nonneg s) (Ne.symm (hS' s hs))
    have hioc : ∀ t, a < t → t ≤ b → w t = (r t / r b) • w b := by
      intro t hat htb
      exact hpos_case t hat htb (fun s hs1 hs2 => hrpos s ⟨hat.le.trans hs1, hs2⟩)
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | hat
    · -- left endpoint: both sides are limits from the right
      have hIccmem : Icc a b ∈ 𝓝[>] a :=
        mem_of_superset (Ioo_mem_nhdsGT hab) Ioo_subset_Icc_self
      have hIocmem : Ioc a b ∈ 𝓝[>] a :=
        mem_of_superset (Ioo_mem_nhdsGT hab) Ioo_subset_Ioc_self
      have hlim1 : Tendsto w (𝓝[>] a) (𝓝 (w a)) :=
        Filter.Tendsto.mono_left (hw_cont a (left_mem_Icc.mpr hab.le))
          (nhdsWithin_le_of_mem hIccmem)
      have hlimr : Tendsto (fun s => r s / r b) (𝓝[>] a) (𝓝 (r a / r b)) :=
        (Filter.Tendsto.mono_left (hr_cont a (left_mem_Icc.mpr hab.le))
          (nhdsWithin_le_of_mem hIccmem)).div_const (r b)
      have hlim2 : Tendsto (fun s => (r s / r b) • w b) (𝓝[>] a)
          (𝓝 ((r a / r b) • w b)) := hlimr.smul_const (w b)
      have heqev : (fun s => (r s / r b) • w b) =ᶠ[𝓝[>] a] w := by
        filter_upwards [hIocmem] with s hs
        exact (hioc s hs.1 hs.2).symm
      exact tendsto_nhds_unique hlim1 (hlim2.congr' heqev)
    · exact hioc t hat ht.2

/-- **Math.** **The equality case in polar form, piecewise competitors: the
competitor runs along the ray** (do Carmo Ch. 3, Prop. 3.6, equality
analysis, global stage, polar form, piecewise-`C¹`). There is `ρ > 0` (a
Gauss ball for `exp_p`) such that every polar competitor `w` on a partition
`τ 0 ≤ ⋯ ≤ τ n` — continuous on the span, `C¹` on each piece — realizing the
total radius comparison with **equality** satisfies:

* the radius `r(t) = |w(t)|_p` is monotone on the span;
* on each piece the equality propagates in FTC form,
  `r(t) = r(τ i) + ∫_{τ i}^t |ċ|`;
* for every `t` in the span, `w(t) = (r(t)/r(τ n)) · w(τ n)`: the competitor
  traces the radial segment through its final point.

Total equality forces per-piece equality by telescoping; each piece traces
the ray of its right endpoint by `exists_gauss_equality_ray_interval`, and a
backward induction over the pieces composes the scalar factors. -/
theorem exists_gauss_equality_ray_piecewise (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : E, ‖u‖ < ρ → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ρ →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ (n : ℕ) (τ : ℕ → ℝ) (w : ℝ → E) (w' : ℕ → ℝ → E),
        (∀ i < n, τ i ≤ τ (i + 1)) →
        ContinuousOn w (Icc (τ 0) (τ n)) →
        (∀ i < n, ∀ t ∈ Ioo (τ i) (τ (i + 1)), HasDerivAt w (w' i t) t) →
        (∀ i < n, ContinuousOn (w' i) (Icc (τ i) (τ (i + 1)))) →
        (∀ t ∈ Icc (τ 0) (τ n), ‖w t‖ < ρ) →
        (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τ n)) (w (τ n)))
            - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w (τ 0)) (w (τ 0)))
          = ∑ i ∈ Finset.range n, ∫ t in τ i..τ (i + 1),
              Real.sqrt (chartMetricInner (I := I) g p
                (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
                (fderiv ℝ (fun u : E =>
                  extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                  (w t) (w' i t))
                (fderiv ℝ (fun u : E =>
                  extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                  (w t) (w' i t)))) →
        MonotoneOn (fun t => Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p p) (w t) (w t))) (Icc (τ 0) (τ n)) ∧
        (∀ i < n, ∀ t ∈ Icc (τ i) (τ (i + 1)),
          Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w t) (w t))
            = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w (τ i)) (w (τ i)))
              + ∫ s in τ i..t, Real.sqrt (chartMetricInner (I := I) g p
                  (extChartAt I p (expMap (I := I) g p (w s : TangentSpace I p)))
                  (fderiv ℝ (fun u : E =>
                    extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                    (w s) (w' i s))
                  (fderiv ℝ (fun u : E =>
                    extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                    (w s) (w' i s)))) ∧
        ∀ t ∈ Icc (τ 0) (τ n),
          w t = (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w t) (w t))
              / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w (τ n)) (w (τ n)))) • w (τ n)) := by
  classical
  obtain ⟨ρ₁, hρ₁, hdom₁, hsrc₁, hkey₁⟩ :=
    exists_gauss_equality_ray_interval (I := I) g p
  obtain ⟨ρr, hρr, hdomr, hsrcr, hradial⟩ :=
    exists_gauss_radial_lower_bound_ball (I := I) g p
  obtain ⟨ε₁, hε₁, hdome, hsrce, hinje, hopene, hfC1e, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  have hgram0 : ∀ z : E,
      ‖z‖ ^ 2 ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) z z :=
    fun z => hgramV _ (mem_of_mem_nhds hVc) z
  have hQnonneg : ∀ z : E,
      0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) z z := fun z =>
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p
      (mem_extChartAt_target p) z
  have hQzero : ∀ z : E,
      chartMetricInner (I := I) g p (extChartAt I p p) z z = 0 → z = 0 := by
    intro z hz
    have h1 := hgram0 z
    rw [hz, mul_zero] at h1
    have h2 : ‖z‖ = 0 := by nlinarith [norm_nonneg z, sq_nonneg ‖z‖]
    exact norm_eq_zero.mp h2
  set ρ : ℝ := min ρ₁ (min ρr ε₁) with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ (lt_min hρr hε₁)
  have hρρ₁ : ρ ≤ ρ₁ := min_le_left _ _
  have hρρr : ρ ≤ ρr := (min_le_right _ _).trans (min_le_left _ _)
  have hρε₁ : ρ ≤ ε₁ := (min_le_right _ _).trans (min_le_right _ _)
  have htgt : ∀ u : E, ‖u‖ < ρ →
      (fun u : E => extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) u
        ∈ (extChartAt I p).target := by
    intro u hu
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrce u (hu.trans_le hρε₁))
  have hfC1 : ContDiffOn ℝ 1
      (fun u : E => extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
      (ball (0 : E) ρ) :=
    hfC1e.mono (ball_subset_ball hρε₁)
  have hradialρ : ∀ v ξ : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (extChartAt I p p) v ξ ^ 2
        ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v
          * chartMetricInner (I := I) g p
              ((fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) v)
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) v ξ)
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) v ξ) :=
    fun v ξ hv => hradial v ξ (hv.trans_le hρρr)
  refine ⟨ρ, hρ, fun u hu => hdom₁ u (hu.trans_le hρρ₁),
    fun u hu => hsrc₁ u (hu.trans_le hρρ₁), ?_⟩
  intro n τ w w' hτ hw_cont hw hw' hwball heq
  -- pieces of the partition sit inside the span
  have hsub : ∀ i < n, Icc (τ i) (τ (i + 1)) ⊆ Icc (τ 0) (τ n) := fun i hi =>
    Icc_subset_Icc (partition_le hτ (Nat.zero_le i) hi.le)
      (partition_le hτ hi le_rfl)
  -- the per-piece radius comparison
  have hcomp : ∀ i < n,
      Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
          (w (τ (i + 1))) (w (τ (i + 1))))
        - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            (w (τ i)) (w (τ i)))
        ≤ ∫ t in τ i..τ (i + 1),
            Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' i t))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' i t))) := by
    intro i hi
    exact gauss_radius_comparison (I := I) g p
      (fun u : E => extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
      htgt hfC1 hradialρ (hτ i hi) (hw_cont.mono (hsub i hi)) (hw i hi)
      (hw' i hi) (fun t ht => hwball t (hsub i hi ht))
  -- total equality forces equality on every piece
  have htele : ∑ i ∈ Finset.range n,
      (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
          (w (τ (i + 1))) (w (τ (i + 1))))
        - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            (w (τ i)) (w (τ i))))
      = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
          (w (τ n)) (w (τ n)))
        - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            (w (τ 0)) (w (τ 0))) :=
    Finset.sum_range_sub (fun i => Real.sqrt (chartMetricInner (I := I) g p
      (extChartAt I p p) (w (τ i)) (w (τ i)))) n
  have heach : ∀ i < n,
      Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
          (w (τ (i + 1))) (w (τ (i + 1))))
        - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            (w (τ i)) (w (τ i)))
        = ∫ t in τ i..τ (i + 1),
            Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' i t))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' i t))) := by
    have hzero : ∑ i ∈ Finset.range n,
        ((∫ t in τ i..τ (i + 1),
            Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' i t))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' i t))))
          - (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τ (i + 1))) (w (τ (i + 1))))
            - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w (τ i)) (w (τ i))))) = 0 := by
      rw [Finset.sum_sub_distrib, htele, ← heq]
      ring
    have hnonneg : ∀ i ∈ Finset.range n,
        0 ≤ (∫ t in τ i..τ (i + 1),
            Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' i t))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' i t))))
          - (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τ (i + 1))) (w (τ (i + 1))))
            - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w (τ i)) (w (τ i)))) := fun i hi =>
      sub_nonneg.mpr (hcomp i (Finset.mem_range.mp hi))
    intro i hi
    have h := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero i
      (Finset.mem_range.mpr hi)
    linarith [h]
  -- per-piece monotonicity and per-piece ray identification
  have hmono_piece : ∀ i < n, MonotoneOn (fun t =>
      Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t)))
      (Icc (τ i) (τ (i + 1))) := by
    intro i hi
    rcases eq_or_lt_of_le (hτ i hi) with hdeg | hlt
    · intro x hx y hy _
      have hx' : x = τ i := le_antisymm (hdeg ▸ hx.2) hx.1
      have hy' : y = τ i := le_antisymm (hdeg ▸ hy.2) hy.1
      rw [hx', hy']
    · exact (hkey₁ w (w' i) (τ i) (τ (i + 1)) hlt (hw_cont.mono (hsub i hi))
        (hw i hi) (hw' i hi)
        (fun t ht => (hwball t (hsub i hi ht)).trans_le hρρ₁)
        (heach i hi)).1
  have hray_piece : ∀ i < n, ∀ t ∈ Icc (τ i) (τ (i + 1)),
      w t = (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            (w t) (w t))
          / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            (w (τ (i + 1))) (w (τ (i + 1))))) • w (τ (i + 1)) := by
    intro i hi t ht
    rcases eq_or_lt_of_le (hτ i hi) with hdeg | hlt
    · have ht' : t = τ (i + 1) := le_antisymm ht.2 (hdeg ▸ ht.1)
      rw [ht']
      rcases eq_or_ne (Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p p) (w (τ (i + 1))) (w (τ (i + 1))))) 0 with h0 | h0
      · have hw0 : w (τ (i + 1)) = 0 := by
          refine hQzero _ ?_
          have := Real.sq_sqrt (hQnonneg (w (τ (i + 1))))
          rw [h0] at this
          simpa using this.symm
        rw [hw0, smul_zero]
      · rw [div_self h0, one_smul]
    · exact (hkey₁ w (w' i) (τ i) (τ (i + 1)) hlt (hw_cont.mono (hsub i hi))
        (hw i hi) (hw' i hi)
        (fun t' ht' => (hwball t' (hsub i hi ht')).trans_le hρρ₁)
        (heach i hi)).2 t ht
  -- global monotonicity of the radius
  have hmono : MonotoneOn (fun t =>
      Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t)))
      (Icc (τ 0) (τ n)) := monotoneOn_of_partition hτ hmono_piece
  refine ⟨hmono, ?_, ?_⟩
  · -- per-piece FTC form of the equality
    intro i hi t ht
    rcases eq_or_lt_of_le (hτ i hi) with hdeg | hlt
    · have ht' : t = τ i := le_antisymm (hdeg ▸ ht.2) ht.1
      rw [ht', intervalIntegral.integral_same, add_zero]
    · have hftc := (gauss_radius_equality_ftc (I := I) g p
        (fun u : E => extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
        htgt hfC1 hradialρ (hw_cont.mono (hsub i hi)) (hw i hi) (hw' i hi)
        (fun t' ht' => hwball t' (hsub i hi ht')) (heach i hi)).1
      have h := hftc t ht
      linarith [h]
  · -- the ray identity, by backward induction over the pieces
    have hback : ∀ k, k ≤ n → ∀ t ∈ Icc (τ (n - k)) (τ n),
        w t = (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w t) (w t))
            / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τ n)) (w (τ n)))) • w (τ n) := by
      intro k
      induction k with
      | zero =>
        intro _ t ht
        simp only [Nat.sub_zero] at ht
        have ht' : t = τ n := le_antisymm ht.2 ht.1
        rw [ht']
        rcases eq_or_ne (Real.sqrt (chartMetricInner (I := I) g p
            (extChartAt I p p) (w (τ n)) (w (τ n)))) 0 with h0 | h0
        · have hw0 : w (τ n) = 0 := by
            refine hQzero _ ?_
            have := Real.sq_sqrt (hQnonneg (w (τ n)))
            rw [h0] at this
            simpa using this.symm
          rw [hw0, smul_zero]
        · rw [div_self h0, one_smul]
      | succ k ih =>
        intro hk t ht
        have hkn : k ≤ n := k.le_succ.trans hk
        have hi1 : n - (k + 1) + 1 = n - k := by omega
        have hin : n - (k + 1) < n := by omega
        rcases le_or_gt (τ (n - k)) t with hge | hlt2
        · exact ih hkn t ⟨hge, ht.2⟩
        · have htmem : t ∈ Icc (τ (n - (k + 1))) (τ (n - (k + 1) + 1)) :=
            ⟨ht.1, by rw [hi1]; exact hlt2.le⟩
          have h1 := hray_piece (n - (k + 1)) hin t htmem
          rw [hi1] at h1
          have h2 := ih hkn (τ (n - k))
            ⟨le_rfl, partition_le hτ (by omega) le_rfl⟩
          have h3 : w t = ((Real.sqrt (chartMetricInner (I := I) g p
                (extChartAt I p p) (w t) (w t))
              / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w (τ (n - k))) (w (τ (n - k)))))
              * (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                  (w (τ (n - k))) (w (τ (n - k))))
                / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                  (w (τ n)) (w (τ n))))) • w (τ n) := by
            rw [← smul_smul, ← h2]
            exact h1
          rcases eq_or_ne (Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p p) (w (τ (n - k))) (w (τ (n - k))))) 0
              with h0 | h0
          · -- the right endpoint of the piece has vanishing radius, so the
            -- monotone radius vanishes at `t` as well
            have hrt : Real.sqrt (chartMetricInner (I := I) g p
                (extChartAt I p p) (w t) (w t)) = 0 := by
              have hmp := hmono_piece (n - (k + 1)) hin htmem
                ⟨hτ (n - (k + 1)) hin, le_rfl⟩ (by rw [hi1]; exact hlt2.le)
              rw [hi1] at hmp
              simp only at hmp
              rw [h0] at hmp
              exact le_antisymm hmp (Real.sqrt_nonneg _)
            have hwt0 : w t = 0 := by
              refine hQzero _ ?_
              have := Real.sq_sqrt (hQnonneg (w t))
              rw [hrt] at this
              simpa using this.symm
            rw [hwt0, chartMetricInner_zero_left, Real.sqrt_zero, zero_div,
              zero_smul]
          · have hscalar : (Real.sqrt (chartMetricInner (I := I) g p
                  (extChartAt I p p) (w t) (w t))
                / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                  (w (τ (n - k))) (w (τ (n - k)))))
                * (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                    (w (τ (n - k))) (w (τ (n - k))))
                  / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                    (w (τ n)) (w (τ n))))
                = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                    (w t) (w t))
                  / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                    (w (τ n)) (w (τ n))) := by
              rw [div_mul_div_comm,
                mul_comm (Real.sqrt (chartMetricInner (I := I) g p
                  (extChartAt I p p) (w t) (w t))) _,
                mul_div_mul_left _ _ h0]
            rw [hscalar] at h3
            exact h3
    have := hback n le_rfl
    simpa [Nat.sub_self] using this

/-- **Math.** **The equality case of the minimizing property, in the manifold,
piecewise competitors** (do Carmo Ch. 3, Prop. 3.6, equality clause,
piecewise-`C¹` case). There is a Gauss ball radius `ρ > 0` at `p` such that
every piecewise-`C¹` competitor `σ : [0,1] → M` from `p` to `exp_p v`
(`‖v‖ < ρ`) — continuous on `[0,1]`, `C¹` on each piece of a partition
`0 = τ 0 ≤ ⋯ ≤ τ n = 1` — that stays in `exp_p(B_ρ(0))` and realizes the
radial length `√⟨v,v⟩_p` is a **monotone reparametrization of the radial
geodesic**; in particular `σ([0,1]) = exp_p([0,1]·v)` (do Carmo's
`c([0,1]) = γ([0,1])` in its literal regularity class).

The polar lift is `C¹` on each piece; the length bridges to the chart
integral of the polar speed piece by piece and sums by
`pathELength_sum_partition`, so length equality becomes the total FTC-form
hypothesis of `exists_gauss_equality_ray_piecewise`; the running-length
identity telescopes over the truncated partition `min (τ j) t`. -/
theorem exists_gauss_equality_manifold_piecewise_ball [T2Space M]
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ρ) ∧
      (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
       ∀ v : E, ‖v‖ < ρ → ∀ (σ : ℝ → M) (n : ℕ) (τ : ℕ → ℝ),
        τ 0 = 0 → τ n = 1 → (∀ i < n, τ i ≤ τ (i + 1)) →
        ContinuousOn σ (Icc (0 : ℝ) 1) →
        (∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (τ i) (τ (i + 1)))) →
        σ 0 = p →
        σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
        (∀ t ∈ Icc (0 : ℝ) 1, σ t ∈
          (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
            ball (0 : E) ρ) →
        Manifold.pathELength I σ 0 1
          = ENNReal.ofReal (Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v)) →
        ∃ s : ℝ → ℝ,
          ContinuousOn s (Icc 0 1) ∧ MonotoneOn s (Icc 0 1) ∧
          s 0 = 0 ∧ s 1 = 1 ∧
          (∀ t ∈ Icc (0 : ℝ) 1, s t ∈ Icc (0 : ℝ) 1 ∧
            σ t = expMap (I := I) g p ((s t • v : E) : TangentSpace I p)) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I σ 0 t
            = ENNReal.ofReal (s t * Real.sqrt
                (chartMetricInner (I := I) g p (extChartAt I p p) v v))) ∧
          σ '' Icc 0 1
            = (fun τ' : ℝ => expMap (I := I) g p ((τ' • v : E) : TangentSpace I p)) ''
                Icc 0 1) := by
  classical
  obtain ⟨ε₁, hε₁, hdom₁, hsrc₁, hinj₁, hopenM₁, hfC1, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  obtain ⟨ρy, hρy, hdomy, hsrcy, hraypw⟩ :=
    exists_gauss_equality_ray_piecewise (I := I) g p
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  set ρ : ℝ := min ε₁ ρy with hρdef
  have hρ : 0 < ρ := lt_min hε₁ hρy
  have hρε₁ : ρ ≤ ε₁ := min_le_left _ _
  have hρρy : ρ ≤ ρy := min_le_right _ _
  refine ⟨ρ, hρ, fun w hw => hdom₁ w (hw.trans_le hρε₁),
    fun w hw => hsrc₁ w (hw.trans_le hρε₁),
    hinj₁.mono (ball_subset_ball hρε₁), ?_⟩
  intro v hv σ n τ hτ0 hτn hτ hσcont hσp hσ0 hσ1 htrace hlen
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  -- the pieces sit inside `[0,1]`
  have hsub01 : ∀ i < n, Icc (τ i) (τ (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
    intro i hi
    refine Icc_subset_Icc ?_ ?_
    · rw [← hτ0]; exact partition_le hτ (Nat.zero_le i) hi.le
    · rw [← hτn]; exact partition_le hτ hi le_rfl
  -- the polar lift of the competitor through the local inverse of `exp_p`
  set w : ℝ → E := fun t => finv (extChartAt I p (σ t)) with hw_def
  have hwt : ∀ t ∈ Icc (0 : ℝ) 1, ‖w t‖ < ρ ∧
      expMap (I := I) g p (w t : TangentSpace I p) = σ t := by
    intro t ht
    obtain ⟨x, hx, hxe⟩ := htrace t ht
    have hxball : ‖x‖ < ρ := by simpa [mem_ball_zero_iff] using hx
    have hwx : w t = x := by
      rw [hw_def]
      simp only
      rw [← hxe]
      exact hlinv x (hxball.trans_le hρε₁)
    rw [hwx]
    exact ⟨hxball, hxe⟩
  have hsrcσ : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ (chartAt H p).source := by
    intro t ht
    obtain ⟨hwb, hwe⟩ := hwt t ht
    rw [← hwe]
    exact hsrc₁ (w t) (hwb.trans_le hρε₁)
  -- global continuity of the chart reading and of the polar lift
  have hucont : ContinuousOn (fun t => extChartAt I p (σ t)) (Icc (0 : ℝ) 1) := by
    refine (continuousOn_extChartAt (I := I) p).comp hσcont ?_
    intro t ht
    rw [extChartAt_source]
    exact hsrcσ t ht
  have humaps : MapsTo (fun t => extChartAt I p (σ t)) (Icc (0 : ℝ) 1)
      ((fun z : E => extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) ''
        ball (0 : E) ε₁) := by
    intro t ht
    obtain ⟨hwb, hwe⟩ := hwt t ht
    exact ⟨w t, mem_ball_zero_iff.mpr (hwb.trans_le hρε₁),
      congrArg (extChartAt I p) hwe⟩
  have hwcont : ContinuousOn w (Icc (0 : ℝ) 1) := by
    have h := (hfinvC1.continuousOn).comp hucont humaps
    exact h.congr fun t _ => by rw [hw_def]; rfl
  -- per-piece regularity of the polar lift
  have huC1 : ∀ i < n, ContDiffOn ℝ 1 (fun t => extChartAt I p (σ t))
      (Icc (τ i) (τ (i + 1))) := fun i hi =>
    contDiffOn_extChartAt_comp (hσp i hi) fun t ht => hsrcσ t (hsub01 i hi ht)
  have hwC1 : ∀ i < n, ContDiffOn ℝ 1 w (Icc (τ i) (τ (i + 1))) := by
    intro i hi
    have h := hfinvC1.comp (huC1 i hi) fun t ht => humaps (hsub01 i hi ht)
    exact h.congr fun t _ => by rw [hw_def]; rfl
  have hw'cont : ∀ i < n, ContinuousOn (derivWithin w (Icc (τ i) (τ (i + 1))))
      (Icc (τ i) (τ (i + 1))) := by
    intro i hi
    rcases eq_or_lt_of_le (hτ i hi) with hdeg | hlt
    · rw [← hdeg, Icc_self]
      exact continuousOn_singleton _ _
    · exact (hwC1 i hi).continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
  have hw'deriv : ∀ i < n, ∀ t ∈ Ioo (τ i) (τ (i + 1)),
      HasDerivAt w (derivWithin w (Icc (τ i) (τ (i + 1))) t) t := by
    intro i hi t ht
    have h1 : HasDerivWithinAt w (derivWithin w (Icc (τ i) (τ (i + 1))) t)
        (Icc (τ i) (τ (i + 1))) t :=
      ((hwC1 i hi).differentiableOn one_ne_zero t
        (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    exact h1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  -- endpoint values of the polar lift
  have hw0 : w 0 = 0 := by
    have h : extChartAt I p (σ 0)
        = extChartAt I p (expMap (I := I) g p ((0 : E) : TangentSpace I p)) := by
      rw [hσ0]
      exact (congrArg (extChartAt I p) (expMap_zero (I := I) g p)).symm
    rw [hw_def]
    simp only
    rw [h]
    exact hlinv 0 (by simpa using hε₁)
  have hw1 : w 1 = v := by
    have h : extChartAt I p (σ 1)
        = extChartAt I p (expMap (I := I) g p (v : TangentSpace I p)) := by
      rw [hσ1]
    rw [hw_def]
    simp only
    rw [h]
    exact hlinv v (hv.trans_le hρε₁)
  -- the chain rule on each piece
  have hchain : ∀ i < n, ∀ t ∈ Ioo (τ i) (τ (i + 1)),
      HasDerivAt (fun s => extChartAt I p (σ s))
        (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t)) t := by
    intro i hi t ht
    have hwb : ‖w t‖ < ρ := (hwt t (hsub01 i hi (Ioo_subset_Icc_self ht))).1
    have hf_at : HasFDerivAt (fun z : E =>
        extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
        (fderiv ℝ (fun z : E =>
          extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (w t))
        (w t) :=
      ((hfC1.contDiffAt (isOpen_ball.mem_nhds
        (mem_ball_zero_iff.mpr (hwb.trans_le hρε₁)))).differentiableAt
          one_ne_zero).hasFDerivAt
    have hcomp : HasDerivAt (fun s => extChartAt I p
        (expMap (I := I) g p (w s : TangentSpace I p)))
        (fderiv ℝ (fun z : E =>
          extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t)) t :=
      hf_at.comp_hasDerivAt t (hw'deriv i hi t ht)
    refine hcomp.congr_of_eventuallyEq ?_
    have hnhds : Icc (0 : ℝ) 1 ∈ 𝓝 t := by
      refine mem_of_superset (Icc_mem_nhds ht.1 ht.2) (hsub01 i hi)
    filter_upwards [hnhds] with s hs
    rw [(hwt s hs).2]
  -- the per-piece length bridge to the polar speed integral
  have hbridgepiece : ∀ i < n, Manifold.pathELength I σ (τ i) (τ (i + 1))
      = ENNReal.ofReal (∫ t in τ i..τ (i + 1),
          Real.sqrt (chartMetricInner (I := I) g p
            (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
            (fderiv ℝ (fun z : E =>
                extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
              (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t))
            (fderiv ℝ (fun z : E =>
                extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
              (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t)))) := by
    intro i hi
    have hbridge := pathELength_eq_ofReal_integral_chartMetricInner (I := I) g
      (hτ i hi) (hσp i hi) fun t ht => hsrcσ t (hsub01 i hi ht)
    rw [hbridge]
    congr 1
    rw [intervalIntegral.integral_of_le (hτ i hi),
      intervalIntegral.integral_of_le (hτ i hi),
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hd : derivWithin (fun s => extChartAt I p (σ s))
        (Icc (τ i) (τ (i + 1))) t
        = fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t) :=
      (hchain i hi t ht).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc (ht.1.trans ht.2) t (Ioo_subset_Icc_self ht))
    rw [hd, (hwt t (hsub01 i hi (Ioo_subset_Icc_self ht))).2]
  -- the total length as the summed polar speed integral
  have hInonneg : ∀ i < n, (0 : ℝ) ≤ ∫ t in τ i..τ (i + 1),
      Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
        (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t))
        (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t))) := fun i hi =>
    intervalIntegral.integral_nonneg (hτ i hi) fun t _ => Real.sqrt_nonneg _
  have htotal : Manifold.pathELength I σ 0 1
      = ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ t in τ i..τ (i + 1),
          Real.sqrt (chartMetricInner (I := I) g p
            (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
            (fderiv ℝ (fun z : E =>
                extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
              (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t))
            (fderiv ℝ (fun z : E =>
                extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
              (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t)))) := by
    have hsum := pathELength_sum_partition (I := I) g (σ := σ) (τ := τ) hτ
    rw [hτ0, hτn] at hsum
    rw [← hsum]
    rw [ENNReal.ofReal_sum_of_nonneg fun i hi => hInonneg i (Finset.mem_range.mp hi)]
    exact Finset.sum_congr rfl fun i hi =>
      hbridgepiece i (Finset.mem_range.mp hi)
  -- real equality of the summed polar-speed integral with the radius gain
  have heqI : (∑ i ∈ Finset.range n, ∫ t in τ i..τ (i + 1),
      Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
        (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t))
        (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t))))
      = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) := by
    have h1 : ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ t in τ i..τ (i + 1),
        Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
          (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
            (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t))
          (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
            (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t))))
        = ENNReal.ofReal (Real.sqrt
            (chartMetricInner (I := I) g p (extChartAt I p p) v v)) := by
      rw [← htotal]
      exact hlen
    refine (ENNReal.ofReal_eq_ofReal_iff ?_ (Real.sqrt_nonneg _)).mp h1
    exact Finset.sum_nonneg fun i hi => hInonneg i (Finset.mem_range.mp hi)
  -- the total FTC-form equality hypothesis of the piecewise polar lemma
  have hFTC : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
        (w (τ n)) (w (τ n)))
      - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
        (w (τ 0)) (w (τ 0)))
      = ∑ i ∈ Finset.range n, ∫ t in τ i..τ (i + 1),
          Real.sqrt (chartMetricInner (I := I) g p
            (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
            (fderiv ℝ (fun z : E =>
                extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
              (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t))
            (fderiv ℝ (fun z : E =>
                extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
              (w t) (derivWithin w (Icc (τ i) (τ (i + 1))) t))) := by
    rw [hτ0, hτn, hw1, hw0, chartMetricInner_zero_left, Real.sqrt_zero,
      sub_zero, heqI]
  -- the piecewise polar equality lemma
  have hwball : ∀ t ∈ Icc (τ 0) (τ n), ‖w t‖ < ρy := by
    rw [hτ0, hτn]
    exact fun t ht => ((hwt t ht).1).trans_le hρρy
  obtain ⟨hmono, hftcpiece, hraykey⟩ := hraypw n τ w
    (fun i => derivWithin w (Icc (τ i) (τ (i + 1)))) hτ
    (by rw [hτ0, hτn]; exact hwcont) hw'deriv hw'cont hwball hFTC
  rw [hτ0, hτn] at hmono hraykey
  rw [hw1] at hraykey
  -- continuity and vanishing at `0` of the radius of the polar lift
  have hrcont : ContinuousOn (fun t => Real.sqrt
      (chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t)))
      (Icc (0 : ℝ) 1) := by
    refine Real.continuous_sqrt.comp_continuousOn ?_
    exact continuousOn_chartMetricInner_along (I := I) g p continuousOn_const
      hwcont hwcont fun t _ => mem_extChartAt_target p
  have hr0 : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
      (w 0) (w 0)) = 0 := by
    rw [hw0, chartMetricInner_zero_left, Real.sqrt_zero]
  -- the running length over the truncated partition
  have hrunning : ∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I σ 0 t
      = ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p p) (w t) (w t))) := by
    intro t ht
    set τt : ℕ → ℝ := fun j => min (τ j) t with hτt_def
    have hτt : ∀ i < n, τt i ≤ τt (i + 1) := fun i hi =>
      min_le_min (hτ i hi) le_rfl
    have hτt0 : τt 0 = 0 := by
      rw [hτt_def]
      simp only
      rw [hτ0]
      exact min_eq_left ht.1
    have hτtn : τt n = t := by
      rw [hτt_def]
      simp only
      rw [hτn]
      exact min_eq_right ht.2
    have hτtmem : ∀ j ≤ n, τt j ∈ Icc (0 : ℝ) 1 := by
      intro j hj
      constructor
      · rw [hτt_def]
        simp only
        refine le_min ?_ ht.1
        rw [← hτ0]
        exact partition_le hτ (Nat.zero_le j) hj
      · exact (min_le_right _ _).trans ht.2
    -- the value of the length over each truncated piece
    have hpieceval : ∀ i < n, Manifold.pathELength I σ (τt i) (τt (i + 1))
        = ENNReal.ofReal
            (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τt (i + 1))) (w (τt (i + 1))))
            - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τt i)) (w (τt i)))) := by
      intro i hi
      rcases eq_or_lt_of_le (hτt i hi) with hdeg | hlt
      · rw [← hdeg, Manifold.pathELength_self, sub_self, ENNReal.ofReal_zero]
      · -- the truncated piece is nondegenerate: it is `[τ i, min (τ (i+1)) t]`
        have h1 : τ i < τ (i + 1) := by
          by_contra h
          exact absurd hlt (not_lt.mpr (min_le_min (not_lt.mp h) le_rfl))
        have h2 : τ i < t := by
          by_contra h
          have ht1 : τt i = t := min_eq_right (not_lt.mp h)
          have ht2 : τt (i + 1) = t := min_eq_right
            ((not_lt.mp h).trans (hτ i hi))
          rw [ht1, ht2] at hlt
          exact lt_irrefl t hlt
        have hτti : τt i = τ i := min_eq_left h2.le
        have hm1 : τt (i + 1) ≤ τ (i + 1) := min_le_left _ _
        have hsubpiece : Icc (τt i) (τt (i + 1)) ⊆ Icc (τ i) (τ (i + 1)) := by
          rw [hτti]
          exact Icc_subset_Icc le_rfl hm1
        have hbridge := pathELength_eq_ofReal_integral_chartMetricInner (I := I) g
          hlt.le ((hσp i hi).mono hsubpiece)
          fun s hs => hsrcσ s (hsub01 i hi (hsubpiece hs))
        rw [hbridge]
        congr 1
        have hIcongr : (∫ s in τt i..τt (i + 1), Real.sqrt
            (chartMetricInner (I := I) g p (extChartAt I p (σ s))
              (derivWithin (fun u => extChartAt I p (σ u))
                (Icc (τt i) (τt (i + 1))) s)
              (derivWithin (fun u => extChartAt I p (σ u))
                (Icc (τt i) (τt (i + 1))) s)))
            = ∫ s in τt i..τt (i + 1), Real.sqrt (chartMetricInner (I := I) g p
                (extChartAt I p (expMap (I := I) g p (w s : TangentSpace I p)))
                (fderiv ℝ (fun z : E =>
                    extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
                  (w s) (derivWithin w (Icc (τ i) (τ (i + 1))) s))
                (fderiv ℝ (fun z : E =>
                    extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
                  (w s) (derivWithin w (Icc (τ i) (τ (i + 1))) s))) := by
          rw [intervalIntegral.integral_of_le hlt.le,
            intervalIntegral.integral_of_le hlt.le,
            MeasureTheory.integral_Ioc_eq_integral_Ioo,
            MeasureTheory.integral_Ioc_eq_integral_Ioo]
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
            fun s hs => ?_
          have hsIoo : s ∈ Ioo (τ i) (τ (i + 1)) := by
            refine ⟨?_, hs.2.trans_le hm1⟩
            rw [← hτti]
            exact hs.1
          have hd : derivWithin (fun u => extChartAt I p (σ u))
              (Icc (τt i) (τt (i + 1))) s
              = fderiv ℝ (fun z : E =>
                  extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
                (w s) (derivWithin w (Icc (τ i) (τ (i + 1))) s) :=
            (hchain i hi s hsIoo).hasDerivWithinAt.derivWithin
              (uniqueDiffOn_Icc hlt s (Ioo_subset_Icc_self hs))
          rw [hd, (hwt s (hsub01 i hi (hsubpiece (Ioo_subset_Icc_self hs)))).2]
        rw [hIcongr]
        -- the FTC clause of the piecewise polar lemma evaluates the integral
        have hupper : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τt (i + 1))) (w (τt (i + 1))))
            = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w (τ i)) (w (τ i)))
              + ∫ s in τ i..τt (i + 1), Real.sqrt (chartMetricInner (I := I) g p
                  (extChartAt I p (expMap (I := I) g p (w s : TangentSpace I p)))
                  (fderiv ℝ (fun z : E =>
                      extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
                    (w s) (derivWithin w (Icc (τ i) (τ (i + 1))) s))
                  (fderiv ℝ (fun z : E =>
                      extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
                    (w s) (derivWithin w (Icc (τ i) (τ (i + 1))) s))) :=
          hftcpiece i hi (τt (i + 1)) ⟨by rw [← hτti]; exact hlt.le, hm1⟩
        rw [hτti]
        linarith [hupper]
    -- sum over the truncated partition
    have hdiffnn : ∀ i < n,
        0 ≤ Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            (w (τt (i + 1))) (w (τt (i + 1))))
          - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            (w (τt i)) (w (τt i))) := by
      intro i hi
      refine sub_nonneg.mpr (hmono (hτtmem i hi.le) (hτtmem (i + 1) hi)
        (hτt i hi))
    calc Manifold.pathELength I σ 0 t
        = Manifold.pathELength I σ (τt 0) (τt n) := by rw [hτt0, hτtn]
      _ = ∑ i ∈ Finset.range n, Manifold.pathELength I σ (τt i) (τt (i + 1)) :=
          (pathELength_sum_partition (I := I) g (σ := σ) (τ := τt) hτt).symm
      _ = ∑ i ∈ Finset.range n, ENNReal.ofReal
            (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τt (i + 1))) (w (τt (i + 1))))
            - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τt i)) (w (τt i)))) :=
          Finset.sum_congr rfl fun i hi => hpieceval i (Finset.mem_range.mp hi)
      _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
            (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τt (i + 1))) (w (τt (i + 1))))
            - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τt i)) (w (τt i))))) :=
          (ENNReal.ofReal_sum_of_nonneg fun i hi =>
            hdiffnn i (Finset.mem_range.mp hi)).symm
      _ = ENNReal.ofReal
            (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τt n)) (w (τt n)))
            - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τt 0)) (w (τt 0)))) := by
          rw [Finset.sum_range_sub (fun i => Real.sqrt
            (chartMetricInner (I := I) g p (extChartAt I p p)
              (w (τt i)) (w (τt i))))]
      _ = ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p
            (extChartAt I p p) (w t) (w t))) := by
          rw [hτt0, hτtn, hr0, sub_zero]
  -- final assembly, splitting on the degenerate direction `v = 0`
  by_cases hv0 : v = 0
  · -- degenerate case: the competitor is constant at `p`
    subst hv0
    have hwzero : ∀ t ∈ Icc (0 : ℝ) 1, w t = 0 := by
      intro t ht
      have h := hraykey t ht
      simpa using h
    have hσconst : ∀ t ∈ Icc (0 : ℝ) 1, σ t = p := by
      intro t ht
      rw [← (hwt t ht).2, hwzero t ht]
      exact expMap_zero (I := I) g p
    have hexp0 : ∀ τ' : ℝ,
        expMap (I := I) g p ((τ' • (0 : E) : E) : TangentSpace I p) = p := by
      intro τ'
      rw [smul_zero]
      exact expMap_zero (I := I) g p
    refine ⟨fun t => t, continuousOn_id, monotone_id.monotoneOn _, rfl, rfl,
      fun t ht => ⟨ht, by rw [hσconst t ht, hexp0 t]⟩, ?_, ?_⟩
    · intro t ht
      rw [hrunning t ht, hwzero t ht, chartMetricInner_zero_left, Real.sqrt_zero,
        mul_zero]
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by
        simp only [hexp0]
        exact (hσconst t ht).symm⟩
    · rintro ⟨τ', hτ', rfl⟩
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by
        simp only [hexp0]
        exact hσconst 0 ⟨le_rfl, zero_le_one⟩⟩
  · -- nondegenerate case: reparametrize by the normalized radius
    have hQv_pos : 0 < chartMetricInner (I := I) g p (extChartAt I p p) v v := by
      have h1 := hgramV _ (mem_of_mem_nhds hVc) v
      have h2 : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      nlinarith [sq_nonneg ‖v‖]
    have hr1 : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
        (w 1) (w 1))
        = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) := by
      rw [hw1]
    have hr1pos : 0 < Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p p) v v) := Real.sqrt_pos.mpr hQv_pos
    set s : ℝ → ℝ := fun t => Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p p) (w t) (w t))
      / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v)
      with hs_def
    have hskey : ∀ t ∈ Icc (0 : ℝ) 1,
        σ t = expMap (I := I) g p ((s t • v : E) : TangentSpace I p) := by
      intro t ht
      have h := hraykey t ht
      rw [← (hwt t ht).2]
      congr 1
    have hsnn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ s t := fun t ht =>
      div_nonneg (Real.sqrt_nonneg _) hr1pos.le
    have hsle1 : ∀ t ∈ Icc (0 : ℝ) 1, s t ≤ 1 := by
      intro t ht
      rw [hs_def]
      simp only
      rw [div_le_one hr1pos, ← hr1]
      exact hmono ht (right_mem_Icc.mpr zero_le_one) ht.2
    have hscont : ContinuousOn s (Icc (0 : ℝ) 1) := hrcont.div_const _
    have hsmono : MonotoneOn s (Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      exact div_le_div_of_nonneg_right (hmono hx hy hxy) hr1pos.le
    have hs0 : s 0 = 0 := by
      rw [hs_def]
      simp only
      rw [hr0, zero_div]
    have hs1 : s 1 = 1 := by
      rw [hs_def]
      simp only
      rw [hw1]
      exact div_self hr1pos.ne'
    refine ⟨s, hscont, hsmono, hs0, hs1,
      fun t ht => ⟨⟨hsnn t ht, hsle1 t ht⟩, hskey t ht⟩, ?_, ?_⟩
    · intro t ht
      rw [hrunning t ht]
      congr 1
      rw [hs_def]
      simp only
      rw [div_mul_cancel₀ _ hr1pos.ne']
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨s t, ⟨hsnn t ht, hsle1 t ht⟩, (hskey t ht).symm⟩
    · rintro ⟨τ', hτ', rfl⟩
      have hmem : τ' * Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p p) v v)
          ∈ Icc (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w 0) (w 0)))
            (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w 1) (w 1))) := by
        constructor
        · rw [hr0]
          exact mul_nonneg hτ'.1 hr1pos.le
        · rw [hr1]
          calc τ' * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              v v)
              ≤ 1 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                v v) := mul_le_mul_of_nonneg_right hτ'.2 hr1pos.le
            _ = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                v v) := one_mul _
      obtain ⟨t, htI, hrt⟩ := intermediate_value_Icc zero_le_one hrcont hmem
      refine ⟨t, htI, ?_⟩
      rw [hskey t htI]
      congr 2
      have hrt' : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
          (w t) (w t))
          = τ' * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            v v) := hrt
      rw [hs_def]
      simp only
      rw [hrt']
      exact mul_div_cancel_right₀ τ' hr1pos.ne'

/-- **Math.** **Confinement: a short piecewise-`C¹` curve from `p` stays in
the Gauss ball** (do Carmo Ch. 3, the escape case of the equality analysis of
Prop. 3.6, piecewise competitors). For every radius `ρ' > 0` there is a
length threshold `δ > 0` such that every piecewise-`C¹` curve from `p` of
`pathELength < δ` remains in `exp_p(B_{ρ'}(0))`: truncate at time `t`,
reparametrize each truncated piece affinely to a piecewise curve on `[0,1]`,
and apply the escape estimate of `exists_le_pathELength_piecewise` — a curve
whose endpoint escaped the ball of radius `min ρ' ε` would have length at
least `(min ρ' ε)/√c`. -/
theorem exists_forall_mem_expMap_ball_of_pathELength_lt_piecewise [T2Space M]
    (g : RiemannianMetric I M) (p : M) {ρ' : ℝ} (hρ' : 0 < ρ') :
    ∃ δ : ℝ, 0 < δ ∧
      (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
       ∀ (σ : ℝ → M) (n : ℕ) (τ : ℕ → ℝ),
        τ 0 = 0 → τ n = 1 → (∀ i < n, τ i ≤ τ (i + 1)) →
        ContinuousOn σ (Icc (0 : ℝ) 1) →
        (∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (τ i) (τ (i + 1)))) →
        σ 0 = p →
        Manifold.pathELength I σ 0 1 < ENNReal.ofReal δ →
        ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈
          (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
            ball (0 : E) ρ') := by
  classical
  obtain ⟨ε, c, hε, hc, hdom, hsrc, hinj, hopen, hmain⟩ :=
    exists_le_pathELength_piecewise (I := I) g p
  obtain ⟨hlow, hesc⟩ := hmain
  set ρ'' : ℝ := min ρ' ε with hρ''def
  have hρ'' : 0 < ρ'' := lt_min hρ' hε
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  set δ : ℝ := ρ'' / Real.sqrt c with hδdef
  have hδ : 0 < δ := div_pos hρ'' hsc
  refine ⟨δ, hδ, ?_⟩
  intro σ n τ hτ0 hτn hτ hσcont hσp hσ0 hlen t ht
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  rcases ht.1.eq_or_lt with rfl | ht0
  · -- at time `0` the curve is at the center
    refine ⟨0, mem_ball_zero_iff.mpr (by simpa using hρ'), ?_⟩
    show expMap (I := I) g p ((0 : E) : TangentSpace I p) = σ 0
    rw [hσ0]
    exact expMap_zero (I := I) g p
  · -- the truncation of `σ` at time `t`, reparametrized to `[0,1]`
    set f : ℝ → ℝ := fun τ' => t * τ' with hfdef
    set τt : ℕ → ℝ := fun j => min (τ j) t with hτt_def
    set τr : ℕ → ℝ := fun j => τt j / t with hτr_def
    have hτt : ∀ i < n, τt i ≤ τt (i + 1) := fun i hi =>
      min_le_min (hτ i hi) le_rfl
    have hτt0 : τt 0 = 0 := by
      rw [hτt_def]
      simp only
      rw [hτ0]
      exact min_eq_left ht.1
    have hτtn : τt n = t := by
      rw [hτt_def]
      simp only
      rw [hτn]
      exact min_eq_right ht.2
    have hτr : ∀ i < n, τr i ≤ τr (i + 1) := by
      intro i hi
      rw [hτr_def]
      simp only
      gcongr
      exact hτt i hi
    have hτr0 : τr 0 = 0 := by
      rw [hτr_def]
      simp only
      rw [hτt0, zero_div]
    have hτrn : τr n = 1 := by
      rw [hτr_def]
      simp only
      rw [hτtn]
      exact div_self ht0.ne'
    have hfτr : ∀ j, f (τr j) = τt j := by
      intro j
      rw [hfdef, hτr_def]
      simp only
      rw [mul_comm, div_mul_cancel₀ _ ht0.ne']
    -- the reparametrized truncation and its per-piece regularity
    have hfmaps : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
      intro x hx
      exact ⟨mul_nonneg ht.1 hx.1,
        le_trans (mul_le_mul ht.2 hx.2 hx.1 zero_le_one) (by norm_num)⟩
    have hfcont : ContinuousOn f (Icc (0 : ℝ) 1) :=
      (continuous_const.mul continuous_id).continuousOn
    have hσfcont : ContinuousOn (σ ∘ f) (Icc (0 : ℝ) 1) :=
      hσcont.comp hfcont hfmaps
    have hfsmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 f (Icc (0 : ℝ) 1) :=
      contMDiffOn_iff_contDiffOn.mpr ((contDiff_const.mul contDiff_id).contDiffOn)
    -- the nondegenerate truncated pieces sit inside the original pieces
    have hkey_piece : ∀ i < n, τt i < τt (i + 1) →
        τt i = τ i ∧ Icc (τt i) (τt (i + 1)) ⊆ Icc (τ i) (τ (i + 1)) := by
      intro i hi hlt
      have h2 : τ i < t := by
        by_contra h
        have ht1 : τt i = t := min_eq_right (not_lt.mp h)
        have ht2 : τt (i + 1) = t := min_eq_right ((not_lt.mp h).trans (hτ i hi))
        rw [ht1, ht2] at hlt
        exact lt_irrefl t hlt
      have hτti : τt i = τ i := min_eq_left h2.le
      refine ⟨hτti, ?_⟩
      rw [hτti]
      exact Icc_subset_Icc le_rfl (min_le_left _ _)
    have hσfp : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (σ ∘ f)
        (Icc (τr i) (τr (i + 1))) := by
      intro i hi
      rcases eq_or_lt_of_le (hτt i hi) with hdeg | hlt
      · -- collapsed piece: the restriction is a constant
        have hdegr : τr i = τr (i + 1) := by
          rw [hτr_def]
          simp only
          rw [hdeg]
        rw [← hdegr, Icc_self]
        refine (contMDiffOn_const (c := (σ ∘ f) (τr i))).congr fun x hx => ?_
        rw [mem_singleton_iff] at hx
        rw [hx]
      · obtain ⟨hτti, hsubpiece⟩ := hkey_piece i hi hlt
        have hmaps : MapsTo f (Icc (τr i) (τr (i + 1)))
            (Icc (τ i) (τ (i + 1))) := by
          intro x hx
          refine hsubpiece ⟨?_, ?_⟩
          · rw [← hfτr i]
            exact mul_le_mul_of_nonneg_left hx.1 ht.1
          · rw [← hfτr (i + 1)]
            exact mul_le_mul_of_nonneg_left hx.2 ht.1
        have hsub01r : Icc (τr i) (τr (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
          refine Icc_subset_Icc ?_ ?_
          · rw [← hτr0]
            exact partition_le hτr (Nat.zero_le i) hi.le
          · rw [← hτrn]
            exact partition_le hτr hi le_rfl
        exact (hσp i hi).comp (hfsmooth.mono hsub01r) hmaps
    have hσf0 : (σ ∘ f) 0 = p := by
      show σ (f 0) = p
      rw [hfdef]
      simp only
      rw [mul_zero, hσ0]
    -- the length of the reparametrized truncation is the truncated length
    have hreparam : Manifold.pathELength I (σ ∘ f) 0 1
        = Manifold.pathELength I σ 0 t := by
      have hsum1 := pathELength_sum_partition (I := I) g (σ := σ ∘ f) (τ := τr) hτr
      rw [hτr0, hτrn] at hsum1
      have hsum2 := pathELength_sum_partition (I := I) g (σ := σ) (τ := τt) hτt
      rw [hτt0, hτtn] at hsum2
      rw [← hsum1, ← hsum2]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i < n := Finset.mem_range.mp hi
      rcases eq_or_lt_of_le (hτt i hin) with hdeg | hlt
      · have hdegr : τr i = τr (i + 1) := by
          rw [hτr_def]
          simp only
          rw [hdeg]
        rw [← hdegr, ← hdeg, Manifold.pathELength_self,
          Manifold.pathELength_self]
      · obtain ⟨hτti, hsubpiece⟩ := hkey_piece i hin hlt
        have hlt_r : τr i ≤ τr (i + 1) := hτr i hin
        have hfmono : MonotoneOn f (Icc (τr i) (τr (i + 1))) := by
          intro a _ b _ hab
          exact mul_le_mul_of_nonneg_left hab ht.1
        have hfdiff : DifferentiableOn ℝ f (Icc (τr i) (τr (i + 1))) :=
          (differentiable_id.const_mul t).differentiableOn
        have hσmdiff : MDifferentiableOn 𝓘(ℝ, ℝ) I σ
            (Icc (f (τr i)) (f (τr (i + 1)))) := by
          rw [hfτr i, hfτr (i + 1)]
          exact ((hσp i hin).mdifferentiableOn one_ne_zero).mono hsubpiece
        have h := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := σ)
          hlt_r hfmono hfdiff hσmdiff
        rw [hfτr i, hfτr (i + 1)] at h
        exact h
    -- the escape estimate: the truncated endpoint stays in the ball
    have hshort : Manifold.pathELength I (σ ∘ f) 0 1 < ENNReal.ofReal δ := by
      rw [hreparam]
      exact lt_of_le_of_lt (Manifold.pathELength_mono le_rfl ht.2) hlen
    have hin : (σ ∘ f) 1 ∈
        (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
          ball (0 : E) ρ'' := by
      by_contra hout
      have h1 := hesc ρ'' hρ'' (min_le_right _ _) (σ ∘ f) n τr hτr0 hτrn hτr
        hσfcont hσfp hσf0 hout
      rw [hδdef] at hshort
      exact absurd h1 (not_le.mpr hshort)
    have hσt : σ t = (σ ∘ f) 1 := by
      show σ t = σ (f 1)
      rw [hfdef]
      simp only
      rw [mul_one]
    rw [hσt]
    obtain ⟨z, hz, hze⟩ := hin
    exact ⟨z, ball_subset_ball (min_le_left _ _) hz, hze⟩

/-- **Math.** **The equality case of the minimizing property, in the manifold,
piecewise competitors, without the confinement hypothesis** (do Carmo Ch. 3,
Prop. 3.6, equality clause, piecewise-`C¹` case, escape handled). There is
`ρ > 0` such that every piecewise-`C¹` competitor `σ : [0,1] → M` from `p` to
`exp_p v` (`‖v‖ < ρ`) realizing the radial length `√⟨v,v⟩_p` — with no
assumption on where it travels — is a monotone reparametrization of the
radial geodesic, with the running-length identity and do Carmo's image
equality `σ([0,1]) = exp_p([0,1]·v)`. This is do Carmo's Proposition 3.6
equality clause in its literal regularity class: an equality competitor is
automatically confined
(`exists_forall_mem_expMap_ball_of_pathELength_lt_piecewise`), so
`exists_gauss_equality_manifold_piecewise_ball` applies. -/
theorem exists_gauss_equality_manifold_piecewise [T2Space M]
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ρ) ∧
      (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
       ∀ v : E, ‖v‖ < ρ → ∀ (σ : ℝ → M) (n : ℕ) (τ : ℕ → ℝ),
        τ 0 = 0 → τ n = 1 → (∀ i < n, τ i ≤ τ (i + 1)) →
        ContinuousOn σ (Icc (0 : ℝ) 1) →
        (∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (τ i) (τ (i + 1)))) →
        σ 0 = p →
        σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
        Manifold.pathELength I σ 0 1
          = ENNReal.ofReal (Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v)) →
        ∃ s : ℝ → ℝ,
          ContinuousOn s (Icc 0 1) ∧ MonotoneOn s (Icc 0 1) ∧
          s 0 = 0 ∧ s 1 = 1 ∧
          (∀ t ∈ Icc (0 : ℝ) 1, s t ∈ Icc (0 : ℝ) 1 ∧
            σ t = expMap (I := I) g p ((s t • v : E) : TangentSpace I p)) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I σ 0 t
            = ENNReal.ofReal (s t * Real.sqrt
                (chartMetricInner (I := I) g p (extChartAt I p p) v v))) ∧
          σ '' Icc 0 1
            = (fun τ' : ℝ => expMap (I := I) g p ((τ' • v : E) : TangentSpace I p)) ''
                Icc 0 1) := by
  classical
  obtain ⟨ρ₀, hρ₀, hdom₀, hsrc₀, hinj₀, hkey⟩ :=
    exists_gauss_equality_manifold_piecewise_ball (I := I) g p
  obtain ⟨δ, hδ, hconf⟩ :=
    exists_forall_mem_expMap_ball_of_pathELength_lt_piecewise (I := I) g p hρ₀
  obtain ⟨εQ, hεQ, hQlt⟩ :=
    exists_forall_chartMetricInner_self_lt (I := I) g p
      (θ := δ ^ 2) (by positivity)
  set ρ : ℝ := min ρ₀ εQ with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ hεQ
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρεQ : ρ ≤ εQ := min_le_right _ _
  refine ⟨ρ, hρ, fun w hw => hdom₀ w (hw.trans_le hρρ₀),
    fun w hw => hsrc₀ w (hw.trans_le hρρ₀),
    hinj₀.mono (ball_subset_ball hρρ₀), ?_⟩
  intro v hv σ n τ hτ0 hτn hτ hσcont hσp hσ0 hσ1 hlen
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  have hQv_nonneg : 0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v :=
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p
      (mem_extChartAt_target p) v
  have hQv : chartMetricInner (I := I) g p (extChartAt I p p) v v < δ ^ 2 :=
    hQlt v (hv.trans_le hρεQ)
  have hlt : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v)
      < δ := by
    nlinarith [Real.sq_sqrt hQv_nonneg, Real.sqrt_nonneg
      (chartMetricInner (I := I) g p (extChartAt I p p) v v), hδ]
  have htrace := hconf σ n τ hτ0 hτn hτ hσcont hσp hσ0 (by
    rw [hlen]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hlt)
  exact hkey v (hv.trans_le hρρ₀) σ n τ hτ0 hτn hτ hσcont hσp hσ0 hσ1
    htrace hlen

end Exponential

end Riemannian
