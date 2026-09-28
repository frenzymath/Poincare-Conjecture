import MorganTianLib.Ch04.ScalarMinimumOn
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Quadratic lower comparison for scalar minima

Integrating the lower forward-Dini inequality `f' >= k f^2` gives the
barrier `c / (1 - k c (t - a))` before its pole. The minimum-envelope theorem
then applies this comparison to a compact family using only derivative
bounds at minimizing points. This is the analytic integration in
Morgan--Tian Chapter 4, `prop:scalar-curvature-min-evolution`.
-/

open Filter Set Function
open scoped Topology

noncomputable section

namespace MorganTianLib

/-- The rational quadratic barrier solves its autonomous ODE away from its pole. -/
theorem hasDerivAt_quadratic_lower_barrier {a c k t : ℝ}
    (hden : 1 - k * c * (t - a) ≠ 0) :
    HasDerivAt (fun s => c / (1 - k * c * (s - a)))
      (k * (c / (1 - k * c * (t - a))) ^ 2) t := by
  have hd : HasDerivAt (fun s : ℝ => 1 - k * c * (s - a)) (-(k * c)) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub
      (((hasDerivAt_id t).sub_const a).const_mul (k * c)) using 1 <;>
      first | rfl | ring
  convert (hasDerivAt_const t c).div hd hden using 1 <;>
    first | rfl | (simp only [div_pow]; ring)

/-- A continuous function with lower forward derivative at least `k f^2`
dominates the quadratic ODE solution on every interval before its pole. -/
theorem quadratic_lower_bound_of_forwardDiffQuotientGE
    {f : ℝ → ℝ} {a b c k : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hfd : ∀ t ∈ Ico a b, ForwardDiffQuotientGE f t (k * f t ^ 2))
    (hinit : c ≤ f a)
    (hden : ∀ t ∈ Icc a b, 0 < 1 - k * c * (t - a)) :
    ∀ t ∈ Icc a b, c / (1 - k * c * (t - a)) ≤ f t := by
  have hneg : ∀ t ∈ Ico a b,
      ForwardDiffQuotientLE (fun s => -f s) t (-k * (-f t) ^ 2) := by
    intro t ht r hr
    have hr' : -r < k * f t ^ 2 := by nlinarith
    filter_upwards [hfd t ht (-r) hr'] with z hz
    rw [slope_neg]
    linarith
  have hpsi : ContDiffOn ℝ 1 (uncurry (fun _ y : ℝ => -k * y ^ 2))
      (Icc a b ×ˢ (univ : Set ℝ)) := by fun_prop
  have hbarrier : ContinuousOn (fun t => c / (1 - k * c * (t - a)))
      (Icc a b) := by
    exact continuousOn_const.div (by fun_prop) (fun t ht => ne_of_gt (hden t ht))
  have hbarrier' : ∀ t ∈ Ico a b,
      HasDerivWithinAt (fun s => -(c / (1 - k * c * (s - a))))
        (-k * (-(c / (1 - k * c * (t - a)))) ^ 2) (Ici t) t := by
    intro t ht
    convert (hasDerivAt_quadratic_lower_barrier
      (ne_of_gt (hden t ⟨ht.1, ht.2.le⟩))).neg.hasDerivWithinAt using 1 <;>
      first | rfl | ring
  have hstart : -f a ≤ -(c / (1 - k * c * (a - a))) := by simpa using hinit
  have h := le_of_forwardDiffQuotientLE hf.neg hneg hpsi hbarrier.neg hbarrier' hstart
  intro t ht
  exact neg_le_neg_iff.mp (h t ht)

/-- A continuous function with positive initial value and lower forward
derivative at least `k f^2` cannot reach the pole on a closed time interval. -/
theorem endpoint_lt_of_forwardDiffQuotientGE_quadratic
    {f : ℝ → ℝ} {a b c k : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hfd : ∀ t ∈ Ico a b, ForwardDiffQuotientGE f t (k * f t ^ 2))
    (hinit : c ≤ f a) (hc : 0 < c) (hk : 0 < k) :
    b < a + 1 / (k * c) := by
  by_contra! hbp
  let p := a + 1 / (k * c)
  have hkc : 0 < k * c := mul_pos hk hc
  have hap : a < p := lt_add_of_pos_right a (div_pos zero_lt_one hkc)
  have hp : k * c * (p - a) = 1 := by
    dsimp [p]
    field_simp
    ring
  have hbound : ∀ t ∈ Ico a p, c ≤ f t * (1 - k * c * (t - a)) := by
    intro t ht
    have hden : ∀ s ∈ Icc a t, 0 < 1 - k * c * (s - a) := by
      intro s hs
      have hsp : s < p := hs.2.trans_lt ht.2
      nlinarith
    have hcomp := quadratic_lower_bound_of_forwardDiffQuotientGE
      (hf.mono (Icc_subset_Icc le_rfl (ht.2.le.trans hbp)))
      (fun s hs => hfd s ⟨hs.1, hs.2.trans_le (ht.2.le.trans hbp)⟩)
      hinit hden t ⟨ht.1, le_rfl⟩
    exact (div_le_iff₀ (hden t ⟨ht.1, le_rfl⟩)).mp hcomp
  have hcont : ContinuousOn (fun t => f t * (1 - k * c * (t - a)))
      (closure (Ico a p)) := by
    rw [closure_Ico hap.ne]
    exact (hf.mono (Icc_subset_Icc le_rfl hbp)).mul (by fun_prop)
  have hzero := le_on_closure hbound continuousOn_const hcont
    (show p ∈ closure (Ico a p) by rw [closure_Ico hap.ne]; exact ⟨hap.le, le_rfl⟩)
  rw [hp, sub_self, mul_zero] at hzero
  exact (not_le_of_gt hc) hzero

/-- On a half-open time interval the quadratic lower-Dini inequality bounds
the lifespan by the pole time, without assuming continuity at the final time. -/
theorem endpoint_le_of_forwardDiffQuotientGE_quadratic_Ico
    {f : ℝ → ℝ} {a b c k : ℝ}
    (hf : ContinuousOn f (Ico a b))
    (hfd : ∀ t ∈ Ico a b, ForwardDiffQuotientGE f t (k * f t ^ 2))
    (hinit : c ≤ f a) (hc : 0 < c) (hk : 0 < k) :
    b ≤ a + 1 / (k * c) := by
  by_contra! hpb
  have h := endpoint_lt_of_forwardDiffQuotientGE_quadratic
    (hf.mono (Icc_subset_Ico_right hpb))
    (fun t ht => hfd t ⟨ht.1, ht.2.trans hpb⟩) hinit hc hk
  exact (lt_irrefl _) h

/-- The quadratic comparison remains valid on the whole interval when the
initial lower barrier is nonpositive.  In this sign range its denominator is
automatically positive, which gives the negative-curvature branch of the
scalar minimum estimate without an endpoint-pole argument. -/
theorem quadratic_lower_bound_of_forwardDiffQuotientGE_nonpos
    {f : ℝ → ℝ} {a b c k : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hfd : ∀ t ∈ Ico a b, ForwardDiffQuotientGE f t (k * f t ^ 2))
    (hinit : c ≤ f a) (hc : c ≤ 0) (hk : 0 ≤ k) :
    ∀ t ∈ Icc a b, c / (1 - k * c * (t - a)) ≤ f t := by
  apply quadratic_lower_bound_of_forwardDiffQuotientGE hf hfd hinit
  intro t ht
  have hkc : k * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk hc
  have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
  nlinarith

/-- Nonnegative lower forward derivative implies monotonicity, without
differentiability of the scalar function. -/
theorem monotoneOn_of_forwardDiffQuotientGE_nonneg
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hfd : ∀ t ∈ Ico a b, ForwardDiffQuotientGE f t 0) :
    MonotoneOn f (Icc a b) := by
  intro s hs t ht hst
  have h := quadratic_lower_bound_of_forwardDiffQuotientGE
    (a := s) (b := t) (c := f s) (k := 0)
    (hf.mono (Icc_subset_Icc hs.1 ht.2))
    (fun u hu => by
      simpa using hfd u ⟨hs.1.trans hu.1, hu.2.trans_le ht.2⟩)
    le_rfl (by intro u hu; norm_num)
  simpa using h t ⟨hst, le_rfl⟩

/-- A continuous lower-Dini bound on the interior extends to the initial
endpoint when both the function and the prescribed bound are continuous there. -/
theorem forwardDiffQuotientGE_of_continuousOn_Ioo
    {f C : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hC : ContinuousOn C (Icc a b))
    (hfd : ∀ t ∈ Ioo a b, ForwardDiffQuotientGE f t (C t)) :
    ForwardDiffQuotientGE f a (C a) := by
  intro r hr
  obtain ⟨q, hrq, hqC⟩ := exists_between hr
  have hCt : Tendsto C (𝓝[>] a) (𝓝 (C a)) := by
    have h := hC a ⟨le_rfl, hab.le⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hab] at h
    exact h.mono_left (nhdsWithin_mono a Ioi_subset_Ici_self)
  have hq : ∀ᶠ t in 𝓝[>] a, q < C t := hCt (Ioi_mem_nhds hqC)
  obtain ⟨d, had, hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hq.and (Ioo_mem_nhdsGT hab))
  filter_upwards [Ioo_mem_nhdsGT had] with s hs
  have hsab : s ∈ Ioo a b := (hd hs).2
  have hbound : ∀ u ∈ Ioc a s, f u - q * u ≤ f s - q * s := by
    intro u hu
    apply monotoneOn_of_forwardDiffQuotientGE_nonneg
      (a := u) (b := s)
      ((hf.mono (Icc_subset_Icc hu.1.le hsab.2.le)).sub (by fun_prop)) _
      ⟨le_rfl, hu.2⟩ ⟨hu.2, le_rfl⟩ hu.2
    intro v hv z hz
    have hvad : v ∈ Ioo a d := ⟨hu.1.trans_le hv.1, hv.2.trans hs.2⟩
    have hvab : v ∈ Ioo a b := (hd hvad).2
    have hqv : q ≤ C v := ((hd hvad).1).le
    filter_upwards [(hfd v hvab).mono hqv (z + q) (by linarith),
      self_mem_nhdsWithin] with w hw hwv
    have hvw : w - v ≠ 0 := sub_ne_zero.mpr (ne_of_gt hwv)
    have hslope : slope (fun t => f t - q * t) v w = slope f v w - q := by
      simp only [slope_def_field]
      field_simp
      ring
    change z < slope (fun t => f t - q * t) v w
    rw [hslope]
    linarith
  have hcont : ContinuousOn (fun u => f u - q * u) (closure (Ioc a s)) := by
    rw [closure_Ioc hs.1.ne]
    exact (hf.mono (Icc_subset_Icc le_rfl hsab.2.le)).sub (by fun_prop)
  have hstart := le_on_closure hbound hcont continuousOn_const
    (show a ∈ closure (Ioc a s) by
      rw [closure_Ioc hs.1.ne]
      exact ⟨le_rfl, hs.1.le⟩)
  have hqs : q ≤ slope f a s := by
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hs.1)]
    linarith
  exact hrq.trans_le hqs

section CompactFamily

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

/-- Quadratic comparison for a compact family only requires joint continuity
on the time slab on which the comparison is made. -/
theorem quadratic_lower_bound_iInfOn_of_min_deriv
    {F F' : X → ℝ → ℝ} {a b c k : ℝ}
    (hF : ContinuousOn (fun z : X × ℝ => F z.1 z.2) (univ ×ˢ Icc a b))
    (hF' : ContinuousOn (fun z : X × ℝ => F' z.1 z.2) (univ ×ˢ Icc a b))
    (hderiv : ∀ x, ∀ s ∈ Ioo a b, HasDerivAt (F x) (F' x s) s)
    (hmin : ∀ t ∈ Ico a b, ∀ x, F x t = (⨅ y, F y t) →
      k * F x t ^ 2 ≤ F' x t)
    (hinit : c ≤ ⨅ x, F x a)
    (hden : ∀ t ∈ Icc a b, 0 < 1 - k * c * (t - a)) :
    ∀ t ∈ Icc a b, c / (1 - k * c * (t - a)) ≤ ⨅ x, F x t := by
  apply quadratic_lower_bound_of_forwardDiffQuotientGE
    (continuousOn_iInf_of_compact hF) _ hinit hden
  intro t ht
  apply forwardDiffQuotientGE_iInfOn ht.1 ht.2 hF hF'
    (fun x s hs => hderiv x s ⟨ht.1.trans_lt hs.1, hs.2⟩)
  intro x hx
  simpa only [hx] using hmin t ht x hx

/-- Interval-local derivative bounds at spatial minima imply monotonicity of
the compact minimum on the closed time slab. -/
theorem monotoneOn_iInfOn_of_min_deriv_nonneg
    {F F' : X → ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn (fun z : X × ℝ => F z.1 z.2) (univ ×ˢ Icc a b))
    (hF' : ContinuousOn (fun z : X × ℝ => F' z.1 z.2) (univ ×ˢ Icc a b))
    (hderiv : ∀ x, ∀ s ∈ Ioo a b, HasDerivAt (F x) (F' x s) s)
    (hmin : ∀ t ∈ Ico a b, ∀ x, F x t = (⨅ y, F y t) → 0 ≤ F' x t) :
    MonotoneOn (fun t => ⨅ x, F x t) (Icc a b) := by
  apply monotoneOn_of_forwardDiffQuotientGE_nonneg (continuousOn_iInf_of_compact hF)
  intro t ht
  exact forwardDiffQuotientGE_iInfOn ht.1 ht.2 hF hF'
    (fun x s hs => hderiv x s ⟨ht.1.trans_lt hs.1, hs.2⟩) (hmin t ht)

/-- Quadratic lower bounds at every spatial minimizer give the rational
lower bound for the minimum of a compact scalar family. -/
theorem quadratic_lower_bound_iInf_of_min_deriv
    {F F' : X → ℝ → ℝ} {a b c k : ℝ}
    (hF : Continuous ↿F) (hF' : Continuous ↿F')
    (hderiv : ∀ x, ∀ s ∈ Ioo a b, HasDerivAt (F x) (F' x s) s)
    (hmin : ∀ t ∈ Ico a b, ∀ x, F x t = (⨅ y, F y t) →
      k * F x t ^ 2 ≤ F' x t)
    (hinit : c ≤ ⨅ x, F x a)
    (hden : ∀ t ∈ Icc a b, 0 < 1 - k * c * (t - a)) :
    ∀ t ∈ Icc a b, c / (1 - k * c * (t - a)) ≤ ⨅ x, F x t := by
  apply quadratic_lower_bound_of_forwardDiffQuotientGE
    (continuous_iInf_of_compact hF).continuousOn _ hinit hden
  intro t ht
  apply forwardDiffQuotientGE_iInf ht.2 hF hF'
    (fun x s hs => hderiv x s ⟨ht.1.trans_lt hs.1, hs.2⟩)
  intro x hx
  simpa only [hx] using hmin t ht x hx

/-- The minimum of a compact scalar family is nondecreasing when all
minimizers have nonnegative time derivative. -/
theorem monotoneOn_iInf_of_min_deriv_nonneg
    {F F' : X → ℝ → ℝ} {a b : ℝ}
    (hF : Continuous ↿F) (hF' : Continuous ↿F')
    (hderiv : ∀ x, ∀ s ∈ Ioo a b, HasDerivAt (F x) (F' x s) s)
    (hmin : ∀ t ∈ Ico a b, ∀ x, F x t = (⨅ y, F y t) → 0 ≤ F' x t) :
    MonotoneOn (fun t => ⨅ x, F x t) (Icc a b) := by
  apply monotoneOn_of_forwardDiffQuotientGE_nonneg
    (continuous_iInf_of_compact hF).continuousOn
  intro t ht
  exact forwardDiffQuotientGE_iInf ht.2 hF hF'
    (fun x s hs => hderiv x s ⟨ht.1.trans_lt hs.1, hs.2⟩) (hmin t ht)

/-! The following adapter packages the three scalar-minimum conclusions used
in the source proposition: monotonicity, the quadratic barrier before its
pole, and the resulting lifespan bound. -/

/-- **Math.** A compact scalar family whose minimizing points satisfy the
quadratic lower derivative inequality has a nondecreasing minimum.  For a
positive initial minimum, the minimum dominates the quadratic barrier at
every time before its pole, and the interval endpoint cannot pass that pole.
This is the compact-family form of `prop:scalar-curvature-min-evolution`;
geometric Ricci-flow hypotheses enter through `hderiv` and `hmin`.
-/
theorem scalar_min_evolution_of_compact_family
    {F F' : X → ℝ → ℝ} {a b c k : ℝ}
    (hF : Continuous ↿F) (hF' : Continuous ↿F')
    (hderiv : ∀ x, ∀ s ∈ Ioo a b, HasDerivAt (F x) (F' x s) s)
    (hmin : ∀ t ∈ Ico a b, ∀ x, F x t = (⨅ y, F y t) →
      k * F x t ^ 2 ≤ F' x t)
    (hinit : c ≤ ⨅ x, F x a) (hc : 0 < c) (hk : 0 < k) :
    MonotoneOn (fun t => ⨅ x, F x t) (Icc a b) ∧
      (∀ t ∈ Icc a b, t < a + 1 / (k * c) →
        c / (1 - k * c * (t - a)) ≤ ⨅ x, F x t) ∧
      b ≤ a + 1 / (k * c) := by
  have hfd : ∀ t ∈ Ico a b,
      ForwardDiffQuotientGE (fun s => ⨅ x, F x s) t
        (k * (⨅ x, F x t) ^ 2) := by
    intro t ht
    exact forwardDiffQuotientGE_iInf ht.2 hF hF'
      (fun x s hs => hderiv x s ⟨ht.1.trans_lt hs.1, hs.2⟩) (by
        intro x hx
        simpa only [hx] using hmin t ht x hx)
  have hmono : MonotoneOn (fun t => ⨅ x, F x t) (Icc a b) := by
    apply monotoneOn_iInf_of_min_deriv_nonneg hF hF' hderiv
    intro t ht x hx
    exact (mul_nonneg (le_of_lt hk) (sq_nonneg _)).trans (hmin t ht x hx)
  have hlife := endpoint_le_of_forwardDiffQuotientGE_quadratic_Ico
    ((continuous_iInf_of_compact hF).continuousOn.mono Ico_subset_Icc_self)
    hfd hinit hc hk
  have hbound : ∀ t ∈ Icc a b, t < a + 1 / (k * c) →
      c / (1 - k * c * (t - a)) ≤ ⨅ x, F x t := by
    intro t ht htp
    have hden : ∀ s ∈ Icc a t, 0 < 1 - k * c * (s - a) := by
      intro s hs
      have hkc : 0 < k * c := mul_pos hk hc
      have hpole : s < a + 1 / (k * c) := by
        exact lt_of_le_of_lt (by linarith [hs.2]) htp
      have hsrel : s - a < 1 / (k * c) := by linarith
      have hmul : (s - a) * (k * c) < 1 := (lt_div_iff₀ hkc).mp hsrel
      nlinarith
    exact quadratic_lower_bound_of_forwardDiffQuotientGE
      ((continuous_iInf_of_compact hF).continuousOn.mono
        (Icc_subset_Icc le_rfl ht.2))
      (fun s hs => hfd s ⟨hs.1, hs.2.trans_le ht.2⟩)
      hinit hden t ⟨ht.1, le_rfl⟩
  exact ⟨hmono, hbound, hlife⟩

/-! The negative initial-curvature branch has no pole.  Export the source's
explicit formula from the generic nonpositive quadratic comparison. -/

/-- **Math.** If the compact-family minimum starts nonpositive and satisfies
the scalar quadratic lower derivative inequality with coefficient `2 / n`,
then it obeys the negative-curvature barrier from the source proposition. -/
theorem scalar_min_negative_bound_of_compact_family
    {F F' : X → ℝ → ℝ} {a b c : ℝ} {n : ℕ}
    (hn : 0 < (n : ℝ))
    (hF : Continuous ↿F) (hF' : Continuous ↿F')
    (hderiv : ∀ x, ∀ s ∈ Ioo a b, HasDerivAt (F x) (F' x s) s)
    (hmin : ∀ t ∈ Ico a b, ∀ x, F x t = (⨅ y, F y t) →
      (2 / (n : ℝ)) * F x t ^ 2 ≤ F' x t)
    (hinit : c ≤ ⨅ x, F x a) (hc : c ≤ 0) :
    ∀ t ∈ Icc a b,
      -(n : ℝ) * |c| / (2 * (t - a) * |c| + n) ≤ ⨅ x, F x t := by
  have hbound : ∀ t ∈ Icc a b,
      c / (1 - (2 / (n : ℝ)) * c * (t - a)) ≤ ⨅ x, F x t := by
    apply quadratic_lower_bound_of_forwardDiffQuotientGE_nonpos
      (continuous_iInf_of_compact hF).continuousOn
    · intro t ht
      exact forwardDiffQuotientGE_iInf ht.2 hF hF'
        (fun x s hs => hderiv x s ⟨ht.1.trans_lt hs.1, hs.2⟩) (by
          intro x hx
          simpa only [hx] using hmin t ht x hx)
    · exact hinit
    · exact hc
    · positivity
  intro t ht
  have hden : 0 < 1 - (2 / (n : ℝ)) * c * (t - a) := by
    have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have hcoef : 0 ≤ (2 / (n : ℝ)) := by positivity
    have hprod : (2 / (n : ℝ)) * c * (t - a) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hcoef hc) hta
    linarith
  have habs : |c| = -c := abs_of_nonpos hc
  have hform : c / (1 - (2 / (n : ℝ)) * c * (t - a)) =
      -(n : ℝ) * |c| / (2 * (t - a) * |c| + n) := by
    rw [habs]
    field_simp
    ring
  have h := hbound t ht
  rw [hform] at h
  exact h

end CompactFamily

end MorganTianLib
