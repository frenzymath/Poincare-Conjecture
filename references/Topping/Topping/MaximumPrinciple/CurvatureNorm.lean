import Topping.MaximumPrinciple.ScalarConsequences
import Topping.Riemannian.TensorNorm

/-!
# The curvature-norm barrier

Topping's Theorem 3.2.11 bounds `|Rm|` along a Ricci flow by
`M / (1 - C M t / 2)`.  Its maximum-principle content concerns the square
`u = |Rm| ^ 2`, which satisfies the parabolic inequality

`∂_t u ≤ Δ u + C u ^ (3/2)`

obtained by weakening the curvature-norm evolution inequality.  The comparison
ODE `φ' = C φ ^ (3/2)` with `φ 0 = M ^ 2` has the explicit solution
`M ^ 2 / (1 - C M t / 2) ^ 2`, whose square root is the stated bound.

This module proves that comparison.  The reaction `r ↦ C r ^ (3/2)` is not
smooth at `r = 0`, so the smooth-reaction route is unavailable; instead the
one-sided Lipschitz bound is established directly, from
`x ^ (3/2) - y ^ (3/2) ≤ (3/2) √x (x - y)` for `0 ≤ y ≤ x`.

The geometric input — that `|Rm| ^ 2` satisfies the displayed inequality — is
the separate curvature-norm evolution statement and is *not* proved here.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian

noncomputable section

namespace Topping

/-- **Math.** The reaction term of the curvature-norm comparison, `r ↦ c r ^ (3/2)`
extended by `0` to negative values. -/
def sesquiReaction (c r : ℝ) : ℝ := c * r * Real.sqrt r

/-- **Math.** The comparison profile solving `φ' = c φ ^ (3/2)` with
`φ 0 = m ^ 2`. -/
def curvatureNormSqBarrier (c m t : ℝ) : ℝ := m ^ 2 / (1 - c * m * t / 2) ^ 2

/-- **Math.** `x ^ (3/2)` has one-sided Lipschitz constant `(3/2) √x` upwards:
for `0 ≤ y ≤ x` one has `x √x - y √y ≤ (3/2) √x (x - y)`.  Writing
`a = √x, b = √y`, this is `2 (a ^ 3 - b ^ 3) ≤ 3 a (a ^ 2 - b ^ 2)`, i.e.
`2 b ^ 2 ≤ a ^ 2 + a b`, which holds because `b ≤ a`. -/
theorem sesqui_sub_le {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    x * Real.sqrt x - y * Real.sqrt y ≤
      3 / 2 * Real.sqrt x * (x - y) := by
  have hx : 0 ≤ x := hy.trans hyx
  have ha : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hb : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hanneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hbnneg : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hba : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hyx
  -- reduce to a polynomial inequality in the square roots
  have hkey : 2 * Real.sqrt y ^ 2 ≤
      Real.sqrt x ^ 2 + Real.sqrt x * Real.sqrt y := by
    nlinarith [mul_le_mul_of_nonneg_left hba hbnneg,
      mul_le_mul_of_nonneg_left hba hanneg]
  calc x * Real.sqrt x - y * Real.sqrt y
      = Real.sqrt x ^ 3 - Real.sqrt y ^ 3 := by
        rw [show Real.sqrt x ^ 3 = Real.sqrt x ^ 2 * Real.sqrt x by ring,
          show Real.sqrt y ^ 3 = Real.sqrt y ^ 2 * Real.sqrt y by ring, ha, hb]
    _ ≤ 3 / 2 * Real.sqrt x * (Real.sqrt x ^ 2 - Real.sqrt y ^ 2) := by
        nlinarith [hkey, sub_nonneg.mpr hba]
    _ = 3 / 2 * Real.sqrt x * (x - y) := by rw [ha, hb]

/-- **Math.** The reaction `sesquiReaction c` has one-sided Lipschitz constant
`(3/2) c √b` on `[a, b]` when `c ≥ 0` and `a ≥ 0`. -/
theorem sesquiReaction_sub_le {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hyx : y ≤ x) :
    sesquiReaction c x - sesquiReaction c y ≤
      3 / 2 * c * Real.sqrt b * (x - y) := by
  have hynneg : 0 ≤ y := ha.trans hy.1
  have hsq := sesqui_sub_le hynneg hyx
  have hxb : Real.sqrt x ≤ Real.sqrt b := Real.sqrt_le_sqrt hx.2
  have hdiff : 0 ≤ x - y := sub_nonneg.mpr hyx
  have hstep : 3 / 2 * Real.sqrt x * (x - y) ≤
      3 / 2 * Real.sqrt b * (x - y) := by
    have := mul_le_mul_of_nonneg_right hxb hdiff
    nlinarith
  have hmain : x * Real.sqrt x - y * Real.sqrt y ≤
      3 / 2 * Real.sqrt b * (x - y) := hsq.trans hstep
  have := mul_le_mul_of_nonneg_left hmain hc
  simp only [sesquiReaction]
  nlinarith

/-- **Math.** The comparison profile solves `φ' = c φ ^ (3/2)` wherever its
denominator is positive, for a positive initial value `m`. -/
theorem curvatureNormSqBarrier_hasDerivWithinAt {c m T t : ℝ} (hm : 0 < m)
    (hdenom : 0 < 1 - c * m * t / 2) :
    HasDerivWithinAt (curvatureNormSqBarrier c m)
      (sesquiReaction c (curvatureNormSqBarrier c m t)) (Icc 0 T) t := by
  have hne : (1 - c * m * t / 2) ≠ 0 := ne_of_gt hdenom
  -- differentiate `m ^ 2 * (1 - c m t / 2) ^ (-2)`
  have hden : HasDerivAt (fun s : ℝ => 1 - c * m * s / 2) (-(c * m / 2)) t := by
    have h : HasDerivAt (fun s : ℝ => c * m * s / 2) (c * m / 2) t := by
      simpa [mul_comm, mul_div_assoc] using
        ((hasDerivAt_id t).const_mul (c * m)).div_const 2
    have h2 := (hasDerivAt_const t (1 : ℝ)).sub h
    convert h2 using 1 <;> first | apply Subsingleton.elim | rfl | ring
  have hsq : HasDerivAt (fun s : ℝ => (1 - c * m * s / 2) ^ 2)
      (2 * (1 - c * m * t / 2) * -(c * m / 2)) t := by
    have h2 := hden.pow 2
    convert h2 using 1 <;> first | apply Subsingleton.elim | rfl | ring
  have hquot := (hasDerivAt_const t (m ^ 2)).div hsq (by positivity)
  -- identify the derivative with the reaction at the barrier value
  have hval : sesquiReaction c (curvatureNormSqBarrier c m t) =
      (0 * (1 - c * m * t / 2) ^ 2 -
          m ^ 2 * (2 * (1 - c * m * t / 2) * -(c * m / 2))) /
        ((1 - c * m * t / 2) ^ 2) ^ 2 := by
    have hsqrt : Real.sqrt (curvatureNormSqBarrier c m t) =
        m / (1 - c * m * t / 2) := by
      rw [curvatureNormSqBarrier, ← div_pow, Real.sqrt_sq]
      positivity
    rw [sesquiReaction, hsqrt, curvatureNormSqBarrier]
    field_simp
    ring
  rw [hval]
  exact hquot.hasDerivWithinAt

/-- **Math.** The comparison profile of Theorem 3.2.11 blows up at `2 / (c m)`:
every level is exceeded strictly before that time.  Choosing a denominator
`d ∈ (0, 1)` with `m ^ 2 / d ^ 2 > B` and setting `t = 2 (1 - d) / (c m)` makes
the profile exactly `m ^ 2 / d ^ 2`. -/
theorem exists_sq_barrier_gt_of_pos {c m B : ℝ} (hc : 0 < c) (hm : 0 < m)
    (hB : 0 < B) :
    ∃ t : ℝ, 0 < t ∧ t < 2 / (c * m) ∧
      B < m ^ 2 / (1 - c * m * t / 2) ^ 2 := by
  obtain ⟨d, hdpos, hdlt1, hdB⟩ :
      ∃ d : ℝ, 0 < d ∧ d < 1 ∧ B * d ^ 2 < m ^ 2 := by
    refine ⟨min (1 / 2) (m / (2 * Real.sqrt B + 1)),
      lt_min (by norm_num) (by positivity),
      lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_⟩
    have h1 : min (1 / 2) (m / (2 * Real.sqrt B + 1)) ≤
        m / (2 * Real.sqrt B + 1) := min_le_right _ _
    have hd0 : 0 < min (1 / 2) (m / (2 * Real.sqrt B + 1)) :=
      lt_min (by norm_num) (by positivity)
    have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.le
    have hsBpos : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
    have hsq : min (1 / 2) (m / (2 * Real.sqrt B + 1)) ^ 2 ≤
        (m / (2 * Real.sqrt B + 1)) ^ 2 := pow_le_pow_left₀ hd0.le h1 2
    have hkey : B * (m / (2 * Real.sqrt B + 1)) ^ 2 < m ^ 2 := by
      rw [div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)]
      have hlt : B < (2 * Real.sqrt B + 1) ^ 2 := by nlinarith
      have hm2 : 0 < m ^ 2 := by positivity
      calc B * m ^ 2 < (2 * Real.sqrt B + 1) ^ 2 * m ^ 2 :=
            mul_lt_mul_of_pos_right hlt hm2
        _ = m ^ 2 * (2 * Real.sqrt B + 1) ^ 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hsq hB.le]
  refine ⟨2 * (1 - d) / (c * m), by positivity, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hc hm, hdpos]
  · have hkey : 1 - c * m * (2 * (1 - d) / (c * m)) / 2 = d := by
      field_simp
      ring
    rw [hkey, lt_div_iff₀ (by positivity)]
    linarith

/-- **Math.** The barrier is positive where its denominator is. -/
theorem curvatureNormSqBarrier_pos {c m t : ℝ} (hm : 0 < m)
    (hdenom : 0 < 1 - c * m * t / 2) :
    0 < curvatureNormSqBarrier c m t := by
  rw [curvatureNormSqBarrier]
  positivity

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M]

/-- **Math.** Topping, Theorem 3.2.11, maximum-principle step.  A nonnegative
quantity `u` obeying `∂_t u ≤ Δ u + c u ^ (3/2)` and starting below `m ^ 2` stays
below the profile `m ^ 2 / (1 - c m t / 2) ^ 2`, on any time interval where that
denominator is positive.

The reaction `r ↦ c r √r` fails to be differentiable at `r = 0`, so the
one-sided Lipschitz bound is supplied directly by `sesquiReaction_sub_le` rather
than by smoothness. -/
theorem curvatureNormSq_le_barrier
    {g : ℝ → RiemannianMetric I M} {u : M → ℝ → ℝ} {c m T : ℝ}
    (hT : 0 ≤ T) (hc : 0 ≤ c) (hm : 0 < m)
    (hcont : ContinuousOn (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hspace : ∀ t ∈ Icc 0 T, ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x => u x t)
    (huderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (u x) (derivWithin (u x) (Icc 0 T) t) (Icc 0 T) t)
    (hpde : ∀ t ∈ Icc 0 T, ∀ x,
      derivWithin (u x) (Icc 0 T) t ≤
        metricLaplacianAt (g t) (fun y => u y t) x + sesquiReaction c (u x t))
    (hdenom : ∀ t ∈ Icc 0 T, 0 < 1 - c * m * t / 2)
    (hunneg : ∀ x t, t ∈ Icc 0 T → 0 ≤ u x t)
    (hzero : ∀ x, u x 0 ≤ m ^ 2) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ curvatureNormSqBarrier c m t := by
  cases isEmpty_or_nonempty M with
  | inl hM => intro x; exact (hM.false x).elim
  | inr hM =>
    letI : Nonempty M := hM
    have hφcont : ContinuousOn (curvatureNormSqBarrier c m) (Icc 0 T) :=
      fun t ht =>
        (curvatureNormSqBarrier_hasDerivWithinAt (T := T) hm
          (hdenom t ht)).continuousWithinAt
    -- a common compact range for `u` and the barrier
    obtain ⟨a, b, hu_range, hφ_range⟩ :=
      exists_common_value_interval hT hcont hφcont
    -- the reaction is nonnegative-side Lipschitz on `[max a 0, b]`
    apply le_ode_solution_of_parabolic_inequality
      (g := g) (X := fun _ => 0)
      (ut := fun x t => derivWithin (u x) (Icc 0 T) t)
      (φ := curvatureNormSqBarrier c m)
      (φ' := fun t => sesquiReaction c (curvatureNormSqBarrier c m t))
      (F := fun r _ => sesquiReaction c r)
      (K := 3 / 2 * c * Real.sqrt b)
      hT hcont hspace huderiv
      (fun t ht => curvatureNormSqBarrier_hasDerivWithinAt hm (hdenom t ht))
      (fun _t _ht => rfl)
    · intro t ht x
      have hdrift :
          (0 : SmoothVectorField I M).dir (fun y => u y t) x = 0 := by
        rw [SmoothVectorField.dir, SmoothVectorField.zero_apply]
        exact map_zero _
      rw [hdrift, add_zero]
      exact hpde t ht x
    · intro t ht x hlt
      -- both compared values are nonnegative, so `[0, b]` contains them
      refine sesquiReaction_sub_le (a := 0) (b := b) hc le_rfl
        ⟨hunneg x t ht, (hu_range x t ht).2⟩
        ⟨(curvatureNormSqBarrier_pos hm (hdenom t ht)).le, (hφ_range t ht).2⟩
        hlt.le
    · intro x
      calc u x 0 ≤ m ^ 2 := hzero x
        _ = curvatureNormSqBarrier c m 0 := by
            rw [curvatureNormSqBarrier]; norm_num

/-- **Math.** Topping, Theorem 3.2.11.  If a nonnegative quantity `v` (to be read
as `|Rm|`) has `v ≤ m` initially and its square obeys
`∂_t(v ^ 2) ≤ Δ(v ^ 2) + c (v ^ 2) ^ (3/2)`, then

`v ≤ m / (1 - c m t / 2)`

wherever the denominator is positive.  This is the square root of the barrier
comparison: the profile `m ^ 2 / (1 - c m t / 2) ^ 2` is a perfect square. -/
theorem curvatureNorm_le
    {g : ℝ → RiemannianMetric I M} {v : M → ℝ → ℝ} {c m T : ℝ}
    (hT : 0 ≤ T) (hc : 0 ≤ c) (hm : 0 < m)
    (hvnneg : ∀ x t, t ∈ Icc 0 T → 0 ≤ v x t)
    (hcont : ContinuousOn (fun z : M × ℝ => v z.1 z.2 ^ 2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hspace : ∀ t ∈ Icc 0 T, ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x => v x t ^ 2)
    (hderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => v x s ^ 2)
        (derivWithin (fun s => v x s ^ 2) (Icc 0 T) t) (Icc 0 T) t)
    (hpde : ∀ t ∈ Icc 0 T, ∀ x,
      derivWithin (fun s => v x s ^ 2) (Icc 0 T) t ≤
        metricLaplacianAt (g t) (fun y => v y t ^ 2) x
          + sesquiReaction c (v x t ^ 2))
    (hdenom : ∀ t ∈ Icc 0 T, 0 < 1 - c * m * t / 2)
    (hzero : ∀ x, v x 0 ≤ m) :
    ∀ x t, t ∈ Icc 0 T → v x t ≤ m / (1 - c * m * t / 2) := by
  have hsq := curvatureNormSq_le_barrier (g := g) (u := fun x t => v x t ^ 2)
    hT hc hm hcont hspace hderiv hpde hdenom
    (fun x t _ht => sq_nonneg (v x t))
    (fun x => by
      have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
      exact pow_le_pow_left₀ (hvnneg x 0 h0) (hzero x) 2)
  intro x t ht
  have hd : 0 < 1 - c * m * t / 2 := hdenom t ht
  have hb := hsq x t ht
  rw [curvatureNormSqBarrier, ← div_pow] at hb
  -- both sides are nonnegative, so compare after taking square roots
  have hrhs : 0 ≤ m / (1 - c * m * t / 2) := by positivity
  nlinarith [hvnneg x t ht, hb, hrhs]

end Comparison

section Riemann

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M]

/-- **Math.** The Riemann tensor of `g` as a covariant `4`-tensor field.  This
agrees with `Topping.riemannTensorField` of `Topping.RicciFlow.Evolution`; it is
restated here so that this module does not depend on the evolution-equation file
(see the note in `riemannNormAt`). -/
def riemannCovTensorField (g : RiemannianMetric I M) : CovTensorField I M 4 :=
  fun Y p => riemannCurvatureAt g p (Y 0 p) (Y 1 p) (Y 2 p) (Y 3 p)

/-- **Math.** `|Rm|` at a point of a metric, as `normAt` of the curvature tensor
field.  This is the quantity Topping's Theorem 3.2.11 bounds. -/
def riemannNormAt (g : RiemannianMetric I M) (p : M) : ℝ :=
  normAt g (riemannCovTensorField g) p

omit [I.Boundaryless] [CompactSpace M] in
/-- **Math.** `|Rm| ≥ 0`. -/
theorem riemannNormAt_nonneg (g : RiemannianMetric I M) (p : M) :
    0 ≤ riemannNormAt g p :=
  normAt_nonneg g _ p

omit [I.Boundaryless] [CompactSpace M] in
/-- **Math.** `|Rm| ^ 2 = normSqAt Rm`. -/
theorem riemannNormAt_sq (g : RiemannianMetric I M) (p : M) :
    riemannNormAt g p ^ 2 = normSqAt g (riemannCovTensorField g) p :=
  normAt_sq g _ p

/-- **Math.** The curvature-norm parabolic inequality of Topping's
Proposition 3.2.10, in the weakened form Theorem 3.2.11 uses: `|Rm| ^ 2` is a
subsolution of the heat equation up to the reaction `c |Rm| ^ 3`.

The `- 2 |∇Rm| ^ 2` term of the proposition has already been discarded here, which
is exactly the weakening the book performs before applying the maximum principle
("after weakening the resulting estimate").  Note `c (|Rm| ^ 2) ^ (3/2)` is
`c |Rm| ^ 3` since `|Rm| ≥ 0`, so this matches `sesquiReaction`. -/
def HasCurvatureNormSqInequalityOn (g : ℝ → RiemannianMetric I M) (c : ℝ)
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ p,
    derivWithin (fun s => riemannNormAt (g s) p ^ 2) J t ≤
      metricLaplacianAt (g t) (fun q => riemannNormAt (g t) q ^ 2) p
        + c * riemannNormAt (g t) p ^ 3

omit [I.Boundaryless] [CompactSpace M] in
/-- **Math.** The reaction of the curvature-norm inequality is the sesquilinear
reaction of the barrier comparison: `c |Rm| ^ 3 = sesquiReaction c (|Rm| ^ 2)`,
because `|Rm| ≥ 0`. -/
theorem sesquiReaction_riemannNormAt_sq (g : RiemannianMetric I M) (c : ℝ)
    (p : M) :
    sesquiReaction c (riemannNormAt g p ^ 2) = c * riemannNormAt g p ^ 3 := by
  rw [sesquiReaction, Real.sqrt_sq (riemannNormAt_nonneg g p)]
  ring

/-- **Math.** Topping, Theorem 3.2.11.  Let `g t` be a family of metrics on a
closed manifold whose curvature norm satisfies the weakened evolution inequality
with constant `c ≥ 0`, and suppose `|Rm| ≤ m` at time `0`, with `m > 0`.  Then

`|Rm| ≤ m / (1 - c m t / 2)`

for every `t` in the time interval on which that denominator stays positive. -/
theorem riemannNormAt_le
    {g : ℝ → RiemannianMetric I M} {c m T : ℝ}
    (hT : 0 ≤ T) (hc : 0 ≤ c) (hm : 0 < m)
    (hcont : ContinuousOn (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hspace : ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x => riemannNormAt (g t) x ^ 2)
    (hderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => riemannNormAt (g s) x ^ 2)
        (derivWithin (fun s => riemannNormAt (g s) x ^ 2) (Icc 0 T) t)
        (Icc 0 T) t)
    (hineq : HasCurvatureNormSqInequalityOn g c (Icc 0 T))
    (hdenom : ∀ t ∈ Icc 0 T, 0 < 1 - c * m * t / 2)
    (hzero : ∀ p, riemannNormAt (g 0) p ≤ m) :
    ∀ p t, t ∈ Icc 0 T →
      riemannNormAt (g t) p ≤ m / (1 - c * m * t / 2) := by
  apply curvatureNorm_le (g := g) (v := fun p t => riemannNormAt (g t) p)
    hT hc hm (fun p t _ht => riemannNormAt_nonneg (g t) p)
    hcont hspace hderiv ?_ hdenom hzero
  intro t ht p
  rw [sesquiReaction_riemannNormAt_sq]
  exact hineq t ht p

end Riemann

end Topping
