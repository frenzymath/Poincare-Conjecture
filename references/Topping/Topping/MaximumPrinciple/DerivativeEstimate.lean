import Topping.MaximumPrinciple.CurvatureNorm

/-!
# The first global curvature derivative estimate

Topping's Theorem 3.3.1 for `k = 1` states `|∇Rm| ≤ C M / √t` on `[0, 1/M]`
whenever `|Rm| ≤ M`.  Its maximum-principle content is a weighted combination
trick: for the auxiliary quantity

`u = t w + α q`,   `w = |∇Rm| ^ 2`,  `q = |Rm| ^ 2`,

the two evolution inequalities

`∂_t w ≤ Δ w + C |Rm| w`,   `∂_t q ≤ Δ q - 2 w + C |Rm| ^ 3`

combine to

`∂_t u ≤ Δ u + w (1 + C t |Rm| - 2 α) + C α |Rm| ^ 3`.

On `[0, 1/M]` with `|Rm| ≤ M` the bracket is `≤ 1 + C - 2 α`, which a large
enough `α` makes nonpositive; the surviving reaction is the *constant* `C α M ^ 3`,
so the comparison ODE is affine and the weak maximum principle gives
`u ≤ α M ^ 2 + C α M ^ 3 t`.  Since `t w ≤ u`, dividing by `t` yields the
estimate.

The reaction here is constant in the solution, so this is the affine-barrier case
of the maximum principle and no Lipschitz work is needed.  The *geometric* inputs
— the two evolution inequalities for `|∇Rm| ^ 2` and `|Rm| ^ 2` — are the separate
`curvature-norm-evolution` statement and its `∇Rm` analogue, and are hypotheses
here.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian

noncomputable section

namespace Topping

/-- **Math.** The affine comparison profile `α m ^ 2 + c t` of the derivative
estimate. -/
def affineBarrier (a c t : ℝ) : ℝ := a + c * t

/-- **Math.** The affine profile solves `φ' = c`. -/
theorem affineBarrier_hasDerivWithinAt (a c : ℝ) {T t : ℝ} :
    HasDerivWithinAt (affineBarrier a c) c (Icc 0 T) t := by
  have h : HasDerivAt (fun s : ℝ => a + c * s) c t := by
    have h2 := (hasDerivAt_const t a).add ((hasDerivAt_id t).const_mul c)
    convert h2 using 1 <;> first | apply Subsingleton.elim | rfl | ring
  exact h.hasDerivWithinAt

section Estimate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M]

/-- **Math.** The weak maximum principle with a reaction that does not depend on
the solution: the comparison profile is then affine.  This is the case used by
the curvature derivative estimates. -/
theorem le_affineBarrier_of_parabolic_inequality
    {g : ℝ → RiemannianMetric I M} {u : M → ℝ → ℝ} {T a c : ℝ}
    (hT : 0 < T)
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => u z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hpde : ∀ t ∈ Icc 0 T, ∀ x,
      derivWithin (u x) (Icc 0 T) t ≤
        metricLaplacianAt (g t) (fun y => u y t) x + c)
    (hzero : ∀ x, u x 0 ≤ a) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ affineBarrier a c t := by
  apply weak_maximum_principle
    (g := g) (X := fun _ => 0) (u := u)
    (φ := affineBarrier a c) (F := fun _ _ => c)
    (T := T) (α := a) hT
  · fun_prop
  · exact hu
  · intro t ht x
    have hdrift :
        (0 : SmoothVectorField I M).dir (fun y => u y t) x = 0 := by
      rw [SmoothVectorField.dir, SmoothVectorField.zero_apply]
      exact map_zero _
    rw [hdrift, add_zero]
    exact hpde t ht x
  · intro t _ht
    exact affineBarrier_hasDerivWithinAt a c
  · simp [affineBarrier]
  · exact hzero

/-- **Math.** Topping, Theorem 3.3.1 for `k = 1`, maximum-principle step.

Let `w` and `q` be nonnegative (to be read as `|∇Rm| ^ 2` and `|Rm| ^ 2`) with
`q ≤ m ^ 2` throughout, on the time interval `[0, T]` with `T ≤ 1 / m`.  Suppose

* `∂_t w ≤ Δ w + c √q · w`   (the `|∇Rm| ^ 2` inequality, with `|Rm| = √q`),
* `∂_t q ≤ Δ q - 2 w + c m ^ 3`  (the `|Rm| ^ 2` inequality).

Then for `α = (1 + c) / 2` the combination `u = t w + α q` obeys
`∂_t u ≤ Δ u + c α m ^ 3`, hence

`t · w ≤ α m ^ 2 + c α m ^ 3 t`.

The reaction bracket is `w (1 + c t √q - 2 α)`, which `t √q ≤ T m ≤ 1` and
`α = (1 + c) / 2` render nonpositive.  This is the estimate before dividing by
`t`; the division and the passage from `w = |∇Rm| ^ 2` to `|∇Rm|` are
`sq_le_of_mul_le` below and the geometric interpretation. -/
theorem mul_le_of_gradient_parabolic_inequalities
    {g : ℝ → RiemannianMetric I M} {w q : M → ℝ → ℝ} {T c m : ℝ}
    (hT : 0 < T) (hc : 0 ≤ c) (hm : 0 < m) (hTm : T * m ≤ 1)
    (hwnneg : ∀ x t, t ∈ Icc 0 T → 0 ≤ w x t)
    (hqnneg : ∀ x t, t ∈ Icc 0 T → 0 ≤ q x t)
    (hqbound : ∀ x t, t ∈ Icc 0 T → q x t ≤ m ^ 2)
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => z.2 * w z.1 z.2 + (1 + c) / 2 * q z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hcomb : ∀ t ∈ Icc 0 T, ∀ x,
      derivWithin (fun s => s * w x s + (1 + c) / 2 * q x s) (Icc 0 T) t ≤
        metricLaplacianAt (g t)
            (fun y => t * w y t + (1 + c) / 2 * q y t) x
          + (w x t * (1 + c * t * Real.sqrt (q x t) - 2 * ((1 + c) / 2))
             + c * ((1 + c) / 2) * m ^ 3)) :
    ∀ x t, t ∈ Icc 0 T →
      t * w x t ≤ affineBarrier ((1 + c) / 2 * m ^ 2)
        (c * ((1 + c) / 2) * m ^ 3) t := by
  set alpha : ℝ := (1 + c) / 2 with halpha
  have halphapos : 0 < alpha := by rw [halpha]; positivity
  -- the reaction bracket is nonpositive: `t √q ≤ T m ≤ 1`
  have hbracket : ∀ x t, t ∈ Icc 0 T →
      w x t * (1 + c * t * Real.sqrt (q x t) - 2 * alpha) ≤ 0 := by
    intro x t ht
    have hsq : Real.sqrt (q x t) ≤ m := by
      rw [show m = Real.sqrt (m ^ 2) by rw [Real.sqrt_sq hm.le]]
      exact Real.sqrt_le_sqrt (hqbound x t ht)
    have hsqnneg : 0 ≤ Real.sqrt (q x t) := Real.sqrt_nonneg _
    have htm : t * Real.sqrt (q x t) ≤ 1 := by
      calc t * Real.sqrt (q x t) ≤ T * m := by
            have h1 : t * Real.sqrt (q x t) ≤ t * m :=
              mul_le_mul_of_nonneg_left hsq ht.1
            have h2 : t * m ≤ T * m :=
              mul_le_mul_of_nonneg_right ht.2 hm.le
            linarith
        _ ≤ 1 := hTm
    have hfac : 1 + c * t * Real.sqrt (q x t) - 2 * alpha ≤ 0 := by
      have hct : c * (t * Real.sqrt (q x t)) ≤ c * 1 :=
        mul_le_mul_of_nonneg_left htm hc
      rw [halpha]
      nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (hwnneg x t ht) hfac
  -- so the combination obeys a parabolic inequality with a constant reaction
  have hconst : ∀ t ∈ Icc 0 T, ∀ x,
      derivWithin (fun s => s * w x s + alpha * q x s) (Icc 0 T) t ≤
        metricLaplacianAt (g t) (fun y => t * w y t + alpha * q y t) x
          + c * alpha * m ^ 3 := by
    intro t ht x
    have h := hcomb t ht x
    have hb := hbracket x t ht
    linarith
  have hzero : ∀ x, (0 : ℝ) * w x 0 + alpha * q x 0 ≤ alpha * m ^ 2 := by
    intro x
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
    have := mul_le_mul_of_nonneg_left (hqbound x 0 h0) halphapos.le
    linarith
  have hmain := le_affineBarrier_of_parabolic_inequality
    (g := g) (u := fun x t => t * w x t + alpha * q x t)
    (a := alpha * m ^ 2) (c := c * alpha * m ^ 3) hT hu hconst hzero
  intro x t ht
  have h := hmain x t ht
  have hq := mul_le_mul_of_nonneg_left (hqnneg x t ht) halphapos.le
  linarith

/-- **Math.** Dividing the previous estimate by `t`: on `[0, T]` with `T ≤ 1 / m`,
`t w ≤ α m ^ 2 + c α m ^ 3 t` gives `w ≤ (α m ^ 2 + c α m ^ 2) / t`, since
`m ^ 3 t ≤ m ^ 2` there.  For `w = |∇Rm| ^ 2` this is `|∇Rm| ≤ C m / √t`. -/
theorem le_div_of_mul_le {w a c m t T : ℝ} (hm : 0 < m) (hc : 0 ≤ c)
    (hT : T * m ≤ 1) (ht : 0 < t) (htT : t ≤ T) (ha : 0 ≤ a)
    (h : t * w ≤ affineBarrier (a * m ^ 2) (c * a * m ^ 3) t) :
    w ≤ (a * m ^ 2 + c * a * m ^ 2) / t := by
  rw [affineBarrier] at h
  have hmt : m ^ 3 * t ≤ m ^ 2 := by
    have h1 : t * m ≤ T * m := mul_le_mul_of_nonneg_right htT hm.le
    have h2 : t * m ≤ 1 := h1.trans hT
    nlinarith [sq_nonneg m, hm.le]
  have hstep : c * a * m ^ 3 * t ≤ c * a * m ^ 2 := by
    have := mul_le_mul_of_nonneg_left hmt (by positivity : (0 : ℝ) ≤ c * a)
    nlinarith
  rw [le_div_iff₀ ht]
  nlinarith

end Estimate

end Topping
