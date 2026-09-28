import Topping.MaximumPrinciple.CurvatureNormEvolution
import Topping.MaximumPrinciple.DerivativeEstimate

/-!
# Theorem 3.3.1 for `k = 1`, at the actual `|∇Rm|`

`Topping.MaximumPrinciple.DerivativeEstimate` proves the maximum-principle content
of Topping's Theorem 3.3.1 over *abstract* nonnegative quantities `w` and `q`.
This module instantiates it at the geometric quantities it is about,

`w = |∇\Rm|^2`,  `q = |\Rm|^2`,

and takes the square root, giving Topping's `k = 1` estimate

`|∇\Rm| ≤ C M / √t`   on `(0, T]`, `T ≤ 1/M`, whenever `|\Rm| ≤ M`.

The geometric input is the `∇\Rm` analogue of Proposition 3.2.10,

`∂_t|∇\Rm|^2 ≤ Δ|∇\Rm|^2 - 2|∇^2\Rm|^2 + C|\Rm|\,|∇\Rm|^2`,

which Topping derives from the commutation formulae
`∇(Δ\Rm) = Δ(∇\Rm) + \Rm*∇\Rm` and
`∇∂_t\Rm = ∂_t∇\Rm + \Rm*∇\Rm`. It is a named hypothesis here, exactly like the
two ingredients of 3.2.10; nothing in the project proves it yet.

What *is* proved here is the whole maximum-principle half at the real curvature:
the weighted combination `u = t|∇\Rm|^2 + α|\Rm|^2`, the choice of `α` killing
the reaction bracket, the affine comparison, the division by `t`, and the square
root. So the remaining gap on `first-derivative-estimate` is precisely the two
geometric evolution inequalities and nothing else.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M]

/-- **Math.** The `∇\Rm` analogue of Proposition 3.2.10, in the weakened form the
derivative estimate uses: `∂_t|∇\Rm|^2 ≤ Δ|∇\Rm|^2 + c|\Rm|\,|∇\Rm|^2`.

The favourable `-2|∇^2\Rm|^2` has already been discarded, as in the passage from
`HasCurvatureNormEvolutionInequalityOn` to `HasCurvatureNormSqInequalityOn`. -/
def HasGradCurvatureNormSqInequalityOn (g : ℝ → RiemannianMetric I M) (c : ℝ)
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ p : M,
    derivWithin (fun s => gradRiemannNormSqAt (g s) p) J t ≤
      metricLaplacianAt (g t) (fun q => gradRiemannNormSqAt (g t) q) p
        + c * riemannNormAt (g t) p * gradRiemannNormSqAt (g t) p

set_option linter.unusedSectionVars false in
/-- **Math.** The reaction of the `∇\Rm` inequality is the one
`mul_le_of_gradient_parabolic_inequalities` expects: `|\Rm| = √(|\Rm|^2)`, so
`c|\Rm|w` is `c√q·w` with `q = |\Rm|^2`. -/
theorem sqrt_riemannNormAt_sq (g : RiemannianMetric I M) (p : M) :
    Real.sqrt (riemannNormAt g p ^ 2) = riemannNormAt g p :=
  Real.sqrt_sq (riemannNormAt_nonneg g p)

set_option linter.unusedSectionVars false in
/-- **Math.** **The weighted combination step of Topping's Theorem 3.3.1.** The
two evolution inequalities really do combine into the parabolic inequality for
`u = t|∇\Rm|^2 + α|\Rm|^2` that the maximum principle consumes.

This is the Leibniz computation the book performs in one line. Writing
`w = |∇\Rm|^2` and `q = |\Rm|^2`, the time derivative of `u` is
`w + t w' + α q'` by the product rule, and the Laplacian is `tΔw + αΔq` by
linearity, so the two inequalities

`w' ≤ Δw + c|\Rm|w`,   `q' ≤ Δq - 2w + c|\Rm|^3`

give
`u' ≤ Δu + w(1 + ct|\Rm| - 2α) + αc|\Rm|^3`,
and `|\Rm| ≤ m` bounds the last term by `αcm^3`. Nothing here is assumed beyond
the two inequalities, the differentiability of `w` and `q` in time, and the
smoothness in space that makes `Δ` linear. -/
theorem hcomb_of_evolution_inequalities
    {g : ℝ → RiemannianMetric I M} {T c m : ℝ} (hT : 0 < T) (hc : 0 ≤ c)
    (hbound : ∀ p, ∀ t ∈ Icc 0 T, riemannNormAt (g t) p ≤ m)
    (hwderiv : ∀ p, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => gradRiemannNormSqAt (g s) p)
        (derivWithin (fun s => gradRiemannNormSqAt (g s) p) (Icc 0 T) t)
        (Icc 0 T) t)
    (hqderiv : ∀ p, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => riemannNormAt (g s) p ^ 2)
        (derivWithin (fun s => riemannNormAt (g s) p ^ 2) (Icc 0 T) t)
        (Icc 0 T) t)
    (hwsmooth : ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun q => gradRiemannNormSqAt (g t) q)
    (hqsmooth : ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun q => riemannNormAt (g t) q ^ 2)
    (hw : HasGradCurvatureNormSqInequalityOn g c (Icc 0 T))
    (hq : HasCurvatureNormEvolutionInequalityOn g c (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, ∀ p,
      derivWithin (fun s => s * gradRiemannNormSqAt (g s) p
          + (1 + c) / 2 * riemannNormAt (g s) p ^ 2) (Icc 0 T) t ≤
        metricLaplacianAt (g t)
            (fun q => t * gradRiemannNormSqAt (g t) q
              + (1 + c) / 2 * riemannNormAt (g t) q ^ 2) p
          + (gradRiemannNormSqAt (g t) p *
              (1 + c * t * riemannNormAt (g t) p - 2 * ((1 + c) / 2))
             + c * ((1 + c) / 2) * m ^ 3) := by
  intro t ht p
  set alpha : ℝ := (1 + c) / 2 with halpha
  set w := fun s => gradRiemannNormSqAt (g s) p with hw'
  set q := fun s => riemannNormAt (g s) p ^ 2 with hq'
  -- the product rule for `s ↦ s * w s + α * q s`
  have hderiv : HasDerivWithinAt (fun s => s * w s + alpha * q s)
      (w t + t * derivWithin w (Icc 0 T) t
        + alpha * derivWithin q (Icc 0 T) t) (Icc 0 T) t := by
    have hid : HasDerivWithinAt (fun s : ℝ => s) 1 (Icc 0 T) t :=
      (hasDerivAt_id t).hasDerivWithinAt
    have hprod : HasDerivWithinAt (fun s => s * w s)
        (1 * w t + t * derivWithin w (Icc 0 T) t) (Icc 0 T) t :=
      hid.mul (hwderiv p t ht)
    have hsc : HasDerivWithinAt (fun s => alpha * q s)
        (alpha * derivWithin q (Icc 0 T) t) (Icc 0 T) t :=
      (hqderiv p t ht).const_mul alpha
    have hsum := hprod.add hsc
    rw [one_mul] at hsum
    exact hsum
  rw [hderiv.derivWithin (uniqueDiffOn_Icc hT t ht)]
  -- the Laplacian of the combination splits by linearity
  have hlap : metricLaplacianAt (g t)
      (fun y => t * gradRiemannNormSqAt (g t) y
        + alpha * riemannNormAt (g t) y ^ 2) p
      = t * metricLaplacianAt (g t) (fun y => gradRiemannNormSqAt (g t) y) p
        + alpha * metricLaplacianAt (g t) (fun y => riemannNormAt (g t) y ^ 2) p := by
    have hws : ContMDiff I 𝓘(ℝ, ℝ) ∞ fun y => t * gradRiemannNormSqAt (g t) y :=
      contMDiff_const.mul (hwsmooth t ht)
    have hqs : ContMDiff I 𝓘(ℝ, ℝ) ∞ fun y => alpha * riemannNormAt (g t) y ^ 2 :=
      contMDiff_const.mul (hqsmooth t ht)
    rw [metricLaplacianAt_add (g t) hws hqs,
      metricLaplacianAt_const_mul (g t) t (hwsmooth t ht),
      metricLaplacianAt_const_mul (g t) alpha (hqsmooth t ht)]
  rw [hlap]
  -- the two geometric inequalities, and `|Rm| ≤ m` on the cubic term
  have hwt := hw t ht p
  have hqt := hq t ht p
  have hwnn : 0 ≤ gradRiemannNormSqAt (g t) p := gradRiemannNormSqAt_nonneg (g t) p
  have htnn : 0 ≤ t := ht.1
  have hRnn : 0 ≤ riemannNormAt (g t) p := riemannNormAt_nonneg (g t) p
  have hRm : riemannNormAt (g t) p ≤ m := hbound p t ht
  have hcube : c * riemannNormAt (g t) p ^ 3 ≤ c * m ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRnn hRm 3) hc
  -- `t * (w' bound)` and `α * (q' bound)`
  have hwscaled := mul_le_mul_of_nonneg_left hwt htnn
  have halphann : 0 ≤ alpha := by rw [halpha]; linarith
  have hqscaled := mul_le_mul_of_nonneg_left hqt halphann
  have hcubescaled := mul_le_mul_of_nonneg_left hcube halphann
  show gradRiemannNormSqAt (g t) p
      + t * derivWithin (fun s => gradRiemannNormSqAt (g s) p) (Icc 0 T) t
      + alpha * derivWithin (fun s => riemannNormAt (g s) p ^ 2) (Icc 0 T) t ≤ _
  simp only [halpha] at hwscaled hqscaled hcubescaled ⊢
  nlinarith [hwscaled, hqscaled, hcubescaled, hwnn, htnn, hRnn]

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Theorem 3.3.1 for `k = 1`, at the real curvature.**
On `[0,T]` with `T ≤ 1/m` and `|\Rm| ≤ m`, the two evolution inequalities give

`t|∇\Rm|^2 ≤ α m^2 + cα m^3 t`,   `α = (1+c)/2`.

This is `mul_le_of_gradient_parabolic_inequalities` instantiated at
`w = |∇\Rm|^2`, `q = |\Rm|^2`. The reaction bracket vanishes for that `α` because
`t|\Rm| ≤ Tm ≤ 1`; the surviving reaction is the constant `cαm^3`, so the
comparison ODE is affine. -/
theorem mul_gradRiemannNormSq_le
    {g : ℝ → RiemannianMetric I M} {T c m : ℝ}
    (hT : 0 < T) (hc : 0 ≤ c) (hm : 0 < m) (hTm : T * m ≤ 1)
    (hbound : ∀ p, ∀ t ∈ Icc 0 T, riemannNormAt (g t) p ≤ m)
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => z.2 * gradRiemannNormSqAt (g z.2) z.1
        + (1 + c) / 2 * riemannNormAt (g z.2) z.1 ^ 2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hcomb : ∀ t ∈ Icc 0 T, ∀ p,
      derivWithin (fun s => s * gradRiemannNormSqAt (g s) p
          + (1 + c) / 2 * riemannNormAt (g s) p ^ 2) (Icc 0 T) t ≤
        metricLaplacianAt (g t)
            (fun q => t * gradRiemannNormSqAt (g t) q
              + (1 + c) / 2 * riemannNormAt (g t) q ^ 2) p
          + (gradRiemannNormSqAt (g t) p *
              (1 + c * t * riemannNormAt (g t) p - 2 * ((1 + c) / 2))
             + c * ((1 + c) / 2) * m ^ 3)) :
    ∀ p t, t ∈ Icc 0 T →
      t * gradRiemannNormSqAt (g t) p ≤
        affineBarrier ((1 + c) / 2 * m ^ 2) (c * ((1 + c) / 2) * m ^ 3) t := by
  apply mul_le_of_gradient_parabolic_inequalities
    (g := g) (w := fun p t => gradRiemannNormSqAt (g t) p)
    (q := fun p t => riemannNormAt (g t) p ^ 2)
    hT hc hm hTm
    (fun p t _ht => gradRiemannNormSqAt_nonneg (g t) p)
    (fun p t _ht => sq_nonneg (riemannNormAt (g t) p))
    (fun p t ht => pow_le_pow_left₀ (riemannNormAt_nonneg (g t) p)
      (hbound p t ht) 2)
    hu
  intro t ht p
  rw [sqrt_riemannNormAt_sq]
  exact hcomb t ht p

set_option linter.unusedSectionVars false in
/-- **Math.** `|∇\Rm| ≤ C m / √t`: the square root of the previous estimate,
which is Topping's Theorem 3.3.1 for `k = 1` as displayed in the book.

The constant is `C = √(2α)` with `α = (1+c)/2`, i.e. `√(1+c)`: dividing by `t`
gives `|∇\Rm|^2 ≤ (α + cα) m^2 / t`, and `α + cα = α(1+c) = (1+c)^2/2`. -/
theorem gradRiemannNorm_le_div_sqrt
    {g : ℝ → RiemannianMetric I M} {T c m t : ℝ}
    (hc : 0 ≤ c) (hm : 0 < m) (hTm : T * m ≤ 1) (ht : 0 < t) (htT : t ≤ T)
    {p : M}
    (h : t * gradRiemannNormSqAt (g t) p ≤
      affineBarrier ((1 + c) / 2 * m ^ 2) (c * ((1 + c) / 2) * m ^ 3) t) :
    Real.sqrt (gradRiemannNormSqAt (g t) p) ≤
      Real.sqrt ((1 + c) / 2 * (1 + c)) * m / Real.sqrt t := by
  have halpha : (0 : ℝ) ≤ (1 + c) / 2 := by linarith
  have hstep := le_div_of_mul_le (w := gradRiemannNormSqAt (g t) p)
    (a := (1 + c) / 2) (c := c) (m := m) (t := t) (T := T)
    hm hc hTm ht htT halpha h
  -- `(α m ^ 2 + c α m ^ 2) / t = (α (1 + c)) m ^ 2 / t`
  have hrw : (1 + c) / 2 * m ^ 2 + c * ((1 + c) / 2) * m ^ 2
      = (1 + c) / 2 * (1 + c) * m ^ 2 := by ring
  rw [hrw] at hstep
  calc Real.sqrt (gradRiemannNormSqAt (g t) p)
      ≤ Real.sqrt ((1 + c) / 2 * (1 + c) * m ^ 2 / t) := Real.sqrt_le_sqrt hstep
    _ = Real.sqrt ((1 + c) / 2 * (1 + c)) * m / Real.sqrt t := by
        rw [Real.sqrt_div (by positivity) t, Real.sqrt_mul (by positivity),
          Real.sqrt_sq hm.le]

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Theorem 3.3.1 for `k = 1`, end to end.** The two
geometric evolution inequalities, plus regularity, give

`|∇\Rm| ≤ √((1+c)^2/2) · m / √t`   for `t ∈ (0,T]`, `T ≤ 1/m`,

whenever `|\Rm| ≤ m` on `[0,T]`. This composes the whole chain in one statement:
`hcomb_of_evolution_inequalities` (the Leibniz combination),
`mul_gradRiemannNormSq_le` (the affine comparison via the weak maximum principle),
and `gradRiemannNorm_le_div_sqrt` (division by `t` and the square root).

The hypotheses are now exactly the geometric inputs and the regularity the
computation needs; no combined parabolic inequality is assumed. The two open
geometric antecedents are `HasGradCurvatureNormSqInequalityOn` and Proposition
3.2.10, and nothing else. -/
theorem gradRiemannNorm_le_of_evolution_inequalities
    {g : ℝ → RiemannianMetric I M} {T c m : ℝ}
    (hT : 0 < T) (hc : 0 ≤ c) (hm : 0 < m) (hTm : T * m ≤ 1)
    (hbound : ∀ p, ∀ t ∈ Icc 0 T, riemannNormAt (g t) p ≤ m)
    (hwderiv : ∀ p, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => gradRiemannNormSqAt (g s) p)
        (derivWithin (fun s => gradRiemannNormSqAt (g s) p) (Icc 0 T) t)
        (Icc 0 T) t)
    (hqderiv : ∀ p, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun s => riemannNormAt (g s) p ^ 2)
        (derivWithin (fun s => riemannNormAt (g s) p ^ 2) (Icc 0 T) t)
        (Icc 0 T) t)
    (hwsmooth : ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun q => gradRiemannNormSqAt (g t) q)
    (hqsmooth : ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ fun q => riemannNormAt (g t) q ^ 2)
    (hu : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => z.2 * gradRiemannNormSqAt (g z.2) z.1
        + (1 + c) / 2 * riemannNormAt (g z.2) z.1 ^ 2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hw : HasGradCurvatureNormSqInequalityOn g c (Icc 0 T))
    (hq : HasCurvatureNormEvolutionInequalityOn g c (Icc 0 T)) :
    ∀ p, ∀ t, 0 < t → t ≤ T →
      Real.sqrt (gradRiemannNormSqAt (g t) p) ≤
        Real.sqrt ((1 + c) / 2 * (1 + c)) * m / Real.sqrt t := by
  have hcomb := hcomb_of_evolution_inequalities hT hc hbound hwderiv hqderiv
    hwsmooth hqsmooth hw hq
  have hmul := mul_gradRiemannNormSq_le hT hc hm hTm hbound hu hcomb
  intro p t htpos htT
  exact gradRiemannNorm_le_div_sqrt hc hm hTm htpos htT
    (hmul p t ⟨htpos.le, htT⟩)

end Topping

end
