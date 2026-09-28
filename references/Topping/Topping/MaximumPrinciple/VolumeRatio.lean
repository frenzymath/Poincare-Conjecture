import MorganTianLib.Ch01.RiemannianMeasure
import Topping.MaximumPrinciple.Volume
import Topping.RicciFlow.ScalarEvolutionUnconditional

/-!
# The volume ratio decreases (Topping, Cor. 3.2.7)

Topping's Corollary 3.2.7: for a Ricci flow on a closed manifold with
`α := \inf R < 0` at `t = 0`, the ratio

`t ↦ V(t) / (1 + 2(-α)t/n)^{n/2}`

is weakly decreasing, hence `V(t) ≤ V(0)(1 + 2(-α)t/n)^{n/2}`.

His proof differentiates the logarithm:

`(d/dt)\ln[V/(1+2(-α)t/n)^{n/2}] = -(1/V)∫R\,dV + α/(1 - 2αt/n) ≤ -\inf_\M R(t) + α/(1-2αt/n) ≤ 0`,

the last step being Theorem 3.2.1 — the quadratic lower barrier.

What the module supplies, and it is worth stating precisely because the sloppy
version of this claim is tempting: the denominator of the volume ratio and the
denominator of the scalar barrier are **the same expression**, recorded as `rfl` in
`scalarLowerBarrier_eq_div_volumeRatioDenom`. The exponent `n/2` is what makes the
chain rule turn `D' = -2α/n` into exactly `-α · D^{n/2-1}`, so the barrier's value
`α/D` is what the quotient rule needs and no cruder bound on `R` would do. That is
an identification, not a claim about how tight the final inequality is: the proof
below bounds a numerator by zero and does not divide by `V`, so it is one-sided and
carries no information about the sign of `V`.

Note `(1 + 2(-α)t/n) = (1 - 2αt/n)`; the file works with
`volumeRatioDenom α t := 1 - 2αt/n` throughout.

**Antecedents.** As in `Volume.lean`, `V' = -∫R\,dV` is the named hypothesis
`HasVolumeDerivativeOn` (the integrated volume-form variation, not available in this
project). `IsVolumeOfMeasureOn` adds that `V(t)` is the total mass of `μ t` and that
`R` is `μ t`-integrable — both true for a continuous scalar curvature on a closed
manifold, and what turns the pointwise barrier into the integral bound. No
positivity of `V` is needed or assumed. The scalar lower bound is *proved*, from
`HasScalarCurvatureEvolutionOn`.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian MeasureTheory

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [MeasurableSpace M]

/-! ### The comparison denominator -/

/-- **Math.** Topping's factor `1 + 2(-α)t/n = 1 - 2αt/n`, the denominator of both
the volume ratio (to the power `n/2`) and the scalar lower barrier. -/
def volumeRatioDenom (n : ℕ) (alpha t : ℝ) : ℝ := 1 - (2 / (n : ℝ)) * alpha * t

/-- **Math.** Topping's volume ratio `V(t)/(1 + 2(-α)t/n)^{n/2}`. -/
def volumeRatio (n : ℕ) (alpha : ℝ) (V : ℝ → ℝ) (t : ℝ) : ℝ :=
  V t / volumeRatioDenom n alpha t ^ ((n : ℝ) / 2)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless] [SigmaCompactSpace M]
  [T2Space M] [MeasurableSpace M] in
/-- **Math.** For `α ≤ 0` the denominator is at least `1` at every nonnegative
time, so in particular positive: the subtracted term is a product of a nonnegative
and a nonpositive factor. -/
theorem one_le_volumeRatioDenom (alpha : ℝ) (halpha : alpha ≤ 0) {t : ℝ}
    (ht : 0 ≤ t) : 1 ≤ volumeRatioDenom (Module.finrank ℝ E) alpha t := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have : (2 / (Module.finrank ℝ E : ℝ)) * alpha * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) halpha) ht
  rw [volumeRatioDenom]
  linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [MeasurableSpace M] in
/-- **Math.** The scalar lower barrier of Theorem 3.2.1 is `α` divided by this same
denominator. This is the identification that makes the cancellation in the
log-derivative exact. -/
theorem scalarLowerBarrier_eq_div_volumeRatioDenom (alpha t : ℝ) :
    scalarLowerBarrier (Module.finrank ℝ E) alpha t =
      alpha / volumeRatioDenom (Module.finrank ℝ E) alpha t := rfl

/-! ### The volume is the total mass of its measure

Topping's `-(1/V)∫R\,dV` presumes `V(t) = \Vol_{g(t)}(\M)`, i.e. that `V` is the
total mass of `μ t`. That is what converts a *pointwise* lower bound on `R` into a
lower bound on the integral, so it is stated explicitly rather than left implicit in
the notation. -/

/-- **Math.** `V(t)` is the total mass of the volume measure `μ t`, and `R` is
`μ t`-integrable — both true for a continuous scalar curvature on a closed manifold,
and both needed to turn the pointwise barrier into an integral bound. -/
def IsVolumeOfMeasureOn (g : ℝ → RiemannianMetric I M) (V : ℝ → ℝ)
    (μ : ℝ → Measure M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, (μ t).real univ = V t ∧
    Integrable (fun p => scalarCurvatureAt (g t) p) (μ t)

section CanonicalVolumeMeasure

variable [MeasurableSpace E] [BorelSpace E] [CompactSpace M] [BorelSpace M]
  [SecondCountableTopology M] [Nonempty M]

/-- **Math.** On a closed manifold, the canonical Riemannian measure genuinely
witnesses `IsVolumeOfMeasureOn`: its associated volume is its total mass, and
scalar curvature is integrable because it is smooth. -/
theorem isVolumeOfMeasureOn_riemannianMeasure
    (g : ℝ → RiemannianMetric I M) (μ₀ : Measure E) (J : Set ℝ)
    (hfinite : ∀ t : ℝ, IsFiniteMeasure
      (MorganTianLib.riemannianMeasure (I := I) (g t) μ₀)) :
    IsVolumeOfMeasureOn g
      (fun t => (MorganTianLib.riemannianMeasure (I := I) (g t) μ₀).real univ)
      (fun t => MorganTianLib.riemannianMeasure (I := I) (g t) μ₀) J := by
  intro t _ht
  letI := hfinite t
  refine ⟨rfl, ?_⟩
  exact (scalarCurvatureAt_contMDiff (g t)).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

#print axioms Topping.isVolumeOfMeasureOn_riemannianMeasure

end CanonicalVolumeMeasure

set_option linter.unusedSectionVars false in
/-- **Math.** A pointwise lower bound on `R` integrates to `∫R\,dV ≥ c·V(t)`: the
constant function `c` is integrable against a finite measure and `∫c\,dV = c·V(t)`
once `V(t)` is the total mass. This is the step Topping writes as
`(1/V)∫R\,dV ≥ \inf_\M R`. -/
theorem mul_volume_le_integral_scalarCurvature
    {g : ℝ → RiemannianMetric I M} {V : ℝ → ℝ} {μ : ℝ → Measure M} {J : Set ℝ}
    (hVμ : IsVolumeOfMeasureOn g V μ J) {t : ℝ} (ht : t ∈ J)
    [IsFiniteMeasure (μ t)] {c : ℝ} (hc : ∀ p, c ≤ scalarCurvatureAt (g t) p) :
    c * V t ≤ ∫ p, scalarCurvatureAt (g t) p ∂(μ t) := by
  obtain ⟨hmass, hint⟩ := hVμ t ht
  have hmono : ∫ _p : M, c ∂(μ t) ≤ ∫ p, scalarCurvatureAt (g t) p ∂(μ t) :=
    integral_mono (integrable_const c) hint hc
  rwa [integral_const, hmass, smul_eq_mul, mul_comm] at hmono

/-! ### The ratio's derivative -/

set_option linter.unusedSectionVars false in
/-- **Math.** **The log-derivative computation of Topping's Corollary 3.2.7.** The
volume ratio has nonpositive derivative at `t`, given `R ≥ α/(1-2αt/n)` there.

Writing `D` for the denominator and `p = n/2`, the quotient rule gives

`ratio' = (V'D^p + αVD^{p-1})/D^{2p}`,

because `D' = -2α/n` contributes `D' · p = -α`. The barrier bounds
`V' = -∫R\,dV ≤ -(α/D)V`, and `-(α/D)V · D^p` is `-αVD^{p-1}` — the same expression
as the second term, so the numerator is bounded by `0`.

This is a one-sided bound on the numerator, not a computation of the derivative: it
shows the sign, and needs no hypothesis on `V`. The exponent `n/2` is what makes the
two expressions match, which is the reason the barrier of Theorem 3.2.1 rather than
some weaker bound on `R` is the right input. -/
theorem derivWithin_volumeRatio_nonpos
    {g : ℝ → RiemannianMetric I M} {V : ℝ → ℝ} {μ : ℝ → Measure M} {J : Set ℝ}
    {alpha t : ℝ} (halpha : alpha ≤ 0) (ht0 : 0 ≤ t) (ht : t ∈ J)
    [IsFiniteMeasure (μ t)]
    (hV : HasVolumeDerivativeOn g V μ J) (hVμ : IsVolumeOfMeasureOn g V μ J)
    (hbar : ∀ p, scalarLowerBarrier (Module.finrank ℝ E) alpha t ≤
      scalarCurvatureAt (g t) p) :
    ∃ r : ℝ, r ≤ 0 ∧
      HasDerivWithinAt (volumeRatio (Module.finrank ℝ E) alpha V) r J t := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  set n := (Module.finrank ℝ E : ℝ) with hnd
  set D := volumeRatioDenom (Module.finrank ℝ E) alpha with hD
  have hD1 : 1 ≤ D t := one_le_volumeRatioDenom (E := E) alpha halpha ht0
  have hDpos : 0 < D t := lt_of_lt_of_le zero_lt_one hD1
  -- the denominator is affine with slope `-2α/n`
  have hDderiv : HasDerivAt D (-(2 / n) * alpha) t := by
    have h := (hasDerivAt_const t (1 : ℝ)).sub
      ((hasDerivAt_id t).const_mul ((2 / n) * alpha))
    rw [hD]
    convert h using 1 <;> first | rfl | ring
  -- its `n/2` power differentiates to `-α D^{n/2-1}`
  have hpow : HasDerivAt (fun s => D s ^ (n / 2)) (-alpha * D t ^ (n / 2 - 1)) t := by
    have h := hDderiv.rpow_const (p := n / 2) (Or.inl (ne_of_gt hDpos))
    convert h using 1
    field_simp
  have hpowpos : 0 < D t ^ (n / 2) := Real.rpow_pos_of_pos hDpos _
  refine ⟨_, ?_, (hV t ht).div hpow.hasDerivWithinAt (ne_of_gt hpowpos)⟩
  -- the barrier turns `V' = -∫R` into a bound that cancels the second term exactly
  have hbarint : alpha / D t * V t ≤ ∫ p, scalarCurvatureAt (g t) p ∂(μ t) := by
    refine mul_volume_le_integral_scalarCurvature hVμ ht ?_
    intro p
    have := hbar p
    rwa [scalarLowerBarrier_eq_div_volumeRatioDenom] at this
  have hsplit : D t ^ (n / 2) = D t * D t ^ (n / 2 - 1) := by
    have h : D t ^ (1 + (n / 2 - 1)) = D t ^ (1 : ℝ) * D t ^ (n / 2 - 1) :=
      Real.rpow_add hDpos 1 _
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  have hpm1 : 0 < D t ^ (n / 2 - 1) := Real.rpow_pos_of_pos hDpos _
  -- numerator is at most zero
  have hnum : (-∫ p, scalarCurvatureAt (g t) p ∂(μ t)) * D t ^ (n / 2)
      - V t * (-alpha * D t ^ (n / 2 - 1)) ≤ 0 := by
    have hkey : (alpha / D t * V t) * D t ^ (n / 2) ≤
        (∫ p, scalarCurvatureAt (g t) p ∂(μ t)) * D t ^ (n / 2) :=
      mul_le_mul_of_nonneg_right hbarint hpowpos.le
    have hlhs : (alpha / D t * V t) * D t ^ (n / 2)
        = alpha * V t * D t ^ (n / 2 - 1) := by
      rw [hsplit]
      field_simp
    rw [hlhs] at hkey
    nlinarith [hkey]
  exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)

/-! ### Corollary 3.2.7 -/

section

variable [CompactSpace M]

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Corollary 3.2.7, first half.** For a Ricci flow on a closed
manifold with `α := \inf R ≤ 0` at `t = 0`, the ratio
`V(t)/(1 + 2(-α)t/n)^{n/2}` is weakly decreasing on `[0,T]`.

The scalar lower bound is *proved* here, from `HasScalarCurvatureEvolutionOn`, via
`scalarLowerBarrier_le_of_initial_nonpos` — which is the reason `α ≤ 0` is the right
hypothesis rather than a convenience: for a nonpositive initial bound the barrier's
denominator is positive at every time, so Theorem 3.2.1 needs no restriction on `T`
(the book's `α < 0` is the case of interest, and `α = 0` is covered too). -/
theorem volumeRatio_antitoneOn
    {g : ℝ → RiemannianMetric I M} {V : ℝ → ℝ} {μ : ℝ → Measure M} {T alpha : ℝ}
    (hT : 0 < T) (halpha : alpha ≤ 0)
    [∀ t : ℝ, IsFiniteMeasure (μ t)]
    (hRsmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T))
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p)
    (hV : HasVolumeDerivativeOn g V μ (Icc 0 T))
    (hVμ : IsVolumeOfMeasureOn g V μ (Icc 0 T)) :
    AntitoneOn (volumeRatio (Module.finrank ℝ E) alpha V) (Icc 0 T) := by
  -- Theorem 3.2.1 supplies the barrier at every time, with no bound on `T`.
  have hbar : ∀ t ∈ Icc 0 T, ∀ p,
      scalarLowerBarrier (Module.finrank ℝ E) alpha t ≤
        scalarCurvatureAt (g t) p := by
    intro t ht p
    exact scalarLowerBarrier_le_of_initial_nonpos hT hRsmooth hevolution halpha
      hzero p t ht
  -- Name the derivative at each time of the interval, with its sign.
  have hder : ∀ t ∈ Icc 0 T, ∃ r : ℝ, r ≤ 0 ∧
      HasDerivWithinAt (volumeRatio (Module.finrank ℝ E) alpha V) r (Icc 0 T) t :=
    fun t ht => derivWithin_volumeRatio_nonpos (E := E) (μ := μ)
      halpha ht.1 ht hV hVμ (hbar t ht)
  choose! r hrneg hrderiv using hder
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
    (fun t ht => (hrderiv t ht).continuousWithinAt) (f' := r)
    (fun t ht => (hrderiv t (interior_subset ht)).mono interior_subset)
    (fun t ht => hrneg t (interior_subset ht))

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Corollary 3.2.7, displayed conclusion.**
`V(t) ≤ V(0)(1 + 2(-α)t/n)^{n/2}` on `[0,T]`.

This is the monotone ratio evaluated against `t = 0`, where the denominator is `1`.
-/
theorem volume_le_of_scalarCurvature_initial_ge
    {g : ℝ → RiemannianMetric I M} {V : ℝ → ℝ} {μ : ℝ → Measure M} {T alpha : ℝ}
    (hT : 0 < T) (halpha : alpha ≤ 0)
    [∀ t : ℝ, IsFiniteMeasure (μ t)]
    (hRsmooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T))
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p)
    (hV : HasVolumeDerivativeOn g V μ (Icc 0 T))
    (hVμ : IsVolumeOfMeasureOn g V μ (Icc 0 T)) :
    ∀ t ∈ Icc 0 T,
      V t ≤ V 0 * volumeRatioDenom (Module.finrank ℝ E) alpha t ^
        ((Module.finrank ℝ E : ℝ) / 2) := by
  intro t ht
  have hanti := volumeRatio_antitoneOn (E := E) hT halpha hRsmooth hevolution hzero hV hVμ
  have h := hanti (left_mem_Icc.mpr hT.le) ht ht.1
  have hD1 : 1 ≤ volumeRatioDenom (Module.finrank ℝ E) alpha t :=
    one_le_volumeRatioDenom (E := E) alpha halpha ht.1
  have hDpos : 0 < volumeRatioDenom (Module.finrank ℝ E) alpha t :=
    lt_of_lt_of_le zero_lt_one hD1
  have hpowpos : 0 < volumeRatioDenom (Module.finrank ℝ E) alpha t ^
      ((Module.finrank ℝ E : ℝ) / 2) := Real.rpow_pos_of_pos hDpos _
  have hzeroD : volumeRatioDenom (Module.finrank ℝ E) alpha 0 ^
      ((Module.finrank ℝ E : ℝ) / 2) = 1 := by
    rw [show volumeRatioDenom (Module.finrank ℝ E) alpha 0 = 1 by
      simp [volumeRatioDenom], Real.one_rpow]
  rw [volumeRatio, volumeRatio, hzeroD, div_one] at h
  rw [div_le_iff₀ hpowpos] at h
  linarith

end

end Topping

end
