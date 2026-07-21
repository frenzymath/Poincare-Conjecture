import PetersenLib.Ch05.DistanceSegments
import PetersenLib.Ch05.EnergyMinimizers
import PetersenLib.Ch05.MetricTopology
import PetersenLib.Ch05.SpeedIntegrable

/-!
# Petersen Ch. 5, §5.2 — distance functions produce geodesics (Remark 5.2.1)

Petersen's Remark 5.2.1 observes that if `r : U → ℝ` is a *distance function*
(`|∇r| ≡ 1` on the open set `U`), then the integral curves of `∂_r = ∇r` are
geodesics.

## What this file provides

* `distanceFunction_curveLength_ge_on` — the `ContMDiffOn (Icc a b)`
  generalisation of `distanceFunction_curveLength_ge`.
* `distanceFunction_curveLength_ge_piecewise` — the same bound for a
  piecewise-`C^∞` curve, by telescoping over the partition.
* `CurveVariation.eventually_mem_of_isOpen` — a tube lemma: every curve of a
  variation of `γ` stays in an open `U ⊇ γ([a,b])` for parameters near `0`.
* `curveLength_sq_le_sub_mul_two_mul_energyFunctional` — Cauchy–Schwarz
  `L² ≤ (b−a)·2E` on a general `[a,b]` (the existing version is `[0,1]`-only).
* `distanceFunctionIntegralCurvesAreGeodesics` — the node: an integral curve of
  `∇r` has vanishing `curveAcceleration` at every interior time.
* `distanceFunctionIntegralCurvesAreGeodesicsOn` — the same, packaged as
  `Geodesic.IsGeodesicOn g c (Ioo a b)`.

## Route

The proof is **variational**, not connection-theoretic:

  unit speed + minimises length in `U`  --(Cauchy–Schwarz)-->  minimises energy
  in `U`  --(Theorem 5.4.3)-->  `c̈ = 0`.

The tube lemma is what makes "minimises only among curves in `U`" strong enough
to feed `stationary_curveAcceleration_eq_zero`: `IsLocalMin` only compares
against variations with parameter near `0`, and joint continuity of a
`CurveVariation` on `Ioo (-width) width ×ˢ Icc a b` plus compactness of
`Icc a b` confines all such competitors to `U`.

## What this file does NOT provide

It does **not** formalise the remark's first clause `∇_{∂_r}∂_r = 0`, and
nothing here implies it. `PetersenLib.IsGeodesic`/`curveAcceleration` are
defined off the metric's moving-foot **chart Christoffel symbols**
(`Ch05/Geodesics.lean`), whereas `hessianOperator`/`AffineConnection`
(`Ch03/DistanceFunctions.lean`) live in a formally unrelated world: there is no
bridge on disk from "acceleration of an integral curve of `V`" to `∇_V V`. So
the covariant-derivative identity of the remark remains unformalised; only the
asserted *consequence* (integral curves are geodesics) is proved here, and by a
route that never constructs a covariant derivative.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section
open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-- **Math.** Petersen Ch. 5, §5.3: for a distance function `r` on an open set
`U` and a curve `γ` that is `C^∞` **on `[a,b]`** and stays in `U`, the increment
of `r` is bounded by the length: `r (γ b) − r (γ a) ≤ L(γ|[a,b])`.  This is the
`ContMDiffOn` generalisation of `distanceFunction_curveLength_ge`: since
`(r ∘ γ)' = g(∇r, γ') ≤ |∇r||γ'| = |γ'|` by Cauchy–Schwarz, integrating the
fundamental theorem of calculus over `[a,b]` gives the claim.  Working with
`derivWithin` on `Icc a b` (rather than `deriv`) is what removes the global
smoothness assumption; at interior points `Icc a b ∈ 𝓝 s`, so the two agree. -/
theorem distanceFunction_curveLength_ge_on {g : RiemannianMetric I M}
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b))
    (hmem : ∀ t ∈ Icc a b, γ t ∈ U) :
    r (γ b) - r (γ a) ≤ curveLength (I := I) g γ a b := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp
  set f : ℝ → ℝ := fun s => r (γ s) with hf
  -- `f` is `C^∞` on `Icc a b`
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ f (Icc a b) := by
    refine ContMDiffOn.comp (t := U) ?_ hγ (fun s hs => hmem s hs)
    exact hr.1
  have hcd : ContDiffOn ℝ ∞ f (Icc a b) := hcomp.contDiffOn
  have huniq : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab'
  set f' : ℝ → ℝ := derivWithin f (Icc a b) with hf'
  have hf'cont : ContinuousOn f' (Icc a b) :=
    hcd.continuousOn_derivWithin huniq (by norm_num)
  have hf'int : IntervalIntegrable f' volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  -- at interior points `f'` is the genuine derivative
  have hderiv : ∀ s ∈ Ioo a b, HasDerivAt f (f' s) s := by
    intro s hs
    have hnhds : Icc a b ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s :=
      ((hγ s (Ioo_subset_Icc_self hs)).contMDiffAt hnhds).mdifferentiableAt (by norm_num)
    have hD := hasDerivAt_distanceFunction_comp hU hr (hmem s (Ioo_subset_Icc_self hs)) hγd
    have hdw : f' s = deriv f s := derivWithin_of_mem_nhds hnhds
    rw [hdw, hD.deriv]
    exact hD
  have hFTC : ∫ s in a..b, f' s = f b - f a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ hderiv hf'int
    exact hcd.continuousOn
  -- the pointwise Cauchy–Schwarz bound at interior points
  have hspeed_int : IntervalIntegrable
      (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s)) volume a b :=
    ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq g hab hγ
  have hpt : ∀ s ∈ Ioo a b, f' s ≤ Real.sqrt (curveSpeedSq (I := I) g γ s) := by
    intro s hs
    have hnhds : Icc a b ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ s :=
      ((hγ s (Ioo_subset_Icc_self hs)).contMDiffAt hnhds).mdifferentiableAt (by norm_num)
    have hD := hasDerivAt_distanceFunction_comp hU hr (hmem s (Ioo_subset_Icc_self hs)) hγd
    have hdw : f' s = deriv f s := derivWithin_of_mem_nhds hnhds
    have : f' s = g.metricInner (γ s) (gradient g r (γ s)) (velocity (I := I) γ s) := by
      rw [hdw, hD.deriv]
    rw [this]
    exact distanceFunction_deriv_le_speed hr (hmem s (Ioo_subset_Icc_self hs)) hγd
  have hmono : ∫ s in a..b, f' s
      ≤ ∫ s in a..b, Real.sqrt (curveSpeedSq (I := I) g γ s) := by
    refine intervalIntegral.integral_mono_ae_restrict hab hf'int hspeed_int ?_
    have hae : ∀ᵐ s ∂(volume.restrict (Icc a b)), s ∈ Ioo a b := by
      rw [← MeasureTheory.Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := a) (b := b))]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hae] with s hs
    exact hpt s hs
  rw [hFTC] at hmono
  rw [curveLength_def]
  exact hmono

/-- **Math.** Petersen Ch. 5, §5.3: the increment bound
`r (γ b) − r (γ a) ≤ L(γ|[a,b])` for a **piecewise**-`C^∞` curve staying in `U`.
Telescoping `distanceFunction_curveLength_ge_on` over the partition: the
increments of `r` add exactly, the lengths add by `curveLength_additive`, so the
per-piece bounds sum.  Unlike the `ENNReal`-valued
`riemannianEDist_le_ofReal_curveLength_of_isPiecewiseSmoothCurve`, the telescoping
here is over `ℝ`, so no nonnegativity side conditions are needed. -/
theorem distanceFunction_curveLength_ge_piecewise {g : RiemannianMetric I M}
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b)
    (hmem : ∀ t ∈ Icc a b, γ t ∈ U) :
    r (γ b) - r (γ a) ≤ curveLength (I := I) g γ a b := by
  have hγint := hγ.intervalIntegrable_sqrt_curveSpeedSq g
  obtain ⟨-, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  subst hu0; subst hun
  -- accumulate over the partition prefix `[u 0, u k]`
  have key : ∀ k : ℕ, ∀ hk : k < n + 1,
      r (γ (u ⟨k, hk⟩)) - r (γ (u 0)) ≤ curveLength (I := I) g γ (u 0) (u ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : (⟨0, hk⟩ : Fin (n + 1)) = 0 := rfl
      rw [h0, curveLength_self]
      simp
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hk1 : k < n + 1 := by omega
      have hcast : (⟨k, hk1⟩ : Fin (n + 1)) = (⟨k, hkn⟩ : Fin n).castSucc := rfl
      have hsucc : (⟨k + 1, hk⟩ : Fin (n + 1)) = (⟨k, hkn⟩ : Fin n).succ := rfl
      have hle_prefix : u 0 ≤ u ⟨k, hk1⟩ := hmono (Fin.zero_le _)
      have hle_piece : u ⟨k, hk1⟩ ≤ u ⟨k + 1, hk⟩ := by
        rw [hcast, hsucc]; exact hmono Fin.castSucc_lt_succ.le
      have hle_last : u ⟨k + 1, hk⟩ ≤ u (Fin.last n) := hmono (Fin.le_last _)
      -- the smooth piece `[u k, u (k+1)]`
      have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)) := by
        rw [hcast, hsucc]; exact hsmooth ⟨k, hkn⟩
      -- length additivity on the Petersen side
      have hsubL : Set.uIcc (u 0) (u ⟨k, hk1⟩) ⊆ Set.uIcc (u 0) (u (Fin.last n)) := by
        rw [Set.uIcc_of_le hle_prefix,
          Set.uIcc_of_le (hle_prefix.trans (hle_piece.trans hle_last))]
        exact Set.Icc_subset_Icc_right (hle_piece.trans hle_last)
      have hsubR : Set.uIcc (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩)
          ⊆ Set.uIcc (u 0) (u (Fin.last n)) := by
        rw [Set.uIcc_of_le hle_piece,
          Set.uIcc_of_le (hle_prefix.trans (hle_piece.trans hle_last))]
        exact Set.Icc_subset_Icc hle_prefix hle_last
      have hsplit : curveLength (I := I) g γ (u 0) (u ⟨k + 1, hk⟩)
          = curveLength (I := I) g γ (u 0) (u ⟨k, hk1⟩)
            + curveLength (I := I) g γ (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩) :=
        curveLength_additive (I := I) g γ (hγint.mono_set hsubL) (hγint.mono_set hsubR)
      -- the piece stays in `U`
      have hmemPiece : ∀ t ∈ Icc (u ⟨k, hk1⟩) (u ⟨k + 1, hk⟩), γ t ∈ U := fun t ht =>
        hmem t (Set.Icc_subset_Icc hle_prefix hle_last ht)
      have hpiece := distanceFunction_curveLength_ge_on hU hr hle_piece hsm hmemPiece
      have hih := ih hk1
      rw [hsplit]
      linarith
  have hfin := key n n.lt_succ_self
  have hlast : (⟨n, n.lt_succ_self⟩ : Fin (n + 1)) = Fin.last n := rfl
  rwa [hlast] at hfin

/-- **Math.** **Tube lemma for variations.**  If `γ([a,b]) ⊆ U` with `U` open,
then every curve `V.curve s` of a variation of `γ` stays in `U` for all `s` in
some `Ioo (-δ) δ`.  A `CurveVariation` is **jointly** continuous on
`Ioo (-width) width ×ˢ Icc a b`, so the preimage of `U` is relatively open and
contains the compact slice `{0} ×ˢ Icc a b`; mathlib's `generalized_tube_lemma`
thickens that slice to a uniform tube.  This is what makes a hypothesis of the
form "minimises only among competitors inside `U`" strong enough to produce an
`IsLocalMin`, whose comparison is itself only local in the parameter. -/
theorem CurveVariation.eventually_mem_of_isOpen {γ : ℝ → M} {a b : ℝ}
    (V : CurveVariation (I := I) γ a b) {U : Set M} (hU : IsOpen U)
    (hmem : ∀ t ∈ Icc a b, γ t ∈ U) :
    ∃ δ > 0, ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b, V.curve s t ∈ U := by
  classical
  set S : Set (ℝ × ℝ) := Ioo (-V.width) V.width ×ˢ Icc a b with hS
  have hcont : ContinuousOn (Function.uncurry V.toFun) S := V.continuousOn
  -- relative openness of the preimage
  obtain ⟨O, hO_open, hO_eq⟩ :=
    _root_.continuousOn_iff'.mp hcont U hU
  have hzero : ({0} : Set ℝ) ×ˢ Icc a b ⊆ O := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    simp only [Set.mem_singleton_iff] at hs
    subst hs
    have hmemS : ((0 : ℝ), t) ∈ S := ⟨⟨by linarith [V.width_pos], V.width_pos⟩, ht⟩
    have : Function.uncurry V.toFun ((0 : ℝ), t) ∈ U := by
      show V.toFun 0 t ∈ U
      rw [V.init t ht]; exact hmem t ht
    have : ((0 : ℝ), t) ∈ Function.uncurry V.toFun ⁻¹' U ∩ S := ⟨this, hmemS⟩
    rw [hO_eq] at this
    exact this.1
  obtain ⟨u, v, hu_open, hv_open, hu_sub, hv_sub, huv⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : ℝ))) isCompact_Icc hO_open hzero
  have h0u : (0 : ℝ) ∈ u := hu_sub rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu_open 0 h0u
  refine ⟨min ε V.width, lt_min hε V.width_pos, ?_⟩
  intro s hs t ht
  have hsu : s ∈ u := by
    apply hball
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    have h1 := min_le_left ε V.width
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsw : s ∈ Ioo (-V.width) V.width := by
    have h2 := min_le_right ε V.width
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmemS : (s, t) ∈ S := ⟨hsw, ht⟩
  have hmemO : (s, t) ∈ O := huv ⟨hsu, hv_sub ht⟩
  have : (s, t) ∈ Function.uncurry V.toFun ⁻¹' U ∩ S := by
    rw [hO_eq]; exact ⟨hmemO, hmemS⟩
  exact this.1

/-- **Math.** **Cauchy–Schwarz for length versus energy on `[a,b]`**:
`L(γ|[a,b])² ≤ (b − a) · 2E(γ|[a,b])`, with equality iff the speed is constant.
Expand `0 ≤ ∫ (|γ'| − k)²` with the constant `k := L / (b − a)`.  This
generalises `curveLength_sq_le_two_mul_energyFunctional`, which is hard-coded to
`[0,1]` (where `b − a = 1` and `k = L`). -/
theorem curveLength_sq_le_sub_mul_two_mul_energyFunctional (g : RiemannianMetric I M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : IsPiecewiseSmoothCurve (I := I) γ a b) :
    curveLength (I := I) g γ a b ^ 2
      ≤ (b - a) * (2 * energyFunctional (I := I) g γ a b) := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp [energyFunctional_def]
  set L : ℝ := curveLength (I := I) g γ a b with hL_def
  set k : ℝ := L / (b - a) with hk_def
  have hba : (0 : ℝ) < b - a := by linarith
  have hne : b - a ≠ 0 := ne_of_gt hba
  have hIf : IntervalIntegrable (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t))
      volume a b := hγ.intervalIntegrable_sqrt_curveSpeedSq (I := I) g
  have hIsp : IntervalIntegrable (curveSpeedSq (I := I) g γ) volume a b :=
    hγ.intervalIntegrable_curveSpeedSq (I := I) g
  have hIB : IntervalIntegrable (fun t => 2 * k * Real.sqrt (curveSpeedSq (I := I) g γ t))
      volume a b := hIf.const_mul _
  have hnonneg : (0 : ℝ) ≤ ∫ t in a..b,
      (Real.sqrt (curveSpeedSq (I := I) g γ t) - k) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
  have hptw : ∀ t : ℝ, (Real.sqrt (curveSpeedSq (I := I) g γ t) - k) ^ 2
      = curveSpeedSq (I := I) g γ t
        - 2 * k * Real.sqrt (curveSpeedSq (I := I) g γ t) + k ^ 2 := by
    intro t
    have hsq : Real.sqrt (curveSpeedSq (I := I) g γ t) ^ 2
        = curveSpeedSq (I := I) g γ t :=
      Real.sq_sqrt (curveSpeedSq_nonneg (I := I) g γ t)
    nlinarith [hsq]
  have hexpand : (∫ t in a..b, (Real.sqrt (curveSpeedSq (I := I) g γ t) - k) ^ 2)
      = (∫ t in a..b, curveSpeedSq (I := I) g γ t) - 2 * k * L + (b - a) * k ^ 2 := by
    rw [intervalIntegral.integral_congr (g := fun t => curveSpeedSq (I := I) g γ t
        - 2 * k * Real.sqrt (curveSpeedSq (I := I) g γ t) + k ^ 2)
        (fun t _ => hptw t),
      intervalIntegral.integral_add (hIsp.sub hIB) intervalIntegrable_const,
      intervalIntegral.integral_sub hIsp hIB,
      intervalIntegral.integral_const_mul]
    simp [hL_def, curveLength_def]
  rw [hexpand] at hnonneg
  have h2E : 2 * energyFunctional (I := I) g γ a b
      = ∫ t in a..b, curveSpeedSq (I := I) g γ t := by
    rw [energyFunctional_def]; ring
  rw [← h2E] at hnonneg
  -- `hnonneg : 0 ≤ 2E - 2kL + (b-a)k²`
  have hdiv : L ^ 2 / (b - a) ≤ 2 * energyFunctional (I := I) g γ a b := by
    have hk2 : (b - a) * k ^ 2 = L ^ 2 / (b - a) := by
      rw [hk_def]; field_simp
    have h2kL : 2 * k * L = 2 * L ^ 2 / (b - a) := by
      rw [hk_def]; field_simp
    rw [hk2, h2kL] at hnonneg
    have : L ^ 2 / (b - a) = 2 * L ^ 2 / (b - a) - L ^ 2 / (b - a) := by ring
    linarith
  rw [div_le_iff₀ hba] at hdiv
  nlinarith [hdiv]

/-- **Math.** Petersen Ch. 5, **Remark 5.2.1** (the asserted consequence): if
`r` is a distance function on the open set `U` (`|∇r| ≡ 1`) and `c` is an
integral curve of `∂_r = ∇r` staying in `U` on `[a,b]`, then `c` has vanishing
acceleration at every interior time `τ ∈ Ioo a b` — i.e. `c` is a geodesic.

The proof is variational rather than connection-theoretic.  Being an integral
curve of a unit gradient, `c` has unit speed, so `E(c) = (b−a)/2` and
`L(c) = b − a = r(c b) − r(c a)`.  Any competitor `γ` in `U` with the same
endpoints has `L(γ) ≥ r(γ b) − r(γ a) = b − a`
(`distanceFunction_curveLength_ge_piecewise`), hence
`2E(γ) ≥ L(γ)²/(b−a) ≥ b − a` by Cauchy–Schwarz: `c` minimises energy among
curves in `U`.  The tube lemma confines the competitors of a variation to `U`
for small parameters, which is all `IsLocalMin` requires, so Theorem 5.4.3
(`stationary_curveAcceleration_eq_zero`) applies with the trivial one-piece
partition and yields `c̈ = 0`.

Note this does **not** formalise the remark's other clause `∇_{∂_r}∂_r = 0`;
see the module docstring. -/
theorem distanceFunctionIntegralCurvesAreGeodesics {g : RiemannianMetric I M}
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {c : ℝ → M} {a b : ℝ} (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c)
    (hcU : ∀ t ∈ Icc a b, c t ∈ U)
    (hint : ∀ t ∈ Icc a b, velocity (I := I) c t = gradient g r (c t))
    {τ : ℝ} (hτ : τ ∈ Ioo a b) :
    curveAcceleration (I := I) g c τ = 0 := by
  classical
  have hab' : a ≤ b := hab.le
  have hcOn : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c (Icc a b) := hc.contMDiffOn
  have hpw : IsPiecewiseSmoothCurve (I := I) c a b :=
    ContMDiffOn.isPiecewiseSmoothCurve (I := I) hab' hcOn
  -- `c` has unit speed on `[a,b]`
  have hspeed : ∀ s ∈ Icc a b, curveSpeedSq (I := I) g c s = 1 := by
    intro s hs
    rw [curveSpeedSq_eq_metricInner_velocity g (hc.mdifferentiableAt (by norm_num)),
      hint s hs, hr.2 (c s) (hcU s hs)]
  -- `E(c) = (b-a)/2`
  have hEc : energyFunctional (I := I) g c a b = (b - a) / 2 := by
    rw [energyFunctional_def,
      intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))
        (fun s hs => hspeed s (by rwa [uIcc_of_le hab'] at hs))]
    simp; ring
  -- length identity: `r (c b) - r (c a) = b - a`
  have hrdiff : r (c b) - r (c a) = b - a := by
    have h := distanceFunction_integralCurve_curveLength hU hr hab' hc hcU hint
    have hlen : curveLength (I := I) g c a b = b - a := by
      rw [curveLength_def,
        intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))
          (fun s hs => by
            rw [hspeed s (by rwa [uIcc_of_le hab'] at hs), Real.sqrt_one])]
      simp
    rw [← h, hlen]
  -- the minimality hypothesis
  have hmin : ∀ V : CurveVariation (I := I) c a b, IsProperVariation V →
      IsLocalMin (fun s => energyFunctional (I := I) g (V.curve s) a b) 0 := by
    intro V hV
    obtain ⟨δ, hδ, hδU⟩ := V.eventually_mem_of_isOpen hU hcU
    have hsub : Ioo (-(min δ V.width)) (min δ V.width) ∈ 𝓝 (0 : ℝ) := by
      apply Ioo_mem_nhds
      · have := lt_min hδ V.width_pos; linarith
      · exact lt_min hδ V.width_pos
    filter_upwards [hsub] with s hs
    have hsδ : s ∈ Ioo (-δ) δ := by
      have := min_le_left δ V.width
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hsw : s ∈ Ioo (-V.width) V.width := by
      have := min_le_right δ V.width
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hVU : ∀ t ∈ Icc a b, V.curve s t ∈ U := hδU s hsδ
    have hVpw : IsPiecewiseSmoothCurve (I := I) (V.curve s) a b :=
      V.isPiecewiseSmoothCurve hsw
    -- endpoints match
    have hea : V.curve s a = c a := (hV s hsw).1
    have heb : V.curve s b = c b := (hV s hsw).2
    -- length bound
    have hL : b - a ≤ curveLength (I := I) g (V.curve s) a b := by
      have := distanceFunction_curveLength_ge_piecewise hU hr hab' hVpw hVU
      rw [hea, heb] at this
      linarith [hrdiff]
    have hCS := curveLength_sq_le_sub_mul_two_mul_energyFunctional g hab' hVpw
    have hLnn : (0 : ℝ) ≤ curveLength (I := I) g (V.curve s) a b := by linarith
    have hsq : (b - a) ^ 2 ≤ (b - a) * (2 * energyFunctional (I := I) g (V.curve s) a b) := by
      nlinarith [hCS, hL, hLnn]
    have hba : (0 : ℝ) < b - a := by linarith
    have hEge : (b - a) / 2 ≤ energyFunctional (I := I) g (V.curve s) a b := by
      nlinarith [hsq, hba]
    have hE0 : energyFunctional (I := I) g (V.curve 0) a b
        = energyFunctional (I := I) g c a b := by
      rw [energyFunctional_def, energyFunctional_def]
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      have hb : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({b} : Set ℝ) :=
        MeasureTheory.Measure.ae_ne volume b
      filter_upwards [hb] with t ht htI
      rw [Set.uIoc_of_le hab'] at htI
      have htoo : t ∈ Ioo a b :=
        ⟨htI.1, lt_of_le_of_ne htI.2 (by simpa using ht)⟩
      refine curveSpeedSq_congr_nhds (I := I) g ?_
      filter_upwards [Icc_mem_nhds htoo.1 htoo.2] with t' ht'
      exact V.init t' ht'
    show (fun s => energyFunctional (I := I) g (V.curve s) a b) 0 ≤ _
    simp only
    rw [hE0, hEc]
    exact hEge
  -- apply the first-variation converse with the trivial 1-piece partition
  refine stationary_curveAcceleration_eq_zero g hpw
    (n := 1) (u := fun i => if i = 0 then a else b) ?_ ?_ ?_ ?_ hmin (i := 0) one_pos ?_
  · intro i hi; interval_cases i; simpa using hab
  · simp
  · simp
  · intro i hi; interval_cases i; simpa using hcOn
  · simpa using hτ

/-- **Math.** Petersen Ch. 5, **Remark 5.2.1**, packaged as a geodesic
statement: an integral curve of `∂_r = ∇r` for a distance function `r` on an
open set `U` is a geodesic on `Ioo a b` in the sense of
`def:pet-ch5-geodesic`.  The `C²`-regularity conjunct hidden in
`Geodesic.HasGeodesicEquationAt` is free here because `c` is `C^∞`. -/
theorem distanceFunctionIntegralCurvesAreGeodesicsOn {g : RiemannianMetric I M}
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {c : ℝ → M} {a b : ℝ} (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c)
    (hcU : ∀ t ∈ Icc a b, c t ∈ U)
    (hint : ∀ t ∈ Icc a b, velocity (I := I) c t = gradient g r (c t)) :
    Geodesic.IsGeodesicOn (I := I) g c (Ioo a b) := by
  intro τ hτ
  exact hasGeodesicEquationAt_of_isOpen_contMDiffOn g isOpen_Ioo hτ hc.contMDiffOn
    (distanceFunctionIntegralCurvesAreGeodesics hU hr hab hc hcU hint hτ)

end PetersenLib
