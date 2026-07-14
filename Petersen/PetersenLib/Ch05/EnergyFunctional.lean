import PetersenLib.Ch05.ConstantSpeedApproximation

/-!
# Petersen Ch. 5, §5.4 — the energy functional and Prop. 5.4.1

Petersen's energy functional (`def:pet-ch5-energy-functional`)

  `E(c) = ½ ∫₀¹ |ċ|² dt`,   `c ∈ Ω_{p,q}`,

the Cauchy–Schwarz comparison `L(c)² ≤ 2 E(c)` with equality for
constant-speed curves, and Proposition 5.4.1
(`prop:pet-ch5-energy-length-minimizers`): a constant-speed length minimizer
minimizes energy, and an energy minimizer minimizes length.  Also the
variation of a curve (`def:pet-ch5-variation`): `CurveVariation`,
`IsProperVariation`, and the slices `c_s = c̄(s, ·)`.

* `energyFunctional` — the energy `E(γ)|_a^b = ½ ∫_a^b |γ̇|² dt`.
* `ContMDiffOn.intervalIntegrable_curveSpeedSq` /
  `IsPiecewiseSmoothCurve.intervalIntegrable_curveSpeedSq` — the squared
  speed of a (piecewise) smooth curve is interval-integrable, by the same
  windowed continuous-representative argument as for the speed itself.
* `curveLength_sq_le_two_mul_energyFunctional` — **Cauchy–Schwarz**:
  `L(c)² ≤ 2E(c)` on `[0,1]`, via `0 ≤ ∫ (|ċ| − L)²`.
* `IsConstantSpeedCurve.two_mul_energyFunctional` — for constant-speed
  curves `2E = L²`.
* `energyMinimizer_of_constantSpeed_lengthMinimizer`,
  `lengthMinimizer_of_energyMinimizer` — the two directions of
  Prop. 5.4.1; the second uses the constant-speed approximation
  `approximateByConstantSpeedCurve` (Cor. 5.3.10) and `ε → 0`.
* `CurveVariation`, `IsProperVariation`, `CurveVariation.curve` — the
  variation of a curve (`def:pet-ch5-variation`) with its piecewise-smooth
  partition datum, and the slice curves `c_s`, each piecewise smooth.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open scoped Manifold Topology ContDiff Interval

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The energy functional -/

/-- **Math.** Petersen Ch. 5, §5.4 (`def:pet-ch5-energy-functional`): the
**energy functional** `E(γ)|_a^b = ½ ∫_a^b |γ̇(t)|² dt` of a curve
`γ : ℝ → M`.  Unlike the length it is not invariant under reparametrization:
it measures the total kinetic energy of the parametrized motion. -/
def energyFunctional (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  (1 / 2) * ∫ t in a..b, curveSpeedSq (I := I) g γ t

@[simp] lemma energyFunctional_def (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    energyFunctional (I := I) g γ a b =
      (1 / 2) * ∫ t in a..b, curveSpeedSq (I := I) g γ t := rfl

/-- **Math.** The energy of `γ|_{[a,b]}` is nonnegative for `a ≤ b`: the
integrand `|γ̇|²` is nonnegative. -/
theorem energyFunctional_nonneg (g : RiemannianMetric I M) (γ : ℝ → M) {a b : ℝ}
    (hab : a ≤ b) :
    0 ≤ energyFunctional (I := I) g γ a b :=
  mul_nonneg (by norm_num)
    (intervalIntegral.integral_nonneg hab fun t _ => curveSpeedSq_nonneg (I := I) g γ t)

section Boundaryless

variable [I.Boundaryless]

/-! ## Integrability of the squared speed -/

/-- **Math.** The squared speed `t ↦ g(γ̇, γ̇)` of a curve `γ` that is `C^∞`
on `[c, d]` is interval-integrable on `[c, d]`: near each base time it
agrees a.e. with a continuous fixed-chart Gram pairing
(`exists_continuousOn_eqOn_curveSpeedSq`), and compactness glues the
windows.  In particular the energy of a (piecewise) smooth curve is a
well-defined finite number. -/
theorem ContMDiffOn.intervalIntegrable_curveSpeedSq (g : RiemannianMetric I M)
    {γ : ℝ → M} {c d : ℝ} (hcd : c ≤ d)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc c d)) :
    IntervalIntegrable (curveSpeedSq (I := I) g γ) MeasureTheory.volume c d := by
  rcases hcd.eq_or_lt with rfl | hlt
  · exact IntervalIntegrable.refl
  -- local windows with continuous representatives
  have hloc : ∀ t₀ ∈ Icc c d, ∃ δ > (0 : ℝ), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc c d ∩ closedBall t₀ δ) ∧
      ∀ s ∈ Ioo c d ∩ ball t₀ δ, curveSpeedSq (I := I) g γ s = F s :=
    fun t₀ ht₀ => exists_continuousOn_eqOn_curveSpeedSq (I := I) g hlt hγ ht₀
  choose! δ hδpos F hFcont hFeq using hloc
  -- finite subcover of the compact interval by the open windows
  obtain ⟨τ, hτcover⟩ := isCompact_Icc.elim_nhds_subcover'
    (fun t₀ (_ : t₀ ∈ Icc c d) => ball t₀ (δ t₀))
    (fun t₀ ht₀ => ball_mem_nhds t₀ (hδpos t₀ ht₀))
  -- integrability on each closed window
  have hpiece : ∀ t₀ : ↥(Icc c d), IntegrableOn (curveSpeedSq (I := I) g γ)
      (Icc c d ∩ closedBall (t₀ : ℝ) (δ (t₀ : ℝ))) volume := by
    rintro ⟨t₀, ht₀⟩
    set S : Set ℝ := Icc c d ∩ closedBall t₀ (δ t₀) with hSdef
    have hK : IsCompact S := isCompact_Icc.inter_right isClosed_closedBall
    have hSmeas : MeasurableSet S :=
      (isClosed_Icc.inter isClosed_closedBall).measurableSet
    have hFI : IntegrableOn (F t₀) S volume :=
      (hFcont t₀ ht₀).integrableOn_compact hK
    refine hFI.congr ?_
    -- a.e. agreement on the window: the exceptional set is four points
    have hbadnull : volume ({c, d, t₀ - δ t₀, t₀ + δ t₀} : Set ℝ) = 0 :=
      (Set.toFinite _).measure_zero volume
    rw [Filter.EventuallyEq, ae_restrict_iff' hSmeas]
    filter_upwards [compl_mem_ae_iff.mpr hbadnull] with s hsbad hsS
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at hsbad
    obtain ⟨hsc, hsd, hsl, hsr⟩ := hsbad
    have hIoo : s ∈ Ioo c d :=
      ⟨lt_of_le_of_ne hsS.1.1 (Ne.symm hsc), lt_of_le_of_ne hsS.1.2 hsd⟩
    have hIcc' : s ∈ Icc (t₀ - δ t₀) (t₀ + δ t₀) := by
      rw [← Real.closedBall_eq_Icc]; exact hsS.2
    have hball : s ∈ ball t₀ (δ t₀) := by
      rw [Real.ball_eq_Ioo]
      exact ⟨lt_of_le_of_ne hIcc'.1 (Ne.symm hsl), lt_of_le_of_ne hIcc'.2 hsr⟩
    exact (hFeq t₀ ht₀ s ⟨hIoo, hball⟩).symm
  -- glue the finitely many windows
  have hunion : IntegrableOn (curveSpeedSq (I := I) g γ)
      (⋃ t₀ ∈ τ, Icc c d ∩ closedBall (t₀ : ℝ) (δ (t₀ : ℝ))) volume :=
    integrableOn_finset_iUnion.mpr fun t₀ _ => hpiece t₀
  have hcover' : Icc c d ⊆ ⋃ t₀ ∈ τ, Icc c d ∩ closedBall (t₀ : ℝ) (δ (t₀ : ℝ)) := by
    intro s hs
    obtain ⟨t₀, ht₀τ, hst₀⟩ := mem_iUnion₂.mp (hτcover hs)
    exact mem_iUnion₂.mpr ⟨t₀, ht₀τ, hs, ball_subset_closedBall hst₀⟩
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlt.le]
  exact hunion.mono_set hcover'

/-- **Math.** The squared speed of a piecewise `C^∞` curve on `[a, b]` is
interval-integrable on `[a, b]`: it is integrable on each smooth piece, and
adjacent pieces chain. -/
theorem IsPiecewiseSmoothCurve.intervalIntegrable_curveSpeedSq
    {γ : ℝ → M} {a b : ℝ} (hγ : IsPiecewiseSmoothCurve (I := I) γ a b)
    (g : RiemannianMetric I M) :
    IntervalIntegrable (curveSpeedSq (I := I) g γ) MeasureTheory.volume a b := by
  obtain ⟨-, n, u, hmono, hu0, hun, hsmooth⟩ := hγ
  have key : ∀ k : ℕ, ∀ hk : k < n + 1,
      IntervalIntegrable (curveSpeedSq (I := I) g γ)
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
      exact ContMDiffOn.intervalIntegrable_curveSpeedSq (I := I) g hle
        (hsmooth ⟨k, hkn⟩)
  rw [← hu0, ← hun]
  exact key n n.lt_succ_self

/-! ## Cauchy–Schwarz: `L² ≤ 2E` -/

/-- **Math.** Petersen Ch. 5, §5.4 (p. 199), the **Cauchy–Schwarz
comparison** of length and energy on `[0, 1]`:
`L(γ)² = (∫₀¹ |γ̇| ⋅ 1)² ≤ ∫₀¹ |γ̇|² ⋅ ∫₀¹ 1² = 2 E(γ)`.

Proven by expanding `0 ≤ ∫₀¹ (|γ̇(t)| − L)² dt` with `L = L(γ)`. -/
theorem curveLength_sq_le_two_mul_energyFunctional (g : RiemannianMetric I M)
    {γ : ℝ → M} (hγ : IsPiecewiseSmoothCurve (I := I) γ 0 1) :
    curveLength (I := I) g γ 0 1 ^ 2 ≤ 2 * energyFunctional (I := I) g γ 0 1 := by
  set L : ℝ := curveLength (I := I) g γ 0 1 with hL_def
  have hIf : IntervalIntegrable (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t))
      MeasureTheory.volume 0 1 := hγ.intervalIntegrable_sqrt_curveSpeedSq (I := I) g
  have hIsp : IntervalIntegrable (curveSpeedSq (I := I) g γ) MeasureTheory.volume 0 1 :=
    hγ.intervalIntegrable_curveSpeedSq (I := I) g
  have hIB : IntervalIntegrable (fun t => 2 * L * Real.sqrt (curveSpeedSq (I := I) g γ t))
      MeasureTheory.volume 0 1 := hIf.const_mul _
  have hnonneg : (0:ℝ) ≤ ∫ t in (0:ℝ)..1,
      (Real.sqrt (curveSpeedSq (I := I) g γ t) - L) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
  have hptw : ∀ t : ℝ, (Real.sqrt (curveSpeedSq (I := I) g γ t) - L) ^ 2
      = curveSpeedSq (I := I) g γ t
        - 2 * L * Real.sqrt (curveSpeedSq (I := I) g γ t) + L ^ 2 := by
    intro t
    have hsq : Real.sqrt (curveSpeedSq (I := I) g γ t) ^ 2
        = curveSpeedSq (I := I) g γ t :=
      Real.sq_sqrt (curveSpeedSq_nonneg (I := I) g γ t)
    nlinarith [hsq]
  have hexpand : (∫ t in (0:ℝ)..1,
        (Real.sqrt (curveSpeedSq (I := I) g γ t) - L) ^ 2)
      = (∫ t in (0:ℝ)..1, curveSpeedSq (I := I) g γ t) - 2 * L * L + L ^ 2 := by
    rw [intervalIntegral.integral_congr (g := fun t => curveSpeedSq (I := I) g γ t
        - 2 * L * Real.sqrt (curveSpeedSq (I := I) g γ t) + L ^ 2)
        (fun t _ => hptw t),
      intervalIntegral.integral_add (hIsp.sub hIB) intervalIntegrable_const,
      intervalIntegral.integral_sub hIsp hIB,
      intervalIntegral.integral_const_mul]
    simp [hL_def]
  rw [hexpand] at hnonneg
  have h2E : 2 * energyFunctional (I := I) g γ 0 1
      = ∫ t in (0:ℝ)..1, curveSpeedSq (I := I) g γ t := by
    rw [energyFunctional_def]; ring
  rw [h2E]
  nlinarith [hnonneg]

/-- **Math.** For a constant-speed curve on `[0, 1]` the Cauchy–Schwarz
comparison is an equality: `2 E(σ) = L(σ)²` — the speed is a.e. a constant
`k ≥ 0`, so `E = k²/2` and `L = k`. -/
theorem IsConstantSpeedCurve.two_mul_energyFunctional (g : RiemannianMetric I M)
    {σ : ℝ → M} (h : IsConstantSpeedCurve (I := I) g σ 0 1) :
    2 * energyFunctional (I := I) g σ 0 1 = curveLength (I := I) g σ 0 1 ^ 2 := by
  obtain ⟨k, hk, T, hT⟩ := h
  have hae : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Ι (0:ℝ) 1 →
      curveSpeedSq (I := I) g σ x = k ^ 2 := by
    have hnull : MeasureTheory.volume (T : Set ℝ) = 0 :=
      (T.finite_toSet).measure_zero MeasureTheory.volume
    filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx hxI
    rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hxI
    exact hT x ⟨⟨hxI.1.le, hxI.2⟩, hx⟩
  have hsp : (∫ t in (0:ℝ)..1, curveSpeedSq (I := I) g σ t) = k ^ 2 := by
    rw [intervalIntegral.integral_congr_ae
      (g := fun _ => k ^ 2) (by filter_upwards [hae] with x hx hxI; exact hx hxI)]
    simp
  have hL : curveLength (I := I) g σ 0 1 = k := by
    have hae' : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Ι (0:ℝ) 1 →
        Real.sqrt (curveSpeedSq (I := I) g σ x) = k := by
      filter_upwards [hae] with x hx hxI
      rw [hx hxI, Real.sqrt_sq hk]
    calc curveLength (I := I) g σ 0 1
        = ∫ _ in (0:ℝ)..1, k := intervalIntegral.integral_congr_ae hae'
      _ = k := by simp
  calc 2 * energyFunctional (I := I) g σ 0 1
      = ∫ t in (0:ℝ)..1, curveSpeedSq (I := I) g σ t := by
        rw [energyFunctional_def]; ring
    _ = k ^ 2 := hsp
    _ = curveLength (I := I) g σ 0 1 ^ 2 := by rw [hL]

/-! ## Proposition 5.4.1 -/

/-- **Math.** Petersen Ch. 5, §5.4, **Proposition 5.4.1, first direction**
(`prop:pet-ch5-energy-length-minimizers`): a **constant-speed length
minimizer minimizes the energy**.  For any competitor `c ∈ Ω_{p,q}`,
`2E(σ) = L(σ)² ≤ L(c)² ≤ 2E(c)` by the constant-speed equality and
Cauchy–Schwarz. -/
theorem energyMinimizer_of_constantSpeed_lengthMinimizer (g : RiemannianMetric I M)
    {p q : M} {σ : ℝ → M}
    (hconst : IsConstantSpeedCurve (I := I) g σ 0 1)
    (hmin : ∀ c : ℝ → M, IsPiecewiseSmoothCurve (I := I) c 0 1 → c 0 = p → c 1 = q →
      curveLength (I := I) g σ 0 1 ≤ curveLength (I := I) g c 0 1) :
    ∀ c : ℝ → M, IsPiecewiseSmoothCurve (I := I) c 0 1 → c 0 = p → c 1 = q →
      energyFunctional (I := I) g σ 0 1 ≤ energyFunctional (I := I) g c 0 1 := by
  intro c hc hc0 hc1
  have h1 := hconst.two_mul_energyFunctional (I := I) g
  have h2 := curveLength_sq_le_two_mul_energyFunctional (I := I) g hc
  have h3 := hmin c hc hc0 hc1
  have hσL : 0 ≤ curveLength (I := I) g σ 0 1 :=
    curveLength_nonneg (I := I) g σ zero_le_one
  have h4 : curveLength (I := I) g σ 0 1 ^ 2 ≤ curveLength (I := I) g c 0 1 ^ 2 := by
    nlinarith [h3, hσL]
  linarith

/-- **Math.** Petersen Ch. 5, §5.4, **Proposition 5.4.1, second direction**
(`prop:pet-ch5-energy-length-minimizers`): an **energy minimizer minimizes
the length**.  For a competitor `c ∈ Ω_{p,q}` and `ε > 0`, the constant-speed
approximation `c_ε` of Cor. 5.3.10 gives
`L(σ)² ≤ 2E(σ) ≤ 2E(c_ε) = L(c_ε)² ≤ ((1+ε) L(c))²`, and `ε → 0`. -/
theorem lengthMinimizer_of_energyMinimizer (g : RiemannianMetric I M)
    {p q : M} {σ : ℝ → M} (hσ : IsPiecewiseSmoothCurve (I := I) σ 0 1)
    (hmin : ∀ c : ℝ → M, IsPiecewiseSmoothCurve (I := I) c 0 1 → c 0 = p → c 1 = q →
      energyFunctional (I := I) g σ 0 1 ≤ energyFunctional (I := I) g c 0 1) :
    ∀ c : ℝ → M, IsPiecewiseSmoothCurve (I := I) c 0 1 → c 0 = p → c 1 = q →
      curveLength (I := I) g σ 0 1 ≤ curveLength (I := I) g c 0 1 := by
  intro c hc hc0 hc1
  have hσL : 0 ≤ curveLength (I := I) g σ 0 1 :=
    curveLength_nonneg (I := I) g σ zero_le_one
  have hcL : 0 ≤ curveLength (I := I) g c 0 1 :=
    curveLength_nonneg (I := I) g c zero_le_one
  have hkey : ∀ ε : ℝ, 0 < ε →
      curveLength (I := I) g σ 0 1 ≤ (1 + ε) * curveLength (I := I) g c 0 1 := by
    intro ε hε
    obtain ⟨c', hc', hc'0, hc'1, hc'const, hc'len⟩ :=
      approximateByConstantSpeedCurve (I := I) g hc hε
    have h1 := curveLength_sq_le_two_mul_energyFunctional (I := I) g hσ
    have h2 := hmin c' hc' (by rw [hc'0, hc0]) (by rw [hc'1, hc1])
    have h3 := hc'const.two_mul_energyFunctional (I := I) g
    have hc'L : 0 ≤ curveLength (I := I) g c' 0 1 :=
      curveLength_nonneg (I := I) g c' zero_le_one
    have hsq : curveLength (I := I) g σ 0 1 ^ 2 ≤ curveLength (I := I) g c' 0 1 ^ 2 := by
      linarith
    have h4 : curveLength (I := I) g σ 0 1 ≤ curveLength (I := I) g c' 0 1 := by
      have h5 := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq hσL, Real.sqrt_sq hc'L] at h5
    exact h4.trans hc'len
  by_contra hcon
  push Not at hcon
  set Lσ : ℝ := curveLength (I := I) g σ 0 1 with hLσ_def
  set Lc : ℝ := curveLength (I := I) g c 0 1 with hLc_def
  rcases hcL.eq_or_lt with h0 | hLcpos
  · have h1 := hkey 1 one_pos
    rw [← h0] at h1
    simp only [mul_zero] at h1
    linarith
  · have hε : 0 < (Lσ - Lc) / (2 * Lc) := div_pos (by linarith) (by linarith)
    have h1 := hkey _ hε
    have hcomp : (1 + (Lσ - Lc) / (2 * Lc)) * Lc = Lc + (Lσ - Lc) / 2 := by
      field_simp
    rw [hcomp] at h1
    linarith

end Boundaryless

/-! ## Variations of a curve -/

/-- **Math.** Petersen Ch. 5, §5.4 (`def:pet-ch5-variation`): a **piecewise
smooth variation** of a curve `γ : [a, b] → M`: a map
`c̄ : (-ε, ε) × [a, b] → M` with `c̄(0, t) = γ t`, continuous on
`(-ε, ε) × [a, b]` and smooth on each slab `(-ε, ε) × [aᵢ, aᵢ₊₁]` of a
partition `a = a₀ ≤ ⋯ ≤ aₘ = b`.  The slices `c_s = c̄(s, ·)` are the
curves of the variation (`CurveVariation.curve`), each piecewise smooth
(`CurveVariation.isPiecewiseSmoothCurve`). -/
structure CurveVariation (γ : ℝ → M) (a b : ℝ) where
  /-- The two-parameter map `(s, t) ↦ c̄(s, t)`. -/
  toFun : ℝ → ℝ → M
  /-- The half-width `ε` of the variation parameter interval `(-ε, ε)`. -/
  width : ℝ
  width_pos : 0 < width
  /-- The variation deforms `γ`: `c̄(0, t) = γ t` on `[a, b]`. -/
  init : ∀ t ∈ Icc a b, toFun 0 t = γ t
  /-- The variation is continuous on `(-ε, ε) × [a, b]`. -/
  continuousOn : ContinuousOn (Function.uncurry toFun) (Ioo (-width) width ×ˢ Icc a b)
  /-- The variation is smooth on the slabs of a partition of `[a, b]`. -/
  exists_partition : ∃ (n : ℕ) (u : Fin (n + 1) → ℝ), Monotone u ∧ u 0 = a ∧
    u (Fin.last n) = b ∧ ∀ i : Fin n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (Function.uncurry toFun) (Ioo (-width) width ×ˢ Icc (u i.castSucc) (u i.succ))

/-- **Math.** The curve `c_s = c̄(s, ·)` of a variation at parameter `s`. -/
def CurveVariation.curve {γ : ℝ → M} {a b : ℝ}
    (V : CurveVariation (I := I) γ a b) (s : ℝ) : ℝ → M :=
  fun t => V.toFun s t

@[simp] lemma CurveVariation.curve_apply {γ : ℝ → M} {a b : ℝ}
    (V : CurveVariation (I := I) γ a b) (s t : ℝ) :
    V.curve s t = V.toFun s t := rfl

/-- **Math.** The curve at parameter `0` is the deformed curve `γ` itself,
on `[a, b]`. -/
theorem CurveVariation.curve_zero {γ : ℝ → M} {a b : ℝ}
    (V : CurveVariation (I := I) γ a b) {t : ℝ} (ht : t ∈ Icc a b) :
    V.curve 0 t = γ t :=
  V.init t ht

/-- **Math.** Petersen Ch. 5, §5.4 (`def:pet-ch5-variation`): a variation is
**proper** if every curve of the variation has the same endpoints as `γ` —
so all `c_s` belong to `Ω_{p,q}` when `γ` does. -/
def IsProperVariation {γ : ℝ → M} {a b : ℝ}
    (V : CurveVariation (I := I) γ a b) : Prop :=
  ∀ s ∈ Ioo (-V.width) V.width, V.toFun s a = γ a ∧ V.toFun s b = γ b

/-- **Math.** Each curve `c_s` of a piecewise smooth variation is a piecewise
smooth curve on `[a, b]`: slice the slab continuity and smoothness along
`t ↦ (s, t)`. -/
theorem CurveVariation.isPiecewiseSmoothCurve {γ : ℝ → M} {a b : ℝ}
    (V : CurveVariation (I := I) γ a b) {s : ℝ}
    (hs : s ∈ Ioo (-V.width) V.width) :
    IsPiecewiseSmoothCurve (I := I) (V.curve s) a b := by
  obtain ⟨n, u, hmono, hu0, hun, hsm⟩ := V.exists_partition
  refine ⟨?_, n, u, hmono, hu0, hun, ?_⟩
  · have hc : ContinuousOn (fun t : ℝ => Function.uncurry V.toFun (s, t)) (Icc a b) :=
      V.continuousOn.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun t ht => ⟨hs, ht⟩)
    exact hc
  · intro i
    have hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => Function.uncurry V.toFun (s, t))
        (Icc (u i.castSucc) (u i.succ)) :=
      (hsm i).comp ((contDiff_prodMk_right s).contMDiff.contMDiffOn)
        (fun t ht => ⟨hs, ht⟩)
    exact hc

end PetersenLib
