/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Exponential/MinimizingPathPiecewise.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Exponential.MinimizingPiecewise
import PetersenLib.Riemannian.Exponential.NormalBallEDist

/-!
# Radial geodesics minimize among piecewise differentiable curves, path-length
form (do Carmo Ch. 3, Prop. 3.6, inequality clause, both cases)

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 3.6: on a normal ball the
radial geodesic from `p` to `exp_p v` is at least as short as **every**
piecewise differentiable curve joining the same endpoints — including
competitors that leave the ball. This file assembles that statement at the
honest manifold level, with lengths measured by mathlib's
`Manifold.pathELength` (competitors are continuous curves `σ : [0,1] → M`,
`C¹` on each piece of a partition; by `pathELength_sum_partition` their total
`pathELength` is the sum of the piece lengths, so `pathELength I σ 0 1` is the
classical piecewise arc length):

* `pathELength_sum_partition` — additivity of `pathELength` over a monotone
  partition `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ n`.
* `exists_le_pathELength_piecewise` — **the piecewise competitor bound**:
  there are `ε > 0` and a Gram comparison constant `c > 0` at `p` such that,
  with `exp_p` injective on `B_ε(0) ⊂ T_pM` and open on sub-balls,

  - every piecewise-`C¹` curve `σ : [0,1] → M` from `p` to `exp_p v`
    (`‖v‖ < ε`) has `pathELength` at least the `g_p`-length `√⟨v, v⟩_p` of the
    radial geodesic — do Carmo's inequality `ℓ(γ) ≤ ℓ(c)`, with the escape
    case (a competitor leaving the normal ball) absorbed;
  - every piecewise-`C¹` curve from `p` ending outside `exp_p(B_r(0))`
    (`0 < r ≤ ε`) has `pathELength` at least `r/√c` (the escape estimate).

The single-`C¹`-piece case is `exists_le_pathELength`
(`NormalBallEDist.lean`); the chart-polar piecewise comparison it rests on is
`gauss_radius_reach_piecewise` (`MinimizingPiecewise.lean`). The proof mirrors
`exists_le_pathELength`: chart-read the competitor, polar-lift it through the
local `C¹` inverse of `exp_p`, and control the `g_p`-radius of the lift by the
telescoped Gauss comparison; a competitor that leaves the polar region is cut
at its first exit time (a compactness argument needing only continuity), and
the partition is truncated at that time.

The remaining gap to do Carmo's full Proposition 3.6 is the equality clause
(`ℓ(c) = ℓ(γ)` forces `c([0,1]) = γ([0,1])`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal ENNReal

set_option linter.unusedSectionVars false

namespace PetersenLib

namespace Exponential

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **Additivity of the path length over a partition**: for a
monotone partition `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ n`, the total `pathELength` of a curve
over `[τ 0, τ n]` is the sum of the piece lengths. This identifies
`pathELength I σ (τ 0) (τ n)` with the classical length of a piecewise
differentiable curve (do Carmo Ch. 3, Definition 3.1: the length of `c` is the
sum of the lengths of its differentiable pieces). -/
theorem pathELength_sum_partition (g : RiemannianMetric I M) {σ : ℝ → M}
    {n : ℕ} {τ : ℕ → ℝ} (hτ : ∀ i < n, τ i ≤ τ (i + 1)) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i ∈ Finset.range n, Manifold.pathELength I σ (τ i) (τ (i + 1))
      = Manifold.pathELength I σ (τ 0) (τ n) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  revert hτ
  induction n with
  | zero => intro _; simp
  | succ k ih =>
    intro hτ
    have hτk : ∀ i < k, τ i ≤ τ (i + 1) :=
      fun i hi => hτ i (hi.trans k.lt_succ_self)
    rw [Finset.sum_range_succ, ih hτk,
      Manifold.pathELength_add (partition_le hτk (Nat.zero_le k) le_rfl)
        (hτ k k.lt_succ_self)]

/-- **Math.** **The piecewise competitor bound** (do Carmo Ch. 3,
Proposition 3.6, inequality clause, both cases, for piecewise differentiable
competitors). There are `ε > 0` and a Gram comparison constant `c > 0` at `p`
such that, with `exp_p` injective on `B_ε(0) ⊂ T_pM` and open on sub-balls:

* every continuous curve `σ : [0,1] → M` from `p` to `exp_p v` (`‖v‖ < ε`)
  that is `C¹` on each piece of a partition `0 = τ 0 ≤ ⋯ ≤ τ n = 1` has
  `pathELength` at least the `g_p`-length `√⟨v, v⟩_p` of the radial geodesic —
  the competitor either stays in the normal ball, where the telescoped Gauss
  radius comparison applies to its polar lift, or leaves it, which already
  costs more than `√⟨v, v⟩_p`;
* every such curve from `p` ending outside `exp_p(B_r(0))` (`0 < r ≤ ε`) has
  `pathELength` at least `r/√c` (the escape estimate).

By `pathELength_sum_partition`, `pathELength I σ 0 1` is the sum of the piece
lengths, i.e. the classical length of the piecewise differentiable curve. The
single-`C¹`-piece form is `exists_le_pathELength`; the equality analysis of
do Carmo's Proposition 3.6 is not part of this statement. -/
theorem exists_le_pathELength_piecewise [T2Space M] (g : RiemannianMetric I M) (p : M) :
    ∃ (ε c : ℝ), 0 < ε ∧ 0 < c ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ε →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ε) ∧
      (∀ r : ℝ, r ≤ ε →
        IsOpen ((fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
          ball (0 : E) r)) ∧
      (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
       (∀ v : E, ‖v‖ < ε →
          ∀ (σ : ℝ → M) (n : ℕ) (τ : ℕ → ℝ),
          τ 0 = 0 → τ n = 1 → (∀ i < n, τ i ≤ τ (i + 1)) →
          ContinuousOn σ (Icc (0 : ℝ) 1) →
          (∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (τ i) (τ (i + 1)))) →
          σ 0 = p → σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
          ENNReal.ofReal (Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v))
            ≤ Manifold.pathELength I σ 0 1) ∧
       (∀ r : ℝ, 0 < r → r ≤ ε →
          ∀ (σ : ℝ → M) (n : ℕ) (τ : ℕ → ℝ),
          τ 0 = 0 → τ n = 1 → (∀ i < n, τ i ≤ τ (i + 1)) →
          ContinuousOn σ (Icc (0 : ℝ) 1) →
          (∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (τ i) (τ (i + 1)))) →
          σ 0 = p →
          σ 1 ∉ (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
            ball (0 : E) r →
          ENNReal.ofReal (r / Real.sqrt c) ≤ Manifold.pathELength I σ 0 1)) := by
  classical
  obtain ⟨ε₁, hε₁, hdom₁, hsrc₁, hinj₁, hopenM₁, hfC1, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  obtain ⟨ρ₁, hρ₁, hdomr, hsrcr, hradial₁⟩ :=
    exists_gauss_radial_lower_bound_ball (I := I) g p
  obtain ⟨ρo, hρo, hdomo, hsrco, hopen⟩ := exists_isOpen_expMap_image (I := I) g p
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  have hgram0 : ∀ w : E,
      ‖w‖ ^ 2 ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) w w :=
    fun w => hgramV _ (mem_of_mem_nhds hVc) w
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  set f : E → E :=
    fun w => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  -- radii: `ρ` fits inside every input radius; `r'` is the escape radius,
  -- `ρ''` an intermediate open ball on which the inverse chart data is `C¹`
  set ρ : ℝ := min (min ε₁ ρ₁) ρo with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hε₁ hρ₁) hρo
  have hρε₁ : ρ ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hρρ₁ : ρ ≤ ρ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hρρo : ρ ≤ ρo := min_le_right _ _
  set r' : ℝ := ρ / 2 with hr'def
  set ρ'' : ℝ := 3 * ρ / 4 with hρ''def
  have hr' : 0 < r' := by positivity
  have hr'ρ'' : r' < ρ'' := by rw [hr'def, hρ''def]; linarith
  have hρ''ρ : ρ'' < ρ := by rw [hρ''def]; linarith
  have hr'ρ : r' < ρ := hr'ρ''.trans hρ''ρ
  have hr'ε₁ : r' < ε₁ := lt_of_lt_of_le hr'ρ hρε₁
  -- the abstract inputs of the telescoped Gauss comparison, on the `ρ`-ball
  have htgt : ∀ u : E, ‖u‖ < ρ → f u ∈ (extChartAt I p).target := by
    intro u hu
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc₁ u (hu.trans_le hρε₁))
  have hfC1ρ : ContDiffOn ℝ 1 f (ball (0 : E) ρ) :=
    hfC1.mono (ball_subset_ball hρε₁)
  have hradial : ∀ v ξ : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (extChartAt I p p) v ξ ^ 2
        ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v
          * chartMetricInner (I := I) g p (f v) (fderiv ℝ f v ξ) (fderiv ℝ f v ξ) :=
    fun v ξ hv => hradial₁ v ξ (hv.trans_le hρρ₁)
  -- the escape neighborhood `U` and the ambient `C¹`-inverse region
  set U : Set M :=
    (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) '' ball (0 : E) r'
    with hUdef
  have hUopen : IsOpen U :=
    (hopen (ball (0 : E) r') (ball_subset_ball (le_of_lt (hr'ρ.trans_le hρρo)))
      isOpen_ball).2
  have hfopen : IsOpen (f '' ball (0 : E) ρ'') :=
    (hopen (ball (0 : E) ρ'') (ball_subset_ball (hρ''ρ.le.trans hρρo)) isOpen_ball).1
  have hfinvC1'' : ContDiffOn ℝ 1 finv (f '' ball (0 : E) ρ'') :=
    hfinvC1.mono (image_mono (ball_subset_ball (hρ''ρ.le.trans hρε₁)))
  have hfinv_fderiv_cont : ContinuousOn (fderiv ℝ finv) (f '' ball (0 : E) ρ'') :=
    hfinvC1''.continuousOn_fderiv_of_isOpen hfopen le_rfl
  have hpU : p ∈ U :=
    ⟨0, mem_ball_zero_iff.mpr (by simpa using hr'), expMap_zero (I := I) g p⟩
  -- membership in `U` gives the polar description
  have hpolar : ∀ x ∈ U, ∃ z : E, ‖z‖ < r' ∧
      x = expMap (I := I) g p (z : TangentSpace I p) := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨z, mem_ball_zero_iff.mp hz, rfl⟩
  -- ## The piecewise core comparison: a piecewise-`C¹` curve staying in the
  -- closed `r'`-region on `[0, T]` is at least as long as the `g_p`-radius of
  -- its polar endpoint at time `T`
  have hcore : ∀ (σ : ℝ → M) (n : ℕ) (τ : ℕ → ℝ) (T : ℝ), 0 < T → T ≤ 1 →
      τ 0 = 0 → τ n = 1 → (∀ i < n, τ i ≤ τ (i + 1)) →
      ContinuousOn σ (Icc (0 : ℝ) 1) →
      (∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (τ i) (τ (i + 1)))) →
      σ 0 = p →
      (∀ t ∈ Icc (0 : ℝ) T, ∃ z : E, ‖z‖ ≤ r' ∧
        σ t = expMap (I := I) g p (z : TangentSpace I p)) →
      ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
          (finv (extChartAt I p (σ T))) (finv (extChartAt I p (σ T)))))
        ≤ Manifold.pathELength I σ 0 T := by
    intro σ n τ T hT0 hT1 hτ0 hτn hτmono hσcont hσpc hσ0 hstay
    -- `n` is positive since `τ 0 = 0 < 1 = τ n`
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · rw [hτ0] at hτn; norm_num at hτn
      · exact h
    -- the truncated partition `τ' i = min (τ i) T` of `[0, T]`
    set τ' : ℕ → ℝ := fun i => min (τ i) T with hτ'def
    have hτ'0 : τ' 0 = 0 := by
      simp only [hτ'def]
      rw [hτ0]
      exact min_eq_left hT0.le
    have hτ'n : τ' n = T := by
      simp only [hτ'def]
      rw [hτn]
      exact min_eq_right hT1
    have hτ'mono : ∀ i < n, τ' i ≤ τ' (i + 1) :=
      fun i hi => min_le_min (hτmono i hi) le_rfl
    have hτ'le : ∀ i ≤ n, 0 ≤ τ' i ∧ τ' i ≤ T := by
      intro i hin
      refine ⟨?_, min_le_right _ _⟩
      rw [← hτ'0]
      exact partition_le hτ'mono (Nat.zero_le i) hin
    -- the curve stays in the chart source on `[0, T]`
    have hsrcσ : ∀ t ∈ Icc (0 : ℝ) T, σ t ∈ (chartAt H p).source := by
      intro t ht
      obtain ⟨z, hz, hσt⟩ := hstay t ht
      rw [hσt]
      exact hsrc₁ z (hz.trans_lt hr'ε₁)
    set u : ℝ → E := fun s => extChartAt I p (σ s) with hudef
    -- global continuity of the chart reading on `[0, T]`
    have hu_cont : ContinuousOn u (Icc (0 : ℝ) T) := by
      refine (continuousOn_extChartAt (I := I) p).comp
        (hσcont.mono (Icc_subset_Icc le_rfl hT1)) ?_
      intro t ht
      rw [extChartAt_source]
      exact hsrcσ t ht
    -- the polar coordinates of the curve
    have hwz : ∀ t ∈ Icc (0 : ℝ) T, ‖finv (u t)‖ ≤ r' ∧ f (finv (u t)) = u t := by
      intro t ht
      obtain ⟨z, hz, hσt⟩ := hstay t ht
      have hut : u t = f z := by rw [hudef]; simp only; rw [hσt]
      have hwt : finv (u t) = z := by
        rw [hut]; exact hlinv z (hz.trans_lt hr'ε₁)
      rw [hwt]
      exact ⟨hz, hut.symm⟩
    set w : ℝ → E := fun s => finv (u s) with hwdef
    have humem : ∀ t ∈ Icc (0 : ℝ) T, u t ∈ f '' ball (0 : E) ρ'' := by
      intro t ht
      exact ⟨w t, mem_ball_zero_iff.mpr ((hwz t ht).1.trans_lt hr'ρ''), (hwz t ht).2⟩
    have hw_cont : ContinuousOn w (Icc (0 : ℝ) T) :=
      (hfinvC1''.continuousOn).comp hu_cont humem
    -- per-piece derivative data on the truncated pieces
    set u' : ℕ → ℝ → E := fun i => derivWithin u (Icc (τ' i) (τ' (i + 1))) with hu'def
    set w' : ℕ → ℝ → E := fun i t => fderiv ℝ finv (u t) (u' i t) with hw'def
    have hpiece_sub : ∀ i < n, Icc (τ' i) (τ' (i + 1)) ⊆ Icc (0 : ℝ) T := by
      intro i hi
      exact Icc_subset_Icc (hτ'le i hi.le).1 (hτ'le (i + 1) hi).2
    -- a nondegenerate truncated piece keeps its left end and sits inside the
    -- original piece
    have hpiece_orig : ∀ i < n, τ' i < τ' (i + 1) →
        Icc (τ' i) (τ' (i + 1)) ⊆ Icc (τ i) (τ (i + 1)) := by
      intro i hi hlt
      have hτiT : τ i < T := by
        by_contra hnot
        push Not at hnot
        have h1 : τ' (i + 1) ≤ τ' i := by
          simp only [hτ'def]
          rw [min_eq_right hnot]
          exact min_le_right _ _
        exact absurd hlt (not_lt.mpr h1)
      have hτ'i : τ' i = τ i := by
        simp only [hτ'def]
        exact min_eq_left hτiT.le
      rw [hτ'i]
      exact Icc_subset_Icc le_rfl (min_le_left _ _)
    have huC1 : ∀ i < n, τ' i < τ' (i + 1) →
        ContDiffOn ℝ 1 u (Icc (τ' i) (τ' (i + 1))) := by
      intro i hi hlt
      refine Geodesic.contDiffOn_extChartAt_comp
        ((hσpc i hi).mono (hpiece_orig i hi hlt)) ?_
      intro t ht
      exact hsrcσ t (hpiece_sub i hi ht)
    have hu'deriv : ∀ i < n, ∀ t ∈ Ioo (τ' i) (τ' (i + 1)),
        HasDerivAt u (u' i t) t := by
      intro i hi t ht
      have hlt : τ' i < τ' (i + 1) := ht.1.trans ht.2
      have h1 : HasDerivWithinAt u (u' i t) (Icc (τ' i) (τ' (i + 1))) t :=
        ((huC1 i hi hlt).differentiableOn one_ne_zero t
          (Ioo_subset_Icc_self ht)).hasDerivWithinAt
      exact h1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hu'cont : ∀ i < n, τ' i < τ' (i + 1) →
        ContinuousOn (u' i) (Icc (τ' i) (τ' (i + 1))) := by
      intro i hi hlt
      exact (huC1 i hi hlt).continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
    have hw_deriv : ∀ i < n, ∀ t ∈ Ioo (τ' i) (τ' (i + 1)),
        HasDerivAt w (w' i t) t := by
      intro i hi t ht
      have htIcc : t ∈ Icc (0 : ℝ) T := hpiece_sub i hi (Ioo_subset_Icc_self ht)
      have hfinv_at : HasFDerivAt finv (fderiv ℝ finv (u t)) (u t) :=
        ((hfinvC1''.contDiffAt (hfopen.mem_nhds (humem t htIcc))).differentiableAt
          one_ne_zero).hasFDerivAt
      simpa [hwdef, hw'def, Function.comp_def] using
        hfinv_at.comp_hasDerivAt t (hu'deriv i hi t ht)
    have hw'_cont : ∀ i < n, ContinuousOn (w' i) (Icc (τ' i) (τ' (i + 1))) := by
      intro i hi
      rcases lt_or_ge (τ' i) (τ' (i + 1)) with hlt | hge
      · exact (hfinv_fderiv_cont.comp (hu_cont.mono (hpiece_sub i hi))
          (fun t ht => humem t (hpiece_sub i hi ht))).clm_apply (hu'cont i hi hlt)
      · have heq : τ' (i + 1) = τ' i := le_antisymm hge (hτ'mono i hi)
        rw [heq, Icc_self]
        exact continuousOn_singleton _ _
    have hwball : ∀ t ∈ Icc (0 : ℝ) T, ‖w t‖ < ρ :=
      fun t ht => ((hwz t ht).1).trans_lt hr'ρ
    -- the telescoped Gauss radius comparison on the truncated partition
    have hreach := gauss_radius_reach_piecewise (I := I) g p f htgt hfC1ρ hradial
      hτ'mono (by rw [hτ'0, hτ'n]; exact hw_cont) hw_deriv hw'_cont
      (by rw [hτ'0, hτ'n]; exact hwball) hn
      (t₁ := T) (by rw [hτ'0, hτ'n]; exact ⟨hT0.le, le_rfl⟩)
    -- the lift starts at the origin
    have hw0 : w 0 = 0 := by
      have hu0 : u 0 = f 0 := by
        rw [hudef, hfdef]; simp only; rw [hσ0]
        exact congrArg (extChartAt I p) (expMap_zero (I := I) g p).symm
      rw [hwdef]; simp only; rw [hu0]
      exact hlinv 0 (by simpa using hε₁)
    rw [hτ'0, hw0, chartMetricInner_zero_left, Real.sqrt_zero, sub_zero] at hreach
    -- identify the comparison integrand with the chart-read speed of `σ`
    have hcongr : ∀ i < n,
        (∫ t in τ' i..τ' (i + 1), Real.sqrt (chartMetricInner (I := I) g p
          (f (w t)) (fderiv ℝ f (w t) (w' i t)) (fderiv ℝ f (w t) (w' i t))))
        = ∫ t in τ' i..τ' (i + 1), Real.sqrt (chartMetricInner (I := I) g p
            (u t) (u' i t) (u' i t)) := by
      intro i hi
      rw [intervalIntegral.integral_of_le (hτ'mono i hi),
        intervalIntegral.integral_of_le (hτ'mono i hi),
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
      have htIcc : t ∈ Icc (0 : ℝ) T := hpiece_sub i hi (Ioo_subset_Icc_self ht)
      have ht0T : t ∈ Ioo (0 : ℝ) T :=
        ⟨(hτ'le i hi.le).1.trans_lt ht.1, ht.2.trans_le (hτ'le (i + 1) hi).2⟩
      have hf_at : HasFDerivAt f (fderiv ℝ f (w t)) (w t) :=
        ((hfC1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr
          (((hwz t htIcc).1).trans_lt hr'ε₁)))).differentiableAt
            one_ne_zero).hasFDerivAt
      have hfw : HasDerivAt (fun s => f (w s))
          (fderiv ℝ f (w t) (w' i t)) t := by
        simpa [Function.comp_def] using hf_at.comp_hasDerivAt t (hw_deriv i hi t ht)
      have hfw_u : HasDerivAt u (fderiv ℝ f (w t) (w' i t)) t := by
        refine hfw.congr_of_eventuallyEq ?_
        filter_upwards [Icc_mem_nhds ht0T.1 ht0T.2] with s hs
        exact ((hwz s hs).2).symm
      have hfd : fderiv ℝ f (w t) (w' i t) = u' i t :=
        hfw_u.unique (hu'deriv i hi t ht)
      have hbase : f (w t) = u t := (hwz t htIcc).2
      rw [hbase, hfd]
    -- per-piece bridge to `pathELength`
    have hbridge : ∀ i < n,
        ENNReal.ofReal (∫ t in τ' i..τ' (i + 1), Real.sqrt
            (chartMetricInner (I := I) g p (u t) (u' i t) (u' i t)))
          = Manifold.pathELength I σ (τ' i) (τ' (i + 1)) := by
      intro i hi
      rcases eq_or_lt_of_le (hτ'mono i hi) with heq | hlt
      · rw [← heq]
        simp [Manifold.pathELength_self, intervalIntegral.integral_same]
      · exact (Geodesic.pathELength_eq_ofReal_integral_chartMetricInner (I := I) g
          (hτ'mono i hi) ((hσpc i hi).mono (hpiece_orig i hi hlt))
          (fun t ht => hsrcσ t (hpiece_sub i hi ht))).symm
    -- assemble
    have htotal : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
          (w T) (w T))
        ≤ ∑ i ∈ Finset.range n, ∫ t in τ' i..τ' (i + 1),
            Real.sqrt (chartMetricInner (I := I) g p (u t) (u' i t) (u' i t)) := by
      refine le_trans hreach (le_of_eq ?_)
      exact Finset.sum_congr rfl fun i hi => hcongr i (Finset.mem_range.mp hi)
    have hsum_eq : ∑ i ∈ Finset.range n,
          Manifold.pathELength I σ (τ' i) (τ' (i + 1))
        = Manifold.pathELength I σ 0 T := by
      have h := pathELength_sum_partition (I := I) g (σ := σ) hτ'mono
      rw [hτ'0, hτ'n] at h
      exact h
    calc ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p p) (w T) (w T)))
        ≤ ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ t in τ' i..τ' (i + 1),
            Real.sqrt (chartMetricInner (I := I) g p (u t) (u' i t) (u' i t))) :=
          ENNReal.ofReal_le_ofReal htotal
      _ = ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ t in τ' i..τ' (i + 1),
            Real.sqrt (chartMetricInner (I := I) g p (u t) (u' i t) (u' i t))) :=
          ENNReal.ofReal_sum_of_nonneg fun i hi =>
            intervalIntegral.integral_nonneg (hτ'mono i (Finset.mem_range.mp hi))
              fun t _ => Real.sqrt_nonneg _
      _ = ∑ i ∈ Finset.range n, Manifold.pathELength I σ (τ' i) (τ' (i + 1)) :=
          Finset.sum_congr rfl fun i hi => hbridge i (Finset.mem_range.mp hi)
      _ = Manifold.pathELength I σ 0 T := hsum_eq
  -- `exp_p` is continuous on the closed `r'`-ball (through the chart and `f`)
  have hexp_cont : ContinuousOn
      (fun z : E => expMap (I := I) g p (z : TangentSpace I p))
      (closedBall (0 : E) r') := by
    have h1 : ContinuousOn f (closedBall (0 : E) r') :=
      hfC1.continuousOn.mono (closedBall_subset_ball hr'ε₁)
    have h2 : ContinuousOn (extChartAt I p).symm (extChartAt I p).target :=
      continuousOn_extChartAt_symm p
    have hmap : MapsTo f (closedBall (0 : E) r') (extChartAt I p).target := by
      intro z hz
      exact (extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hsrc₁ z ((mem_closedBall_zero_iff.mp hz).trans_lt hr'ε₁))
    refine (h2.comp h1 hmap).congr ?_
    intro z hz
    show expMap (I := I) g p (z : TangentSpace I p) = (extChartAt I p).symm (f z)
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hsrc₁ z ((mem_closedBall_zero_iff.mp hz).trans_lt hr'ε₁))).symm
  -- ## First exit: a continuous curve leaving `U` stays in the closed region
  -- up to a first exit time, where it sits exactly on the coordinate
  -- `r'`-sphere (only continuity of the curve is used)
  have hfirstexit : ∀ σ : ℝ → M, ContinuousOn σ (Icc (0 : ℝ) 1) → σ 0 = p →
      (∃ t ∈ Icc (0 : ℝ) 1, σ t ∉ U) →
      ∃ T ∈ Ioc (0 : ℝ) 1, (∃ z₀ : E, ‖z₀‖ = r' ∧
          σ T = expMap (I := I) g p (z₀ : TangentSpace I p)) ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∃ z : E, ‖z‖ ≤ r' ∧
          σ t = expMap (I := I) g p (z : TangentSpace I p) := by
    rintro σ hσcont hσ0 ⟨t₀, ht₀, ht₀U⟩
    set A : Set ℝ := Icc (0 : ℝ) 1 ∩ σ ⁻¹' Uᶜ with hAdef
    have hA_closed : IsClosed A :=
      hσcont.preimage_isClosed_of_isClosed isClosed_Icc hUopen.isClosed_compl
    have hA_ne : A.Nonempty := ⟨t₀, ht₀, ht₀U⟩
    have hA_bdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
    set T : ℝ := sInf A with hTdef
    have hTA : T ∈ A := hA_closed.csInf_mem hA_ne hA_bdd
    have hT01 : T ∈ Icc (0 : ℝ) 1 := hTA.1
    have hT_pos : 0 < T := by
      rcases eq_or_lt_of_le hT01.1 with h | h
      · exact absurd (h ▸ (hσ0 ▸ hpU) : σ T ∈ U) hTA.2
      · exact h
    have hbefore : ∀ t, 0 ≤ t → t < T → σ t ∈ U := by
      intro t ht0 htT
      by_contra hnot
      exact absurd (csInf_le hA_bdd ⟨⟨ht0, htT.le.trans hT01.2⟩, hnot⟩)
        (not_le.mpr htT)
    -- the exit point lies on the closed `r'`-sphere via compactness
    set K : Set M :=
      (fun z : E => expMap (I := I) g p (z : TangentSpace I p)) ''
        closedBall (0 : E) r' with hKdef
    have hKclosed : IsClosed K :=
      ((isCompact_closedBall (0 : E) r').image_of_continuousOn hexp_cont).isClosed
    have hUK : U ⊆ K := image_mono ball_subset_closedBall
    have hσT_K : σ T ∈ K := by
      have hne : (𝓝[Ioo (0 : ℝ) T] T).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (by
          rw [closure_Ioo hT_pos.ne]
          exact right_mem_Icc.mpr hT_pos.le)
      have htend : Tendsto σ (𝓝[Ioo (0 : ℝ) T] T) (𝓝 (σ T)) :=
        ((hσcont T hT01).mono
          (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hT01.2))).tendsto
      exact hKclosed.mem_of_tendsto htend
        (eventually_nhdsWithin_of_forall fun t ht => hUK (hbefore t ht.1.le ht.2))
    obtain ⟨z₀, hz₀mem, hz₀eq⟩ := hσT_K
    have hz₀norm : ‖z₀‖ = r' := by
      rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz₀mem) with h | h
      · exact absurd (⟨z₀, mem_ball_zero_iff.mpr h, hz₀eq⟩ : σ T ∈ U) hTA.2
      · exact h
    have hstayT : ∀ t ∈ Icc (0 : ℝ) T, ∃ z : E, ‖z‖ ≤ r' ∧
        σ t = expMap (I := I) g p (z : TangentSpace I p) := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with rfl | htT
      · exact ⟨z₀, hz₀norm.le, hz₀eq.symm⟩
      · obtain ⟨z, hz, hzeq⟩ := hpolar (σ t) (hbefore t ht.1 htT)
        exact ⟨z, hz.le, hzeq⟩
    exact ⟨T, ⟨hT_pos, hT01.2⟩, ⟨z₀, hz₀norm, hz₀eq.symm⟩, hstayT⟩
  -- ## The escape estimate for piecewise competitors: leaving `U` costs at
  -- least `r'/√c`
  have hexit : ∀ (σ : ℝ → M) (n : ℕ) (τ : ℕ → ℝ),
      τ 0 = 0 → τ n = 1 → (∀ i < n, τ i ≤ τ (i + 1)) →
      ContinuousOn σ (Icc (0 : ℝ) 1) →
      (∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc (τ i) (τ (i + 1)))) →
      σ 0 = p → (∃ t ∈ Icc (0 : ℝ) 1, σ t ∉ U) →
      ENNReal.ofReal (r' / Real.sqrt c) ≤ Manifold.pathELength I σ 0 1 := by
    intro σ n τ hτ0 hτn hτmono hσcont hσpc hσ0 hex
    obtain ⟨T, hT, ⟨z₀, hz₀norm, hz₀eq⟩, hstayT⟩ := hfirstexit σ hσcont hσ0 hex
    have hbound := hcore σ n τ T hT.1 hT.2 hτ0 hτn hτmono hσcont hσpc hσ0 hstayT
    have hwT : finv (extChartAt I p (σ T)) = z₀ := by
      rw [hz₀eq]
      exact hlinv z₀ (hz₀norm ▸ hr'ε₁)
    rw [hwT] at hbound
    refine le_trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hbound)
      (Manifold.pathELength_mono le_rfl hT.2)
    have hQ0 : 0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) z₀ z₀ :=
      chartMetricInner_self_nonneg_of_mem_target (I := I) g p
        (mem_extChartAt_target p) z₀
    have h2 : r' ^ 2 / c
        ≤ chartMetricInner (I := I) g p (extChartAt I p p) z₀ z₀ := by
      rw [div_le_iff₀ hc, mul_comm]
      calc r' ^ 2 = ‖z₀‖ ^ 2 := by rw [hz₀norm]
        _ ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) z₀ z₀ := hgram0 z₀
    calc r' / Real.sqrt c = Real.sqrt (r' ^ 2 / c) := by
          rw [Real.sqrt_div (by positivity) c, Real.sqrt_sq hr'.le]
      _ ≤ Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) z₀ z₀) :=
          Real.sqrt_le_sqrt h2
  -- ## smallness: coordinate-`ε` vectors are `g_p`-shorter than the escape cost
  obtain ⟨ε₂, hε₂, hQsmall⟩ := exists_forall_chartMetricInner_self_lt (I := I) g p
    (θ := (r' / Real.sqrt c) ^ 2) (by positivity)
  set ε : ℝ := min r' ε₂ with hεdef
  have hε : 0 < ε := lt_min hr' hε₂
  have hεr' : ε ≤ r' := min_le_left _ _
  have hεε₂ : ε ≤ ε₂ := min_le_right _ _
  have hεε₁ : ε < ε₁ := lt_of_le_of_lt hεr' hr'ε₁
  refine ⟨ε, c, hε, hc,
    fun w hw => hdom₁ w (hw.trans hεε₁),
    fun w hw => hsrc₁ w (hw.trans hεε₁),
    hinj₁.mono (ball_subset_ball hεε₁.le),
    fun r hr => (hopen (ball (0 : E) r) (ball_subset_ball
      (hr.trans (hεr'.trans (hr'ρ.le.trans hρρo)))) isOpen_ball).2, ?_, ?_⟩
  -- ### endpoint bound
  · intro v hv σ n τ hτ0 hτn hτmono hσcont hσpc hσ0 hσ1
    by_cases hstay : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ U
    · -- staying case: the polar endpoint is `v` itself
      have hstay' : ∀ t ∈ Icc (0 : ℝ) 1, ∃ z : E, ‖z‖ ≤ r' ∧
          σ t = expMap (I := I) g p (z : TangentSpace I p) := by
        intro t ht
        obtain ⟨z, hz, hzeq⟩ := hpolar (σ t) (hstay t ht)
        exact ⟨z, hz.le, hzeq⟩
      have hbound := hcore σ n τ 1 one_pos le_rfl hτ0 hτn hτmono hσcont hσpc
        hσ0 hstay'
      have hwv : finv (extChartAt I p (σ 1)) = v := by
        rw [hσ1]
        exact hlinv v (hv.trans hεε₁)
      rwa [hwv] at hbound
    · -- escape case: the curve is longer than `r'/√c > √⟨v,v⟩_p`
      push Not at hstay
      have hbound := hexit σ n τ hτ0 hτn hτmono hσcont hσpc hσ0 hstay
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hbound
      have hQv : chartMetricInner (I := I) g p (extChartAt I p p) v v
          < (r' / Real.sqrt c) ^ 2 := hQsmall v (hv.trans_le hεε₂)
      calc Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v)
          ≤ Real.sqrt ((r' / Real.sqrt c) ^ 2) := Real.sqrt_le_sqrt hQv.le
        _ = r' / Real.sqrt c := Real.sqrt_sq (by positivity)
  -- ### escape bound for sub-balls
  · intro r hr hrε σ n τ hτ0 hτn hτmono hσcont hσpc hσ0 hσ1
    by_cases hstay : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ U
    · -- staying case: the polar endpoint has norm at least `r`
      have hstay' : ∀ t ∈ Icc (0 : ℝ) 1, ∃ z : E, ‖z‖ ≤ r' ∧
          σ t = expMap (I := I) g p (z : TangentSpace I p) := by
        intro t ht
        obtain ⟨z, hz, hzeq⟩ := hpolar (σ t) (hstay t ht)
        exact ⟨z, hz.le, hzeq⟩
      have hbound := hcore σ n τ 1 one_pos le_rfl hτ0 hτn hτmono hσcont hσpc
        hσ0 hstay'
      obtain ⟨z₁, hz₁, hz₁eq⟩ := hpolar (σ 1) (hstay 1 (right_mem_Icc.mpr zero_le_one))
      have hwz₁ : finv (extChartAt I p (σ 1)) = z₁ := by
        rw [hz₁eq]
        exact hlinv z₁ (hz₁.trans hr'ε₁)
      rw [hwz₁] at hbound
      have hz₁r : r ≤ ‖z₁‖ := by
        by_contra hlt
        exact hσ1 ⟨z₁, mem_ball_zero_iff.mpr (not_le.mp hlt), hz₁eq.symm⟩
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hbound
      have hQ0 : 0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) z₁ z₁ :=
        chartMetricInner_self_nonneg_of_mem_target (I := I) g p
          (mem_extChartAt_target p) z₁
      have h2 : r ^ 2 / c
          ≤ chartMetricInner (I := I) g p (extChartAt I p p) z₁ z₁ := by
        rw [div_le_iff₀ hc, mul_comm]
        calc r ^ 2 ≤ ‖z₁‖ ^ 2 := pow_le_pow_left₀ hr.le hz₁r 2
          _ ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) z₁ z₁ :=
              hgram0 z₁
      calc r / Real.sqrt c = Real.sqrt (r ^ 2 / c) := by
            rw [Real.sqrt_div (by positivity) c, Real.sqrt_sq hr.le]
        _ ≤ Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) z₁ z₁) :=
            Real.sqrt_le_sqrt h2
    · -- escape case: leaving `U` costs `r'/√c ≥ r/√c`
      push Not at hstay
      refine le_trans (ENNReal.ofReal_le_ofReal ?_)
        (hexit σ n τ hτ0 hτn hτmono hσcont hσpc hσ0 hstay)
      gcongr
      exact hrε.trans hεr'

end Exponential

end PetersenLib
