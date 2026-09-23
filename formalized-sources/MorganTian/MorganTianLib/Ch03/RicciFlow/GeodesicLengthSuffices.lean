import MorganTianLib.Ch03.RicciFlow.MetricTimeBoundary
import MorganTianLib.Ch03.RicciFlow.ForwardDifference
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Morgan--Tian Claim 3.23: geodesic length suffices for distance

This version includes initial times. A short closed interval to the right of
the time under consideration must lie in the flow domain. All compactness
and length-variation properties are derived from the geometric hypotheses.
-/

open scoped Topology Manifold ContDiff NNReal Interval Bundle ENNReal
open Set Filter Metric Riemannian Riemannian.Geodesic MeasureTheory

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

/-- **Math.** The lower forward-Dini bound in this project is precisely the lower bound
on the extended-real liminf of right slopes. Using `EReal` avoids the arbitrary
real-valued `sSup` of an unbounded set of eventual lower bounds. -/
theorem forwardDiffQuotientGE_iff_le_liminf
    {f : ℝ → ℝ} {t C : ℝ} :
    ForwardDiffQuotientGE f t C ↔
      (C : EReal) ≤ liminf (fun s => (slope f t s : EReal)) (𝓝[>] t) := by
  rw [le_liminf_iff]
  constructor
  · intro h y hy
    obtain ⟨r, hyr, hrC⟩ := EReal.exists_between_coe_real hy
    filter_upwards [h r (EReal.coe_lt_coe_iff.mp hrC)] with s hs
    exact hyr.trans (EReal.coe_lt_coe_iff.mpr hs)
  · intro h r hr
    filter_upwards [h (r : EReal) (EReal.coe_lt_coe_iff.mpr hr)] with s hs
    exact EReal.coe_lt_coe_iff.mp hs

variable {X : Type*} [TopologicalSpace X]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [T3Space M] [ConnectedSpace M]
  [T2Space (TangentBundle I M)]

/-- **Math.** Claim 3.23 including initial metric times, for distinct endpoints.
All geodesic compactness and length-continuity inputs are derived in the
proof; the only derivative bound assumed is the one on initial minimizers. -/
theorem geodesic_length_suffices_for_distance_right_of_ne
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    (hcomplete : ∀ t ∈ J, IsCompleteMetric (g t))
    {t₀ b C : ℝ} (htb : t₀ < b) (hwindow : Icc t₀ b ⊆ J) {x y : M} (hxy : x ≠ y)
    (hbound : ∀ γ : ℝ → M, γ 0 = x → γ 1 = y → Continuous γ → IsGeodesic (g t₀) γ →
      metricCurveLengthReal (g t₀) γ 0 1 = metricDistanceReal (g t₀) x y →
      C ≤ derivWithin (fun t => metricCurveLengthReal (g t) γ 0 1) (Ici t₀) t₀) :
    ForwardDiffQuotientGE (fun t => metricDistanceReal (g t) x y) t₀ C := by
  classical
  have ht₀ : t₀ ∈ J := hwindow ⟨le_rfl, htb.le⟩
  have hwin : Ioo t₀ b ⊆ interior J :=
    interior_maximal (Ioo_subset_Icc_self.trans hwindow) isOpen_Ioo
  let d := fun t => metricDistanceReal (g t) x y
  intro r hr
  by_contra hbad
  have hfreq : ∃ᶠ t in 𝓝[>] t₀, t ∈ Ioo t₀ b ∧ slope d t₀ t ≤ r :=
    ((show ∃ᶠ t in 𝓝[>] t₀, ¬r < slope d t₀ t by
      simpa only [Filter.Frequently, not_not] using hbad).and_eventually
      (Ioo_mem_nhdsGT htb)).mono fun t ht => ⟨ht.2, not_lt.mp ht.1⟩
  obtain ⟨ts, hts', hbadts⟩ := exists_seq_forall_of_frequently hfreq
  have hts : Tendsto ts atTop (𝓝 t₀) := hts'.mono_right nhdsWithin_le_nhds
  have htI : ∀ n, ts n ∈ Ioo t₀ b := fun n => (hbadts n).1
  have htJ : ∀ n, ts n ∈ interior J := fun n => hwin (htI n)
  choose γs hstart hend hcγs hγs hmin using fun n =>
    exists_minimizing_geodesic_metricDistanceReal_at hg.smooth (interior_subset (htJ n))
      (hcomplete _ (interior_subset (htJ n))) x y
  obtain ⟨η, hη0, hη1, hcη, hη, hηmin⟩ := exists_minimizing_geodesic_metricDistanceReal_at
    hg.smooth ht₀ (hcomplete _ ht₀) x y
  have hηdata : GeodesicDataTendsto (I := I) η (fun _ => η) (fun _ => 0) 0 :=
    ⟨tendsto_const_nhds, tendsto_const_nhds⟩
  have hηlim := geodesicMetric_tendsto_length_right hg.smooth htb hwindow tendsto_const_nhds hts
    (fun _ => le_rfl) (fun n => (htI n).1.le) hη hcη (fun _ => hη) (fun _ => hcη) hηdata 0 1
  have hB : ∀ᶠ n in atTop, metricCurveLengthReal (g (ts n)) (γs n) 0 1 ≤
      metricCurveLengthReal (g t₀) η 0 1 + 1 := by
    filter_upwards [hηlim.eventually (gt_mem_nhds (lt_add_one _))] with n hn
    rw [hmin n]
    have hcmp : metricDistanceReal (g (ts n)) x y ≤ metricCurveLengthReal (g (ts n)) η 0 1 := by
      simpa only [hη0, hη1] using metricDistanceReal_le_geodesic_length hg.smooth hη hcη (htJ n)
    exact hcmp.trans hn.le
  obtain ⟨γ, φ, hφ, hγ0, hcγ, hγ, hinit⟩ :=
    exists_geodesic_subseq_of_eventually_length_le_right hg.smooth htb hwindow hts
      (fun n => (htI n).1.le) (hcomplete _ ht₀) hγs hcγs hstart hB
  have htsφ := hts.comp hφ.tendsto_atTop
  have hγ1 : γ 1 = y := by
    have hlim := (geodesicMetric_dataTendsto_right hg.smooth htb hwindow htsφ
      (fun n => (htI (φ n)).1.le) hγ hcγ
      (fun n => hγs (φ n)) (fun n => hcγs (φ n)) hinit (s₀ := 1) tendsto_const_nhds).1
    have hconst : Tendsto (fun n => γs (φ n) 1) atTop (𝓝 y) := by
      simpa only [hend] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))
    exact tendsto_nhds_unique hlim hconst
  have hLlim := geodesicMetric_tendsto_length_right hg.smooth htb hwindow htsφ htsφ
    (fun n => (htI (φ n)).1.le) (fun n => (htI (φ n)).1.le) hγ hcγ
    (fun n => hγs (φ n)) (fun n => hcγs (φ n)) hinit 0 1
  have hγmin : metricCurveLengthReal (g t₀) γ 0 1 = d t₀ := by
    apply le_antisymm _ (by simpa only [hγ0, hγ1] using
      metricDistanceReal_le_geodesic_length_at hg.smooth hγ hcγ ht₀)
    change metricCurveLengthReal (g t₀) γ 0 1 ≤ metricDistanceReal (g t₀) x y
    rw [← hηmin]
    apply le_of_tendsto_of_tendsto hLlim (hηlim.comp hφ.tendsto_atTop)
    exact Eventually.of_forall fun n => by
      change metricCurveLengthReal (g (ts (φ n))) (γs (φ n)) 0 1 ≤
        metricCurveLengthReal (g (ts (φ n))) η 0 1
      rw [hmin (φ n)]
      simpa only [hη0, hη1] using
        metricDistanceReal_le_geodesic_length hg.smooth hη hcη (htJ (φ n))
  have hvγ : ∀ s, mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) ≠ 0 :=
    geodesic_velocity_ne_zero_of_endpoints_ne hγ hcγ (by simpa only [hγ0, hγ1] using hxy)
  have hvs : ∀ n s, mfderiv 𝓘(ℝ, ℝ) I (γs n) s (1 : ℝ) ≠ 0 :=
    fun n => geodesic_velocity_ne_zero_of_endpoints_ne (hγs n) (hcγs n)
      (by simpa only [hstart, hend] using hxy)
  have hderiv (n : ℕ) (t : ℝ) (ht : t ∈ Ioo t₀ (ts n)) :=
    hasDerivAt_metricCurveLengthReal_geodesic (a := 0) (b := 1) hg (hγs n) (hcγs n)
      (fun s _ => hvs n s) (hwin ⟨ht.1, ht.2.trans (htI n).2⟩)
  have hmean : ∀ n, ∃ s ∈ Ioo t₀ (ts n),
      (∫ u in (0 : ℝ)..1, metricCurveNormTimeDeriv (g s) (γs n) u) ≤ r := by
    intro n
    obtain ⟨s, hs, hslope⟩ := exists_hasDerivAt_eq_slope
      (fun t => metricCurveLengthReal (g t) (γs n) 0 1)
      (fun t => ∫ u in (0 : ℝ)..1, metricCurveNormTimeDeriv (g t) (γs n) u) (htI n).1
      (fun t ht => by
        by_cases heq : t = t₀
        · subst t
          exact (continuousWithinAt_length_right hg.smooth htb hwindow (hγs n) (hcγs n) 0 1).mono
            (fun _ hu => hu.1)
        · exact (hasDerivAt_metricCurveLengthReal_geodesic (a := 0) (b := 1) hg (hγs n)
            (hcγs n) (fun s _ => hvs n s)
            (hwin ⟨lt_of_le_of_ne ht.1 (Ne.symm heq), ht.2.trans_lt (htI n).2⟩)).continuousAt.continuousWithinAt)
      (fun t ht => hderiv n t ht)
    refine ⟨s, hs, ?_⟩
    rw [hslope, hmin n]
    have hinitlen := metricDistanceReal_le_geodesic_length_at hg.smooth (hγs n) (hcγs n) ht₀
    rw [hstart n, hend n] at hinitlen
    have hdist := (hbadts n).2
    rw [slope_def_field] at hdist
    exact (div_le_div_of_nonneg_right (sub_le_sub_left hinitlen _)
      (sub_pos.mpr (htI n).1).le).trans hdist
  choose us hus husbound using hmean
  have huslim : Tendsto us atTop (𝓝 t₀) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hts
      (fun n => (hus n).1.le) (fun n => (hus n).2.le)
  have hDlim := geodesicMetric_tendsto_lengthTimeDeriv_right (c := 0) (d := 1) hg htb hwindow htsφ
    (huslim.comp hφ.tendsto_atTop) (fun n => (htI (φ n)).1.le)
    (fun n => ⟨(hus (φ n)).1.le, (hus (φ n)).2.le.trans (htI (φ n)).2.le⟩) hγ hcγ (fun n => hγs (φ n)) (fun n => hcγs (φ n)) hinit
    (fun s _ => hvγ s) (fun n s _ => hvs (φ n) s)
  have hle := le_of_tendsto hDlim (Eventually.of_forall fun n => husbound (φ n))
  have hC := hbound γ hγ0 hγ1 hcγ hγ hγmin
  rw [(hasDerivWithinAt_length_geodesic_right (c := 0) (d := 1) hg htb hwindow hγ hcγ
    (fun s _ => hvγ s)).derivWithin (uniqueDiffWithinAt_Ici t₀)] at hC
  exact (not_le_of_gt hr) (hC.trans hle)

/-- **Math.** Claim 3.23 including initial metric times, including coincident
endpoints. This proves the forward lower-Dini bound for the actual metric
distance, with completeness and the initial-minimizer derivative bound as
the geometric hypotheses. -/
theorem geodesic_length_suffices_for_distance_right
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    (hcomplete : ∀ t ∈ J, IsCompleteMetric (g t))
    {t₀ b C : ℝ} (htb : t₀ < b) (hwindow : Icc t₀ b ⊆ J) (x y : M)
    (hbound : ∀ γ : ℝ → M, γ 0 = x → γ 1 = y → Continuous γ → IsGeodesic (g t₀) γ →
      metricCurveLengthReal (g t₀) γ 0 1 = metricDistanceReal (g t₀) x y →
      C ≤ derivWithin (fun t => metricCurveLengthReal (g t) γ 0 1) (Ici t₀) t₀) :
    ForwardDiffQuotientGE (fun t => metricDistanceReal (g t) x y) t₀ C := by
  by_cases hxy : x = y
  · subst y
    have hC := hbound (fun _ => x) rfl rfl continuous_const (isGeodesic_const (g t₀) x)
      (by simp only [metricCurveLengthReal_const, metricDistanceReal, dist_self])
    have hL : (fun t => metricCurveLengthReal (g t) (fun _ : ℝ => x) 0 1) = (fun _ : ℝ => 0) :=
      funext fun t => metricCurveLengthReal_const (g t) x
    rw [hL, (hasDerivWithinAt_const t₀ (Ici t₀) (0 : ℝ)).derivWithin
      (uniqueDiffWithinAt_Ici t₀)] at hC
    have hGE : ForwardDiffQuotientGE (fun _ => (0 : ℝ)) t₀ 0 :=
      HasDerivWithinAt.forwardDiffQuotientGE (hasDerivAt_const t₀ (0 : ℝ)).hasDerivWithinAt
    simpa only [metricDistanceReal, dist_self] using hGE.mono hC
  · exact geodesic_length_suffices_for_distance_right_of_ne hg hcomplete htb hwindow hxy hbound

/-- **Math.** The literal extended-real liminf formulation of Claim 3.23
including initial metric times. -/
theorem geodesic_length_suffices_for_distance_right_liminf
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    (hcomplete : ∀ t ∈ J, IsCompleteMetric (g t))
    {t₀ b C : ℝ} (htb : t₀ < b) (hwindow : Icc t₀ b ⊆ J) (x y : M)
    (hbound : ∀ γ : ℝ → M, γ 0 = x → γ 1 = y → Continuous γ → IsGeodesic (g t₀) γ →
      metricCurveLengthReal (g t₀) γ 0 1 = metricDistanceReal (g t₀) x y →
      C ≤ derivWithin (fun t => metricCurveLengthReal (g t) γ 0 1) (Ici t₀) t₀) :
    (C : EReal) ≤ Filter.liminf
      (fun t => (slope (fun u => metricDistanceReal (g u) x y) t₀ t : EReal)) (𝓝[>] t₀) :=
  forwardDiffQuotientGE_iff_le_liminf.mp
    (geodesic_length_suffices_for_distance_right hg hcomplete htb hwindow x y hbound)

/-- **Math.** At a differentiability time, the distance has derivative at
least the common lower bound on initial minimizing-geodesic length derivatives. -/
theorem geodesic_length_suffices_for_distance_right_deriv
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    (hcomplete : ∀ t ∈ J, IsCompleteMetric (g t))
    {t₀ b C d : ℝ} (htb : t₀ < b) (hwindow : Icc t₀ b ⊆ J) (x y : M)
    (hbound : ∀ γ : ℝ → M, γ 0 = x → γ 1 = y → Continuous γ → IsGeodesic (g t₀) γ →
      metricCurveLengthReal (g t₀) γ 0 1 = metricDistanceReal (g t₀) x y →
      C ≤ derivWithin (fun t => metricCurveLengthReal (g t) γ 0 1) (Ici t₀) t₀)
    (hd : HasDerivAt (fun t => metricDistanceReal (g t) x y) d t₀) : C ≤ d :=
  (HasDerivAt.forwardDiffQuotientGE_iff hd).mp
    (geodesic_length_suffices_for_distance_right hg hcomplete htb hwindow x y hbound)

/-- **Math.** Claim 3.23 at an interior metric time, including coincident
endpoints. This is a corollary of the right-time theorem, using the equality of the
ordinary and right derivatives at an interior time. -/
theorem geodesic_length_suffices_for_distance
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    (hcomplete : ∀ t ∈ J, IsCompleteMetric (g t))
    {t₀ C : ℝ} (ht₀ : t₀ ∈ interior J) (x y : M)
    (hbound : ∀ γ : ℝ → M, γ 0 = x → γ 1 = y → Continuous γ → IsGeodesic (g t₀) γ →
      metricCurveLengthReal (g t₀) γ 0 1 = metricDistanceReal (g t₀) x y →
      C ≤ deriv (fun t => metricCurveLengthReal (g t) γ 0 1) t₀) :
    ForwardDiffQuotientGE (fun t => metricDistanceReal (g t) x y) t₀ C := by
  by_cases hxy : x = y
  · subst y
    have hC := hbound (fun _ => x) rfl rfl continuous_const (isGeodesic_const (g t₀) x)
      (by simp only [metricCurveLengthReal_const, metricDistanceReal, dist_self])
    have hL : (fun t => metricCurveLengthReal (g t) (fun _ : ℝ => x) 0 1) = (fun _ : ℝ => 0) :=
      funext fun t => metricCurveLengthReal_const (g t) x
    rw [hL, deriv_const] at hC
    have hGE : ForwardDiffQuotientGE (fun _ => (0 : ℝ)) t₀ 0 :=
      HasDerivWithinAt.forwardDiffQuotientGE (hasDerivAt_const t₀ (0 : ℝ)).hasDerivWithinAt
    simpa only [metricDistanceReal, dist_self] using hGE.mono hC
  obtain ⟨l, b, _, hnhds, hwindow⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (isOpen_interior.mem_nhds ht₀)
  have ht₀I : t₀ ∈ Ioo l b := by
    simpa only [interior_Icc] using mem_interior_iff_mem_nhds.mpr hnhds
  apply geodesic_length_suffices_for_distance_right hg hcomplete ht₀I.2
    (fun t ht => interior_subset (hwindow ⟨ht₀I.1.le.trans ht.1, ht.2⟩)) x y
  intro γ hγ0 hγ1 hcγ hγ hmin
  have hv := geodesic_velocity_ne_zero_of_endpoints_ne hγ hcγ
    (by simpa only [hγ0, hγ1] using hxy)
  have hd := hasDerivAt_metricCurveLengthReal_geodesic (a := 0) (b := 1)
    hg hγ hcγ (fun u _ => hv u) ht₀
  rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici t₀), ← hd.deriv]
  exact hbound γ hγ0 hγ1 hcγ hγ hmin

/-- **Math.** The literal extended-real liminf formulation of Claim 3.23
at an interior metric time. -/
theorem geodesic_length_suffices_for_distance_liminf
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    (hcomplete : ∀ t ∈ J, IsCompleteMetric (g t))
    {t₀ C : ℝ} (ht₀ : t₀ ∈ interior J) (x y : M)
    (hbound : ∀ γ : ℝ → M, γ 0 = x → γ 1 = y → Continuous γ → IsGeodesic (g t₀) γ →
      metricCurveLengthReal (g t₀) γ 0 1 = metricDistanceReal (g t₀) x y →
      C ≤ deriv (fun t => metricCurveLengthReal (g t) γ 0 1) t₀) :
    (C : EReal) ≤ Filter.liminf
      (fun t => (slope (fun u => metricDistanceReal (g u) x y) t₀ t : EReal)) (𝓝[>] t₀) :=
  forwardDiffQuotientGE_iff_le_liminf.mp
    (geodesic_length_suffices_for_distance hg hcomplete ht₀ x y hbound)

/-- **Math.** At a differentiability time, the distance has derivative at
least the common lower bound on initial minimizing-geodesic length derivatives. -/
theorem geodesic_length_suffices_for_distance_deriv
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    (hcomplete : ∀ t ∈ J, IsCompleteMetric (g t))
    {t₀ C d : ℝ} (ht₀ : t₀ ∈ interior J) (x y : M)
    (hbound : ∀ γ : ℝ → M, γ 0 = x → γ 1 = y → Continuous γ → IsGeodesic (g t₀) γ →
      metricCurveLengthReal (g t₀) γ 0 1 = metricDistanceReal (g t₀) x y →
      C ≤ deriv (fun t => metricCurveLengthReal (g t) γ 0 1) t₀)
    (hd : HasDerivAt (fun t => metricDistanceReal (g t) x y) d t₀) : C ≤ d :=
  (HasDerivAt.forwardDiffQuotientGE_iff hd).mp
    (geodesic_length_suffices_for_distance hg hcomplete ht₀ x y hbound)

end MorganTianLib
