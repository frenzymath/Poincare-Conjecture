import MorganTianLib.Ch03.RicciFlow.GeodesicMetricReadback

/-!
# Global continuous dependence of geodesics on the metric

The curves in this file are genuine global intrinsic geodesics for possibly
different metrics in a smooth family. Local parameter-dependent coordinate
flows propagate convergence in both directions near each point of the limit
geodesic. A clopen argument then propagates it along the whole real line.
-/

open scoped Topology Manifold ContDiff NNReal
open Set Filter Metric Riemannian Riemannian.Geodesic

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Position and velocity convergence, with velocity expressed in
the chart at the limit foot. The curve parameters may vary with the sequence. -/
def GeodesicDataTendsto (γ : ℝ → M) (γs : ℕ → ℝ → M) (ss : ℕ → ℝ) (s₀ : ℝ) : Prop :=
  Tendsto (fun n => γs n (ss n)) atTop (𝓝 (γ s₀)) ∧
    Tendsto (fun n => deriv (chartReading (I := I) (γ s₀) (γs n)) (ss n))
      atTop (𝓝 (deriv (chartReading (I := I) (γ s₀) γ) s₀))

/-- **Math.** A common flow neighborhood propagates data convergence for
varying metrics between any two nearby curve parameters, including evaluation
at moving parameters. -/
theorem exists_geodesicMetric_convergence_step
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {ts : ℕ → ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ interior J) (hts : Tendsto ts atTop (𝓝 t₀))
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγ : IsGeodesic (g t₀) γ) (hcγ : Continuous γ)
    (hγs : ∀ n, IsGeodesic (g (ts n)) (γs n)) (hcγs : ∀ n, Continuous (γs n))
    (sstar : ℝ) :
    ∃ ρ > 0, ∀ b ∈ ball sstar ρ,
      GeodesicDataTendsto (I := I) γ γs (fun _ => b) b →
      ∀ {ss : ℕ → ℝ} {s₀ : ℝ}, s₀ ∈ ball sstar ρ → Tendsto ss atTop (𝓝 s₀) →
        GeodesicDataTendsto (I := I) γ γs ss s₀ := by
  let p := γ sstar
  let D : ℝ → ℝ × (E × E) := fun s =>
    (t₀, (extChartAt I p (γ s), deriv (chartReading (I := I) p γ) s))
  obtain ⟨r, ε, Z, L, hr, hε, hZ, hLip⟩ :=
    exists_local_geodesicFlow_metricParameter hg p ht₀ (mem_extChartAt_target p)
      (v₀ := deriv (chartReading (I := I) p γ) sstar)
  have hDcont : ContinuousAt D sstar := by
    obtain ⟨hfirst, a, ha, _⟩ := (hγ.hasGeodesicEquationAt sstar).solvesGeodesicODEAt
      hcγ.continuousAt (mem_chart_source H p)
    exact continuousAt_const.prodMk (hfirst.self_of_nhds.continuousAt.prodMk ha.continuousAt)
  have hnear : ∀ᶠ s in 𝓝 sstar,
      D s ∈ ball (D sstar) r ∧ γ s ∈ (chartAt H p).source :=
    (hDcont.eventually_mem (ball_mem_nhds _ hr)).and
      (hcγ.continuousAt.eventually_mem ((chartAt H p).open_source.mem_nhds
        (mem_chart_source H p)))
  obtain ⟨δ, hδ, hnearδ⟩ := Metric.eventually_nhds_iff.mp hnear
  let ρ := min δ (ε / 3)
  have hρ : 0 < ρ := lt_min hδ (by positivity)
  refine ⟨ρ, hρ, ?_⟩
  intro b hb hconv ss s₀ hs₀ hss
  have hbδ : dist b sstar < δ := (mem_ball.mp hb).trans_le (min_le_left _ _)
  have hsδ : dist s₀ sstar < δ := (mem_ball.mp hs₀).trans_le (min_le_left _ _)
  obtain ⟨hDb, hsrcb⟩ := hnearδ hbδ
  have hsrc₀ := (hnearδ hsδ).2
  have hDbc : D b ∈ closedBall (D sstar) r := ball_subset_closedBall hDb
  have hvelb : Tendsto (fun n => deriv (chartReading (I := I) p (γs n)) b)
      atTop (𝓝 (deriv (chartReading (I := I) p γ) b)) :=
    tendsto_geodesic_velocity_chartTransfer
      (fun n => (hγs n).hasGeodesicEquationAt b) (fun n => (hcγs n).continuousAt)
      (hγ.hasGeodesicEquationAt b) hcγ.continuousAt (mem_chart_source H (γ b))
      hsrcb hconv.1 hconv.2
  have hchartb : Tendsto (fun n => extChartAt I p (γs n b)) atTop
      (𝓝 (extChartAt I p (γ b))) :=
    ((continuousOn_extChartAt p).continuousAt
      ((isOpen_extChartAt_source p).mem_nhds (by rwa [extChartAt_source]))).tendsto.comp hconv.1
  let Ds : ℕ → ℝ × (E × E) := fun n =>
    (ts n, (extChartAt I p (γs n b), deriv (chartReading (I := I) p (γs n)) b))
  have hDs : Tendsto Ds atTop (𝓝 (D b)) := hts.prodMk_nhds (hchartb.prodMk_nhds hvelb)
  have hDsmem : ∀ᶠ n in atTop, Ds n ∈ closedBall (D sstar) r :=
    (hDs.eventually_mem (isOpen_ball.mem_nhds hDb)).mono fun _ hn => ball_subset_closedBall hn
  have hsrcs : ∀ᶠ n in atTop, γs n b ∈ (chartAt H p).source :=
    hconv.1.eventually_mem ((chartAt H p).open_source.mem_nhds hsrcb)
  have hdif : s₀ - b ∈ Ioo (-ε) ε := by
    have hsb : dist s₀ b < ε := calc
      dist s₀ b ≤ dist s₀ sstar + dist b sstar := dist_triangle_right _ _ _
      _ < ρ + ρ := add_lt_add (mem_ball.mp hs₀) (mem_ball.mp hb)
      _ ≤ ε / 3 + ε / 3 := add_le_add (min_le_right _ _) (min_le_right _ _)
      _ < ε := by linarith
    exact abs_lt.mp (by simpa only [Real.dist_eq] using hsb)
  have hss' : Tendsto (fun n => ss n - b) atTop (𝓝 (s₀ - b)) := hss.sub_const b
  have hssmem : ∀ᶠ n in atTop, ss n - b ∈ Ioo (-ε) ε :=
    hss'.eventually_mem (isOpen_Ioo.mem_nhds hdif)
  have hread₀ := geodesic_eq_metricParameterFlow_shift hε (hZ _ hDbc).1
    (hZ _ hDbc).2.1 (hZ _ hDbc).2.2 hγ hcγ hsrcb rfl rfl
  have hread₀' := hread₀ (s₀ - b) hdif
  simp only [sub_add_cancel] at hread₀'
  have hZconv : Tendsto (fun n => Z (Ds n) (ss n - b)) atTop (𝓝 (Z (D b) (s₀ - b))) :=
    tendsto_metricParameterFlow_eval hLip hDbc
      (fun s hs => ((hZ _ hDbc).2.1 s hs).continuousWithinAt)
      hDs hDsmem hss' (Ioo_subset_Icc_self hdif)
      (hssmem.mono fun _ hn => Ioo_subset_Icc_self hn)
  have hreads : ∀ᶠ n in atTop,
      γs n (ss n) = (extChartAt I p).symm (Z (Ds n) (ss n - b)).1 ∧
      deriv (chartReading (I := I) p (γs n)) (ss n) = (Z (Ds n) (ss n - b)).2 := by
    filter_upwards [hDsmem, hsrcs, hssmem] with n hn hsrcn hsn
    have hread := geodesic_eq_metricParameterFlow_shift hε (hZ _ hn).1
      (hZ _ hn).2.1 (hZ _ hn).2.2 (hγs n) (hcγs n) hsrcn rfl rfl (ss n - b) hsn
    simp only [sub_add_cancel] at hread
    exact ⟨hread.1, hread.2.2.2⟩
  have hpos : Tendsto (fun n => γs n (ss n)) atTop (𝓝 (γ s₀)) := by
    rw [hread₀'.1]
    have htarget := (hZ _ hDbc).2.2 _ (Ioo_subset_Icc_self hdif)
    exact (((continuousOn_extChartAt_symm p).continuousAt
      ((isOpen_extChartAt_target p).mem_nhds htarget)).tendsto.comp (continuous_fst.tendsto _ |>.comp hZconv)).congr'
        (hreads.mono fun _ hn => hn.1.symm)
  have hvel : Tendsto (fun n => deriv (chartReading (I := I) p (γs n)) (ss n))
      atTop (𝓝 (deriv (chartReading (I := I) p γ) s₀)) := by
    rw [hread₀'.2.2.2]
    exact (continuous_snd.tendsto _ |>.comp hZconv).congr' (hreads.mono fun _ hn => hn.2.symm)
  exact ⟨hpos, tendsto_geodesic_velocity_chartTransfer
    (fun n => (hγs n).hasGeodesicEquationAt (ss n)) (fun n => (hcγs n).continuousAt)
    (hγ.hasGeodesicEquationAt s₀) hcγ.continuousAt hsrc₀ (mem_chart_source H (γ s₀))
    hpos hvel⟩

/-- **Math.** Initial position and velocity convergence propagates along
global geodesics when the underlying metrics converge in a smooth family. -/
theorem geodesicMetric_dataTendsto_of_initial
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {ts : ℕ → ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ interior J) (hts : Tendsto ts atTop (𝓝 t₀))
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγ : IsGeodesic (g t₀) γ) (hcγ : Continuous γ)
    (hγs : ∀ n, IsGeodesic (g (ts n)) (γs n)) (hcγs : ∀ n, Continuous (γs n))
    (h0 : GeodesicDataTendsto (I := I) γ γs (fun _ => 0) 0)
    {ss : ℕ → ℝ} {s₀ : ℝ} (hss : Tendsto ss atTop (𝓝 s₀)) :
    GeodesicDataTendsto (I := I) γ γs ss s₀ := by
  let S : Set ℝ := {s | GeodesicDataTendsto (I := I) γ γs (fun _ => s) s}
  have hstep := exists_geodesicMetric_convergence_step hg ht₀ hts hγ hcγ hγs hcγs
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro b hb
    obtain ⟨ρ, hρ, hprop⟩ := hstep b
    refine mem_of_superset (ball_mem_nhds b hρ) ?_
    intro s hs
    exact hprop b (mem_ball_self hρ) hb hs tendsto_const_nhds
  have hcompl : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro b hb
    obtain ⟨ρ, hρ, hprop⟩ := hstep b
    refine mem_of_superset (ball_mem_nhds b hρ) ?_
    intro s hs hgood
    exact hb (hprop s hs hgood (mem_ball_self hρ) tendsto_const_nhds)
  have hall : S = univ := (show IsClopen S from
    ⟨isOpen_compl_iff.mp hcompl, hopen⟩).eq_univ ⟨0, h0⟩
  have hs₀ : s₀ ∈ S := hall ▸ mem_univ s₀
  obtain ⟨ρ, hρ, hprop⟩ := hstep s₀
  exact hprop s₀ (mem_ball_self hρ) hs₀ (mem_ball_self hρ) hss

end MorganTianLib
