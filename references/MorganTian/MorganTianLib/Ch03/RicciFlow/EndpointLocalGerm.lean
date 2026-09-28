import MorganTianLib.Ch03.RicciFlow.SmoothPatching

/-!
# Local smooth germs for an endpoint restart

The endpoint bootstrap is local in space: at each point of the joining slice,
the two coefficient families are represented by one smooth section germ.  This
file records that producer explicitly and proves that the resulting patched
horizontal metric is jointly smooth on the whole restarted interval.  The
germ is analytic input, not a disguised `IsSmoothMetricFamilyOn` conclusion.

The final lemma is the scalar jet consequence used by coefficient bootstraps:
an actually smooth extension has every one-sided limit needed by a restart.
-/

open scoped ContDiff ContMDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Filter Set Riemannian

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-!
**Math.** The type of horizontal metric sections over the ambient product.
-/
abbrev MetricSection :=
  (z : M × ℝ) →
    TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (fun q : M × ℝ =>
        HorizontalTangentSpace I M q →L[ℝ]
          HorizontalTangentSpace I M q →L[ℝ] ℝ)

/--
**Math.** A local smooth endpoint germ consists of smooth left and right
families together with one smooth ambient section germ at every spatial point
of the joining slice.  The germ is required to agree with the *patched*
section, so it contains the full spatial and temporal compatibility needed for
joint smoothness.
-/
structure LocalSmoothEndpointGerm
    {a b c : ℝ} (gLeft gRight : ℝ → RiemannianMetric I M) where
  left_smooth : IsSmoothMetricFamilyOn gLeft (Ico a b)
  right_smooth : IsSmoothMetricFamilyOn gRight (Ico b c)
  join_germ :
    ∀ p : M, ∃ F : MetricSection (I := I) (M := M),
      ContMDiffAt (I.prod 𝓘(ℝ, ℝ))
        ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
        ∞ F (p, b) ∧
      F =ᶠ[𝓝 (p, b)]
        horizontalMetricSection (patchedMetricFamily b gLeft gRight)

private theorem product_Ico_eq_near_left
    {a b c t : ℝ} (hbc : b < c) (ht : t < b) (p : M) :
    (Set.univ : Set M) ×ˢ Ico a b =ᶠ[𝓝 (p, t)]
      (Set.univ : Set M) ×ˢ Ico a c := by
  have htime : (Prod.snd ⁻¹' Iio b) ∈ 𝓝 (p, t) :=
    continuousAt_snd.preimage_mem_nhds (Iio_mem_nhds ht)
  filter_upwards [htime] with z hz
  rcases z with ⟨q, s⟩
  change s < b at hz
  have hsb : s < b := hz
  apply propext
  change (q ∈ (Set.univ : Set M) ∧ s ∈ Ico a b) ↔
    (q ∈ (Set.univ : Set M) ∧ s ∈ Ico a c)
  constructor
  · intro hs
    exact ⟨hs.1, hs.2.1, lt_trans hs.2.2 hbc⟩
  · intro hs
    exact ⟨hs.1, hs.2.1, hsb⟩

private theorem product_Ico_eq_near_right
    {a b c t : ℝ} (hab : a < b) (ht : b < t) (p : M) :
    (Set.univ : Set M) ×ˢ Ico b c =ᶠ[𝓝 (p, t)]
      (Set.univ : Set M) ×ˢ Ico a c := by
  have htime : (Prod.snd ⁻¹' Ioi b) ∈ 𝓝 (p, t) :=
    continuousAt_snd.preimage_mem_nhds (Ioi_mem_nhds ht)
  filter_upwards [htime] with z hz
  rcases z with ⟨q, s⟩
  change b < s at hz
  have hbs : b < s := hz
  apply propext
  change (q ∈ (Set.univ : Set M) ∧ s ∈ Ico b c) ↔
    (q ∈ (Set.univ : Set M) ∧ s ∈ Ico a c)
  constructor
  · intro hs
    exact ⟨hs.1, le_trans (le_of_lt hab) hs.2.1, hs.2.2⟩
  · intro hs
    exact ⟨hs.1, le_of_lt hbs, hs.2.2⟩

private theorem patchedSection_eq_left_near
    {a b c t : ℝ} (ht : t < b) (p : M)
    (gLeft gRight : ℝ → RiemannianMetric I M) :
    horizontalMetricSection (patchedMetricFamily b gLeft gRight) =ᶠ[𝓝 (p, t)]
      horizontalMetricSection gLeft := by
  have htime : (Prod.snd ⁻¹' Iio b) ∈ 𝓝 (p, t) :=
    continuousAt_snd.preimage_mem_nhds (Iio_mem_nhds ht)
  filter_upwards [htime] with z hz
  change z.2 < b at hz
  simp only [horizontalMetricSection, patchedMetricFamily, if_pos hz]

private theorem patchedSection_eq_right_near
    {a b c t : ℝ} (ht : b < t) (p : M)
    (gLeft gRight : ℝ → RiemannianMetric I M) :
    horizontalMetricSection (patchedMetricFamily b gLeft gRight) =ᶠ[𝓝 (p, t)]
      horizontalMetricSection gRight := by
  have htime : (Prod.snd ⁻¹' Ioi b) ∈ 𝓝 (p, t) :=
    continuousAt_snd.preimage_mem_nhds (Ioi_mem_nhds ht)
  filter_upwards [htime] with z hz
  change b < z.2 at hz
  simp only [horizontalMetricSection, patchedMetricFamily,
    if_neg (not_lt.mpr hz.le)]

/--
**Math.** Local smooth endpoint germs produce a jointly smooth patched metric
family.  The proof is pointwise: away from the join it changes only the time
set and uses side smoothness; at the join it changes the patched section to the
supplied smooth germ by `ContMDiffAt.congr_of_eventuallyEq`.
-/
theorem smoothMetricFamilyOn_patchedMetricFamily_of_local_germ
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {gLeft gRight : ℝ → RiemannianMetric I M}
    (h : LocalSmoothEndpointGerm (I := I) (a := a) (b := b) (c := c)
      gLeft gRight) :
    IsSmoothMetricFamilyOn
      (patchedMetricFamily b gLeft gRight) (Ico a c) := by
  intro z hz
  rcases z with ⟨p, t⟩
  rcases hz with ⟨_, ht⟩
  rcases lt_trichotomy t b with htb | htb | hbt
  · have hleft := h.left_smooth (p, t) ⟨Set.mem_univ _, ht.1, htb⟩
    have hset := product_Ico_eq_near_left (a := a) (b := b) (c := c)
      hbc htb p
    have hleft' := hleft.congr_set hset
    have heq := patchedSection_eq_left_near (a := a) (b := b) (c := c)
      htb p gLeft gRight
    exact hleft'.congr_of_eventuallyEq_of_mem
      (heq.filter_mono nhdsWithin_le_nhds) ⟨Set.mem_univ _, ht⟩
  · subst t
    obtain ⟨F, hF, hFgerm⟩ := h.join_germ p
    have hF' := hF.contMDiffWithinAt
      (s := (Set.univ : Set M) ×ˢ Ico a c)
    exact hF'.congr_of_eventuallyEq_of_mem
      (hFgerm.symm.filter_mono nhdsWithin_le_nhds)
      ⟨Set.mem_univ _, hab.le, hbc⟩
  · have hright := h.right_smooth (p, t) ⟨Set.mem_univ _, hbt.le, ht.2⟩
    have hset := product_Ico_eq_near_right (a := a) (b := b) (c := c)
      hab hbt p
    have hright' := hright.congr_set hset
    have heq := patchedSection_eq_right_near (a := a) (b := b) (c := c)
      hbt p gLeft gRight
    exact hright'.congr_of_eventuallyEq_of_mem
      (heq.filter_mono nhdsWithin_le_nhds) ⟨Set.mem_univ _, ht⟩

/--
**Math.** A smooth scalar germ has a one-sided endpoint limit for every ordinary
derivative order.  This is the coefficient-level jet fact used when a Ricci
equation bootstraps endpoint smoothness.
-/
theorem tendsto_iteratedDeriv_of_contDiffAt
    {a b : ℝ} (_hab : a < b) {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ (n : ℕ∞) f b) :
    Tendsto (fun t => iteratedDeriv n f t)
      (𝓝[Ioo a b] b) (𝓝 (iteratedDeriv n f b)) := by
  have hF : ContinuousAt (iteratedFDeriv ℝ n f) b :=
    hf.continuousAt_iteratedFDeriv (k := n) (by simp)
  have hev : ContinuousAt
      (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℝ =>
        L (fun _ => (1 : ℝ))) (iteratedFDeriv ℝ n f b) :=
    (ContinuousEvalConst.continuous_eval_const (fun _ : Fin n => (1 : ℝ))).continuousAt
  have hc : ContinuousAt (fun t =>
      (iteratedFDeriv ℝ n f t) (fun _ : Fin n => (1 : ℝ))) b := by
    convert hev.comp hF using 1
    funext t
    rfl
  have hEq : (fun t => iteratedDeriv n f t) =
      (fun t => (iteratedFDeriv ℝ n f t) (fun _ : Fin n => (1 : ℝ))) := by
    funext t
    exact iteratedDeriv_eq_iteratedFDeriv
  rw [hEq]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

#print axioms smoothMetricFamilyOn_patchedMetricFamily_of_local_germ
#print axioms tendsto_iteratedDeriv_of_contDiffAt

end MorganTianLib

end
