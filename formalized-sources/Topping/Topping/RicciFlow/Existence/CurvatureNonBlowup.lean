import Topping.RicciFlow.Existence.CurvatureTailAssembly

/-!
# The non-blow-up curvature consumer

This module closes the order/filter part of the first finite-time extension
step.  Failure of curvature blow-up supplies an anchor arbitrarily close to the
endpoint; the anchored maximum-principle comparison controls a short tail, and
compactness controls the remaining prefix.  The intrinsic space-time
continuity and the Ricci-flow predicate are intentionally explicit inputs.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Filter Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [Nonempty M] [CompactSpace M]

/-- **Math.** On a compact manifold, failure of finite-time curvature blow-up
and a supplied jointly continuous squared curvature norm yield a uniform
pointwise curvature bound before the endpoint.  This is the precise
non-blow-up consumer used by the extension argument; endpoint regularity and
the restart theorem remain separate hypotheses/conclusions.
-/
theorem hasUniformCurvatureBoundBefore_of_not_curvatureBlowsUpAt
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (hnot : ¬ CurvatureBlowsUpAt g T)
    (hcont : ContinuousOn
      (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
      ((Set.univ : Set M) ×ˢ Ico (0 : ℝ) T))
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico (0 : ℝ) T)) :
    HasUniformCurvatureBoundBefore g T := by
  obtain ⟨c, hc, htail⟩ :=
    exists_uniform_curvature_bound_on_Ico_of_anchored_comparison
      (I := I) (M := M)
  obtain ⟨Csup, hCsup, hchoose⟩ :=
    exists_curvatureSup_le_in_nhdsWithin_of_not_curvatureBlowsUpAt
      (g := g) (T := T) hT hnot
  let m : ℝ := max Csup 1
  have hm : 0 < m := by
    dsimp [m]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCm : Csup ≤ m := le_max_left _ _
  let q : ℝ := c * m
  have hq : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg hc (le_of_lt hm)
  have hq1 : 0 < q + 1 := by linarith
  let δ : ℝ := 1 / (q + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact one_div_pos.mpr hq1
  let U : Set ℝ := Ioo (T - δ) (T + 1)
  have hU_nhds : U ∈ 𝓝 T := by
    dsimp [U]
    apply Ioo_mem_nhds
    · linarith
    · linarith
  have hU : U ∈ 𝓝[Iio T] T := by
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨U, hU_nhds, ?_⟩
    exact inter_subset_left
  obtain ⟨a, ha, haCurv⟩ := hchoose U hU
  have haU : a ∈ U := ha.1
  have haIoo : a ∈ Ioo (0 : ℝ) T := ha.2
  have ha0 : 0 < a := haIoo.1
  have haT : a < T := haIoo.2
  have hdelta : T - a < δ := by
    linarith [haU.1]
  have hratio : q / (q + 1) < 1 := by
    apply (div_lt_iff₀ hq1).2
    linarith
  have hhalf : q * (1 / (q + 1)) / 2 < 1 := by
    have hrewrite : q * (1 / (q + 1)) = q / (q + 1) := by
      ring
    rw [hrewrite]
    nlinarith
  have hglobal : q * (T - a) / 2 < 1 := by
    have hmul : q * (T - a) ≤ q * (1 / (q + 1)) := by
      exact mul_le_mul_of_nonneg_left (le_of_lt (by simpa [δ] using hdelta)) hq
    exact lt_of_le_of_lt (by
      exact div_le_div_of_nonneg_right hmul (by norm_num)) hhalf
  have hdenom : ∀ t ∈ Icc a T, 0 < 1 - c * m * (t - a) / 2 := by
    intro t ht
    have hta : t - a ≤ T - a := by linarith [ht.2]
    have hmul : q * (t - a) / 2 ≤ q * (T - a) / 2 := by
      have hmul' := mul_le_mul_of_nonneg_left hta hq
      exact div_le_div_of_nonneg_right hmul' (by norm_num)
    have hlt : q * (t - a) / 2 < 1 := hmul.trans_lt hglobal
    dsimp [q] at hlt
    linarith
  have hanchor : ∀ p : M, riemannNormAt (g a) p ≤ m := by
    intro p
    have hp := pointwise_le_of_curvatureSup_le
      (bddAbove_range_riemannNormAt (g a)) haCurv p
    exact hp.trans hCm
  obtain ⟨C₁, hC₁, htailbound⟩ :=
    htail g T a m ha0 haT hm hcont hflow hdenom hanchor
  have hcont_prefix_sq : ContinuousOn
      (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
      ((Set.univ : Set M) ×ˢ Icc (0 : ℝ) a) := by
    apply hcont.mono
    exact Set.prod_mono subset_rfl (by
      intro t ht
      exact ⟨ht.1, lt_of_le_of_lt ht.2 haT⟩)
  have hcont_prefix : ContinuousOn
      (fun z : M × ℝ => riemannNormAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc (0 : ℝ) a) := by
    have hsqrt := hcont_prefix_sq.sqrt
    convert hsqrt using 1
    funext z
    exact (Real.sqrt_sq (riemannNormAt_nonneg (g z.2) z.1)).symm
  obtain ⟨C₀, hC₀, hprefix⟩ :=
    exists_uniform_curvature_bound_on_Icc_of_continuous
      (I := I) (M := M) (g := g) (a := a) hcont_prefix
  exact hasUniformCurvatureBoundBefore_of_prefix_and_tail
    hC₀ hC₁ hprefix htailbound

#print axioms hasUniformCurvatureBoundBefore_of_not_curvatureBlowsUpAt

/-- **Math.** The non-blow-up consumer specialized to a smooth metric family;
the joint squared-curvature continuity is supplied by the intrinsic spacetime
regularity bridge on the same half-open time interval. -/
theorem hasUniformCurvatureBoundBefore_of_not_curvatureBlowsUpAt_of_isSmoothMetricFamilyOn
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (hnot : ¬ CurvatureBlowsUpAt g T)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico (0 : ℝ) T))
    :
    HasUniformCurvatureBoundBefore g T := by
  exact hasUniformCurvatureBoundBefore_of_not_curvatureBlowsUpAt
    hT hnot
    (continuousOn_riemannNormAt_sq_of_isSmoothMetricFamilyOn hflow.smooth)
    hflow

end Topping

end
