import MorganTianLib.Ch04.ScalarComparison
import MorganTianLib.Ch04.ScalarRicciTraceBridge
import MorganTianLib.Ch04.PositiveRicciScalar
import MorganTianLib.Ch03.RicciFlow.ScalarTimeDerivative

/-!
# Minimum scalar curvature along a compact Ricci flow

The compact-envelope estimate consumes the intrinsic scalar evolution equation
and joint regularity. Interior time slabs give the lower forward-Dini bound;
continuity extends monotonicity to the initial time.

Blueprint: `claim:scalar-min-forward-difference` and
`prop:scalar-curvature-min-evolution`.
-/

open Filter Set
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] in
private theorem scalarMinimumCanonicalLC (g : RiemannianMetric I M) :
    g.leviCivitaConnection.IsLeviCivita g :=
  g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)

/-- **Math.** The infimum of the intrinsic scalar curvature of a metric. On a nonempty
compact manifold this is its attained spatial minimum. -/
def scalarCurvatureMinimum (g : RiemannianMetric I M) : ℝ :=
  ⨅ p, scalarCurvatureAt g g.leviCivitaConnection (scalarMinimumCanonicalLC g) p

variable [CompactSpace M] [Nonempty M]

/-- **Math.** The minimum scalar curvature is continuous on each closed time slab of a
compact Ricci flow, including any initial endpoint. -/
theorem continuousOn_scalarCurvatureMinimum_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {a b : ℝ}
    (hflow : IsRicciFlowOn g J) (hJ : Icc a b ⊆ J) :
    ContinuousOn (fun t => scalarCurvatureMinimum (g t)) (Icc a b) :=
  continuousOn_iInf_of_compact
    ((scalarCurvature_continuousOn_of_isRicciFlowOn hflow).mono
      (Set.prod_mono Subset.rfl hJ))

/-- **Math.** The intrinsic Ricci-flow equation supplies the quadratic lower forward-Dini
bound for its compact scalar minimum on every interior time slab. -/
theorem forwardDiffQuotientGE_scalarCurvatureMinimum_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {a b t : ℝ}
    (hflow : IsRicciFlowOn g J) (hJ : Icc a b ⊆ interior J) (ht : t ∈ Ico a b) :
    ForwardDiffQuotientGE (fun s => scalarCurvatureMinimum (g s)) t
      ((2 / (Module.finrank ℝ E : ℝ)) * scalarCurvatureMinimum (g t) ^ 2) := by
  let R : M → ℝ → ℝ := fun p s => scalarCurvatureAt (g s)
    (g s).leviCivitaConnection (scalarMinimumCanonicalLC (g s)) p
  have hR := (scalarCurvature_continuousOn_of_isRicciFlowOn hflow).mono
    (Set.prod_mono Subset.rfl (hJ.trans interior_subset))
  have hR' := (scalarCurvature_timeDeriv_continuousOn_of_isRicciFlowOn hflow).mono
    (Set.prod_mono Subset.rfl hJ)
  apply forwardDiffQuotientGE_iInfOn (F := R) (F' := fun p s => deriv (R p) s)
    ht.1 ht.2 hR hR'
  · intro p s hs
    have hd :=
      hasDerivAt_scalarCurvatureAt_leviCivita_of_isRicciFlowOn_eq_laplacian_add_reaction
        hflow p (hJ ⟨ht.1.trans hs.1.le, hs.2.le⟩)
        ((extChartAt I p).map_source (mem_extChartAt_source p))
    simp only [extChartAt_to_inv] at hd
    exact hd.differentiableAt.hasDerivAt
  · intro p hp
    have hslice : Continuous (fun q => R q t) :=
      (scalarCurvatureAt_contMDiff (g t) (g t).leviCivitaConnection
        (scalarMinimumCanonicalLC (g t))).continuous
    have hmin : IsLocalMin (fun q => R q t) p := by
      apply Filter.Eventually.of_forall
      intro q
      change R p t ≤ R q t
      rw [hp]
      exact ciInf_le (isCompact_range hslice).bddBelow q
    change (2 / (Module.finrank ℝ E : ℝ)) * (⨅ q, R q t) ^ 2 ≤ deriv (R p) t
    rw [← hp]
    exact
      scalar_min_deriv_bound_of_isRicciFlowOn hflow (hJ ⟨ht.1, ht.2.le⟩) hmin

/-- **Math.** The quadratic lower forward-Dini inequality holds throughout a compact
Ricci flow's half-open time interval, including time zero. Continuity transfers
the interior inequality to the initial endpoint. -/
theorem forwardDiffQuotientGE_scalarCurvatureMinimum_of_isRicciFlowOn_Ico
    {g : ℝ → RiemannianMetric I M} {T t : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T)) (ht : t ∈ Ico 0 T) :
    ForwardDiffQuotientGE (fun s => scalarCurvatureMinimum (g s)) t
      ((2 / (Module.finrank ℝ E : ℝ)) * scalarCurvatureMinimum (g t) ^ 2) := by
  obtain ⟨b, htb, hbT⟩ := exists_between ht.2
  have hslab : Icc t b ⊆ Ico 0 T :=
    fun s hs => ⟨ht.1.trans hs.1, hs.2.trans_lt hbT⟩
  have hcont := continuousOn_scalarCurvatureMinimum_of_isRicciFlowOn hflow hslab
  apply forwardDiffQuotientGE_of_continuousOn_Ioo htb hcont
    (continuousOn_const.mul (hcont.pow 2))
  intro s hs
  apply forwardDiffQuotientGE_scalarCurvatureMinimum_of_isRicciFlowOn hflow
    (a := s) (b := b) _ ⟨le_rfl, hs.2⟩
  intro u hu
  rw [interior_Ico]
  exact ⟨(ht.1.trans_lt hs.1).trans_le hu.1, hu.2.trans_lt hbT⟩

/-- **Math.** The compact scalar minimum is nondecreasing on interior time slabs. -/
theorem monotoneOn_scalarCurvatureMinimum_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {a b : ℝ}
    (hflow : IsRicciFlowOn g J) (hJ : Icc a b ⊆ interior J) :
    MonotoneOn (fun t => scalarCurvatureMinimum (g t)) (Icc a b) := by
  apply monotoneOn_of_forwardDiffQuotientGE_nonneg
    (continuousOn_scalarCurvatureMinimum_of_isRicciFlowOn hflow
      (hJ.trans interior_subset))
  intro t ht
  exact (forwardDiffQuotientGE_scalarCurvatureMinimum_of_isRicciFlowOn hflow hJ ht).mono
    (by positivity)

/-- **Math.** On the actual half-open time interval of a compact Ricci flow, the scalar
minimum is nondecreasing from time zero. No endpoint time derivative is assumed. -/
theorem monotoneOn_scalarCurvatureMinimum_of_isRicciFlowOn_Ico
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T)) :
    MonotoneOn (fun t => scalarCurvatureMinimum (g t)) (Ico 0 T) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with rfl | hst
  · exact le_rfl
  have hpos : ∀ u ∈ Ioc 0 t, scalarCurvatureMinimum (g u) ≤
      scalarCurvatureMinimum (g t) := by
    intro u hu
    apply monotoneOn_scalarCurvatureMinimum_of_isRicciFlowOn hflow
      (a := u) (b := t) _ ⟨le_rfl, hu.2⟩ ⟨hu.2, le_rfl⟩ hu.2
    intro v hv
    rw [interior_Ico]
    exact ⟨hu.1.trans_le hv.1, hv.2.trans_lt ht.2⟩
  have h0t : 0 < t := hs.1.trans_lt hst
  have hcont := continuousOn_scalarCurvatureMinimum_of_isRicciFlowOn hflow
    (show Icc 0 t ⊆ Ico 0 T from fun u hu => ⟨hu.1, hu.2.trans_lt ht.2⟩)
  have hbound := le_on_closure hpos
    (by simpa only [closure_Ioc h0t.ne] using hcont) continuousOn_const
  exact hbound (by rw [closure_Ioc h0t.ne]; exact ⟨hs.1, hst.le⟩)

end MorganTianLib

#print axioms MorganTianLib.forwardDiffQuotientGE_scalarCurvatureMinimum_of_isRicciFlowOn
#print axioms MorganTianLib.forwardDiffQuotientGE_scalarCurvatureMinimum_of_isRicciFlowOn_Ico
#print axioms MorganTianLib.monotoneOn_scalarCurvatureMinimum_of_isRicciFlowOn_Ico
