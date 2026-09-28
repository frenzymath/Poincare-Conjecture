import MorganTianLib.Ch04.ScalarMinimumFlow

/-!
# Morgan--Tian Ch. 4 - one-sided scalar-minimum derivative bridge

The scalar minimum estimate is naturally a lower forward-Dini statement at
the initial endpoint.  This file records the elementary conversion to an
ordinary one-sided derivative when that derivative exists, with the domain
`Ici t` made explicit.
-/

open Filter Set
open scoped Topology

noncomputable section

namespace MorganTianLib

/-! A one-sided derivative cannot be replaced by an unrestricted derivative at
an endpoint.  The following lemma keeps the one-sided domain visible. -/

theorem HasDerivWithinAt.le_of_forwardDiffQuotientGE
    {f : ℝ → ℝ} {t c C : ℝ}
    (hderiv : HasDerivWithinAt f c (Ici t) t)
    (hforward : ForwardDiffQuotientGE f t C) :
    C ≤ c := by
  by_contra hnot
  have hcc : c < C := lt_of_not_ge hnot
  let r : ℝ := (c + C) / 2
  have hcr : c < r := by
    dsimp [r]
    linarith
  have hrC : r < C := by
    dsimp [r]
    linarith
  have hslope : Tendsto (slope f t) (𝓝[>] t) (𝓝 c) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).1
      hderiv.Ioi_of_Ici
  have hupper : ∀ᶠ z in 𝓝[>] t, slope f t z < r :=
    hslope (Iio_mem_nhds hcr)
  have hlower : ∀ᶠ z in 𝓝[>] t, r < slope f t z :=
    hforward r hrC
  obtain ⟨z, hzupper, hzlower⟩ := (hupper.and hlower).exists
  exact (lt_asymm hzlower hzupper)

/-! The source-facing endpoint consequence for the compact scalar minimum. -/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

variable {E H M : Type*}

theorem scalarCurvatureMinimum_rightDeriv_ge_of_isRicciFlowOn_Ico
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    {g : ℝ → RiemannianMetric I M} {T d : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hT : 0 < T)
    (hderiv : HasDerivWithinAt
      (fun s => scalarCurvatureMinimum (g s)) d (Ici 0) 0) :
    (2 / (Module.finrank ℝ E : ℝ)) *
        scalarCurvatureMinimum (g 0) ^ 2 ≤ d := by
  have hforward :=
    forwardDiffQuotientGE_scalarCurvatureMinimum_of_isRicciFlowOn_Ico
      (E := E) hflow ⟨le_rfl, hT⟩
  exact MorganTianLib.HasDerivWithinAt.le_of_forwardDiffQuotientGE hderiv hforward

end MorganTianLib

end

#print axioms MorganTianLib.HasDerivWithinAt.le_of_forwardDiffQuotientGE
#print axioms MorganTianLib.scalarCurvatureMinimum_rightDeriv_ge_of_isRicciFlowOn_Ico
