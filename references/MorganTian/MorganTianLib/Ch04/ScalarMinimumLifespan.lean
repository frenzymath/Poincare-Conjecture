import MorganTianLib.Ch04.ScalarMinimumFlow

/-!
# Lifespan bound from positive scalar curvature

The intrinsic scalar minimum of a compact Ricci flow satisfies the quadratic
lower-Dini inequality on interior time slabs. Applying the scalar comparison
from each positive initial time and letting that time tend to zero bounds the
half-open flow interval by the pole time. Positive Ricci curvature supplies a
strictly positive initial scalar minimum by compact attainment.
-/

open Filter Set
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M]

/-- **Math.** A compact Ricci flow whose initial scalar curvature is bounded
below by a positive constant cannot exist past the scalar comparison pole. -/
theorem lifespan_le_of_isRicciFlowOn_of_scalarCurvatureMinimum_pos
    {g : ℝ → RiemannianMetric I M} {T c : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T)) (hT : 0 < T)
    (hc : 0 < c) (hinit : c ≤ scalarCurvatureMinimum (g 0)) :
    T ≤ (Module.finrank ℝ E : ℝ) / (2 * c) := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hbound : ∀ a ∈ Ioo 0 T,
      T ≤ a + (Module.finrank ℝ E : ℝ) / (2 * c) := by
    intro a ha
    have hcont : ContinuousOn (fun t => scalarCurvatureMinimum (g t))
        (Ico a T) := by
      intro t ht
      have htb : t < (t + T) / 2 := by linarith [ht.2]
      have hbT : (t + T) / 2 < T := by linarith [ht.2]
      have hs := continuousOn_scalarCurvatureMinimum_of_isRicciFlowOn hflow
        (show Icc 0 ((t + T) / 2) ⊆ Ico 0 T from
          fun s hs => ⟨hs.1, hs.2.trans_lt hbT⟩)
      exact (hs.continuousAt (Icc_mem_nhds (ha.1.trans_le ht.1) htb)).continuousWithinAt
    have hfd : ∀ t ∈ Ico a T,
        ForwardDiffQuotientGE (fun s => scalarCurvatureMinimum (g s)) t
          ((2 / (Module.finrank ℝ E : ℝ)) * scalarCurvatureMinimum (g t) ^ 2) := by
      intro t ht
      apply forwardDiffQuotientGE_scalarCurvatureMinimum_of_isRicciFlowOn
        hflow (a := a) (b := (t + T) / 2)
      · intro s hs
        rw [interior_Ico]
        constructor <;> linarith [ha.1, ht.2, hs.1, hs.2]
      · exact ⟨ht.1, by linarith [ht.2]⟩
    have hinitA : c ≤ scalarCurvatureMinimum (g a) :=
      hinit.trans (monotoneOn_scalarCurvatureMinimum_of_isRicciFlowOn_Ico hflow
        ⟨le_rfl, hT⟩ ⟨ha.1.le, ha.2⟩ ha.1.le)
    have h := endpoint_le_of_forwardDiffQuotientGE_quadratic_Ico hcont hfd
      hinitA hc (by positivity)
    have hinv : 1 / ((2 / (Module.finrank ℝ E : ℝ)) * c) =
        (Module.finrank ℝ E : ℝ) / (2 * c) := by
      field_simp
    simpa only [hinv] using h
  have hzero := le_on_closure hbound continuousOn_const
    (show ContinuousOn (fun a : ℝ => a + (Module.finrank ℝ E : ℝ) / (2 * c))
      (closure (Ioo 0 T)) from by fun_prop)
    (show (0 : ℝ) ∈ closure (Ioo 0 T) by
      rw [closure_Ioo hT.ne]
      exact ⟨le_rfl, hT.le⟩)
  simpa only [zero_add] using hzero

/-- **Math.** Positive Ricci curvature gives a strictly positive scalar
minimum on a nonempty compact manifold. -/
theorem scalarCurvatureMinimum_pos_of_ricciTensorAt_pos
    (g : RiemannianMetric I M)
    (hRic : ∀ p, ∀ v : TangentSpace I p, v ≠ 0 →
      0 < ricciTensorAt g p v v) :
    0 < scalarCurvatureMinimum g := by
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have hcont := (scalarCurvatureAt_contMDiff g g.leviCivitaConnection hLC).continuous
  obtain ⟨p, hp⟩ := exists_eq_iInf_of_continuous hcont
  change 0 < ⨅ q, scalarCurvatureAt g g.leviCivitaConnection hLC q
  rw [← hp]
  exact scalarCurvatureAt_pos_of_ricciTensorAt_pos g p hLC (hRic p)

/-- **Math.** An initially positive-Ricci compact Ricci flow has its half-open
time interval bounded by the pole determined by its initial scalar minimum. -/
theorem lifespan_le_of_isRicciFlowOn_of_ricciTensorAt_pos
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T)) (hT : 0 < T)
    (hRic : ∀ p, ∀ v : TangentSpace I p, v ≠ 0 →
      0 < ricciTensorAt (g 0) p v v) :
    T ≤ (Module.finrank ℝ E : ℝ) / (2 * scalarCurvatureMinimum (g 0)) :=
  lifespan_le_of_isRicciFlowOn_of_scalarCurvatureMinimum_pos hflow hT
    (scalarCurvatureMinimum_pos_of_ricciTensorAt_pos (g 0) hRic) le_rfl

/-! The dimension-three specialization is the form used by the corrected
Hamilton roundness theorem. -/

/-- **Math.** In dimension three, positive initial Ricci curvature bounds the
maximal half-open flow interval by `3 / (2 R_min(0))`. -/
theorem lifespan_le_three_div_two_of_isRicciFlowOn_of_ricciTensorAt_pos
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T)) (hT : 0 < T)
    (hdim : Module.finrank ℝ E = 3)
    (hRic : ∀ p, ∀ v : TangentSpace I p, v ≠ 0 →
      0 < ricciTensorAt (g 0) p v v) :
    T ≤ 3 / (2 * scalarCurvatureMinimum (g 0)) := by
  have h := lifespan_le_of_isRicciFlowOn_of_ricciTensorAt_pos hflow hT hRic
  rw [hdim] at h
  exact h

end MorganTianLib

#print axioms MorganTianLib.lifespan_le_of_isRicciFlowOn_of_scalarCurvatureMinimum_pos
#print axioms MorganTianLib.scalarCurvatureMinimum_pos_of_ricciTensorAt_pos
#print axioms MorganTianLib.lifespan_le_of_isRicciFlowOn_of_ricciTensorAt_pos
#print axioms MorganTianLib.lifespan_le_three_div_two_of_isRicciFlowOn_of_ricciTensorAt_pos
