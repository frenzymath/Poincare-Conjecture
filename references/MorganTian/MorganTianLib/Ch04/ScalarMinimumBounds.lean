import MorganTianLib.Ch04.ScalarMinimumLifespan
import MorganTianLib.Ch03.RicciFlow.MetricDistortion

/-!
# Rational scalar-curvature bounds along compact Ricci flows

The intrinsic scalar minimum satisfies the quadratic lower-Dini inequality,
including the initial time. The scalar comparison theorem therefore gives
both rational bounds in Morgan--Tian Chapter 4,
`prop:scalar-curvature-min-evolution`, on the actual half-open flow interval.
The positive branch uses the proved lifespan estimate to stay before its pole.
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

omit [Nonempty M] in
/-- **Math.** The compact scalar minimum is bounded above by the scalar
curvature at every point. -/
theorem scalarCurvatureMinimum_le_scalarCurvatureAt
    (g : RiemannianMetric I M)
    (hLC : g.leviCivitaConnection.IsLeviCivita g) (p : M) :
    scalarCurvatureMinimum g ≤ scalarCurvatureAt g g.leviCivitaConnection hLC p := by
  unfold scalarCurvatureMinimum
  exact ciInf_le (isCompact_range
    (scalarCurvatureAt_contMDiff g g.leviCivitaConnection hLC).continuous).bddBelow p

/-- **Math.** A uniform pointwise lower scalar-curvature bound is equivalent
to the same bound on the compact scalar minimum. -/
theorem le_scalarCurvatureMinimum_iff
    (g : RiemannianMetric I M)
    (hLC : g.leviCivitaConnection.IsLeviCivita g) {c : ℝ} :
    c ≤ scalarCurvatureMinimum g ↔
      ∀ p, c ≤ scalarCurvatureAt g g.leviCivitaConnection hLC p := by
  constructor
  · intro hc p
    exact hc.trans (scalarCurvatureMinimum_le_scalarCurvatureAt g hLC p)
  · intro hc
    exact le_ciInf hc

/-- **Math.** Strict positivity of scalar curvature on a nonempty compact
manifold is equivalent to strict positivity of its attained scalar minimum. -/
theorem scalarCurvatureMinimum_pos_iff
    (g : RiemannianMetric I M)
    (hLC : g.leviCivitaConnection.IsLeviCivita g) :
    0 < scalarCurvatureMinimum g ↔
      ∀ p, 0 < scalarCurvatureAt g g.leviCivitaConnection hLC p := by
  constructor
  · intro hpos p
    exact hpos.trans_le (scalarCurvatureMinimum_le_scalarCurvatureAt g hLC p)
  · intro hpos
    obtain ⟨p, hp⟩ := exists_eq_iInf_of_continuous
      (scalarCurvatureAt_contMDiff g g.leviCivitaConnection hLC).continuous
    change 0 < ⨅ q, scalarCurvatureAt g g.leviCivitaConnection hLC q
    rw [← hp]
    exact hpos p

/-- **Math.** An initial lower bound for the scalar curvature of a compact
Ricci flow evolves by the rational quadratic barrier wherever its denominator
is positive. -/
theorem scalarCurvatureMinimum_rational_lower_bound_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {T c t : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T)) (ht : t ∈ Ico 0 T)
    (hinit : c ≤ scalarCurvatureMinimum (g 0))
    (hden : 0 < 1 - (2 / (Module.finrank ℝ E : ℝ)) * c * t) :
    c / (1 - (2 / (Module.finrank ℝ E : ℝ)) * c * t) ≤
      scalarCurvatureMinimum (g t) := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hbound := quadratic_lower_bound_of_forwardDiffQuotientGE
    (continuousOn_scalarCurvatureMinimum_of_isRicciFlowOn hflow
      (show Icc 0 t ⊆ Ico 0 T from fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩))
    (fun s hs => forwardDiffQuotientGE_scalarCurvatureMinimum_of_isRicciFlowOn_Ico
      hflow ⟨hs.1, hs.2.trans_le ht.2.le⟩) hinit
    (show ∀ s ∈ Icc 0 t,
        0 < 1 - (2 / (Module.finrank ℝ E : ℝ)) * c * (s - 0) from by
      intro s hs
      simp only [sub_zero]
      rcases le_total 0 c with hc | hc
      · have hcoef : 0 ≤ (2 / (Module.finrank ℝ E : ℝ)) * c := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hs.2 hcoef]
      · have hprod : (2 / (Module.finrank ℝ E : ℝ)) * c * s ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (by positivity) hc) hs.1
        linarith)
  simpa only [sub_zero] using hbound t ⟨ht.1, le_rfl⟩

/-- **Math.** A compact Ricci flow with a positive initial scalar lower bound
remains strictly before the pole of its scalar comparison barrier. -/
theorem scalarCurvatureMinimum_barrier_denominator_pos_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {T c t : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T)) (ht : t ∈ Ico 0 T)
    (hc : 0 < c) (hinit : c ≤ scalarCurvatureMinimum (g 0)) :
    0 < 1 - (2 / (Module.finrank ℝ E : ℝ)) * c * t := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have htp := ht.2.trans_le
    (lifespan_le_of_isRicciFlowOn_of_scalarCurvatureMinimum_pos
      hflow (ht.1.trans_lt ht.2) hc hinit)
  have hpole : (Module.finrank ℝ E : ℝ) / (2 * c) =
      1 / ((2 / (Module.finrank ℝ E : ℝ)) * c) := by field_simp
  rw [hpole] at htp
  have hmul := (lt_div_iff₀ (show
    0 < (2 / (Module.finrank ℝ E : ℝ)) * c by positivity)).mp htp
  nlinarith

/-- **Math.** A positive initial lower scalar-curvature bound gives the
rational lower bound at every time of the compact Ricci flow. Its lifespan
estimate makes the denominator positive automatically. -/
theorem scalarCurvatureMinimum_positive_lower_bound_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {T c t : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T)) (ht : t ∈ Ico 0 T)
    (hc : 0 < c) (hinit : c ≤ scalarCurvatureMinimum (g 0)) :
    c / (1 - (2 / (Module.finrank ℝ E : ℝ)) * c * t) ≤
      scalarCurvatureMinimum (g t) :=
  scalarCurvatureMinimum_rational_lower_bound_of_isRicciFlowOn hflow ht hinit
    (scalarCurvatureMinimum_barrier_denominator_pos_of_isRicciFlowOn hflow ht hc hinit)

/-- **Math.** The nonnegative branch includes zero initial curvature, where
the rational bound is scalar nonnegativity and has no finite pole. -/
theorem scalarCurvatureMinimum_nonnegative_lower_bound_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {T c t : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T)) (ht : t ∈ Ico 0 T)
    (hc : 0 ≤ c) (hinit : c ≤ scalarCurvatureMinimum (g 0)) :
    c / (1 - (2 / (Module.finrank ℝ E : ℝ)) * c * t) ≤
      scalarCurvatureMinimum (g t) := by
  rcases hc.eq_or_lt with rfl | hc
  · exact scalarCurvatureMinimum_rational_lower_bound_of_isRicciFlowOn
      hflow ht hinit (by norm_num)
  · exact scalarCurvatureMinimum_positive_lower_bound_of_isRicciFlowOn hflow ht hc hinit

/-- **Math.** A nonpositive initial lower scalar-curvature bound gives the
negative rational barrier on the whole compact Ricci-flow interval. -/
theorem scalarCurvatureMinimum_negative_lower_bound_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {T c t : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T)) (ht : t ∈ Ico 0 T)
    (hc : c ≤ 0) (hinit : c ≤ scalarCurvatureMinimum (g 0)) :
    -(Module.finrank ℝ E : ℝ) * |c| /
        (2 * t * |c| + (Module.finrank ℝ E : ℝ)) ≤
      scalarCurvatureMinimum (g t) := by
  have hn : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  have hprod : (2 / (Module.finrank ℝ E : ℝ)) * c * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hc) ht.1
  have hbound := scalarCurvatureMinimum_rational_lower_bound_of_isRicciFlowOn
    hflow ht hinit (by linarith : 0 < 1 - (2 / (Module.finrank ℝ E : ℝ)) * c * t)
  have hform : c / (1 - (2 / (Module.finrank ℝ E : ℝ)) * c * t) =
      -(Module.finrank ℝ E : ℝ) * |c| /
        (2 * t * |c| + (Module.finrank ℝ E : ℝ)) := by
    rw [abs_of_nonpos hc]
    field_simp
    ring
  rwa [hform] at hbound

/-- **Math.** Nonnegative initial scalar curvature is preserved at every
point and every time of a compact Ricci flow. -/
theorem scalarCurvatureAt_nonneg_of_initial_nonneg_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hinit : ∀ p, 0 ≤ scalarCurvatureAt (g 0) (g 0).leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita (g 0)) p)
    {t : ℝ} (ht : t ∈ Ico 0 T) (p : M) :
    0 ≤ scalarCurvatureAt (g t) (g t).leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita (g t)) p := by
  have hmin := (le_scalarCurvatureMinimum_iff (g 0)
    (canonicalLeviCivita_isLeviCivita (g 0))).mpr hinit
  have hbound := scalarCurvatureMinimum_nonnegative_lower_bound_of_isRicciFlowOn
    hflow ht le_rfl hmin
  have hnonneg : 0 ≤ scalarCurvatureMinimum (g t) := by simpa using hbound
  exact hnonneg.trans (scalarCurvatureMinimum_le_scalarCurvatureAt (g t)
    (canonicalLeviCivita_isLeviCivita (g t)) p)

/-- **Math.** Strictly positive initial scalar curvature is preserved at
every point and every time of a compact Ricci flow. Compact attainment supplies
a positive initial scalar minimum, whose rational lower barrier stays positive. -/
theorem scalarCurvatureAt_pos_of_initial_pos_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hinit : ∀ p, 0 < scalarCurvatureAt (g 0) (g 0).leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita (g 0)) p)
    {t : ℝ} (ht : t ∈ Ico 0 T) (p : M) :
    0 < scalarCurvatureAt (g t) (g t).leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita (g t)) p := by
  have hmin := (scalarCurvatureMinimum_pos_iff (g 0)
    (canonicalLeviCivita_isLeviCivita (g 0))).mpr hinit
  have hbound := scalarCurvatureMinimum_positive_lower_bound_of_isRicciFlowOn
    hflow ht hmin le_rfl
  have hden := scalarCurvatureMinimum_barrier_denominator_pos_of_isRicciFlowOn
    hflow ht hmin le_rfl
  exact ((div_pos hmin hden).trans_le hbound).trans_le
    (scalarCurvatureMinimum_le_scalarCurvatureAt (g t)
      (canonicalLeviCivita_isLeviCivita (g t)) p)

end MorganTianLib

#print axioms MorganTianLib.scalarCurvatureMinimum_nonnegative_lower_bound_of_isRicciFlowOn
#print axioms MorganTianLib.scalarCurvatureMinimum_negative_lower_bound_of_isRicciFlowOn
#print axioms MorganTianLib.scalarCurvatureAt_nonneg_of_initial_nonneg_of_isRicciFlowOn
#print axioms MorganTianLib.scalarCurvatureAt_pos_of_initial_pos_of_isRicciFlowOn
