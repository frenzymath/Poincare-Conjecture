import PetersenLib.Ch05.HopfRinowSegment
import PetersenLib.Ch05.MetricTopology

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]
  [ConnectedSpace M]

/-- The unit-speed segment on `[0, |pq|]`. -/
theorem completeManifold_exists_isSegment_unitSpeed (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] (p q : M) :
    ∃ σ : ℝ → M, IsSegment (I := I) g σ 0 (riemannianDistance (I := I) g p q) ∧
      σ 0 = p ∧ σ (riemannianDistance (I := I) g p q) = q := by
  classical
  set d : ℝ := riemannianDistance (I := I) g p q with hddef
  have hd0 : 0 ≤ d := riemannianDistance_nonneg (I := I) g p q
  rcases eq_or_lt_of_le hd0 with hd | hd
  · -- degenerate case `d = 0`, so `p = q` and the segment is the constant curve on `[0,0]`
    have hpq : p = q :=
      eq_of_riemannianDistance_eq_zero (I := I) g (hddef.symm.trans hd.symm)
    refine ⟨fun _ => p, ⟨?_, ?_, 0, le_rfl, ?_⟩, rfl, ?_⟩
    · exact isPiecewiseSmoothCurve_const (I := I) p (hd ▸ le_rfl)
    · rw [← hd]; simp
    · intro t ht
      rw [← hd, Set.Icc_self, Set.mem_singleton_iff] at ht
      subst ht; simp
    · rw [← hd]; exact hpq
  · -- nondegenerate case `0 < d`: rescale time by `1/d`
    obtain ⟨γ, hγ0, hγ1, hpw, hL, k, hk0, hk⟩ :=
      completeManifold_allPointsJoinedBySegment (I := I) g hg p q
    have hdne : d ≠ 0 := hd.ne'
    have hc : 0 < d⁻¹ := inv_pos.mpr hd
    -- the constant speed of the `[0,1]` segment is exactly `|pq|`
    have hkd : k = d := by
      have h1 := hk 1 (right_mem_Icc.mpr zero_le_one)
      rw [hL, hγ0, hγ1] at h1
      rw [← hddef] at h1
      simpa using h1.symm
    refine ⟨fun t => γ (d⁻¹ * t + 0), ⟨?_, ?_, 1, zero_le_one, ?_⟩, ?_, ?_⟩
    · refine isPiecewiseSmoothCurve_comp_mul_add (I := I) hc ?_
      simpa [inv_mul_cancel₀ hdne] using hpw
    · rw [curveLength_comp_mul_add (I := I) g γ hc.le 0 0 d]
      simp only [mul_zero, add_zero, inv_mul_cancel₀ hdne]
      rw [hL]
    · intro t ht
      rw [curveLength_comp_mul_add (I := I) g γ hc.le 0 0 t]
      simp only [mul_zero, add_zero]
      have hmem : d⁻¹ * t ∈ Icc (0 : ℝ) 1 := by
        refine ⟨mul_nonneg hc.le ht.1, ?_⟩
        have h := mul_le_mul_of_nonneg_left ht.2 hc.le
        rwa [inv_mul_cancel₀ hdne] at h
      rw [hk (d⁻¹ * t) hmem, hkd]
      field_simp
      ring
    · simp [hγ0]
    · simp only [add_zero, inv_mul_cancel₀ hdne]
      exact hγ1

open Classical in
/-- `segmentNotation` is meaningful on a complete manifold. -/
theorem segmentNotation_spec (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p q : M) :
    IsSegment (I := I) g (segmentNotation (I := I) g p q) 0
        (riemannianDistance (I := I) g p q) ∧
      segmentNotation (I := I) g p q 0 = p ∧
      segmentNotation (I := I) g p q (riemannianDistance (I := I) g p q) = q := by
  classical
  have h := completeManifold_exists_isSegment_unitSpeed (I := I) g hg p q
  rw [segmentNotation, dif_pos h]
  exact h.choose_spec

/-- Any segment on `[0, |pq|]` from `p` to `q` is UNIT speed: the constant `k` is forced to `1`. -/
theorem IsSegment.curveLength_eq_self_of_domain (g : RiemannianMetric I M) {σ : ℝ → M}
    {p q : M} (hσ : IsSegment (I := I) g σ 0 (riemannianDistance (I := I) g p q))
    (h0 : σ 0 = p) (hd : σ (riemannianDistance (I := I) g p q) = q)
    (hne : p ≠ q) :
    ∀ t ∈ Icc 0 (riemannianDistance (I := I) g p q),
      curveLength (I := I) g σ 0 t = t := by
  obtain ⟨-, hL, k, hk0, hk⟩ := hσ
  set d : ℝ := riemannianDistance (I := I) g p q with hddef
  have hd0 : d ≠ 0 := fun h =>
    hne (eq_of_riemannianDistance_eq_zero (I := I) g (hddef ▸ h))
  have hkone : k = 1 := by
    have h1 := hk d (right_mem_Icc.mpr (riemannianDistance_nonneg (I := I) g p q))
    rw [hL, h0, hd, ← hddef, sub_zero] at h1
    have h2 : k * d = 1 * d := by rw [one_mul, ← h1]
    exact mul_right_cancel₀ hd0 h2
  intro t ht
  rw [hk t ht, hkone]
  ring

end PetersenLib
