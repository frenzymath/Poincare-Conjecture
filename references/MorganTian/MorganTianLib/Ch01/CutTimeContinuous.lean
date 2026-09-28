import MorganTianLib.Ch01.CutLocusAgreement
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Continuity of the cut time

The openness of the metric segment domain upgrades the usual closed
superlevel argument for `cutTime` to lower semicontinuity.  Together with
the closed minimizing-time sets this gives continuity in the extended
nonnegative reals.
-/

open MeasureTheory Set Filter Metric Riemannian Riemannian.Geodesic
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace M]

theorem lowerSemicontinuous_cutTime
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [Nonempty M] [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    LowerSemicontinuous
      (fun v : E => cutTime (I := I) g hg p (v : TangentSpace I p)) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro c
  by_cases htop : c = (⊤ : ℝ≥0∞)
  · simp [htop]
  by_cases hzero : c = 0
  · have hEq :
        (fun v : E => cutTime (I := I) g hg p (v : TangentSpace I p)) ⁻¹'
            Ioi (0 : ℝ≥0∞) = Set.univ := by
      ext v
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact cutTime_pos (I := I) g hg p (v : TangentSpace I p)
    rw [hzero, hEq]
    exact isOpen_univ
  have ht : 0 < c.toReal := ENNReal.toReal_pos hzero htop
  have hcEq : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal htop
  have hset :
      (fun v : E => cutTime (I := I) g hg p (v : TangentSpace I p)) ⁻¹' Ioi c =
        (fun v : E => ((c.toReal • v : E) : TangentSpace I p)) ⁻¹'
          segmentDomain (I := I) g hg p := by
    ext v
    change c < cutTime (I := I) g hg p (v : TangentSpace I p) ↔
      ((c.toReal • v : E) : TangentSpace I p) ∈
        segmentDomain (I := I) g hg p
    have hsmul := smul_mem_segmentDomain_iff_lt_cutTime (I := I) g hg p
      (v := (v : TangentSpace I p)) (t := c.toReal) ht
    simpa only [hcEq] using hsmul.symm
  rw [hset]
  exact (isOpen_segmentDomain (I := I) g hg p).preimage
    ((continuous_id (X := E)).const_smul c.toReal)

theorem upperSemicontinuous_cutTime
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [Nonempty M] [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    UpperSemicontinuous
      (fun v : E => cutTime (I := I) g hg p (v : TangentSpace I p)) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc0 : c = 0
  · rw [hc0]
    have hEq :
        (fun v : E => cutTime (I := I) g hg p (v : TangentSpace I p)) ⁻¹'
            Ici (0 : ℝ≥0∞) = Set.univ := by
      ext v
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      exact bot_le
    rw [hEq]
    exact isClosed_univ
  by_cases htop : c = (⊤ : ℝ≥0∞)
  · have hEq :
        (fun v : E => cutTime (I := I) g hg p (v : TangentSpace I p)) ⁻¹'
            Ici (⊤ : ℝ≥0∞) =
          ⋂ n : ℕ, {v : E |
            IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) (n : ℝ)} := by
      ext v
      simp only [mem_preimage, mem_Ici, top_le_iff, mem_iInter, mem_setOf_eq]
      constructor
      · intro htopv n
        refine (le_cutTime_iff (I := I) g hg p (v : TangentSpace I p)
          (Nat.cast_nonneg n)).1 ?_
        rw [htopv]
        exact le_top
      · intro hall
        refine eq_top_iff.2 (le_of_forall_lt fun b hb => ?_)
        obtain ⟨n, hn⟩ := exists_nat_gt b.toReal
        refine lt_of_lt_of_le ?_
          ((le_cutTime_iff (I := I) g hg p (v : TangentSpace I p)
            (Nat.cast_nonneg n)).2 (hall n))
        calc
          b = ENNReal.ofReal b.toReal :=
            (ENNReal.ofReal_toReal hb.ne_top).symm
          _ < ENNReal.ofReal (n : ℝ) :=
            ENNReal.ofReal_lt_ofReal_iff
              (lt_of_le_of_lt ENNReal.toReal_nonneg hn) |>.2 hn
    rw [htop, hEq]
    exact isClosed_iInter fun n =>
      isClosed_setOf_isMinimizingUpTo (I := I) g hg p (n : ℝ)
  have hcr : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal htop
  have hEq :
      (fun v : E => cutTime (I := I) g hg p (v : TangentSpace I p)) ⁻¹' Ici c =
        {v : E | IsMinimizingUpTo (I := I) g hg p
          (v : TangentSpace I p) c.toReal} := by
    ext v
    change c ≤ cutTime (I := I) g hg p (v : TangentSpace I p) ↔
      IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) c.toReal
    have hle := le_cutTime_iff (I := I) g hg p (v : TangentSpace I p)
      (t := c.toReal) ENNReal.toReal_nonneg
    simpa only [hcr] using hle
  rw [hEq]
  exact isClosed_setOf_isMinimizingUpTo (I := I) g hg p c.toReal

theorem continuous_cutTime
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [Nonempty M] [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    Continuous
      (fun v : E => cutTime (I := I) g hg p (v : TangentSpace I p)) := by
  rw [continuous_iff_lower_upperSemicontinuous]
  exact ⟨lowerSemicontinuous_cutTime (I := I) g hg p,
    upperSemicontinuous_cutTime (I := I) g hg p⟩

end MorganTianLib
