import PetersenLib.Ch05.ConstantSpeedApproximation

/-!
# Petersen Ch. 5, §5.3 — the distance is an infimum over constant-speed curves

The constant-speed half of Remark 5.3.11: the Riemannian distance
`riemannianDistance g p q`, defined in `PetersenLib/Ch05/MetricStructure.lean` as
the infimum of the lengths of *all* piecewise smooth curves joining `p` to `q`,
is unchanged if the competitors are restricted to those piecewise smooth curves
that additionally have **constant speed**.

* `constantSpeedDistanceSet` — the restricted competitor set: the lengths of the
  piecewise smooth constant-speed curves `γ : [0,1] → M` with `γ 0 = p`,
  `γ 1 = q`.

* `riemannianDistance_eq_sInf_constantSpeedDistanceSet` — the two infima agree.
  The inequality `≤` is the inclusion of competitor sets; the inequality `≥` is
  Corollary 5.3.10 (`approximateByConstantSpeedCurve`: every piecewise smooth
  curve is approximated, to within a factor `1 + ε` in length and with the same
  endpoints, by a piecewise smooth constant-speed curve) followed by `ε → 0`.
  No connectedness hypothesis is needed: the restricted set is empty exactly when
  the full set is, so when `p` and `q` lie in different components both sides
  degenerate to the junk value `sInf ∅ = 0` together.

This file serves the blueprint node `lem:pet-ch5-constant-speed-distance`.  It
does **not** address the other sentence of Remark 5.3.11, that the distance
theory can equivalently be developed using absolutely continuous curves
(`rem:pet-ch5-absolutely-continuous-curves`); that program is the subject of
Exercise 5.9.29 (`rem:pet-ch5-ex-29`) and is not formalized here.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open scoped Manifold Topology ContDiff Interval

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Boundaryless

variable [I.Boundaryless]

/-- **Math.** The set of lengths of the piecewise smooth **constant-speed** curves
`γ : [0,1] → M` joining `p` to `q`.  This is the competitor set of
`riemannianDistance` cut down by the extra requirement `IsConstantSpeedCurve`. -/
def constantSpeedDistanceSet (g : RiemannianMetric I M) (p q : M) : Set ℝ :=
  {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
    IsConstantSpeedCurve (I := I) g γ 0 1 ∧
    γ 0 = p ∧ γ 1 = q ∧ L = curveLength (I := I) g γ 0 1}

/-- **Math.** Lengths of constant-speed competitors are nonnegative. -/
theorem forall_mem_constantSpeedDistanceSet_nonneg (g : RiemannianMetric I M) (p q : M) :
    ∀ L ∈ constantSpeedDistanceSet (I := I) g p q, 0 ≤ L := by
  rintro L ⟨γ, -, -, -, -, rfl⟩
  exact curveLength_nonneg (I := I) g γ zero_le_one

/-- **Math.** The constant-speed competitor set is bounded below by `0`. -/
theorem bddBelow_constantSpeedDistanceSet (g : RiemannianMetric I M) (p q : M) :
    BddBelow (constantSpeedDistanceSet (I := I) g p q) :=
  ⟨0, forall_mem_constantSpeedDistanceSet_nonneg (I := I) g p q⟩

/-- **Math.** Every constant-speed competitor is a competitor for
`riemannianDistance`: forgetting the constant-speed clause embeds the restricted
set into the full one. -/
theorem constantSpeedDistanceSet_subset (g : RiemannianMetric I M) (p q : M) :
    constantSpeedDistanceSet (I := I) g p q ⊆
      {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
        γ 0 = p ∧ γ 1 = q ∧ L = curveLength (I := I) g γ 0 1} := by
  rintro L ⟨γ, hγ, -, h0, h1, rfl⟩
  exact ⟨γ, hγ, h0, h1, rfl⟩

/-- **Math.** For every piecewise smooth curve `γ` from `p` to `q`, the infimum of
the lengths of the constant-speed competitors is at most `L(γ)`.  Indeed
Corollary 5.3.10 produces, for each `ε > 0`, a constant-speed competitor of
length at most `(1 + ε) L(γ)`; letting `ε → 0` gives the claim. -/
theorem sInf_constantSpeedDistanceSet_le_curveLength (g : RiemannianMetric I M)
    {γ : ℝ → M} {p q : M} (hγ : IsPiecewiseSmoothCurve (I := I) γ 0 1)
    (h0 : γ 0 = p) (h1 : γ 1 = q) :
    sInf (constantSpeedDistanceSet (I := I) g p q) ≤ curveLength (I := I) g γ 0 1 := by
  have hL : 0 ≤ curveLength (I := I) g γ 0 1 :=
    curveLength_nonneg (I := I) g γ zero_le_one
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  set ε : ℝ := δ / (curveLength (I := I) g γ 0 1 + 1) with hε_def
  have hden : (0:ℝ) < curveLength (I := I) g γ 0 1 + 1 := by linarith
  have hε : 0 < ε := div_pos hδ hden
  obtain ⟨σ, hσ, hσ0, hσ1, hσconst, hσlen⟩ :=
    approximateByConstantSpeedCurve (I := I) g hγ hε
  have hmem : curveLength (I := I) g σ 0 1 ∈ constantSpeedDistanceSet (I := I) g p q :=
    ⟨σ, hσ, hσconst, by rw [hσ0, h0], by rw [hσ1, h1], rfl⟩
  have hle : sInf (constantSpeedDistanceSet (I := I) g p q) ≤ curveLength (I := I) g σ 0 1 :=
    csInf_le (bddBelow_constantSpeedDistanceSet (I := I) g p q) hmem
  have harith : (1 + ε) * curveLength (I := I) g γ 0 1 ≤ curveLength (I := I) g γ 0 1 + δ := by
    have : ε * curveLength (I := I) g γ 0 1 ≤ δ := by
      rw [hε_def, div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith
    nlinarith
  linarith [hle.trans hσlen]

/-- **Math.** Remark 5.3.11 (constant-speed sentence): the Riemannian distance is
equally the infimum of the lengths of the piecewise smooth **constant-speed**
curves joining `p` to `q`,
`d(p, q) = inf {L(γ) : γ piecewise smooth of constant speed, γ(0) = p, γ(1) = q}`.
The inequality `≤` holds because constant-speed competitors are competitors; the
inequality `≥` is Corollary 5.3.10 with `ε → 0`.  When `p` and `q` lie in
different components both competitor sets are empty and both sides take the value
`sInf ∅ = 0`, so no connectedness hypothesis is required. -/
theorem riemannianDistance_eq_sInf_constantSpeedDistanceSet (g : RiemannianMetric I M) (p q : M) :
    riemannianDistance (I := I) g p q = sInf (constantSpeedDistanceSet (I := I) g p q) := by
  classical
  set S : Set ℝ := {L : ℝ | ∃ γ : ℝ → M, IsPiecewiseSmoothCurve (I := I) γ 0 1 ∧
    γ 0 = p ∧ γ 1 = q ∧ L = curveLength (I := I) g γ 0 1} with hS
  set C : Set ℝ := constantSpeedDistanceSet (I := I) g p q with hC
  have hd : riemannianDistance (I := I) g p q = sInf S := rfl
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · have hsub : C ⊆ S := constantSpeedDistanceSet_subset (I := I) g p q
    rw [hSe] at hsub
    have hCe : C = ∅ := Set.subset_empty_iff.mp hsub
    rw [hd, hSe, hCe]
  · obtain ⟨L₀, γ₀, hγ₀, h0₀, h1₀, -⟩ := id hSne
    have hCne : C.Nonempty := by
      obtain ⟨σ, hσ, hσ0, hσ1, hσconst, -⟩ :=
        approximateByConstantSpeedCurve (I := I) g hγ₀ one_pos
      exact ⟨curveLength (I := I) g σ 0 1,
        ⟨σ, hσ, hσconst, by rw [hσ0, h0₀], by rw [hσ1, h1₀], rfl⟩⟩
    refine le_antisymm ?_ ?_
    · exact csInf_le_csInf ⟨0, forall_mem_riemannianDistanceSet_nonneg (I := I) g p q⟩
        hCne (constantSpeedDistanceSet_subset (I := I) g p q)
    · refine le_csInf hSne ?_
      rintro L ⟨γ, hγ, h0, h1, rfl⟩
      exact sInf_constantSpeedDistanceSet_le_curveLength (I := I) g hγ h0 h1

end Boundaryless

end PetersenLib
