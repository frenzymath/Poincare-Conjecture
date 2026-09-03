import MorganTianLib.Ch05.CompactStageConsequences

/-!
# Morgan--Tian Chapter 5: bounded sequences in the assembled ambient

Radial closed-ball coverage places every bounded sequence in one compact stage.
This file records the resulting subsequence extraction directly, providing a
sequential precompactness input for the Chapter 5 diagonal argument.
-/

open Set Filter Metric Topology

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Under radial closed-ball coverage, every sequence with bounded
range has a convergent strictly monotone subsequence in the completed common
ambient.  The compact stage containing the range supplies the subsequence; no
completeness or independent GH-limit choice is needed beyond the assembled
stage system.
-/
theorem exists_subseq_tendsto_of_bounded_range_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (u : ℕ → S.completedLimit.carrier)
    (hu : Bornology.IsBounded (Set.range u)) :
    ∃ y : S.completedLimit.carrier, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        Tendsto (fun k => u (φ k)) atTop (𝓝 y) := by
  obtain ⟨n, hn, _⟩ :=
    S.exists_eventually_stageEmbedding_range_superset_of_bounded hcover hu
  choose c hc using fun k => hn (Set.mem_range_self k)
  have hcompact : IsCompact (Set.univ : Set (S.stage n).carrier) :=
    isCompact_univ
  obtain ⟨a, ha, φ, hφ, hconv⟩ :=
    hcompact.tendsto_subseq (fun k => Set.mem_univ (c k))
  refine ⟨S.stageEmbedding n a, φ, hφ, ?_⟩
  have hcont :
      Tendsto (S.stageEmbedding n) (𝓝 a)
        (𝓝 (S.stageEmbedding n a)) :=
    (S.stageEmbedding_isometry n).continuous.continuousAt
  have hpush := hcont.comp hconv
  have heq :
      (fun k => S.stageEmbedding n (c (φ k))) =
        (fun k => u (φ k)) := by
    funext k
    exact hc (φ k)
  simpa [Function.comp_def, heq] using hpush

end CompatiblePointedCompactSystem

end MorganTianLib

#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_subseq_tendsto_of_bounded_range_of_radial_stage_coverage
