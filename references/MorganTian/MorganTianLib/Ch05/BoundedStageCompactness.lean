import MorganTianLib.Ch05.CompactStageConsequences

/-!
# Morgan--Tian Chapter 5: bounded sequences in a compact-stage assembly

Radial coverage captures bounded sets in a compact stage.  Since each stage
image is closed in the completed ambient, the same stage also captures the
closure of the set.  For sequences this gives a stage-level subsequence
producer, retaining the preimages and the convergent subsequence rather than
only its ambient limit.
-/

open Set Filter Metric Topology

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Under radial closed-ball coverage, the closure of every bounded
subset of the completed common ambient is contained in one compact stage image,
and hence in every later stage image. -/
theorem exists_stageEmbedding_range_superset_of_closure_of_bounded
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    {K : Set S.completedLimit.carrier} (hK : Bornology.IsBounded K) :
    ∃ n : ℕ, closure K ⊆ Set.range (S.stageEmbedding n) ∧
      ∀ m : ℕ, n ≤ m → closure K ⊆ Set.range (S.stageEmbedding m) := by
  obtain ⟨n, hKn, htail⟩ :=
    S.exists_eventually_stageEmbedding_range_superset_of_bounded hcover hK
  refine ⟨n, ?_, ?_⟩
  · exact closure_minimal hKn (S.isCompact_range_stageEmbedding n).isClosed
  · intro m hnm
    exact closure_minimal (htail m hnm)
      (S.isCompact_range_stageEmbedding m).isClosed

/-- **Math.** Under radial closed-ball coverage, a bounded sequence in the
completed common ambient has a fixed compact-stage model whose preimage
sequence has a convergent strictly monotone subsequence.  The stage index,
preimages, and subsequence are all retained for later diagonal assembly. -/
theorem exists_stage_subseq_tendsto_of_bounded_range_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (u : ℕ → S.completedLimit.carrier)
    (hu : Bornology.IsBounded (Set.range u)) :
    ∃ n : ℕ, ∃ v : ℕ → (S.stage n).carrier,
      ∃ y : (S.stage n).carrier,
        (∀ k, S.stageEmbedding n (v k) = u k) ∧
          ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Tendsto (fun k => v (φ k)) atTop (𝓝 y) := by
  obtain ⟨n, hn, _⟩ :=
    S.exists_eventually_stageEmbedding_range_superset_of_bounded hcover hu
  choose v hv using fun k => hn (Set.mem_range_self k)
  have hcompact : IsCompact (Set.univ : Set (S.stage n).carrier) :=
    isCompact_univ
  obtain ⟨y, hy, φ, hφ, hconv⟩ :=
    hcompact.tendsto_subseq (fun k => Set.mem_univ (v k))
  exact ⟨n, v, y, hv, φ, hφ, hconv⟩

end CompatiblePointedCompactSystem

end MorganTianLib

end

#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.exists_stageEmbedding_range_superset_of_closure_of_bounded
#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.exists_stage_subseq_tendsto_of_bounded_range_of_radial_stage_coverage
