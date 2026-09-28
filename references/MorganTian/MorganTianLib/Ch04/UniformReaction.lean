import MorganTianLib.Ch04.HamiltonMaximumLocalReaction
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Morgan--Tian Ch. 4 - uniform local reaction constants

A continuous family of fibre derivatives has a uniform norm bound on a compact
parameter-domain product. The convex mean-value theorem turns this into one
Lipschitz constant for every parameter, which supplies the constant in the
support-pair reaction estimate. Joint derivative continuity is an explicit
regularity assumption; fibrewise smoothness alone does not imply it.
-/

open Set
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace MorganTianLib

section UniformLipschitz

variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Math.** Compactness of the parameter-domain product bounds all fibre derivatives
by a common constant. Convexity then gives a uniform Lipschitz estimate. -/
theorem exists_uniform_lipschitzOnWith_of_continuousOn_fderiv
    {T : Set P} {S : Set E} {ψ : P → E → F}
    (hT : IsCompact T) (hS : IsCompact S) (hSconv : Convex ℝ S)
    (hψ : ∀ p ∈ T, ∀ v ∈ S, DifferentiableAt ℝ (ψ p) v)
    (hD : ContinuousOn (fun z : P × E => fderiv ℝ (ψ z.1) z.2) (T ×ˢ S)) :
    ∃ K : ℝ≥0, ∀ p ∈ T, LipschitzOnWith K (ψ p) S := by
  obtain ⟨K, hK⟩ := (hT.prod hS).bddAbove_image hD.nnnorm
  refine ⟨K, fun p hp => hSconv.lipschitzOnWith_of_nnnorm_fderiv_le (hψ p hp) ?_⟩
  intro v hv
  exact hK ⟨(p, v), ⟨hp, hv⟩, rfl⟩

/-- **Math.** For a compact parameter space and a finite-dimensional fibre, every closed
ball with jointly continuous fibre derivative has one uniform Lipschitz
constant. No restriction on the sign of the radius is needed. -/
theorem exists_uniform_lipschitzOnWith_closedBall_of_continuousOn_fderiv
    [CompactSpace P] [FiniteDimensional ℝ E]
    {ψ : P → E → F} {c : E} {r : ℝ}
    (hψ : ∀ p, ∀ v ∈ Metric.closedBall c r, DifferentiableAt ℝ (ψ p) v)
    (hD : ContinuousOn (fun z : P × E => fderiv ℝ (ψ z.1) z.2)
      (univ ×ˢ Metric.closedBall c r)) :
    ∃ K : ℝ≥0, ∀ p, LipschitzOnWith K (ψ p) (Metric.closedBall c r) := by
  obtain ⟨K, hK⟩ := exists_uniform_lipschitzOnWith_of_continuousOn_fderiv
    isCompact_univ (isCompact_closedBall c r) (convex_closedBall c r)
    (fun p _ => hψ p) hD
  exact ⟨K, fun p => hK p (mem_univ p)⟩

end UniformLipschitz

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Math.** Projection onto a closed convex set does not increase the
distance from any point in that set. -/
theorem convexProjection_dist_le_of_mem
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z)
    {c : E} (hc : c ∈ Z) (v : E) :
    dist (convexProjection Z hZne hZclosed hZconv v) c ≤ dist v c := by
  let p := convexProjection Z hZne hZclosed hZconv v
  have hinner : ⟪v - p, c - p⟫_ℝ ≤ 0 :=
    convexProjection_inner_nonpos Z hZne hZclosed hZconv v c hc
  have hsq := norm_sub_sq_real (v - p) (c - p)
  rw [show v - p - (c - p) = v - c by abel] at hsq
  change dist p c ≤ dist v c
  rw [dist_comm p c, dist_eq_norm, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖v - p‖]

/-- **Math.** A closed ball centered in the convex carrier contains the
projection of each of its points. -/
theorem convexProjection_mem_closedBall
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z)
    {c : E} (hc : c ∈ Z) {r : ℝ} {v : E} (hv : v ∈ Metric.closedBall c r) :
    convexProjection Z hZne hZclosed hZconv v ∈ Metric.closedBall c r := by
  exact (convexProjection_dist_le_of_mem hZne hZclosed hZconv hc v).trans hv

end Projection

section Reaction

variable {P E : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Math.** Joint continuity of the fibre derivative supplies a single reaction
constant at all active support pairs over the compact parameter set. The
compact convex comparison domain must contain the nearest-point projections
used in the reaction estimate. -/
theorem exists_uniform_convexSupportPair_reaction_bound_of_continuousOn_fderiv
    {T : Set P} {Z S : Set E} {ψ : P → E → E}
    (hT : IsCompact T) (hS : IsCompact S) (hSconv : Convex ℝ S)
    (hZne : Z.Nonempty) (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z)
    (hpres : ∀ p ∈ T, vectorFieldPreservesConvexSet Z (ψ p))
    (hψ : ∀ p ∈ T, ∀ v ∈ S, DifferentiableAt ℝ (ψ p) v)
    (hD : ContinuousOn (fun z : P × E => fderiv ℝ (ψ z.1) z.2) (T ×ˢ S))
    (hproj : ∀ v ∈ S, convexProjection Z hZne hZclosed hZconv v ∈ S) :
    ∃ K : ℝ≥0, ∀ p ∈ T, ∀ v ∈ S, ∀ q : ConvexSupportPair Z,
      ⟪q.1.2, v - q.1.1⟫_ℝ = Metric.infDist v Z →
        ⟪q.1.2, ψ p v⟫_ℝ ≤ (K : ℝ) * Metric.infDist v Z := by
  obtain ⟨K, hK⟩ := exists_uniform_lipschitzOnWith_of_continuousOn_fderiv
    hT hS hSconv hψ hD
  refine ⟨K, ?_⟩
  intro p hp v hv q hvalue
  exact convexSupportPair_reaction_bound_of_lipschitzOnWith hZne hZclosed hZconv
    (hpres p hp) (hK p hp) hproj hv q hvalue

/-- **Math.** On a closed ball centered in the carrier, joint continuity of
the fibre derivative gives one reaction bound for a compact parameter family.
The projection comparison region and the Lipschitz constant are both produced
from the stated geometric and regularity assumptions. -/
theorem exists_uniform_convexSupportPair_reaction_bound_closedBall_of_continuousOn_fderiv
    [CompactSpace P] {Z : Set E} {ψ : P → E → E}
    (hZne : Z.Nonempty) (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z)
    {c : E} (hc : c ∈ Z) {r : ℝ}
    (hpres : ∀ p, vectorFieldPreservesConvexSet Z (ψ p))
    (hψ : ∀ p, ∀ v ∈ Metric.closedBall c r, DifferentiableAt ℝ (ψ p) v)
    (hD : ContinuousOn (fun z : P × E => fderiv ℝ (ψ z.1) z.2)
      (univ ×ˢ Metric.closedBall c r)) :
    ∃ K : ℝ≥0, ∀ p, ∀ v ∈ Metric.closedBall c r, ∀ q : ConvexSupportPair Z,
      ⟪q.1.2, v - q.1.1⟫_ℝ = Metric.infDist v Z →
        ⟪q.1.2, ψ p v⟫_ℝ ≤ (K : ℝ) * Metric.infDist v Z := by
  obtain ⟨K, hK⟩ :=
    exists_uniform_lipschitzOnWith_closedBall_of_continuousOn_fderiv hψ hD
  refine ⟨K, ?_⟩
  intro p v hv q hvalue
  exact convexSupportPair_reaction_bound_of_lipschitzOnWith hZne hZclosed hZconv
    (hpres p) (hK p) (fun _ hw => convexProjection_mem_closedBall hZne hZclosed hZconv hc hw)
    hv q hvalue

end Reaction

end MorganTianLib

#print axioms MorganTianLib.exists_uniform_lipschitzOnWith_of_continuousOn_fderiv
#print axioms MorganTianLib.exists_uniform_lipschitzOnWith_closedBall_of_continuousOn_fderiv
#print axioms MorganTianLib.exists_uniform_convexSupportPair_reaction_bound_of_continuousOn_fderiv
#print axioms MorganTianLib.convexProjection_dist_le_of_mem
#print axioms MorganTianLib.convexProjection_mem_closedBall
#print axioms MorganTianLib.exists_uniform_convexSupportPair_reaction_bound_closedBall_of_continuousOn_fderiv
