import MorganTianLib.Ch04.HamiltonMaximumBounded

/-!
# Morgan--Tian Ch. 4 - compact-time boundedness adapter

On a compact spatial domain and a compact time slab, a jointly continuous
finite-dimensional solution has bounded norm.  This module feeds that elementary
compactness fact into the existing bounded-support Hamilton barrier.  It removes
an independently supplied trajectory bound, while retaining the scalarized
regularity and spatial maximum hypotheses that belong to the analytic/geometric
producer.
-/

open Filter Set Function
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace MorganTianLib

variable {E X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace X] [CompactSpace X] [Nonempty X]

/-- A jointly continuous finite-dimensional solution on a compact time slab
inherits the boundedness required by the unbounded-carrier Hamilton barrier.
The theorem is an analytic adapter; it does not assert the missing tensor-bundle
parallel-frame or rough-Laplacian contact identities. -/
theorem hamilton_tensor_maximum_principle_bounded_of_continuous
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) {ψ : E → E} {K : ℝ≥0}
    (hpres : vectorFieldPreservesConvexSet Z ψ) (hψ : LipschitzWith K ψ)
    (L : ℝ → (X → E) → X → E)
    (hL : ∀ (t : ℝ) (f : X → E) (n : E) (x : X),
      IsMaxOn (fun y : X => ⟪n, f y⟫_ℝ) (univ : Set X) x →
        ⟪n, L t f x⟫_ℝ ≤ 0)
    (u : X → ℝ → E) {a b : ℝ}
    (hu : ContinuousOn (fun p : X × ℝ => u p.1 p.2)
      (univ ×ˢ Icc a b))
    (hpde : ∀ x : X, ∀ s : ℝ,
      HasDerivAt (u x) (L s (fun y : X => u y s) x + ψ (u x s)) s)
    (hF : Continuous ↿(hamiltonSupportValueFamily Z u))
    (hF' : Continuous ↿(hamiltonSupportDerivativeFamily Z u L ψ))
    (hinit : ∀ x : X, u x a ∈ Z) :
    ∀ x : X, ∀ t ∈ Icc a b, u x t ∈ Z := by
  let S : Set (X × ℝ) := (univ : Set X) ×ˢ Icc a b
  have hS : IsCompact S := isCompact_univ.prod isCompact_Icc
  let U : X × ℝ → E := fun p => u p.1 p.2
  have hU : ContinuousOn U S := by
    simpa [U, S] using hu
  have himage : IsCompact (U '' S) := hS.image_of_continuousOn hU
  obtain ⟨B, hB⟩ := himage.isBounded.subset_closedBall (0 : E)
  let B₀ : ℝ := max B 0
  have hbound : ∀ x t, t ∈ Icc a b → ‖u x t‖ ≤ B₀ := by
    intro x t ht
    have hmem : U (x, t) ∈ U '' S := by
      refine ⟨(x, t), ?_, rfl⟩
      exact ⟨mem_univ x, ht⟩
    have hball := hB hmem
    have hnorm : ‖u x t‖ ≤ B := by
      simpa [Metric.mem_closedBall, U, dist_zero_right] using hball
    exact hnorm.trans (le_max_left _ _)
  apply hamilton_tensor_maximum_principle_bounded
    hZne hZclosed hZconv hpres hψ L hL u hpde hbound
  · exact le_max_right _ _
  · exact hF
  · exact hF'
  · exact hinit

end MorganTianLib
