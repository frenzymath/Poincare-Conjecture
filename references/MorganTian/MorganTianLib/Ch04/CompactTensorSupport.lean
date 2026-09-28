import MorganTianLib.Ch04.LocalTensorSupportFamily
import MorganTianLib.Ch04.HamiltonMaximumBounded
import MorganTianLib.Ch04.TensorDistanceContinuity

/-!
# Compact covers for actual transported tensor families

On a compact manifold, finitely many compact patches carry jointly continuous
representatives of a tensor family in fixed tangent fibres. Each representative
is identified with actual Levi-Civita parallel transport, uniformly in the
parameter. These patches supply the spatial indices for Hamilton's compact
support envelope.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Riemannian
open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]

/-- **Math.** A finite compact cover carries smooth frames that reconstruct actual
inverse-transported tensors. The same cover and frames work for every tensor
field, so in particular for a time family and its time derivative. -/
theorem exists_finite_compact_localLeviCivitaTensor_cover
    (g : RiemannianMetric I M) (k : ℕ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ (s : Finset M) (K : M → Set M)
      (Y : ∀ p : M, Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M),
      (∀ p, IsCompact (K p)) ∧ (univ : Set M) = ⋃ p ∈ s, K p ∧
      ∀ p x, x ∈ K p → ∃ e : TangentSpace I p ≃ₗᵢ[ℝ] TangentSpace I x,
        (covariantTensorTransportEquiv k e).toLinearEquiv ∈
          leviCivitaCovariantTensorTransports g k p x ∧
        ∀ (A : CovTensorField I M k) (hA : IsCovariantTensorField A),
          tensorInSmoothFrame g p (Y p) A x =
            hilbertCovariantTensorTransportEquiv k e.symm (hA.toHilbertFiber g x) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hlocal (p : M) : ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∃ Y : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M,
        ∀ x ∈ V, ∃ e : TangentSpace I p ≃ₗᵢ[ℝ] TangentSpace I x,
          (covariantTensorTransportEquiv k e).toLinearEquiv ∈
            leviCivitaCovariantTensorTransports g k p x ∧
          ∀ (A : CovTensorField I M k) (hA : IsCovariantTensorField A),
            tensorInSmoothFrame g p Y A x =
              hilbertCovariantTensorTransportEquiv k e.symm (hA.toHilbertFiber g x) := by
    obtain ⟨U, hU, hpU, hC, hmem⟩ := exists_local_leviCivitaTangentTransport g k p
    obtain ⟨V, hV, hpV, hVU, Y, hY⟩ :=
      exists_localLeviCivitaTensor_frame g p hU hpU hC
    refine ⟨V, hV, hpV, Y, ?_⟩
    intro x hx
    refine ⟨localLeviCivitaTangentTransport g p hC ⟨x, hVU hx⟩,
      hmem ⟨x, hVU hx⟩, ?_⟩
    intro A hA
    exact hY hA x hx
  choose V hV hpV Y hY using hlocal
  have hcover : (univ : Set M) ⊆ ⋃ p, V p := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hpV x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hV hcover
  obtain ⟨K, hK, hKV, hKeq⟩ :=
    isCompact_univ.finite_compact_cover s V (fun p _ => hV p) hs
  exact ⟨s, K, Y, hK, hKeq, fun p x hx => hY p x (hKV p hx)⟩

/-- **Math.** A tensor family with jointly continuous evaluations has a uniform
intrinsic Hilbert norm bound on each compact time slab. -/
theorem exists_uniform_tensorHilbertFiber_norm_bound
    (g : RiemannianMetric I M) {k : ℕ} {A : ℝ → CovTensorField I M k}
    (hA : ∀ t, IsCovariantTensorField (A t))
    (hcont : ∀ Y : Fin k → SmoothVectorField I M,
      Continuous (fun z : ℝ × M => A z.1 Y z.2)) (a b : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x : M,
      ‖(hA t).toHilbertFiber g x‖ ≤ B := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hn := continuous_tensorHilbertFiber_norm g hA hcont
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set M))).bddAbove_image
    hn.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht x
  exact (hB ⟨(t, x), ⟨ht, mem_univ x⟩, rfl⟩).trans (le_max_left _ _)

end MorganTianLib
