import MorganTianLib.Ch04.ActiveFiniteTensorSupport
import MorganTianLib.Ch04.HamiltonPositiveEnvelope

/-!
# Geometric tensor preservation on a compact manifold

The finite transported support envelope converts the geometric tensor PDE into
the scalar positive-maximum comparison. Closedness then recovers fibrewise
membership in the parallel-invariant convex carrier for the full time slab.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Riemannian
open scoped ContDiff Manifold Topology Bundle InnerProductSpace NNReal

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M]

/-- **Math.** A tensor field solving the rough-Laplacian reaction equation on
a compact manifold with fixed metric stays in a nonempty closed convex
parallel-invariant fibre carrier. The reaction has one local Lipschitz
constant on comparison domains containing the solution and its projections;
its vector field preserves the carrier. Joint continuity of the evaluated
tensor and time derivative supplies the compact scalar comparison. -/
theorem geometric_tensor_preserves_parallelInvariantConvexSet
    (g : RiemannianMetric I M) {k : ℕ}
    {A D : ℝ → CovTensorField I M k} (hA : ∀ t, IsCovariantTensorField (A t))
    (hcontA : ∀ V : Fin k → SmoothVectorField I M,
      Continuous (fun z : ℝ × M => A z.1 V z.2))
    (hcontD : ∀ V : Fin k → SmoothVectorField I M,
      Continuous (fun z : ℝ × M => D z.1 V z.2))
    {a b : ℝ}
    (hderiv : ∀ t ∈ Ioo a b, ∀ (x : M) (V : Fin k → SmoothVectorField I M),
      HasDerivAt (fun r => A r V x) (D t V x) t) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x)))
      (hne : ∀ x, (Z x).Nonempty) (hclosed : ∀ x, IsClosed (Z x))
      (hconv : ∀ x, Convex ℝ (Z x))
      (ψ : ∀ x : M, HilbertCovariantTensor k (TangentSpace I x) →
        HilbertCovariantTensor k (TangentSpace I x)) (C : ℝ≥0)
      (S : ∀ x : M, Set (HilbertCovariantTensor k (TangentSpace I x))),
      parallelInvariantFiberSet Z (leviCivitaCovariantTensorTransports g k) →
      (∀ x, vectorFieldPreservesConvexSet (hilbertCovariantTensorEquiv ⁻¹' Z x) (ψ x)) →
      (∀ x, LipschitzOnWith C (ψ x) (S x)) →
      (∀ x w, w ∈ S x → convexProjection (hilbertCovariantTensorEquiv ⁻¹' Z x)
        ⟨WithLp.toLp 2 (hne x).choose, (hne x).choose_spec⟩
        ((hclosed x).preimage hilbertCovariantTensorEquiv.continuous)
        ((hconv x).linear_preimage hilbertCovariantTensorEquiv.toLinearMap) w ∈ S x) →
      (∀ t ∈ Ioo a b, ∀ x, (hA t).toHilbertFiber g x ∈ S x) →
      (∀ t ∈ Ioo a b, ∀ (x : M) (V : Fin k → SmoothVectorField I M),
        HasDerivAt (fun r => A r V x)
          (roughLaplacian g g.leviCivitaConnection (A t) V x +
            (ψ x ((hA t).toHilbertFiber g x)).ofLp (fun j => V j x)) t) →
      (∀ x, (hA a).toFiber g x ∈ Z x) →
      ∀ t ∈ Icc a b, ∀ x, (hA t).toFiber g x ∈ Z x := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z hne hclosed hconv ψ C S hparallel hpres hψ hproj hrange hPDE hinit
  by_cases hab : a ≤ b
  · obtain ⟨s, K, Y, R, _hK, _hcover, hframe, hcompact, hF, hsup⟩ :=
      exists_compact_tensorSupport_envelope g hA hcontA a b Z hne hclosed hconv hparallel
    let P := Unit ⊕ Σ p : s, K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)
    let F : P → ℝ → ℝ := fun q t => finiteTensorSupportValue g s K Y Z R (A t) q
    let F' : P → ℝ → ℝ := fun q t => finiteTensorSupportDerivative g s K Y Z R (D t) q
    letI : CompactSpace P := hcompact
    have hF' : Continuous (Function.uncurry F') :=
      continuous_finiteTensorSupportDerivative g s K Y Z R hcontD
    have hinitF : (⨆ q : P, F q a) ≤ 0 := by
      rw [hsup a ⟨le_rfl, hab⟩]
      apply ciSup_le
      intro x
      apply le_of_eq
      exact Metric.infDist_zero_of_mem (hinit x)
    have hderivF : ∀ q : P, ∀ t ∈ Ioo a b, HasDerivAt (F q) (F' q t) t := by
      intro q t ht
      exact hasDerivAt_finiteTensorSupportValue g s K Y Z R (hderiv t ht) q
    have hmax : ∀ t ∈ Ico a b, 0 < (⨆ r : P, F r t) → ∀ q : P,
        F q t = (⨆ r : P, F r t) → F' q t ≤ (C : ℝ) * (⨆ r : P, F r t) := by
      intro t ht hpos q hq
      by_cases hta : t = a
      · subst t
        exact (not_lt_of_ge hinitF hpos).elim
      · have ht' : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), ht.2⟩
        exact finiteTensorSupportDerivative_le_of_positive_max g s K Y hA hcontA
          (hderiv t ht') Z R hne hclosed hconv ψ C S hparallel hpres hψ hproj
          (hrange t ht') (hPDE t ht')
          (fun p x hx => by
            obtain ⟨e, he, hrep⟩ := hframe p x hx
            exact ⟨e, he, fun r => hrep (A r) (hA r)⟩)
          (hsup t ⟨ht.1, ht.2.le⟩) hpos q hq
    have hnonpos := hamilton_envelope_nonpositive_of_positive_max
      hF hF' hderivF hmax hinitF
    intro t ht x
    have hd := continuous_tensorHilbertFiber_infDist (I := I) (M := M) (A := A)
      g hA hcontA Z hparallel
    have hdSlice : Continuous (fun z : M => Metric.infDist ((hA t).toHilbertFiber g z)
        (hilbertCovariantTensorEquiv ⁻¹' Z z)) :=
      hd.comp (f := fun z : M => (t, z)) (continuous_const.prodMk continuous_id)
    have hle : Metric.infDist ((hA t).toHilbertFiber g x)
        (hilbertCovariantTensorEquiv ⁻¹' Z x) ≤ 0 := by
      refine (le_ciSup (isCompact_range hdSlice).bddAbove x).trans ?_
      rw [← hsup t ht]
      exact hnonpos t ht
    have hzero := le_antisymm hle Metric.infDist_nonneg
    exact (((hclosed x).preimage hilbertCovariantTensorEquiv.continuous).mem_iff_infDist_zero
      ⟨WithLp.toLp 2 (hne x).choose, (hne x).choose_spec⟩).mpr hzero
  · intro t ht
    exact (hab (ht.1.trans ht.2)).elim

end MorganTianLib

#print axioms MorganTianLib.geometric_tensor_preserves_parallelInvariantConvexSet
