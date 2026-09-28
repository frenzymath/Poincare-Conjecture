import MorganTianLib.Ch04.CompactTensorSupport
import MorganTianLib.Ch04.FiniteTensorSupport

/-!
# Compact support envelopes for geometric tensor distance

The canonical finite frame cover and the uniform tensor norm bound produce
bounded support carriers. Their scalar envelope is exactly the supremum of
the intrinsic fibre distances on each compact time slab.

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
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M]

/-- **Math.** Actual tensor families on compact manifolds admit a compact,
jointly continuous scalar support family whose envelope is the global
intrinsic distance to the parallel-invariant convex carrier. The chosen
frames reconstruct every tensor field, including time derivatives. -/
theorem exists_compact_tensorSupport_envelope
    (g : RiemannianMetric I M) {k : ℕ} {A : ℝ → CovTensorField I M k}
    (hA : ∀ t, IsCovariantTensorField (A t))
    (hcont : ∀ Y : Fin k → SmoothVectorField I M,
      Continuous (fun z : ℝ × M => A z.1 Y z.2)) (a b : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x))),
      (∀ x, (Z x).Nonempty) → (∀ x, IsClosed (Z x)) → (∀ x, Convex ℝ (Z x)) →
      parallelInvariantFiberSet Z (leviCivitaCovariantTensorTransports g k) →
      ∃ (s : Finset M) (K : M → Set M)
        (Y : ∀ p : M, Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M)
        (R : M → ℝ),
        (∀ p, IsCompact (K p)) ∧ (univ : Set M) = ⋃ p ∈ s, K p ∧
        (∀ p x, x ∈ K p → ∃ e : TangentSpace I p ≃ₗᵢ[ℝ] TangentSpace I x,
          (covariantTensorTransportEquiv k e).toLinearEquiv ∈
            leviCivitaCovariantTensorTransports g k p x ∧
          ∀ (B : CovTensorField I M k) (hB : IsCovariantTensorField B),
            tensorInSmoothFrame g p (Y p) B x =
              hilbertCovariantTensorTransportEquiv k e.symm (hB.toHilbertFiber g x)) ∧
        let P := Unit ⊕ Σ p : s, K p ×
          BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)
        let F : P → ℝ → ℝ := fun q t => finiteTensorSupportValue g s K Y Z R (A t) q
        CompactSpace P ∧ Continuous (Function.uncurry F) ∧
          ∀ t ∈ Icc a b, (⨆ q : P, F q t) =
            ⨆ x : M, Metric.infDist ((hA t).toHilbertFiber g x)
              (hilbertCovariantTensorEquiv ⁻¹' Z x) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z hne hclosed hconv hparallel
  obtain ⟨s, K, Y, hK, hcover, hframe⟩ := exists_finite_compact_localLeviCivitaTensor_cover g k
  obtain ⟨B, hB0, hB⟩ := exists_uniform_tensorHilbertFiber_norm_bound g hA hcont a b
  let ZH (p : M) : Set (HilbertCovariantTensor k (TangentSpace I p)) :=
    hilbertCovariantTensorEquiv ⁻¹' Z p
  have hneH (p : M) : (ZH p).Nonempty :=
    ⟨WithLp.toLp 2 (hne p).choose, (hne p).choose_spec⟩
  have hclosedH (p : M) : IsClosed (ZH p) :=
    (hclosed p).preimage hilbertCovariantTensorEquiv.continuous
  have hconvH (p : M) : Convex ℝ (ZH p) :=
    (hconv p).linear_preimage hilbertCovariantTensorEquiv.toLinearMap
  let R (p : M) : ℝ := ‖(hneH p).choose‖ + 2 * B
  let P := Unit ⊕ Σ p : s, K p × BoundedConvexSupportPair (ZH p) (R p)
  let F : P → ℝ → ℝ := fun q t => finiteTensorSupportValue g s K Y Z R (A t) q
  let d : M → ℝ → ℝ := fun x t =>
    Metric.infDist ((hA t).toHilbertFiber g x) (ZH x)
  letI : CompactSpace P := compactSpace_finiteTensorSupportIndex g s K Z R hK hclosed
  have hF : Continuous (Function.uncurry F) :=
    continuous_finiteTensorSupportValue g s K Y Z R hcont
  have hdist := continuous_tensorHilbertFiber_infDist (I := I) (M := M) (A := A)
    g hA hcont Z hparallel
  have hd : Continuous (Function.uncurry d) :=
    hdist.comp (f := (Prod.swap : M × ℝ → ℝ × M)) continuous_swap
  have hchartDist (p x : M) (hx : x ∈ K p) (t : ℝ) :
      Metric.infDist (tensorInSmoothFrame g p (Y p) (A t) x) (ZH p) = d x t := by
    obtain ⟨e, he, hrep⟩ := hframe p x hx
    rw [hrep (A t) (hA t)]
    apply infDist_transport_eq
    rw [hilbertCovariantTensorTransportEquiv_image_preimage]
    congr 1
    have hforward := hparallel p x (covariantTensorTransportEquiv k e).toLinearEquiv he
    rw [← covariantTensorTransportEquiv_symm, ← hforward]
    exact (covariantTensorTransportEquiv k e).toEquiv.symm_image_image (Z p)
  refine ⟨s, K, Y, R, hK, hcover, hframe, inferInstance, hF, ?_⟩
  intro t ht
  change (⨆ q : P, F q t) = ⨆ x : M, d x t
  have hFb := bddAbove_range_family (F := F) hF t
  have hdb := bddAbove_range_family (F := d) hd t
  have hzero : 0 ≤ ⨆ q : P, F q t := by
    exact le_ciSup hFb (Sum.inl ())
  apply le_antisymm
  · apply ciSup_le
    intro q
    cases q with
    | inl z =>
      exact (Metric.infDist_nonneg : 0 ≤ d (Classical.arbitrary M) t).trans
        (le_ciSup hdb (Classical.arbitrary M))
    | inr q =>
      have hle := convexSupportPair_eval_le_infDist (ZH q.1) (hneH q.1)
        (hclosedH q.1) (hconvH q.1)
        (boundedPairSupport (ZH q.1) (R q.1) q.2.2)
        (tensorInSmoothFrame g q.1 (Y q.1) (A t) q.2.1)
      change F (Sum.inr q) t ≤ _ at hle
      rw [hchartDist q.1 q.2.1 q.2.1.property t] at hle
      exact hle.trans (le_ciSup hdb q.2.1)
  · apply ciSup_le
    intro x
    by_cases hxZ : (hA t).toHilbertFiber g x ∈ ZH x
    · simpa only [d, Metric.infDist_zero_of_mem hxZ] using hzero
    · have hxcover : x ∈ ⋃ p ∈ s, K p := hcover ▸ mem_univ x
      obtain ⟨p, hp, hxK⟩ := mem_iUnion₂.mp hxcover
      have hv : ‖tensorInSmoothFrame g p (Y p) (A t) x‖ ≤ B := by
        obtain ⟨e, _, hrep⟩ := hframe p x hxK
        rw [hrep (A t) (hA t), (hilbertCovariantTensorTransportEquiv k e.symm).norm_map]
        exact hB t ht x
      have hvout : tensorInSmoothFrame g p (Y p) (A t) x ∉ ZH p := by
        intro hvZ
        have hz := Metric.infDist_zero_of_mem hvZ
        rw [hchartDist p x hxK t] at hz
        exact hxZ ((hclosedH x).mem_iff_infDist_zero (hneH x) |>.mpr hz)
      obtain ⟨q, hq⟩ := exists_boundedConvexSupportPair_eval_eq_infDist
        (hneH p) (hclosedH p) (hconvH p) (hneH p).choose (hneH p).choose_spec
        hB0 _ hv hvout
      have hvalue : F (Sum.inr ⟨⟨p, hp⟩, ⟨x, hxK⟩, q⟩) t = d x t := by
        exact hq.trans (hchartDist p x hxK t)
      rw [← hvalue]
      exact le_ciSup hFb _

/-! Compact support indices attain their positive envelope.  This is the
analytic half of the finite-maximizer bridge; geometric identification of a
maximizer with an active fibre is supplied by the surrounding support family. -/

theorem exists_finiteTensorSupport_positive_maximizer
    {P : Type*} [TopologicalSpace P] [CompactSpace P] [Nonempty P]
    {F : P → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    (t : ℝ) (hpos : 0 < ⨆ q : P, F q t) :
    ∃ q : P, F q t = ⨆ r : P, F r t ∧ 0 < F q t := by
  have hFt : Continuous (fun q : P => F q t) := by
    exact (hF.comp (continuous_id.prodMk continuous_const))
  have hne : (Set.univ : Set P).Nonempty := Set.univ_nonempty
  obtain ⟨q, hq, hqmax⟩ := isCompact_univ.exists_isMaxOn hne hFt.continuousOn
  have heq : F q t = ⨆ r : P, F r t := by
    apply le_antisymm
    · exact le_ciSup (bddAbove_range_family hF t) q
    · apply ciSup_le
      intro r
      change F r t ≤ F q t
      exact (isMaxOn_iff.mp hqmax) r (Set.mem_univ r)
  refine ⟨q, heq, ?_⟩
  rw [heq]
  exact hpos

end MorganTianLib

#print axioms MorganTianLib.exists_compact_tensorSupport_envelope
#print axioms MorganTianLib.exists_finiteTensorSupport_positive_maximizer
