import MorganTianLib.Ch04.LocalTensorSupportFamily
import MorganTianLib.Ch04.HamiltonMaximumBounded
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Finite families of transported tensor supports

Finitely many compact spatial patches, each paired with bounded support
normals in its centre fibre, give a compact parameter space. The scalar
family and its time derivative are the pairings of the reconstructed tensors
with those normals. A zero scalar is included in the same index space.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Riemannian
open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The scalar supports over finitely many spatial patches, together
with the zero scalar. -/
def finiteTensorSupportValue (g : RiemannianMetric I M) {k : ℕ}
    (s : Finset M) (K : M → Set M)
    (Y : ∀ p : M, Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x))) →
      (R : M → ℝ) → CovTensorField I M k →
      (Unit ⊕ Σ p : s, K p ×
        BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) → ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  fun _ _ A => Sum.elim (fun _ => 0) (fun r =>
    ⟪r.2.2.1.2, tensorInSmoothFrame g r.1 (Y r.1) A r.2.1 - r.2.2.1.1⟫_ℝ)

/-- **Math.** Pairing the tensor derivative with the same indexed normal gives
the derivative of the scalar support. -/
def finiteTensorSupportDerivative (g : RiemannianMetric I M) {k : ℕ}
    (s : Finset M) (K : M → Set M)
    (Y : ∀ p : M, Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x))) →
      (R : M → ℝ) → CovTensorField I M k →
      (Unit ⊕ Σ p : s, K p ×
        BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) → ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  fun _ _ D => Sum.elim (fun _ => 0) (fun r =>
    ⟪r.2.2.1.2, tensorInSmoothFrame g r.1 (Y r.1) D r.2.1⟫_ℝ)

/-- **Math.** Joint continuity of tensor evaluations implies joint continuity
of the full finite scalar support family, including its support parameters. -/
theorem continuous_finiteTensorSupportValue
    (g : RiemannianMetric I M) {k : ℕ} (s : Finset M) (K : M → Set M)
    (Y : ∀ p : M, Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x))) (R : M → ℝ)
      {A : ℝ → CovTensorField I M k},
      (∀ V : Fin k → SmoothVectorField I M,
        Continuous (fun z : ℝ × M => A z.1 V z.2)) →
      Continuous (fun qt : (Unit ⊕ Σ p : s, K p ×
        BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) × ℝ =>
          finiteTensorSupportValue g s K Y Z R (A qt.2) qt.1) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z R A hcont
  apply (Homeomorph.sumProdDistrib (X := Unit) (Y := Σ p : s, K p ×
    BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p))
      (Z := ℝ)).symm.comp_continuous_iff'.mp
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_const
  · apply (Homeomorph.sigmaProdDistrib (X := fun p : s => K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p))
        (Y := ℝ)).symm.comp_continuous_iff'.mp
    apply continuous_sigma
    intro p
    change Continuous (fun z : (K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) × ℝ =>
        ⟪z.1.2.1.2, tensorInSmoothFrame g p (Y p) (A z.2) z.1.1 - z.1.2.1.1⟫_ℝ)
    exact continuous_fst.snd.subtype_val.snd.inner
      (((continuous_tensorInSmoothFrame g p (Y p) hcont).comp
        (continuous_snd.prodMk continuous_fst.fst.subtype_val)).sub
          continuous_fst.snd.subtype_val.fst)

/-- **Math.** Joint continuity of the tensor derivative evaluations gives
joint continuity of the derivative support family on the identical index. -/
theorem continuous_finiteTensorSupportDerivative
    (g : RiemannianMetric I M) {k : ℕ} (s : Finset M) (K : M → Set M)
    (Y : ∀ p : M, Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x))) (R : M → ℝ)
      {D : ℝ → CovTensorField I M k},
      (∀ V : Fin k → SmoothVectorField I M,
        Continuous (fun z : ℝ × M => D z.1 V z.2)) →
      Continuous (fun qt : (Unit ⊕ Σ p : s, K p ×
        BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) × ℝ =>
          finiteTensorSupportDerivative g s K Y Z R (D qt.2) qt.1) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z R D hcont
  apply (Homeomorph.sumProdDistrib (X := Unit) (Y := Σ p : s, K p ×
    BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p))
      (Z := ℝ)).symm.comp_continuous_iff'.mp
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_const
  · apply (Homeomorph.sigmaProdDistrib (X := fun p : s => K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p))
        (Y := ℝ)).symm.comp_continuous_iff'.mp
    apply continuous_sigma
    intro p
    change Continuous (fun z : (K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) × ℝ =>
        ⟪z.1.2.1.2, tensorInSmoothFrame g p (Y p) (D z.2) z.1.1⟫_ℝ)
    exact continuous_fst.snd.subtype_val.snd.inner
      ((continuous_tensorInSmoothFrame g p (Y p) hcont).comp
        (continuous_snd.prodMk continuous_fst.fst.subtype_val))

/-- **Math.** The time derivative of each indexed support is the pairing with
the reconstructed tensor derivative at the same space and support index. -/
theorem hasDerivAt_finiteTensorSupportValue
    (g : RiemannianMetric I M) {k : ℕ} (s : Finset M) (K : M → Set M)
    (Y : ∀ p : M, Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x))) (R : M → ℝ)
      {A : ℝ → CovTensorField I M k} {D : CovTensorField I M k} {t : ℝ},
      (∀ (x : M) (V : Fin k → SmoothVectorField I M),
        HasDerivAt (fun r => A r V x) (D V x) t) →
      ∀ q : Unit ⊕ Σ p : s, K p ×
        BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p),
        HasDerivAt (fun r => finiteTensorSupportValue g s K Y Z R (A r) q)
          (finiteTensorSupportDerivative g s K Y Z R D q) t := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z R A D t hderiv q
  cases q with
  | inl _ => exact hasDerivAt_const t 0
  | inr q =>
      change HasDerivAt (fun r =>
        ⟪q.2.2.1.2, tensorInSmoothFrame g q.1 (Y q.1) (A r) q.2.1 - q.2.2.1.1⟫_ℝ)
          ⟪q.2.2.1.2, tensorInSmoothFrame g q.1 (Y q.1) D q.2.1⟫_ℝ t
      exact (innerSL ℝ q.2.2.1.2).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_tensorInSmoothFrame g q.1 q.2.1 (Y q.1)
          (hderiv q.2.1)).sub_const q.2.2.1.1)

/-- **Math.** Compact patches and closed convex carriers give a compact finite
support index space after bounding the contact-point norms. -/
theorem compactSpace_finiteTensorSupportIndex
    (g : RiemannianMetric I M) {k : ℕ} (s : Finset M) (K : M → Set M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x))) (R : M → ℝ),
      (∀ p, IsCompact (K p)) → (∀ p, IsClosed (Z p)) →
      CompactSpace (Unit ⊕ Σ p : s, K p ×
        BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z R hK hZ
  letI (p : s) : CompactSpace (K p) := isCompact_iff_compactSpace.mp (hK p)
  letI (p : s) : CompactSpace
      (BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p)) :=
    compactSpace_boundedConvexSupportPair _ _
      ((hZ p).preimage hilbertCovariantTensorEquiv.continuous)
  infer_instance

end MorganTianLib

#print axioms MorganTianLib.continuous_finiteTensorSupportValue
#print axioms MorganTianLib.continuous_finiteTensorSupportDerivative
#print axioms MorganTianLib.hasDerivAt_finiteTensorSupportValue
#print axioms MorganTianLib.compactSpace_finiteTensorSupportIndex
