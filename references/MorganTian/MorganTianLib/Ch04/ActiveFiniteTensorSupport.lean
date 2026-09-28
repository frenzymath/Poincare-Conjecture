import MorganTianLib.Ch04.ActiveTensorEvolution
import MorganTianLib.Ch04.CompactTensorEnvelope
import MorganTianLib.Ch04.ConvexSupportTransport

/-!
# The tensor PDE at finite support maxima

A support pair in a compact frame patch is transported to the actual tensor
fibre by one time-independent isometry. The scalar trajectories agree, so
the intrinsic tensor PDE estimate bounds the derivative of the indexed support.

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
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A time-independent transported frame carries the actual tensor PDE bound
to every active support in that frame. The derivative tensor only needs the
evaluated time derivative property. -/
theorem tensorInSmoothFrame_support_derivative_le_of_active
    (g : RiemannianMetric I M) (p x : M) {k : ℕ}
    (Y : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M)
    {A : ℝ → CovTensorField I M k} (hA : ∀ t, IsCovariantTensorField (A t))
    {D : CovTensorField I M k} {t : ℝ}
    (hderiv : ∀ V : Fin k → SmoothVectorField I M,
      HasDerivAt (fun r => A r V x) (D V x) t) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ z : M, Set (CovariantTensorFiber k (TangentSpace I z)))
      (hne : ∀ z, (Z z).Nonempty) (hclosed : ∀ z, IsClosed (Z z))
      (hconv : ∀ z, Convex ℝ (Z z))
      (ψ : HilbertCovariantTensor k (TangentSpace I x) →
        HilbertCovariantTensor k (TangentSpace I x)) (C : ℝ≥0)
      (S : Set (HilbertCovariantTensor k (TangentSpace I x))),
      parallelInvariantFiberSet Z (leviCivitaCovariantTensorTransports g k) →
      vectorFieldPreservesConvexSet (hilbertCovariantTensorEquiv ⁻¹' Z x) ψ →
      LipschitzOnWith C ψ S →
      (∀ w ∈ S, convexProjection (hilbertCovariantTensorEquiv ⁻¹' Z x)
        ⟨WithLp.toLp 2 (hne x).choose, (hne x).choose_spec⟩
        ((hclosed x).preimage hilbertCovariantTensorEquiv.continuous)
        ((hconv x).linear_preimage hilbertCovariantTensorEquiv.toLinearMap) w ∈ S) →
      (hA t).toHilbertFiber g x ∈ S →
      (∀ V : Fin k → SmoothVectorField I M,
        HasDerivAt (fun r => A r V x)
          (roughLaplacian g g.leviCivitaConnection (A t) V x +
            (ψ ((hA t).toHilbertFiber g x)).ofLp (fun j => V j x)) t) →
      (∃ e : TangentSpace I p ≃ₗᵢ[ℝ] TangentSpace I x,
        (covariantTensorTransportEquiv k e).toLinearEquiv ∈
          leviCivitaCovariantTensorTransports g k p x ∧
        ∀ r, tensorInSmoothFrame g p Y (A r) x =
          hilbertCovariantTensorTransportEquiv k e.symm ((hA r).toHilbertFiber g x)) →
      (hA t).toFiber g x ∉ Z x →
      IsLocalMax (fun z => Metric.infDist ((hA t).toHilbertFiber g z)
        (hilbertCovariantTensorEquiv ⁻¹' Z z)) x →
      ∀ q : ConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p),
        ⟪q.1.2, tensorInSmoothFrame g p Y (A t) x - q.1.1⟫_ℝ =
          Metric.infDist ((hA t).toHilbertFiber g x)
            (hilbertCovariantTensorEquiv ⁻¹' Z x) →
        ⟪q.1.2, tensorInSmoothFrame g p Y D x⟫_ℝ ≤
          (C : ℝ) * Metric.infDist ((hA t).toHilbertFiber g x)
            (hilbertCovariantTensorEquiv ⁻¹' Z x) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z hne hclosed hconv ψ C S hparallel hpres hψ hproj hv hPDE hframe hout hmax q hq
  obtain ⟨e, he, hrep⟩ := hframe
  let T := hilbertCovariantTensorTransportEquiv k e.symm
  have hT : T '' (hilbertCovariantTensorEquiv ⁻¹' Z x) =
      hilbertCovariantTensorEquiv ⁻¹' Z p := by
    rw [hilbertCovariantTensorTransportEquiv_image_preimage]
    congr 1
    have hforward := hparallel p x (covariantTensorTransportEquiv k e).toLinearEquiv he
    rw [← covariantTensorTransportEquiv_symm, ← hforward]
    exact (covariantTensorTransportEquiv k e).toEquiv.symm_image_image (Z p)
  have hTinv : T.symm '' (hilbertCovariantTensorEquiv ⁻¹' Z p) =
      hilbertCovariantTensorEquiv ⁻¹' Z x := by
    rw [← hT]
    exact T.toEquiv.symm_image_image _
  let qx := q.map T.symm hTinv
  have heval (r : ℝ) :
      ⟪qx.1.2, (hA r).toHilbertFiber g x - qx.1.1⟫_ℝ =
        ⟪q.1.2, tensorInSmoothFrame g p Y (A r) x - q.1.1⟫_ℝ := by
    rw [hrep r]
    simpa only [T.symm_apply_apply] using q.map_eval T.symm hTinv
      (T ((hA r).toHilbertFiber g x))
  have hbound := tensorHilbertSupport_deriv_le_of_active g x hA Z ψ C S
    (hne x) (hclosed x) (hconv x) hparallel hpres hψ hproj hv hPDE hout hmax qx
    ((heval t).trans hq)
  have htime := (innerSL ℝ q.1.2).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_tensorInSmoothFrame g p x Y hderiv).sub_const q.1.1)
  simp only [Function.comp_def, innerSL_apply_apply] at htime
  have hfun : (fun r => ⟪qx.1.2, (hA r).toHilbertFiber g x - qx.1.1⟫_ℝ) =
      (fun r => ⟪q.1.2, tensorInSmoothFrame g p Y (A r) x - q.1.1⟫_ℝ) := funext heval
  rw [hfun, htime.deriv] at hbound
  exact hbound

variable [CompactSpace M]

/-- **Math.** Every positive maximizer of the finite tensor support envelope
satisfies the reaction bound coming from the geometric tensor PDE. -/
theorem finiteTensorSupportDerivative_le_of_positive_max
    (g : RiemannianMetric I M) {k : ℕ} (s : Finset M) (K : M → Set M)
    (Y : ∀ p : M, Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M)
    {A : ℝ → CovTensorField I M k} (hA : ∀ t, IsCovariantTensorField (A t))
    (hcont : ∀ V : Fin k → SmoothVectorField I M,
      Continuous (fun z : ℝ × M => A z.1 V z.2))
    {D : CovTensorField I M k} {t : ℝ}
    (hderiv : ∀ (x : M) (V : Fin k → SmoothVectorField I M),
      HasDerivAt (fun r => A r V x) (D V x) t) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x)))
      (R : M → ℝ) (hne : ∀ x, (Z x).Nonempty)
      (hclosed : ∀ x, IsClosed (Z x)) (hconv : ∀ x, Convex ℝ (Z x))
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
      (∀ x, (hA t).toHilbertFiber g x ∈ S x) →
      (∀ (x : M) (V : Fin k → SmoothVectorField I M),
        HasDerivAt (fun r => A r V x)
          (roughLaplacian g g.leviCivitaConnection (A t) V x +
            (ψ x ((hA t).toHilbertFiber g x)).ofLp (fun j => V j x)) t) →
      (∀ p x, x ∈ K p → ∃ e : TangentSpace I p ≃ₗᵢ[ℝ] TangentSpace I x,
        (covariantTensorTransportEquiv k e).toLinearEquiv ∈
          leviCivitaCovariantTensorTransports g k p x ∧
        ∀ r, tensorInSmoothFrame g p (Y p) (A r) x =
          hilbertCovariantTensorTransportEquiv k e.symm ((hA r).toHilbertFiber g x)) →
      let F := fun q => finiteTensorSupportValue g s K Y Z R (A t) q
      (⨆ q, F q) = (⨆ x : M, Metric.infDist ((hA t).toHilbertFiber g x)
        (hilbertCovariantTensorEquiv ⁻¹' Z x)) →
      0 < (⨆ q, F q) → ∀ q, F q = (⨆ r, F r) →
        finiteTensorSupportDerivative g s K Y Z R D q ≤ (C : ℝ) * (⨆ r, F r) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z R hne hclosed hconv ψ C S hparallel hpres hψ hproj hv hPDE hframe F hsup hpos q hq
  let d : M → ℝ := fun x => Metric.infDist ((hA t).toHilbertFiber g x)
    (hilbertCovariantTensorEquiv ⁻¹' Z x)
  have hd : Continuous d :=
    (continuous_tensorHilbertFiber_infDist (I := I) (M := M) (A := A) g hA hcont Z hparallel).comp
      (f := fun x : M => (t, x)) (continuous_const.prodMk continuous_id)
  have hdb : BddAbove (range d) := isCompact_range hd |>.bddAbove
  cases q with
  | inl z =>
    have hz : F (Sum.inl z) = 0 := rfl
    rw [← hq, hz] at hpos
    exact (lt_irrefl 0 hpos).elim
  | inr q =>
    rcases q with ⟨⟨p, hp⟩, ⟨x, hx⟩, q⟩
    let r := (⟨⟨p, hp⟩, ⟨x, hx⟩, q⟩ : Σ p : s, K p ×
      BoundedConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p))
    let qp := boundedPairSupport (hilbertCovariantTensorEquiv ⁻¹' Z p) (R p) q
    obtain ⟨e, he, hrep⟩ := hframe p x hx
    have hT : hilbertCovariantTensorTransportEquiv k e.symm ''
        (hilbertCovariantTensorEquiv ⁻¹' Z x) =
          hilbertCovariantTensorEquiv ⁻¹' Z p := by
      rw [hilbertCovariantTensorTransportEquiv_image_preimage]
      congr 1
      have hforward := hparallel p x (covariantTensorTransportEquiv k e).toLinearEquiv he
      rw [← covariantTensorTransportEquiv_symm, ← hforward]
      exact (covariantTensorTransportEquiv k e).toEquiv.symm_image_image (Z p)
    have hdist : Metric.infDist (tensorInSmoothFrame g p (Y p) (A t) x)
        (hilbertCovariantTensorEquiv ⁻¹' Z p) = d x := by
      rw [hrep t]
      exact infDist_transport_eq (hilbertCovariantTensorTransportEquiv k e.symm) hT
        ((hA t).toHilbertFiber g x)
    have hle : F (Sum.inr r) ≤ d x := by
      have h := convexSupportPair_eval_le_infDist _
        ⟨WithLp.toLp 2 (hne p).choose, (hne p).choose_spec⟩
        ((hclosed p).preimage hilbertCovariantTensorEquiv.continuous)
        ((hconv p).linear_preimage hilbertCovariantTensorEquiv.toLinearMap) qp
        (tensorInSmoothFrame g p (Y p) (A t) x)
      exact h.trans_eq hdist
    have hactive : F (Sum.inr r) = d x := by
      apply le_antisymm hle
      rw [hq, hsup]
      exact le_ciSup hdb x
    have hdmax : d x = ⨆ z : M, d z := hactive.symm.trans (hq.trans hsup)
    have hout : (hA t).toFiber g x ∉ Z x := by
      intro hz
      have hzero : d x = 0 := Metric.infDist_zero_of_mem hz
      rw [← hq, hactive, hzero] at hpos
      exact lt_irrefl 0 hpos
    have hmax : IsLocalMax d x := Filter.Eventually.of_forall fun z => by
      change d z ≤ d x
      rw [hdmax]
      exact le_ciSup hdb z
    have hbound := tensorInSmoothFrame_support_derivative_le_of_active
      g p x (Y p) hA (hderiv x) Z hne hclosed hconv
      (ψ x) C (S x) hparallel (hpres x) (hψ x) (hproj x)
      (hv x) (hPDE x) ⟨e, he, hrep⟩ hout hmax qp hactive
    change finiteTensorSupportDerivative g s K Y Z R D (Sum.inr r) ≤
      (C : ℝ) * d x at hbound
    rwa [← hactive, hq] at hbound

end MorganTianLib

#print axioms MorganTianLib.tensorInSmoothFrame_support_derivative_le_of_active
#print axioms MorganTianLib.finiteTensorSupportDerivative_le_of_positive_max
