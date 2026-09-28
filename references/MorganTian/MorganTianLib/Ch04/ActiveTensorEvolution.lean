import MorganTianLib.Ch04.TensorRoughLaplacianFiber
import MorganTianLib.Ch04.TensorFiberEvolution
import MorganTianLib.Ch04.ActiveSupportNormal
import MorganTianLib.Ch04.HamiltonMaximumLocalReaction

/-!
# Evolution at active tensor supports

At an exterior spatial maximum of distance from a parallel-invariant convex
carrier, every active normal pairs nonpositively with the actual rough
Laplacian. The tensor PDE therefore bounds the time derivative of every
active support by the reaction Lipschitz constant times this distance.

This is a pointwise producer for the compact envelope comparison, for the
fixed metric in Morgan--Tian's global tensor maximum principle.
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

/-- **Math.** Every active unit normal, not just the one selected by the
spatial support construction, has nonpositive rough-Laplacian pairing. -/
theorem tensorHilbert_roughLaplacian_nonpos_of_active
    (g : RiemannianMetric I M) (p : M)
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x)),
      (Z p).Nonempty → IsClosed (Z p) → Convex ℝ (Z p) →
      parallelInvariantFiberSet Z (leviCivitaCovariantTensorTransports g k) →
      hA.toFiber g p ∉ Z p →
      IsLocalMax (fun x => Metric.infDist (hA.toHilbertFiber g x)
        (hilbertCovariantTensorEquiv ⁻¹' Z x)) p →
      ∀ q : ConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p),
        ⟪q.1.2, hA.toHilbertFiber g p - q.1.1⟫_ℝ =
          Metric.infDist (hA.toHilbertFiber g p) (hilbertCovariantTensorEquiv ⁻¹' Z p) →
        ⟪q.1.2, hA.roughLaplacianHilbertFiber g g.leviCivitaConnection p⟫_ℝ ≤ 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z hne hclosed hconv hparallel hout hmax q hq
  obtain ⟨q₀, hq₀, hlap⟩ :=
    exists_localLeviCivitaTensor_support_roughLaplacianHilbertFiber_nonpos
      g p hA Z hne hclosed hconv hparallel hout hmax
  have hne' : (hilbertCovariantTensorEquiv ⁻¹' Z p).Nonempty := by
    obtain ⟨B, hB⟩ := hne
    exact ⟨WithLp.toLp 2 B, hB⟩
  have hnormal := convexSupportPair_normal_eq_of_active hne'
    (hclosed.preimage hilbertCovariantTensorEquiv.continuous)
    (hconv.linear_preimage hilbertCovariantTensorEquiv.toLinearMap)
    hout q q₀ hq hq₀
  rwa [hnormal]

/-- **Math.** The evaluated tensor heat-reaction equation gives the time
derivative of the actual tensor fibre, with the intrinsic rough Laplacian. -/
theorem hasDerivAt_tensorHilbertFiber_of_roughLaplacian
    (g : RiemannianMetric I M) (p : M)
    {k : ℕ} {A : ℝ → CovTensorField I M k}
    (hA : ∀ t, IsCovariantTensorField (A t)) {t : ℝ} :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ R : HilbertCovariantTensor k (TangentSpace I p),
      (∀ Y : Fin k → SmoothVectorField I M,
        HasDerivAt (fun s => A s Y p)
          (roughLaplacian g g.leviCivitaConnection (A t) Y p +
            R.ofLp (fun j => Y j p)) t) →
      HasDerivAt (fun s => (hA s).toHilbertFiber g p)
        ((hA t).roughLaplacianHilbertFiber g g.leviCivitaConnection p + R) t := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro R hPDE
  apply hasDerivAt_tensorHilbertFiber_of_evaluations g p hA
  intro Y
  simpa only [WithLp.ofLp_add, add_apply,
    IsCovariantTensorField.roughLaplacianHilbertFiber_apply] using hPDE Y

/-- **Math.** At a positive spatial distance maximum, every active support
of a tensor heat-reaction solution has time derivative at most `K` times
the distance to the parallel-invariant convex carrier. The reaction need
only be Lipschitz on a projection-closed region containing the tensor value. -/
theorem tensorHilbertSupport_deriv_le_of_active
    (g : RiemannianMetric I M) (p : M)
    {k : ℕ} {A : ℝ → CovTensorField I M k}
    (hA : ∀ t, IsCovariantTensorField (A t)) {t : ℝ} :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x)))
      (ψ : HilbertCovariantTensor k (TangentSpace I p) →
        HilbertCovariantTensor k (TangentSpace I p)) (K : ℝ≥0)
      (S : Set (HilbertCovariantTensor k (TangentSpace I p)))
      (hne : (Z p).Nonempty) (hclosed : IsClosed (Z p)) (hconv : Convex ℝ (Z p)),
      parallelInvariantFiberSet Z (leviCivitaCovariantTensorTransports g k) →
      vectorFieldPreservesConvexSet (hilbertCovariantTensorEquiv ⁻¹' Z p) ψ →
      LipschitzOnWith K ψ S →
      (∀ w ∈ S, convexProjection (hilbertCovariantTensorEquiv ⁻¹' Z p)
        ⟨WithLp.toLp 2 hne.choose, hne.choose_spec⟩
        (hclosed.preimage hilbertCovariantTensorEquiv.continuous)
        (hconv.linear_preimage hilbertCovariantTensorEquiv.toLinearMap) w ∈ S) →
      (hA t).toHilbertFiber g p ∈ S →
      (∀ Y : Fin k → SmoothVectorField I M,
        HasDerivAt (fun s => A s Y p)
          (roughLaplacian g g.leviCivitaConnection (A t) Y p +
            (ψ ((hA t).toHilbertFiber g p)).ofLp (fun j => Y j p)) t) →
      (hA t).toFiber g p ∉ Z p →
      IsLocalMax (fun x => Metric.infDist ((hA t).toHilbertFiber g x)
        (hilbertCovariantTensorEquiv ⁻¹' Z x)) p →
      ∀ q : ConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p),
        ⟪q.1.2, (hA t).toHilbertFiber g p - q.1.1⟫_ℝ =
          Metric.infDist ((hA t).toHilbertFiber g p)
            (hilbertCovariantTensorEquiv ⁻¹' Z p) →
        deriv (fun s => ⟪q.1.2, (hA s).toHilbertFiber g p - q.1.1⟫_ℝ) t ≤
          (K : ℝ) * Metric.infDist ((hA t).toHilbertFiber g p)
            (hilbertCovariantTensorEquiv ⁻¹' Z p) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z ψ K S hne hclosed hconv hparallel hpres hψ hproj hv hPDE hout hmax q hq
  have htime := hasDerivAt_tensorHilbertFiber_of_roughLaplacian
    g p hA (ψ ((hA t).toHilbertFiber g p)) hPDE
  have hsupport := (innerSL ℝ q.1.2).hasFDerivAt.comp_hasDerivAt t
    (htime.sub_const q.1.1)
  simp only [Function.comp_def, innerSL_apply_apply] at hsupport
  rw [hsupport.deriv, inner_add_right]
  have hlap := tensorHilbert_roughLaplacian_nonpos_of_active g p (hA t) Z
    hne hclosed hconv hparallel hout hmax q hq
  have hne' : (hilbertCovariantTensorEquiv ⁻¹' Z p).Nonempty := by
    obtain ⟨B, hB⟩ := hne
    exact ⟨WithLp.toLp 2 B, hB⟩
  have hreact := convexSupportPair_reaction_bound_of_lipschitzOnWith hne'
    (hclosed.preimage hilbertCovariantTensorEquiv.continuous)
    (hconv.linear_preimage hilbertCovariantTensorEquiv.toLinearMap)
    hpres hψ hproj hv q hq
  linarith

end MorganTianLib

#print axioms MorganTianLib.tensorHilbert_roughLaplacian_nonpos_of_active
#print axioms MorganTianLib.hasDerivAt_tensorHilbertFiber_of_roughLaplacian
#print axioms MorganTianLib.tensorHilbertSupport_deriv_le_of_active
