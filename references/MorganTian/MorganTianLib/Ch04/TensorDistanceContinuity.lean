import MorganTianLib.Ch04.LeviCivitaTensorTransport
import MorganTianLib.Ch04.LocalTensorSupportFamily

/-!
# Continuity of intrinsic tensor distance

Canonical Levi-Civita transport preserves the distance of a tensor to a
parallel-invariant carrier. Local continuous transported tensor families
therefore prove joint continuity of the intrinsic distance.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Transport to the centre along the canonical local Levi-Civita
curves preserves intrinsic distance to a parallel-invariant tensor carrier. -/
theorem infDist_localLeviCivitaTensorTransport
    (g : RiemannianMetric I M) (k : ℕ) (p : M) {U : Set M}
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x)),
      parallelInvariantFiberSet Z (leviCivitaCovariantTensorTransports g k) →
      ∀ (x : U) (B : HilbertCovariantTensor k (TangentSpace I (x : M))),
        Metric.infDist (hilbertCovariantTensorTransportEquiv k
            (localLeviCivitaTangentTransport g p hC x).symm B)
          (hilbertCovariantTensorEquiv ⁻¹' Z p) =
        Metric.infDist B (hilbertCovariantTensorEquiv ⁻¹' Z x) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z hparallel x B
  let e := localLeviCivitaTangentTransport g p hC x
  have hmem : (covariantTensorTransportEquiv k e).toLinearEquiv ∈
      leviCivitaCovariantTensorTransports g k p x :=
    parallelTransportTangentBetween_mem g k (by norm_num : (0 : ℝ) < 1)
      (hC x x.property).1 (hC x x.property).2.1 (hC x x.property).2.2
  have hforward : covariantTensorTransportEquiv k e '' Z p = Z x :=
    hparallel p x (covariantTensorTransportEquiv k e).toLinearEquiv hmem
  have hinverse : covariantTensorTransportEquiv k e.symm '' Z x = Z p := by
    rw [← covariantTensorTransportEquiv_symm, ← hforward]
    exact (covariantTensorTransportEquiv k e).toEquiv.symm_image_image (Z p)
  apply infDist_transport_eq
  rw [hilbertCovariantTensorTransportEquiv_image_preimage, hinverse]

/-- **Math.** Joint continuity of smooth tensor evaluations implies joint
continuity of the intrinsic distance to a parallel-invariant carrier. -/
theorem continuous_tensorHilbertFiber_infDist
    (g : RiemannianMetric I M)
    {T : Type*} [TopologicalSpace T] {k : ℕ} {A : T → CovTensorField I M k}
    (hA : ∀ t, IsCovariantTensorField (A t))
    (hcont : ∀ Y : Fin k → SmoothVectorField I M,
      Continuous (fun z : T × M => A z.1 Y z.2)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x)),
      parallelInvariantFiberSet Z (leviCivitaCovariantTensorTransports g k) →
      Continuous (fun z : T × M => Metric.infDist ((hA z.1).toHilbertFiber g z.2)
        (hilbertCovariantTensorEquiv ⁻¹' Z z.2)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z hparallel
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, p⟩
  obtain ⟨U, hU, hpU, hC, _⟩ := exists_local_leviCivitaTangentTransport g k p
  obtain ⟨V, hV, hpV, hVU, F, hF, hFeq⟩ :=
    exists_continuous_localLeviCivitaTensor_family g p hU hpU hC hA hcont
  have hD : Continuous (fun z : T × M =>
      Metric.infDist (F z.1 z.2) (hilbertCovariantTensorEquiv ⁻¹' Z p)) :=
    (Metric.continuous_infDist_pt _).comp hF
  apply hD.continuousAt.congr
  have hnear : ∀ᶠ z : T × M in 𝓝 (t, p), z.2 ∈ V :=
    continuous_snd.continuousAt.preimage_mem_nhds (hV.mem_nhds hpV)
  filter_upwards [hnear] with z hz
  rw [hFeq z.1 z.2 hz]
  exact infDist_localLeviCivitaTensorTransport g k p hC Z hparallel
    ⟨z.2, hVU hz⟩ ((hA z.1).toHilbertFiber g z.2)

/-- **Math.** The intrinsic Hilbert norm of a family of smooth tensors is
jointly continuous when all of its smooth evaluations are jointly continuous. -/
theorem continuous_tensorHilbertFiber_norm
    (g : RiemannianMetric I M)
    {T : Type*} [TopologicalSpace T] {k : ℕ} {A : T → CovTensorField I M k}
    (hA : ∀ t, IsCovariantTensorField (A t))
    (hcont : ∀ Y : Fin k → SmoothVectorField I M,
      Continuous (fun z : T × M => A z.1 Y z.2)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Continuous (fun z : T × M => ‖(hA z.1).toHilbertFiber g z.2‖) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hparallel : parallelInvariantFiberSet
      (fun x : M => ({0} : Set (CovariantTensorFiber k (TangentSpace I x))))
      (leviCivitaCovariantTensorTransports g k) := by
    intro x y e _
    simp
  have hdist := continuous_tensorHilbertFiber_infDist g hA hcont _ hparallel
  convert hdist using 1
  funext z
  have hzero : hilbertCovariantTensorEquiv ⁻¹'
      ({0} : Set (CovariantTensorFiber k (TangentSpace I z.2))) =
      ({0} : Set (HilbertCovariantTensor k (TangentSpace I z.2))) := by
    ext B
    simp
  rw [hzero, Metric.infDist_singleton, dist_zero_right]

end MorganTianLib

#print axioms MorganTianLib.infDist_localLeviCivitaTensorTransport
#print axioms MorganTianLib.continuous_tensorHilbertFiber_infDist
#print axioms MorganTianLib.continuous_tensorHilbertFiber_norm
