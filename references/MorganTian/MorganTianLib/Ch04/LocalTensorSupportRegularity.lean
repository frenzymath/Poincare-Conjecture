import MorganTianLib.Ch04.LocalTransportField
import MorganTianLib.Ch04.TensorFieldFiber

/-!
# Smooth scalar supports from canonical tensor transport

The Hilbert pairing of a fixed support normal with a transported smooth
tensor is a finite contraction in a transported orthonormal basis. Smooth
vector fields realizing that same transport therefore give a smooth scalar
with the required support germ.

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

/-- **Math.** A support scalarization of a smooth tensor by canonical
Levi-Civita transport has a globally smooth representative near the centre. -/
theorem exists_contMDiff_localLeviCivitaTensor_support_germ
    (g : RiemannianMetric I M) (p : M) {U : Set M} (hpU : p ∈ U)
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x)
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ N B : HilbertCovariantTensor k (TangentSpace I p),
      ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
        ∀ᶠ x in 𝓝 p, ∀ hx : x ∈ U,
          f x = ⟪N, WithLp.toLp 2
            (covariantTensorTransportEquiv k
              (localLeviCivitaTangentTransport g p hC ⟨x, hx⟩).symm
                (hA.toFiber g x)) - B⟫_ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro N B
  let b := stdOrthonormalBasis ℝ (TangentSpace I p)
  obtain ⟨Y, _, hY⟩ := exists_smoothVectorFieldFamily_localLeviCivitaTangentTransport
    g p hpU hC b
  let f : M → ℝ := fun x =>
    (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
      N.ofLp (fun j => b (a j)) * A (fun j => Y (a j)) x) - ⟪N, B⟫_ℝ
  refine ⟨f, ?_, ?_⟩
  · exact (contMDiff_finsetSum (fun a _ =>
      contMDiff_const.mul (hA.contMDiff_eval (fun j => Y (a j))))).sub contMDiff_const
  · filter_upwards [hY] with x hxY
    intro hx
    rw [inner_sub_right, hilbertCovariantTensor_inner_eq b]
    change (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
      N.ofLp (fun j => b (a j)) * A (fun j => Y (a j)) x) - _ = _
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp only [covariantTensorTransportEquiv_apply_apply, LinearIsometryEquiv.symm_symm]
    congr 1
    rw [← hA.toFiber_apply g x (fun j => Y (a j))]
    congr 1
    funext j
    exact hxY hx (a j)

/-- **Math.** At an exterior local maximum of intrinsic tensor distance,
parallel invariance produces an active support represented by a smooth
scalar with a local maximum. Its germ is the actual transported support. -/
theorem exists_contMDiff_localLeviCivitaTensor_support
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
      ∃ U : Set M, IsOpen U ∧ ∃ _hpU : p ∈ U,
        ∃ hC : ∀ x ∈ U,
          ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
          localTransportCurve (I := I) p x 0 = p ∧
          localTransportCurve (I := I) p x 1 = x,
          ∃ (q : ConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p)) (f : M → ℝ),
            ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ IsLocalMax f p ∧
            f p = Metric.infDist (hA.toHilbertFiber g p)
              (hilbertCovariantTensorEquiv ⁻¹' Z p) ∧
            ∀ᶠ x in 𝓝 p, ∀ hx : x ∈ U,
              f x = ⟪q.1.2, WithLp.toLp 2
                (covariantTensorTransportEquiv k
                  (localLeviCivitaTangentTransport g p hC ⟨x, hx⟩).symm
                    (hA.toFiber g x)) - q.1.1⟫_ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z hne hclosed hconv hparallel hout hmax
  obtain ⟨U, hU, hpU, hC, _, q, hq, hqmax⟩ :=
    exists_local_leviCivitaTensor_support g k p Z (hA.toFiber g)
      hne hclosed hconv hparallel hout hmax
  obtain ⟨f, hf, hfeq⟩ := exists_contMDiff_localLeviCivitaTensor_support_germ
    g p hpU hC hA q.1.2 q.1.1
  have hfp := hfeq.self_of_nhds hpU
  refine ⟨U, hU, hpU, hC, q, f, hf, ?_, hfp.trans hq, hfeq⟩
  change ∀ᶠ x in 𝓝 (⟨p, hpU⟩ : U), _ ≤ _ at hqmax
  rw [nhds_subtype_eq_comap] at hqmax
  have hm := Filter.eventually_comap.mp hqmax
  filter_upwards [hm, hU.mem_nhds hpU, hfeq] with x hxmax hxU hxEq
  rw [hxEq hxU, hfp]
  exact hxmax ⟨x, hxU⟩ rfl

end MorganTianLib
