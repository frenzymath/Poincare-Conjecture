import MorganTianLib.Ch04.TensorHilbert
import MorganTianLib.Ch04.TransportedSupport

/-!
# Supporting functionals for covariant tensor carriers

Closed convex carriers stated in the existing continuous multilinear tensor
fibres are carried to their Hilbert realization. Tangent isometries preserving
the original carriers then produce an active local scalar support maximum.
The local tangent isometries and their carrier preservation are inputs; their
construction from a connection and the support Laplacian identity remain open.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace MorganTianLib

variable {k : ℕ} {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Math.** Tensor transport commutes with realizing a carrier in its Hilbert norm. -/
theorem hilbertCovariantTensorTransportEquiv_image_preimage
    (e : V ≃ₗᵢ[ℝ] W) (Z : Set (CovariantTensorFiber k V)) :
    hilbertCovariantTensorTransportEquiv k e ''
        (hilbertCovariantTensorEquiv ⁻¹' Z) =
      hilbertCovariantTensorEquiv ⁻¹' (covariantTensorTransportEquiv k e '' Z) := by
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A.ofLp, hA, rfl⟩
  · rintro ⟨A, hA, hAB⟩
    refine ⟨WithLp.toLp 2 A, hA, ?_⟩
    exact WithLp.ofLp_injective 2 hAB

variable {X : Type*} [TopologicalSpace X] {F : X → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℝ (F x)]
  [∀ x, FiniteDimensional ℝ (F x)]

/-- **Math.** A local distance maximum for an actual covariant tensor section admits
an active scalar support after carrier-preserving tangent transport. The carrier
is specified in the original tensor representation; distance uses its Hilbert norm. -/
theorem exists_covariantTensor_support_isLocalMax
    (Z : ∀ x, Set (CovariantTensorFiber k (F x))) {Z₀ : Set (CovariantTensorFiber k V)}
    (hZne : Z₀.Nonempty) (hZclosed : IsClosed Z₀) (hZconv : Convex ℝ Z₀)
    (e : ∀ x, F x ≃ₗᵢ[ℝ] V) (u : ∀ x, CovariantTensorFiber k (F x))
    (p : X) (he : ∀ᶠ x in 𝓝 p, covariantTensorTransportEquiv k (e x) '' Z x = Z₀)
    (hp : u p ∉ Z p)
    (hmax : IsLocalMax (fun x => Metric.infDist (WithLp.toLp 2 (u x))
      (hilbertCovariantTensorEquiv ⁻¹' Z x)) p) :
    ∃ q : ConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z₀),
      ⟪q.1.2, WithLp.toLp 2 (covariantTensorTransportEquiv k (e p) (u p)) - q.1.1⟫_ℝ =
        Metric.infDist (WithLp.toLp 2 (u p)) (hilbertCovariantTensorEquiv ⁻¹' Z p) ∧
      IsLocalMax (fun x => ⟪q.1.2,
        WithLp.toLp 2 (covariantTensorTransportEquiv k (e x) (u x)) - q.1.1⟫_ℝ) p := by
  have hne : (hilbertCovariantTensorEquiv ⁻¹' Z₀).Nonempty := by
    obtain ⟨A, hA⟩ := hZne
    exact ⟨WithLp.toLp 2 A, hA⟩
  have hclosed : IsClosed (hilbertCovariantTensorEquiv ⁻¹' Z₀) :=
    hZclosed.preimage hilbertCovariantTensorEquiv.continuous
  have hconv : Convex ℝ (hilbertCovariantTensorEquiv ⁻¹' Z₀) :=
    hZconv.linear_preimage hilbertCovariantTensorEquiv.toLinearMap
  have htransport : ∀ᶠ x in 𝓝 p,
      hilbertCovariantTensorTransportEquiv k (e x) ''
        (hilbertCovariantTensorEquiv ⁻¹' Z x) = hilbertCovariantTensorEquiv ⁻¹' Z₀ := by
    filter_upwards [he] with x hx
    rw [hilbertCovariantTensorTransportEquiv_image_preimage, hx]
  exact exists_transportedSupport_isLocalMax_of_isLocalMax_infDist
    (fun x => hilbertCovariantTensorEquiv ⁻¹' Z x) hne hclosed hconv
    (fun x => hilbertCovariantTensorTransportEquiv k (e x))
    (fun x => WithLp.toLp 2 (u x)) p htransport hp hmax

end MorganTianLib
