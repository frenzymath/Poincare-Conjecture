import MorganTianLib.Ch04.ConvexSupport
import Mathlib.Topology.Order.LocalExtr

/-!
# Local support maxima through carrier-preserving isometries

An isometry carrying each fiber carrier to one fixed closed convex set
preserves distance to that carrier. An active supporting functional at a
maximum of the intrinsic distance then has a scalar local maximum after
transport. The isometries and their carrier-preservation property remain
explicit inputs. This file constructs neither Levi--Civita transports nor
the derivative identities needed to identify a rough Laplacian.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace MorganTianLib

section Distance

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Math.** A carrier-preserving linear isometry preserves distance to the
carrier, with no closedness or nonemptiness requirement. -/
theorem infDist_transport_eq (e : V ≃ₗᵢ[ℝ] W)
    {Z : Set V} {Z₀ : Set W} (he : e '' Z = Z₀) (v : V) :
    Metric.infDist (e v) Z₀ = Metric.infDist v Z := by
  rw [← he]
  exact Metric.infDist_image e.isometry

end Distance

section Support

variable {X E : Type*} {F : X → Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℝ (F x)]

/-- **Math.** An active supporting functional has a scalar maximum wherever
the intrinsic distance to the fiber carrier has a maximum. Only carrier
preservation on the specified set is needed. The active pair is based at
the transported value at `p`, so no normalization of `e p` is required. -/
theorem isMaxOn_transportedSupport_of_isMaxOn_infDist
    (Z : ∀ x, Set (F x)) {Z₀ : Set E}
    (hZne : Z₀.Nonempty) (hZclosed : IsClosed Z₀) (hZconv : Convex ℝ Z₀)
    (e : ∀ x, F x ≃ₗᵢ[ℝ] E) (u : ∀ x, F x)
    {U : Set X} {p : X} (hp : p ∈ U)
    (he : ∀ x ∈ U, e x '' Z x = Z₀)
    (q : ConvexSupportPair Z₀)
    (hq : ⟪q.1.2, e p (u p) - q.1.1⟫_ℝ = Metric.infDist (e p (u p)) Z₀)
    (hmax : IsMaxOn (fun x => Metric.infDist (u x) (Z x)) U p) :
    IsMaxOn (fun x => ⟪q.1.2, e x (u x) - q.1.1⟫_ℝ) U p := by
  intro x hx
  calc
    ⟪q.1.2, e x (u x) - q.1.1⟫_ℝ ≤ Metric.infDist (e x (u x)) Z₀ :=
      convexSupportPair_eval_le_infDist Z₀ hZne hZclosed hZconv q _
    _ = Metric.infDist (u x) (Z x) := infDist_transport_eq (e x) (he x hx) _
    _ ≤ Metric.infDist (u p) (Z p) := hmax hx
    _ = Metric.infDist (e p (u p)) Z₀ :=
      (infDist_transport_eq (e p) (he p hp) _).symm
    _ = ⟪q.1.2, e p (u p) - q.1.1⟫_ℝ := hq.symm

/-- **Math.** The support maximum is local when the distance maximum and
carrier-preserving transport laws hold on a neighborhood. No regularity of
the isometry family is needed for this order-theoretic contact statement. -/
theorem isLocalMax_transportedSupport_of_isLocalMax_infDist
    [TopologicalSpace X]
    (Z : ∀ x, Set (F x)) {Z₀ : Set E}
    (hZne : Z₀.Nonempty) (hZclosed : IsClosed Z₀) (hZconv : Convex ℝ Z₀)
    (e : ∀ x, F x ≃ₗᵢ[ℝ] E) (u : ∀ x, F x)
    (p : X) (he : ∀ᶠ x in 𝓝 p, e x '' Z x = Z₀)
    (q : ConvexSupportPair Z₀)
    (hq : ⟪q.1.2, e p (u p) - q.1.1⟫_ℝ = Metric.infDist (e p (u p)) Z₀)
    (hmax : IsLocalMax (fun x => Metric.infDist (u x) (Z x)) p) :
    IsLocalMax (fun x => ⟪q.1.2, e x (u x) - q.1.1⟫_ℝ) p := by
  have hp : e p '' Z p = Z₀ := he.self_of_nhds
  filter_upwards [he, hmax] with x hx hxp
  calc
    ⟪q.1.2, e x (u x) - q.1.1⟫_ℝ ≤ Metric.infDist (e x (u x)) Z₀ :=
      convexSupportPair_eval_le_infDist Z₀ hZne hZclosed hZconv q _
    _ = Metric.infDist (u x) (Z x) := infDist_transport_eq (e x) hx _
    _ ≤ Metric.infDist (u p) (Z p) := hxp
    _ = Metric.infDist (e p (u p)) Z₀ :=
      (infDist_transport_eq (e p) hp _).symm
    _ = ⟪q.1.2, e p (u p) - q.1.1⟫_ℝ := hq.symm

/-- **Math.** At an exterior local maximum of intrinsic distance, the nearest
point and its unit supporting normal produce an active transported scalar
support with a local maximum. The isometry family remains geometric input. -/
theorem exists_transportedSupport_isLocalMax_of_isLocalMax_infDist
    [TopologicalSpace X]
    (Z : ∀ x, Set (F x)) {Z₀ : Set E}
    (hZne : Z₀.Nonempty) (hZclosed : IsClosed Z₀) (hZconv : Convex ℝ Z₀)
    (e : ∀ x, F x ≃ₗᵢ[ℝ] E) (u : ∀ x, F x)
    (p : X) (he : ∀ᶠ x in 𝓝 p, e x '' Z x = Z₀)
    (hp : u p ∉ Z p)
    (hmax : IsLocalMax (fun x => Metric.infDist (u x) (Z x)) p) :
    ∃ q : ConvexSupportPair Z₀,
      ⟪q.1.2, e p (u p) - q.1.1⟫_ℝ = Metric.infDist (u p) (Z p) ∧
      IsLocalMax (fun x => ⟪q.1.2, e x (u x) - q.1.1⟫_ℝ) p := by
  have hep : e p '' Z p = Z₀ := he.self_of_nhds
  have hpexterior : e p (u p) ∉ Z₀ := by
    rw [← hep]
    rintro ⟨v, hv, hveq⟩
    exact hp ((e p).injective hveq ▸ hv)
  let q := exteriorSupportPair Z₀ hZne hZclosed hZconv (e p (u p)) hpexterior
  have hq : ⟪q.1.2, e p (u p) - q.1.1⟫_ℝ = Metric.infDist (e p (u p)) Z₀ :=
    exteriorSupportPair_eval_eq_infDist Z₀ hZne hZclosed hZconv _ hpexterior
  refine ⟨q, ?_, ?_⟩
  · exact hq.trans (infDist_transport_eq (e p) hep _)
  · exact isLocalMax_transportedSupport_of_isLocalMax_infDist Z
      hZne hZclosed hZconv e u p he q hq hmax

end Support

end MorganTianLib
