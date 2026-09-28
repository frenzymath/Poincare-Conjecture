import MorganTianLib.Ch04.ConvexTransport
import MorganTianLib.Ch04.HamiltonMaximumBundle
import MorganTianLib.Ch04.HamiltonMaximumFiberwiseReaction

/-!
# Morgan--Tian Ch. 4 - reduction through declared parallel transports

This module connects the checked finite-dimensional Hamilton barrier to the
fiberwise carrier and reaction predicates from the source.  A chosen based
family of isometric frames is required to belong to a declared transport
family.  Parallel invariance then identifies the original fiber carrier with
one fixed model carrier, while tangent-cone functoriality transports the
fiberwise reaction condition automatically.

The final theorem remains a reduction theorem, not the source's geometric
global tensor maximum principle. Its universal fixed-frame maximum property
is a special-case assumption that need not hold for a curved connection.
The general geometric route uses locally transported active supporting
functionals, as in `TransportedSupport` and `TensorHilbertSupport`.
-/

open Filter Set Function
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace MorganTianLib

section TransportedCarrier

variable {X : Type*} {F : X → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℝ (F x)]

/-- Parallel invariance identifies every fiber carrier with the pullback of a
fixed based carrier along any chosen family of declared isometric transports. -/
theorem fiberSet_eq_frameCarrier_of_parallelInvariant
    (Z : FiberSet X F) (P : LinearTransportFamily F)
    (hZ : parallelInvariantFiberSet Z P)
    (x₀ : X) (e : FiberFrame (X := X) (E := F x₀) (F := F))
    (he : ∀ x, (e x).toLinearEquiv ∈ P x x₀) :
    Z = frameCarrier e (Z x₀) := by
  funext x
  ext v
  have himage : (e x).toLinearEquiv '' Z x = Z x₀ :=
    hZ x x₀ (e x).toLinearEquiv (he x)
  change v ∈ Z x ↔ e x v ∈ Z x₀
  constructor
  · intro hv
    rw [← himage]
    exact ⟨v, hv, rfl⟩
  · intro hv
    rw [← himage] at hv
    obtain ⟨w, hw, hwv⟩ := hv
    have : w = v := (e x).injective hwv
    simpa [this] using hw

/-- A fiberwise preserving reaction remains preserving after every based
isometric transport supplied by a parallel-invariant carrier. -/
theorem frameReaction_preserves_of_parallelInvariant
    (Z : FiberSet X F) (P : LinearTransportFamily F)
    (hZ : parallelInvariantFiberSet Z P)
    (x₀ : X) (e : FiberFrame (X := X) (E := F x₀) (F := F))
    (he : ∀ x, (e x).toLinearEquiv ∈ P x x₀)
    (ψ : FiberwiseVectorField F)
    (hψ : convexSubbundlePreservingVectorField Z ψ) :
    ∀ x, vectorFieldPreservesConvexSet (Z x₀) (frameReaction e ψ x) := by
  intro x
  have himage : (e x).toLinearEquiv '' Z x = Z x₀ :=
    hZ x x₀ (e x).toLinearEquiv (he x)
  have himage' : (e x).toContinuousLinearEquiv '' Z x = Z x₀ := by
    rw [← himage]
    ext v
    constructor <;> rintro ⟨w, hw, rfl⟩ <;> exact ⟨w, hw, rfl⟩
  have hpres := vectorFieldPreservesConvexSet_image
    (e x).toContinuousLinearEquiv (hψ x)
  rw [himage'] at hpres
  have hreac : frameReaction e ψ x =
      transportedVectorField (e x).toContinuousLinearEquiv (ψ x) := by
    funext v
    rfl
  rw [hreac]
  exact hpres

/-- The transported family inherits a common fiberwise Lipschitz constant. -/
theorem frameReaction_lipschitz
    (x₀ : X) (e : FiberFrame (X := X) (E := F x₀) (F := F))
    (ψ : FiberwiseVectorField F) {K : ℝ≥0}
    (hψ : ∀ x, LipschitzWith K (ψ x)) :
    ∀ x, LipschitzWith K (frameReaction e ψ x) := by
  intro x
  have hreac : frameReaction e ψ x =
      transportedVectorField (e x).toContinuousLinearEquiv (ψ x) := by
    funext v
    rfl
  rw [hreac]
  exact lipschitzWith_transportedVectorField (e x) (hψ x)

end TransportedCarrier

section BasedTransportPrinciple

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  {F : X → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℝ (F x)]
  [∀ x, FiniteDimensional ℝ (F x)]

/-- Hamilton's bounded finite-dimensional barrier reduced to an original
fiberwise carrier through a chosen based family of declared transports.

Unlike `hamilton_tensor_maximum_principle_of_parallel_frame`, the carrier and
reaction hypotheses are stated fiberwise.  Their model-coordinate versions
are consequences of parallel invariance and isometric conjugation rather than
extra assumptions. The operator maximum property remains an explicit
special-case restriction; it is not supplied by general Levi--Civita geometry.
-/
theorem hamilton_tensor_maximum_principle_of_based_transport_frame
    (Z : FiberSet X F) (hZclosed : fiberwiseClosed Z)
    (hZconv : fiberwiseConvex Z)
    (P : LinearTransportFamily F)
    (hZparallel : parallelInvariantFiberSet Z P)
    (x₀ : X) (e : FiberFrame (X := X) (E := F x₀) (F := F))
    (he : ∀ x, (e x).toLinearEquiv ∈ P x x₀)
    (ψ : FiberwiseVectorField F)
    (hψpres : convexSubbundlePreservingVectorField Z ψ)
    {K : ℝ≥0} (hψlip : ∀ x, LipschitzWith K (ψ x))
    (L : ℝ → (∀ x, F x) → ∀ x, F x)
    (hLmax : ∀ (t : ℝ) (f : X → F x₀) (n : F x₀) (x : X),
      IsMaxOn (fun y : X => ⟪n, f y⟫_ℝ) (univ : Set X) x →
        ⟪n, frameOperator e L t f x⟫_ℝ ≤ 0)
    (u : ∀ x, ℝ → F x) {a b : ℝ}
    (hpde : ∀ x s,
      HasDerivAt (u x)
        (L s (fun y => u y s) x + ψ x (u x s)) s)
    {B : ℝ} (hbound : ∀ x t, t ∈ Icc a b → ‖u x t‖ ≤ B)
    (hB0 : 0 ≤ B)
    (hF : Continuous ↿(hamiltonSupportValueFamily
      (X := X) (Z x₀) (fun x t => e x (u x t))))
    (hF' : Continuous ↿(hamiltonSupportDerivativeFamilyFiberwise
      (X := X) (Z x₀) (fun x t => e x (u x t))
        (frameOperator e L) (frameReaction e ψ)))
    (hinit : ∀ x, u x a ∈ Z x) :
    ∀ x t, t ∈ Icc a b → u x t ∈ Z x := by
  have hcarrier : Z = frameCarrier e (Z x₀) :=
    fiberSet_eq_frameCarrier_of_parallelInvariant Z P hZparallel x₀ e he
  have hinitModel : ∀ x, e x (u x a) ∈ Z x₀ := by
    intro x
    have hx : u x a ∈ frameCarrier e (Z x₀) x := by
      rw [← hcarrier]
      exact hinit x
    exact (mem_frameCarrier_iff e (Z x₀) x (u x a)).mp hx
  have hZne : (Z x₀).Nonempty := ⟨e x₀ (u x₀ a), hinitModel x₀⟩
  have hpresModel :
      ∀ x, vectorFieldPreservesConvexSet (Z x₀) (frameReaction e ψ x) :=
    frameReaction_preserves_of_parallelInvariant
      Z P hZparallel x₀ e he ψ hψpres
  have hlipModel : ∀ x, LipschitzWith K (frameReaction e ψ x) :=
    frameReaction_lipschitz x₀ e ψ hψlip
  have hpdeModel : ∀ x s,
      HasDerivAt (fun t => e x (u x t))
        (frameOperator e L s (fun y => e y (u y s)) x +
          frameReaction e ψ x (e x (u x s))) s := by
    intro x s
    have hc : HasDerivAt
        (fun _ : ℝ => (e x).toContinuousLinearEquiv.toContinuousLinearMap)
        0 s :=
      hasDerivAt_const (x := s)
        (c := (e x).toContinuousLinearEquiv.toContinuousLinearMap)
    have hh := hc.clm_apply (hpde x s)
    convert hh using 1
    · rfl
    · simp [frameOperator, frameReaction]
  have hboundModel : ∀ x t, t ∈ Icc a b → ‖e x (u x t)‖ ≤ B := by
    intro x t ht
    simpa using hbound x t ht
  have hmodel := hamilton_tensor_maximum_principle_bounded_fiberwise
    (X := X) (Z := Z x₀) hZne (hZclosed x₀) (hZconv x₀)
    hpresModel hlipModel (frameOperator e L) hLmax
    (fun x t => e x (u x t)) hpdeModel hboundModel hB0 hF hF' hinitModel
  intro x t ht
  rw [hcarrier]
  exact (mem_frameCarrier_iff e (Z x₀) x (u x t)).mpr (hmodel x t ht)

end BasedTransportPrinciple

end MorganTianLib
