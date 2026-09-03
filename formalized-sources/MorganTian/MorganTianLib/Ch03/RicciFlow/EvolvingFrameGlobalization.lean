import MorganTianLib.Ch03.RicciFlow.EvolvingFrameTransport

/-!
# Morgan--Tian Ch. 3 -- globalization of the evolving transport

The transport ODE is constructed fiberwise.  This module records the finite
dimensional algebraic step needed to regard each transported fiber map as an
automorphism: metric preservation gives injectivity, and finite dimensionality
upgrades it to surjectivity.
-/

open Set

noncomputable section

namespace MorganTianLib

/-! ## Pointwise automorphism consequences -/

/-- **Math.** A metric-preserving evolving transport is bijective at every
time on a positive compact interval when the initial metric is nondegenerate.
The only finite-dimensional input is equality of the domain and codomain
dimensions of the transport endomorphism.
-/
theorem EvolvingTransportData.bijective_of_initial_metric_nondegenerate
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {J : Set ℝ} {G : EvolvingMetricData V J}
    (P : EvolvingTransportData V J G)
    (hnd : ∀ v : V, G.metric 0 v v = 0 → v = 0)
    {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Function.Bijective (P.transport t) := by
  have hinj := P.injective_of_initial_metric_nondegenerate hnd hT ht
  have hinjL : Function.Injective ((P.transport t).toLinearMap) := hinj
  have hsurjL : Function.Surjective ((P.transport t).toLinearMap) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinjL
  exact ⟨hinj, hsurjL⟩

/-- **Math.** Package the pointwise evolving transport as a continuous linear
equivalence.  This is the fiberwise automorphism used by the bundle
globalization of the moving-frame construction.
-/
noncomputable def EvolvingTransportData.equivAt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {J : Set ℝ} {G : EvolvingMetricData V J}
    (P : EvolvingTransportData V J G)
    (hnd : ∀ v : V, G.metric 0 v v = 0 → v = 0)
    {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) : V ≃L[ℝ] V :=
  (LinearEquiv.ofBijective (P.transport t).toLinearMap
      (P.bijective_of_initial_metric_nondegenerate hnd hT ht)).toContinuousLinearEquiv

@[simp] theorem EvolvingTransportData.equivAt_apply
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {J : Set ℝ} {G : EvolvingMetricData V J}
    (P : EvolvingTransportData V J G)
    (hnd : ∀ v : V, G.metric 0 v v = 0 → v = 0)
    {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) (v : V) :
    P.equivAt hnd hT ht v = P.transport t v := rfl

end MorganTianLib

end

#print axioms MorganTianLib.EvolvingTransportData.bijective_of_initial_metric_nondegenerate
#print axioms MorganTianLib.EvolvingTransportData.equivAt
