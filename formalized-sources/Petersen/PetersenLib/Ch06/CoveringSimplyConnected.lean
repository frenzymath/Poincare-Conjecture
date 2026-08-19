import PetersenLib.Ch06.CartanHadamardCore
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Petersen Ch. 6, Section 6.2 - simply connected covering spaces

The Cartan-Hadamard argument first promotes the exponential map to a covering
map.  This file supplies the next topological step: a covering map between
simply connected, locally path-connected spaces is a homeomorphism.

The Petersen-specific corollary remains conditional on the local-homeomorphism,
closed-map, and finite-fibre hypotheses of `cartanHadamard_coveringCore`; it does
not assert the still-missing curvature-to-nonsingularity bridge.
-/

noncomputable section

namespace PetersenLib

/-- A covering map between simply connected, locally path-connected spaces is
bijective.  The inverse is obtained by uniquely lifting the identity map. -/
theorem coveringMap_bijective_of_simplyConnected
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (cov : IsCoveringMap p) :
    Function.Bijective p := by
  let e₀ : E := Classical.choice (inferInstance : Nonempty E)
  let pC : C(E, X) := ⟨p, cov.continuous⟩
  let idX : C(X, X) := ContinuousMap.id X
  obtain ⟨s, hs, -⟩ :=
    cov.existsUnique_continuousMap_lifts idX (p e₀) e₀ rfl
  obtain ⟨t, -, ht_unique⟩ :=
    cov.existsUnique_continuousMap_lifts pC e₀ e₀ rfl
  have hs_comp : s.comp pC = t := ht_unique (s.comp pC) ⟨by
    change s (p e₀) = e₀
    exact hs.1
    , by
      ext e
      exact congr_fun hs.2 (p e)⟩
  have hid : ContinuousMap.id E = t :=
    ht_unique (ContinuousMap.id E) ⟨rfl, rfl⟩
  have hleft : Function.LeftInverse s p := by
    intro e
    simpa [pC] using DFunLike.congr_fun (hs_comp.trans hid.symm) e
  have hright : Function.RightInverse s p := by
    intro x
    exact congr_fun hs.2 x
  exact ⟨hleft.injective, hright.surjective⟩

/-- The homeomorphism underlying a covering map between simply connected,
locally path-connected spaces. -/
noncomputable def coveringMapHomeomorphOfSimplyConnected
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {p : E → X} (cov : IsCoveringMap p) : E ≃ₜ X :=
  (Equiv.ofBijective p (coveringMap_bijective_of_simplyConnected cov)).toHomeomorphOfContinuousOpen
    cov.continuous cov.isLocalHomeomorph.isOpenMap

/-- **Math.** The simply connected topological core of Petersen Theorem 6.2.2.

Under the explicit covering hypotheses used by `cartanHadamard_coveringCore`,
the exponential-map candidate is a homeomorphism when the target is simply
connected.  Its source also has the expected Euclidean continuous-linear model.
-/
theorem cartanHadamard_homeomorphCore
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (exp_p : V → X)
    (hlocal : IsLocalHomeomorph exp_p)
    (hclosed : IsClosedMap exp_p)
    (hfinite : ∀ x : X, (exp_p ⁻¹' {x}).Finite) :
    Nonempty (V ≃ₜ X) ∧
      Nonempty (V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) := by
  obtain ⟨hcover, hlinear⟩ :=
    cartanHadamard_coveringCore exp_p hlocal hclosed hfinite
  exact ⟨⟨coveringMapHomeomorphOfSimplyConnected hcover⟩, hlinear⟩

end PetersenLib

end
