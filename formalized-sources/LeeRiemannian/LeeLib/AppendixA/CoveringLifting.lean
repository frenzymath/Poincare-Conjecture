import Mathlib.Topology.Homotopy.Lifting

/-!
# Appendix A: lifting properties of covering maps

These are the three covering-space facts used by Lee's Appendix A and Chapter
6.  Mathlib's `IsCoveringMap` API supplies continuous path lifts, uniqueness on
preconnected domains, and the endpoint-invariance (monodromy) theorem.  The
declarations below expose those facts with the hypotheses and notation used in
Lee's text.
-/

namespace LeeLib.AppendixA

open Topology unitInterval

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace A] {p : E → X}

/-- **Math.** **Lee, Appendix A.54(a) (unique lifting).** Two continuous lifts
of the same map through a covering map, agreeing at one point of a connected
domain, are equal. -/
theorem coveringMap_unique_lift [ConnectedSpace A]
    (cov : IsCoveringMap p) {g₁ g₂ : A → E}
    (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ := by
  exact cov.eq_of_comp_eq h₁ h₂ he a ha

/-- **Math.** **Lee, Appendix A.54(b) (path lifting).** Every continuous path
in the base has a unique continuous lift through a prescribed point of the
fiber over its initial point. -/
theorem coveringMap_path_lift (cov : IsCoveringMap p)
    (γ : C(unitInterval, X)) (e : E) (hγ₀ : γ 0 = p e) :
    ∃! Γ : C(unitInterval, E), p ∘ Γ = γ ∧ Γ 0 = e := by
  refine ⟨cov.liftPath γ e hγ₀, ⟨cov.liftPath_lifts γ e hγ₀, cov.liftPath_zero γ e hγ₀⟩, ?_⟩
  intro Γ hΓ
  exact (cov.eq_liftPath_iff' hγ₀).mpr ⟨hΓ.1, hΓ.2⟩

/-- **Math.** **Lee, Appendix A.54(c) (monodromy).** Homotopic paths with
the same initial lift have the same lifted endpoint. -/
theorem coveringMap_monodromy
    (cov : IsCoveringMap p) (γ₀ γ₁ : C(unitInterval, X))
    (hγ : γ₀.HomotopicRel γ₁ ({0, 1} : Set unitInterval))
    (Γ₀ Γ₁ : C(unitInterval, E))
    (h₀ : p ∘ Γ₀ = γ₀) (h₁ : p ∘ Γ₁ = γ₁)
    (hstart : Γ₀ 0 = Γ₁ 0) : Γ₀ 1 = Γ₁ 1 := by
  let e : E := Γ₀ 0
  have hγ₀ : γ₀ 0 = p e := by
    change γ₀ 0 = p (Γ₀ 0)
    exact (congr_fun h₀ 0).symm
  have hγ₁ : γ₁ 0 = p e := by
    change γ₁ 0 = p (Γ₀ 0)
    exact (congr_fun h₁ 0).symm.trans (congrArg p hstart.symm)
  have hΓ₀ : Γ₀ = cov.liftPath γ₀ e hγ₀ :=
    (cov.eq_liftPath_iff' hγ₀).mpr ⟨h₀, rfl⟩
  have hΓ₁ : Γ₁ = cov.liftPath γ₁ e hγ₁ :=
    (cov.eq_liftPath_iff' hγ₁).mpr ⟨h₁, hstart.symm⟩
  rw [hΓ₀, hΓ₁]
  exact cov.liftPath_apply_one_eq_of_homotopicRel hγ e hγ₀ hγ₁

end LeeLib.AppendixA
