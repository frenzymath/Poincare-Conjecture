import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.IsLocalHomeomorph

noncomputable section

namespace PetersenLib

variable {M M' : Type*} [TopologicalSpace M] [T2Space M] [TopologicalSpace M']

/-- **Math.** **Uniqueness of continuous lifts through a local homeomorphism.**
If `f : M → M'` is a local homeomorphism out of a Hausdorff space and `g₁`,
`g₂` are continuous lifts of the same curve over a preconnected parameter set,
then they agree everywhere on that set once they agree at one parameter. -/
theorem IsLocalHomeomorph.eqOn_lift {f : M → M'} (hf : IsLocalHomeomorph f)
    {c : ℝ → M'} {g₁ g₂ : ℝ → M} {s : Set ℝ} (hs : IsPreconnected s)
    (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (hlift₁ : ∀ t ∈ s, f (g₁ t) = c t) (hlift₂ : ∀ t ∈ s, f (g₂ t) = c t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (h0 : g₁ t₀ = g₂ t₀) :
    Set.EqOn g₁ g₂ s := by
  have sep : IsSeparatedMap f := T2Space.isSeparatedMap f
  have inj : IsLocallyInjective f := hf.isLocallyInjective
  have he : Set.EqOn (f ∘ g₁) (f ∘ g₂) s := fun t ht =>
    (hlift₁ t ht).trans (hlift₂ t ht).symm
  exact sep.eqOn_of_comp_eqOn inj hs h₁ h₂ he ht₀ h0

end PetersenLib
