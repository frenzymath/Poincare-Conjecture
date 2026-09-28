import MorganTianLib.Ch03.RicciFlow.ForwardDifference

/-!
# Minimum envelopes on compact spaces

The spatial minimum of a jointly continuous scalar family is attained and
continuous. A lower bound for the time derivative at every minimizing point
gives the same lower forward-Dini bound for the minimum. These are the compact
envelope inputs to Morgan--Tian Chapter 4, `claim:scalar-min-forward-difference`.
The derivative and its joint continuity remain explicit analytic hypotheses.
-/

open Filter Set Function
open scoped Topology

noncomputable section

namespace MorganTianLib

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

/-- A continuous function on a nonempty compact space attains its infimum. -/
theorem exists_eq_iInf_of_continuous {f : X → ℝ} (hf : Continuous f) :
    ∃ x, f x = ⨅ y, f y := by
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  exact ⟨x, le_antisymm (le_ciInf fun y => hx (mem_univ y))
    (ciInf_le (isCompact_range hf).bddBelow x)⟩

/-- The maximum of the negative family is the negative of its minimum. -/
theorem iSup_neg_eq_neg_iInf_of_continuous {f : X → ℝ} (hf : Continuous f) :
    (⨆ x, -f x) = -(⨅ x, f x) := by
  refine le_antisymm (ciSup_le fun x => ?_) ?_
  · exact neg_le_neg (ciInf_le (isCompact_range hf).bddBelow x)
  · obtain ⟨x, hx⟩ := exists_eq_iInf_of_continuous hf
    rw [← hx]
    exact le_ciSup (isCompact_range hf.neg).bddAbove x

/-- The minimum of a jointly continuous family over a compact space is continuous. -/
theorem continuous_iInf_of_compact {F : X → ℝ → ℝ} (hF : Continuous ↿F) :
    Continuous fun t => ⨅ x, F x t := by
  have heq : (fun t => ⨆ x, -F x t) = fun t => -(⨅ x, F x t) := by
    funext t
    exact iSup_neg_eq_neg_iInf_of_continuous
      (hF.comp (continuous_id.prodMk continuous_const))
  have h : Continuous (fun t => -(⨆ x, -F x t)) :=
    (continuous_iSup_of_compact (F := fun x t => -F x t) hF.neg).neg
  convert h using 1
  funext t
  rw [congrFun heq t, neg_neg]

/-- A lower derivative bound at all current minimizers controls the lower
forward difference quotient of the compact spatial minimum. -/
theorem forwardDiffQuotientGE_iInf {F F' : X → ℝ → ℝ} {t b c : ℝ}
    (htb : t < b) (hF : Continuous ↿F) (hF' : Continuous ↿F')
    (hderiv : ∀ x, ∀ s ∈ Ioo t b, HasDerivAt (F x) (F' x s) s)
    (hc : ∀ x, F x t = (⨅ y, F y t) → c ≤ F' x t) :
    ForwardDiffQuotientGE (fun s => ⨅ x, F x s) t c := by
  have heq : (fun s => ⨆ x, -F x s) = fun s => -(⨅ x, F x s) := by
    funext s
    exact iSup_neg_eq_neg_iInf_of_continuous
      (hF.comp (continuous_id.prodMk continuous_const))
  have hneg := forwardDiffQuotientLE_iSup (F := fun x s => -F x s)
    (F' := fun x s => -F' x s) (c := -c) htb hF.neg hF'.neg
    (fun x s hs => (hderiv x s hs).neg) (by
      intro x hx
      have hx' : F x t = ⨅ y, F y t := by
        have hh := congrFun heq t
        rw [hh] at hx
        exact neg_injective hx
      exact neg_le_neg (hc x hx'))
  rw [heq] at hneg
  intro r hr
  filter_upwards [hneg (-r) (neg_lt_neg hr)] with z hz
  rw [slope_neg] at hz
  exact neg_lt_neg_iff.mp hz

end MorganTianLib
