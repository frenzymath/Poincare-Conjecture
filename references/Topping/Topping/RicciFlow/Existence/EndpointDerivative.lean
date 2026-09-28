import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Topology.Order.ExtendFrom

open Filter Set
open scoped Topology

noncomputable section

namespace Topping

/-
  Endpoint regularity is often obtained by proving convergence of the spatial
  derivative on the open time interval.  These small bridges package the
  one-sided endpoint theorems from Mathlib in the interval notation used by the
  Ricci-flow existence files.
-/

variable {E : Type*} [NormedAddCommGroup E]

section Derivative

variable [NormedSpace ℝ E]

theorem hasDerivWithinAt_leftEndpoint_of_tendsto_deriv
    {a T : ℝ} (hAT : a < T) {f : ℝ → E} {f' : E}
    (hDiff : DifferentiableOn ℝ f (Ioo a T))
    (hCont : ContinuousWithinAt f (Ioo a T) T)
    (hDeriv : Tendsto (fun t => deriv f t) (𝓝[<] T) (𝓝 f')) :
    HasDerivWithinAt f f' (Iic T) T := by
  exact hasDerivWithinAt_Iic_of_tendsto_deriv hDiff hCont
    (Ioo_mem_nhdsLT hAT) hDeriv

theorem hasDerivWithinAt_leftEndpoint_of_tendsto_deriv_Icc
    {a T : ℝ} (hAT : a < T) {f : ℝ → E} {f' : E}
    (hDiff : DifferentiableOn ℝ f (Ioo a T))
    (hCont : ContinuousWithinAt f (Ioo a T) T)
    (hDeriv : Tendsto (fun t => deriv f t) (𝓝[<] T) (𝓝 f')) :
    HasDerivWithinAt f f' (Icc a T) T := by
  exact (hasDerivWithinAt_leftEndpoint_of_tendsto_deriv hAT hDiff hCont hDeriv).mono
    Icc_subset_Iic_self

theorem hasDerivWithinAt_endpoint_of_tendsto_deriv_Ioo
    {T : ℝ} (hT : 0 < T) {f : ℝ → E} {f' : E}
    (hDiff : DifferentiableOn ℝ f (Ioo 0 T))
    (hCont : ContinuousWithinAt f (Ioo 0 T) T)
    (hDeriv : Tendsto (fun t => deriv f t) (𝓝[Ioo (0 : ℝ) T] T) (𝓝 f')) :
    HasDerivWithinAt f f' (Icc 0 T) T := by
  apply hasDerivWithinAt_leftEndpoint_of_tendsto_deriv_Icc hT hDiff hCont
  simpa [nhdsWithin_Ioo_eq_nhdsLT hT] using hDeriv

end Derivative

theorem continuousOn_extendFrom_Ioc_of_left_limit
    {a T : ℝ} {f : ℝ → E} {L : E}
    (hCont : ContinuousOn f (Ioo a T))
    (hLimit : Tendsto f (𝓝[<] T) (𝓝 L)) :
    ContinuousOn (extendFrom (Ioo a T) f) (Ioc a T) := by
  exact continuousOn_Ioc_extendFrom_Ioo hCont hLimit

theorem extendFrom_rightEndpoint_eq_left_limit
    {a T : ℝ} (hAT : a < T) {f : ℝ → E} {L : E}
    (hLimit : Tendsto f (𝓝[<] T) (𝓝 L)) :
    extendFrom (Ioo a T) f T = L := by
  exact eq_lim_at_right_extendFrom_Ioo hAT hLimit

theorem extendFrom_Ioo_eq_on_Ioo
    {a T : ℝ} {f : ℝ → E} (hCont : ContinuousOn f (Ioo a T))
    {t : ℝ} (ht : t ∈ Ioo a T) :
    extendFrom (Ioo a T) f t = f t := by
  exact extendFrom_extends hCont t ht

end Topping

end
