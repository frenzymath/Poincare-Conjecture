import MorganTianLib.Ch04.ScalarMinimum

/-!
# Morgan--Tian Ch. 4 - interval-local compact minimum envelopes

The compact minimum lemmas are stated for globally continuous families.  This
file supplies the interval-local adapter used by Ricci-flow applications:
continuity on `X × Icc a b` is extended by `Set.IccExtend`, while derivative
and minimizer hypotheses are only required on the original interval.
-/

open Filter Set Function
open scoped Topology

noncomputable section

namespace MorganTianLib

variable {X : Type*}

/-- Extend a jointly continuous family on a closed time interval to all times. -/
def intervalExtend {a b : ℝ} (hab : a ≤ b) (F : X → ℝ → ℝ) : X → ℝ → ℝ :=
  fun x => Set.IccExtend hab (fun t : Icc a b => F x t)

theorem intervalExtend_eq_of_mem {a b : ℝ} (hab : a ≤ b) (F : X → ℝ → ℝ)
    {x : X} {t : ℝ} (ht : t ∈ Icc a b) : intervalExtend hab F x t = F x t := by
  simp [intervalExtend, Set.IccExtend_of_mem, ht]

variable [TopologicalSpace X]

theorem continuous_intervalExtend {a b : ℝ} (hab : a ≤ b) {F : X → ℝ → ℝ}
    (hF : ContinuousOn (fun z : X × ℝ => F z.1 z.2) (univ ×ˢ Icc a b)) :
    Continuous ↿(intervalExtend hab F) := by
  exact hF.comp_continuous
    (continuous_fst.prodMk (continuous_subtype_val.comp
      ((continuous_projIcc (h := hab)).comp continuous_snd)))
    (fun z => ⟨mem_univ _, (projIcc a b hab z.2).property⟩)

variable [CompactSpace X] [Nonempty X]

/-- A compact spatial minimum is continuous on every closed time interval on
which the original family is jointly continuous. -/
theorem continuousOn_iInf_of_compact {F : X → ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn (fun z : X × ℝ => F z.1 z.2) (univ ×ˢ Icc a b)) :
    ContinuousOn (fun t => ⨅ x, F x t) (Icc a b) := by
  by_cases hab : a ≤ b
  · apply (continuous_iInf_of_compact (continuous_intervalExtend hab hF)).continuousOn.congr
    intro t ht
    simp only [intervalExtend_eq_of_mem hab F ht]
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab)]

/-- The lower forward-difference estimate for a compact minimum needs only
continuity on the closed time interval; the derivative data remain local. -/
theorem forwardDiffQuotientGE_iInfOn {F F' : X → ℝ → ℝ} {a b t c : ℝ}
    (hat : a ≤ t) (htb : t < b)
    (hF : ContinuousOn (fun z : X × ℝ => F z.1 z.2) (univ ×ˢ Icc a b))
    (hF' : ContinuousOn (fun z : X × ℝ => F' z.1 z.2) (univ ×ˢ Icc a b))
    (hderiv : ∀ x, ∀ s ∈ Ioo t b, HasDerivAt (F x) (F' x s) s)
    (hc : ∀ x, F x t = (⨅ y, F y t) → c ≤ F' x t) :
    ForwardDiffQuotientGE (fun s => ⨅ x, F x s) t c := by
  have hab : a ≤ b := hat.trans htb.le
  have htIcc : t ∈ Icc a b := ⟨hat, htb.le⟩
  let Fe := intervalExtend hab F
  let F'e := intervalExtend hab F'
  have hFe := continuous_intervalExtend hab hF
  have hF'e := continuous_intervalExtend hab hF'
  have hlocal : ∀ x, ∀ s ∈ Ioo t b, HasDerivAt (Fe x) (F'e x s) s := by
    intro x s hs
    have hsIcc : s ∈ Icc a b := ⟨hat.trans hs.1.le, hs.2.le⟩
    rw [show F'e x s = F' x s from intervalExtend_eq_of_mem hab F' hsIcc]
    apply (hderiv x s hs).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (hat.trans_lt hs.1) hs.2] with u hu
    exact intervalExtend_eq_of_mem hab F ⟨hu.1.le, hu.2.le⟩
  have hmin : ∀ x, Fe x t = (⨅ y, Fe y t) → c ≤ F'e x t := by
    intro x hx
    have hFx : F x t = (⨅ y, F y t) := by
      simpa only [Fe, intervalExtend_eq_of_mem hab F htIcc] using hx
    simpa only [F'e, intervalExtend_eq_of_mem hab F' htIcc] using hc x hFx
  have H := forwardDiffQuotientGE_iInf (F := Fe) (F' := F'e) htb hFe hF'e hlocal hmin
  intro r hr
  filter_upwards [H r hr, Ioo_mem_nhdsGT htb] with s hs hsIoo
  simpa only [slope, Fe, intervalExtend_eq_of_mem hab F htIcc,
    intervalExtend_eq_of_mem hab F ⟨hat.trans hsIoo.1.le, hsIoo.2.le⟩] using hs

end MorganTianLib

end
