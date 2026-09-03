import MorganTianLib.Ch02.ForwardDifference

/-!
# Morgan--Tian Ch. 3 - lower forward difference quotients

The distance-variation statements in Chapter 3 use a lower forward Dini
derivative.  Chapter 2 already supplies the dual upper-bound interface.  This
file records the lower-bound interface and proves that, at a differentiability
time, it is exactly the ordinary derivative inequality.

Blueprint: `rem:forward-difference-quotient`.
-/

open Filter Real Set
open scoped Topology

namespace MorganTianLib

/-- **Math.** The forward difference quotient of `f` at `t` is at least `c`:
every strict lower bound `r < c` eventually bounds the right slopes from
below.  Equivalently, the lower right Dini derivative is at least `c`. -/
def ForwardDiffQuotientGE (f : ℝ → ℝ) (t c : ℝ) : Prop :=
  ∀ r, r < c → ∀ᶠ z in 𝓝[>] t, r < slope f t z

/-- **Math.** A lower forward-difference bound remains true after weakening
its lower bound. -/
theorem ForwardDiffQuotientGE.mono {f : ℝ → ℝ} {t c c' : ℝ}
    (h : ForwardDiffQuotientGE f t c) (hc'c : c' ≤ c) :
    ForwardDiffQuotientGE f t c' :=
  fun r hr => h r (lt_of_lt_of_le hr hc'c)

/-- **Math.** A function with right derivative `c` at `t` has lower forward
difference quotient at least `c` there. -/
theorem HasDerivWithinAt.forwardDiffQuotientGE {f : ℝ → ℝ} {t c : ℝ}
    (h : HasDerivWithinAt f c (Ici t) t) : ForwardDiffQuotientGE f t c := by
  intro r hr
  have h' : Tendsto (slope f t) (𝓝[>] t) (𝓝 c) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).1 h.Ioi_of_Ici
  exact h' (Ioi_mem_nhds hr)

/-- **Math.** At a differentiability time, saying that the ordinary
derivative is at least `C` is equivalent to saying that the lower forward
difference quotient is at least `C`. -/
theorem HasDerivAt.forwardDiffQuotientGE_iff {f : ℝ → ℝ} {t c C : ℝ}
    (h : HasDerivAt f c t) :
    ForwardDiffQuotientGE f t C ↔ C ≤ c := by
  constructor
  · intro hGE
    by_contra hC
    have hcC : c < C := lt_of_not_ge hC
    let r := (c + C) / 2
    have hcr : c < r := by
      dsimp [r]
      linarith
    have hrC : r < C := by
      dsimp [r]
      linarith
    have hRight : HasDerivWithinAt f c (Ici t) t := h.hasDerivWithinAt
    have hLE : ForwardDiffQuotientLE f t c :=
      HasDerivWithinAt.forwardDiffQuotientLE hRight
    obtain ⟨z, hzGE, hzLE⟩ := ((hGE r hrC).and (hLE r hcr)).exists
    exact (lt_asymm hzGE hzLE)
  · intro hCc
    have hRight : HasDerivWithinAt f c (Ici t) t := h.hasDerivWithinAt
    exact (HasDerivWithinAt.forwardDiffQuotientGE hRight).mono hCc

/-- **Math.** Source-facing orientation of
`HasDerivAt.forwardDiffQuotientGE_iff`: the derivative lower bound and the
forward-difference lower bound are equivalent. -/
theorem HasDerivAt.le_deriv_iff_forwardDiffQuotientGE
    {f : ℝ → ℝ} {t c C : ℝ} (h : HasDerivAt f c t) :
    C ≤ c ↔ ForwardDiffQuotientGE f t C :=
  (HasDerivAt.forwardDiffQuotientGE_iff h).symm

#print axioms MorganTianLib.HasDerivAt.le_deriv_iff_forwardDiffQuotientGE

end MorganTianLib
