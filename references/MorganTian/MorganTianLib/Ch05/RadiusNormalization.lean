import MorganTianLib.Ch05.UnboundedAssembly

/-!
# Morgan--Tian Chapter 5: positive-radius normalization

An eventually positive radius sequence converging to a positive target can be
made pointwise positive by clamping it below at half the target radius.  The
clamped sequence has the same limit and agrees with the original sequence on a
cofinal tail, so the unbounded pointed-GH transport API applies directly.
-/

open Set Filter Topology
open scoped Topology

namespace MorganTianLib

universe u

/-- **Math.** Normalize an eventually positive radius sequence to a globally
positive one without changing its eventual values or its pointed-GH limit.

The explicit eventual-positivity hypothesis records the source-side domain
condition; convergence to the positive target supplies the stronger eventual
lower bound needed for the clamp to become inactive.
-/
theorem PointedGHConvergesUnbounded.normalize_radius
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    [∀ k, LengthSpace (X k).carrier]
    (h : PointedGHConvergesUnbounded X Y)
    (r : ℕ → ℝ) {R : ℝ} (hR : 0 < R)
    (hrlim : Tendsto r atTop (𝓝 R))
    (hr_eventually_pos : ∀ᶠ k in atTop, 0 < r k) :
    ∃ rPos : ℕ → ℝ, ∃ hPos : ∀ k, 0 < rPos k,
      Tendsto rPos atTop (𝓝 R) ∧
      (∀ᶠ k in atTop, rPos k = r k) ∧
      PointedGHConverges
        (fun k => ballModel (X k) (rPos k) (hPos k))
        (ballModel Y R hR) := by
  let rPos : ℕ → ℝ := fun k => max (r k) (R / 2)
  have hhalf : 0 < R / 2 := by linarith
  have hhalf_le : R / 2 ≤ R := by linarith
  have hPos : ∀ k, 0 < rPos k := by
    intro k
    exact lt_max_of_lt_right hhalf
  have hPosLim : Tendsto rPos atTop (𝓝 R) := by
    have hmax := hrlim.max (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => R / 2) atTop (𝓝 (R / 2)))
    simpa [rPos, max_eq_left hhalf_le] using hmax
  have hgt : ∀ᶠ k in atTop, R / 2 < r k := by
    have hnhds : ∀ᶠ x : ℝ in 𝓝 R, R / 2 < x :=
      eventually_gt_nhds (by linarith : R / 2 < R)
    exact hrlim.eventually hnhds
  have heq : ∀ᶠ k in atTop, rPos k = r k := by
    filter_upwards [hgt, hr_eventually_pos] with k hk _hpos
    exact max_eq_left (le_of_lt hk)
  refine ⟨rPos, hPos, hPosLim, heq, ?_⟩
  exact h.converges_ballModel_tendsto_radius rPos hPos hR hPosLim

end MorganTianLib

#print axioms MorganTianLib.PointedGHConvergesUnbounded.normalize_radius
