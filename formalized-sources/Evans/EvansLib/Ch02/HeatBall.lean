import EvansLib.Ch02.Heat

/-!
# Evans, Ch. 2 §2.3.2 — Parabolic cylinder, parabolic boundary, and the heat ball

This file formalizes the three space–time regions Evans introduces in §2.3.2 en route
to the mean-value formula for the heat equation:

* the **parabolic cylinder** `U_T = U × (0,T]` (`def:parabolic-cylinder-heat-ball`);
* the **parabolic boundary** `Γ_T = \overline{U_T} \ U_T` (`def:parabolic-boundary-heat-ball`);
* the **heat ball** `E(x,t;r) = {(y,s) : s ≤ t, Φ(x-y,t-s) ≥ r^{-n}}`, the space–time
  analogue of a Euclidean ball, whose boundary is a level set of the fundamental
  solution (`def:heat-ball`).

Space–time is `SpaceTime n = ℝ^{n+1}` with coordinate `0` the time `t` and coordinates
`1,…,n` the spatial variables; `spacePart p` extracts the spatial vector and `p 0` the
time. The heat ball is stated through the fixed-time Gaussian slice
`heatKernelSpatial n (t - p 0) (x - spacePart p)`, which equals `Φ(x-y,t-s)` wherever the
latter is positive (i.e. for `s < t`); at `s = t` the slice is `0`, so — since the level
`r^{-n} > 0` — the two descriptions cut out the same region.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.3.2.
-/

open scoped Real
open MeasureTheory Set

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- **Evans §2.3.2, parabolic cylinder** (`def:parabolic-cylinder-heat-ball`). For an
open bounded `U ⊆ ℝⁿ` and `T > 0`, the parabolic cylinder is `U_T = U × (0,T]`, viewed as
a subset of space–time: those points whose spatial part lies in `U` and whose time
coordinate lies in `(0,T]`. Note it includes the top `U × {T}`. -/
def parabolicCylinder (U : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) : Set (SpaceTime n) :=
  {p | spacePart p ∈ U ∧ p 0 ∈ Set.Ioc 0 T}

/-- **Evans §2.3.2, parabolic boundary** (`def:parabolic-boundary-heat-ball`). The
parabolic boundary of `U_T` is `Γ_T = \overline{U_T} \ U_T`: the closure of the parabolic
cylinder minus the cylinder itself. It comprises the bottom and the vertical sides of
`U × [0,T]` but not the top. -/
def parabolicBoundary (U : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) : Set (SpaceTime n) :=
  closure (parabolicCylinder U T) \ parabolicCylinder U T

/-- **Evans §2.3.2, heat ball** (`def:heat-ball`). For a fixed center `(x,t)` and radius
`r > 0`, the heat ball is
`E(x,t;r) = { (y,s) : s ≤ t, Φ(x-y,t-s) ≥ r^{-n} }`,
the space–time region bounded by a level set of the fundamental solution `Φ`, with the
center `(x,t)` at the top. Here `s = p 0` and `y = spacePart p`, and `Φ(x-y,t-s)` is the
Gaussian slice `heatKernelSpatial n (t - p 0) (x - spacePart p)`. -/
def heatBall (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) (r : ℝ) : Set (SpaceTime n) :=
  {p | p 0 ≤ t ∧ 1 / r ^ n ≤ heatKernelSpatial n (t - p 0) (x - spacePart p)}

end EvansLib
