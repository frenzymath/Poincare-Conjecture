import EvansLib.Ch02.LaplaceMeanValueTheorem
import EvansLib.Ch02.ConverseMVP
import EvansLib.Ch02.Harnack
import EvansLib.Ch02.Liouville

/-!
# Evans, Ch. 2 section 2.2.3 - consequences for harmonic functions

The maximum principle, Dirichlet uniqueness, Liouville theorem, and Harnack
inequality were first proved in this development for functions satisfying the
solid-ball mean-value property.  This file composes those results with Evans's
mean-value theorem, giving the corresponding statements directly for harmonic
functions.
-/

open Metric Set InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : Nat}

/-- **Evans section 2.2.2, Theorem 3 (converse mean-value theorem).**
If every admissible spherical shell centered at `x` has the same normalized
value as the radius-zero shell, then a continuous function is harmonic.  The
argument first integrates the shells in the radial variable to obtain the
solid-ball mean-value property. -/
theorem harmonicOnNhd_of_unitSphereRadialIntegralAt_eq_zero [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {U : Set (EuclideanSpace Real (Fin n))}
    (hUopen : IsOpen U) (hcont : ContinuousOn u U)
    (hshell : ∀ ⦃x : EuclideanSpace Real (Fin n)⦄ ⦃r : Real⦄,
      0 < r -> closedBall x r ⊆ U -> ∀ t ∈ Ioo (0 : Real) r,
        unitSphereRadialIntegralAt u x t = unitSphereRadialIntegralAt u x 0) :
    HarmonicOnNhd u U := by
  exact HasBallMeanValueProperty.harmonicOnNhd
    (hasBallMeanValueProperty_of_unitSphereRadialIntegralAt_eq_zero hcont hshell)
    hUopen hcont

/-- **Evans section 2.2.3, Theorem 4(ii) (strong maximum principle).**
A harmonic function on a connected open set which attains an interior maximum
is constant. -/
theorem harmonic_eqOn_of_isPreconnected_of_isMaxOn [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {U : Set (EuclideanSpace Real (Fin n))}
    (hu : HarmonicOnNhd u U) (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    {x0 : EuclideanSpace Real (Fin n)} (hx0 : x0 ∈ U)
    (hmax : ∀ y ∈ U, u y ≤ u x0) :
    ∀ y ∈ U, u y = u x0 := by
  exact eqOn_of_isPreconnected_of_isMaxOn
    (HarmonicOnNhd.hasBallMeanValueProperty hu hUopen) hu.contDiffOn.continuousOn
    hUopen hUconn hx0 hmax

/-- **Evans section 2.2.3, Theorem 4(i) (maximum principle).**
For a nonempty bounded open set, the maximum of a harmonic function continuous
up to the closure is attained on the boundary. -/
theorem harmonic_exists_frontier_isMaxOn [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {U : Set (EuclideanSpace Real (Fin n))}
    (hu : HarmonicOnNhd u U) (hcont : ContinuousOn u (closure U))
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U) (hUne : U.Nonempty) :
    ∃ z ∈ frontier U, ∀ y ∈ closure U, u y ≤ u z := by
  exact exists_frontier_isMaxOn (HarmonicOnNhd.hasBallMeanValueProperty hu hUopen)
    hcont hUopen hUbdd hUne

/-- **Evans section 2.2.3, Theorem 5 (Poisson--Dirichlet uniqueness).**
If the difference of two candidate solutions is harmonic and their boundary
values agree, then the candidates agree throughout the closure.  Equality of
their Poisson right-hand sides is precisely what makes the difference harmonic.
-/
theorem eqOn_closure_of_eqOn_frontier_of_harmonic_sub [Nonempty (Fin n)]
    {u v : EuclideanSpace Real (Fin n) -> Real}
    {U : Set (EuclideanSpace Real (Fin n))}
    (huv : HarmonicOnNhd (fun y => u y - v y) U)
    (hcu : ContinuousOn u (closure U)) (hcv : ContinuousOn v (closure U))
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hbdry : ∀ z ∈ frontier U, u z = v z) :
    ∀ y ∈ closure U, u y = v y := by
  have hzero := eqOn_closure_of_eqOn_frontier
    (HarmonicOnNhd.hasBallMeanValueProperty huv hUopen)
    (hasBallMeanValueProperty_const (n := n) 0)
    (hcu.sub hcv) continuousOn_const hUopen hUbdd
    (fun z hz => by simp [hbdry z hz])
  intro y hy
  have hy0 := hzero y hy
  linarith

/-- A direct Poisson uniqueness form: two `C²` functions with the same
Laplacian and the same boundary values agree on the closure of a bounded open
set. -/
theorem eqOn_closure_of_eqOn_frontier_of_laplacian_eq [Nonempty (Fin n)]
    {u v : EuclideanSpace Real (Fin n) -> Real}
    {U : Set (EuclideanSpace Real (Fin n))}
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hcu2 : ContDiffOn Real 2 u U) (hcv2 : ContDiffOn Real 2 v U)
    (hlap : ∀ x ∈ U, Δ u x = Δ v x)
    (hcu : ContinuousOn u (closure U)) (hcv : ContinuousOn v (closure U))
    (hbdry : ∀ z ∈ frontier U, u z = v z) :
    ∀ y ∈ closure U, u y = v y := by
  have huv : HarmonicOnNhd (fun y => u y - v y) U := by
    intro x hx
    have hux : ContDiffAt Real 2 u x :=
      (hcu2 x hx).contDiffAt (hUopen.mem_nhds hx)
    have hvx : ContDiffAt Real 2 v x :=
      (hcv2 x hx).contDiffAt (hUopen.mem_nhds hx)
    refine ⟨hux.sub hvx, ?_⟩
    filter_upwards [hUopen.mem_nhds hx] with y hy
    have huy : ContDiffAt Real 2 u y :=
      (hcu2 y hy).contDiffAt (hUopen.mem_nhds hy)
    have hvy : ContDiffAt Real 2 v y :=
      (hcv2 y hy).contDiffAt (hUopen.mem_nhds hy)
    change Δ (u - v) y = 0
    rw [huy.laplacian_sub hvy, hlap y hy]
    ring
  exact eqOn_closure_of_eqOn_frontier_of_harmonic_sub huv hcu hcv hUopen hUbdd hbdry

/-- **Evans section 2.2.3, Theorem 8 (Liouville).**
A bounded harmonic function on Euclidean space of positive dimension is
constant. -/
theorem harmonic_liouville_of_isBounded [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    (hu : HarmonicOnNhd u univ) (hbdd : Bornology.IsBounded (range u)) :
    ∃ c : Real, u = fun _ => c := by
  have hcont : Continuous u := by
    simpa only [continuousOn_univ] using hu.contDiffOn.continuousOn
  exact liouville_of_isBounded
    (HarmonicOnNhd.hasBallMeanValueProperty hu isOpen_univ) hcont hbdd

/-- **Evans section 2.2.3, Theorem 11 (Harnack inequality).**
On every bounded preconnected set compactly contained in the harmonicity
domain, all values of every nonnegative harmonic function are comparable by a
constant independent of the function. -/
theorem exists_harnack_const_harmonic [Nonempty (Fin n)]
    {U V : Set (EuclideanSpace Real (Fin n))}
    (hUopen : IsOpen U) (hVconn : IsPreconnected V)
    (hVbdd : Bornology.IsBounded V) (hVU : closure V ⊆ U) :
    ∃ C : Real, 0 < C ∧
      ∀ u : EuclideanSpace Real (Fin n) -> Real,
        HarmonicOnNhd u U -> (∀ z ∈ U, 0 ≤ u z) ->
        ∀ x ∈ V, ∀ y ∈ V, u x ≤ C * u y := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_harnack_const (n := n) hUopen hVconn hVbdd hVU
  refine ⟨C, hC, ?_⟩
  intro u hu hnonneg x hx y hy
  exact hbound u (HarmonicOnNhd.hasBallMeanValueProperty hu hUopen)
    hu.contDiffOn.continuousOn hnonneg x hx y hy

end EvansLib
