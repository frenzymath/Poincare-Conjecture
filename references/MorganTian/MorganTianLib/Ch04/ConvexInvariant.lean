import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Morgan--Tian Ch. 4 - convex invariant sets

This module records the finite-dimensional vector-space part of Hamilton's
tensor maximum-principle setup.  The tangent-cone condition is kept separate
from the analytic ODE and parabolic inputs: those inputs are supplied by later
modules rather than hidden in a certificate-shaped proposition.
-/

open Filter Set
open scoped Topology NNReal

noncomputable section

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Convex sets and vector fields -/

/-- A vector field is tangent to a set at every point of the set.

For a closed convex set this is Hamilton's definition of a vector field
preserving the set.  We leave closedness and convexity as explicit hypotheses
where they are used, so the predicate itself remains the intrinsic tangent
condition and does not silently discard degenerate sets.
-/
def vectorFieldPreservesConvexSet (Z : Set V) (ψ : V → V) : Prop :=
  ∀ ⦃z : V⦄, z ∈ Z → ψ z ∈ posTangentConeAt Z z

/-- The geometric hypotheses attached to the carrier in the source definition. -/
def isClosedConvexSet (Z : Set V) : Prop :=
  IsClosed Z ∧ Convex ℝ Z

/-- For points of a convex set, the chord direction lies in the positive tangent cone. -/
theorem sub_mem_posTangentConeAt_of_convex {Z : Set V} (hZ : Convex ℝ Z)
    {z y : V} (hz : z ∈ Z) (hy : y ∈ Z) :
    y - z ∈ posTangentConeAt Z z := by
  exact sub_mem_posTangentConeAt_of_segment_subset (hZ.segment_subset hz hy)

/-- A useful concrete sufficient condition for the tangent-cone preservation predicate. -/
theorem vectorFieldPreservesConvexSet_of_segment {Z : Set V} {ψ : V → V}
    (hZ : Convex ℝ Z)
    (hψ : ∀ ⦃z : V⦄, z ∈ Z → ∃ y ∈ Z, ψ z = y - z) :
    vectorFieldPreservesConvexSet Z ψ := by
  intro z hz
  obtain ⟨y, hy, hzy⟩ := hψ hz
  rw [hzy]
  exact sub_mem_posTangentConeAt_of_convex hZ hz hy

/-- The zero vector field is tangent to every set at each of its points. -/
theorem vectorFieldPreservesConvexSet_zero {Z : Set V} :
    vectorFieldPreservesConvexSet Z (fun _ : V => 0) := by
  intro z hz
  exact zero_mem_tangentConeAt (subset_closure hz)

/-! ### Integral curves -/

/-- Every integral curve starting in `Z` stays in `Z` at later times on an
order-connected time set.

`IsIntegralCurveOn` is Mathlib's derivative-based ODE predicate.  Requiring
`OrdConnected` prevents a disconnected time set from being mistaken for one
continuous interval of evolution.
-/
def integralCurvePreservesSet (Z : Set V) (ψ : V → V) : Prop :=
  ∀ (γ : ℝ → V) (s : Set ℝ), s.OrdConnected →
    IsIntegralCurveOn γ (fun _ : ℝ => ψ) s →
    ∀ t₀ ∈ s, γ t₀ ∈ Z → ∀ t ∈ s, t₀ ≤ t → γ t ∈ Z

/-- An explicit local ODE-existence input at a point.

The derivative witness is included because a one-sided `HasDerivWithinAt` at the
initial endpoint alone is weaker than the ambient derivative needed to recover
the tangent-cone direction.  Picard--Lindelöf supplies this package for a
smooth locally Lipschitz vector field; this definition does not assert that
existence theorem.
-/
def forwardIntegralCurveExistsAt (ψ : V → V) (z : V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → V,
    γ 0 = z ∧
      IsIntegralCurveOn γ (fun _ : ℝ => ψ) (Icc 0 ε) ∧
      HasDerivAt γ (ψ z) 0

/-! ### The easy (and load-bearing) implication of the integral-curve criterion -/

private theorem mem_posTangentConeAt_of_forward_curve
    {Z : Set V} {z v : V} {γ : ℝ → V} {ε : ℝ}
    (hε : 0 < ε) (hz : γ 0 = z)
    (hderiv : HasDerivAt γ v 0)
    (hmem : ∀ t ∈ Icc 0 ε, γ t ∈ Z) :
    v ∈ posTangentConeAt Z z := by
  let l : Filter ℝ≥0 := 𝓝[>] (0 : ℝ≥0)
  let d : ℝ≥0 → V := fun r => γ (r : ℝ) - z
  let c : ℝ≥0 → ℝ≥0 := fun r => r⁻¹
  have hcoel : Tendsto (fun r : ℝ≥0 => (r : ℝ)) l (𝓝[>] (0 : ℝ)) := by
    have h := (tendsto_map (f := NNReal.toReal) (x := 𝓝[>] (0 : ℝ≥0)))
    rw [NNReal.map_coe_nhdsGT] at h
    exact h
  have hd : Tendsto d l (𝓝 0) := by
    have hγ : Tendsto γ (𝓝 (0 : ℝ)) (𝓝 z) := by
      simpa [hz] using hderiv.continuousAt.tendsto
    have hγ' : Tendsto (fun r : ℝ≥0 => γ (r : ℝ)) l (𝓝 z) := by
      exact hγ.comp (hcoel.mono_right nhdsWithin_le_nhds)
    have hz' : Tendsto (fun _ : ℝ≥0 => z) l (𝓝 z) := tendsto_const_nhds
    simpa [d] using hγ'.sub hz'
  let ε' : ℝ≥0 := ⟨ε, hε.le⟩
  have hmem' : ∀ᶠ r : ℝ≥0 in l, z + d r ∈ Z := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ≥0) < ε' by exact_mod_cast hε)] with r hr
    have hri : (r : ℝ) ∈ Icc 0 ε := by
      constructor
      · exact_mod_cast (le_of_lt (show (0 : ℝ≥0) < r from hr.1))
      · exact_mod_cast (le_of_lt hr.2)
    simpa [d, hz] using hmem (r : ℝ) hri
  have hc : Tendsto (fun r : ℝ≥0 => c r • d r) l (𝓝 v) := by
    have hs : Tendsto (fun t : ℝ => t⁻¹ • (γ (0 + t) - γ 0))
        (𝓝[>] (0 : ℝ)) (𝓝 v) :=
      hderiv.tendsto_slope_zero_right
    have hc' := hs.comp hcoel
    simpa [c, d, Function.comp_def, hz, NNReal.smul_def] using hc'
  exact mem_tangentConeAt_of_frequently l c d hd hmem'.frequently hc

/-- If all forward integral curves from points of `Z` preserve `Z`, then their
initial derivatives satisfy the tangent-cone condition.

This is the direction of Hamilton's integral-curve criterion that only uses
the actual ODE witnesses.  The converse (tangent condition implies preservation)
requires the local existence/uniqueness and convex-set viability argument and
is intentionally left to the analytic producer that supplies it.
-/
theorem vectorFieldPreservesConvexSet_of_integralCurvePreservesSet
    {Z : Set V} {ψ : V → V}
    (hcurves : integralCurvePreservesSet Z ψ)
    (hexists : ∀ z ∈ Z, forwardIntegralCurveExistsAt ψ z) :
    vectorFieldPreservesConvexSet Z ψ := by
  intro z hz
  obtain ⟨ε, hε, γ, hγ0, hγode, hγderiv⟩ := hexists z hz
  have hγmem : ∀ t ∈ Icc 0 ε, γ t ∈ Z := by
    intro t ht
    exact hcurves γ (Icc 0 ε) ordConnected_Icc hγode 0
      (⟨le_rfl, hε.le⟩) (by simpa [hγ0] using hz) t ht ht.1
  exact mem_posTangentConeAt_of_forward_curve hε hγ0 hγderiv hγmem

/-! ### Supporting functionals -/

/-- A supporting continuous linear functional is nonpositive on a preserving
vector field at the supported point. -/
theorem support_functional_nonpos_of_vectorFieldPreservesConvexSet
    {Z : Set V} {ψ : V → V}
    (hpres : vectorFieldPreservesConvexSet Z ψ)
    {z : V} (hz : z ∈ Z) (φ : V →L[ℝ] ℝ)
    (hsupport : ∀ y ∈ Z, φ y ≤ φ z) :
    φ (ψ z) ≤ 0 := by
  have hmax : IsLocalMaxOn (fun x : V => φ x) Z z := by
    rw [IsLocalMaxOn, IsMaxFilter]
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hsupport y hy
  have hderiv : HasFDerivWithinAt (fun x : V => φ x) φ Z z :=
    φ.hasFDerivAt.hasFDerivWithinAt
  exact hmax.hasFDerivWithinAt_nonpos hderiv (hpres hz)

/-! ### Fiberwise convex subbundles -/

/-- A family of subsets, one subset in each fiber of a dependent bundle. -/
abbrev FiberSet (M : Type*) (F : M → Type*) := ∀ x, Set (F x)

variable {M : Type*} {F : M → Type*}
variable [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℝ (F x)]

/-- Fiberwise closedness of a family of carriers. -/
def fiberwiseClosed (Z : FiberSet M F) : Prop :=
  ∀ x, IsClosed (Z x)

/-- Fiberwise convexity of a family of carriers. -/
def fiberwiseConvex (Z : FiberSet M F) : Prop :=
  ∀ x, Convex ℝ (Z x)

/-- A fiberwise vector field, with no regularity hidden in the type. -/
abbrev FiberwiseVectorField (F : M → Type*) := ∀ x, F x → F x

/-- Fiberwise tangent-cone preservation of a convex subbundle carrier. -/
def convexSubbundlePreservingVectorField (Z : FiberSet M F)
    (ψ : FiberwiseVectorField F) : Prop :=
  ∀ x, vectorFieldPreservesConvexSet (Z x) (ψ x)

/-- A family of declared linear transports between fibers.  The geometric
connection supplies this family; the predicate below does not conflate an
arbitrary equivalence with parallel transport. -/
abbrev LinearTransportFamily (F : M → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℝ (F x)] :=
  ∀ x y, Set (F x ≃ₗ[ℝ] F y)

/-- Invariance of a fiber family under every declared parallel transport.

The image equality records both directions of invariance for a linear
equivalence; a one-sided `MapsTo` statement would only express preservation.
-/
def parallelInvariantFiberSet (Z : FiberSet M F)
    (P : LinearTransportFamily F) : Prop :=
  ∀ x y (p : F x ≃ₗ[ℝ] F y), p ∈ P x y → p '' Z x = Z y

end MorganTianLib
