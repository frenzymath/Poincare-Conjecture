# Relative arc winding and extension

## Informal description

Let r > 0. Two continuous paths with common endpoints in the exterior of
(-r,r)^2, admitting continuous angular lifts that agree at both endpoints,
admit a continuous homotopy in that exterior fixing both endpoints.
Square-boundary contact is permitted. Having the same relative winding is
defined here to mean admitting this endpoint-relative continuous homotopy.

For a fixed closed square, a smooth family of embedded regular arcs, stationary
on two nontrivial endpoint intervals and outside that square on the intervening
interval, admits an ambient isotopy whose time-one map carries the initial
arc to the final arc with their given parametrizations. The isotopy and its inverse
are jointly smooth for all real times and have a common compact support
disjoint from the fixed square. Its time-one map carries the first arc to the
last with the given parametrizations.
Here smoothness holds on an open neighborhood of the parameter rectangle;
the stationary intervals are [0,l] and [u,1] with 0 < l <= u < 1.
The coordinate radius of the fixed closed square can be any real number,
with the square interpreted as empty when that radius is negative.

## Informal proof

Interpolate the angular lifts and the positive square gauges linearly.
Rescale the interpolated unit direction to have the interpolated gauge.
The gauge stays at least r, and agreement of the angular lifts at the
endpoints makes this a homotopy relative to those endpoints.

For ambient extension, choose smaller endpoint intervals inside the stationary
ones and apply relative interval isotopy extension in the complement of the
fixed closed square. Parametric inversion gives smoothness of the inverses.

These arguments do not prove that the continuous homotopy can be replaced by
a smooth embedded family. That is the remaining geometric producer obligation.

## Proposed formal statements

```lean
import PoincareLib.Topology.Manifold.Schoenflies.Plane.Arcs.SquareInversion
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Coordinates
import PoincareLib.Topology.Manifold.Schoenflies.Isotopy.Interval.RelativeLocal
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Basic

noncomputable section
open Set
open scoped Manifold ContDiff unitInterval
namespace Poincare.Manifold.Schoenflies.PlaneArcs

def SameWindingRelSquare (r : Real)
    (α β : C(unitInterval, EuclideanSpace Real (Fin 2))) : Prop :=
  ∃ H : α.HomotopyRel β {0, 1}, ∀ p, r ≤ squareGauge (H p)

theorem sameWindingRelSquare_of_argument_lifts
    {r : Real} (hr : 0 < r)
    (α β : C(unitInterval, EuclideanSpace Real (Fin 2)))
    (hα : ∀ s, r ≤ squareGauge (α s))
    (hβ : ∀ s, r ≤ squareGauge (β s))
    (hzero : α 0 = β 0) (hone : α 1 = β 1)
    (θ₀ θ₁ : C(unitInterval, Real))
    (hθ₀ : ∀ s, (Circle.exp (θ₀ s) : Complex) =
      ‖α s‖⁻¹ • Complex.orthonormalBasisOneI.repr.symm (α s))
    (hθ₁ : ∀ s, (Circle.exp (θ₁ s) : Complex) =
      ‖β s‖⁻¹ • Complex.orthonormalBasisOneI.repr.symm (β s))
    (hθzero : θ₀ 0 = θ₁ 0) (hθone : θ₀ 1 = θ₁ 1) :
    SameWindingRelSquare r α β := by
  sorry

theorem exists_planar_arc_isotopy_rel_square_of_family
    {ρ l u : Real} {α β : Real → EuclideanSpace Real (Fin 2)}
    (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1)
    (F : Real × Real → EuclideanSpace Real (Fin 2)) {W : Set (Real × Real)}
    (hW : IsOpen W) (hrect : Icc (0 : Real) 1 ×ˢ Icc (0 : Real) 1 ⊆ W)
    (hF : ContDiffOn Real ∞ F W)
    (hstart : ∀ s ∈ Icc (0 : Real) 1, F (0, s) = α s)
    (hend : ∀ s ∈ Icc (0 : Real) 1, F (1, s) = β s)
    (hinj : ∀ t ∈ Icc (0 : Real) 1,
      InjOn (fun s => F (t, s)) (Icc (0 : Real) 1))
    (hder : ∀ t ∈ Icc (0 : Real) 1, ∀ s ∈ Icc (0 : Real) 1,
      deriv (fun y => F (t, y)) s ≠ 0)
    (hstationary : ∀ t ∈ Icc (0 : Real) 1,
      ∀ s ∈ Icc (0 : Real) l ∪ Icc u 1, F (t, s) = F (0, s))
    (htrace : ∀ t ∈ Icc (0 : Real) 1, ∀ s ∈ Icc l u,
      F (t, s) ∉ SaddleLevel.closedSquare ρ) :
    ∃ K : Set (EuclideanSpace Real (Fin 2)), IsCompact K ∧
      Disjoint K (SaddleLevel.closedSquare ρ) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2)
          (EuclideanSpace Real (Fin 2)) (EuclideanSpace Real (Fin 2)) ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × EuclideanSpace Real (Fin 2) => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × EuclideanSpace Real (Fin 2) => (Φ z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Φ t x = x) ∧
        ∀ t ∈ Icc (0 : Real) 1, Φ 1 (α t) = β t := by
  sorry

end Poincare.Manifold.Schoenflies.PlaneArcs
```

## Alignment review

Independent formal-only translation and prose-only review accepted the
statements with the precise description above on 23 September 2026.
The review required explicit common endpoints, positive winding radius,
boundary contact, and time-one rather than intermediate-time matching.
The continuous winding statement is not an embedded-isotopy theorem.
The family assumptions are explicit binders in the final extension lemma;
no predicate packages an assumed isotopy. Expanding those binders preserves
the reviewed mathematical proposition.

## Annular integration

For two nonzero continuous connectors with common endpoints on the circles of
radii r and R, where 0 < r < R, an annularly supported smooth norm-preserving
twist makes the connectors homotopic relative to their endpoints outside some
positive square. The twist is the existing integer winding correction;
compactness supplies a common positive square-gauge lower bound.

```lean
import PoincareLib.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Winding
import PoincareLib.Topology.Manifold.Schoenflies.Plane.CirclePair.Annulus.Winding
open Set
open scoped Manifold ContDiff unitInterval
namespace Poincare.Manifold.Schoenflies.PlaneArcs
theorem exists_twist_sameWindingRelSquare
    {r R : Real} (hr : 0 < r) (hrR : r < R)
    (g₀ g₁ : C(unitInterval, EuclideanSpace Real (Fin 2)))
    (hg₀ : ∀ t, g₀ t ≠ 0) (hg₁ : ∀ t, g₁ t ≠ 0)
    (hzero : g₀ 0 = g₁ 0) (hone : g₀ 1 = g₁ 1)
    (hstart : ‖g₀ 0‖ = r) (hend : ‖g₀ 1‖ = R) :
    ∃ K : Set (EuclideanSpace Real (Fin 2)),
      IsCompact K ∧ K ⊆ {x | r < ‖x‖ ∧ ‖x‖ < R} ∧
      ∃ D : Diffeomorph (𝓡 2) (𝓡 2)
          (EuclideanSpace Real (Fin 2)) (EuclideanSpace Real (Fin 2)) ∞,
        (∀ x ∉ K, D x = x) ∧ (∀ x, ‖D x‖ = ‖x‖) ∧
        ∃ ρ : Real, 0 < ρ ∧
          SameWindingRelSquare ρ g₀
            ((⟨fun x => D x, D.continuous⟩ : C(EuclideanSpace Real (Fin 2),
              EuclideanSpace Real (Fin 2))).comp g₁) := by
  sorry
end Poincare.Manifold.Schoenflies.PlaneArcs
```

The independent translator and reviewer also accepted the annular integration
statement on 23 September 2026. The connectors need not themselves stay in the
support annulus; the positive square is chosen from their compact traces.

## Informal translation

For a positive radius r, let two continuous paths avoid the open square
(-r,r)^2 and have equal initial and terminal points. If their continuous
angular lifts have equal values at both endpoints, there is a continuous
endpoint-fixed homotopy between the paths avoiding the same open square.

Let 0 < l <= u < 1. Suppose a family F is smooth on an open neighborhood of
[0,1]^2, each parameter slice is injective with nonzero derivative in the arc
parameter, the slices are constant in time on [0,l] and [u,1], and the traces
of [l,u] avoid the fixed closed square. There are a compact set disjoint from
that square and an all-real-time family of plane diffeomorphisms, jointly
smooth in both directions, identity at time zero and outside that compact
set at every time, taking F(0,s) to F(1,s) at time one.

Let 0 < r < R and let two continuous paths in the punctured plane have common
initial and terminal points of norms r and R. There is a smooth
norm-preserving plane diffeomorphism supported on a compact subset of the
open annulus r < norm(x) < R and a positive radius rho such that the first
path and the image of the second admit an endpoint-fixed continuous homotopy
outside the open square (-rho,rho)^2.

## Candidate hashes

SHA-256 of the displayed declaration blocks, including the candidate proof
`by sorry` for theorems and the trailing blank line for the definition:

| Declaration | SHA-256 |
| --- | --- |
| `SameWindingRelSquare` | `9ffa9e6a9cc7840d431b034eaa4343492bcdc439288cbe9e6ab2b8ce9ffeb44c` |
| `sameWindingRelSquare_of_argument_lifts` | `d989b14ba8c180b964cc1215b5e23746e7e2a6bce3251b7fb0bd1d3f5f03ce31` |
| `exists_planar_arc_isotopy_rel_square_of_family` | `588c09dbb106745558516e70bc52b8d2c3bdb04fb6da5798b9c6012eb886a4c2` |
| `exists_twist_sameWindingRelSquare` | `3875b51972a74478d53c921e6a9b600589c68b97540475440ab001bb201d0ebc` |

The compiled declarations have complete proofs. The audit is in `Checks.lean`.

## Verification

Lean 4.33.1: the focused `Arcs.Checks` build passed, and all four audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
`make check` passed all 12 frozen-contract hashes and 20,304 build jobs on
23 September 2026. These checks establish the winding and extension lemmas;
the height-parametrized critical-slab matching remains unproved.

## References

Hatcher, *Algebraic Topology*, Section 1.3, Proposition 1.30, printed p. 60
(homotopy lifting); the explicit square-gauge interpolation is elementary.
Relative interval extension uses the existing proved
`exists_relative_ambient_isotopy_of_interval_isotopy_within_of_contDiffOn`.
