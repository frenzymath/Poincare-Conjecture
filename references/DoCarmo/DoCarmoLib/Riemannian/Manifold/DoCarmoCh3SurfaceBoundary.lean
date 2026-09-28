import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3SurfaceRegularity

/-!
# The boundary data in do Carmo, Chapter 3, Definition 3.3

The legacy surface predicate records only map regularity.  This file records
the remaining geometric data explicitly: a finite piecewise-`C^1` closed
parametrization of the frontier, its one-sided tangent vectors at every
breakpoint (including the cyclic endpoint), and the exclusion of a straight
angle.  The extension predicate from `DoCarmoCh3SurfaceRegularity` is retained
as a separate component; no choice-independence statement is asserted here.
-/

open Manifold Set
open scoped ContDiff Manifold Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## One-sided angles -/

/-- **Math.** Two nonzero planar vectors make a non-`pi` angle when they are not
oppositely directed.  This is the algebraic form of the vertex-angle clause;
it avoids choosing an inverse-trigonometric convention. -/
def IsNonPiAngle (vIncoming vOutgoing : ℝ × ℝ) : Prop :=
  vIncoming ≠ 0 ∧ vOutgoing ≠ 0 ∧
    ¬ ∃ c : ℝ, 0 < c ∧ vOutgoing = (-c) • vIncoming

namespace IsNonPiAngle

variable {vIncoming vOutgoing : ℝ × ℝ}

theorem incoming_ne_zero (h : IsNonPiAngle vIncoming vOutgoing) :
    vIncoming ≠ 0 := h.1

theorem outgoing_ne_zero (h : IsNonPiAngle vIncoming vOutgoing) :
    vOutgoing ≠ 0 := h.2.1

theorem not_opposite (h : IsNonPiAngle vIncoming vOutgoing) :
    ¬ ∃ c : ℝ, 0 < c ∧ vOutgoing = (-c) • vIncoming := h.2.2

end IsNonPiAngle

/-! ## A finite boundary parametrization -/

/-- **Math.** A finite piecewise-`C¹` parametrization of the boundary of a
planar set.  The image equality makes the coverage of the frontier explicit;
`endpoint_eq` closes the parameter interval into a boundary cycle.  The
`piece_tangent_ne_zero` field supplies the one-sided tangent on each side of
every breakpoint, while `vertex_angle_nonPi` also checks the cyclic endpoint.

The derivatives are `derivWithin` on the adjacent closed pieces.  Thus at an
interior breakpoint they are genuinely the right and left one-sided
derivatives, rather than an unqualified derivative of a piecewise map. -/
structure PiecewiseC1BoundaryParametrization (A : Set (ℝ × ℝ)) where
  /-- The compact parameter interval. -/
  a : ℝ
  b : ℝ
  /-- Number of pieces in the finite subdivision. -/
  n : ℕ
  /-- Breakpoint map, with `tau 0 = a` and `tau n = b`. -/
  tau : ℕ → ℝ
  /-- The boundary map, defined globally so that `derivWithin` is available. -/
  gamma : ℝ → ℝ × ℝ
  n_pos : 0 < n
  a_lt_b : a < b
  tau_zero : tau 0 = a
  tau_last : tau n = b
  tau_strict : ∀ i : ℕ, i < n → tau i < tau (i + 1)
  continuous : ContinuousOn gamma (Icc a b)
  piecewise_c1 : ∀ i : ℕ, i < n →
    ContDiffOn ℝ 1 gamma (Icc (tau i) (tau (i + 1)))
  /-- The two ends represent the same point of the closed boundary. -/
  endpoint_eq : gamma a = gamma b
  /-- Every point of the parameter interval maps to the frontier, and every
  frontier point is covered by the parametrization. -/
  coverage : gamma '' Icc a b = frontier A
  /-- Every one-sided tangent of every piece is nonzero. -/
  piece_tangent_ne_zero :
    ∀ i : ℕ, i < n →
      derivWithin gamma (Icc (tau i) (tau (i + 1))) (tau i) ≠ 0 ∧
        derivWithin gamma (Icc (tau i) (tau (i + 1))) (tau (i + 1)) ≠ 0
  /-- Interior and cyclic endpoint vertices have angle different from `pi`. -/
  vertex_angle_nonPi :
    (∀ i : ℕ, 0 < i → i < n →
      IsNonPiAngle
        (derivWithin gamma (Icc (tau (i - 1)) (tau i)) (tau i))
        (derivWithin gamma (Icc (tau i) (tau (i + 1))) (tau i))) ∧
      IsNonPiAngle
        (derivWithin gamma (Icc (tau (n - 1)) (tau n)) (tau n))
        (derivWithin gamma (Icc (tau 0) (tau 1)) (tau 0))

namespace PiecewiseC1BoundaryParametrization

variable {A : Set (ℝ × ℝ)} (B : PiecewiseC1BoundaryParametrization A)

/-- **Math.** The outgoing one-sided tangent at the start of piece `i`. -/
def outgoingTangent (i : ℕ) : ℝ × ℝ :=
  derivWithin B.gamma (Icc (B.tau i) (B.tau (i + 1))) (B.tau i)

/-- **Math.** The incoming one-sided tangent at the end of piece `i`. -/
def incomingTangent (i : ℕ) : ℝ × ℝ :=
  derivWithin B.gamma (Icc (B.tau i) (B.tau (i + 1))) (B.tau (i + 1))

/-- **Math.** The incoming tangent at the cyclic endpoint. -/
def closingIncomingTangent : ℝ × ℝ := B.incomingTangent (B.n - 1)

/-- **Math.** The outgoing tangent at the cyclic endpoint. -/
def closingOutgoingTangent : ℝ × ℝ := B.outgoingTangent 0

theorem outgoingTangent_ne_zero {i : ℕ} (hi : i < B.n) :
    B.outgoingTangent i ≠ 0 :=
  (B.piece_tangent_ne_zero i hi).1

theorem incomingTangent_ne_zero {i : ℕ} (hi : i < B.n) :
    B.incomingTangent i ≠ 0 :=
  (B.piece_tangent_ne_zero i hi).2

theorem closingIncomingTangent_ne_zero :
    B.closingIncomingTangent ≠ 0 := by
  have hidx : B.n - 1 < B.n := by
    simpa [← Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt B.n_pos)
  have hlast : B.n - 1 + 1 = B.n := Nat.sub_add_cancel B.n_pos
  unfold closingIncomingTangent incomingTangent
  simpa only [hlast] using (B.piece_tangent_ne_zero (B.n - 1) hidx).2

theorem closingOutgoingTangent_ne_zero :
    B.closingOutgoingTangent ≠ 0 := by
  unfold closingOutgoingTangent outgoingTangent
  exact (B.piece_tangent_ne_zero 0 B.n_pos).1

theorem boundary_mem {t : ℝ} (ht : t ∈ Icc B.a B.b) :
    B.gamma t ∈ frontier A := by
  rw [← B.coverage]
  exact ⟨t, ht, rfl⟩

theorem exists_parameter {p : ℝ × ℝ} (hp : p ∈ frontier A) :
    ∃ t ∈ Icc B.a B.b, B.gamma t = p := by
  rw [← B.coverage] at hp
  exact hp

theorem interior_vertex_nonPi {i : ℕ} (hi0 : 0 < i) (hin : i < B.n) :
    IsNonPiAngle
      (B.incomingTangent (i - 1))
      (B.outgoingTangent i) := by
  have hi : i - 1 + 1 = i := by omega
  simpa only [incomingTangent, outgoingTangent, hi] using
    B.vertex_angle_nonPi.1 i hi0 hin

theorem closing_vertex_nonPi :
    IsNonPiAngle B.closingIncomingTangent B.closingOutgoingTangent := by
  have hlast : B.n - 1 + 1 = B.n := Nat.sub_add_cancel B.n_pos
  simpa only [closingIncomingTangent, closingOutgoingTangent, incomingTangent,
    outgoingTangent, hlast] using B.vertex_angle_nonPi.2

end PiecewiseC1BoundaryParametrization

/-! ## Surfaces carrying the full Definition 3.3 data -/

/-- **Math.** A do Carmo Ch. 3 parametrized surface with its full boundary
data and an order-`r` open-neighborhood extension. -/
structure IsParametrizedSurfaceWithBoundary
    (I : ModelWithCorners ℝ E H) (r : ℕ∞ω)
    (A : Set (ℝ × ℝ)) (s : ℝ × ℝ → M) : Prop
    extends IsExtendedParametrizedSurfaceOfOrder I r A s where
  boundary : Nonempty (PiecewiseC1BoundaryParametrization A)

/-- **Math.** The smooth (`C^∞`) version of a surface with boundary. -/
abbrev IsSmoothParametrizedSurfaceWithBoundary
    (I : ModelWithCorners ℝ E H) (A : Set (ℝ × ℝ)) (s : ℝ × ℝ → M) : Prop :=
  IsParametrizedSurfaceWithBoundary I ∞ A s

namespace IsParametrizedSurfaceWithBoundary

variable {r r' : ℕ∞ω} {A : Set (ℝ × ℝ)} {s : ℝ × ℝ → M}

/-- **Math.** Forget the chosen boundary parametrization. -/
theorem toExtended (hs : IsParametrizedSurfaceWithBoundary I r A s) :
    IsExtendedParametrizedSurfaceOfOrder I r A s :=
  hs.toIsExtendedParametrizedSurfaceOfOrder

/-- **Math.** Forgetting the surface map retains the connected parameter set
and its open core. -/
theorem surfaceDomain (hs : IsParametrizedSurfaceWithBoundary I r A s) :
    ParametrizedSurfaceDomain A :=
  hs.toExtended.domain

/-- **Math.** The map-regularity predicate retained after forgetting all boundary data. -/
theorem regularOn (hs : IsParametrizedSurfaceWithBoundary I r A s) :
    IsParametrizedSurfaceOfOrder I r A s :=
  hs.toExtended.regularOn

/-- **Math.** Forgetting the boundary data and all regularity above `C¹`. -/
theorem isParametrizedSurface
    (hs : IsParametrizedSurfaceWithBoundary I r A s)
    (hr : (1 : ℕ∞ω) ≤ r) : IsParametrizedSurface (I := I) A s :=
  hs.toExtended.isParametrizedSurface hr

/-- **Math.** Add a boundary parametrization to an already extended surface. -/
theorem of_extended
    (hs : IsExtendedParametrizedSurfaceOfOrder I r A s)
    (hboundary : PiecewiseC1BoundaryParametrization A) :
    IsParametrizedSurfaceWithBoundary I r A s :=
  ⟨hs, ⟨hboundary⟩⟩

/-- **Math.** Lower regularity while retaining exactly the same boundary data. -/
theorem of_le (hs : IsParametrizedSurfaceWithBoundary I r A s)
    (hrr' : r' ≤ r) : IsParametrizedSurfaceWithBoundary I r' A s := by
  exact ⟨hs.toExtended.of_le hrr', hs.boundary⟩

end IsParametrizedSurfaceWithBoundary

end Geodesic
end Riemannian
