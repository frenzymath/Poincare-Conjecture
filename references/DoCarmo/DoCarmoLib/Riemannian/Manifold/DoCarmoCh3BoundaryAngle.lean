import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3VertexAngle
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3SurfaceBoundary
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# do Carmo Chapter 3, Definition 3.3: the boundary vertex angles are angles

Definition 3.3 requires the boundary `∂A` of a parametrized surface to be a
piecewise differentiable curve *with vertex angles different from `π`*.
`DoCarmoCh3SurfaceBoundary.lean` states that as `IsNonPiAngle`, which is an
*algebraic* condition: both one-sided tangents are nonzero and the outgoing one is
not a negative multiple of the incoming one.

That is the right condition, but as stated it never mentions an angle, so nothing
connected it to the book's word "angle". This file supplies the connection, for
the plane tangents of the boundary and hence for the boundary parametrization's own
vertices.

## Why the `WithLp 2` detour is necessary rather than decorative

`ℝ × ℝ` carries the *sup* norm in mathlib, so it is not an inner-product space and
`InnerProductGeometry.angle` is not available on it — the instance genuinely does
not exist, it is not a matter of unfolding. `WithLp 2 (ℝ × ℝ)` is the same type
with the Euclidean norm, where the angle is defined. `WithLp.toLp 2` is a linear
equivalence, so transporting along it changes nothing about the algebra: the
non-opposition condition is preserved in both directions, which is exactly what
`isNonPiAngle_iff_angle_ne_pi` proves.

This is also why the identification is worth having rather than obvious. It says
`IsNonPiAngle` is not an arbitrary algebraic stand-in: it is the Euclidean vertex
angle differing from `π`, which is what do Carmo wrote.
-/

open Set Riemannian Riemannian.Geodesic InnerProductGeometry

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Riemannian.Geodesic

/-- **Math.** **`IsNonPiAngle` is exactly "the Euclidean angle differs from `π`".**
For nonzero plane vectors, the algebraic non-opposition condition of Definition
3.3 and the metric statement `∠(v,w) ≠ π` are the same condition, read in the
Euclidean (`L²`) structure on `ℝ × ℝ` where the angle exists.

The nonvanishing hypotheses are the ones `IsNonPiAngle` already carries in its own
first two clauses, so nothing is assumed here that Definition 3.3 does not. -/
theorem isNonPiAngle_iff_angle_ne_pi (v w : ℝ × ℝ) (hv : v ≠ 0) (hw : w ≠ 0) :
    IsNonPiAngle v w ↔
      angle (WithLp.toLp 2 v : WithLp 2 (ℝ × ℝ)) (WithLp.toLp 2 w) ≠ Real.pi := by
  have hv' : (WithLp.toLp 2 v : WithLp 2 (ℝ × ℝ)) ≠ 0 := by simpa using hv
  have key : angle (WithLp.toLp 2 v : WithLp 2 (ℝ × ℝ)) (WithLp.toLp 2 w) = Real.pi
      ↔ ∃ c : ℝ, 0 < c ∧ w = (-c) • v := by
    rw [InnerProductGeometry.angle_eq_pi_iff]
    constructor
    · rintro ⟨-, r, hrneg, hr⟩
      refine ⟨-r, by linarith, ?_⟩
      have hlp : (WithLp.toLp 2 w : WithLp 2 (ℝ × ℝ)) = WithLp.toLp 2 ((-(-r)) • v) := by
        rw [hr]; norm_num
      exact WithLp.toLp_injective 2 hlp
    · rintro ⟨c, hcpos, rfl⟩
      exact ⟨hv', -c, by linarith, rfl⟩
  rw [IsNonPiAngle, Ne,
    show (angle (WithLp.toLp 2 v : WithLp 2 (ℝ × ℝ)) (WithLp.toLp 2 w) ≠ Real.pi)
      = ¬ (angle (WithLp.toLp 2 v : WithLp 2 (ℝ × ℝ)) (WithLp.toLp 2 w) = Real.pi) from rfl,
    not_congr key]
  exact ⟨fun h => h.2.2, fun h => ⟨hv, hw, h⟩⟩

namespace PiecewiseC1BoundaryParametrization

variable {A : Set (ℝ × ℝ)} (B : PiecewiseC1BoundaryParametrization A)

/-- **Math.** **do Carmo Def. 3.3 at an interior boundary vertex:** the Euclidean
angle between the incoming and outgoing one-sided tangents differs from `π`.

This is the book's sentence for the boundary of a parametrized surface, stated
about an angle.  The incoming tangent at vertex `i` is `incomingTangent (i - 1)`:
it belongs to the piece *ending* at that vertex. -/
theorem interior_vertex_angle_ne_pi {i : ℕ} (hi0 : 0 < i) (hin : i < B.n) :
    angle (WithLp.toLp 2 (B.incomingTangent (i - 1)) : WithLp 2 (ℝ × ℝ))
        (WithLp.toLp 2 (B.outgoingTangent i)) ≠ Real.pi := by
  have h := B.interior_vertex_nonPi hi0 hin
  exact (isNonPiAngle_iff_angle_ne_pi _ _ h.incoming_ne_zero h.outgoing_ne_zero).mp h

/-- **Math.** The same at the vertex where the boundary cycle closes, which
Definition 3.3 constrains along with the interior ones — the boundary is a closed
curve, so the point where the parametrization returns to its start is a vertex like
any other. -/
theorem closing_vertex_angle_ne_pi :
    angle (WithLp.toLp 2 B.closingIncomingTangent : WithLp 2 (ℝ × ℝ))
        (WithLp.toLp 2 B.closingOutgoingTangent) ≠ Real.pi := by
  have h := B.closing_vertex_nonPi
  exact (isNonPiAngle_iff_angle_ne_pi _ _ h.incoming_ne_zero h.outgoing_ne_zero).mp h

end PiecewiseC1BoundaryParametrization

end Riemannian.Geodesic
