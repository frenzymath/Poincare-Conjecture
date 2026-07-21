import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhoodConvex
import DoCarmoLib.Riemannian.Exponential.MovingBaseProp36LowerBound

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Convex neighborhoods: discharging the base-uniform lower bound (do Carmo Ch. 3, §4)

The reductions of `ConvexNeighborhoodConvex.lean` package do Carmo's Proposition 4.2 for the closed
ball modulo two isolated hypotheses:

* `Hlb` — the *base-uniform lower bound*: short geodesics of small initial velocity near `p` realize
  the distance between their endpoints (`prop:dc-ch3-3-6`, phrased base-uniformly);
* `Huniq` — the *local uniqueness* of minimizing geodesics near `p`.

`Hlb` is now a theorem: `exists_movingBase_prop36_lower_bound`
(`MovingBaseProp36LowerBound.lean`) proves exactly the `Hlb` statement, base-uniformly over the ball
of centres, by transporting the Gauss radius comparison to the moving-base geodesic flow family.

This file feeds that proof into the two reductions, so:

* `exists_minimizing_interior_ball` — **unconditional** now: for every `p` there is `B₀ > 0` such
  that any two points of a small `closedBall p β` are joined by a *minimizing* geodesic whose open
  arc lies in the ball (the existence + minimizing + interior clauses of strong convexity, with no
  remaining hypothesis);
* `exists_stronglyConvex_closedBall_of_uniq` — the *whole* of do Carmo's Proposition 4.2 for the
  closed ball, reduced to the single residual `Huniq`.

The closed ball is used deliberately: the literal open-ball statement of
`def:dc-ch3-4-2-stronglyconvex` is unsatisfiable at a boundary diagonal `q₁ = q₂ ∈ ∂ B_β(p)`, where
the constant minimizing geodesic's interior `{q₁}` is not in the *open* ball.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal ENNReal

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M')]

/-- **Math.** **Minimizing geodesics with interior in the ball (do Carmo Prop 4.2, existence +
minimizing + interior, unconditional).** For every `p` there is `B₀ > 0` such that for every
`0 < β ≤ B₀`, any two points `q₁, q₂` of `closedBall p β` are joined by a geodesic `γ` on `[0,1]`
that is *minimizing* (`d(γ s, γ t) = |s-t| · d(q₁, q₂)`) and whose open arc `γ((0,1))` lies in
`closedBall p β`. This is the strong-convexity content of do Carmo's Proposition 4.2 except the
uniqueness clause; the base-uniform lower bound crux `Hlb` is now discharged by
`exists_movingBase_prop36_lower_bound`. -/
theorem exists_minimizing_interior_ball
    (g : RiemannianMetric I M') (hg : g.IsRiemannianDist) (p : M') :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ β : ℝ, 0 < β → β ≤ B₀ →
      ∀ q₁ ∈ closedBall p β, ∀ q₂ ∈ closedBall p β,
        ∃ γ : ℝ → M',
          γ 0 = q₁ ∧ γ 1 = q₂ ∧
          IsGeodesicOn (I := I) g γ (Icc 0 1) ∧
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (γ s) (γ t) = |s - t| * dist q₁ q₂) ∧
          γ '' Ioo (0 : ℝ) 1 ⊆ closedBall p β :=
  exists_minimizing_interior_ball_of_lower_bound (I := I) g hg p
    (exists_movingBase_prop36_lower_bound (I := I) g hg p)

/-- **Math.** **Convex neighborhoods (do Carmo Proposition 4.2), reduced to uniqueness alone.**
Given the *local uniqueness* `Huniq` of minimizing geodesics near `p` (any two constant-speed
distance-realizing geodesics joining the same pair of points near `p` coincide on `[0,1]` — do
Carmo's reading of the injectivity of `exp_{q₁}`), there is `β > 0` such that the **closed** geodesic
ball `closedBall p β` is strongly convex (`def:dc-ch3-4-2-stronglyconvex`). The base-uniform lower
bound `Hlb` is discharged internally by `exists_movingBase_prop36_lower_bound`, so `Huniq` is the
sole remaining hypothesis. This is the full Proposition 4.2 for the closed ball. -/
theorem exists_stronglyConvex_closedBall_of_uniq
    (g : RiemannianMetric I M') (hg : g.IsRiemannianDist) (p : M')
    (Huniq : ∃ βU : ℝ, 0 < βU ∧ ∀ (q₁ q₂ : M') (α β' : ℝ → M'),
               dist p q₁ ≤ βU → dist p q₂ ≤ βU →
               α 0 = q₁ → α 1 = q₂ → IsGeodesicOn (I := I) g α (Icc 0 1) →
               (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
                 dist (α s) (α t) = |s - t| * dist q₁ q₂) →
               β' 0 = q₁ → β' 1 = q₂ → IsGeodesicOn (I := I) g β' (Icc 0 1) →
               (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
                 dist (β' s) (β' t) = |s - t| * dist q₁ q₂) →
               Set.EqOn β' α (Icc 0 1)) :
    ∃ β : ℝ, 0 < β ∧ StronglyConvex (I := I) g (closedBall p β) :=
  exists_stronglyConvex_closedBall_of_lower_bound (I := I) g hg p
    (exists_movingBase_prop36_lower_bound (I := I) g hg p) Huniq

end Exponential

end Riemannian

end
