import KleinerLott.RicciFlow.FlowData

/-!
# Kappa noncollapsing

This file defines the metric-measure predicates used to state local
noncollapsing for Ricci flows.
-/

namespace KleinerLott

namespace RicciFlowData

/-- The open ball for the metric at a specified time. -/
def ball {M : Type*} (flow : RicciFlowData M) (t : ℝ) (x₀ : M) (r : ℝ) :
    Set M :=
  {x | flow.dist t x₀ x < r}

/-- A curvature bound on a terminal-time ball throughout a backward time
interval whose length is the square of the radius. -/
def HasCurvatureBoundOnParabolicBall {M : Type*} (flow : RicciFlowData M)
    (x₀ : M) (t₀ r bound : ℝ) : Prop :=
  ∀ x ∈ flow.ball t₀ x₀ r, ∀ t ∈ Set.Icc (t₀ - r ^ 2) t₀,
    flow.curvatureNorm x t ≤ bound

end RicciFlowData

/-- A flow on `[0, T)` is kappa-noncollapsed on scale `rho` when every
admissible parabolic ball has the prescribed volume lower bound. -/
def IsKappaNoncollapsedOnScale {M : Type*} (flow : RicciFlowData M) (n : ℕ)
    (T kappa rho : ℝ) : Prop :=
  ∀ x₀ t₀ r, 0 < r → r < rho → r ^ 2 ≤ t₀ → t₀ < T →
    flow.HasCurvatureBoundOnParabolicBall x₀ t₀ r ((r⁻¹) ^ 2) →
      kappa * r ^ n ≤ flow.volume t₀ (flow.ball t₀ x₀ r)

/-- A flow is kappa-collapsed at a spacetime point on scale `r` when
curvature is controlled on the associated parabolic ball but its terminal
volume is at most `kappa * r ^ n`. -/
def IsKappaCollapsedAt {M : Type*} (flow : RicciFlowData M) (n : ℕ)
    (kappa r t₀ : ℝ) (x₀ : M) : Prop :=
  0 < r ∧
    flow.HasCurvatureBoundOnParabolicBall x₀ t₀ r ((r⁻¹) ^ 2) ∧
      flow.volume t₀ (flow.ball t₀ x₀ r) ≤ kappa * r ^ n

end KleinerLott
