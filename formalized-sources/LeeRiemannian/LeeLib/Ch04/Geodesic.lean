/-
Chapter 4, "Connections", §"Geodesics": the definition of a geodesic and the
geodesic equation, in chart coordinates.

For a connection `∇` in `TM`, Lee defines the **acceleration** of a smooth curve
`γ` to be `D_t γ'`, and calls `γ` a **geodesic** when its acceleration vanishes,
`D_t γ' ≡ 0` — i.e. a geodesic is exactly a curve whose velocity field is parallel
along it.  Read in a chart (via the covariant derivative along a curve
`covariantDerivAlongChart` of `LeeLib.Ch04.ParallelTransport`), the acceleration of
the coordinate curve `u : ℝ → E` is `ü + Γ(u̇, u̇)(c)`, so the geodesic condition
is Lee's **geodesic equation** (4.16)

  `ü(t) + Γ(u̇(t), u̇(t))(c(t)) = 0`,

equivalently the first-order form `u̇' = −Γ(u̇, u̇)(c)`.  This is the (nonlinear,
quadratic-in-velocity) ODE whose solutions are geodesics; existence/uniqueness of
solutions (Theorem 4.27) is the geodesic-spray/integral-curve construction, left to
a later development.  This file records the definition and the equation.
-/
import LeeLib.Ch04.ParallelTransport

namespace LeeLib.Ch04

open Bundle Module
open scoped Manifold ContDiff Topology
open Set

set_option linter.unusedSectionVars false

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι]
  {e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)}
  [MemTrivializationAtlas e] {b : Basis ι ℝ E}

/-- **Acceleration of a curve** (Lee, §"Geodesics"): the covariant derivative `D_t γ'`
of the velocity field of `γ`, read in a chart.  For the coordinate curve `u : ℝ → E`
(chart image of `γ`, over the base curve `c : ℝ → M`), it is `ü + Γ(u̇, u̇)(c)`. -/
def chartAcceleration (cov : Connection I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Basis ι ℝ E) (u : ℝ → E) (c : ℝ → M) (t : ℝ) : E :=
  covariantDerivAlongChart cov e b u c (deriv u) t

@[simp] theorem chartAcceleration_def (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) (t : ℝ) :
    chartAcceleration cov e b u c t
      = deriv (deriv u) t + chartGamma cov e b (deriv u t) (deriv u t) (c t) := rfl

/-- **Geodesic** (Lee, §"Geodesics"): a curve is a geodesic when its acceleration
vanishes, `D_t γ' ≡ 0` — equivalently, its velocity field is parallel along it. -/
def IsGeodesicInChart (cov : Connection I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Basis ι ℝ E) (u : ℝ → E) (c : ℝ → M) : Prop :=
  ∀ t, chartAcceleration cov e b u c t = 0

/-- A geodesic is exactly a curve whose velocity is parallel along it (Lee's
characterization "a geodesic is a curve whose velocity vector field is parallel"). -/
theorem isGeodesicInChart_iff_isParallel (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) :
    IsGeodesicInChart cov e b u c ↔ IsParallelAlongChart cov e b u c (deriv u) :=
  Iff.rfl

/-- **Lee's geodesic equation (4.16)**: `γ` is a geodesic iff its coordinate curve
satisfies `ü(t) + Γ(u̇(t), u̇(t))(c(t)) = 0` for all `t`. -/
theorem isGeodesicInChart_iff (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) :
    IsGeodesicInChart cov e b u c
      ↔ ∀ t, deriv (deriv u) t + chartGamma cov e b (deriv u t) (deriv u t) (c t) = 0 :=
  Iff.rfl

/-- **Lee's geodesic equation, first-order (solved) form** (4.16)/(4.17): a curve whose
velocity `u̇` is (everywhere) differentiable is a geodesic iff its velocity solves the
first-order system `u̇'(t) = −Γ(u̇(t), u̇(t))(c(t))`. -/
theorem isGeodesicInChart_iff_hasDerivAt (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) (hu : ∀ t, DifferentiableAt ℝ (deriv u) t) :
    IsGeodesicInChart cov e b u c
      ↔ ∀ t, HasDerivAt (deriv u) (-chartGamma cov e b (deriv u t) (deriv u t) (c t)) t :=
  isParallelAlongChart_iff_hasDerivAt cov u c (deriv u) hu

end

end LeeLib.Ch04
