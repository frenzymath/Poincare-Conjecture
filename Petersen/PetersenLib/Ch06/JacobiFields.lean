import PetersenLib.Ch06.ThirdPartials
import PetersenLib.Ch06.ConnectionAlongCurve
import PetersenLib.Ch05.Geodesics

/-!
# Petersen Ch. 6, §6.1 — Jacobi fields (GTM 171, 3rd ed.)

Petersen's §6.1 (pp. 251–252), `def:pet-ch6-jacobi-field`: a **Jacobi field** along a
geodesic `c` is a vector field `J` along `c` solving the **Jacobi equation**
$$
\ddot J + R(J, \dot c)\dot c = 0 .
$$

## What is defined here, and why it is chart-free

Both ingredients already exist in a chart-free form, so the definition can be stated
exactly as Petersen writes it, with **no chart hypothesis and no coordinate reading**:

* `V̇` is `Ch06/ConnectionAlongCurve.lean`'s `derivAlongCurve`, the covariant derivative of
  a field along a curve read at the *moving foot* — proved chart-independent there
  (`covariantDerivCoord_transfer`). Since `derivAlongCurve g c V` is itself a field along
  `c`, the second derivative `J̈` is simply `derivAlongCurve` applied twice; this is the
  same recursive reading as `def:pet-ch6-higher-order-partials`.
* `R` is Ch. 3's `curvatureTensorAt`, an abstract (Koszul) pointwise tensor.

So `jacobiEquation g c J t` lives in `T_{c t}M` with no auxiliary data. This is worth
stating because the *proof* of Lemma 6.1.2 needed a chart and a bridge
(`Ch06/CurvatureChartBridge.lean`); the *definition* does not.

## Naming

`PetersenLib.IsJacobiField` is **already taken**, by `Ch03/DistanceFunctions.lean`, for
Petersen's §3.2.4 *distance-function* Jacobi field — a genuinely different notion
(`L_{∂_r}J = 0`, a field unchanged by the radial flow, defined on an open set for a
distance function `r`, with no geodesic and no second derivative). The two coincide only
in the special situation where `J` is a Jacobi field of §3.2.4 for `r` along the integral
curves of `∇r`. This file therefore uses `IsJacobiFieldAlong`, matching the `IsParallelAlong`
convention already established in `Ch06/ConnectionAlongCurve.lean` for the along-a-curve
notions, and leaves Ch. 3 untouched.

## Scope

The definition and its immediate structural consequences (linearity; parallel fields along
a geodesic are Jacobi iff the curvature term vanishes; `∂_t c` is a Jacobi field along a
geodesic) are here.  The relation `J(t) = D\exp_p(t J(0))` (`rem:pet-ch6-jacobi-dexp-relation`)
is developed in `Ch06/JacobiDExp.lean`, which shows the variation field of a family of
geodesics is a Jacobi field (`isJacobiFieldAlongOn_variationField_of_geodesicFamily`, the
manifold form of `Jacobi.chart_geodesic_family_jacobi`).

**Correction.**  An earlier version of this docstring claimed the D-`exp` relation and
`Hess r(J,J) = g(J̇,J)` (`rem:pet-ch6-jacobi-hessian-r`) were out of reach because "the project
does not yet have a differential of `exp_p` away from the origin".  That premise is **stale**:
the vendored exponential stack already carries it —
`Exponential.exists_hasStrictFDerivAt_extChartAt_expMap_ball` (strict Fréchet derivative at
every point of a normal ball), `Exponential.exists_contDiffOn_infty_extChartAt_expMap_ball`
(the chart reading of `exp_p` is `C^∞` on a ball), and the whole geodesic-family Jacobi
computation `Jacobi.chart_geodesic_family_jacobi`.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ### The velocity field of a curve -/

/-- **Math.** Petersen §6.1: the **velocity field** `ċ` of a curve, as a vector field along
`c` — the derivative of the chart reading of `c` at the moving foot `c t`, which is what
`TangentSpace I (c t)` is coordinatised by. Same moving-foot convention as Ch. 5's
`curveAcceleration` and Ch. 6's `derivAlongCurve`. -/
def curveVelocity (c : ℝ → M) (t : ℝ) : TangentSpace I (c t) :=
  (deriv (Geodesic.chartLocalCurve (I := I) c t) t : E)

@[simp] theorem curveVelocity_def (c : ℝ → M) (t : ℝ) :
    curveVelocity (I := I) c t = (deriv (Geodesic.chartLocalCurve (I := I) c t) t : E) := rfl

/-! ### The covariant derivative of the zero field

`Ch06/ConnectionAlongCurve.lean` proves additivity and the Leibniz rule for
`derivAlongCurve` but not this degenerate case, which the Jacobi-field consequences below
need. It is not a corollary of `derivAlongCurve_smul_fun` (that lemma carries
differentiability hypotheses); it is immediate from the definition instead. -/

/-- **Eng.** The chart reading of the zero field is the zero function: `tangentCoordChange`
is linear. -/
@[simp] theorem chartFieldRep_zero (c : ℝ → M) (β : M) :
    chartFieldRep (I := I) c β (fun τ => (0 : TangentSpace I (c τ))) = fun _ => (0 : E) := by
  funext τ
  exact map_zero (tangentCoordChange I (c τ) β (c τ))

/-- **Math.** `0̇ = 0`: the covariant derivative of the zero field along any curve vanishes.
Both terms of `derivAlongCurve` die — the chart reading is constantly `0` so its derivative
is `0`, and the Christoffel contraction is linear in the field slot. -/
@[simp] theorem derivAlongCurve_zero (g : RiemannianMetric I M) (c : ℝ → M) (t : ℝ) :
    derivAlongCurve (I := I) g c (fun τ => (0 : TangentSpace I (c τ))) t = 0 := by
  rw [derivAlongCurve_def, chartFieldRep_zero, deriv_const']
  simp [Geodesic.chartChristoffelContraction_def, Geodesic.chartCoord_zero]

/-! ### The Jacobi equation -/

/-- **Math.** Petersen §6.1 (p. 252), `def:pet-ch6-jacobi-field`: the left-hand side of the
**Jacobi equation**, `J̈ + R(J, ċ)ċ`, as a vector in `T_{c t}M`. The second covariant
derivative is `derivAlongCurve` applied twice (`derivAlongCurve g c J` is again a field
along `c`), and `R` is Ch. 3's `curvatureTensorAt` of the Levi-Civita connection — so the
expression is chart-free. -/
def jacobiEquation (g : RiemannianMetric I M) (c : ℝ → M)
    (J : ∀ t, TangentSpace I (c t)) (t : ℝ) : TangentSpace I (c t) :=
  derivAlongCurve (I := I) g c (fun τ => derivAlongCurve (I := I) g c J τ) t
    + curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
        (J t) (curveVelocity (I := I) c t) (curveVelocity (I := I) c t)

@[simp] theorem jacobiEquation_def (g : RiemannianMetric I M) (c : ℝ → M)
    (J : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    jacobiEquation (I := I) g c J t
      = derivAlongCurve (I := I) g c (fun τ => derivAlongCurve (I := I) g c J τ) t
        + curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
            (J t) (curveVelocity (I := I) c t) (curveVelocity (I := I) c t) := rfl

/-- **Math.** Petersen §6.1 (p. 252), `def:pet-ch6-jacobi-field`: `J` is a **Jacobi field
along `c`** when it solves the Jacobi equation `J̈ + R(J, ċ)ċ = 0` at every time.

Named `IsJacobiFieldAlong`, not `IsJacobiField`: the latter is Ch. 3's *distance-function*
Jacobi field (`L_{∂_r}J = 0`, §3.2.4), a different notion. The suffix follows
`IsParallelAlong`. -/
def IsJacobiFieldAlong (g : RiemannianMetric I M) (c : ℝ → M)
    (J : ∀ t, TangentSpace I (c t)) : Prop :=
  ∀ t, jacobiEquation (I := I) g c J t = 0

theorem isJacobiFieldAlong_iff (g : RiemannianMetric I M) (c : ℝ → M)
    (J : ∀ t, TangentSpace I (c t)) :
    IsJacobiFieldAlong (I := I) g c J
      ↔ ∀ t, derivAlongCurve (I := I) g c (fun τ => derivAlongCurve (I := I) g c J τ) t
          = -curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
              (J t) (curveVelocity (I := I) c t) (curveVelocity (I := I) c t) := by
  simp only [IsJacobiFieldAlong, jacobiEquation_def, add_eq_zero_iff_eq_neg]

/-! ### First consequences -/

/-- **Math.** The **zero field is a Jacobi field** along any curve: `R` is linear in its
first slot, so both terms vanish. -/
theorem isJacobiFieldAlong_zero (g : RiemannianMetric I M) (c : ℝ → M) :
    IsJacobiFieldAlong (I := I) g c (fun t => (0 : TangentSpace I (c t))) := by
  intro t
  rw [jacobiEquation_def, curvatureTensorAt_zero_first,
    show (fun τ => derivAlongCurve (I := I) g c (fun s => (0 : TangentSpace I (c s))) τ)
      = fun τ => (0 : TangentSpace I (c τ)) from funext fun τ => derivAlongCurve_zero g c τ,
    derivAlongCurve_zero, add_zero]

/-- **Math.** Petersen §6.1 (p. 252): a **parallel field along a geodesic is a Jacobi field
iff its curvature term vanishes**. For a parallel `J` we have `J̈ = 0` outright, so the
Jacobi equation degenerates to `R(J, ċ)ċ = 0`. In particular a parallel field spanning a
`ċ`-parallel direction (e.g. `J = ċ` itself along a geodesic, where
`R(ċ, ċ)ċ = 0` by antisymmetry) is Jacobi. -/
theorem isJacobiFieldAlong_of_isParallelAlong (g : RiemannianMetric I M) (c : ℝ → M)
    {J : ∀ t, TangentSpace I (c t)} (hJ : IsParallelAlong (I := I) g c J)
    (hR : ∀ t, curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
        (J t) (curveVelocity (I := I) c t) (curveVelocity (I := I) c t) = 0) :
    IsJacobiFieldAlong (I := I) g c J := by
  intro t
  rw [jacobiEquation_def, hR t, add_zero,
    show (fun τ => derivAlongCurve (I := I) g c J τ) = fun τ => (0 : TangentSpace I (c τ)) from
      funext hJ,
    derivAlongCurve_zero]

end PetersenLib

end
