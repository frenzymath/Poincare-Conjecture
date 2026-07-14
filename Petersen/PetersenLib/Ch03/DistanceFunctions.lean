import PetersenLib.Ch02.CovariantDerivative
import PetersenLib.Ch01.RiemannianManifolds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Norm

/-!
# Petersen Ch. 3, §3.2.1–§3.2.6 — Distance functions, Jacobi and parallel fields

The first definitional layer of Petersen §3.2 ("The Equations of Riemannian
Geometry"): the Hessian **operator** `S(X) = ∇_X∇f` (`hessianOperator`), the
notion of a **distance function** `r` (`IsDistanceFunction`: smooth, solving
the eikonal equation `|∇r|² = 1`), the associated notation `∂_r = ∇r`, `S = ∇∂_r`
(`distanceFunctionNotation`), **Jacobi fields** (`IsJacobiField`,
`L_{∂_r}J = 0`) together with the first-order form of the Jacobi equation
(`jacobiField_equivalentEquation`, `∇_{∂_r}J = S(J)`, proved via
torsion-freeness), **parallel fields** (`IsParallelField`, `∇_{∂_r}X = 0`),
and **conjugate points** (`ConjugatePoint`).

## Design notes

* As throughout the Ch. 2–3 API, vector fields are raw sections
  `Π x : M, TangentSpace I x` with explicit `IsSmoothVectorField` hypotheses,
  and a distance function `r : M → ℝ` is a genuine total function, restricted
  to an open set `U : Set M` by explicit `ContMDiffOn`/pointwise-on-`U`
  hypotheses rather than by working with a subtype.
* `hessianOperator D g f p v := D.cov p v (gradient g f)` realizes
  `S(X) = ∇_X∇f` directly from the Ch. 2 connection and gradient API; the
  companion `hessianOperatorSquared` realizes the `(0,2)`-tensor `Hess²f = S∘S`
  of the same definition block, converted to a bilinear form via the metric.
* `distanceFunctionNotation` packages Petersen's notation `(∂_r, O_r, g_r, S)`
  as a quadruple: the radial field `∂_r`, the level sets `O_t ⊂ U`, the
  induced metric `g_r` (the ambient inner product, restricted to level-set
  tangent vectors represented as ambient vectors in `ker dr`), and the shape
  operator `S`.
* `ConjugatePoint`: the source defines a conjugate point through failure of a
  Riccati-type ODE for `Hess r` along an integral curve of `∂_r` to admit a
  solution ("`Hess r` becomes undefined"). Absent ODE/geodesic-flow blow-up
  infrastructure at this point in the project, the closest faithful shape
  used here is a neighbourhood blow-up of the Hessian operator's associated
  quadratic form (using `g`, since `TangentSpace I p` carries no independent
  `Norm` instance) in a fixed raw direction `w : E`, reused across fibres via
  the definitional identification `TangentSpace I q = E`. The companion notion
  of a *focal point* (integral curves of `∇r` meeting) is not separately
  formalized, for lack of an integral-curve/geodesic-flow API at the Ch. 3
  stage; it is recorded only in the docstring.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.2.1, §3.2.2, §3.2.4,
§3.2.5, §3.2.6.
-/

open Bundle Set Function Filter
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## §3.2.1 — the Hessian operator -/

section HessianOperator

variable [FiniteDimensional ℝ E]

/-- **Math.** The **Hessian operator** `S(X) = ∇_X∇f` (Petersen §3.2.1,
`def:pet-ch3-hessian-square-notation`): for a connection `D` and a smooth
function `f` (possibly only on an open subset of `M`), the `(1,1)`-tensor
corresponding to `Hess f`. -/
def hessianOperator (D : AffineConnection I M) (g : RiemannianMetric I M) (f : M → ℝ)
    (p : M) (v : TangentSpace I p) : TangentSpace I p :=
  D.cov p v (gradient g f)

@[simp]
theorem hessianOperator_apply (D : AffineConnection I M) (g : RiemannianMetric I M)
    (f : M → ℝ) (p : M) (v : TangentSpace I p) :
    hessianOperator D g f p v = D.cov p v (gradient g f) := rfl

/-- **Math.** The **squared Hessian** `(0,2)`-tensor `Hess²f = S∘S` (Petersen
§3.2.1, `def:pet-ch3-hessian-square-notation`): the composition of the
Hessian operator with itself, converted to a bilinear form via the metric. -/
def hessianOperatorSquared (D : AffineConnection I M) (g : RiemannianMetric I M)
    (f : M → ℝ) (p : M) (v w : TangentSpace I p) : ℝ :=
  g.metricInner p (hessianOperator D g f p (hessianOperator D g f p v)) w

@[simp]
theorem hessianOperatorSquared_apply (D : AffineConnection I M)
    (g : RiemannianMetric I M) (f : M → ℝ) (p : M) (v w : TangentSpace I p) :
    hessianOperatorSquared D g f p v w
      = g.metricInner p (hessianOperator D g f p (hessianOperator D g f p v)) w := rfl

end HessianOperator

/-! ## §3.2.2 — distance functions -/

section DistanceFunction

variable [FiniteDimensional ℝ E]

/-- **Math.** `r` is a **distance function** on the open set `U` (Petersen
§3.2.2, `def:pet-ch3-distance-function`): `r` is smooth on `U` and solves the
**eikonal** (Hamilton–Jacobi) equation `|∇r|² = 1` there. -/
def IsDistanceFunction (g : RiemannianMetric I M) (U : Set M) (r : M → ℝ) : Prop :=
  ContMDiffOn I 𝓘(ℝ) ∞ r U ∧
    ∀ x ∈ U, g.metricInner x (gradient g r x) (gradient g r x) = 1

/-- **Math.** **Distance-function notation** (Petersen §3.2.2,
`def:pet-ch3-distance-function-notation`): for a distance function `r` on
`U`, the quadruple `(∂_r, O_r, g_r, S)` — the radial field `∂_r := ∇r`, the
level sets `O_t = {x ∈ U | r(x) = t}`, the induced metric `g_r` on each level
set, and the shape operator `S := ∇∂_r` — the common `(1,1)`-tensor Petersen
also uses for `Hess r`, since `|∂_r| ≡ 1`.

**Eng.** With no Riemannian-submanifold layer, tangent vectors of a level set
are represented as ambient vectors in `ker dr`, and the induced metric `g_r`
is the restriction of the ambient inner product to them — recorded as the
ambient `g.metricInner` itself. -/
def distanceFunctionNotation (D : AffineConnection I M) (g : RiemannianMetric I M)
    (U : Set M) (r : M → ℝ) (_hr : IsDistanceFunction g U r) :
    (Π x : M, TangentSpace I x) × (ℝ → Set M)
      × (∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
      × (∀ p : M, TangentSpace I p → TangentSpace I p) :=
  (gradient g r, fun t => {x ∈ U | r x = t}, fun p v w => g.metricInner p v w,
    hessianOperator D g r)

@[simp]
theorem distanceFunctionNotation_radial (D : AffineConnection I M)
    (g : RiemannianMetric I M) (U : Set M) (r : M → ℝ)
    (hr : IsDistanceFunction g U r) :
    (distanceFunctionNotation D g U r hr).1 = gradient g r := rfl

@[simp]
theorem distanceFunctionNotation_levelSet (D : AffineConnection I M)
    (g : RiemannianMetric I M) (U : Set M) (r : M → ℝ)
    (hr : IsDistanceFunction g U r) (t : ℝ) :
    (distanceFunctionNotation D g U r hr).2.1 t = {x ∈ U | r x = t} := rfl

@[simp]
theorem distanceFunctionNotation_inducedMetric (D : AffineConnection I M)
    (g : RiemannianMetric I M) (U : Set M) (r : M → ℝ)
    (hr : IsDistanceFunction g U r) (p : M) (v w : TangentSpace I p) :
    (distanceFunctionNotation D g U r hr).2.2.1 p v w = g.metricInner p v w := rfl

@[simp]
theorem distanceFunctionNotation_shapeOperator (D : AffineConnection I M)
    (g : RiemannianMetric I M) (U : Set M) (r : M → ℝ)
    (hr : IsDistanceFunction g U r) :
    (distanceFunctionNotation D g U r hr).2.2.2 = hessianOperator D g r := rfl

end DistanceFunction

/-! ## §3.2.4 — Jacobi fields -/

section JacobiField

variable [FiniteDimensional ℝ E]

/-- **Math.** `J` is a **Jacobi field** for the distance function `r`
(Petersen §3.2.4, `def:pet-ch3-jacobi-field`): a vector field independent of
`r`, i.e. solving the **Jacobi equation** `L_{∂_r}J = 0` at every point of
`U`. -/
def IsJacobiField (g : RiemannianMetric I M) (U : Set M) (r : M → ℝ)
    (J : Π x : M, TangentSpace I x) : Prop :=
  ∀ p ∈ U, lieDerivativeVectorField I (gradient g r) J p = 0

/-- **Math.** **Construction of Jacobi fields** (Petersen §3.2.4,
`rem:pet-ch3-jacobi-field-construction`): the Jacobi equation `L_{∂_r}J = 0` is
a first-order linear PDE solvable by characteristics; in coordinates
`(r, x², …, xⁿ)` adapted to `r` it says the components of `J` are independent of
`r`, so `J` is determined by its values on a hypersurface transverse to `∂_r`,
and *the coordinate vector fields are themselves Jacobi fields*. The cleanest
instance realizable with the chart-free API here: the radial field `∂_r = ∇r`
— itself the `r`-direction coordinate field of any adapted chart — is a Jacobi
field, since `L_{∂_r}∂_r = [∂_r, ∂_r] = 0` for any vector field. -/
theorem jacobiField_construction (g : RiemannianMetric I M) (U : Set M) (r : M → ℝ) :
    IsJacobiField g U r (gradient g r) := by
  intro p _
  rw [lieDerivativeVectorField_eq_mlieBracket]
  exact congrFun (VectorField.mlieBracket_self (I := I) (V := gradient g r)) p

/-- **Math.** **First-order form of the Jacobi equation** (Petersen §3.2.4,
`lem:pet-ch3-jacobi-field-equivalent-equation`): `L_{∂_r}J = 0` is equivalent
to `∇_{∂_r}J = S(J)`, via torsion-freeness (`[∂_r,J] = ∇_{∂_r}J - ∇_J∂_r` and
`∇_J∂_r = S(J)` by definition of the shape operator). -/
theorem jacobiField_equivalentEquation {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {r : M → ℝ} {J : Π x : M, TangentSpace I x}
    (hgradr : IsSmoothVectorField (gradient g r)) (hJ : IsSmoothVectorField J)
    (p : M) :
    lieDerivativeVectorField I (gradient g r) J p = 0 ↔
      D.cov p ((gradient g r) p) J
        = hessianOperator D.toAffineConnection g r p (J p) := by
  have htf : D.cov p ((gradient g r) p) J - D.cov p (J p) (gradient g r)
      = lieDerivativeVectorField I (gradient g r) J p :=
    D.torsion_free hgradr hJ p
  have hS : hessianOperator D.toAffineConnection g r p (J p)
      = D.cov p (J p) (gradient g r) := rfl
  rw [hS]
  constructor
  · intro h0
    have hsub : D.cov p ((gradient g r) p) J - D.cov p (J p) (gradient g r) = 0 := by
      rw [htf, h0]
    exact sub_eq_zero.mp hsub
  · intro heq
    rw [← htf, heq]
    exact sub_self _

end JacobiField

section JacobiFieldHessian

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]

/-- **Math.** Consequence of `jacobiField_equivalentEquation` (Petersen
§3.2.4, `lem:pet-ch3-jacobi-field-equivalent-equation`): for a Jacobi field
`J`, `Hess r(J,J) = g(∇_{∂_r}J,J) = ½ ∂_r g(J,J)`. -/
theorem jacobiField_hessian_metricInner {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {r : M → ℝ} {J : Π x : M, TangentSpace I x}
    (hr : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r)) (hJ : IsSmoothVectorField J)
    (p : M) (hJacobi : lieDerivativeVectorField I (gradient g r) J p = 0) :
    hessianLieDerivative g r ![J, J] p
        = g.metricInner p (D.cov p ((gradient g r) p) J) (J p) ∧
      g.metricInner p (D.cov p ((gradient g r) p) J) (J p)
        = (1 / 2 : ℝ) * directionalDerivative (gradient g r)
            (fun q => g.metricInner q (J q) (J q)) p := by
  have heq : D.cov p ((gradient g r) p) J = D.cov p (J p) (gradient g r) :=
    (jacobiField_equivalentEquation D hgradr hJ p).mp hJacobi
  refine ⟨?_, ?_⟩
  · have hbridge : hessianLieDerivative g r ![J, J] p
        = g.metricInner p (D.cov p (J p) (gradient g r)) (J p) :=
      (hessian_via_covariantDerivative D hr hJ hJ hgradr p).symm.trans
        (covariantDerivative_differential_eq_gradient D J J hJ hgradr p)
    rw [hbridge, heq]
  · have hcompat := D.metric_compat hJ hJ p ((gradient g r) p)
    rw [dirTangent_eq_directionalDerivative] at hcompat
    have hcomm : g.metricInner p (J p) (D.cov p ((gradient g r) p) J)
        = g.metricInner p (D.cov p ((gradient g r) p) J) (J p) := g.metricInner_comm ..
    rw [hcomm] at hcompat
    linarith [hcompat]

end JacobiFieldHessian

/-! ## §3.2.5 — parallel fields -/

section ParallelField

variable [FiniteDimensional ℝ E]

/-- **Math.** `X` is a **parallel field** for the distance function `r`
(Petersen §3.2.5, `def:pet-ch3-parallel-field`): `∇_{∂_r}X = 0` at every
point of `U`. Parallel fields are almost never Jacobi fields. -/
def IsParallelField (D : AffineConnection I M) (g : RiemannianMetric I M)
    (U : Set M) (r : M → ℝ) (X : Π x : M, TangentSpace I x) : Prop :=
  ∀ p ∈ U, D.cov p ((gradient g r) p) X = 0

end ParallelField

/-! ## §3.2.6 — conjugate points -/

section ConjugatePointSec

variable [FiniteDimensional ℝ E]

/-- **Math.** A **conjugate point** of the distance function `r` (Petersen
§3.2.6, `def:pet-ch3-conjugate-focal-point`): informally, the point `p` where
the shape operator `S = ∇∂_r` "becomes undefined" while solving its
Riccati-type differential equation along an integral curve of `∂_r`; equation
(2) of `prop:pet-ch3-distance-function-curvature-equations` forces `Hess r`
to be decreasing as `r` increases, so any blow-up can only be towards `-∞`.
(The companion notion of a **focal point** — integral curves of `∇r` meeting
— is not formalized here; the two frequently coincide but need not, see
`rem:pet-ch3-conjugate-vs-focal-example`.)

**Eng.** Absent ODE/geodesic-flow blow-up infrastructure at this point in the
project, the closest faithful shape is: for some fixed raw direction `w : E`
(reused across the fibres `TangentSpace I q = E` in place of a
parallel-transported frame), the quadratic form `q ↦ g(S_q w, w)` of the
Hessian operator at `q` tends to `-∞` as `q → p` within `M`, `q ≠ p`. -/
def ConjugatePoint (D : AffineConnection I M) (g : RiemannianMetric I M) (r : M → ℝ)
    (p : M) : Prop :=
  ∃ w : E, Filter.Tendsto
    (fun q => g.metricInner q (hessianOperator D g r q (w : TangentSpace I q))
      (w : TangentSpace I q))
    (nhdsWithin p {p}ᶜ) Filter.atBot

end ConjugatePointSec

/-! ## §3.2.2 — Example 3.2.6: the distance to a point -/

section DistanceToPoint

/-- **Math.** The Fréchet derivative of the norm on a real inner product space,
away from the origin: `D‖·‖|_u = ‖u‖⁻¹⟨u, ·⟩` for `u ≠ 0`. (A missing Mathlib
lemma; `Mathlib.Analysis.Calculus.FDeriv.Norm` only records `‖D‖·‖‖ = 1`.)
Proved by identifying `D(‖·‖²) = 2⟨u,·⟩` with `2‖u‖·D‖·‖` via the product
rule and cancelling `2‖u‖`. -/
theorem hasFDerivAt_norm_ne_zero {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {u : F} (hu : u ≠ 0) :
    HasFDerivAt (fun z : F => ‖z‖) (‖u‖⁻¹ • innerSL ℝ u) u := by
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hd : DifferentiableAt ℝ (fun z : F => ‖z‖) u :=
    (contDiffAt_norm ℝ (n := 1) hu).differentiableAt (by norm_num)
  have hN : HasFDerivAt (fun z : F => ‖z‖) (fderiv ℝ (fun z : F => ‖z‖) u) u := hd.hasFDerivAt
  have hprod : HasFDerivAt (fun z : F => ‖z‖ * ‖z‖)
      (‖u‖ • fderiv ℝ (fun z : F => ‖z‖) u + ‖u‖ • fderiv ℝ (fun z : F => ‖z‖) u) u :=
    hN.mul hN
  have hpow : (fun z : F => ‖z‖ * ‖z‖) = (fun z : F => ‖z‖ ^ 2) := by funext z; rw [sq]
  rw [hpow] at hprod
  have hsq : HasFDerivAt (fun z : F => ‖z‖ ^ 2) (2 • innerSL ℝ u) u :=
    (hasStrictFDerivAt_norm_sq u).hasFDerivAt
  have huniq := hsq.unique hprod
  have hfe : fderiv ℝ (fun z : F => ‖z‖) u = ‖u‖⁻¹ • innerSL ℝ u := by
    have hc : (2 * ‖u‖ : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hnu
    apply smul_right_injective (F →L[ℝ] ℝ) hc
    show (2 * ‖u‖ : ℝ) • fderiv ℝ (fun z : F => ‖z‖) u = (2 * ‖u‖ : ℝ) • (‖u‖⁻¹ • innerSL ℝ u)
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hnu, mul_one, mul_smul, two_smul, two_smul]
    rw [two_smul] at huniq
    exact huniq.symm
  rw [hfe] at hN
  exact hN

/-- **Math.** **Example 3.2.6** (Petersen §3.2.2, `ex:pet-ch3-distance-to-points`).
On `(ℝⁿ, g_can)`, the distance to a point `r(x) = |x − y|` is a distance
function on `ℝⁿ ∖ {y}`: it is smooth there and solves the eikonal equation
`|∇r| ≡ 1`. Indeed `∇r = (x − y)/|x − y|` is a unit vector. -/
theorem distanceFunction_points (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    IsDistanceFunction (euclideanMetric n) {y}ᶜ (fun x => ‖x - y‖) := by
  refine ⟨?_, ?_⟩
  · -- `r` is smooth on `ℝⁿ ∖ {y}` (norm is smooth away from `0`)
    have hcd : ContDiffOn ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => ‖z - y‖) {y}ᶜ := by
      intro x hx
      exact ((contDiffAt_norm ℝ (sub_ne_zero.mpr hx)).comp x
        (contDiffAt_id.sub contDiffAt_const)).contDiffWithinAt
    exact hcd.contMDiffOn
  · -- eikonal: `∇r = (x − y)/|x − y|` has `|∇r|² = 1`
    intro x hx
    have hu : x - y ≠ 0 := sub_ne_zero.mpr hx
    have hnu : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have hFD : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => ‖z - y‖)
        (‖x - y‖⁻¹ • innerSL ℝ (x - y)) x := by
      have := (hasFDerivAt_norm_ne_zero hu).comp x ((hasFDerivAt_id x).sub_const y)
      simpa using this
    have hgrad : gradient (euclideanMetric n) (fun z => ‖z - y‖) x
        = ‖x - y‖⁻¹ • (x - y) := by
      refine (gradient_unique (euclideanMetric n) (fun z => ‖z - y‖) x _ (fun w => ?_)).symm
      rw [euclideanMetric_apply, real_inner_smul_left, mfderiv_eq_fderiv, hFD.fderiv]
      rfl
    rw [hgrad, euclideanMetric_apply, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp

end DistanceToPoint

end PetersenLib
