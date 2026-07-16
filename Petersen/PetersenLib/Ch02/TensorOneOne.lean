import PetersenLib.Ch02.CovariantDerivative
import PetersenLib.Ch02.MetricOperator

/-!
# Petersen Ch. 2, §2.5 — `(1,1)`-tensor fields and their derivatives

A `(1,1)`-tensor field (endomorphism field) is a fibrewise endomorphism
`S : Π x, T_xM →L[ℝ] T_xM` of the tangent bundle. This file builds the
`(1,1)`-tensor layer needed for Exercises 2.5.9 and 2.5.10:

* `applyEndField` — the action `S(Y)(x) = S_x(Y_x)` of an endomorphism field on a
  vector field, and `IsSmoothEndField` (smoothness);
* `endFieldLower` — the associated `(0,2)`-tensor `T(Y,Z) = g(S(Y), Z)`;
* `covariantDerivativeEndField` — `(∇_X S)(Y) = ∇_X(S(Y)) − S(∇_X Y)`;
* `lieDerivativeEndField` — `(L_X S)(Y) = [X, S(Y)] − S([X, Y])`.

The two Leibniz interplays are the analytic heart of the exercises:

* `covariantDerivativeTensor_endFieldLower` (**Ex 2.5.9(2)**):
  `(∇_X T)(Y,Z) = g((∇_X S)(Y), Z)`, from metric compatibility `∇g = 0`;
* `lieDerivativeTensor_endFieldLower` (**Ex 2.5.10(2)**):
  `(L_X T)(Y,Z) = (L_X g)(S(Y), Z) + g((L_X S)(Y), Z)`, purely algebraic.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercises 9–10.
-/

set_option linter.unusedSectionVars false

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Endomorphism fields (`(1,1)`-tensor fields) -/

variable (I) in
/-- **Eng.** A `(1,1)`-tensor field on `M`: a fibrewise (continuous-linear)
endomorphism `S_x : T_xM → T_xM` of every tangent space. Petersen manipulates
such a tensor through its action `S(X)` on vector fields and its trace. -/
abbrev EndField (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :=
  Π x : M, (TangentSpace I x →L[ℝ] TangentSpace I x)

/-- **Math.** The action of an endomorphism field `S` on a vector field `Y`:
`S(Y)(x) = S_x(Y_x)`, again a vector field. -/
def applyEndField (S : EndField I M) (Y : Π x : M, TangentSpace I x) :
    Π x : M, TangentSpace I x :=
  fun x => S x (Y x)

@[simp]
theorem applyEndField_apply (S : EndField I M) (Y : Π x : M, TangentSpace I x) (x : M) :
    applyEndField S Y x = S x (Y x) := rfl

/-- **Math.** `S` is a **smooth** `(1,1)`-tensor field: its action on smooth
vector fields is smooth. -/
def IsSmoothEndField (S : EndField I M) : Prop :=
  ∀ Y : Π x : M, TangentSpace I x, IsSmoothVectorField Y →
    IsSmoothVectorField (applyEndField S Y)

/-! ## The associated `(0,2)`-tensor `T(Y,Z) = g(S(Y), Z)` -/

/-- **Math.** The `(0,2)`-tensor associated to a `(1,1)`-tensor `S` by the metric:
`T(Y, Z) = g(S(Y), Z)` (Petersen §2.5, Ex. 9/10). -/
def endFieldLower (g : RiemannianMetric I M) (S : EndField I M) : TensorOperator I M 2 :=
  fun Y x => g.metricInner x (S x (Y 0 x)) (Y 1 x)

@[simp]
theorem endFieldLower_apply (g : RiemannianMetric I M) (S : EndField I M)
    (Y : Fin 2 → Π x : M, TangentSpace I x) (x : M) :
    endFieldLower g S Y x = g.metricInner x (S x (Y 0 x)) (Y 1 x) := rfl

/-! ## The covariant and Lie derivatives of a `(1,1)`-tensor -/

/-- **Math.** The **covariant derivative of a `(1,1)`-tensor** `S` in the direction
of a vector field `X` (Petersen §2.5, Ex. 9): the endomorphism-valued operator
`(∇_X S)(Y) = ∇_X(S(Y)) − S(∇_X Y)`. -/
def covariantDerivativeEndField (D : AffineConnection I M)
    (X : Π x : M, TangentSpace I x) (S : EndField I M)
    (Y : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun x => D.covField X (applyEndField S Y) x - applyEndField S (D.covField X Y) x

@[simp]
theorem covariantDerivativeEndField_apply (D : AffineConnection I M)
    (X : Π x : M, TangentSpace I x) (S : EndField I M)
    (Y : Π x : M, TangentSpace I x) (x : M) :
    covariantDerivativeEndField D X S Y x
      = D.cov x (X x) (applyEndField S Y) - S x (D.cov x (X x) Y) := rfl

/-- **Math.** The **Lie derivative of a `(1,1)`-tensor** `S` in the direction of a
vector field `X` (Petersen §2.5, Ex. 10): the endomorphism-valued operator
`(L_X S)(Y) = [X, S(Y)] − S([X, Y])`. -/
def lieDerivativeEndField (X : Π x : M, TangentSpace I x) (S : EndField I M)
    (Y : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun x => lieDerivativeVectorField I X (applyEndField S Y) x
    - S x (lieDerivativeVectorField I X Y x)

@[simp]
theorem lieDerivativeEndField_apply (X : Π x : M, TangentSpace I x) (S : EndField I M)
    (Y : Π x : M, TangentSpace I x) (x : M) :
    lieDerivativeEndField X S Y x
      = lieDerivativeVectorField I X (applyEndField S Y) x
        - S x (lieDerivativeVectorField I X Y x) := rfl

/-! ## Exercise 2.5.9(2): `(∇_X T)(Y,Z) = g((∇_X S)(Y), Z)` -/

/-- **Math.** **Exercise 2.5.9(2).** For a `(1,1)`-tensor `S` and its associated
`(0,2)`-tensor `T(Y,Z) = g(S(Y), Z)`, the covariant derivatives are related by
`(∇_X T)(Y, Z) = g((∇_X S)(Y), Z)`. This is the metric-compatibility (`∇g = 0`)
identity: differentiating `g(S(Y), Z)` splits into `g(∇_X(S(Y)), Z)` plus
`g(S(Y), ∇_X Z)`, and the latter cancels the `Z`-slot correction term. -/
theorem covariantDerivativeTensor_endFieldLower {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (S : EndField I M) (hS : IsSmoothEndField S)
    {X Y Z : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    (x : M) :
    covariantDerivativeTensor D.toAffineConnection X (endFieldLower g S) ![Y, Z] x
      = g.metricInner x (covariantDerivativeEndField D.toAffineConnection X S Y x) (Z x) := by
  have hSY : IsSmoothVectorField (applyEndField S Y) := hS Y hY
  -- expand the (0,2) covariant derivative
  rw [covariantDerivativeTensor_formula, Fin.sum_univ_two]
  -- the directional-derivative term via metric compatibility
  have hmc : directionalDerivative X (endFieldLower g S ![Y, Z]) x
      = g.metricInner x (D.cov x (X x) (applyEndField S Y)) (Z x)
        + g.metricInner x (applyEndField S Y x) (D.cov x (X x) Z) := by
    rw [← dirTangent_eq_directionalDerivative]
    exact D.metric_compat hSY hZ x (X x)
  rw [hmc]
  -- simplify the two update-slot correction terms
  simp only [endFieldLower_apply, covariantDerivativeEndField_apply, applyEndField_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, Function.update_of_ne,
    zero_ne_one, AffineConnection.covField_apply]
  rw [g.metricInner_sub_left]
  ring

/-! ## Exercise 2.5.10(2): `(L_X T)(Y,Z) = (L_X g)(S(Y),Z) + g((L_X S)(Y), Z)` -/

/-- **Math.** **Exercise 2.5.10(2).** For a `(1,1)`-tensor `S` and its associated
`(0,2)`-tensor `T(Y,Z) = g(S(Y), Z)`, the Lie derivatives are related by
`(L_X T)(Y, Z) = (L_X g)(S(Y), Z) + g((L_X S)(Y), Z)`. Purely algebraic: both
sides expand to `D_X(g(S(Y),Z)) − g(S([X,Y]),Z) − g(S(Y),[X,Z])` after cancelling
the `[X, S(Y)]` terms. -/
theorem lieDerivativeTensor_endFieldLower {g : RiemannianMetric I M}
    (S : EndField I M) (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    lieDerivativeTensor I X (endFieldLower g S) ![Y, Z] x
      = lieDerivativeTensor I X (metricOperator g) ![applyEndField S Y, Z] x
        + g.metricInner x (lieDerivativeEndField X S Y x) (Z x) := by
  rw [lieDerivativeTensor_formula, lieDerivativeTensor_formula, Fin.sum_univ_two,
    Fin.sum_univ_two]
  -- the two undifferentiated `D_X(g(S(Y),Z))` terms agree definitionally
  have hdd : directionalDerivative X (endFieldLower g S ![Y, Z]) x
      = directionalDerivative X (metricOperator g ![applyEndField S Y, Z]) x := rfl
  rw [hdd]
  simp only [endFieldLower_apply, metricOperator_apply, lieDerivativeEndField_apply,
    applyEndField_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Function.update_self, ne_eq, one_ne_zero, not_false_eq_true, Function.update_of_ne,
    zero_ne_one]
  rw [g.metricInner_sub_left]
  ring

/-! ## The exercises -/

/-- **Math.** **Exercise 2.5.9.** For a `(1,1)`-tensor `S` with associated
`(0,2)`-tensor `T(Y,Z) = g(S(Y), Z)`, part (2): the covariant derivatives obey
`(∇_X T)(Y, Z) = g((∇_X S)(Y), Z)`.

Parts (1), (3), (4) — `tr(∇_X S) = ∇_X(tr S)`, that contraction commutes with
covariant differentiation in general, and that type change commutes with it —
require the fibrewise trace and `(s,t)`-type-change layers on the manifold, which
are not yet built; part (2) is the metric-compatibility interplay that identifies
the `(0,2)`- and `(1,1)`-covariant derivatives and is the analytic heart of the
exercise. -/
theorem exercise2_5_9 {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (S : EndField I M) (hS : IsSmoothEndField S)
    {X Y Z : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z) (x : M) :
    covariantDerivativeTensor D.toAffineConnection X (endFieldLower g S) ![Y, Z] x
      = g.metricInner x (covariantDerivativeEndField D.toAffineConnection X S Y x) (Z x) :=
  covariantDerivativeTensor_endFieldLower D S hS hY hZ x

/-- **Math.** **Exercise 2.5.10.** For a `(1,1)`-tensor `S` with associated
`(0,2)`-tensor `T(Y,Z) = g(S(Y), Z)`, part (2): the Lie derivatives obey
`(L_X T)(Y, Z) = (L_X g)(S(Y), Z) + g((L_X S)(Y), Z)`.

Part (1), `tr(L_X S) = L_X(tr S)`, is `traceEndField_lieDerivative_commute`
(`Ch02/TensorOneOneTrace.lean`), reducing to the covariant trace by
torsion-freeness. Part (3) — that contraction commutes with Lie differentiation in
general — requires the `(s,t)`-type-change layer, not yet built; part (2) here is
the purely algebraic Leibniz interplay and is the analytic heart of the
exercise. -/
theorem exercise2_5_10 {g : RiemannianMetric I M} (S : EndField I M)
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    lieDerivativeTensor I X (endFieldLower g S) ![Y, Z] x
      = lieDerivativeTensor I X (metricOperator g) ![applyEndField S Y, Z] x
        + g.metricInner x (lieDerivativeEndField X S Y x) (Z x) :=
  lieDerivativeTensor_endFieldLower S X Y Z x

end PetersenLib

end
