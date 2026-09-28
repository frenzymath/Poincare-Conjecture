import PetersenLib.Ch03.RicciEquations

/-!
# Petersen Ch. 3, §3.4 Exercise 3.4.11 — the full submanifold curvature equation

For a submanifold `M ⊂ M̄` with tangential/normal splitting `T M̄|_M = TM ⊕ NM`,
the (vector-valued) **second fundamental form** `T` and the **normal
connection** `∇^⊥`, Petersen's Exercise 3.4.11 combines the tangential (Gauss)
and normal (Codazzi) curvature equations into the single vector identity: for
`X, Y, Z` tangent to `M`,
```
R̄(X,Y)Z = R^M(X,Y)Z + (T_X T_Y Z − T_Y T_X Z) + ((∇^⊥_X T)_Y Z − (∇^⊥_Y T)_X Z),
```
where `(∇^⊥_X T)_Y Z = ∇^⊥_X(T_Y Z) − T_{∇^M_X Y}Z − T_Y ∇^M_X Z`.  Projecting to
`TM` recovers the Gauss equations; projecting to `NM` recovers the
Peterson–Codazzi–Mainardi equations.

## The abstract normal-bundle encoding (as in `RicciEquations.lean`)

Following `RicciEquations.lean`, the tangential/normal splitting is encoded by
the smooth field of orthogonal projections `P : x ↦ (T_xM̄ →L NM_x)` onto the
normal bundle.  From `P`:

* `shapeTangent D P p v W = ∇_v W − P(∇_v W) = (∇_v W)^⊤` — for a **tangent** field
  `W = Z` this is the induced connection `∇^M`; for a **normal** field `W`
  (`= T_Y Z`) it is Petersen's `T` on normal inputs (the tangential/Weingarten
  part);
* `normalCov D P p v W = P(∇_v W) = (∇_v W)^⊥` — for a **tangent** field `W = Z`
  this is Petersen's second fundamental form `T_v Z` (the normal part), and for a
  **normal** field it is the normal connection `∇^⊥`.

So a single pair of operators `(shapeTangent, normalCov)` realizes Petersen's
full `T` on both tangent and normal inputs.  The point of the proof is that the
splitting `∇_v W = shapeTangent + normalCov` is **definitional**, so expanding
each second covariant derivative `∇_X(∇_Y Z)` produces exactly the four
`(⊤/⊥)×(⊤/⊥)` blocks that assemble into `R^M`, the shape terms and the `∇^⊥ T`
terms.  The only non-formal inputs are additivity of `∇` over a field split
(`add_field`, needing smoothness of the two projected fields, from
`RicciEquations.lean`), direction-linearity of `∇` (`cov_sub_direction`), and
**torsion-freeness** together with **integrability** of the tangent distribution
`P([X,Y]) = 0` — the latter automatic on a genuine submanifold, where `[X,Y]` is
tangent whenever `X, Y` are.

The theorem is stated and proved as a pure operator identity valid for *any*
smooth fields `X, Y, Z` once `P([X,Y]_p) = 0`; on a genuine submanifold `X,Y,Z`
are tangent and `R^M`, `T`, `∇^⊥` are the honest submanifold objects, recovering
Petersen's statement.  No idempotence or self-adjointness of `P` is needed for
the vector identity.

Reference: Petersen, *Riemannian Geometry* (GTM 171, 3rd ed.), Exercise 3.4.11,
page 122.
-/

open Bundle Set Function Filter
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]

/-! ## The induced tangential curvature and the normal derivative of `T` -/

/-- **Math.** The curvature `R^M(X,Y)Z` of the **induced tangential connection**
`∇^M = shapeTangent` (the tangential part of the ambient `∇`):
`R^M(X,Y)Z = ∇^M_X∇^M_YZ − ∇^M_Y∇^M_XZ − ∇^M_{[X,Y]}Z`. -/
def inducedTangentialCurvature (D : AffineConnection I M)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (X Y Z : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun p => shapeTangent D P p (X p) (shapeTangentField D P Y Z)
    - shapeTangent D P p (Y p) (shapeTangentField D P X Z)
    - shapeTangent D P p (lieDerivativeVectorField I X Y p) Z

/-- **Math.** The **normal covariant derivative of the second fundamental form**
`(∇^⊥_X T)_Y Z = ∇^⊥_X(T_Y Z) − T_{∇^M_X Y}Z − T_Y ∇^M_X Z`, with the second
fundamental form `T_·· = normalCov` (the normal part of `∇`), the normal
connection `∇^⊥ = normalCov` and the induced connection `∇^M = shapeTangent`. -/
def secondFundamentalNormalDerivative (D : AffineConnection I M)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
    (X Y Z : Π x : M, TangentSpace I x) (p : M) : TangentSpace I p :=
  normalCov D P p (X p) (normalCovField D P Y Z)
    - normalCov D P p (shapeTangentField D P X Y p) Z
    - normalCov D P p (Y p) (shapeTangentField D P X Z)

/-! ## Exercise 3.4.11 — the full curvature equation -/

/-- **Math.** **Exercise 3.4.11** (Petersen, `rem:pet-ch3-ex-11`): the full
submanifold curvature equation
```
R̄(X,Y)Z = R^M(X,Y)Z + (T_X T_Y Z − T_Y T_X Z) + ((∇^⊥_X T)_Y Z − (∇^⊥_Y T)_X Z),
```
where `T` is the second fundamental form, `∇^M` the induced tangential
connection, `∇^⊥` the normal connection — all encoded through the orthogonal
projection `P` onto the normal bundle (`shapeTangent`, `normalCov`).  The
tangential part of the identity is the Gauss equation, the normal part the
Peterson–Codazzi–Mainardi equation.

The identity holds as a pure operator identity given only the **integrability**
`P([X,Y]_p) = 0` of the tangent distribution at `p` (automatic on a genuine
submanifold, where `[X,Y]` is tangent for tangent `X, Y`); it needs neither
idempotence nor self-adjointness of `P`, only smoothness of the projected fields
(`hPsmooth`) and torsion-freeness of the ambient Riemannian connection. -/
theorem exercise3_4_11 {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hPsmooth : ∀ S : Π x : M, TangentSpace I x, IsSmoothVectorField S →
      IsSmoothVectorField (fun q => P q (S q)))
    {X Y Z : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    {p : M} (hInt : P p (lieDerivativeVectorField I X Y p) = 0) :
    curvatureTensor D.toAffineConnection X Y Z p
      = inducedTangentialCurvature D.toAffineConnection P X Y Z p
        + (shapeTangent D.toAffineConnection P p (X p)
              (normalCovField D.toAffineConnection P Y Z)
            - shapeTangent D.toAffineConnection P p (Y p)
              (normalCovField D.toAffineConnection P X Z))
        + (secondFundamentalNormalDerivative D.toAffineConnection P X Y Z p
            - secondFundamentalNormalDerivative D.toAffineConnection P Y X Z p) := by
  set D' := D.toAffineConnection with hD'
  -- pointwise definitional split `∇_v W = (∇_v W)^⊤ + (∇_v W)^⊥`
  have cov_split : ∀ (v : TangentSpace I p) (W : Π x : M, TangentSpace I x),
      D'.cov p v W = shapeTangent D' P p v W + normalCov D' P p v W := by
    intro v W; simp only [shapeTangent, normalCov]; abel
  -- smoothness of the four projected fields
  have hshpYZ : IsSmoothVectorField (shapeTangentField D' P Y Z) :=
    isSmoothVectorField_shapeTangentField D' hPsmooth hY hZ
  have hnorYZ : IsSmoothVectorField (normalCovField D' P Y Z) :=
    isSmoothVectorField_normalCovField D' hPsmooth hY hZ
  have hshpXZ : IsSmoothVectorField (shapeTangentField D' P X Z) :=
    isSmoothVectorField_shapeTangentField D' hPsmooth hX hZ
  have hnorXZ : IsSmoothVectorField (normalCovField D' P X Z) :=
    isSmoothVectorField_normalCovField D' hPsmooth hX hZ
  -- `∇_A B` splits into its tangential and normal fields
  have hsplitField : ∀ A B : Π x : M, TangentSpace I x,
      D'.covField A B
        = fun q => shapeTangentField D' P A B q + normalCovField D' P A B q := by
    intro A B; funext q
    simp only [shapeTangentField, shapeTangent, normalCovField, normalCov,
      AffineConnection.covField_apply]; abel
  -- expand `∇_X(∇_Y Z)` into the four `(⊤/⊥)×(⊤/⊥)` blocks
  have hA : D'.cov p (X p) (D'.covField Y Z)
      = shapeTangent D' P p (X p) (shapeTangentField D' P Y Z)
        + normalCov D' P p (X p) (shapeTangentField D' P Y Z)
        + shapeTangent D' P p (X p) (normalCovField D' P Y Z)
        + normalCov D' P p (X p) (normalCovField D' P Y Z) := by
    rw [hsplitField Y Z, D'.add_field p (X p) hshpYZ hnorYZ,
      cov_split (X p) (shapeTangentField D' P Y Z),
      cov_split (X p) (normalCovField D' P Y Z)]
    abel
  have hB : D'.cov p (Y p) (D'.covField X Z)
      = shapeTangent D' P p (Y p) (shapeTangentField D' P X Z)
        + normalCov D' P p (Y p) (shapeTangentField D' P X Z)
        + shapeTangent D' P p (Y p) (normalCovField D' P X Z)
        + normalCov D' P p (Y p) (normalCovField D' P X Z) := by
    rw [hsplitField X Z, D'.add_field p (Y p) hshpXZ hnorXZ,
      cov_split (Y p) (shapeTangentField D' P X Z),
      cov_split (Y p) (normalCovField D' P X Z)]
    abel
  -- the torsion/integrability identity for the bracket normal-correction:
  -- `T_{∇^M_X Y}Z − T_{∇^M_Y X}Z = T_{[X,Y]}Z`
  have htor : normalCov D' P p (shapeTangentField D' P X Y p) Z
        - normalCov D' P p (shapeTangentField D' P Y X p) Z
      = normalCov D' P p (lieDerivativeVectorField I X Y p) Z := by
    have hdir : shapeTangentField D' P X Y p - shapeTangentField D' P Y X p
        = lieDerivativeVectorField I X Y p := by
      have htf : D'.cov p (X p) Y - D'.cov p (Y p) X
          = lieDerivativeVectorField I X Y p := by
        rw [hD']; exact D.torsion_free hX hY p
      simp only [shapeTangentField, shapeTangent]
      have hcombine : (D'.cov p (X p) Y - P p (D'.cov p (X p) Y))
            - (D'.cov p (Y p) X - P p (D'.cov p (Y p) X))
          = (D'.cov p (X p) Y - D'.cov p (Y p) X)
            - P p (D'.cov p (X p) Y - D'.cov p (Y p) X) := by
        rw [map_sub]; abel
      rw [hcombine, htf, hInt, sub_zero]
    simp only [normalCov]
    rw [← map_sub, ← D'.cov_sub_direction, hdir]
  -- assemble everything into the operator identity
  rw [curvatureTensor_apply, hA, hB,
    cov_split (lieDerivativeVectorField I X Y p) Z]
  simp only [inducedTangentialCurvature, secondFundamentalNormalDerivative]
  linear_combination (norm := module) htor

end PetersenLib
