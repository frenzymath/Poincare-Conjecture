import Topping.Riemannian.CurvatureLaplacianProducer
import Topping.Riemannian.SmoothTensor
import Topping.RicciFlow.CurvatureStarUniform

/-!
# Topping 2.5.1, derived rather than assumed

The curvature evolution equation is not an independent statement: Topping obtains
it by substituting `h = -2\Ric` into the first variation of the Riemann tensor
(2.3.5) and recognising the resulting second-derivative terms through the formula
for `Δ\Rm` (2.4.1). This module carries out that substitution.

The computation is exact, and worth seeing before the Lean. Prop. 2.3.5 says

`∂_t\Rm(X,Y,W,Z) = ½[h(R(X,Y)W,Z) - h(R(X,Y)Z,W)]
  + ½[∇²_{Y,W}h(X,Z) - ∇²_{X,W}h(Y,Z) + ∇²_{X,Z}h(Y,W) - ∇²_{Y,Z}h(X,W)]`.

At `h = -2\Ric` the two halves behave differently:

* the first bracket becomes `-\Ric(R(X,Y)W,Z) + \Ric(R(X,Y)Z,W)`, which is
  already the first line of 2.5.1's correction;
* the second becomes `-∇²_{Y,W}\Ric(X,Z) + ∇²_{X,W}\Ric(Y,Z) - ∇²_{X,Z}\Ric(Y,W)
  + ∇²_{Y,Z}\Ric(X,W)` — *character for character the four `∇²\Ric` terms of
  2.4.1*. So 2.4.1, read backwards, replaces them by `Δ\Rm` plus the two
  remaining `\Ric`-of-curvature terms and the four `B` terms, with the sign of
  each `B` term flipped.

Nothing is left over: the four second-covariant-derivative terms cancel
identically, and the surviving terms are exactly Topping's eight. This is the
reason the curvature evolution has a heat-type form at all — the only terms in
`∂_t\Rm` that carry derivatives of the curvature are the ones `Δ\Rm` accounts
for.

Two technical points are real mathematical content rather than bookkeeping:

* pulling the `-2` out of `∇²h` needs `∇²(c\Ric) = c∇²\Ric`, which needs the
  Ricci tensor field to have *smooth* components, not merely differentiable ones,
  because `∇²` differentiates `∇\Ric`. That is
  `secondCovDerivAlong_const_mul` with `hasSmoothComponents_ricciTensorField`.
* Ricci flow is not assumed. As on the scalar side, the flow enters only by
  choosing the direction `h = -2\Ric`; `isMetricVariationOn_of_isRicciFlowOn`
  is what lines the two up for a family that does solve the flow.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Bookkeeping: tuples and the pointwise curvature operator -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A `4`-tuple of vector fields, rebuilt from its four entries by
nested conditionals, is itself. This is what lets a formula stated on four named
fields be read on an arbitrary tuple. -/
theorem tuple_four_eta (Y : Fin 4 → SmoothVectorField I M) :
    (fun i => if i = 0 then Y 0 else if i = 1 then Y 1 else
      if i = 2 then Y 2 else Y 3) = Y := by
  funext i
  fin_cases i <;> rfl

/-! ### The second-derivative terms at `h = -2\Ric`

The bridge from the field-level `curvatureOperator` to the pointwise
`curvatureOperatorAt` is `curvatureOperator_apply_eq_curvatureOperatorAt`, proved
for the Ricci evolution and reused here. -/

/-- **Math.** The four second-covariant-derivative terms of 2.3.5, evaluated at
`h = -2\Ric`, are `-2` times those of 2.4.1. This is the identity that makes the
two formulas cancel, and the only place regularity is used: the constant leaves
`∇²` by `secondCovDerivAlong_const_mul`, whose hypothesis is smoothness of the
components of `\Ric`. -/
theorem secondCovDerivAlong_covTensorOfBilin_neg_two_ricci
    (g : RiemannianMetric I M) (X W : SmoothVectorField I M)
    (Z : Fin 2 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection X W
        (covTensorOfBilin
          (fun q (x y : TangentSpace I q) => -2 * ricciTensorAt g q x y)) Z p
      = -2 * secondCovDerivAlong g.leviCivitaConnection X W
          (ricciTensorField g) Z p := by
  rw [covTensorOfBilin_neg_two_ricci,
    secondCovDerivAlong_const_mul g.leviCivitaConnection X W (-2)
      (hasSmoothComponents_ricciTensorField g)]

/-! ### The derivation -/

/-- **Math.** **Topping 2.5.1, derived.** If the Riemann tensor of the family `g`
varies by Topping's first-variation formula 2.3.5 in the direction
`h = -2\Ric`, then the curvature satisfies the component form of the evolution
equation on `J`. The rough-Laplacian formula 2.4.1 is supplied unconditionally
by `hasCurvatureLaplacianFormula`.

The proof is the substitution described in the module docstring: the four
`∇²\Ric` terms produced by the variation formula are exactly those appearing in
2.4.1, so replacing them by `Δ\Rm` and the remaining terms of 2.4.1 leaves
precisely Topping's eight-term correction, with nothing unaccounted for.

The variation hypothesis is the only *time*-analytic input — nothing further is
assumed about the family `g`, and no derivative is computed here. One spatial
regularity fact is used and is not a hypothesis because it is a theorem:
smoothness of the components of `\Ric` (`hasSmoothComponents_ricciTensorField`),
without which the `-2` could not leave `∇²`.

**Status of the antecedent.** `HasCurvatureLaplacianFormula` (2.4.1) is now
genuinely witnessed for every metric. The remaining input is
`HasRiemannVariationOn` (Topping 2.3.5) in the `-2\Ric` direction, which has no
arbitrary-field intrinsic producer in the workspace. -/
theorem hasCurvatureEvolutionComponentsOn_of_variation
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hvar : HasRiemannVariationOn g
      (fun t p (x y : TangentSpace I p) => -2 * ricciTensorAt (g t) p x y) J) :
    HasCurvatureEvolutionComponentsOn g J := by
  intro t ht Y p
  -- The variation formula, on the four entries of the tuple.
  have hv := hvar t ht (Y 0) (Y 1) (Y 2) (Y 3) p
  -- `Δ\Rm` by 2.4.1, on the same four entries.
  have hL := hasCurvatureLaplacianFormula (g t) (Y 0) (Y 1) (Y 2) (Y 3) p
  rw [tuple_four_eta] at hL
  -- Pull the `-2` out of each of the four second-derivative terms.
  simp only [secondCovDerivAlong_covTensorOfBilin_neg_two_ricci] at hv
  -- Both formulas' curvature terms, on the pointwise operator.
  simp only [curvatureOperator_apply_eq_curvatureOperatorAt] at hv hL
  -- `\Rm` as a tensor field on the tuple `Y` *is* the pointwise Riemann tensor of
  -- its entries, definitionally, so the variation formula is already about the
  -- function whose derivative is wanted.
  show HasDerivWithinAt (fun s => riemannCurvatureAt (g s) p
      (Y 0 p) (Y 1 p) (Y 2 p) (Y 3 p)) _ J t
  -- Substitute 2.4.1 into the variation formula and compare with the correction.
  refine hv.congr_deriv ?_
  rw [curvatureEvolutionCorrection, hL]
  ring

/-- **Math.** **Topping 2.5.1 in compact form, derived.** Under the same
variation hypothesis the curvature satisfies `∂_t\Rm = Δ\Rm + \Rm*\Rm`: the
component form established above feeds `hasCurvatureEvolutionOn_of_components`,
whose star witness is `curvatureEvolutionCorrection`.

This closes the chain the chapter is built around — first variation, Laplacian
formula, evolution equation — with the star product's existential discharged by a
named tensor rather than left open. -/
theorem hasCurvatureEvolutionOn_of_variation
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hvar : HasRiemannVariationOn g
      (fun t p (x y : TangentSpace I p) => -2 * ricciTensorAt (g t) p x y) J) :
    HasCurvatureEvolutionOn g J :=
  hasCurvatureEvolutionOn_of_components
    (hasCurvatureEvolutionComponentsOn_of_variation hvar)

#print axioms Topping.hasCurvatureEvolutionComponentsOn_of_variation
#print axioms Topping.hasCurvatureEvolutionOn_of_variation

end Topping

end
