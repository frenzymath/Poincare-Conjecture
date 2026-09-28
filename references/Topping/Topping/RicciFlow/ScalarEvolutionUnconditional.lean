import MorganTianLib.Ch03.RicciFlow.ScalarCurvatureSmooth
import Topping.Riemannian.VariationScalar

/-!
# The scalar-evolution bridge, with its smoothness hypothesis discharged

`hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn` derives Topping's
`∂_tR = ΔR + 2|\Ric|^2` from his first-variation formula 2.3.9 under the
substitution `h = -2\Ric`. It carried one side condition beyond the variation
formula itself: smoothness of the scalar curvature at each fixed time, needed to
pull the constant `-2` through the Laplacian.

That condition is now a theorem, not a hypothesis. MT.CH03's
`MorganTianLib.scalarCurvatureAt_leviCivita_contMDiff` (inbox I-0483) proves the
spatial smoothness of the scalar curvature for the canonical Levi-Civita
connection, and Topping's scalar curvature is that one across
`scalarCurvatureAt_eq_scalarCurvatureAt`. So the bridge below needs *only* the
variation formula.

This is the ownership split of I-0442/I-0450 working as intended: MT supplies the
analysis, TOP ch2 supplies the algebra of the substitution, and neither restates
the other's half.
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

/-- **Math.** Topping's scalar curvature is smooth in the base point. This is
MT.CH03's spatial-smoothness theorem transported across the bridge identifying
Topping's scalar curvature with the Morgan--Tian one. -/
theorem scalarCurvatureAt_contMDiff (g : RiemannianMetric I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => scalarCurvatureAt g q) := by
  have hfun : (fun q => scalarCurvatureAt g q)
      = MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection
          (isLeviCivita_leviCivitaConnection g) :=
    funext fun q => scalarCurvatureAt_eq_scalarCurvatureAt g q
  rw [hfun]
  exact MorganTianLib.scalarCurvatureAt_leviCivita_contMDiff g

/-- **Math.** **Topping 2.5.4 from Topping 2.3.9, unconditionally.** If the family
`g` obeys the first-variation formula in the direction `h = -2\Ric`, then it
satisfies `∂_tR = ΔR + 2|\Ric|^2`. No smoothness side condition: the spatial
smoothness of the scalar curvature is now proved rather than assumed.

The variation formula is the only remaining antecedent under the whole scalar side
of the chapter, which is where the analytic work genuinely lives. -/
theorem hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn'
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hvar : HasScalarVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y) J) :
    HasScalarCurvatureEvolutionOn g J :=
  hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn hvar
    (fun t => scalarCurvatureAt_contMDiff (g t))

/-! The fixed spatial identities used above also give the converse: once the
Ricci-flow scalar evolution is known, the first-variation statement with
`h = -2 Ric` is exactly the same derivative after rewriting its three terms.
This is an algebraic equivalence, not a renamed target hypothesis; the genuine
producer for either side may therefore be supplied by an independent flow
calculation. -/

/-- **Math.** Under the Ricci-flow direction, the scalar evolution equation
`∂ₜR = ΔR + 2|Ric|²` is equivalent to Topping's scalar first-variation formula. -/
theorem hasScalarVariationOn_of_hasScalarCurvatureEvolutionOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hevolution : HasScalarCurvatureEvolutionOn g J) :
    HasScalarVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y) J := by
  intro t ht p
  have he := hevolution t ht p
  have h1 : bilinInnerAt (g t) p
      (fun x y => -2 * ricciTensorAt (g t) p x y) (ricciBilinAt (g t) p)
      = -2 * ricciNormSqAt (g t) p :=
    bilinInnerAt_neg_two_ricci (g t) p
  have h2 : divergence (g t) (g t).leviCivitaConnection
      (divergence (g t) (g t).leviCivitaConnection
        (covTensorOfBilin (fun q (x y : TangentSpace I q) =>
          -2 * ricciTensorAt (g t) q x y))) (fun i => i.elim0) p
      = -metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p := by
    have hone : divergence (g t) (g t).leviCivitaConnection
        (covTensorOfBilin (fun q (x y : TangentSpace I q) =>
          -2 * ricciTensorAt (g t) q x y))
        = differentialOneForm (fun q => scalarCurvatureAt (g t) q) := by
      funext Y q
      rw [differentialOneForm]
      have h := divergence_covTensorOfBilin_neg_two_ricci (g t) (Y 0) q
      rw [show (fun _ : Fin 1 => Y 0) = Y from funext fun j =>
        by rw [Subsingleton.elim j 0]] at h
      exact h
    rw [hone, divergence_differentialOneForm]
  have h3 : metricLaplacianAt (g t)
      (fun q => trace₂ (g t)
        (covTensorOfBilin (fun r (x y : TangentSpace I r) =>
          -2 * ricciTensorAt (g t) r x y)) q) p
      = -2 * metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p := by
    rw [show (fun q => trace₂ (g t)
        (covTensorOfBilin (fun r (x y : TangentSpace I r) =>
          -2 * ricciTensorAt (g t) r x y)) q)
      = fun q => -2 * scalarCurvatureAt (g t) q from
      funext fun q => trace₂_covTensorOfBilin_neg_two_ricci (g t) q]
    exact metricLaplacianAt_const_mul (g t) (-2)
      (scalarCurvatureAt_contMDiff (g t)) p
  convert he using 1
  rw [h1, h2, h3]
  ring

#print axioms Topping.hasScalarVariationOn_of_hasScalarCurvatureEvolutionOn

end Topping

end
