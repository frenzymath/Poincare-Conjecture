import Topping.Riemannian.CurvatureLaplacian
import Topping.Riemannian.CurvatureRicciTrace
import Topping.Riemannian.CurvatureSecondSymmetry

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Contracting the differentiated second Bianchi identity in a
standard orthonormal frame gives
`∑ᵢ ∇²(U,eᵢ)Rm(Y,eᵢ,W,Z) = ∇²(U,Z)Ric(W,Y) - ∇²(U,W)Ric(Z,Y)`.

The first cyclic term is put into this displayed slot order by pair symmetry;
the third term is changed to the negative `W,Y` trace by first-pair
antisymmetry. -/
theorem secondCovDerivAlong_riemannTensorField_contracted_first_pair
    (g : RiemannianMetric I M) (U Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, secondCovDerivAlong g.leviCivitaConnection U
      (MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (riemannTensorField g)
      ![Y, MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i), W, Z] p =
      secondCovDerivAlong g.leviCivitaConnection U Z (ricciTensorField g)
        ![W, Y] p -
      secondCovDerivAlong g.leviCivitaConnection U W (ricciTensorField g)
        ![Z, Y] p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
    fun i => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  have hcyc (i : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong g.leviCivitaConnection U (e i)
          (riemannTensorField g) ![W, Z, Y, e i] p
        + secondCovDerivAlong g.leviCivitaConnection U W
          (riemannTensorField g) ![Z, e i, Y, e i] p
        + secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![e i, W, Y, e i] p = 0 := by
    exact secondCovDerivAlong_riemannTensorField_cyclic_first_pair
      g U (e i) W Z Y (e i) p
  have hpair (i : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong g.leviCivitaConnection U (e i)
          (riemannTensorField g) ![W, Z, Y, e i] p =
        secondCovDerivAlong g.leviCivitaConnection U (e i)
          (riemannTensorField g) ![Y, e i, W, Z] p := by
    exact secondCovDerivAlong_riemannTensorField_pairSwap
      g U (e i) W Z Y (e i) p
  have hanti (i : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![e i, W, Y, e i] p =
        -secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![W, e i, Y, e i] p := by
    exact secondCovDerivAlong_riemannTensorField_antisymm_firstPair
      g U Z (e i) W Y (e i) p
  have hterm (i : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong g.leviCivitaConnection U (e i)
          (riemannTensorField g) ![Y, e i, W, Z] p
        + secondCovDerivAlong g.leviCivitaConnection U W
          (riemannTensorField g) ![Z, e i, Y, e i] p
        - secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![W, e i, Y, e i] p = 0 := by
    have h := hcyc i
    rw [hpair i, hanti i] at h
    simpa [sub_eq_add_neg] using h
  change
    (∑ i, secondCovDerivAlong g.leviCivitaConnection U (e i)
      (riemannTensorField g) ![Y, e i, W, Z] p) =
      secondCovDerivAlong g.leviCivitaConnection U Z (ricciTensorField g)
        ![W, Y] p -
      secondCovDerivAlong g.leviCivitaConnection U W (ricciTensorField g)
        ![Z, Y] p
  have hsum :
      ∑ i, (secondCovDerivAlong g.leviCivitaConnection U (e i)
          (riemannTensorField g) ![Y, e i, W, Z] p
        + secondCovDerivAlong g.leviCivitaConnection U W
          (riemannTensorField g) ![Z, e i, Y, e i] p
        - secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![W, e i, Y, e i] p) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hterm i
  have hsum' := hsum
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum'
  have htraceZ :
      secondCovDerivAlong g.leviCivitaConnection U Z (ricciTensorField g)
          ![W, Y] p =
        ∑ i, secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![W, e i, Y, e i] p := by
    dsimp [e]
    exact secondCovDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum
      g U Z W Y p
  have htraceW :
      secondCovDerivAlong g.leviCivitaConnection U W (ricciTensorField g)
          ![Z, Y] p =
        ∑ i, secondCovDerivAlong g.leviCivitaConnection U W
          (riemannTensorField g) ![Z, e i, Y, e i] p := by
    dsimp [e]
    exact secondCovDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum
      g U W Z Y p
  rw [htraceZ, htraceW]
  linear_combination hsum'

end Topping

end

#print axioms Topping.secondCovDerivAlong_riemannTensorField_contracted_first_pair
