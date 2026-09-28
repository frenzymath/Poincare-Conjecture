import MorganTianLib.Ch03.RicciFlow.CurvatureLaplacianFormula

/-!
# Morgan--Tian Ch. 3 - the differentiated contracted Ricci trace

This module contracts the differentiated second Bianchi identity once more.
It identifies the divergence trace of the Ricci Hessian with one half of its
tensor-slot trace.  The proof uses only intrinsic orthonormal traces, so no
coordinate frame or auxiliary metric variation enters the statement.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Differentiating the contracted second Bianchi identity gives
`2 sum_i (nabla^2_{U,e_i} Ric)(e_i,V)
  = sum_i (nabla^2_{U,V} Ric)(e_i,e_i)`.

This is the intrinsic trace identity needed to cancel the scalar-Hessian
terms in the Ricci-tensor evolution equation. -/
theorem sum_secondCovDerivAlong_ricciTensorField_div_eq_half_trace
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    2 * (∑ i, secondCovDerivAlong g.leviCivitaConnection U
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (ricciTensorField g)
      ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i), V] p) =
      ∑ i, secondCovDerivAlong g.leviCivitaConnection U V
        (ricciTensorField g)
        ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i),
          extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)] p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
    fun i ↦ extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  let HR := fun A B X Y Z W ↦
    secondCovDerivAlong g.leviCivitaConnection A B
      (riemannTensorField g) ![X, Y, Z, W] p
  let HRic := fun A B X Y ↦
    secondCovDerivAlong g.leviCivitaConnection A B
      (ricciTensorField g) ![X, Y] p
  change 2 * (∑ i, HRic U (e i) (e i) V) =
    ∑ i, HRic U V (e i) (e i)
  have hcontract (j : Fin (Module.finrank ℝ (TangentSpace I p))) :
      (∑ i, HR U (e i) (e j) (e i) (e j) V) =
        HRic U V (e j) (e j) - HRic U (e j) (e j) V := by
    have h := secondCovDerivAlong_riemannTensorField_contracted_first_pair
      g U (e j) (e j) V p
    change (∑ i, HR U (e i) (e j) (e i) (e j) V) =
      HRic U V (e j) (e j) - HRic U (e j) V (e j) at h
    have hsymm : HRic U (e j) V (e j) = HRic U (e j) (e j) V := by
      exact secondCovDerivAlong_ricciTensorField_symm
        g U (e j) V (e j) p
    rw [hsymm] at h
    exact h
  have hterm (i j : Fin (Module.finrank ℝ (TangentSpace I p))) :
      HR U (e i) (e j) (e i) (e j) V =
        HR U (e i) V (e j) (e i) (e j) := by
    calc
      HR U (e i) (e j) (e i) (e j) V =
          HR U (e i) (e j) V (e j) (e i) := by
        exact secondCovDerivAlong_riemannTensorField_pairSwap
          g U (e i) (e j) (e i) (e j) V p
      _ = -HR U (e i) V (e j) (e j) (e i) := by
        exact secondCovDerivAlong_riemannTensorField_antisymm_firstPair
          g U (e i) (e j) V (e j) (e i) p
      _ = HR U (e i) V (e j) (e i) (e j) := by
        have hanti : HR U (e i) V (e j) (e j) (e i) =
            -HR U (e i) V (e j) (e i) (e j) := by
          exact secondCovDerivAlong_riemannTensorField_antisymm_secondPair
            g U (e i) V (e j) (e j) (e i) p
        rw [hanti]
        ring
  have hdouble :
      (∑ j, ∑ i, HR U (e i) (e j) (e i) (e j) V) =
        ∑ i, HRic U (e i) (e i) V := by
    calc
      (∑ j, ∑ i, HR U (e i) (e j) (e i) (e j) V) =
          ∑ j, ∑ i, HR U (e i) V (e j) (e i) (e j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        exact Finset.sum_congr rfl fun i _ ↦ hterm i j
      _ = ∑ i, ∑ j, HR U (e i) V (e j) (e i) (e j) := Finset.sum_comm
      _ = ∑ i, HRic U (e i) V (e i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        exact (secondCovDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum
          g U (e i) V (e i) p).symm
      _ = ∑ i, HRic U (e i) (e i) V := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        exact secondCovDerivAlong_ricciTensorField_symm
          g U (e i) V (e i) p
  have hcontractSum :
      (∑ j, ∑ i, HR U (e i) (e j) (e i) (e j) V) =
        ∑ j, (HRic U V (e j) (e j) - HRic U (e j) (e j) V) :=
    Finset.sum_congr rfl fun j _ ↦ hcontract j
  rw [hdouble, Finset.sum_sub_distrib] at hcontractSum
  linear_combination hcontractSum

#print axioms MorganTianLib.sum_secondCovDerivAlong_ricciTensorField_div_eq_half_trace

end MorganTianLib

end
