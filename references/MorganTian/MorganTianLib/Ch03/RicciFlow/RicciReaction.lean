import MorganTianLib.Ch03.RicciFlow.RicciLaplacian

/-!
# Morgan--Tian Ch. 3 - curvature actions in the Ricci evolution

This module identifies the two traced curvature actions supplied by the Ricci
Hessian commutator with the quadratic reaction term in the Ricci-flow
evolution equation.
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

/-! ### The source-faithful reaction term -/

/-- **Math.** The quadratic reaction part of the Ricci-tensor evolution,
evaluated on two fixed vector fields.  The curvature contraction has the
corrected Morgan--Tian index order `R_{jpkr}`. -/
noncomputable def ricciEvolutionReaction
    (g : RiemannianMetric I M) (X W : SmoothVectorField I M) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  2 * ∑ i, ∑ j,
      g.leviCivitaConnection.curvatureFormAt g p
          (X p) (stdOrthonormalBasis ℝ (TangentSpace I p) i) (W p)
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
        ricciTensorAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) j)
    - 2 * ∑ i,
        ricciTensorAt g p (X p)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) *
        ricciTensorAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) (W p)

private theorem curvatureFormAt_isAlg_ricciReaction
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    IsAlgCurvatureForm (g.leviCivitaConnection.curvatureFormAt g p) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g
    (g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q ↦ g.koszulDualSection_dual X Y W q)) p

private theorem ricciTensorAt_eq_curvatureFormAt_sum_ricciReaction
    (g : RiemannianMetric I M) (p : M) (x y : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ricciTensorAt g p x y =
      ∑ i, g.leviCivitaConnection.curvatureFormAt g p x
        (stdOrthonormalBasis ℝ (TangentSpace I p) i) y
        (stdOrthonormalBasis ℝ (TangentSpace I p) i) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simpa [ricciTensorAt, Riemannian.ricciBilin_apply] using
    Riemannian.ricciForm_eq_sum
      (curvatureFormAt_isAlg_ricciReaction g p) x y
      (stdOrthonormalBasis ℝ (TangentSpace I p))

private theorem sum_ricciTensorAt_curvature_diagonal
    (g : RiemannianMetric I M) (X W : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    ∑ i, ricciTensorAt g p
        ((g.leviCivitaConnection.curvature X
          (extendVector p (e i)) (extendVector p (e i))) p) (W p) =
      -∑ i, ricciTensorAt g p (X p) (e i) * ricciTensorAt g p (e i) (W p) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := curvatureFormAt_isAlg_ricciReaction g p
  have hterm (i : Fin (Module.finrank ℝ (TangentSpace I p))) :
      ricciTensorAt g p
          ((g.leviCivitaConnection.curvature X
            (extendVector p (e i)) (extendVector p (e i))) p) (W p) =
        ∑ j, g.leviCivitaConnection.curvatureFormAt g p
            (X p) (e i) (e i) (e j) * ricciTensorAt g p (e j) (W p) := by
    rw [show (g.leviCivitaConnection.curvature X
          (extendVector p (e i)) (extendVector p (e i))) p =
        g.leviCivitaConnection.curvatureOperatorAt p (X p) (e i) (e i) by
      simpa only [curvatureOperatorField, extendVector_apply] using
        curvatureOperatorField_apply_eq_curvatureOperatorAt g X
          (extendVector p (e i)) (extendVector p (e i)) p]
    exact ricciTensorAt_curvatureOperatorAt_expand g p (X p) (e i) (e i) (W p)
  dsimp only
  rw [Finset.sum_congr rfl fun i _ => by simpa only [e] using hterm i, Finset.sum_comm,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  have htrace :
      ∑ i, g.leviCivitaConnection.curvatureFormAt g p
          (X p) (e i) (e i) (e j) = -ricciTensorAt g p (X p) (e j) := by
    rw [ricciTensorAt_eq_curvatureFormAt_sum_ricciReaction g p (X p) (e j),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [halg.antisymm₃₄ (X p) (e i) (e j) (e i)]
    ring
  rw [htrace]
  ring

private theorem sum_ricciTensorAt_curvature_mixed
    (g : RiemannianMetric I M) (X W : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    ∑ i, ricciTensorAt g p (e i)
        ((g.leviCivitaConnection.curvature X (extendVector p (e i)) W) p) =
      ∑ i, ∑ j, g.leviCivitaConnection.curvatureFormAt g p
          (X p) (e i) (W p) (e j) * ricciTensorAt g p (e i) (e j) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ricciTensorAt_symm g p (e i)]
  rw [show (g.leviCivitaConnection.curvature X (extendVector p (e i)) W) p =
      g.leviCivitaConnection.curvatureOperatorAt p (X p) (e i) (W p) by
    simpa only [curvatureOperatorField, extendVector_apply] using
      curvatureOperatorField_apply_eq_curvatureOperatorAt g X
        (extendVector p (e i)) W p]
  rw [ricciTensorAt_curvatureOperatorAt_expand]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ricciTensorAt_symm g p (e j) (e i)]

private theorem curvatureRicciContraction_symm
    (g : RiemannianMetric I M) (p : M) (x w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    (∑ i, ∑ j, g.leviCivitaConnection.curvatureFormAt g p
        w (e i) x (e j) * ricciTensorAt g p (e i) (e j)) =
      ∑ i, ∑ j, g.leviCivitaConnection.curvatureFormAt g p
        x (e i) w (e j) * ricciTensorAt g p (e i) (e j) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := curvatureFormAt_isAlg_ricciReaction g p
  calc
    (∑ i, ∑ j, g.leviCivitaConnection.curvatureFormAt g p
        w (e i) x (e j) * ricciTensorAt g p (e i) (e j)) =
        ∑ i, ∑ j, g.leviCivitaConnection.curvatureFormAt g p
          x (e j) w (e i) * ricciTensorAt g p (e i) (e j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [halg.pairSwap w (e i) x (e j)]
    _ = ∑ i, ∑ j, g.leviCivitaConnection.curvatureFormAt g p
          x (e i) w (e j) * ricciTensorAt g p (e j) (e i) := by
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, g.leviCivitaConnection.curvatureFormAt g p
          x (e i) w (e j) * ricciTensorAt g p (e i) (e j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [ricciTensorAt_symm g p (e j) (e i)]

/-! ### The two commutator traces -/

/-- **Math.** The two traced curvature actions obtained by commuting the Ricci
Hessian equal the complete quadratic reaction in the Ricci-flow equation.
This is unconditional: every term is produced by the Levi--Civita curvature
and the Ricci tensor of `g`. -/
theorem sum_ricciHessian_commutator_curvature_eq_ricciEvolutionReaction
    (g : RiemannianMetric I M) (X W : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
      fun i ↦ extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    (∑ i, (ricciTensorAt g p
          ((g.leviCivitaConnection.curvature X (e i) (e i)) p) (W p) +
        ricciTensorAt g p (e i p)
          ((g.leviCivitaConnection.curvature X (e i) W) p))) +
      (∑ i, (ricciTensorAt g p
          ((g.leviCivitaConnection.curvature W (e i) (e i)) p) (X p) +
        ricciTensorAt g p (e i p)
          ((g.leviCivitaConnection.curvature W (e i) X) p))) =
        ricciEvolutionReaction g X W p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e₀ := stdOrthonormalBasis ℝ (TangentSpace I p)
  let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
    fun i ↦ extendVector p (e₀ i)
  have hdiagX := sum_ricciTensorAt_curvature_diagonal g X W p
  have hdiagW := sum_ricciTensorAt_curvature_diagonal g W X p
  have hmixX := sum_ricciTensorAt_curvature_mixed g X W p
  have hmixW := sum_ricciTensorAt_curvature_mixed g W X p
  have hmixSymm := curvatureRicciContraction_symm g p (X p) (W p)
  have hquad :
      (∑ i, ricciTensorAt g p (W p) (e₀ i) * ricciTensorAt g p (e₀ i) (X p)) =
        ∑ i, ricciTensorAt g p (X p) (e₀ i) *
          ricciTensorAt g p (e₀ i) (W p) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ricciTensorAt_symm g p (W p) (e₀ i),
      ricciTensorAt_symm g p (e₀ i) (X p)]
    ring
  simp only [extendVector_apply, Finset.sum_add_distrib]
  dsimp only [e₀] at hdiagX hdiagW hmixX hmixW hmixSymm hquad ⊢
  rw [hdiagX, hdiagW, hmixX, hmixW, hmixSymm, hquad]
  simp only [ricciEvolutionReaction]
  ring

#print axioms MorganTianLib.ricciEvolutionReaction
#print axioms MorganTianLib.sum_ricciHessian_commutator_curvature_eq_ricciEvolutionReaction

end MorganTianLib

end
