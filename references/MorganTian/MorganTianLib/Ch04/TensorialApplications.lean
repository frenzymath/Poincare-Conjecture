import MorganTianLib.Ch04.Tensoriality
import MorganTianLib.Ch04.TensorialContact
import MorganTianLib.Ch03.RicciFlow.ScalarCurvatureSmooth
import MorganTianLib.Ch03.RicciFlow.CurvatureRicciTrace

/-!
# Morgan--Tian Ch. 4 - tensoriality bridges for curvature fields

The Chapter 3 evaluator definitions for curvature are consumed read-only.  Its
rank-four tensor laws and smoothness theorem provide a concrete instance of
the arbitrary-rank `IsCovariantTensorField` contract introduced in Ch. 4.
This bridge is deliberately separate from the Chapter 3 files so that the
maximum-principle code can use a source-level tensor predicate without changing
the existing evolution API.
-/

open Set Filter Function
open Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The Chapter 3 Riemann curvature evaluator is a genuine smooth
covariant tensor field.  The proof is the arbitrary-rank packaging of do
Carmo's rank-four curvature tensor theorem and the smooth curvature pairing.
-/
theorem riemannTensorField_isCovariantTensorField
    (g : RiemannianMetric I M) :
    IsCovariantTensorField (riemannTensorField g) := by
  let hT := g.leviCivitaConnection.curvatureForm_isCovariantTensor4 g
  have hrepr : ∀ (Y : Fin 4 → SmoothVectorField I M),
      riemannTensorField g Y =
        g.leviCivitaConnection.curvatureForm g (Y 0) (Y 1) (Y 2) (Y 3) := by
    intro Y
    funext q
    change g.leviCivitaConnection.curvatureFormAt g q
      ((Y 0) q) ((Y 1) q) ((Y 2) q) ((Y 3) q) = _
    exact g.leviCivitaConnection.curvatureFormAt_eq g q
      (X := Y 0) (Y := Y 1) (Z := Y 2) (T := Y 3)
      rfl rfl rfl rfl
  refine ⟨?_, ?_, ?_⟩
  · intro Y
    rw [hrepr Y]
    exact curvatureForm_contMDiff g g.leviCivitaConnection (Y 0) (Y 1) (Y 2) (Y 3)
  · intro Y i U V p
    rw [hrepr (Function.update Y i (U + V)), hrepr (Function.update Y i U),
      hrepr (Function.update Y i V)]
    fin_cases i
    · simpa [Function.update] using hT.add₁ U V (Y 1) (Y 2) (Y 3) p
    · simpa [Function.update] using hT.add₂ (Y 0) U V (Y 2) (Y 3) p
    · simpa [Function.update] using hT.add₃ (Y 0) (Y 1) U V (Y 3) p
    · simpa [Function.update] using hT.add₄ (Y 0) (Y 1) (Y 2) U V p
  · intro Y i f hf U p
    rw [hrepr (Function.update Y i (SmoothVectorField.smul f hf U)),
      hrepr (Function.update Y i U)]
    fin_cases i
    · simpa [Function.update] using hT.smul₁ f hf U (Y 1) (Y 2) (Y 3) p
    · simpa [Function.update] using hT.smul₂ f hf (Y 0) U (Y 2) (Y 3) p
    · simpa [Function.update] using hT.smul₃ f hf (Y 0) (Y 1) U (Y 3) p
    · simpa [Function.update] using hT.smul₄ f hf (Y 0) (Y 1) (Y 2) U p

private theorem fin4_update_zero {α : Type*} (Y : Fin 4 → α) (X : α) :
    Function.update Y (0 : Fin 4) X = ![X, Y 1, Y 2, Y 3] := by
  funext j
  fin_cases j <;> simp [Function.update]

private theorem fin4_update_one {α : Type*} (Y : Fin 4 → α) (X : α) :
    Function.update Y (1 : Fin 4) X = ![Y 0, X, Y 2, Y 3] := by
  funext j
  fin_cases j <;> simp [Function.update]

private theorem fin4_update_two {α : Type*} (Y : Fin 4 → α) (X : α) :
    Function.update Y (2 : Fin 4) X = ![Y 0, Y 1, X, Y 3] := by
  funext j
  fin_cases j <;> simp [Function.update]

private theorem fin4_update_three {α : Type*} (Y : Fin 4 → α) (X : α) :
    Function.update Y (3 : Fin 4) X = ![Y 0, Y 1, Y 2, X] := by
  funext j
  fin_cases j <;> simp [Function.update]

/-! ### Covariant-derivative bridge -/

/-- **Math.** For every fixed smooth direction, the covariant derivative of
the Chapter 3 Riemann evaluator is again a smooth covariant tensor in its
curvature slots.  The slot laws come from the read-only Ch03 differentiated
curvature theorem; component smoothness comes from the displayed
four-slot covariant differential. -/
theorem riemannTensorField_covTensorDerivAlong_isCovariantTensorField
    (g : RiemannianMetric I M) (U : SmoothVectorField I M) :
    IsCovariantTensorField
      (covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)) := by
  let nabla := g.leviCivitaConnection
  let T := nabla.curvatureForm g
  have hA : ∀ (Y : Fin 4 → SmoothVectorField I M) (q : M),
      riemannTensorField g Y q = T (Y 0) (Y 1) (Y 2) (Y 3) q := by
    intro Y q
    change nabla.curvatureFormAt g q
      ((Y 0) q) ((Y 1) q) ((Y 2) q) ((Y 3) q) = _
    exact nabla.curvatureFormAt_eq g q
      (X := Y 0) (Y := Y 1) (Z := Y 2) (T := Y 3)
      rfl rfl rfl rfl
  have h4 := isCovariantTensor4_covTensorDerivAlong_riemannTensorField g U
  refine ⟨?_, ?_, ?_⟩
  · intro Y
    have hrepr :
        covTensorDerivAlong nabla U (riemannTensorField g) Y =
          (fun q => covariantDifferential4 nabla T
            (Y 0) (Y 1) (Y 2) (Y 3) U q) := by
      funext q
      exact covTensorDerivAlong_eq_covariantDifferential4 nabla T
        (riemannTensorField g) hA U Y q
    rw [hrepr]
    exact covariantDifferential4_contMDiff' nabla T
      (fun X Y Z W => curvatureForm_contMDiff g nabla X Y Z W)
      (Y 0) (Y 1) (Y 2) (Y 3) U
  · intro Y i V W p
    fin_cases i
    · change
        covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (0 : Fin 4) (V + W)) p =
          covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
              (Function.update Y (0 : Fin 4) V) p +
            covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
              (Function.update Y (0 : Fin 4) W) p
      have hsum := fin4_update_zero Y (V + W)
      have hV := fin4_update_zero Y V
      have hW := fin4_update_zero Y W
      rw [hsum, hV, hW]
      exact h4.add₁ V W (Y 1) (Y 2) (Y 3) p
    · change
        covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (1 : Fin 4) (V + W)) p =
          covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
              (Function.update Y (1 : Fin 4) V) p +
            covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
              (Function.update Y (1 : Fin 4) W) p
      have hsum := fin4_update_one Y (V + W)
      have hV := fin4_update_one Y V
      have hW := fin4_update_one Y W
      rw [hsum, hV, hW]
      exact h4.add₂ (Y 0) V W (Y 2) (Y 3) p
    · change
        covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (2 : Fin 4) (V + W)) p =
          covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
              (Function.update Y (2 : Fin 4) V) p +
            covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
              (Function.update Y (2 : Fin 4) W) p
      have hsum := fin4_update_two Y (V + W)
      have hV := fin4_update_two Y V
      have hW := fin4_update_two Y W
      rw [hsum, hV, hW]
      exact h4.add₃ (Y 0) (Y 1) V W (Y 3) p
    · change
        covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (3 : Fin 4) (V + W)) p =
          covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
              (Function.update Y (3 : Fin 4) V) p +
            covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
              (Function.update Y (3 : Fin 4) W) p
      have hsum := fin4_update_three Y (V + W)
      have hV := fin4_update_three Y V
      have hW := fin4_update_three Y W
      rw [hsum, hV, hW]
      exact h4.add₄ (Y 0) (Y 1) (Y 2) V W p
  · intro Y i f hf V p
    fin_cases i
    · change
        covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (0 : Fin 4) (SmoothVectorField.smul f hf V)) p =
          f p * covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (0 : Fin 4) V) p
      rw [fin4_update_zero Y (SmoothVectorField.smul f hf V), fin4_update_zero Y V]
      exact h4.smul₁ f hf V (Y 1) (Y 2) (Y 3) p
    · change
        covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (1 : Fin 4) (SmoothVectorField.smul f hf V)) p =
          f p * covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (1 : Fin 4) V) p
      rw [fin4_update_one Y (SmoothVectorField.smul f hf V), fin4_update_one Y V]
      exact h4.smul₂ f hf (Y 0) V (Y 2) (Y 3) p
    · change
        covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (2 : Fin 4) (SmoothVectorField.smul f hf V)) p =
          f p * covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (2 : Fin 4) V) p
      rw [fin4_update_two Y (SmoothVectorField.smul f hf V), fin4_update_two Y V]
      exact h4.smul₃ f hf (Y 0) (Y 1) V (Y 3) p
    · change
        covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (3 : Fin 4) (SmoothVectorField.smul f hf V)) p =
          f p * covTensorDerivAlong g.leviCivitaConnection U (riemannTensorField g)
            (Function.update Y (3 : Fin 4) V) p
      rw [fin4_update_three Y (SmoothVectorField.smul f hf V), fin4_update_three Y V]
      exact h4.smul₄ f hf (Y 0) (Y 1) (Y 2) V p

/-- **Math.** The Riemann evaluator's traced contact defect vanishes whenever
the canonical orthonormal extensions have the required first- and second-jet
normality at the contact point.  This is a concrete Ch04 consumer of the
read-only Ch03 differentiated-curvature tensoriality theorem; it does not
assert that those geometric jet hypotheses are available for an arbitrary
connection or evolving section. -/
theorem riemannTensorField_roughLaplacianContactDefect_eq_zero_of_pointwise_normal
    (g : RiemannianMetric I M)
    (Y : Fin 4 → SmoothVectorField I M) (p : M)
    (hfirst : ∀ i j,
      (g.leviCivitaConnection.cov (canonicalContactFrame g p i) (Y j)) p = 0)
    (hsecond : ∀ i j,
      secondCov g.leviCivitaConnection (canonicalContactFrame g p i)
        (canonicalContactFrame g p i) (Y j) p = 0) :
    roughLaplacianContactDefect g g.leviCivitaConnection
      (riemannTensorField g) Y p = 0 := by
  exact roughLaplacianContactDefect_eq_zero_of_pointwise_normal
    g g.leviCivitaConnection (riemannTensorField g) Y p
    (riemannTensorField_isCovariantTensorField g)
    (fun i => riemannTensorField_covTensorDerivAlong_isCovariantTensorField g
      (canonicalContactFrame g p i))
    hfirst hsecond

end MorganTianLib
