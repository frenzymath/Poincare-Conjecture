import Topping.RicciFlow.Evolution
import Topping.Riemannian.CurvatureMultilinear
import Topping.Riemannian.TensorNorm
import Topping.Riemannian.VariationCurvature

/-!
# The rough Laplacian of the curvature tensor

Topping's Chapter 2 §4 computes `Δ\Rm` in terms of second covariant derivatives
of the Ricci tensor, curvature-Ricci contractions, and the tensor `B`
(Topping p. 41):
`B(X,Y,W,Z) = ⟨\Rm(X,\cdot,Y,\cdot),\Rm(W,\cdot,Z,\cdot)⟩`,
the pairing of two curvature slices, which is the quadratic curvature expression
appearing in both the Laplacian formula and the curvature evolution equation.

`B` has some but not all of the symmetries of `\Rm`:
`B(X,Y,W,Z) = B(W,Z,X,Y) = B(Y,X,Z,W)`, both proved below.
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

/-- **Math.** Topping's tensor `B(X,Y,W,Z) = ⟨\Rm(X,·,Y,·),\Rm(W,·,Z,·)⟩`
(Topping p. 41): the metric pairing of two slices of the curvature tensor,
computed as the double sum over an orthonormal basis. -/
def curvatureB (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, ∑ j,
    riemannCurvatureAt g p x (stdOrthonormalBasis ℝ (TangentSpace I p) i) y
        (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
      riemannCurvatureAt g p w (stdOrthonormalBasis ℝ (TangentSpace I p) i) z
        (stdOrthonormalBasis ℝ (TangentSpace I p) j)

omit [I.Boundaryless] in
/-- **Math.** `B(X,Y,W,Z) = B(W,Z,X,Y)`: the pairing is symmetric in its two
curvature slices. -/
theorem curvatureB_swap_pairs (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) :
    curvatureB g p x y w z = curvatureB g p w z x y := by
  simp only [curvatureB]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    mul_comm _ _

/-- **Math.** `B(X,Y,W,Z) = B(Y,X,Z,W)`: swapping the two entries within each
slice is a symmetry, because each factor picks up the pair-swap symmetry of the
curvature tensor followed by relabelling the two summation indices. -/
theorem curvatureB_swap_within (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) :
    curvatureB g p x y w z = curvatureB g p y x z w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have halg := riemannCurvatureAt_isAlg g p
  -- Pair-swap symmetry `Rm(a,b,c,d) = Rm(c,d,a,b)` turns each factor
  -- `Rm(x,eᵢ,y,eⱼ)` into `Rm(y,eⱼ,x,eᵢ)`; then exchange the names of `i` and `j`.
  have hswap : ∀ (a b c d : TangentSpace I p),
      riemannCurvatureAt g p a b c d = riemannCurvatureAt g p c d a b :=
    fun a b c d => halg.pairSwap a b c d
  simp only [curvatureB]
  rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ (TangentSpace I p)))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hswap x (stdOrthonormalBasis ℝ (TangentSpace I p) j) y
      (stdOrthonormalBasis ℝ (TangentSpace I p) i),
    hswap w (stdOrthonormalBasis ℝ (TangentSpace I p) j) z
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)]

/-- **Math.** Differentiating the first-pair second Bianchi identity preserves
its cyclic sum. In corrected second-derivative notation,
nabla²(U,V)R(X,Y,Z,W) + nabla²(U,X)R(Y,V,Z,W)
  + nabla²(U,Y)R(V,X,Z,W) = 0.

This is the untraced identity used in Topping's derivation of equation (2.4.1). -/
theorem secondCovDerivAlong_riemannTensorField_cyclic_first_pair
    (g : RiemannianMetric I M)
    (U V X Y Z W : SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
          ![X, Y, Z, W] p
      + secondCovDerivAlong g.leviCivitaConnection U X (riemannTensorField g)
          ![Y, V, Z, W] p
      + secondCovDerivAlong g.leviCivitaConnection U Y (riemannTensorField g)
          ![V, X, Z, W] p = 0 := by
  let nabla := g.leviCivitaConnection
  let CD : SmoothVectorField I M -> SmoothVectorField I M ->
      SmoothVectorField I M -> SmoothVectorField I M ->
      SmoothVectorField I M -> M -> ℝ :=
    fun A B C D R =>
      MorganTianLib.covariantDifferential4 nabla
        (nabla.curvatureForm g) A B C D R
  have hCD (A B C D R : SmoothVectorField I M) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (CD A B C D R) := by
    exact covariantDifferential4_contMDiff nabla (nabla.curvatureForm g)
      (fun A B C D =>
        MorganTianLib.curvatureForm_contMDiff g nabla A B C D)
      A B C D R
  have hcyc (A B C D R : SmoothVectorField I M) (q : M) :
      CD A B C D R q + CD B R C D A q + CD R A C D B q = 0 := by
    exact
      MorganTianLib.covariantDifferential4_curvatureForm_cyclic_first_pair
        g nabla (isLeviCivita_leviCivitaConnection g).1
        (isLeviCivita_leviCivitaConnection g).2 A B C D R q
  have hfun :
      (fun q => CD X Y Z W V q + CD Y V Z W X q + CD V X Z W Y q) =
        fun _ => 0 := by
    funext q
    exact hcyc X Y Z W V q
  have hbase :
      U.dir (CD X Y Z W V) p + U.dir (CD Y V Z W X) p
          + U.dir (CD V X Z W Y) p = 0 := by
    have h :
        U.dir
          (fun q => CD X Y Z W V q + CD Y V Z W X q + CD V X Z W Y q) p =
            0 := by
      rw [hfun]
      simp only [SmoothVectorField.dir, mfderiv_const]
      rfl
    calc
      U.dir (CD X Y Z W V) p + U.dir (CD Y V Z W X) p
            + U.dir (CD V X Z W Y) p =
          U.dir (fun q => CD X Y Z W V q + CD Y V Z W X q) p
            + U.dir (CD V X Z W Y) p := by
              rw [U.dir_add p
                ((hCD X Y Z W V).mdifferentiableAt (by simp))
                ((hCD Y V Z W X).mdifferentiableAt (by simp))]
      _ = U.dir
          (fun q => CD X Y Z W V q + CD Y V Z W X q + CD V X Z W Y q) p := by
            exact (U.dir_add p
              ((hCD X Y Z W V).add (hCD Y V Z W X) |>.mdifferentiableAt (by simp))
              ((hCD V X Z W Y).mdifferentiableAt (by simp))).symm
      _ = 0 := h
  have hX := hcyc (nabla.cov U X) Y Z W V p
  have hY := hcyc X (nabla.cov U Y) Z W V p
  have hV := hcyc X Y Z W (nabla.cov U V) p
  have hZ := hcyc X Y (nabla.cov U Z) W V p
  have hW := hcyc X Y Z (nabla.cov U W) V p
  rw [secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U V ![X, Y, Z, W] p,
    secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U X ![Y, V, Z, W] p,
    secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U Y ![V, X, Z, W] p]
  change
    (U.dir (CD X Y Z W V) p
          - CD (nabla.cov U X) Y Z W V p
          - CD X (nabla.cov U Y) Z W V p
          - CD X Y (nabla.cov U Z) W V p
          - CD X Y Z (nabla.cov U W) V p
        - CD X Y Z W (nabla.cov U V) p)
      + (U.dir (CD Y V Z W X) p
          - CD (nabla.cov U Y) V Z W X p
          - CD Y (nabla.cov U V) Z W X p
          - CD Y V (nabla.cov U Z) W X p
          - CD Y V Z (nabla.cov U W) X p
        - CD Y V Z W (nabla.cov U X) p)
      + (U.dir (CD V X Z W Y) p
          - CD (nabla.cov U V) X Z W Y p
          - CD V (nabla.cov U X) Z W Y p
          - CD V X (nabla.cov U Z) W Y p
          - CD V X Z (nabla.cov U W) Y p
        - CD V X Z W (nabla.cov U Y) p) = 0
  linear_combination hbase - hX - hY - hV - hZ - hW

/-- **Math.** Tracing the differentiated first-pair Bianchi identity gives
Topping's equation (2.4.1): the rough Laplacian of the Riemann tensor is the
negative of the two cross second-derivative traces. -/
theorem roughLaplacian_riemannTensorField_eq_neg_cyclic_cross_sum
    (g : RiemannianMetric I M)
    (X Y Z W : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M -> Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e : Fin (Module.finrank ℝ E) -> SmoothVectorField I M :=
      fun i => MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    roughLaplacian g g.leviCivitaConnection (riemannTensorField g)
          ![X, Y, Z, W] p =
      -∑ i, (secondCovDerivAlong g.leviCivitaConnection (e i) X
              (riemannTensorField g) ![Y, e i, Z, W] p
            + secondCovDerivAlong g.leviCivitaConnection (e i) Y
              (riemannTensorField g) ![e i, X, Z, W] p) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M -> Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  rw [roughLaplacian_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hcyclic :=
    secondCovDerivAlong_riemannTensorField_cyclic_first_pair g
      (MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      X Y Z W p
  linear_combination hcyclic

/-- **Math.** Topping's formula for the rough Laplacian of the curvature tensor,
`(Δ\Rm)(X,Y,W,Z) = -∇²_{Y,W}\Ric(X,Z) + ∇²_{X,W}\Ric(Y,Z) - ∇²_{X,Z}\Ric(Y,W)
+ ∇²_{Y,Z}\Ric(X,W) - \Ric(R(W,Z)Y,X) + \Ric(R(W,Z)X,Y)
- 2(B(X,Y,W,Z) - B(X,Y,Z,W) + B(X,W,Y,Z) - B(X,Z,Y,W))`.

The `∇²\Ric` terms use `secondCovDerivAlong` on the Ricci `2`-tensor field, and the
two `\Ric`-of-curvature terms feed the curvature operator into `\Ric`. -/
def HasCurvatureLaplacianFormula (g : RiemannianMetric I M) : Prop :=
  ∀ (X Y W Z : SmoothVectorField I M) (p : M),
    roughLaplacian g g.leviCivitaConnection (riemannTensorField g)
        (fun i => if i = 0 then X else if i = 1 then Y else
          if i = 2 then W else Z) p =
      -secondCovDerivAlong g.leviCivitaConnection Y W (ricciTensorField g)
          (fun i => if i = 0 then X else Z) p
        + secondCovDerivAlong g.leviCivitaConnection X W (ricciTensorField g)
          (fun i => if i = 0 then Y else Z) p
        - secondCovDerivAlong g.leviCivitaConnection X Z (ricciTensorField g)
          (fun i => if i = 0 then Y else W) p
        + secondCovDerivAlong g.leviCivitaConnection Y Z (ricciTensorField g)
          (fun i => if i = 0 then X else W) p
        - ricciTensorAt g p (curvatureOperator g W Z Y p) (X p)
        + ricciTensorAt g p (curvatureOperator g W Z X p) (Y p)
        - 2 * (curvatureB g p (X p) (Y p) (W p) (Z p)
            - curvatureB g p (X p) (Y p) (Z p) (W p)
            + curvatureB g p (X p) (W p) (Y p) (Z p)
            - curvatureB g p (X p) (Z p) (Y p) (W p))

#print axioms Topping.secondCovDerivAlong_riemannTensorField_cyclic_first_pair
#print axioms Topping.roughLaplacian_riemannTensorField_eq_neg_cyclic_cross_sum

end Topping

end
