import MorganTianLib.Ch02.Laplacian
import MorganTianLib.Ch03.RicciFlow.Basic

/-!
# Morgan--Tian Ch. 3 - intrinsic tensor Laplacians

This module provides the tensor calculus used to state the intrinsic curvature
evolution equations.  A covariant tensor field is represented by its action on
a tuple of smooth vector fields.  Following the displayed-slot convention used
in the curvature evolution calculation, covariant-derivative directions come
first.

The connection Laplacian is the metric trace of the corrected second covariant
derivative
`nabla^2_{X,Y} A = nabla_X nabla_Y A - nabla_{nabla_X Y} A`.
The module also packages the Riemann and Ricci tensors in this representation
and defines Morgan--Tian's quadratic curvature contraction `B`.
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

/-! ### Covariant tensor fields and covariant derivatives -/

/-- A covariant `k`-tensor field, represented by its action on `k` smooth
vector fields. -/
def CovTensorField (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (k : ℕ) : Type _ :=
  (Fin k → SmoothVectorField I M) → M → ℝ

/-- The covariant derivative `nabla_X A` of a covariant tensor field. -/
def covTensorDerivAlong (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {k : ℕ} (A : CovTensorField I M k) : CovTensorField I M k :=
  fun Y p =>
    X.dir (A Y) p - ∑ i, A (Function.update Y i (nabla.cov X (Y i))) p

/-- The full covariant derivative, with the derivative direction in the first
slot. -/
def covTensorDeriv (nabla : AffineConnection I M) {k : ℕ} (A : CovTensorField I M k) :
    CovTensorField I M (k + 1) :=
  fun Y p => covTensorDerivAlong nabla (Y 0) A (fun i => Y i.succ) p

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem covTensorDeriv_cons (nabla : AffineConnection I M) {k : ℕ}
    (A : CovTensorField I M k) (X : SmoothVectorField I M)
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    covTensorDeriv nabla A (Fin.cons X Y) p = covTensorDerivAlong nabla X A Y p := by
  simp only [covTensorDeriv, Fin.cons_zero, Fin.cons_succ]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
theorem covTensorDerivAlong_apply (nabla : AffineConnection I M)
    (X : SmoothVectorField I M) {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    covTensorDerivAlong nabla X A Y p =
      X.dir (A Y) p - ∑ i, A (Function.update Y i (nabla.cov X (Y i))) p :=
  rfl

/-! ### Corrected second covariant derivative -/

/-- The corrected second covariant derivative
`nabla^2_{X,Y} A = nabla_X nabla_Y A - nabla_{nabla_X Y} A`. -/
def secondCovDerivAlong (nabla : AffineConnection I M)
    (X Y : SmoothVectorField I M) {k : ℕ} (A : CovTensorField I M k) :
    CovTensorField I M k :=
  fun Z p =>
    covTensorDerivAlong nabla X (covTensorDerivAlong nabla Y A) Z p
      - covTensorDerivAlong nabla (nabla.cov X Y) A Z p

/-- The full second covariant derivative, with both derivative directions in
the first two slots. -/
def secondCovDeriv (nabla : AffineConnection I M) {k : ℕ}
    (A : CovTensorField I M k) : CovTensorField I M (k + 2) :=
  covTensorDeriv nabla (covTensorDeriv nabla A)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
theorem secondCovDeriv_cons (nabla : AffineConnection I M) {k : ℕ}
    (A : CovTensorField I M k) (X Y : SmoothVectorField I M)
    (Z : Fin k → SmoothVectorField I M) (p : M) :
    secondCovDeriv nabla A (Fin.cons X (Fin.cons Y Z)) p =
      secondCovDerivAlong nabla X Y A Z p := by
  rw [secondCovDeriv, covTensorDeriv_cons, covTensorDerivAlong_apply,
    secondCovDerivAlong, covTensorDerivAlong_apply, covTensorDerivAlong_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hupd : ∀ i : Fin k,
      Function.update (Fin.cons Y Z : Fin (k + 1) → SmoothVectorField I M)
          i.succ (nabla.cov X (Z i)) =
        Fin.cons Y (Function.update Z i (nabla.cov X (Z i))) := by
    intro i
    funext j
    refine Fin.cases ?_ ?_ j
    · rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      simp
    · intro j
      by_cases hij : j = i
      · subst hij
        simp
      · rw [Function.update_of_ne (fun h => hij (Fin.succ_injective _ h)),
          Fin.cons_succ, Fin.cons_succ, Function.update_of_ne hij]
  have hzero : Function.update
      (Fin.cons Y Z : Fin (k + 1) → SmoothVectorField I M) 0 (nabla.cov X Y) =
        Fin.cons (nabla.cov X Y) Z := by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro j
      rw [Function.update_of_ne (Fin.succ_ne_zero j), Fin.cons_succ, Fin.cons_succ]
  have hfun : covTensorDeriv nabla A (Fin.cons Y Z) =
      covTensorDerivAlong nabla Y A Z :=
    funext fun q => covTensorDeriv_cons nabla A Y Z q
  rw [hzero]
  simp only [hupd, covTensorDeriv_cons, hfun, covTensorDerivAlong_apply]
  ring

/-! ### Metric trace and rough Laplacian -/

/-- The metric trace of the first two slots of a covariant tensor field. -/
def traceFirstTwo (g : RiemannianMetric I M) {k : ℕ}
    (B : CovTensorField I M (k + 2)) : CovTensorField I M k :=
  fun Y p =>
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, B (Fin.cons (extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (Fin.cons (extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)) Y)) p

/-- The connection or rough Laplacian `Delta A = tr_g (nabla^2 A)`. -/
def roughLaplacian (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k) : CovTensorField I M k :=
  traceFirstTwo g (secondCovDeriv nabla A)

omit [CompleteSpace E] in
theorem roughLaplacian_apply (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    roughLaplacian g nabla A Y p =
      ∑ i, secondCovDerivAlong nabla
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
        A Y p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [roughLaplacian, traceFirstTwo, secondCovDeriv_cons]

/-! ### Curvature tensor fields -/

/-- The Riemann curvature tensor of `g` as a covariant `4`-tensor field. -/
def riemannTensorField (g : RiemannianMetric I M) : CovTensorField I M 4 :=
  fun Y p => g.leviCivitaConnection.curvatureFormAt g p
    (Y 0 p) (Y 1 p) (Y 2 p) (Y 3 p)

/-- The Ricci tensor of `g` as a covariant `2`-tensor field. -/
def ricciTensorField (g : RiemannianMetric I M) : CovTensorField I M 2 :=
  fun Y p => ricciTensorAt g p (Y 0 p) (Y 1 p)

@[simp] theorem riemannTensorField_apply (g : RiemannianMetric I M)
    (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    riemannTensorField g Y p = g.leviCivitaConnection.curvatureFormAt g p
      (Y 0 p) (Y 1 p) (Y 2 p) (Y 3 p) :=
  rfl

@[simp] theorem ricciTensorField_apply (g : RiemannianMetric I M)
    (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    ricciTensorField g Y p = ricciTensorAt g p (Y 0 p) (Y 1 p) :=
  rfl

/-! ### The quadratic curvature contraction -/

/-- Morgan--Tian's tensor
`B(x,y,w,z) = sum_i sum_j Rm(x,e_i,y,e_j) Rm(w,e_i,z,e_j)`. -/
def curvatureB (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, ∑ j,
    g.leviCivitaConnection.curvatureFormAt g p x
        (stdOrthonormalBasis ℝ (TangentSpace I p) i) y
        (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
      g.leviCivitaConnection.curvatureFormAt g p w
        (stdOrthonormalBasis ℝ (TangentSpace I p) i) z
        (stdOrthonormalBasis ℝ (TangentSpace I p) j)

/-- `B(x,y,w,z) = B(w,z,x,y)`. -/
theorem curvatureB_swap_pairs (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) :
    curvatureB g p x y w z = curvatureB g p w z x y := by
  simp only [curvatureB]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    mul_comm _ _

/-- `B(x,y,w,z) = B(y,x,z,w)`. -/
theorem curvatureB_swap_within (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) :
    curvatureB g p x y w z = curvatureB g p y x z w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have halg := g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  have hswap : ∀ (a b c d : TangentSpace I p),
      g.leviCivitaConnection.curvatureFormAt g p a b c d =
        g.leviCivitaConnection.curvatureFormAt g p c d a b :=
    fun a b c d => halg.pairSwap a b c d
  simp only [curvatureB]
  rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ (TangentSpace I p)))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hswap x (stdOrthonormalBasis ℝ (TangentSpace I p) j) y
      (stdOrthonormalBasis ℝ (TangentSpace I p) i),
    hswap w (stdOrthonormalBasis ℝ (TangentSpace I p) j) z
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)]

end MorganTianLib

end
