import Topping.ParabolicPDE.Compactness
import Topping.Riemannian.LieDerivative
import Topping.Riemannian.VariationScalar

/-!
# Chapter 5: the Ricci and DeTurck principal-symbol algebra

The analytic existence theorem is not available in the current dependency
cone.  This file therefore separates the part of Topping's calculation which
is genuinely finite-dimensional from the still-missing manifold/operator
bridge.  The matrix formula is the coordinate expression on a fixed frame; it
does not claim that an arbitrary coordinate operator has already been glued
over an atlas.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

/-! ## The raw Ricci-flow operator and the DeTurck modification -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-!
`ricciFlowOperator` is the tensor-field version of (Q(g)=-2\,\mathrm{Ric}(g)).
`deTurckModification` keeps the vector field which represents
`(T⁻¹ δG(T))^#` explicit.  The predicate
`IsDeTurckVectorFieldFor` records the metric-dual equation needed to identify a
chosen smooth field with that pointwise construction; no smooth-section
producer for this field is assumed here.
-/

def ricciFlowOperator (g : RiemannianMetric I M) : CovTensorField I M 2 :=
  fun Y p => -2 * ricciTensorField g Y p

def deTurckOneForm (g T : RiemannianMetric I M) : CovTensorField I M 1 :=
  divergence g g.leviCivitaConnection
    (gravitationTensor g (metricTensorField T))

def IsDeTurckVectorFieldFor (g T : RiemannianMetric I M)
    (V : SmoothVectorField I M) : Prop :=
  ∀ (p : M) (w : TangentSpace I p),
    T.metricInner p (V p) w = oneFormCovec g (deTurckOneForm g T) p w

def deTurckModification (g T : RiemannianMetric I M)
    (V : SmoothVectorField I M)
    (_hV : IsDeTurckVectorFieldFor g T V) : CovTensorField I M 2 :=
  fun Y p => ricciFlowOperator g Y p + symmetricGradient g V Y p

/-! ## Fixed-frame symbol formula -/

abbrev Covector (n : ℕ) := Fin n → ℝ

def covectorNormSq {n : ℕ} (xi : Covector n) : ℝ :=
  ∑ k, xi k ^ 2

/-- **Math.** The fixed-frame fibre of two-tensors, equipped with its Euclidean inner
product so that Chapter 4's strict-parabolicity predicate applies. -/
abbrev MatrixFiber (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

/-- **Math.** Read a Euclidean two-tensor fibre element as a coordinate matrix. -/
def matrixOfFiber {n : ℕ} (h : MatrixFiber n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => h (i, j)

/-- **Math.** Regard a coordinate matrix as a Euclidean two-tensor fibre
element. -/
def fiberOfMatrix {n : ℕ} (h : Matrix (Fin n) (Fin n) ℝ) : MatrixFiber n :=
  WithLp.toLp 2 (fun ij => h ij.1 ij.2)

@[simp] theorem matrixOfFiber_fiberOfMatrix {n : ℕ}
    (h : Matrix (Fin n) (Fin n) ℝ) :
    matrixOfFiber (fiberOfMatrix h) = h := by
  rfl

@[simp] theorem fiberOfMatrix_matrixOfFiber {n : ℕ} (h : MatrixFiber n) :
    fiberOfMatrix (matrixOfFiber h) = h := by
  rfl

/-- **Math.** Symmetric two-tensors in a fixed Euclidean frame. -/
def symmetricTensorSubmodule (n : ℕ) : Submodule ℝ (MatrixFiber n) where
  carrier := {h | ∀ i j, matrixOfFiber h i j = matrixOfFiber h j i}
  zero_mem' := by
    intro i j
    simp [matrixOfFiber]
  add_mem' := by
    intro h k hh hk i j
    simpa [matrixOfFiber] using
      congrArg₂ (· + ·) (hh i j) (hk i j)
  smul_mem' := by
    intro c h hh i j
    simpa [matrixOfFiber, smul_eq_mul] using
      congrArg (fun x : ℝ => c * x) (hh i j)

/-- **Math.** The fixed-frame Euclidean fibre `Sym²`. -/
abbrev FixedFrameSym2 (n : ℕ) := symmetricTensorSubmodule n

/-- **Math.** Read a fixed-frame symmetric two-tensor as a symmetric matrix. -/
def matrixOfSym2 {n : ℕ} (h : FixedFrameSym2 n) :
    Matrix (Fin n) (Fin n) ℝ :=
  matrixOfFiber h.1

@[simp] theorem matrixOfSym2_add {n : ℕ} (h k : FixedFrameSym2 n) :
    matrixOfSym2 (h + k) = matrixOfSym2 h + matrixOfSym2 k := by
  rfl

@[simp] theorem matrixOfSym2_smul {n : ℕ} (c : ℝ)
    (h : FixedFrameSym2 n) :
    matrixOfSym2 (c • h) = c • matrixOfSym2 h := by
  rfl

theorem matrixOfSym2_injective {n : ℕ} :
    Function.Injective (@matrixOfSym2 n) := by
  intro h k hmatrix
  apply Subtype.ext
  rw [← fiberOfMatrix_matrixOfFiber h.1,
    ← fiberOfMatrix_matrixOfFiber k.1]
  exact congrArg fiberOfMatrix hmatrix

/-- **Math.** Regard a symmetric coordinate matrix as an element of the
fixed-frame Euclidean `Sym²` fibre. -/
def sym2OfMatrix {n : ℕ} (h : Matrix (Fin n) (Fin n) ℝ) (hh : h.IsSymm) :
    FixedFrameSym2 n :=
  ⟨fiberOfMatrix h, by
    intro i j
    change h i j = h j i
    exact hh.apply j i⟩

@[simp] theorem matrixOfSym2_sym2OfMatrix {n : ℕ}
    (h : Matrix (Fin n) (Fin n) ℝ) (hh : h.IsSymm) :
    matrixOfSym2 (sym2OfMatrix h hh) = h := by
  rfl

theorem matrixOfSym2_isSymm {n : ℕ} (h : FixedFrameSym2 n) :
    (matrixOfSym2 h).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact h.2 j i

/-- **Math.** The Euclidean squared covector norm, made independent of the one-point
fixed-frame base. -/
def fixedFrameCovectorNormSq {n : ℕ} (_ : Unit) (xi : Covector n) : ℝ :=
  covectorNormSq xi

theorem fixedFrameCovectorNormSq_isSquaredCovectorNorm {n : ℕ} :
    IsSquaredCovectorNorm (@fixedFrameCovectorNormSq n) := by
  change IsSquaredCovectorNorm
    (fun (_ : Unit) (xi : Fin n → ℝ) => ∑ k, xi k ^ 2)
  simpa only [ParabolicPDE.euclideanNormSq] using
    euclideanNormSq_isSquaredCovectorNorm Unit n

def ricciLinearisationSymbol {n : ℕ}
    (xi : Covector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    covectorNormSq xi * h i j
      - xi i * (∑ k, h k j * xi k)
      - xi j * (∑ k, h i k * xi k)
      + xi i * xi j * (∑ k, h k k)

/-! The gauge contribution in the source calculation. -/
def ricciGaugeSymbol {n : ℕ}
    (xi : Covector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    -xi i * (∑ k, h k j * xi k)
      - xi j * (∑ k, h i k * xi k)
      + xi i * xi j * (∑ k, h k k)

def deTurckGaugeCancellationSymbol {n : ℕ}
    (xi : Covector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => -ricciGaugeSymbol xi h i j

def deTurckLinearisationSymbol {n : ℕ}
    (xi : Covector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ricciLinearisationSymbol xi h i j +
    deTurckGaugeCancellationSymbol xi h i j

theorem ricciLinearisationSymbol_formula {n : ℕ}
    (xi : Covector n) (h : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ricciLinearisationSymbol xi h i j =
      covectorNormSq xi * h i j
        - xi i * (∑ k, h k j * xi k)
        - xi j * (∑ k, h i k * xi k)
      + xi i * xi j * (∑ k, h k k) :=
  rfl

theorem ricciLinearisationSymbol_isSymm {n : ℕ} (xi : Covector n)
    {h : Matrix (Fin n) (Fin n) ℝ} (hh : h.IsSymm) :
    (ricciLinearisationSymbol xi h).IsSymm := by
  classical
  apply Matrix.IsSymm.ext
  intro i j
  have hcol :
      (∑ k, h k i * xi k) = ∑ k, h i k * xi k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hh.apply i k]
  have hrow :
      (∑ k, h j k * xi k) = ∑ k, h k j * xi k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hh.apply k j]
  simp only [ricciLinearisationSymbol]
  rw [hh.apply i j, hcol, hrow]
  ring

theorem ricciLinearisationSymbol_add {n : ℕ} (xi : Covector n)
    (h k : Matrix (Fin n) (Fin n) ℝ) :
    ricciLinearisationSymbol xi (h + k) =
      ricciLinearisationSymbol xi h + ricciLinearisationSymbol xi k := by
  classical
  ext i j
  simp only [ricciLinearisationSymbol, Matrix.add_apply,
    add_mul, Finset.sum_add_distrib]
  ring

theorem ricciLinearisationSymbol_smul {n : ℕ} (xi : Covector n)
    (c : ℝ) (h : Matrix (Fin n) (Fin n) ℝ) :
    ricciLinearisationSymbol xi (c • h) =
      c • ricciLinearisationSymbol xi h := by
  classical
  ext i j
  simp only [ricciLinearisationSymbol, Matrix.smul_apply, smul_eq_mul]
  have hcol :
      (∑ k, (c * h k j) * xi k) = c * ∑ k, h k j * xi k := by
    calc
      (∑ k, (c * h k j) * xi k) = ∑ k, c * (h k j * xi k) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = c * ∑ k, h k j * xi k := by rw [Finset.mul_sum]
  have hrow :
      (∑ k, (c * h i k) * xi k) = c * ∑ k, h i k * xi k := by
    calc
      (∑ k, (c * h i k) * xi k) = ∑ k, c * (h i k * xi k) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = c * ∑ k, h i k * xi k := by rw [Finset.mul_sum]
  have htrace : (∑ k, c * h k k) = c * ∑ k, h k k := by
    rw [Finset.mul_sum]
  rw [hcol, hrow, htrace]
  ring

/-- **Math.** The raw Ricci principal symbol as a linear endomorphism of the
fixed-frame symmetric two-tensor fibre. -/
def fixedFrameRicciSymbolLinearMap {n : ℕ} (xi : Covector n) :
    FixedFrameSym2 n →ₗ[ℝ] FixedFrameSym2 n where
  toFun h :=
    sym2OfMatrix (ricciLinearisationSymbol xi (matrixOfSym2 h))
      (ricciLinearisationSymbol_isSymm xi (matrixOfSym2_isSymm h))
  map_add' h k := by
    apply Subtype.ext
    change fiberOfMatrix
        (ricciLinearisationSymbol xi (matrixOfSym2 (h + k))) =
      fiberOfMatrix (ricciLinearisationSymbol xi (matrixOfSym2 h)) +
        fiberOfMatrix (ricciLinearisationSymbol xi (matrixOfSym2 k))
    rw [matrixOfSym2_add, ricciLinearisationSymbol_add]
    rfl
  map_smul' c h := by
    apply Subtype.ext
    change fiberOfMatrix
        (ricciLinearisationSymbol xi (matrixOfSym2 (c • h))) =
      c • fiberOfMatrix (ricciLinearisationSymbol xi (matrixOfSym2 h))
    rw [matrixOfSym2_smul, ricciLinearisationSymbol_smul]
    rfl

/-- **Math.** The raw Ricci principal symbol, bundled as a continuous linear
endomorphism of the finite-dimensional fixed-frame `Sym²` fibre. -/
def fixedFrameRicciSymbol {n : ℕ} :
    Unit → Covector n → FixedFrameSym2 n →L[ℝ] FixedFrameSym2 n :=
  fun _ xi => LinearMap.toContinuousLinearMap
    (fixedFrameRicciSymbolLinearMap xi)

theorem fixedFrameRicciSymbol_apply_matrix {n : ℕ}
    (xi : Covector n) (h : FixedFrameSym2 n) :
    matrixOfSym2 (fixedFrameRicciSymbol () xi h) =
      ricciLinearisationSymbol xi (matrixOfSym2 h) := by
  rfl

theorem ricciGaugeSymbol_formula {n : ℕ}
    (xi : Covector n) (h : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ricciGaugeSymbol xi h i j =
      -xi i * (∑ k, h k j * xi k)
        - xi j * (∑ k, h i k * xi k)
        + xi i * xi j * (∑ k, h k k) :=
  rfl

theorem ricciLinearisationSymbol_rankOne {n : ℕ} (xi : Covector n) :
    ricciLinearisationSymbol xi (fun i j => xi i * xi j) = 0 := by
  classical
  ext i j
  simp only [ricciLinearisationSymbol, covectorNormSq, Matrix.zero_apply]
  have hleft :
      (∑ k, xi k ^ 2) * (xi i * xi j) =
        xi i * (xi j * ∑ k, xi k ^ 2) := by ring
  have hright :
      xi i * (∑ k, xi k * xi j * xi k) =
        xi i * (xi j * ∑ k, xi k ^ 2) := by
    congr 1
    calc
      ∑ k, xi k * xi j * xi k = ∑ k, xi j * (xi k ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = xi j * ∑ k, xi k ^ 2 := by rw [Finset.mul_sum]
  have hmiddle :
      xi j * (∑ k, xi i * xi k * xi k) =
        xi j * (xi i * ∑ k, xi k ^ 2) := by
    congr 1
    calc
      ∑ k, xi i * xi k * xi k = ∑ k, xi i * (xi k ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = xi i * ∑ k, xi k ^ 2 := by rw [Finset.mul_sum]
  have hsum : (∑ k, xi k * xi k) = ∑ k, xi k ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hright, hmiddle]
  rw [hsum]
  ring

/-- **Math.** The symmetric rank-one gauge tensor `xi ⊗ xi` in the
fixed-frame Euclidean `Sym²` fibre. -/
def rankOneSym2 {n : ℕ} (xi : Covector n) : FixedFrameSym2 n :=
  sym2OfMatrix (fun i j => xi i * xi j) (by
    apply Matrix.IsSymm.ext
    intro i j
    ring)

@[simp] theorem matrixOfSym2_rankOneSym2 {n : ℕ} (xi : Covector n) :
    matrixOfSym2 (rankOneSym2 xi) = fun i j => xi i * xi j := by
  rfl

theorem rankOneSym2_ne_zero {n : ℕ} {xi : Covector n} (hxi : xi ≠ 0) :
    rankOneSym2 xi ≠ 0 := by
  intro hz
  apply hxi
  funext i
  have hii := congrArg
    (fun h : FixedFrameSym2 n => matrixOfSym2 h i i) hz
  change xi i * xi i = 0 at hii
  exact mul_self_eq_zero.mp hii

theorem fixedFrameRicciSymbol_rankOne {n : ℕ} (xi : Covector n) :
    fixedFrameRicciSymbol () xi (rankOneSym2 xi) = 0 := by
  apply matrixOfSym2_injective
  rw [fixedFrameRicciSymbol_apply_matrix,
    matrixOfSym2_rankOneSym2, ricciLinearisationSymbol_rankOne]
  rfl

theorem fixedFrameRicciSymbol_not_strictlyParabolic {n : ℕ}
    {xi : Covector n} (hxi : xi ≠ 0) :
    ¬ StrictlyParabolic (@fixedFrameRicciSymbol n)
      (@fixedFrameCovectorNormSq n) := by
  intro hpar
  obtain ⟨hq, lam, hlam, hcoercive⟩ := hpar
  have hqpos : 0 < fixedFrameCovectorNormSq () xi :=
    hq.2.2.1 () xi hxi
  have hvpos : 0 < ‖rankOneSym2 xi‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (rankOneSym2_ne_zero hxi)) 2
  have hle :
      lam * fixedFrameCovectorNormSq () xi * ‖rankOneSym2 xi‖ ^ 2 ≤ 0 := by
    simpa [fixedFrameRicciSymbol_rankOne] using
      hcoercive () xi (rankOneSym2 xi)
  have hlhs :
      0 < lam * fixedFrameCovectorNormSq () xi * ‖rankOneSym2 xi‖ ^ 2 :=
    mul_pos (mul_pos hlam hqpos) hvpos
  exact (not_lt_of_ge hle) hlhs

/-! Remark 5.1.1: every infinitesimal diffeomorphism direction lies in the
fixed-frame symbol kernel. -/
theorem ricciLinearisationSymbol_gaugeKernel {n : ℕ}
    (xi omega : Covector n) :
    ricciLinearisationSymbol xi
      (fun i j => xi i * omega j + omega i * xi j) = 0 := by
  classical
  ext i j
  simp only [ricciLinearisationSymbol, covectorNormSq, Matrix.zero_apply]
  let a : ℝ := ∑ k, xi k * omega k
  have hxx : (∑ k, xi k * xi k) = ∑ k, xi k ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hox : (∑ k, omega k * xi k) = a := by
    dsimp only [a]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hcol :
      (∑ k, (xi k * omega j + omega k * xi j) * xi k) =
        omega j * (∑ k, xi k ^ 2) + xi j * a := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    calc
      (∑ k, xi k * omega j * xi k) + ∑ k, omega k * xi j * xi k
          = omega j * (∑ k, xi k * xi k) +
              xi j * (∑ k, omega k * xi k) := by
              congr 1 <;> rw [Finset.mul_sum]
              · apply Finset.sum_congr rfl
                intro k hk
                ring
              · apply Finset.sum_congr rfl
                intro k hk
                ring
      _ = omega j * (∑ k, xi k ^ 2) + xi j * a := by rw [hxx, hox]
  have hrow :
      (∑ k, (xi i * omega k + omega i * xi k) * xi k) =
        xi i * a + omega i * (∑ k, xi k ^ 2) := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    calc
      (∑ k, xi i * omega k * xi k) + ∑ k, omega i * xi k * xi k
          = xi i * (∑ k, xi k * omega k) +
              omega i * (∑ k, xi k * xi k) := by
              congr 1 <;> rw [Finset.mul_sum]
              · apply Finset.sum_congr rfl
                intro k hk
                ring
              · apply Finset.sum_congr rfl
                intro k hk
                ring
      _ = xi i * a + omega i * (∑ k, xi k ^ 2) := by
            dsimp only [a]
            rw [hxx]
  have htrace :
      (∑ k, (xi k * omega k + omega k * xi k)) = 2 * a := by
    rw [Finset.sum_add_distrib, hox]
    dsimp only [a]
    ring
  rw [hcol, hrow, htrace]
  ring

theorem deTurckLinearisationSymbol_eq_identity {n : ℕ}
    (xi : Covector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    deTurckLinearisationSymbol xi h = covectorNormSq xi • h := by
  classical
  ext i j
  simp only [deTurckLinearisationSymbol, deTurckGaugeCancellationSymbol,
    ricciGaugeSymbol, ricciLinearisationSymbol, covectorNormSq]
  change _ = (∑ k, xi k ^ 2) * h i j
  ring

/-- **Math.** The fixed-frame DeTurck symbol on symmetric two-tensors, bundled
as a continuous linear map with the Euclidean fibre metric. -/
def fixedFrameDeTurckSymbol {n : ℕ} :
    Unit → Covector n → FixedFrameSym2 n →L[ℝ] FixedFrameSym2 n :=
  connectionLaplacianSymbol (@fixedFrameCovectorNormSq n)

theorem fixedFrameDeTurckSymbol_apply_matrix {n : ℕ}
    (xi : Covector n) (h : FixedFrameSym2 n) :
    matrixOfSym2 (fixedFrameDeTurckSymbol () xi h) =
      deTurckLinearisationSymbol xi (matrixOfSym2 h) := by
  rw [deTurckLinearisationSymbol_eq_identity]
  ext i j
  simp [fixedFrameDeTurckSymbol, connectionLaplacianSymbol,
    fixedFrameCovectorNormSq, matrixOfSym2, matrixOfFiber]

/-!
The next predicate is the finite-frame form of the chart/symbol compatibility
needed later in the geometric construction.  It does not identify either
symbol with an intrinsic operator; it records the exact representation change
between the bundled symmetric fibre and its coordinate matrix.
-/

def FixedFrameMatrixSymbolBridge {n : ℕ}
    (sigma : Unit → Covector n → FixedFrameSym2 n →L[ℝ] FixedFrameSym2 n)
    (formula : Covector n → Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ xi h, matrixOfSym2 (sigma () xi h) =
    formula xi (matrixOfSym2 h)

theorem fixedFrameRicciSymbol_matrixBridge {n : ℕ} :
    FixedFrameMatrixSymbolBridge (@fixedFrameRicciSymbol n)
      ricciLinearisationSymbol := by
  intro xi h
  exact fixedFrameRicciSymbol_apply_matrix xi h

theorem fixedFrameDeTurckSymbol_matrixBridge {n : ℕ} :
    FixedFrameMatrixSymbolBridge (@fixedFrameDeTurckSymbol n)
      deTurckLinearisationSymbol := by
  intro xi h
  exact fixedFrameDeTurckSymbol_apply_matrix xi h

/-! The bundled DeTurck symbol is the identity multiple predicted by the
matrix cancellation, with no remaining choice of a matrix representative. -/

theorem fixedFrameDeTurckSymbol_eq_covectorNormSq_smul_id {n : ℕ}
    (xi : Covector n) :
    fixedFrameDeTurckSymbol () xi =
      covectorNormSq xi • ContinuousLinearMap.id ℝ (FixedFrameSym2 n) := by
  rfl

theorem fixedFrameDeTurckSymbol_isPositiveMultipleOfIdentity {n : ℕ} :
    IsPositiveMultipleOfIdentity (@fixedFrameDeTurckSymbol n) := by
  intro _ xi hxi
  refine ⟨covectorNormSq xi, ?_, ?_⟩
  · exact (fixedFrameCovectorNormSq_isSquaredCovectorNorm (n := n)).2.2.1
      () xi hxi
  · exact fixedFrameDeTurckSymbol_eq_covectorNormSq_smul_id xi

theorem deTurckLinearisationSymbol_strictlyParabolic {n : ℕ}
    : StrictlyParabolic (@fixedFrameDeTurckSymbol n)
        (@fixedFrameCovectorNormSq n) := by
  exact connectionLaplacianSymbol_strictlyParabolic
    (@fixedFrameCovectorNormSq n)
    fixedFrameCovectorNormSq_isSquaredCovectorNorm

/-!
The preceding equality is the exact fixed-frame cancellation in (5.2.1).
To use it as a theorem about the Frechet linearisation of the geometric
operator one still needs a chart second-jet/linearisation bridge.  The bridge
is intentionally a named proposition rather than an axiom.
-/

def HasGeometricRicciSymbolBridge {n : ℕ}
    (sigma : Covector n → Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ xi h, sigma xi h = ricciLinearisationSymbol xi h

def HasGeometricDeTurckSymbolBridge {n : ℕ}
    (sigma : Covector n → Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ xi h, sigma xi h = deTurckLinearisationSymbol xi h

theorem geometricRicciSymbol_rankOne_of_bridge {n : ℕ}
    (sigma : Covector n → Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ)
    (hbridge : HasGeometricRicciSymbolBridge sigma)
    (xi : Covector n) :
    sigma xi (fun i j => xi i * xi j) = 0 := by
  rw [hbridge]
  exact ricciLinearisationSymbol_rankOne xi

theorem geometricDeTurckSymbol_identity_of_bridge {n : ℕ}
    (sigma : Covector n → Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ)
    (hbridge : HasGeometricDeTurckSymbolBridge sigma)
    (xi : Covector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    sigma xi h = covectorNormSq xi • h := by
  rw [hbridge]
  exact deTurckLinearisationSymbol_eq_identity xi h

#print axioms ricciLinearisationSymbol_rankOne
#print axioms ricciLinearisationSymbol_gaugeKernel
#print axioms fixedFrameRicciSymbol_not_strictlyParabolic
#print axioms deTurckLinearisationSymbol_eq_identity
#print axioms fixedFrameDeTurckSymbol_apply_matrix
#print axioms deTurckLinearisationSymbol_strictlyParabolic
#print axioms geometricDeTurckSymbol_identity_of_bridge

end Topping

end
