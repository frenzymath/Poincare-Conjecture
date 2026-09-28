import PetersenLib.Foundations.RiemannianMetric
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Petersen Ch. 1, §1.5 — Some Tensor Concepts

Pointwise linear algebra of tensors on a Riemannian manifold, formalized on
a finite-dimensional real inner product space `V` (which instantiates to
`TangentSpace I x` under `[HasMetric I M]`):

* **Type change** (§1.5.1): the musical isomorphism `tensorTypeChange :
  V ≃ₗ[ℝ] V →ₗ[ℝ] ℝ`, and the induced index-raising/lowering equivalences
  `lowerIndex`/`raiseIndex` between `(1,1)`-tensors (`V →ₗ[ℝ] V`) and
  `(0,2)`-tensors (bilinear forms), `twoZeroOfZeroTwo` between `(0,2)`- and
  `(2,0)`-tensors, with the Ricci (`ricciTensorTypes`) and curvature
  (`curvatureTensorTypes`, `curvatureTwoTwoTypes`) bookkeeping.
* **Contractions** (§1.5.2): `tensorContraction` (trace after type change),
  `ricciAsContraction`, `scalarCurvatureOfRicci`.
* **Inner products of tensors** (§1.5.3): `operatorNorm`, the trace inner
  product `traceInnerProduct` with its Euclidean norm
  `euclideanNormLinearMap`, the orthonormal-frame component formulas
  `euclideanNormOneOneTensor` / `euclideanNormZeroTwoTensor`, the pointwise
  inner product of `(0,2)`-tensors `pointwiseTensorInnerProduct`, and the
  `L²` pairing `l2TensorInnerProduct`.
* **Positional notation** (§1.5.4): `positionalTensorNotation`.

Design scope: full mixed `(s,t)`-tensor powers are not built; the four types
used in Petersen Ch. 1–3 (`(1,1)`, `(0,2)`, `(2,0)`, `(0,4)`, `(2,2)`) are
represented by (multi)linear maps and all inner products are transported
through the musical isomorphisms, exactly as Petersen does in an orthonormal
frame.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.5.
-/

open scoped ContDiff Manifold Topology InnerProductSpace Bundle

noncomputable section

namespace PetersenLib

/-! ## §1.5.1 Type change -/

section TypeChange

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- **Math.** The real inner product of `V` is nondegenerate as a bilinear
form (Petersen §1.5.1: the metric identifies `TM` with `T*M`). -/
theorem innerₗ_nondegenerate (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] : (innerₗ V).Nondegenerate :=
  ⟨fun x hx => inner_self_eq_zero.mp (hx x),
   fun y hy => inner_self_eq_zero.mp (hy y)⟩

variable (V) in
/-- **Math.** Petersen §1.5.1 (type change): the **musical isomorphism**
`TM ≅ T*M` induced by the metric, `v ↦ g(v, ·)`. Concretely it sends a frame
vector `E_i` to `g(E_i, ·) = g_{ij} σ^j`; for an orthonormal frame the dual
of `E_i` is just `σ^i`. Replacing occurrences of `TM` by `T*M` (or back via
the inverse) along this isomorphism lets one view an `(s,t)`-tensor as an
`(s-k, t+k)`-tensor. -/
def tensorTypeChange : V ≃ₗ[ℝ] (V →ₗ[ℝ] ℝ) :=
  LinearMap.BilinForm.toDual (innerₗ V) (innerₗ_nondegenerate V)

@[simp]
theorem tensorTypeChange_apply (v w : V) :
    tensorTypeChange V v w = ⟪v, w⟫_ℝ :=
  LinearMap.BilinForm.toDual_def (innerₗ_nondegenerate V)

/-- **Math.** Defining property of the inverse musical isomorphism (the
vector dual to a `1`-form `φ` is `g^{ij}φ_j E_i`): pairing it with the metric
recovers `φ`. -/
@[simp]
theorem inner_tensorTypeChange_symm (φ : V →ₗ[ℝ] ℝ) (w : V) :
    ⟪(tensorTypeChange V).symm φ, w⟫_ℝ = φ w :=
  LinearMap.BilinForm.apply_toDual_symm_apply
    (hB := innerₗ_nondegenerate V) (f := φ) (v := w)

variable (V) in
/-- **Math.** Petersen §1.5.1: **lowering an index**. A `(1,1)`-tensor
`T = T^i_j E_i ⊗ σ^j` corresponds to the `(0,2)`-tensor
`T_{kj} = g_{ki} T^i_j`, i.e. the bilinear form `(v, w) ↦ g(T v, w)`.
This is a linear equivalence of tensor spaces. -/
def lowerIndex : (V →ₗ[ℝ] V) ≃ₗ[ℝ] (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :=
  (LinearEquiv.refl ℝ V).arrowCongr (tensorTypeChange V)

@[simp]
theorem lowerIndex_apply (T : V →ₗ[ℝ] V) (v w : V) :
    lowerIndex V T v w = ⟪T v, w⟫_ℝ := by
  simp [lowerIndex]

variable (V) in
/-- **Math.** Petersen §1.5.1: **raising an index**, the inverse of
`lowerIndex`: a `(0,2)`-tensor `T_{ij}` corresponds to the `(1,1)`-tensor
`T^k_j = g^{ki} T_{ij}`, i.e. the unique linear map with
`g((raiseIndex B) v, w) = B(v, w)`. -/
def raiseIndex : (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →ₗ[ℝ] V) :=
  (lowerIndex V).symm

/-- **Math.** Defining property of `raiseIndex`. -/
@[simp]
theorem inner_raiseIndex (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : V) :
    ⟪raiseIndex V B v, w⟫_ℝ = B v w := by
  have h : lowerIndex V (raiseIndex V B) = B := (lowerIndex V).apply_symm_apply B
  calc ⟪raiseIndex V B v, w⟫_ℝ = lowerIndex V (raiseIndex V B) v w := by simp
    _ = B v w := by rw [h]

@[simp]
theorem raiseIndex_lowerIndex (T : V →ₗ[ℝ] V) :
    raiseIndex V (lowerIndex V T) = T :=
  (lowerIndex V).symm_apply_apply T

@[simp]
theorem lowerIndex_raiseIndex (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    lowerIndex V (raiseIndex V B) = B :=
  (lowerIndex V).apply_symm_apply B

variable (V) in
/-- **Math.** Petersen §1.5.1: type change from a `(0,2)`-tensor to a
`(2,0)`-tensor, `T^{ij} = g^{ik} g^{jl} T_{kl}`: both arguments are raised,
so the `(2,0)`-tensor acts on pairs of `1`-forms by
`(φ, ψ) ↦ B(♯φ, ♯ψ)`. -/
def twoZeroOfZeroTwo :
    (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] ((V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ) :=
  (tensorTypeChange V).arrowCongr
    ((tensorTypeChange V).arrowCongr (LinearEquiv.refl ℝ ℝ))

@[simp]
theorem twoZeroOfZeroTwo_apply (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (φ ψ : V →ₗ[ℝ] ℝ) :
    twoZeroOfZeroTwo V B φ ψ =
      B ((tensorTypeChange V).symm φ) ((tensorTypeChange V).symm ψ) := by
  simp [twoZeroOfZeroTwo]

/-- **Math.** Petersen §1.5.1 (notation, "the Ricci tensor as tensors of
different types"): in an orthonormal frame `E_i` the components of the
`(0,2)`-version `Ric_{jk} = g_{ji} Ric^i_k` and of the `(2,0)`-version
`Ric^{jk} = g^{ki} Ric^j_i` of a `(1,1)`-tensor `Ric` all coincide with
`Ric^j_k = g(Ric(E_j), E_k)`; the `(2,0)`-tensor is evaluated on the dual
coframe `σ^j = ♭E_j`. -/
theorem ricciTensorTypes {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (Ric : V →ₗ[ℝ] V) (j k : ι) :
    lowerIndex V Ric (b j) (b k) = ⟪Ric (b j), b k⟫_ℝ ∧
      twoZeroOfZeroTwo V (lowerIndex V Ric)
        (tensorTypeChange V (b j)) (tensorTypeChange V (b k)) =
        ⟪Ric (b j), b k⟫_ℝ := by
  refine ⟨lowerIndex_apply Ric (b j) (b k), ?_⟩
  simp

variable (V) in
/-- **Math.** Petersen §1.5.1 (notation, "the curvature tensor as tensors of
different types"): the linear equivalence between the `(1,3)`-curvature
tensor `(X, Y, Z) ↦ R(X,Y)Z` and the `(0,4)`-tensor
`R_{ijkl} = g(R(E_i, E_j)E_k, E_l)`, obtained by lowering the vector-valued
slot; per Petersen's convention the raised index is placed **last**. -/
def curvatureTensorTypes :
    (V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V) ≃ₗ[ℝ]
      (V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :=
  (LinearEquiv.refl ℝ V).arrowCongr
    ((LinearEquiv.refl ℝ V).arrowCongr (lowerIndex V))

@[simp]
theorem curvatureTensorTypes_apply (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V)
    (x y z w : V) :
    curvatureTensorTypes V R x y z w = ⟪R x y z, w⟫_ℝ := by
  simp [curvatureTensorTypes]

variable (V) in
/-- **Math.** Petersen §1.5.1: the **curvature operator** type of the
curvature tensor. Raising the last index pair of the `(0,4)`-tensor
`R_{ijkl}` produces the `(2,2)`-tensor `R^{kl}_{ij} = R_{ijst} g^{sk} g^{tl}`,
here encoded as a bilinear map in the two remaining vector slots `(x, y)`
with values in `(2,0)`-tensors (bilinear forms on the dual):
`(x, y, φ, ψ) ↦ R(x, y, ♯φ, ♯ψ)`. Raising a different index pair would give
a different `(2,2)`-tensor. -/
def curvatureTwoTwoTypes :
    (V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
      (V →ₗ[ℝ] V →ₗ[ℝ] ((V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ)) :=
  (LinearEquiv.refl ℝ V).arrowCongr
    ((LinearEquiv.refl ℝ V).arrowCongr (twoZeroOfZeroTwo V))

@[simp]
theorem curvatureOperator_apply (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x y : V) (φ ψ : V →ₗ[ℝ] ℝ) :
    curvatureTwoTwoTypes V R x y φ ψ =
      R x y ((tensorTypeChange V).symm φ) ((tensorTypeChange V).symm ψ) := by
  simp [curvatureTwoTwoTypes]

/-- **Math.** Evaluating the curvature operator on the coframe recovers the
`(0,4)`-components: `R^{kl}_{ij}` evaluated at `σ^k = ♭z, σ^l = ♭w` equals
`R_{ijkl}` (indices raised then lowered cancel). -/
theorem curvatureOperator_apply_tensorTypeChange
    (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (x y z w : V) :
    curvatureTwoTwoTypes V R x y (tensorTypeChange V z) (tensorTypeChange V w) =
      R x y z w := by
  simp

end TypeChange

/-! ## §1.5.2 Contractions -/

section Contractions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- **Eng.** Expansion `∑ i ⟪x, b i⟫⟪y, b i⟫ = ⟪x, y⟫` in an orthonormal
basis (Parseval, with both inner products in the same orientation). -/
private theorem sum_inner_mul_inner_right {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (x y : V) :
    ∑ i, ⟪x, b i⟫_ℝ * ⟪y, b i⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [← b.sum_inner_mul_inner x y]
  exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (b i) y]

variable (V) in
/-- **Math.** Petersen §1.5.2 (contraction): **contractions are traces of
tensors**. The contraction of a `(0,2)`-tensor `T` first type-changes it to a
`(1,1)`-tensor and then takes the trace:
`C(T) = C(T_{ik} g^{kj} E_k ⊗ σ^j) = T_{ik} g^{ki}`, packaged as the linear
functional `B ↦ tr(♯B)` on bilinear forms. The contraction of a
`(1,1)`-tensor is the plain trace `tr T = T^i_i` (Mathlib's
`LinearMap.trace`); the two agree through type change
(`tensorContraction_lowerIndex`). -/
def tensorContraction : (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.trace ℝ V ∘ₗ (raiseIndex V).toLinearMap

theorem tensorContraction_apply (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    tensorContraction V B = LinearMap.trace ℝ V (raiseIndex V B) :=
  rfl

/-- **Math.** Petersen §1.5.2: contraction commutes with type change — the
contraction of the lowered `(1,1)`-tensor `T` is `tr T = T^i_i`. -/
@[simp]
theorem tensorContraction_lowerIndex (T : V →ₗ[ℝ] V) :
    tensorContraction V (lowerIndex V T) = LinearMap.trace ℝ V T := by
  rw [tensorContraction_apply, raiseIndex_lowerIndex]

/-- **Math.** Petersen §1.5.2: in an orthonormal frame,
`C(T) = T_{ik} g^{ki} = ∑ i, T(E_i, E_i)`. -/
theorem tensorContraction_eq_sum_orthonormal {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    tensorContraction V B = ∑ i, B (b i) (b i) := by
  rw [tensorContraction_apply, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm (raiseIndex V B (b i)) (b i), inner_raiseIndex]

variable (V) in
/-- **Math.** Petersen §1.5.2: the **Ricci tensor of a `(0,4)`-curvature
tensor**, `Ric_{ij} = g^{kl} R_{kijl}` — the contraction of `R` in its first
and last slots. Basis-free: `Ric(v, w)` is the contraction
(`tensorContraction`) of the bilinear form `(u, z) ↦ R(u, v, w, z)`. -/
def ricciOfCurvature (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.compr₂
    ((LinearMap.lflip.toLinearMap ∘ₗ LinearMap.flip R :
      V →ₗ[ℝ] V →ₗ[ℝ] (V →ₗ[ℝ] V →ₗ[ℝ] ℝ)))
    (tensorContraction V)

theorem ricciOfCurvature_apply (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (v w : V) :
    ricciOfCurvature V R v w = tensorContraction V ((R.flip v).flip w) :=
  rfl

/-- **Math.** Petersen §1.5.2 (remark, "the Ricci tensor as a contraction of
curvature"): in an orthonormal frame,
`Ric(v, w) = g^{kl} R_{kvwl} = ∑ i, R(E_i, v, w, E_i)`; the `(1,1)`- and
`(0,2)`-expressions of this contraction agree after type change (the
`(0,2)`-version is `ricciOfCurvature`, the `(1,1)`-version its
`raiseIndex`). -/
theorem ricciAsContraction {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V)
    (R : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : V) :
    ricciOfCurvature V R v w = ∑ i, R (b i) v w (b i) := by
  rw [ricciOfCurvature_apply, tensorContraction_eq_sum_orthonormal b]
  simp

/-- **Math.** Petersen §1.5.2 (scalar curvature): the **scalar curvature** is
the contraction of the (`(1,1)`-type) Ricci tensor:
`scal = tr(Ric) = Ric^i_i`. -/
def scalarCurvatureOfRicci (Ric : V →ₗ[ℝ] V) : ℝ :=
  LinearMap.trace ℝ V Ric

omit [FiniteDimensional ℝ V] in
/-- **Math.** Petersen §1.5.2: `scal = Ric_{ik} g^{ki} = ∑ i, Ric(E_i, E_i)`
in an orthonormal frame. -/
theorem scalarCurvature_eq_sum_orthonormal {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (Ric : V →ₗ[ℝ] V) :
    scalarCurvatureOfRicci Ric = ∑ i, ⟪Ric (b i), b i⟫_ℝ := by
  rw [scalarCurvatureOfRicci, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact real_inner_comm (Ric (b i)) (b i)

/-- **Math.** Petersen §1.5.2: the scalar curvature is the contraction of the
`(0,2)`-type Ricci tensor: `scal = Ric_{ik} g^{ki}`. -/
theorem scalarCurvature_eq_tensorContraction (Ric : V →ₗ[ℝ] V) :
    scalarCurvatureOfRicci Ric = tensorContraction V (lowerIndex V Ric) := by
  rw [tensorContraction_lowerIndex, scalarCurvatureOfRicci]

end Contractions

/-! ## §1.5.3 Inner products of tensors -/

section OperatorNorm

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Math.** Petersen §1.5.3 (operator norm): for a continuous linear map
`L : V → W` between normed spaces, the **operator norm** is
`‖L‖ = sup_{|v| = 1} |L v|` (Mathlib's `ContinuousLinearMap` norm). For a
self-adjoint `L : V → V` with eigenvalues `λ₁ ≤ ⋯ ≤ λₙ` it equals
`max {|λ₁|, |λₙ|}`; the inequality `≥` for every eigenvalue is
`abs_eigenvalue_le_operatorNorm`. -/
def operatorNorm (L : V →L[ℝ] W) : ℝ := ‖L‖

@[simp]
theorem operatorNorm_eq_norm (L : V →L[ℝ] W) : operatorNorm L = ‖L‖ := rfl

/-- **Math.** The defining bound of the operator norm:
`|L v| ≤ ‖L‖ |v|`. -/
theorem norm_apply_le_operatorNorm (L : V →L[ℝ] W) (v : V) :
    ‖L v‖ ≤ operatorNorm L * ‖v‖ :=
  L.le_opNorm v

/-- **Math.** Petersen §1.5.3: every eigenvalue of `L` is bounded by the
operator norm, `|λ| ≤ ‖L‖` (half of the characterization
`‖L‖ = max {|λ₁|, |λₙ|}` for self-adjoint `L`). -/
theorem abs_eigenvalue_le_operatorNorm (L : V →L[ℝ] V) {μ : ℝ} {v : V}
    (hv : v ≠ 0) (h : L v = μ • v) : |μ| ≤ operatorNorm L := by
  have h1 : ‖L v‖ = |μ| * ‖v‖ := by rw [h, norm_smul, Real.norm_eq_abs]
  have h2 : |μ| * ‖v‖ ≤ operatorNorm L * ‖v‖ := by
    rw [← h1]; exact norm_apply_le_operatorNorm L v
  exact le_of_mul_le_mul_right h2 (norm_pos_iff.mpr hv)

end OperatorNorm

section TraceInnerProduct

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- **Math.** Petersen §1.5.3 (Euclidean norm and trace inner product): the
**trace inner product** on linear maps `L₁, L₂ : V → W`,
`⟨L₁, L₂⟩ = tr(L₂^* ∘ L₁) = tr(L₁ ∘ L₂^*)`, where `L₂^* : W → V` is the
adjoint. This — not the operator norm — is the inner product used on tensors
throughout Petersen. -/
def traceInnerProduct (L₁ L₂ : V →ₗ[ℝ] W) : ℝ :=
  LinearMap.trace ℝ V (LinearMap.adjoint L₂ ∘ₗ L₁)

/-- **Math.** In an orthonormal basis of the domain,
`⟨L₁, L₂⟩ = ∑ i ⟪L₁ E_i, L₂ E_i⟫`. -/
theorem traceInnerProduct_eq_sum_inner {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (L₁ L₂ : V →ₗ[ℝ] W) :
    traceInnerProduct L₁ L₂ = ∑ i, ⟪L₁ (b i), L₂ (b i)⟫_ℝ := by
  rw [traceInnerProduct, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  exact real_inner_comm _ _

/-- **Math.** Petersen §1.5.3: `tr(L₂^* ∘ L₁) = tr(L₁ ∘ L₂^*)` — the trace
may be computed on either `V` or `W`. -/
theorem traceInnerProduct_eq_trace_comp_adjoint (L₁ L₂ : V →ₗ[ℝ] W) :
    traceInnerProduct L₁ L₂ = LinearMap.trace ℝ W (L₁ ∘ₗ LinearMap.adjoint L₂) :=
  LinearMap.trace_comp_comm' L₁ (LinearMap.adjoint L₂)

/-- **Math.** Petersen §1.5.3: symmetry, `⟨L₁, L₂⟩ = ⟨L₂, L₁⟩`. -/
theorem traceInnerProduct_comm (L₁ L₂ : V →ₗ[ℝ] W) :
    traceInnerProduct L₁ L₂ = traceInnerProduct L₂ L₁ := by
  rw [traceInnerProduct_eq_sum_inner (stdOrthonormalBasis ℝ V),
    traceInnerProduct_eq_sum_inner (stdOrthonormalBasis ℝ V)]
  exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _

theorem traceInnerProduct_add_left (L₁ L₁' L₂ : V →ₗ[ℝ] W) :
    traceInnerProduct (L₁ + L₁') L₂ =
      traceInnerProduct L₁ L₂ + traceInnerProduct L₁' L₂ := by
  have h : LinearMap.adjoint L₂ ∘ₗ (L₁ + L₁') =
      LinearMap.adjoint L₂ ∘ₗ L₁ + LinearMap.adjoint L₂ ∘ₗ L₁' := by
    ext v; simp
  rw [traceInnerProduct, h, map_add]; rfl

theorem traceInnerProduct_smul_left (c : ℝ) (L₁ L₂ : V →ₗ[ℝ] W) :
    traceInnerProduct (c • L₁) L₂ = c * traceInnerProduct L₁ L₂ := by
  have h : LinearMap.adjoint L₂ ∘ₗ (c • L₁) =
      c • (LinearMap.adjoint L₂ ∘ₗ L₁) := by
    ext v; simp
  rw [traceInnerProduct, h, map_smul]; rfl

/-- **Math.** Positivity: `⟨L, L⟩ = ∑ i |L E_i|² ≥ 0`. -/
theorem traceInnerProduct_self_nonneg (L : V →ₗ[ℝ] W) :
    0 ≤ traceInnerProduct L L := by
  rw [traceInnerProduct_eq_sum_inner (stdOrthonormalBasis ℝ V)]
  exact Finset.sum_nonneg fun i _ => real_inner_self_nonneg

/-- **Math.** Definiteness: `⟨L, L⟩ = 0` iff `L = 0`; together with
symmetry, bilinearity and positivity this makes `traceInnerProduct` an inner
product on `Hom(V, W)`. -/
theorem traceInnerProduct_self_eq_zero (L : V →ₗ[ℝ] W) :
    traceInnerProduct L L = 0 ↔ L = 0 := by
  constructor
  · intro h
    rw [traceInnerProduct_eq_sum_inner (stdOrthonormalBasis ℝ V)] at h
    have h' := (Finset.sum_eq_zero_iff_of_nonneg
      fun i _ => real_inner_self_nonneg (x := L (stdOrthonormalBasis ℝ V i))).mp h
    refine (stdOrthonormalBasis ℝ V).toBasis.ext fun i => ?_
    rw [OrthonormalBasis.coe_toBasis]
    exact inner_self_eq_zero.mp (h' i (Finset.mem_univ i))
  · rintro rfl
    rw [traceInnerProduct_eq_sum_inner (stdOrthonormalBasis ℝ V)]
    simp

/-- **Math.** Petersen §1.5.3 (Euclidean norm): the **Euclidean norm** of a
linear map `L : V → W`, `|L| = √(tr(L^* ∘ L)) = √(tr(L ∘ L^*))`, the norm of
the trace inner product. This norm — not the operator norm — is used for
tensors throughout Petersen. -/
def euclideanNormLinearMap (L : V →ₗ[ℝ] W) : ℝ :=
  Real.sqrt (traceInnerProduct L L)

theorem euclideanNormLinearMap_nonneg (L : V →ₗ[ℝ] W) :
    0 ≤ euclideanNormLinearMap L :=
  Real.sqrt_nonneg _

/-- **Math.** `|L|² = ⟨L, L⟩ = tr(L^* ∘ L)`. -/
theorem sq_euclideanNormLinearMap (L : V →ₗ[ℝ] W) :
    euclideanNormLinearMap L ^ 2 = traceInnerProduct L L :=
  Real.sq_sqrt (traceInnerProduct_self_nonneg L)

/-- **Math.** Petersen §1.5.3: for self-adjoint `L : V → V` with eigenvalues
`λ_i` (with multiplicity), `|L|² = ∑ i λ_i²`. -/
theorem traceInnerProduct_self_eq_sum_eigenvalues_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (hn : Module.finrank ℝ V = n)
    {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric) :
    traceInnerProduct T T = ∑ i, hT.eigenvalues hn i ^ 2 := by
  rw [traceInnerProduct_eq_sum_inner (hT.eigenvectorBasis hn)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT.apply_eigenvectorBasis hn i, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_mul_norm, (hT.eigenvectorBasis hn).orthonormal.1 i]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

end TraceInnerProduct

section TensorNorms

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- **Math.** Petersen Prop. §1.5.3 (Euclidean norm of a `(1,1)`-tensor):
`|T|² = tr(T ∘ T^*)`, which in an orthonormal frame is the sum of the squared
components, `|T|² = ∑_{i,j} (T^j_i)²` with `T^j_i = g(T E_i, E_j)` (Petersen
writes this contraction of `T` against the positional components of `T^*` as
`T^i_j T^j_i`; see `positionalTensorNotation`). -/
theorem euclideanNormOneOneTensor {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (T : V →ₗ[ℝ] V) :
    traceInnerProduct T T = ∑ i, ∑ j, ⟪T (b i), b j⟫_ℝ ^ 2 := by
  rw [traceInnerProduct_eq_sum_inner b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_inner_mul_inner_right b (T (b i)) (T (b i))]
  exact Finset.sum_congr rfl fun j _ => (pow_two _).symm

/-- **Math.** Petersen Prop. §1.5.3 (Euclidean norm of a `(0,2)`-tensor):
type-changing `T = T_{ij} σ^i ⊗ σ^j` to a `(1,1)`-tensor and applying
`euclideanNormOneOneTensor` gives `|T|² = T_{ij} T^{ij}`, which in an
orthonormal frame is `∑_{i,j} T(E_i, E_j)²`. -/
theorem euclideanNormZeroTwoTensor {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    traceInnerProduct (raiseIndex V B) (raiseIndex V B) =
      ∑ i, ∑ j, B (b i) (b j) ^ 2 := by
  rw [euclideanNormOneOneTensor b]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [inner_raiseIndex]

/-- **Math.** Petersen §1.5.3 (pointwise inner product of tensors): the
**pointwise inner product** of two `(0,2)`-tensors, computed by
type-changing to `(1,1)`-tensors and taking the trace inner product. Under
this inner product the coframe products `σ^i ⊗ σ^j` of an orthonormal frame
form an orthonormal basis (`pointwiseTensorInnerProduct_orthonormal`), which
is Petersen's defining declaration; it generalizes `g(X, Y)` for vector
fields.

Design scope: mixed `(s,t)`-tensor powers are not formalized; this covers the
`(0,2)` case (and, through `traceInnerProduct` itself, the `(1,1)` case)
actually used in Petersen Ch. 1–3. -/
def pointwiseTensorInnerProduct (B₁ B₂ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : ℝ :=
  traceInnerProduct (raiseIndex V B₁) (raiseIndex V B₂)

/-- **Math.** In an orthonormal frame,
`⟨B₁, B₂⟩ = ∑_{i,j} B₁(E_i, E_j) B₂(E_i, E_j)`. -/
theorem pointwiseTensorInnerProduct_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (B₁ B₂ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    pointwiseTensorInnerProduct B₁ B₂ =
      ∑ i, ∑ j, B₁ (b i) (b j) * B₂ (b i) (b j) := by
  rw [pointwiseTensorInnerProduct, traceInnerProduct_eq_sum_inner b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_inner_mul_inner_right b (raiseIndex V B₁ (b i)) (raiseIndex V B₂ (b i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_raiseIndex, inner_raiseIndex]

theorem pointwiseTensorInnerProduct_comm (B₁ B₂ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    pointwiseTensorInnerProduct B₁ B₂ = pointwiseTensorInnerProduct B₂ B₁ :=
  traceInnerProduct_comm _ _

theorem pointwiseTensorInnerProduct_self_nonneg (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    0 ≤ pointwiseTensorInnerProduct B B :=
  traceInnerProduct_self_nonneg _

variable (V) in
/-- **Math.** The elementary `(0,2)`-tensor `♭x ⊗ ♭y : (v, w) ↦ ⟪x, v⟫⟪y, w⟫`
(for frame vectors `x = E_i`, `y = E_j` this is the coframe product
`σ^i ⊗ σ^j`). -/
def tensorProdForm (x y : V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  (innerₗ V x).smulRight (innerₗ V y)

omit [FiniteDimensional ℝ V] in
@[simp]
theorem tensorProdForm_apply (x y v w : V) :
    tensorProdForm V x y v w = ⟪x, v⟫_ℝ * ⟪y, w⟫_ℝ := by
  simp [tensorProdForm]

/-- **Math.** The pointwise inner product of elementary `(0,2)`-tensors:
`⟨♭x ⊗ ♭y, ♭z ⊗ ♭w⟩ = ⟪x, z⟫ ⟪y, w⟫`. -/
theorem pointwiseTensorInnerProduct_tensorProdForm (x y z w : V) :
    pointwiseTensorInnerProduct (tensorProdForm V x y) (tensorProdForm V z w) =
      ⟪x, z⟫_ℝ * ⟪y, w⟫_ℝ := by
  rw [pointwiseTensorInnerProduct_eq_sum (stdOrthonormalBasis ℝ V)]
  have h : ∀ p q : Fin (Module.finrank ℝ V),
      tensorProdForm V x y (stdOrthonormalBasis ℝ V p) (stdOrthonormalBasis ℝ V q) *
        tensorProdForm V z w (stdOrthonormalBasis ℝ V p) (stdOrthonormalBasis ℝ V q) =
      (⟪x, stdOrthonormalBasis ℝ V p⟫_ℝ * ⟪z, stdOrthonormalBasis ℝ V p⟫_ℝ) *
        (⟪y, stdOrthonormalBasis ℝ V q⟫_ℝ * ⟪w, stdOrthonormalBasis ℝ V q⟫_ℝ) := by
    intro p q
    rw [tensorProdForm_apply, tensorProdForm_apply]
    ring
  simp_rw [h]
  rw [← Fintype.sum_mul_sum, sum_inner_mul_inner_right (stdOrthonormalBasis ℝ V) x z,
    sum_inner_mul_inner_right (stdOrthonormalBasis ℝ V) y w]

/-- **Math.** Petersen §1.5.3: for an orthonormal frame `E_i` with coframe
`σ^i`, the tensors `σ^i ⊗ σ^j` are **orthonormal** for the pointwise inner
product — Petersen's defining declaration for the inner product on
`(s,t)`-tensors, here for type `(0,2)`. -/
theorem pointwiseTensorInnerProduct_orthonormal {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : OrthonormalBasis ι ℝ V) (i j k l : ι) :
    pointwiseTensorInnerProduct
        (tensorProdForm V (b i) (b j)) (tensorProdForm V (b k) (b l)) =
      (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0) := by
  rw [pointwiseTensorInnerProduct_tensorProdForm,
    orthonormal_iff_ite.mp b.orthonormal i k, orthonormal_iff_ite.mp b.orthonormal j l]

end TensorNorms

/-! ## The `L²` inner product of tensor fields -/

section L2

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Petersen §1.5.3 (`L²` inner product of tensors): integrating the
pointwise inner product of two `(0,2)`-tensor fields on a Riemannian manifold
against the volume form gives the `L²` inner product
`(T₁, T₂) = ∫_M g(T₁, T₂) vol`.

The pointwise inner products on the fibres `T_xM` are induced by the metric
of `[HasMetric I M]`. The definition is stated against an arbitrary measure
`μ`; taking `μ` to be the Riemannian volume measure of `g` recovers
Petersen's definition. On non-integrable pairs the Bochner integral is `0`
by convention; Petersen restricts to compactly supported tensors, for which
integrability holds when the fields are continuous. -/
-- TODO(PET.1): the Riemannian volume form/measure of an oriented Riemannian
-- manifold (blueprint node def:pet-ch1-volume-form-oriented) is not yet
-- formalized; once available, specialize `μ` to it.
def l2TensorInnerProduct [HasMetric I M] [MeasurableSpace M] (μ : Measure M)
    (B₁ B₂ : ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) : ℝ :=
  ∫ x, pointwiseTensorInnerProduct (B₁ x) (B₂ x) ∂μ

end L2

/-! ## §1.5.4 Positional notation -/

section PositionalNotation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- **Math.** Petersen §1.5.4 (positional index notation): the frame notation
for a section of `TM ⊗ T*M` and one of `T*M ⊗ TM` can look identical, so
Petersen writes indices *positionally*. The standard `(1,1)`-tensor is
`T = T^i_j E_i ⊗ σ^j`, while its adjoint, a section of `T*M ⊗ TM` written
positionally as `T^* = T^l_k σ^k ⊗ E_l`, has components the transpose of
those of `T` in an orthonormal frame:
`(T^*)^j_i = g(T^* E_i, E_j) = g(E_i, T E_j)` (first conjunct). Contracting
the components of `T` against those of `T^*` recovers the Euclidean norm,
`|T|² = T^i_j T^j_i` in Petersen's positional notation (second conjunct),
as in `euclideanNormOneOneTensor`. -/
theorem positionalTensorNotation {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (T : V →ₗ[ℝ] V) :
    (∀ i j, ⟪LinearMap.adjoint T (b i), b j⟫_ℝ = ⟪b i, T (b j)⟫_ℝ) ∧
      traceInnerProduct T T =
        ∑ i, ∑ j, ⟪T (b j), b i⟫_ℝ * ⟪LinearMap.adjoint T (b i), b j⟫_ℝ := by
  have hadj : ∀ i j, ⟪LinearMap.adjoint T (b i), b j⟫_ℝ = ⟪b i, T (b j)⟫_ℝ :=
    fun i j => T.adjoint_inner_left (b j) (b i)
  refine ⟨hadj, ?_⟩
  rw [euclideanNormOneOneTensor b T, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hadj i j, real_inner_comm (b i) (T (b j)), pow_two]

end PositionalNotation

end PetersenLib

end
