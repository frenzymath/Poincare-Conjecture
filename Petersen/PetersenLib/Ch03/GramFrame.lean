import PetersenLib.Ch03.CurvatureCovariantDerivativeFour
import PetersenLib.Ch03.RicciSectional
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Petersen Ch. 3, §3.1.5 — Gram frames and smoothness of traces

Infrastructure for differentiating traces of curvature (the contracted Bianchi
identity, Prop. 3.1.5). A **Gram frame** at `p` is the family of global smooth
extensions `Eᵢ = extendTangentVector p (eᵢ)` of a `g`-orthonormal basis of
`T_pM`; its Gram matrix `G(q)ᵢⱼ = g(Eᵢ, Eⱼ)(q)` is smooth, equals `1` at `p`,
and stays invertible near `p`, so Cramer's rule `G⁻¹ = det⁻¹ · adjugate`
expresses the inverse entries as smooth functions near `p`.

The payoff is the **Gram-inverse trace formula** (`trace_eq_sum_gramInv`):
`tr S = ∑ᵢⱼ (G⁻¹)ᵢⱼ · g(S(vᵢ), vⱼ)` for any endomorphism and any family with
invertible Gram matrix, which converts the Ricci and scalar curvatures into
visibly-smooth local expressions:

* `ricciCurvature_eval_eventually_eq` / `contMDiff_ricciCurvature_eval` —
  `q ↦ Ric(X,Y)(q)` is smooth;
* `scalarCurvature_eventually_eq` / `contMDiff_scalarCurvature` —
  `q ↦ scal(q)` is smooth.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.5.
-/

open Bundle Set Function Finset Filter
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ## Cramer inverse -/

section CramerInverse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Cramer-rule inverse `det⁻¹ • adjugate` of a square real matrix
(defined for every matrix; the actual inverse when `det ≠ 0`). -/
def cramerInverse (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  A.det⁻¹ • A.adjugate

theorem cramerInverse_apply (A : Matrix ι ι ℝ) (i j : ι) :
    cramerInverse A i j = A.det⁻¹ * A.adjugate i j := rfl

theorem cramerInverse_mul {A : Matrix ι ι ℝ} (h : A.det ≠ 0) :
    cramerInverse A * A = 1 := by
  rw [cramerInverse, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul,
    inv_mul_cancel₀ h, one_smul]

theorem mul_cramerInverse {A : Matrix ι ι ℝ} (h : A.det ≠ 0) :
    A * cramerInverse A = 1 := by
  rw [cramerInverse, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul,
    inv_mul_cancel₀ h, one_smul]

@[simp]
theorem cramerInverse_one : cramerInverse (1 : Matrix ι ι ℝ) = 1 := by
  rw [cramerInverse, Matrix.det_one, Matrix.adjugate_one, inv_one, one_smul]

end CramerInverse

/-! ## Traces through a Gram-invertible family -/

section GramTrace

variable {g : RiemannianMetric I M}

/-- The Gram matrix of a family of tangent vectors at `p`. -/
def gramMatrix (g : RiemannianMetric I M) (p : M)
    (v : Fin (Module.finrank ℝ E) → TangentSpace I p) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j => g.metricInner p (v i) (v j)

theorem gramMatrix_apply (p : M)
    (v : Fin (Module.finrank ℝ E) → TangentSpace I p) (i j) :
    gramMatrix g p v i j = g.metricInner p (v i) (v j) := rfl

theorem gramMatrix_symm (p : M)
    (v : Fin (Module.finrank ℝ E) → TangentSpace I p) (i j) :
    gramMatrix g p v i j = gramMatrix g p v j i :=
  g.metricInner_comm ..

/-- A family with invertible Gram matrix is linearly independent. -/
theorem linearIndependent_of_gramMatrix_det_ne_zero (p : M)
    {v : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (h : (gramMatrix g p v).det ≠ 0) : LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- pairing the vanishing combination against each `v k` gives `G.mulVec c = 0`
  have hpair : ∀ k, ∑ j, gramMatrix g p v k j * c j = 0 := by
    intro k
    calc ∑ j, gramMatrix g p v k j * c j
        = ∑ j, c j * g.metricInner p (v j) (v k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [gramMatrix_apply, g.metricInner_comm p (v k) (v j)]
          ring
      _ = g.metricInner p (∑ j, c j • v j) (v k) :=
          (metricInner_sum_smul_left g p Finset.univ c v (v k)).symm
      _ = 0 := by rw [hc, g.metricInner_zero_left]
  -- multiply by the Cramer inverse
  intro i
  have hCI := cramerInverse_mul (A := gramMatrix g p v) h
  calc c i = ∑ k, (1 : Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ) i k * c k := by
        simp [Matrix.one_apply]
    _ = ∑ k, (∑ j, cramerInverse (gramMatrix g p v) i j
          * gramMatrix g p v j k) * c k := by
        rw [← hCI]
        exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_apply]
    _ = ∑ k, ∑ j, cramerInverse (gramMatrix g p v) i j
          * gramMatrix g p v j k * c k :=
        Finset.sum_congr rfl fun k _ => Finset.sum_mul ..
    _ = ∑ j, ∑ k, cramerInverse (gramMatrix g p v) i j
          * gramMatrix g p v j k * c k := Finset.sum_comm
    _ = ∑ j, cramerInverse (gramMatrix g p v) i j
          * ∑ k, gramMatrix g p v j k * c k := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hpair j, mul_zero]

/-- Coordinates through the Gram inverse: for a family `v` with invertible
Gram matrix `G` (hence a basis `b` with `⇑b = v`), the `b`-coordinates of any
vector are `(repr x)ᵢ = ∑ⱼ (G⁻¹)ᵢⱼ · g(x, vⱼ)`. -/
theorem gram_basis_repr_eq (p : M)
    {v : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (h : (gramMatrix g p v).det ≠ 0)
    {b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p)}
    (hb : ⇑b = v) (x : TangentSpace I p) (i : Fin (Module.finrank ℝ E)) :
    b.repr x i
      = ∑ j, cramerInverse (gramMatrix g p v) i j * g.metricInner p x (v j) := by
  -- pairing `x = ∑ cᵢ vᵢ` against `v k`
  have hpair : ∀ k, g.metricInner p x (v k)
      = ∑ l, b.repr x l * gramMatrix g p v l k := by
    intro k
    conv_lhs => rw [← b.sum_repr x]
    rw [hb, metricInner_sum_smul_left g p Finset.univ _ v (v k)]
    rfl
  have hCI := cramerInverse_mul (A := gramMatrix g p v) h
  calc b.repr x i
      = ∑ l, (1 : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) i l * b.repr x l := by
        simp [Matrix.one_apply]
    _ = ∑ l, (∑ j, cramerInverse (gramMatrix g p v) i j
          * gramMatrix g p v j l) * b.repr x l := by
        rw [← hCI]
        exact Finset.sum_congr rfl fun l _ => by rw [Matrix.mul_apply]
    _ = ∑ l, ∑ j, cramerInverse (gramMatrix g p v) i j
          * gramMatrix g p v j l * b.repr x l :=
        Finset.sum_congr rfl fun l _ => Finset.sum_mul ..
    _ = ∑ j, ∑ l, cramerInverse (gramMatrix g p v) i j
          * gramMatrix g p v j l * b.repr x l := Finset.sum_comm
    _ = ∑ j, cramerInverse (gramMatrix g p v) i j
          * ∑ l, b.repr x l * gramMatrix g p v l j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [gramMatrix_symm p v j l]
        ring
    _ = ∑ j, cramerInverse (gramMatrix g p v) i j * g.metricInner p x (v j) :=
        Finset.sum_congr rfl fun j _ => by rw [← hpair j]

/-- **Gram-inverse trace formula**: for any endomorphism `S` of `T_pM` and any
family `v` with invertible Gram matrix `G`,
`tr S = ∑ᵢⱼ (G⁻¹)ᵢⱼ · g(S(vᵢ), vⱼ)`. -/
theorem trace_eq_sum_gramInv (p : M)
    {v : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (h : (gramMatrix g p v).det ≠ 0)
    (S : Module.End ℝ (TangentSpace I p)) :
    LinearMap.trace ℝ (TangentSpace I p) S
      = ∑ i, ∑ j, cramerInverse (gramMatrix g p v) i j
          * g.metricInner p (S (v i)) (v j) := by
  have hli : LinearIndependent ℝ v :=
    linearIndependent_of_gramMatrix_det_ne_zero p h
  have hcard : Fintype.card (Fin (Module.finrank ℝ E))
      = Module.finrank ℝ (TangentSpace I p) := by
    rw [Fintype.card_fin]
    rfl
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := gram_basis_repr_eq p h hb (S (b i)) i
  rw [hb] at this ⊢
  exact this

end GramTrace

/-! ## Smoothness of matrix functions built from smooth entries -/

section MatrixSmoothness

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant of a matrix of smooth functions is smooth. -/
theorem contMDiff_matrix_det {A : M → Matrix ι ι ℝ}
    (hA : ∀ i j, ContMDiff I 𝓘(ℝ) ∞ (fun q => A q i j)) :
    ContMDiff I 𝓘(ℝ) ∞ (fun q => (A q).det) := by
  have e : (fun q => (A q).det)
      = fun q => ∑ σ : Equiv.Perm ι,
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A q (σ i) i := by
    funext q
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [e]
  refine contMDiff_finset_sum fun σ _ => ?_
  exact (contMDiff_const).mul (contMDiff_finset_prod fun i _ => hA (σ i) i)

/-- Entries of the adjugate of a matrix of smooth functions are smooth. -/
theorem contMDiff_matrix_adjugate {A : M → Matrix ι ι ℝ}
    (hA : ∀ i j, ContMDiff I 𝓘(ℝ) ∞ (fun q => A q i j)) (i j : ι) :
    ContMDiff I 𝓘(ℝ) ∞ (fun q => (A q).adjugate i j) := by
  have e : (fun q => (A q).adjugate i j)
      = fun q => ((A q).updateRow j (Pi.single i 1)).det := by
    funext q
    rw [Matrix.adjugate_apply]
  rw [e]
  refine contMDiff_matrix_det fun k l => ?_
  rcases eq_or_ne k j with hk | hk
  · subst hk
    have e' : (fun q => (A q).updateRow k (Pi.single i 1) k l)
        = fun _ => (Pi.single i 1 : ι → ℝ) l := by
      funext q
      rw [Matrix.updateRow_self]
    rw [e']
    exact contMDiff_const
  · have e' : (fun q => (A q).updateRow j (Pi.single i 1) k l)
        = fun q => A q k l := by
      funext q
      rw [Matrix.updateRow_ne hk]
    rw [e']
    exact hA k l

/-- Entries of the Cramer inverse of a matrix of smooth functions are smooth
at every point where the determinant does not vanish. -/
theorem contMDiffAt_matrix_cramerInverse {A : M → Matrix ι ι ℝ}
    (hA : ∀ i j, ContMDiff I 𝓘(ℝ) ∞ (fun q => A q i j)) {p : M}
    (hdet : (A p).det ≠ 0) (i j : ι) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun q => cramerInverse (A q) i j) p := by
  have e : (fun q => cramerInverse (A q) i j)
      = fun q => ((A q).det)⁻¹ * (A q).adjugate i j := by
    funext q
    rw [cramerInverse_apply]
  rw [e]
  exact (((contMDiff_matrix_det hA) p).inv₀ hdet).mul
    ((contMDiff_matrix_adjugate hA i j) p)

end MatrixSmoothness

/-! ## The Gram matrix field of a family of vector fields -/

section GramField

variable (g : RiemannianMetric I M)

/-- The Gram matrix field of a family of vector fields:
`(gramMatrixField g F q)ᵢⱼ = g(Fᵢ, Fⱼ)(q)`. -/
def gramMatrixField (F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x)
    (q : M) : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  gramMatrix g q (fun i => F i q)

theorem gramMatrixField_apply
    (F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x) (q : M) (i j) :
    gramMatrixField g F q i j = g.metricInner q (F i q) (F j q) := rfl

variable {g}

/-- Entries of the Gram matrix field of smooth vector fields are smooth. -/
theorem contMDiff_gramMatrixField_entry
    {F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hF : ∀ i, IsSmoothVectorField (F i)) (i j) :
    ContMDiff I 𝓘(ℝ) ∞ (fun q => gramMatrixField g F q i j) := by
  have h := (metricOperator_isTensorOperator g).smooth_eval ![F i, F j]
    (by
      intro k
      fin_cases k
      · simpa using hF i
      · simpa using hF j)
  have e : (metricOperator g ![F i, F j] : M → ℝ)
      = fun q => gramMatrixField g F q i j := by
    funext q
    simp [metricOperator, gramMatrixField_apply]
  rwa [e] at h

/-- The Gram determinant of smooth fields is a smooth function. -/
theorem contMDiff_gramMatrixField_det
    {F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hF : ∀ i, IsSmoothVectorField (F i)) :
    ContMDiff I 𝓘(ℝ) ∞ (fun q => (gramMatrixField g F q).det) :=
  contMDiff_matrix_det fun i j => contMDiff_gramMatrixField_entry hF i j

/-- If the fields are orthonormal at `p`, the Gram matrix field is `1` there. -/
theorem gramMatrixField_eq_one_of_orthonormal
    {F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x} {p : M}
    (horth : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0) :
    gramMatrixField g F p = 1 := by
  ext i j
  rw [gramMatrixField_apply, horth i j, Matrix.one_apply]

/-- Near a point where smooth fields are orthonormal, the Gram determinant
does not vanish. -/
theorem gramMatrixField_det_ne_zero_eventually
    {F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hF : ∀ i, IsSmoothVectorField (F i)) {p : M}
    (horth : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0) :
    ∀ᶠ q in 𝓝 p, (gramMatrixField g F q).det ≠ 0 := by
  have hdet1 : (gramMatrixField g F p).det = 1 := by
    rw [gramMatrixField_eq_one_of_orthonormal horth, Matrix.det_one]
  have hcont : ContinuousAt (fun q => (gramMatrixField g F q).det) p :=
    (contMDiff_gramMatrixField_det (g := g) hF).continuous.continuousAt
  exact hcont.eventually_ne (by rw [hdet1]; exact one_ne_zero)

end GramField

/-! ## Local Gram-inverse expressions for the Ricci and scalar curvatures -/

section CurvatureSmoothness

variable {g : RiemannianMetric I M}

/-- Local Gram-inverse expression for the Ricci curvature: wherever the Gram
determinant of a smooth frame does not vanish,
`Ric(X,Y) = ∑ᵢⱼ (G⁻¹)ᵢⱼ · R⁴(Fᵢ, X, Y, Fⱼ)`. -/
theorem ricciCurvature_eval_eq_sum_gramInv (D : RiemannianConnection I g)
    {F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hF : ∀ i, IsSmoothVectorField (F i))
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) {q : M}
    (hdet : (gramMatrixField g F q).det ≠ 0) :
    RicciCurvature D.toAffineConnection q (X q) (Y q)
      = ∑ i, ∑ j, cramerInverse (gramMatrixField g F q) i j
          * curvatureTensorFour D (F i) X Y (F j) q := by
  have htr := trace_eq_sum_gramInv (g := g) q hdet
    (curvatureTensorAtFirstLinear D.toAffineConnection q (X q) (Y q))
  rw [RicciCurvature, htr]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have : g.metricInner q
      (curvatureTensorAtFirstLinear D.toAffineConnection q (X q) (Y q) (F i q))
      (F j q) = curvatureTensorFourAt D q (F i q) (X q) (Y q) (F j q) := rfl
  rw [this, curvatureTensorFourAt_apply D (hF i) hX hY q]

/-- `q ↦ Ric(X,Y)(q)` is smooth for smooth `X`, `Y`. -/
theorem contMDiff_ricciCurvature_eval (D : RiemannianConnection I g)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) :
    ContMDiff I 𝓘(ℝ) ∞
      (fun q => RicciCurvature D.toAffineConnection q (X q) (Y q)) := by
  intro p
  -- a frame orthonormal at `p`: extend the standard orthonormal basis
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  set F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x :=
    fun i => ⇑(extendTangentVector p (e i)) with hFdef
  have hF : ∀ i, IsSmoothVectorField (F i) :=
    fun i => (extendTangentVector p (e i)).smooth
  have horth : ∀ i j, g.metricInner p (F i p) (F j p)
      = if i = j then 1 else 0 := by
    intro i j
    have h1 := orthonormal_iff_ite.mp e.orthonormal i j
    simp only [hFdef, extendTangentVector_apply]
    exact h1
  have hev := gramMatrixField_det_ne_zero_eventually hF horth
  -- the smooth local model
  have hsm : ContMDiffAt I 𝓘(ℝ) ∞
      (fun q => ∑ i, ∑ j, cramerInverse (gramMatrixField g F q) i j
        * curvatureTensorFour D (F i) X Y (F j) q) p := by
    have hdet1 : (gramMatrixField g F p).det ≠ 0 := by
      rw [gramMatrixField_eq_one_of_orthonormal horth, Matrix.det_one]
      exact one_ne_zero
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (contMDiffAt_matrix_cramerInverse
        (fun a b => contMDiff_gramMatrixField_entry hF a b) hdet1 i j).mul
      ((contMDiff_curvatureTensorFour D (hF i) hX hY (hF j)) p)
  refine (hsm.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hev] with q hq
  exact ricciCurvature_eval_eq_sum_gramInv D hF hX hY hq

/-- Local Gram-inverse expression for the scalar curvature: wherever the Gram
determinant of a smooth frame does not vanish,
`scal = ∑ᵢⱼ (G⁻¹)ᵢⱼ · Ric(Fᵢ, Fⱼ)`. -/
theorem scalarCurvature_eq_sum_gramInv (D : RiemannianConnection I g)
    {F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x} {q : M}
    (hdet : (gramMatrixField g F q).det ≠ 0) :
    scalarCurvature D q
      = ∑ i, ∑ j, cramerInverse (gramMatrixField g F q) i j
          * RicciCurvature D.toAffineConnection q (F i q) (F j q) := by
  have htr := trace_eq_sum_gramInv (g := g) q hdet (ricciEndomorphismLinear D q)
  rw [scalarCurvature, htr]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact metricInner_ricciEndomorphism D q (F i q) (F j q)

/-- The scalar curvature is a smooth function on `M`. -/
theorem contMDiff_scalarCurvature (D : RiemannianConnection I g) :
    ContMDiff I 𝓘(ℝ) ∞ (scalarCurvature D) := by
  intro p
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  set F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x :=
    fun i => ⇑(extendTangentVector p (e i)) with hFdef
  have hF : ∀ i, IsSmoothVectorField (F i) :=
    fun i => (extendTangentVector p (e i)).smooth
  have horth : ∀ i j, g.metricInner p (F i p) (F j p)
      = if i = j then 1 else 0 := by
    intro i j
    have h1 := orthonormal_iff_ite.mp e.orthonormal i j
    simp only [hFdef, extendTangentVector_apply]
    exact h1
  have hev := gramMatrixField_det_ne_zero_eventually hF horth
  have hsm : ContMDiffAt I 𝓘(ℝ) ∞
      (fun q => ∑ i, ∑ j, cramerInverse (gramMatrixField g F q) i j
        * RicciCurvature D.toAffineConnection q (F i q) (F j q)) p := by
    have hdet1 : (gramMatrixField g F p).det ≠ 0 := by
      rw [gramMatrixField_eq_one_of_orthonormal horth, Matrix.det_one]
      exact one_ne_zero
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (contMDiffAt_matrix_cramerInverse
        (fun a b => contMDiff_gramMatrixField_entry hF a b) hdet1 i j).mul
      ((contMDiff_ricciCurvature_eval D (hF i) (hF j)) p)
  refine (hsm.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hev] with q hq
  exact scalarCurvature_eq_sum_gramInv D hq

end CurvatureSmoothness

end PetersenLib
