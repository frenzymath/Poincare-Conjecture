import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Han--Lin Chapter 2: the interior maximum test

This file proves the pointwise second-derivative test for a general
nondivergence-form uniformly elliptic operator. The coefficient matrix need
not be symmetric: its symmetric part has the same contraction with a Hessian.
-/

open Filter InnerProductSpace Set Topology
open scoped ContDiff MatrixOrder RealInnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch02

abbrev Euclidean (n : Nat) := EuclideanSpace Real (Fin n)

private lemma deriv_deriv_nonpos_of_isLocalMax {g : Real -> Real} {a : Real}
    (h : IsLocalMax g a) (hg : ContinuousAt g a) :
    deriv (deriv g) a <= 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hmin : IsLocalMin g a :=
    isLocalMin_of_deriv_deriv_pos hpos h.deriv_eq_zero hg
  have hconst : g =ᶠ[nhds a] fun _ => g a := by
    filter_upwards [h, hmin] with s h1 h2
    exact le_antisymm h1 h2
  have h2 : deriv (deriv g) a = deriv (deriv fun _ => g a) a :=
    hconst.deriv.deriv_eq
  rw [h2] at hpos
  simp [deriv_const'] at hpos

/-- The Hessian is nonpositive in every direction at a local maximum. -/
lemma secondDirectional_nonpos_of_isLocalMax
    {n : Nat} {u : Euclidean n -> Real} {p : Euclidean n}
    (hu : ContDiffAt Real 2 u p) (hmax : IsLocalMax u p) (v : Euclidean n) :
    fderiv Real (fderiv Real u) p v v <= 0 := by
  let g : Real -> Real := fun s => u (p + s • v)
  have hA : Continuous fun s : Real => p + s • v := by fun_prop
  have hA0 : p + (0 : Real) • v = p := by simp
  have hAcont : ContinuousAt (fun s : Real => p + s • v) 0 := hA.continuousAt
  have hline_tendsto : Tendsto (fun s : Real => p + s • v) (nhds 0) (nhds p) := by
    have hAt := hAcont
    change Tendsto (fun s : Real => p + s • v) (nhds 0)
      (nhds (p + (0 : Real) • v)) at hAt
    rw [hA0] at hAt
    exact hAt
  have hev : ∀ᶠ s in nhds (0 : Real), ContDiffAt Real 2 u (p + s • v) :=
    hline_tendsto.eventually (hu.eventually (by simp))
  have hderiv_g : deriv g =ᶠ[nhds (0 : Real)]
      fun s => fderiv Real u (p + s • v) v := by
    filter_upwards [hev] with s hs
    have hline : HasDerivAt (fun t : Real => p + t • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add p
    exact (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s hline |>.deriv
  have hF : HasDerivAt (fun s : Real => fderiv Real u (p + s • v) v)
      (fderiv Real (fderiv Real u) p v v) 0 := by
    have hline : HasDerivAt (fun s : Real => p + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : Real)).smul_const v).const_add p
    have hFd : DifferentiableAt Real (fderiv Real u) p :=
      (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have hFd' : HasFDerivAt (fderiv Real u) (fderiv Real (fderiv Real u) p)
        (p + (0 : Real) • v) := by
      rw [hA0]
      exact hFd.hasFDerivAt
    have hcomp : HasDerivAt (fun s : Real => fderiv Real u (p + s • v))
        (fderiv Real (fderiv Real u) p v) 0 := hFd'.comp_hasDerivAt 0 hline
    simpa using hcomp.clm_apply (hasDerivAt_const (0 : Real) v)
  have hgg : deriv (deriv g) 0 = fderiv Real (fderiv Real u) p v v := by
    rw [hderiv_g.deriv_eq]
    exact hF.deriv
  have hgmax : IsLocalMax g 0 := by
    have hm := hline_tendsto.eventually hmax
    filter_upwards [hm] with s hs
    simpa [g] using hs
  have hgcont : ContinuousAt g 0 := by
    have hup : ContinuousAt u p := hu.continuousAt
    have hc := hup.comp_of_eq hAcont hA0
    simpa [g, Function.comp_def] using hc
  have hnonpos := deriv_deriv_nonpos_of_isLocalMax hgmax hgcont
  rwa [hgg] at hnonpos

/-- The second Frechet derivative, regarded as an algebraic bilinear form. -/
def secondDerivativeBilin {n : Nat} (u : Euclidean n -> Real) (p : Euclidean n) :
    LinearMap.BilinForm Real (Euclidean n) :=
  (ContinuousLinearMap.coeLM Real).comp
    (fderiv Real (fderiv Real u) p).toLinearMap

/-- The Hessian matrix in the standard orthonormal basis of `Real^n`. -/
def hessianMatrix {n : Nat} (u : Euclidean n -> Real) (p : Euclidean n) :
    Matrix (Fin n) (Fin n) Real :=
  LinearMap.BilinForm.toMatrix (EuclideanSpace.basisFun (Fin n) Real).toBasis
    (secondDerivativeBilin u p)

lemma hessianMatrix_isHermitian {n : Nat} {u : Euclidean n -> Real} {p : Euclidean n}
    (hu : ContDiffAt Real 2 u p) : (hessianMatrix u p).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro i j
  simp only [hessianMatrix, LinearMap.BilinForm.toMatrix_apply, secondDerivativeBilin]
  exact (hu.isSymmSndFDerivAt (by norm_num) _ _).symm

lemma neg_hessianMatrix_posSemidef {n : Nat} {u : Euclidean n -> Real} {p : Euclidean n}
    (hu : ContDiffAt Real 2 u p) (hmax : IsLocalMax u p) :
    (-hessianMatrix u p).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hessianMatrix_isHermitian hu).neg
  intro x
  simp only [star_trivial]
  let b := (EuclideanSpace.basisFun (Fin n) Real).toBasis
  let v := b.equivFun.symm x
  have hdir := secondDirectional_nonpos_of_isLocalMax hu hmax v
  have heq :
      x ⬝ᵥ ((hessianMatrix u p).mulVec x) = secondDerivativeBilin u p v v := by
    exact LinearMap.BilinForm.dotProduct_toMatrix_mulVec b
      (secondDerivativeBilin u p) x x
  have hneg :
      x ⬝ᵥ ((-hessianMatrix u p).mulVec x) =
        -(x ⬝ᵥ ((hessianMatrix u p).mulVec x)) := by
    rw [Matrix.neg_mulVec, dotProduct_neg]
  rw [hneg, heq]
  exact neg_nonneg.mpr hdir

/-- The symmetric part of a real square matrix. -/
def symmetrize {n : Type*} (A : Matrix n n Real) : Matrix n n Real :=
  (2 : Real)⁻¹ • (A + A.transpose)

/-- The coordinate form of uniform ellipticity at one point. -/
def UniformlyElliptic {n : Type*} [Fintype n]
    (A : Matrix n n Real) (lambda : Real) : Prop :=
  forall xi : n -> Real,
    lambda * (∑ i, (xi i) ^ 2) <= xi ⬝ᵥ (A.mulVec xi)

lemma symmetrize_isHermitian {n : Type*} (A : Matrix n n Real) :
    (symmetrize A).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro i j
  simp [symmetrize, add_comm]

lemma dotProduct_symmetrize_mulVec {n : Type*} [Fintype n]
    (A : Matrix n n Real) (x : n -> Real) :
    x ⬝ᵥ ((symmetrize A).mulVec x) = x ⬝ᵥ (A.mulVec x) := by
  rw [show symmetrize A = (2 : Real)⁻¹ • (A + A.transpose) by rfl,
    Matrix.smul_mulVec, Matrix.add_mulVec]
  simp only [dotProduct, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have hswap :
      (∑ i, x i * (A.transpose.mulVec x) i) =
        ∑ i, x i * (A.mulVec x) i := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    ring
  calc
    (∑ i, x i * (2⁻¹ * ((A.mulVec x) i + (A.transpose.mulVec x) i))) =
        ∑ i, (2⁻¹ * (x i * (A.mulVec x) i) +
          2⁻¹ * (x i * (A.transpose.mulVec x) i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = 2⁻¹ * (∑ i, x i * (A.mulVec x) i) +
        2⁻¹ * (∑ i, x i * (A.transpose.mulVec x) i) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ i, x i * (A.mulVec x) i := by rw [hswap]; ring

lemma symmetrize_posSemidef_of_uniformlyElliptic {n : Type*} [Fintype n]
    (A : Matrix n n Real) {lambda : Real} (hlambda : 0 <= lambda)
    (hA : UniformlyElliptic A lambda) :
    (symmetrize A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (symmetrize_isHermitian A)
  intro x
  simp only [star_trivial]
  rw [dotProduct_symmetrize_mulVec]
  exact (mul_nonneg hlambda (Finset.sum_nonneg fun i _ => sq_nonneg (x i))).trans (hA x)

lemma trace_symmetrize_mul_of_isHermitian {n : Type*} [Fintype n]
    (A H : Matrix n n Real) (hH : H.IsHermitian) :
    (symmetrize A * H).trace = (A * H).trace := by
  have hHt : H.transpose = H :=
    Matrix.isHermitian_iff_isSymm.mp hH
  have htrans : (A.transpose * H).trace = (A * H).trace := by
    calc
      (A.transpose * H).trace = ((A.transpose * H).transpose).trace :=
        (Matrix.trace_transpose _).symm
      _ = (H.transpose * A).trace := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = (H * A).trace := by rw [hHt]
      _ = (A * H).trace := Matrix.trace_mul_comm H A
  simp [symmetrize, add_mul, htrans]
  ring

lemma trace_mul_nonneg_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n Real} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 <= (A * B).trace := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hsq : S * S = A := by
    simpa [pow_two] using (CFC.sq_sqrt A hA.nonneg)
  have hcong : (Matrix.conjTranspose S * B * S).PosSemidef :=
    hB.conjTranspose_mul_mul_same S
  have hsadj : Matrix.conjTranspose S = S := hS.isHermitian
  calc
    0 <= (Matrix.conjTranspose S * B * S).trace := hcong.trace_nonneg
    _ = ((S * B) * S).trace := by rw [hsadj]
    _ = (S * (S * B)).trace := (Matrix.trace_mul_comm S (S * B)).symm
    _ = ((S * S) * B).trace := by rw [mul_assoc]
    _ = (A * B).trace := by rw [hsq]

lemma trace_hessian_nonpos_of_uniformlyElliptic
    {n : Nat} {u : Euclidean n -> Real} {p : Euclidean n}
    (A : Matrix (Fin n) (Fin n) Real) {lambda : Real}
    (hlambda : 0 <= lambda) (hA : UniformlyElliptic A lambda)
    (hu : ContDiffAt Real 2 u p) (hmax : IsLocalMax u p) :
    (A * hessianMatrix u p).trace <= 0 := by
  have hH := neg_hessianMatrix_posSemidef hu hmax
  have hnonneg := trace_mul_nonneg_of_posSemidef
    (symmetrize_posSemidef_of_uniformlyElliptic A hlambda hA) hH
  rw [trace_symmetrize_mul_of_isHermitian A (-hessianMatrix u p) hH.isHermitian]
    at hnonneg
  simpa [mul_neg] using hnonneg

/-- A general nondivergence-form linear second-order operator on `Real^n`. -/
def nondivergenceOperator {n : Nat}
    (a : Euclidean n -> Matrix (Fin n) (Fin n) Real)
    (b : Euclidean n -> Fin n -> Real) (c : Euclidean n -> Real)
    (u : Euclidean n -> Real) (x : Euclidean n) : Real :=
  (a x * hessianMatrix u x).trace +
    ∑ i, b x i * fderiv Real u x (EuclideanSpace.basisFun (Fin n) Real i) +
    c x * u x

lemma fderiv_apply_eq_fderiv_fderiv
    {n : Nat} {u : Euclidean n -> Real} {p v w : Euclidean n}
    (hu : ContDiffAt Real 2 u p) :
    fderiv Real (fun y => fderiv Real u y v) p w =
      fderiv Real (fderiv Real u) p w v := by
  have hdiff : DifferentiableAt Real (fderiv Real u) p :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h := hdiff.hasFDerivAt.clm_apply (hasFDerivAt_const v p)
  have heq := h.fderiv
  simpa using DFunLike.congr_fun heq w

lemma fderiv_fderiv_add_const_smul
    {n : Nat} {u v : Euclidean n -> Real} {p : Euclidean n}
    (t : Real) (hu : ContDiffAt Real 2 u p) (hv : ContDiffAt Real 2 v p) :
    fderiv Real (fderiv Real (u + t • v)) p =
      fderiv Real (fderiv Real u) p + t • fderiv Real (fderiv Real v) p := by
  have heu : ∀ᶠ y in nhds p, ContDiffAt Real 2 u y := hu.eventually (by norm_num)
  have hev : ∀ᶠ y in nhds p, ContDiffAt Real 2 v y := hv.eventually (by norm_num)
  have heq : fderiv Real (u + t • v) =ᶠ[nhds p]
      fun y => fderiv Real u y + t • fderiv Real v y := by
    filter_upwards [heu, hev] with y huy hvy
    have hdu : DifferentiableAt Real u y := huy.differentiableAt (by norm_num)
    have hdv : DifferentiableAt Real v y := hvy.differentiableAt (by norm_num)
    rw [fderiv_add hdu (hdv.const_smul t), fderiv_const_smul hdv t]
  rw [heq.fderiv_eq]
  have hdu : DifferentiableAt Real (fderiv Real u) p :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdv : DifferentiableAt Real (fderiv Real v) p :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  change fderiv Real (fderiv Real u + t • fderiv Real v) p = _
  rw [fderiv_add hdu (hdv.const_smul t), fderiv_const_smul hdv t]

lemma hessianMatrix_add_const_smul
    {n : Nat} {u v : Euclidean n -> Real} {p : Euclidean n}
    (t : Real) (hu : ContDiffAt Real 2 u p) (hv : ContDiffAt Real 2 v p) :
    hessianMatrix (u + t • v) p = hessianMatrix u p + t • hessianMatrix v p := by
  ext i j
  simp only [hessianMatrix, LinearMap.BilinForm.toMatrix_apply, secondDerivativeBilin,
    Matrix.add_apply, Matrix.smul_apply]
  rw [fderiv_fderiv_add_const_smul t hu hv]
  simp

lemma nondivergenceOperator_add_const_smul
    {n : Nat} {u v : Euclidean n -> Real} {p : Euclidean n}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    (t : Real) (hu : ContDiffAt Real 2 u p) (hv : ContDiffAt Real 2 v p) :
    nondivergenceOperator a b c (u + t • v) p =
      nondivergenceOperator a b c u p + t * nondivergenceOperator a b c v p := by
  unfold nondivergenceOperator
  rw [hessianMatrix_add_const_smul t hu hv]
  have hdu : DifferentiableAt Real u p := hu.differentiableAt (by norm_num)
  have hdv : DifferentiableAt Real v p := hv.differentiableAt (by norm_num)
  rw [fderiv_add hdu (hdv.const_smul t), fderiv_const_smul hdv t]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    add_apply, smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  have hreorder :
      (∑ x, b p x * (t * fderiv Real v p
        (EuclideanSpace.basisFun (Fin n) Real x))) =
      t * ∑ x, b p x * fderiv Real v p
        (EuclideanSpace.basisFun (Fin n) Real x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  simp only [mul_add]
  rw [Finset.sum_add_distrib, hreorder]
  ring

lemma nondivergenceOperator_nonpos_at_nonnegative_localMax
    {n : Nat} {u : Euclidean n -> Real} {p : Euclidean n}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    {lambda : Real} (hlambda : 0 <= lambda)
    (helliptic : UniformlyElliptic (a p) lambda)
    (hu : ContDiffAt Real 2 u p) (hmax : IsLocalMax u p)
    (hc : c p <= 0) (hu_nonneg : 0 <= u p) :
    nondivergenceOperator a b c u p <= 0 := by
  have hsecond := trace_hessian_nonpos_of_uniformlyElliptic
    (a p) hlambda helliptic hu hmax
  have hfirst :
      (∑ i, b p i * fderiv Real u p (EuclideanSpace.basisFun (Fin n) Real i)) = 0 := by
    rw [hmax.fderiv_eq_zero]
    simp
  have hzero : c p * u p <= 0 := mul_nonpos_of_nonpos_of_nonneg hc hu_nonneg
  unfold nondivergenceOperator
  rw [hfirst]
  linarith

lemma nondivergenceOperator_nonpos_at_localMax_of_zeroOrder_eq_zero
    {n : Nat} {u : Euclidean n -> Real} {p : Euclidean n}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    {lambda : Real} (hlambda : 0 <= lambda)
    (helliptic : UniformlyElliptic (a p) lambda)
    (hu : ContDiffAt Real 2 u p) (hmax : IsLocalMax u p)
    (hc : c p = 0) :
    nondivergenceOperator a b c u p <= 0 := by
  have hsecond := trace_hessian_nonpos_of_uniformlyElliptic
    (a p) hlambda helliptic hu hmax
  have hfirst :
      (∑ i, b p i * fderiv Real u p (EuclideanSpace.basisFun (Fin n) Real i)) = 0 := by
    rw [hmax.fderiv_eq_zero]
    simp
  unfold nondivergenceOperator
  rw [hfirst, hc]
  simpa using hsecond

/-- Han--Lin Lemma 2.1. For a uniformly elliptic nondivergence-form operator
with nonpositive zeroth-order coefficient, a nonnegative maximum of a strict
subsolution on the closure of a bounded connected domain is not interior. -/
theorem positive_operator_nonnegative_maximum_not_mem
    {n : Nat} {Omega : Set (Euclidean n)}
    {u : Euclidean n -> Real}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    (hOmega_open : IsOpen Omega) (_hOmega_bounded : Bornology.IsBounded Omega)
    (_hOmega_connected : IsConnected Omega)
    (_ha : ContinuousOn a (closure Omega))
    (_hb : ContinuousOn b (closure Omega))
    (_hc_cont : ContinuousOn c (closure Omega))
    (huC2 : ContDiffOn Real 2 u Omega)
    (_hu_cont : ContinuousOn u (closure Omega))
    (helliptic : exists lambda : Real, 0 < lambda /\
      forall x, x ∈ Omega -> UniformlyElliptic (a x) lambda)
    (hLu : forall x, x ∈ Omega -> 0 < nondivergenceOperator a b c u x)
    (hc : forall x, x ∈ Omega -> c x <= 0)
    {x0 : Euclidean n} (hmax : IsMaxOn u (closure Omega) x0)
    (hu_nonneg : 0 <= u x0) :
    x0 ∉ Omega := by
  intro hx0
  obtain ⟨lambda, hlambda, helliptic⟩ := helliptic
  have hclosure_nhds : closure Omega ∈ nhds x0 :=
    mem_of_superset (hOmega_open.mem_nhds hx0) subset_closure
  have hlocal : IsLocalMax u x0 := hmax.isLocalMax hclosure_nhds
  have huAt : ContDiffAt Real 2 u x0 :=
    (huC2 x0 hx0).contDiffAt (hOmega_open.mem_nhds hx0)
  have hnonpos := nondivergenceOperator_nonpos_at_nonnegative_localMax
    (b := b) hlambda.le (helliptic x0 hx0) huAt hlocal (hc x0 hx0) hu_nonneg
  exact (not_lt_of_ge hnonpos) (hLu x0 hx0)

/-- Han--Lin Remark 2.2. If the zeroth-order coefficient vanishes, the sign of
an interior maximum is irrelevant in the strict maximum principle. -/
theorem positive_operator_maximum_not_mem_of_zeroOrder_eq_zero
    {n : Nat} {Omega : Set (Euclidean n)}
    {u : Euclidean n -> Real}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    (hOmega_open : IsOpen Omega) (_hOmega_bounded : Bornology.IsBounded Omega)
    (_hOmega_connected : IsConnected Omega)
    (_ha : ContinuousOn a (closure Omega))
    (_hb : ContinuousOn b (closure Omega))
    (_hc_cont : ContinuousOn c (closure Omega))
    (huC2 : ContDiffOn Real 2 u Omega)
    (_hu_cont : ContinuousOn u (closure Omega))
    (helliptic : exists lambda : Real, 0 < lambda /\
      forall x, x ∈ Omega -> UniformlyElliptic (a x) lambda)
    (hLu : forall x, x ∈ Omega -> 0 < nondivergenceOperator a b c u x)
    (hc : forall x, x ∈ Omega -> c x = 0)
    {x0 : Euclidean n} (hmax : IsMaxOn u (closure Omega) x0) :
    x0 ∉ Omega := by
  intro hx0
  obtain ⟨lambda, hlambda, helliptic⟩ := helliptic
  have hclosure_nhds : closure Omega ∈ nhds x0 :=
    mem_of_superset (hOmega_open.mem_nhds hx0) subset_closure
  have hlocal : IsLocalMax u x0 := hmax.isLocalMax hclosure_nhds
  have huAt : ContDiffAt Real 2 u x0 :=
    (huC2 x0 hx0).contDiffAt (hOmega_open.mem_nhds hx0)
  have hnonpos := nondivergenceOperator_nonpos_at_localMax_of_zeroOrder_eq_zero
    (b := b) hlambda.le (helliptic x0 hx0) huAt hlocal (hc x0 hx0)
  exact (not_lt_of_ge hnonpos) (hLu x0 hx0)

end HanLinLectureNotes.Ch02
