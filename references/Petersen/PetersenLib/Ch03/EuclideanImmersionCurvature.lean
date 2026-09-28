import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Petersen Ch. 3, §3.4 Exercise 3.4.1 — Gauss's Theorema Egregium in coordinates

Let `M` be an `n`-dimensional submanifold of a flat ambient space, given locally by
a smooth parametrization `u : ℝ^n → F` (an immersion, so the Gram matrix
`g_{ij} = B(∂_i u, ∂_j u)` is invertible).  Petersen's Exercise 3.4.1 asks to show
that the curvature coefficients `R^l_{ijk}` of the induced metric depend, in these
coordinates, only on the **first and second** partial derivatives of `u` — the third
derivatives cancel.

This is the coordinate form of Gauss's *Theorema Egregium* in codimension `m`.
We prove the sharper statement it rests on, the **Gauss equation**
```
R_{ijkl} = B(II_{jk}, II_{il}) − B(II_{ik}, II_{jl}),
```
where `II_{ij} = ∂²_{ij}u − ∑ₛ Γˢ_{ij} ∂ₛu` is the (vector-valued) **second
fundamental form** — the `B`-normal component of `∂²_{ij}u`, built only from first
and second partials of `u`.  Since the fully-lowered curvature `R_{ijkl}` is the
`B`-pairing of two second fundamental forms, and `R^l_{ijk} = ∑ₚ gˡᵖ R_{ijkp}`
with `gˡᵖ` a function of the first partials only, the whole curvature depends
only on `∂u` and `∂²u`.  As a consequence we record the exact "jet invariance"
statement: two parametrizations with the same first and second derivatives at a
point induce the same curvature there.

## The ambient form

The ambient pairing enters only as a **continuous symmetric bilinear form**
`B : F →L[ℝ] F →L[ℝ] ℝ` — positive-definiteness, and indeed nondegeneracy, are
*never used*.  Every statement below that needs symmetry takes it as the explicit
hypothesis `hB : ∀ v w, B v w = B w v`, and invertibility of the *induced* Gram
matrix is always a hypothesis (`hx`), never derived from definiteness of `B`.

This generality is not idle.  Taking `B := innerSL ℝ` recovers the Euclidean
ambient `ℝ^{n+m}` (Exercise 3.4.1, `exercise3_4_1` below).  Taking `B` indefinite
of index one gives immersions into **Minkowski space** `ℝ^{n,1}`, which is exactly
what Exercise 3.4.22 needs; see `PetersenLib/Ch03/HypersurfaceFundamentalTheorem.lean`,
where Exercises 3.4.21 (Euclidean) and 3.4.22 (Minkowski) are both obtained from
this one layer — the only difference between them being the scalar `B(N,N) = ±1`.

## Proof idea

The ambient space is flat, so the induced connection is the tangential projection
of the plain derivative: `∇^M_{∂_i}∂_j = (∂²_{ij}u)^⊤ = ∂²_{ij}u − II_{ij}`.
Writing `W_{jk}` for this tangential field, the lowered curvature is
`R_{ijkl} = B(∂_i W_{jk} − ∂_j W_{ik}, ∂_l u)` (the bracket term drops, coordinate
frame).  Differentiating `W_{jk} = ∂²_{jk}u − II_{jk}` and pairing with `∂_l u`:
the third-derivative term `B(∂³_{ijk}u, ∂_l u)` is symmetric in `i,j` (Clairaut /
`IsSymmSndFDerivAt`) and cancels under antisymmetrization, and pairing
`∂_i II_{jk}` with `∂_l u` — computed from `B(II_{jk}, ∂_l u) ≡ 0` by the product
rule — returns `B(II_{jk}, II_{il})`.  Crucially the projection is only used
*through the pairing* `B(II, ∂_l u) = 0`, so we never differentiate the inverse
Gram matrix `gˡᵖ`.

Reference: Petersen, *Riemannian Geometry* (GTM 171, 3rd ed.), Exercise 3.4.1,
page 121.
-/

open scoped InnerProductSpace ContDiff Matrix
open Matrix

noncomputable section

namespace PetersenLib

namespace EuclideanImmersion

variable {n m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Calculus for a continuous bilinear form

The two facts about `B` we need from analysis, mirroring `ContDiff.inner` and
`fderiv_inner_apply` (`Mathlib/Analysis/InnerProductSpace/Calculus.lean`)
structurally, but for a bare continuous bilinear form. -/

/-- Smoothness of `y ↦ B (f y) (g y)` for a continuous bilinear form `B`. -/
theorem contDiff_bilin (B : F →L[ℝ] F →L[ℝ] ℝ) {k : WithTop ℕ∞}
    {f g : EuclideanSpace ℝ (Fin n) → F} (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    ContDiff ℝ k fun y => B (f y) (g y) :=
  (B.contDiff.comp hf).clm_apply hg

/-- Product rule for a continuous bilinear form:
`∂_v (B (f ·) (g ·)) = B (f x) (∂_v g) + B (∂_v f) (g x)`. -/
theorem fderiv_bilin_apply (B : F →L[ℝ] F →L[ℝ] ℝ) {f g : EuclideanSpace ℝ (Fin n) → F}
    {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => B (f y) (g y)) x v
      = B (f x) (fderiv ℝ g x v) + B (fderiv ℝ f x v) (g x) := by
  have hc : HasFDerivAt (fun y => B (f y)) (B.comp (fderiv ℝ f x)) x :=
    B.hasFDerivAt.comp x hf.hasFDerivAt
  rw [(hc.clm_apply hg.hasFDerivAt).fderiv]
  simp

/-! ## The coordinate data of an immersion -/

/-- The `i`-th coordinate direction in `ℝ^n`. -/
abbrev dir (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ)

variable (B : F →L[ℝ] F →L[ℝ] ℝ) (u : EuclideanSpace ℝ (Fin n) → F)

/-- First partial derivative `∂_i u`, as an `F`-valued field on `ℝ^n`. -/
def pd1 (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : F := fderiv ℝ u x (dir i)

/-- Second partial derivative `∂_i (∂_j u)`, as an `F`-valued field on `ℝ^n`. -/
def pd2 (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : F := fderiv ℝ (pd1 u j) x (dir i)

/-- The induced (first fundamental) metric `g_{ij} = B(∂_i u, ∂_j u)`. -/
def gm (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ := B (pd1 u i x) (pd1 u j x)

/-- The induced metric as a matrix at a point. -/
def gmat (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => gm B u i j x

/-- The inverse metric `gˡᵖ`, as the nonsingular matrix inverse `(det)⁻¹ • adj`. -/
def gInv (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  (gmat B u x)⁻¹

/-- Christoffel symbol of the first kind, in the clean tangential form
`Γ_{k,ij} = B(∂²_{ij}u, ∂_k u)`.  (Lemma `christoffelFirst_eq_metric` below shows
this equals the usual `½(∂_i g_{kj}+∂_j g_{ki}−∂_k g_{ij})`.) -/
def christoffelFirst (k i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  B (pd2 u i j x) (pd1 u k x)

/-- Christoffel symbol of the second kind, `Γˢ_{ij} = ∑ₖ gˢᵏ Γ_{k,ij}`. -/
def christoffelSecond (s i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ k, gInv B u x s k * christoffelFirst B u k i j x

/-- The induced covariant derivative `∇^M_{∂_i}∂_j = ∑ₛ Γˢ_{ij} ∂ₛ u`, the
tangential part of `∂²_{ij}u`, as an `F`-valued field. -/
def indCov (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : F :=
  ∑ s, christoffelSecond B u s i j x • pd1 u s x

/-- The (vector-valued) **second fundamental form** `II_{ij} = ∂²_{ij}u −
∇^M_{∂_i}∂_j`, the `B`-normal component of `∂²_{ij}u`. -/
def secondFund (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : F :=
  pd2 u i j x - indCov B u i j x

/-- The fully-lowered Riemann curvature `R_{ijkl}` of the induced metric, realized
through the induced connection `∇^M = indCov`:
`R_{ijkl} = B(∇^M_{∂_i}∇^M_{∂_j}∂_k − ∇^M_{∂_j}∇^M_{∂_i}∂_k, ∂_l u)`.  Because the
induced covariant derivative is the tangential projection of the plain derivative
and `∂_l u` is tangent, the projection can be dropped when pairing with `∂_l u`,
which is what this definition does. -/
def curvatureLower (i j k l : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  B (fderiv ℝ (fun y => indCov B u j k y) x (dir i)
    - fderiv ℝ (fun y => indCov B u i k y) x (dir j)) (pd1 u l x)

/-- The mixed curvature coefficients `R^l_{ijk} = ∑ₚ gˡᵖ R_{ijkp}` (raising the
last index of `curvatureLower` with the inverse metric). -/
def curvatureMixed (l i j k : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ p, gInv B u x l p * curvatureLower B u i j k p x

section Symmetry

variable {u}

/-- `pd2` (a nested single derivative) agrees with the second Fréchet derivative
`fderiv ℝ (fderiv ℝ u) x (dir i) (dir j)`, provided `fderiv ℝ u` is
differentiable at `x`. -/
theorem pd2_eq_sndFDeriv {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ ∞ u x)
    (i j : Fin n) :
    pd2 u i j x = fderiv ℝ (fderiv ℝ u) x (dir i) (dir j) := by
  have hDx : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) x :=
    ((hu.fderiv_right (m := 1) (by norm_cast)).differentiableAt one_ne_zero).hasFDerivAt
  have happ : HasFDerivAt (fun y => fderiv ℝ u y (dir j))
      ((ContinuousLinearMap.apply ℝ F (dir j)).comp (fderiv ℝ (fderiv ℝ u) x)) x :=
    (ContinuousLinearMap.apply ℝ F (dir j)).hasFDerivAt.comp x hDx
  have hbridge : pd2 u i j x = fderiv ℝ (fun y => fderiv ℝ u y (dir j)) x (dir i) := rfl
  rw [hbridge, happ.fderiv]
  simp

/-- `∂²_{ij}u` is symmetric in `i, j` (Clairaut), for a smooth parametrization. -/
theorem pd2_symm (hu : ContDiff ℝ ∞ u) (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    pd2 u i j x = pd2 u j i x := by
  have hsymm : IsSymmSndFDerivAt ℝ u x :=
    hu.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  rw [pd2_eq_sndFDeriv hu.contDiffAt, pd2_eq_sndFDeriv hu.contDiffAt, hsymm (dir i) (dir j)]

end Symmetry

section Algebra

variable {u}

/-- The induced metric is symmetric (for a symmetric ambient form). -/
theorem gm_symm (hB : ∀ v w : F, B v w = B w v) (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    gm B u i j x = gm B u j i x := by
  simp only [gm]; rw [hB]

/-- The defining inverse-Gram contraction `∑ₛ gˢᵏ g_{sl} = δ^k_l`, holding
wherever the Gram matrix is invertible. -/
theorem sum_gInv_gm (hB : ∀ v w : F, B v w = B w v) {x : EuclideanSpace ℝ (Fin n)}
    (hx : IsUnit (gmat B u x).det) (k l : Fin n) :
    ∑ s, gInv B u x s k * gm B u s l x = (1 : Matrix (Fin n) (Fin n) ℝ) l k := by
  have hmul : gmat B u x * gInv B u x = 1 := Matrix.mul_nonsing_inv _ hx
  have hone : (gmat B u x * gInv B u x) l k = ∑ s, gm B u l s x * gInv B u x s k := by
    rw [Matrix.mul_apply]; rfl
  rw [hmul] at hone
  rw [hone]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm, gm_symm B hB]

/-- **Second fundamental form is normal.**  `B(II_{ij}, ∂_l u) = 0`: the tangential
Christoffel part exactly cancels `B(∂²_{ij}u, ∂_l u)`.  Requires only invertibility
of the Gram matrix at the point (and symmetry of `B`). -/
theorem secondFund_normal (hB : ∀ v w : F, B v w = B w v) {x : EuclideanSpace ℝ (Fin n)}
    (hx : IsUnit (gmat B u x).det) (i j l : Fin n) : B (secondFund B u i j x) (pd1 u l x) = 0 := by
  have hI : B (secondFund B u i j x) (pd1 u l x)
      = christoffelFirst B u l i j x - ∑ s, christoffelSecond B u s i j x * gm B u s l x := by
    simp only [secondFund, indCov, map_sub, ContinuousLinearMap.sub_apply, map_sum,
      ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rfl
  rw [hI]
  have hsum : ∑ s, christoffelSecond B u s i j x * gm B u s l x = christoffelFirst B u l i j x := by
    simp only [christoffelSecond, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ k, ∑ s, gInv B u x s k * christoffelFirst B u k i j x * gm B u s l x
        = christoffelFirst B u k i j x * ∑ s, gInv B u x s k * gm B u s l x := by
      intro k; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_; ring
    rw [Finset.sum_congr rfl fun k _ => this k]
    have hkl : ∀ k, christoffelFirst B u k i j x * ∑ s, gInv B u x s k * gm B u s l x
        = christoffelFirst B u k i j x * (1 : Matrix (Fin n) (Fin n) ℝ) l k := by
      intro k; rw [sum_gInv_gm B hB hx]
    rw [Finset.sum_congr rfl fun k _ => hkl k]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [hsum]; ring

end Algebra

section Smoothness

variable {u}

/-- The first-partial field `∂_i u` is smooth. -/
theorem pd1_contDiff (hu : ContDiff ℝ ∞ u) (i : Fin n) : ContDiff ℝ ∞ (pd1 u i) :=
  (ContinuousLinearMap.apply ℝ F (dir i)).contDiff.comp (hu.fderiv_right (le_refl _))

/-- The second-partial field `∂_i(∂_j u)` is smooth. -/
theorem pd2_contDiff (hu : ContDiff ℝ ∞ u) (i j : Fin n) : ContDiff ℝ ∞ (fun x => pd2 u i j x) :=
  (ContinuousLinearMap.apply ℝ F (dir i)).contDiff.comp
    ((pd1_contDiff hu j).fderiv_right (le_refl _))

/-- The induced metric entry `g_{ij}` is smooth. -/
theorem gm_contDiff (hu : ContDiff ℝ ∞ u) (i j : Fin n) : ContDiff ℝ ∞ (gm B u i j) :=
  contDiff_bilin B (pd1_contDiff hu i) (pd1_contDiff hu j)

/-- The determinant of the Gram matrix is smooth at each point. -/
theorem det_contDiffAt (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (fun y => (gmat B u y).det) x := by
  have e : (fun y => (gmat B u y).det)
      = fun y => ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, gmat B u y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [e]
  refine ContDiffAt.sum fun σ _ => ?_
  exact contDiffAt_const.mul (contDiffAt_prod fun i _ => (gm_contDiff B hu (σ i) i).contDiffAt)

/-- Entries of the adjugate of the Gram matrix are smooth at each point. -/
theorem adjugate_contDiffAt (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => (gmat B u y).adjugate i j) x := by
  have e : (fun y => (gmat B u y).adjugate i j)
      = fun y => ((gmat B u y).updateRow j (Pi.single i 1)).det := by
    funext y; rw [Matrix.adjugate_apply]
  rw [e]
  have e2 : (fun y => ((gmat B u y).updateRow j (Pi.single i 1)).det)
      = fun y => ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ)
            * ∏ k, (gmat B u y).updateRow j (Pi.single i 1) (σ k) k := by
    funext y; rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [e2]
  refine ContDiffAt.sum fun σ _ => ?_
  refine contDiffAt_const.mul (contDiffAt_prod fun k _ => ?_)
  rcases eq_or_ne (σ k) j with hk | hk
  · rw [show (fun y => (gmat B u y).updateRow j (Pi.single i 1) (σ k) k)
        = fun _ => (Pi.single i 1 : Fin n → ℝ) k by funext y; rw [hk, Matrix.updateRow_self]]
    exact contDiffAt_const
  · rw [show (fun y => (gmat B u y).updateRow j (Pi.single i 1) (σ k) k)
        = fun y => gmat B u y (σ k) k by funext y; rw [Matrix.updateRow_ne hk]]
    exact (gm_contDiff B hu (σ k) k).contDiffAt

/-- Entries of the inverse Gram matrix are smooth wherever the determinant is
nonzero. -/
theorem gInv_contDiffAt (hu : ContDiff ℝ ∞ u) {x : EuclideanSpace ℝ (Fin n)}
    (hx : (gmat B u x).det ≠ 0) (s k : Fin n) :
    ContDiffAt ℝ ∞ (fun y => gInv B u y s k) x := by
  have e : (fun y => gInv B u y s k)
      = fun y => ((gmat B u y).det)⁻¹ * (gmat B u y).adjugate s k := by
    funext y; rw [gInv, Matrix.inv_def]
    simp [Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  exact ((det_contDiffAt B hu x).inv hx).mul (adjugate_contDiffAt B hu x s k)

/-- `Γ_{k,ij} = B(∂²_{ij}u, ∂_k u)` is smooth. -/
theorem christoffelFirst_contDiff (hu : ContDiff ℝ ∞ u) (k i j : Fin n) :
    ContDiff ℝ ∞ (christoffelFirst B u k i j) :=
  contDiff_bilin B (pd2_contDiff hu i j) (pd1_contDiff hu k)

/-- `Γˢ_{ij}` is smooth wherever the determinant is nonzero. -/
theorem christoffelSecond_contDiffAt (hu : ContDiff ℝ ∞ u) {x : EuclideanSpace ℝ (Fin n)}
    (hx : (gmat B u x).det ≠ 0) (s i j : Fin n) :
    ContDiffAt ℝ ∞ (christoffelSecond B u s i j) x := by
  have e : christoffelSecond B u s i j
      = fun y => ∑ k, gInv B u y s k * christoffelFirst B u k i j y := rfl
  rw [e]
  exact ContDiffAt.sum fun k _ =>
    (gInv_contDiffAt B hu hx s k).mul (christoffelFirst_contDiff B hu k i j).contDiffAt

/-- The induced covariant derivative field `∇^M_{∂_i}∂_j` is smooth where `det ≠ 0`. -/
theorem indCov_contDiffAt (hu : ContDiff ℝ ∞ u) {x : EuclideanSpace ℝ (Fin n)}
    (hx : (gmat B u x).det ≠ 0) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => indCov B u i j y) x := by
  simp only [indCov]
  exact ContDiffAt.sum fun s _ =>
    (christoffelSecond_contDiffAt B hu hx s i j).smul (pd1_contDiff hu s).contDiffAt

/-- The second fundamental form field `II_{ij}` is smooth where `det ≠ 0`. -/
theorem secondFund_contDiffAt (hu : ContDiff ℝ ∞ u) {x : EuclideanSpace ℝ (Fin n)}
    (hx : (gmat B u x).det ≠ 0) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => secondFund B u i j y) x := by
  simp only [secondFund]
  exact (pd2_contDiff hu i j).contDiffAt.sub (indCov_contDiffAt B hu hx i j)

end Smoothness

section MetricChristoffel

variable {u}

/-- Derivative of the induced metric:
`∂_a g_{ij} = B(∂²_{ai}u, ∂_j u) + B(∂_i u, ∂²_{aj}u)`. -/
theorem gm_fderiv (hu : ContDiff ℝ ∞ u) {x : EuclideanSpace ℝ (Fin n)} (a i j : Fin n) :
    fderiv ℝ (fun y => gm B u i j y) x (dir a)
      = B (pd2 u a i x) (pd1 u j x) + B (pd1 u i x) (pd2 u a j x) := by
  have hi : DifferentiableAt ℝ (fun y => pd1 u i y) x :=
    (pd1_contDiff hu i).contDiffAt.differentiableAt (by norm_cast)
  have hj : DifferentiableAt ℝ (fun y => pd1 u j y) x :=
    (pd1_contDiff hu j).contDiffAt.differentiableAt (by norm_cast)
  have hgm : (fun y => gm B u i j y) = fun y => B (pd1 u i y) (pd1 u j y) := rfl
  rw [hgm, fderiv_bilin_apply B hi hj (dir a)]
  have e1 : fderiv ℝ (fun y => pd1 u j y) x (dir a) = pd2 u a j x := rfl
  have e2 : fderiv ℝ (fun y => pd1 u i y) x (dir a) = pd2 u a i x := rfl
  rw [e1, e2, add_comm]

/-- **Faithfulness.**  The Christoffel symbol `Γ_{k,ij} = B(∂²_{ij}u, ∂_k u)` equals
the standard metric formula `½(∂_i g_{kj} + ∂_j g_{ki} − ∂_k g_{ij})`, confirming
that the induced connection `∇^M = indCov` is the Levi-Civita connection of the
induced metric — so `curvatureLower`/`curvatureMixed` really are its curvature. -/
theorem christoffelFirst_eq_metric (hB : ∀ v w : F, B v w = B w v) (hu : ContDiff ℝ ∞ u)
    {x : EuclideanSpace ℝ (Fin n)} (k i j : Fin n) :
    christoffelFirst B u k i j x
      = (1 / 2) * (fderiv ℝ (fun y => gm B u k j y) x (dir i)
          + fderiv ℝ (fun y => gm B u k i y) x (dir j)
          - fderiv ℝ (fun y => gm B u i j y) x (dir k)) := by
  rw [gm_fderiv B hu i k j, gm_fderiv B hu j k i, gm_fderiv B hu k i j]
  simp only [christoffelFirst]
  rw [pd2_symm hu k i, pd2_symm hu k j, pd2_symm hu j i,
    hB (pd1 u k x) (pd2 u i j x), hB (pd1 u i x) (pd2 u j k x)]
  ring

end MetricChristoffel

section Gauss

variable {u}

/-- Third partials are symmetric in the two outer differentiation slots:
`∂_i(∂²_{jk}u) = ∂_j(∂²_{ik}u)`. -/
theorem pd3_symm (hu : ContDiff ℝ ∞ u) {x : EuclideanSpace ℝ (Fin n)} (i j k : Fin n) :
    fderiv ℝ (fun y => pd2 u j k y) x (dir i) = fderiv ℝ (fun y => pd2 u i k y) x (dir j) := by
  have hw : ContDiff ℝ ∞ (pd1 u k) := pd1_contDiff hu k
  have hbridge : ∀ a b : Fin n,
      fderiv ℝ (fun y => pd2 u a k y) x (dir b)
        = fderiv ℝ (fderiv ℝ (pd1 u k)) x (dir b) (dir a) := by
    intro a b
    have hDx : HasFDerivAt (fderiv ℝ (pd1 u k)) (fderiv ℝ (fderiv ℝ (pd1 u k)) x) x :=
      ((hw.contDiffAt.fderiv_right (m := 1) (by norm_cast)).differentiableAt one_ne_zero).hasFDerivAt
    have happ : HasFDerivAt (fun y => fderiv ℝ (pd1 u k) y (dir a))
        ((ContinuousLinearMap.apply ℝ F (dir a)).comp (fderiv ℝ (fderiv ℝ (pd1 u k)) x)) x :=
      (ContinuousLinearMap.apply ℝ F (dir a)).hasFDerivAt.comp x hDx
    have hbr : (fun y => pd2 u a k y) = fun y => fderiv ℝ (pd1 u k) y (dir a) := rfl
    rw [hbr, happ.fderiv]; simp
  have hsymm : IsSymmSndFDerivAt ℝ (pd1 u k) x :=
    hw.contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  rw [hbridge i j, hbridge j i, hsymm (dir j) (dir i)]

/-- `B(II_{ab}, ∇^M_{∂_i}∂_l) = 0`: the second fundamental form is `B`-orthogonal to
the tangential field `∇^M`. -/
theorem secondFund_inner_indCov (hB : ∀ v w : F, B v w = B w v) {x : EuclideanSpace ℝ (Fin n)}
    (hx : IsUnit (gmat B u x).det) (a b i l : Fin n) :
    B (secondFund B u a b x) (indCov B u i l x) = 0 := by
  simp only [indCov, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_eq_zero fun s _ => ?_
  have : B (secondFund B u a b x) (pd1 u s x) = 0 := secondFund_normal B hB hx a b s
  rw [this, mul_zero]

/-- `B(II_{ab}, ∂²_{cl}u) = B(II_{ab}, II_{cl})`: pairing a `B`-normal vector with the
full second partial keeps only the normal component. -/
theorem secondFund_inner_pd2 (hB : ∀ v w : F, B v w = B w v) {x : EuclideanSpace ℝ (Fin n)}
    (hx : IsUnit (gmat B u x).det) (a b c l : Fin n) :
    B (secondFund B u a b x) (pd2 u c l x)
      = B (secondFund B u a b x) (secondFund B u c l x) := by
  have hpd2 : pd2 u c l x = indCov B u c l x + secondFund B u c l x := by
    simp only [secondFund]; abel
  rw [hpd2, map_add, secondFund_inner_indCov B hB hx, zero_add]

/-- The set where the Gram determinant is nonzero is a neighbourhood of any point
where it is nonzero. -/
theorem det_ne_zero_eventually (hu : ContDiff ℝ ∞ u) {x : EuclideanSpace ℝ (Fin n)}
    (hx : (gmat B u x).det ≠ 0) : ∀ᶠ y in nhds x, (gmat B u y).det ≠ 0 :=
  (det_contDiffAt B hu x).continuousAt.eventually_ne hx

/-- **Product-rule step.**  `B(∂_c II_{ab}, ∂_l u) = −B(II_{ab}, II_{cl})`, obtained by
differentiating the identically-zero function `y ↦ B(II_{ab}(y), ∂_l u(y))`. -/
theorem secondFund_deriv_paired (hB : ∀ v w : F, B v w = B w v) (hu : ContDiff ℝ ∞ u)
    {x : EuclideanSpace ℝ (Fin n)} (hx : (gmat B u x).det ≠ 0) (a b c l : Fin n) :
    B (fderiv ℝ (fun y => secondFund B u a b y) x (dir c)) (pd1 u l x)
      = -B (secondFund B u a b x) (secondFund B u c l x) := by
  have hxU : IsUnit (gmat B u x).det := hx.isUnit
  have hII : DifferentiableAt ℝ (fun y => secondFund B u a b y) x :=
    (secondFund_contDiffAt B hu hx a b).differentiableAt (by norm_cast)
  have hDl : DifferentiableAt ℝ (fun y => pd1 u l y) x :=
    (pd1_contDiff hu l).contDiffAt.differentiableAt (by norm_cast)
  -- the paired function vanishes near `x`, so its derivative at `x` is `0`
  have h0 : (fun y => B (secondFund B u a b y) (pd1 u l y)) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [det_ne_zero_eventually B hu hx] with y hy
    exact secondFund_normal B hB hy.isUnit a b l
  have hz : fderiv ℝ (fun y => B (secondFund B u a b y) (pd1 u l y)) x = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq h0]; simp
  -- product rule for the bilinear form, applied to `dir c`
  have hprod : fderiv ℝ (fun y => B (secondFund B u a b y) (pd1 u l y)) x (dir c)
      = B (secondFund B u a b x) (fderiv ℝ (fun y => pd1 u l y) x (dir c))
        + B (fderiv ℝ (fun y => secondFund B u a b y) x (dir c)) (pd1 u l x) :=
    fderiv_bilin_apply B hII hDl (dir c)
  rw [hz] at hprod
  simp only [ContinuousLinearMap.zero_apply] at hprod
  have hpd2 : fderiv ℝ (fun y => pd1 u l y) x (dir c) = pd2 u c l x := rfl
  rw [hpd2, secondFund_inner_pd2 B hB hxU] at hprod
  linarith [hprod]

/-- The key expansion of one covariant-derivative term. -/
theorem curvatureLower_term (hB : ∀ v w : F, B v w = B w v) (hu : ContDiff ℝ ∞ u)
    {x : EuclideanSpace ℝ (Fin n)} (hx : (gmat B u x).det ≠ 0) (a b c l : Fin n) :
    B (fderiv ℝ (fun y => indCov B u a b y) x (dir c)) (pd1 u l x)
      = B (fderiv ℝ (fun y => pd2 u a b y) x (dir c)) (pd1 u l x)
        + B (secondFund B u a b x) (secondFund B u c l x) := by
  have hpd2diff : DifferentiableAt ℝ (fun y => pd2 u a b y) x :=
    (pd2_contDiff hu a b).contDiffAt.differentiableAt (by norm_cast)
  have hIIdiff : DifferentiableAt ℝ (fun y => secondFund B u a b y) x :=
    (secondFund_contDiffAt B hu hx a b).differentiableAt (by norm_cast)
  have hfield : (fun y => indCov B u a b y) = fun y => pd2 u a b y - secondFund B u a b y := by
    funext y; simp only [secondFund]; abel
  have hderivCLM : fderiv ℝ (fun y => indCov B u a b y) x
      = fderiv ℝ (fun y => pd2 u a b y) x - fderiv ℝ (fun y => secondFund B u a b y) x := by
    rw [hfield]; exact fderiv_sub hpd2diff hIIdiff
  have hderiv : fderiv ℝ (fun y => indCov B u a b y) x (dir c)
      = fderiv ℝ (fun y => pd2 u a b y) x (dir c)
        - fderiv ℝ (fun y => secondFund B u a b y) x (dir c) := by
    rw [hderivCLM, ContinuousLinearMap.sub_apply]
  rw [hderiv, map_sub, ContinuousLinearMap.sub_apply,
    secondFund_deriv_paired B hB hu hx a b c l]
  ring

/-- **Gauss's Theorema Egregium in coordinates** (Petersen Exercise 3.4.1).  The
fully-lowered curvature of the induced metric is the *Gauss equation*
```
R_{ijkl} = B(II_{jk}, II_{il}) − B(II_{ik}, II_{jl}),
```
in which the second fundamental forms `II` are built only from the first and
second partial derivatives of `u`.  In particular `R_{ijkl}` — and hence the
mixed coefficients `R^l_{ijk} = ∑ₚ gˡᵖ R_{ijkp}` — depends only on `∂u` and
`∂²u`; the third derivatives cancel. -/
theorem gaussEquation (hB : ∀ v w : F, B v w = B w v) (hu : ContDiff ℝ ∞ u)
    {x : EuclideanSpace ℝ (Fin n)} (hx : (gmat B u x).det ≠ 0) (i j k l : Fin n) :
    curvatureLower B u i j k l x
      = B (secondFund B u j k x) (secondFund B u i l x)
        - B (secondFund B u i k x) (secondFund B u j l x) := by
  simp only [curvatureLower, map_sub, ContinuousLinearMap.sub_apply]
  rw [curvatureLower_term B hB hu hx j k i l, curvatureLower_term B hB hu hx i k j l,
    pd3_symm hu i j k]
  ring

end Gauss

section JetInvariance

variable {u v : EuclideanSpace ℝ (Fin n) → F} {x : EuclideanSpace ℝ (Fin n)}
  (h1 : ∀ i, pd1 u i x = pd1 v i x) (h2 : ∀ i j, pd2 u i j x = pd2 v i j x)

include h1 in
/-- Equal first partials at `x` give equal Gram matrices at `x`. -/
theorem gmat_eq_of_jet : gmat B u x = gmat B v x := by
  ext i j; simp only [gmat, Matrix.of_apply, gm, h1]

include h1 in
/-- Equal first partials at `x` give equal inverse Gram matrices at `x`. -/
theorem gInv_eq_of_jet : gInv B u x = gInv B v x := by
  simp only [gInv, gmat_eq_of_jet B h1]

include h1 h2 in
/-- The second fundamental form at `x` is a function of the first and second
partials at `x` only. -/
theorem secondFund_eq_of_jet (i j : Fin n) : secondFund B u i j x = secondFund B v i j x := by
  have hCF : ∀ k a b, christoffelFirst B u k a b x = christoffelFirst B v k a b x := by
    intro k a b; simp only [christoffelFirst, h1, h2]
  have hCS : ∀ s a b, christoffelSecond B u s a b x = christoffelSecond B v s a b x := by
    intro s a b; simp only [christoffelSecond, gInv_eq_of_jet B h1, hCF]
  have hIC : ∀ a b, indCov B u a b x = indCov B v a b x := by
    intro a b; simp only [indCov, hCS, h1]
  simp only [secondFund, h2, hIC]

include h1 h2 in
/-- **Exercise 3.4.1** (Petersen, `rem:pet-ch3-ex-1`).  For a submanifold of
`ℝ^{n+m}` given by a smooth parametrization `u`, the curvature coefficients
`R^l_{ijk}` of the induced metric depend, in these coordinates, only on the
first and second partial derivatives of `u`: two parametrizations with the same
first and second partials at a point induce the same curvature there.

This is the coordinate form of Gauss's *Theorema Egregium*.  Its mechanism is the
Gauss equation `gaussEquation`, which exhibits the fully-lowered curvature as
`B(II_{jk}, II_{il}) − B(II_{ik}, II_{jl})` with `II` built only from `∂u` and
`∂²u`; raising the last index with the (equally jet-determined) inverse metric
gives the mixed coefficients `R^l_{ijk}`. -/
theorem curvatureMixed_eq_of_jet (hB : ∀ v w : F, B v w = B w v) (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (hx : (gmat B u x).det ≠ 0) (l i j k : Fin n) :
    curvatureMixed B u l i j k x = curvatureMixed B v l i j k x := by
  have hxv : (gmat B v x).det ≠ 0 := by rwa [gmat_eq_of_jet B h1] at hx
  have hCL : ∀ p, curvatureLower B u i j k p x = curvatureLower B v i j k p x := by
    intro p
    rw [gaussEquation B hB hu hx i j k p, gaussEquation B hB hv hxv i j k p]
    simp only [secondFund_eq_of_jet B h1 h2]
  simp only [curvatureMixed, gInv_eq_of_jet B h1, hCL]

end JetInvariance

/-! ## The Euclidean specialization

Exercise 3.4.1 as Petersen states it: the ambient space is `ℝ^{n+m}` with its
inner product, i.e. `B := innerSL ℝ`, whose symmetry is `real_inner_comm`. -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The Euclidean ambient pairing `⟪·,·⟫_ℝ` as a continuous bilinear form. -/
abbrev euclideanForm : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ

theorem euclideanForm_symm (v w : F) : (euclideanForm v) w = (euclideanForm w) v :=
  real_inner_comm w v

/-- **Exercise 3.4.1** in the Euclidean ambient `ℝ^{n+m}`: jet invariance of the
induced curvature. -/
theorem exercise3_4_1 {u v : EuclideanSpace ℝ (Fin n) → F} {x : EuclideanSpace ℝ (Fin n)}
    (h1 : ∀ i, pd1 u i x = pd1 v i x) (h2 : ∀ i j, pd2 u i j x = pd2 v i j x)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hx : (gmat (euclideanForm (F := F)) u x).det ≠ 0) (l i j k : Fin n) :
    curvatureMixed euclideanForm u l i j k x = curvatureMixed euclideanForm v l i j k x :=
  curvatureMixed_eq_of_jet euclideanForm h1 h2 euclideanForm_symm hu hv hx l i j k

end EuclideanImmersion

/-- **Exercise 3.4.1** (Petersen `rem:pet-ch3-ex-1`): for a submanifold of
`ℝ^{n+m}` given by a smooth parametrization, the curvature coefficients
`R^l_{ijk}` of the induced metric depend, in these coordinates, only on the first
and second partial derivatives of the parametrization.  Stated as jet invariance:
two smooth parametrizations sharing their first and second partials at a point
(one of them an immersion there) have the same curvature at that point.  See
`EuclideanImmersion.gaussEquation` for the underlying Gauss / Theorema Egregium
identity. -/
alias exercise3_4_1 := EuclideanImmersion.exercise3_4_1

end PetersenLib
