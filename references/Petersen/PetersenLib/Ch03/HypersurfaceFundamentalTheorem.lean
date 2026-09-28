import PetersenLib.Ch03.EuclideanImmersionCurvature
import PetersenLib.Ch01.Minkowski

/-!
# Petersen Ch. 3, §3.4 — Exercises 3.4.21 and 3.4.22 (fundamental theorem of hypersurface theory)

Let `F = (F, B)` be a flat ambient space carrying a symmetric, nondegenerate
continuous bilinear form `B`, and let `u : ℝⁿ → F` be a smooth immersion of
**codimension one**, presented in coordinates as `F = (u¹, …, u^{n+1})` with
`U^i_k = ∂uⁱ/∂xᵏ`.  A **unit normal** is a smooth field `N` with
`B(N, ∂_k u) ≡ 0` and `B(N, N) ≡ ε`, where `ε = ±1`.

Petersen's second fundamental form is `Π_{jk} = B(∇_j N, ∂_k u)` (`shapeForm`),
and this file proves, for both signs of `ε` at once:

* **part (1) — the Gauss formula.** `∂U^i_j/∂xᵏ = ∑ₛ Γˢ_{kj} U^i_s − ε·Π_{jk} Nⁱ`,
  i.e. the second partial `∂²_{kj}u` splits into its tangential part `∇^M_{∂_k}∂_j`
  and a normal part carried entirely by `N` (`gaussFormula`).
* **part (2) — the integrability conditions are the Gauss and Codazzi equations.**
  `R_{ijkl} = ε·(Π_{jk}Π_{il} − Π_{ik}Π_{jl})` (`gaussEquation_hypersurface`) and
  `(∇_iΠ)_{jk} = (∇_jΠ)_{ik}` (`codazziEquation`).  Both are *integrability
  conditions* in the literal sense used by Exercise 3.4.20: each is the statement
  that a mixed third partial of `u` is symmetric in its two outer slots
  (`pd3_symm`, i.e. Clairaut), read off in the tangential and the normal
  direction respectively.

Taking `ε = +1` and `B = ⟪·,·⟫` gives **Exercise 3.4.21** (immersions into
`ℝ^{n+1}`); taking `ε = −1` and `B` the Minkowski form gives **Exercise 3.4.22**
(immersions into `ℝ^{n,1}`, with `|N|² = −1`).  The two exercises differ *only* in
the scalar `ε`, which is why they are proved together here.

## Modelling

The ambient form enters through `PetersenLib/Ch03/EuclideanImmersionCurvature.lean`
(namespace `EuclideanImmersion`), whose whole coordinate apparatus — `pd1`, `pd2`,
`gm`, `gInv`, `christoffelFirst`/`christoffelSecond`, `indCov`, `secondFund`,
`curvatureLower`, and the Gauss equation `gaussEquation` — is stated for a bare
symmetric continuous bilinear form `B`, positive-definiteness being unused.

Following the house pattern of `Ch03/SecondFundamentalForm.lean` and
`Ch03/GaussCodazzi.lean` ("there is no Riemannian-submanifold layer at this point
of the project, so a hypersurface enters through its unit normal field"), the
normal `N` is **given data** with hypotheses, not constructed.  Codimension one is
expressed by `hspan`: `{N(x), ∂₁u(x), …, ∂ₙu(x)}` spans `F`.  For the actual data
of the exercises (`F = ℝ^{n+1}`, `u` an immersion, `N` a unit normal) this is the
honest content of "codimension one", and it is what makes the normal part of
`∂²u` a multiple of `N`.

## Scope

Parts (1) and (2) — the *necessity* half — are formalized, with one caveat worth
stating precisely: Petersen's part (2) asks to show the integrability conditions are
**equivalent to** Gauss–Codazzi, and only the forward direction is proved here, i.e.
that an actual immersion *satisfies* both equations (Clairaut ⟹ Gauss ∧ Codazzi).
The reverse — that a `(g, Π)` satisfying Gauss–Codazzi makes the system integrable —
is the same Frobenius statement as part (3), and is not formalized; see below.

Petersen's parts (3) and (4) are **existence** statements: (3) given `g_{ij}` and a symmetric `Π_{ij}`
satisfying Gauss–Codazzi, *construct* a local Riemannian immersion realizing them
(the Bonnet / fundamental-theorem-of-hypersurfaces existence theorem), and (4)
*construct* the sphere resp. hyperboloid model for a metric of constant curvature
`±R⁻²`.  Both need an integral-manifold / **Frobenius** PDE-existence theorem,
which is not available in Mathlib (only single-vector-field `PicardLindelof` ODE
existence) and is not formalized in `PetersenLib` — exactly the blocker recorded
at `Ch03/PDEIntegrability.lean` for the sufficiency half of Exercise 3.4.20, of
which this is the geometric instance.

The *converse* (non-existence) direction of part (4) *is* formalized, as
`umbilic_constantCurvature`: an immersion whose normal is the position field,
`N = ±R⁻¹·F` — i.e. one landing in a sphere of radius `R` (`ε = +1`) resp. in the
hyperboloid `H^n(R)` (`ε = −1`) — has `Π = ∓R⁻¹ g` and hence constant curvature
`ε·R⁻²`, giving `+R⁻²` for the sphere and `−R⁻²` for `H^n(R)`.

Reference: Petersen, *Riemannian Geometry* (GTM 171, 3rd ed.), Exercises 3.4.21
and 3.4.22, pages 126–127.
-/

open scoped InnerProductSpace ContDiff Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

namespace Hypersurface

open EuclideanImmersion

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (B : F →L[ℝ] F →L[ℝ] ℝ) (u N : EuclideanSpace ℝ (Fin n) → F)

/-! ## The second fundamental form of a hypersurface, in coordinates -/

/-- **Petersen's second fundamental form** of a hypersurface with unit normal `N`,
in the coordinates of a parametrization `u`:
`Π_{jk} = Π(∂_j, ∂_k) = g(∇_j N, ∂_k) = B(∂_j N, ∂_k u)`.

This is the definition Petersen uses in Exercise 3.4.21 verbatim.  Note `∂_j N` is
the *ambient* derivative of `N`; because `B(N, N)` is constant it is automatically
tangential (`normal_deriv_perp_normal`), so no projection is needed. -/
def shapeForm (j k : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  B (pd1 N j x) (pd1 u k x)

/-- The **coordinate covariant derivative** of the `(0,2)`-tensor `Π`:
`(∇_iΠ)_{jk} = ∂_iΠ_{jk} − ∑ₛ Γˢ_{ij}Π_{sk} − ∑ₛ Γˢ_{ik}Π_{js}`. -/
def shapeFormCovDeriv (i j k : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ (fun y => shapeForm B u N j k y) x (dir i)
    - ∑ s, christoffelSecond B u s i j x * shapeForm B u N s k x
    - ∑ s, christoffelSecond B u s i k x * shapeForm B u N j s x

section Basic

variable {B u N}

/-- The tangential field `∇^M_{∂_j}∂_k` is `B`-orthogonal to `N`. -/
theorem normal_inner_indCov (hNperp : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
    B (N x) (pd1 u i x) = 0) (x : EuclideanSpace ℝ (Fin n)) (j k : Fin n) :
    B (N x) (indCov B u j k x) = 0 := by
  simp only [indCov, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_eq_zero fun s _ => by rw [hNperp x s, mul_zero]

/-- **The sign bridge.**  `Π_{jk} = −B(∂²_{jk}u, N)`: differentiating the identity
`B(N, ∂_k u) ≡ 0` moves the derivative from `N` onto `u`. -/
theorem shapeForm_eq_neg_pd2 (hB : ∀ v w : F, B v w = B w v) (hu : ContDiff ℝ ∞ u)
    (hN : ContDiff ℝ ∞ N)
    (hNperp : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n), B (N x) (pd1 u i x) = 0)
    (x : EuclideanSpace ℝ (Fin n)) (j k : Fin n) :
    shapeForm B u N j k x = -B (pd2 u j k x) (N x) := by
  have hNd : DifferentiableAt ℝ N x := hN.contDiffAt.differentiableAt (by norm_cast)
  have hkd : DifferentiableAt ℝ (fun y => pd1 u k y) x :=
    (pd1_contDiff hu k).contDiffAt.differentiableAt (by norm_cast)
  have hzero : (fun y => B (N y) (pd1 u k y)) = fun _ => (0 : ℝ) := by
    funext y; exact hNperp y k
  have hd : fderiv ℝ (fun y => B (N y) (pd1 u k y)) x (dir j) = 0 := by
    rw [hzero]; simp
  rw [fderiv_bilin_apply B hNd hkd (dir j)] at hd
  have e1 : fderiv ℝ (fun y => pd1 u k y) x (dir j) = pd2 u j k x := rfl
  have e2 : fderiv ℝ N x (dir j) = pd1 N j x := rfl
  rw [e1, e2] at hd
  -- `hd : B (N x) (pd2 u j k x) + B (pd1 N j x) (pd1 u k x) = 0`
  have : shapeForm B u N j k x = -B (N x) (pd2 u j k x) := by
    simp only [shapeForm]; linarith [hd]
  rw [this, hB (N x) (pd2 u j k x)]

/-- `Π_{jk} = −B(II_{jk}, N)`: only the normal component of `∂²_{jk}u` contributes. -/
theorem shapeForm_eq_neg_secondFund (hB : ∀ v w : F, B v w = B w v) (hu : ContDiff ℝ ∞ u)
    (hN : ContDiff ℝ ∞ N)
    (hNperp : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n), B (N x) (pd1 u i x) = 0)
    (x : EuclideanSpace ℝ (Fin n)) (j k : Fin n) :
    shapeForm B u N j k x = -B (secondFund B u j k x) (N x) := by
  rw [shapeForm_eq_neg_pd2 hB hu hN hNperp x j k]
  congr 1
  have hsplit : pd2 u j k x = indCov B u j k x + secondFund B u j k x := by
    simp only [secondFund]; abel
  rw [hsplit, map_add, ContinuousLinearMap.add_apply,
    hB (indCov B u j k x) (N x), normal_inner_indCov hNperp x j k, zero_add]

/-- `Π` is symmetric, `Π_{jk} = Π_{kj}` — a restatement of Clairaut. -/
theorem shapeForm_symm (hB : ∀ v w : F, B v w = B w v) (hu : ContDiff ℝ ∞ u)
    (hN : ContDiff ℝ ∞ N)
    (hNperp : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n), B (N x) (pd1 u i x) = 0)
    (x : EuclideanSpace ℝ (Fin n)) (j k : Fin n) :
    shapeForm B u N j k x = shapeForm B u N k j x := by
  rw [shapeForm_eq_neg_pd2 hB hu hN hNperp x j k, shapeForm_eq_neg_pd2 hB hu hN hNperp x k j,
    pd2_symm hu j k]

/-- `B(∂_i N, N) = 0`: the derivative of a field of constant `B`-square is
`B`-orthogonal to it. -/
theorem normal_deriv_perp_normal (hB : ∀ v w : F, B v w = B w v) (hN : ContDiff ℝ ∞ N) {ε : ℝ}
    (hNunit : ∀ x : EuclideanSpace ℝ (Fin n), B (N x) (N x) = ε)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : B (pd1 N i x) (N x) = 0 := by
  have hNd : DifferentiableAt ℝ N x := hN.contDiffAt.differentiableAt (by norm_cast)
  have hzero : (fun y => B (N y) (N y)) = fun _ => ε := by funext y; exact hNunit y
  have hd : fderiv ℝ (fun y => B (N y) (N y)) x (dir i) = 0 := by rw [hzero]; simp
  rw [fderiv_bilin_apply B hNd hNd (dir i)] at hd
  have e2 : fderiv ℝ N x (dir i) = pd1 N i x := rfl
  rw [e2] at hd
  -- `hd : B (N x) (pd1 N i x) + B (pd1 N i x) (N x) = 0`, and the two agree by symmetry
  rw [hB (N x) (pd1 N i x)] at hd
  linarith [hd]

/-- `B(∂_s u, ∂_i N) = Π_{is}`: the definition of `Π`, read with the slots swapped. -/
theorem inner_pd1_normal_deriv (hB : ∀ v w : F, B v w = B w v)
    (x : EuclideanSpace ℝ (Fin n)) (i s : Fin n) :
    B (pd1 u s x) (pd1 N i x) = shapeForm B u N i s x := by
  rw [shapeForm, hB]

end Basic

/-! ## Part (1): the Gauss formula

The normal part of `∂²_{kj}u` is carried entirely by `N`.  This is the only place
where codimension one (`hspan`) and nondegeneracy of the ambient form (`hBnd`)
are used. -/

section Decomposition

variable {B u N}

/-- **Codimension-one decomposition.**  A vector `w` that is `B`-orthogonal to every
tangent vector `∂_i u(x)` is a multiple of the normal: `w = ε·B(w, N)·N`.

The proof is the parallelogram of the situation: `v := w − ε·B(w,N)·N` is
`B`-orthogonal to `N` (using `ε² = 1`) and to every `∂_i u`, hence — since those
span `F` — `B`-orthogonal to all of `F`, hence zero by nondegeneracy. -/
theorem eq_smul_normal_of_perp
    (hBnd : ∀ v : F, (∀ w, B v w = 0) → v = 0) {x : EuclideanSpace ℝ (Fin n)}
    (hspan : Submodule.span ℝ (insert (N x) (Set.range fun i => pd1 u i x)) = ⊤)
    (hNperp : ∀ i, B (N x) (pd1 u i x) = 0) {ε : ℝ} (hε : ε * ε = 1)
    (hNunit : B (N x) (N x) = ε) {w : F} (hw : ∀ i, B w (pd1 u i x) = 0) :
    w = (ε * B w (N x)) • N x := by
  refine sub_eq_zero.mp (hBnd _ ?_)
  have hvN : B (w - (ε * B w (N x)) • N x) (N x) = 0 := by
    simp only [map_sub, ContinuousLinearMap.sub_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hNunit]
    linear_combination (-(B w (N x))) * hε
  have hvT : ∀ i, B (w - (ε * B w (N x)) • N x) (pd1 u i x) = 0 := by
    intro i
    simp only [map_sub, ContinuousLinearMap.sub_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hw i, hNperp i]
    ring
  have hker : Submodule.span ℝ (insert (N x) (Set.range fun i => pd1 u i x))
      ≤ LinearMap.ker (B (w - (ε * B w (N x)) • N x)).toLinearMap := by
    rw [Submodule.span_le]
    rintro y hy
    simp only [Set.mem_insert_iff, Set.mem_range] at hy
    rcases hy with rfl | ⟨i, rfl⟩
    · exact hvN
    · exact hvT i
  exact fun y => hker (by rw [hspan]; trivial)

end Decomposition

section Main

variable {B u N}

/-- **Exercise 3.4.21/3.4.22, part (1) — the Gauss formula.**
`II_{jk} = −ε·Π_{jk}·N`: the second fundamental form of a *hypersurface* is the
scalar `Π` times the unit normal. -/
theorem secondFund_eq_smul_normal (hB : ∀ v w : F, B v w = B w v)
    (hBnd : ∀ v : F, (∀ w, B v w = 0) → v = 0) (hu : ContDiff ℝ ∞ u) (hN : ContDiff ℝ ∞ N)
    (hdet : ∀ x : EuclideanSpace ℝ (Fin n), (gmat B u x).det ≠ 0)
    (hspan : ∀ x : EuclideanSpace ℝ (Fin n),
      Submodule.span ℝ (insert (N x) (Set.range fun i => pd1 u i x)) = ⊤)
    (hNperp : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n), B (N x) (pd1 u i x) = 0)
    {ε : ℝ} (hε : ε * ε = 1)
    (hNunit : ∀ x : EuclideanSpace ℝ (Fin n), B (N x) (N x) = ε)
    (x : EuclideanSpace ℝ (Fin n)) (j k : Fin n) :
    secondFund B u j k x = (-(ε * shapeForm B u N j k x)) • N x := by
  have hw : ∀ i, B (secondFund B u j k x) (pd1 u i x) = 0 := fun i =>
    secondFund_normal B hB (hdet x).isUnit j k i
  rw [eq_smul_normal_of_perp hBnd (hspan x) (hNperp x) hε (hNunit x) hw]
  congr 1
  rw [shapeForm_eq_neg_secondFund hB hu hN hNperp x j k]
  ring

/-- **Exercise 3.4.21/3.4.22, part (1)**, in Petersen's coordinate form.  With
`U^i_j = ∂uⁱ/∂xʲ`, the Gauss formula reads
`∂U^i_j/∂xᵏ = ∑ₛ Γˢ_{kj} U^i_s − ε·Π_{jk} Nⁱ`,
i.e. as an identity of `F`-valued fields,
`∂²_{kj}u = ∑ₛ Γˢ_{kj} ∂ₛu − ε·Π_{jk}·N`.

(Petersen writes the first term `Γ^i_{kj}U^i_j`; the repeated `i` there is a
transcription slip — the Gauss formula sums over a fresh index `s`.) -/
theorem gaussFormula (hB : ∀ v w : F, B v w = B w v)
    (hBnd : ∀ v : F, (∀ w, B v w = 0) → v = 0) (hu : ContDiff ℝ ∞ u) (hN : ContDiff ℝ ∞ N)
    (hdet : ∀ x : EuclideanSpace ℝ (Fin n), (gmat B u x).det ≠ 0)
    (hspan : ∀ x : EuclideanSpace ℝ (Fin n),
      Submodule.span ℝ (insert (N x) (Set.range fun i => pd1 u i x)) = ⊤)
    (hNperp : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n), B (N x) (pd1 u i x) = 0)
    {ε : ℝ} (hε : ε * ε = 1)
    (hNunit : ∀ x : EuclideanSpace ℝ (Fin n), B (N x) (N x) = ε)
    (x : EuclideanSpace ℝ (Fin n)) (k j : Fin n) :
    pd2 u k j x
      = (∑ s, christoffelSecond B u s k j x • pd1 u s x) - (ε * shapeForm B u N j k x) • N x := by
  have h := secondFund_eq_smul_normal hB hBnd hu hN hdet hspan hNperp hε hNunit x k j
  rw [shapeForm_symm hB hu hN hNperp x k j] at h
  have hsplit : pd2 u k j x = indCov B u k j x + secondFund B u k j x := by
    simp only [secondFund]; abel
  rw [hsplit, h, indCov, neg_smul]
  abel

/-- **Exercise 3.4.21/3.4.22, part (2), Gauss equation.**  The tangential
integrability condition: `R_{ijkl} = ε·(Π_{jk}Π_{il} − Π_{ik}Π_{jl})`.

For `ε = +1` (a hypersurface in `ℝ^{n+1}`) this is Petersen's
`R_{ijkl} = Π_{jk}Π_{il} − Π_{ik}Π_{jl}`; for `ε = −1` (in `ℝ^{n,1}`) the sign
flips. -/
theorem gaussEquation_hypersurface (hB : ∀ v w : F, B v w = B w v)
    (hBnd : ∀ v : F, (∀ w, B v w = 0) → v = 0) (hu : ContDiff ℝ ∞ u) (hN : ContDiff ℝ ∞ N)
    (hdet : ∀ x : EuclideanSpace ℝ (Fin n), (gmat B u x).det ≠ 0)
    (hspan : ∀ x : EuclideanSpace ℝ (Fin n),
      Submodule.span ℝ (insert (N x) (Set.range fun i => pd1 u i x)) = ⊤)
    (hNperp : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n), B (N x) (pd1 u i x) = 0)
    {ε : ℝ} (hε : ε * ε = 1)
    (hNunit : ∀ x : EuclideanSpace ℝ (Fin n), B (N x) (N x) = ε)
    (x : EuclideanSpace ℝ (Fin n)) (i j k l : Fin n) :
    curvatureLower B u i j k l x
      = ε * (shapeForm B u N j k x * shapeForm B u N i l x
            - shapeForm B u N i k x * shapeForm B u N j l x) := by
  have hII : ∀ a b : Fin n,
      secondFund B u a b x = (-(ε * shapeForm B u N a b x)) • N x := fun a b =>
    secondFund_eq_smul_normal hB hBnd hu hN hdet hspan hNperp hε hNunit x a b
  have hpair : ∀ a b c d : Fin n,
      B (secondFund B u a b x) (secondFund B u c d x)
        = ε * (shapeForm B u N a b x * shapeForm B u N c d x) := by
    intro a b c d
    rw [hII a b, hII c d]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hNunit x]
    linear_combination (ε * shapeForm B u N a b x * shapeForm B u N c d x) * hε
  rw [gaussEquation B hB hu (hdet x) i j k l, hpair j k i l, hpair i k j l]
  ring

/-- **Exercise 3.4.21/3.4.22, part (2), Codazzi–Mainardi equation.**  The normal
integrability condition: `(∇_iΠ)_{jk} = (∇_jΠ)_{ik}`.

Unlike the Gauss equation this is independent of `ε`: it is the symmetry of the
third partial `∂_i(∂²_{jk}u)` in `i, j` (Clairaut, `pd3_symm`) read in the normal
direction, and the `Γ`-correction terms of `∇Π` cancel against the tangential
part of `∂²u` exactly. -/
theorem codazziEquation (hB : ∀ v w : F, B v w = B w v)
    (hBnd : ∀ v : F, (∀ w, B v w = 0) → v = 0) (hu : ContDiff ℝ ∞ u) (hN : ContDiff ℝ ∞ N)
    (hdet : ∀ x : EuclideanSpace ℝ (Fin n), (gmat B u x).det ≠ 0)
    (hspan : ∀ x : EuclideanSpace ℝ (Fin n),
      Submodule.span ℝ (insert (N x) (Set.range fun i => pd1 u i x)) = ⊤)
    (hNperp : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n), B (N x) (pd1 u i x) = 0)
    {ε : ℝ} (hε : ε * ε = 1)
    (hNunit : ∀ x : EuclideanSpace ℝ (Fin n), B (N x) (N x) = ε)
    (x : EuclideanSpace ℝ (Fin n)) (i j k : Fin n) :
    shapeFormCovDeriv B u N i j k x = shapeFormCovDeriv B u N j i k x := by
  -- The key computation: `∂_iΠ_{jk} + ∑ₛ Γˢ_{jk}Π_{is} = −B(∂_i∂²_{jk}u, N)`,
  -- whose right-hand side is symmetric in `i, j` by Clairaut.
  have key : ∀ a b c : Fin n,
      fderiv ℝ (fun y => shapeForm B u N b c y) x (dir a)
          + ∑ s, christoffelSecond B u s b c x * shapeForm B u N a s x
        = -B (fderiv ℝ (fun y => pd2 u b c y) x (dir a)) (N x) := by
    intro a b c
    -- rewrite `Π` as `−B(∂²u, N)` as a field, then differentiate by the product rule
    have hfield : (fun y => shapeForm B u N b c y) = fun y => -B (pd2 u b c y) (N y) := by
      funext y; exact shapeForm_eq_neg_pd2 hB hu hN hNperp y b c
    have hpd2d : DifferentiableAt ℝ (fun y => pd2 u b c y) x :=
      (pd2_contDiff hu b c).contDiffAt.differentiableAt (by norm_cast)
    have hNd : DifferentiableAt ℝ N x := hN.contDiffAt.differentiableAt (by norm_cast)
    have hderiv : fderiv ℝ (fun y => shapeForm B u N b c y) x (dir a)
        = -(B (pd2 u b c x) (fderiv ℝ N x (dir a))
            + B (fderiv ℝ (fun y => pd2 u b c y) x (dir a)) (N x)) := by
      rw [hfield]
      have hneg : fderiv ℝ (fun y => -B (pd2 u b c y) (N y)) x
          = -fderiv ℝ (fun y => B (pd2 u b c y) (N y)) x := fderiv_neg
      rw [hneg, ContinuousLinearMap.neg_apply, fderiv_bilin_apply B hpd2d hNd (dir a)]
    rw [hderiv]
    -- the remaining ingredient: `B(∂²_{bc}u, ∂_a N) = ∑ₛ Γˢ_{bc}Π_{as}`
    have htang : B (pd2 u b c x) (pd1 N a x)
        = ∑ s, christoffelSecond B u s b c x * shapeForm B u N a s x := by
      have hsplit : pd2 u b c x = indCov B u b c x + secondFund B u b c x := by
        simp only [secondFund]; abel
      have hII : B (secondFund B u b c x) (pd1 N a x) = 0 := by
        -- `II` is a multiple of `N` (part (1)), and `∂_aN ⊥ N`
        rw [secondFund_eq_smul_normal hB hBnd hu hN hdet hspan hNperp hε hNunit x b c]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [hB (N x) (pd1 N a x), normal_deriv_perp_normal hB hN hNunit x a, mul_zero]
      rw [hsplit, map_add, ContinuousLinearMap.add_apply, hII, add_zero, indCov]
      simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun s _ => by rw [inner_pd1_normal_deriv hB x a s]
    have e2 : fderiv ℝ N x (dir a) = pd1 N a x := rfl
    rw [e2, htang]
    ring
  simp only [shapeFormCovDeriv]
  have hi := key i j k
  have hj := key j i k
  have hsym : fderiv ℝ (fun y => pd2 u j k y) x (dir i)
      = fderiv ℝ (fun y => pd2 u i k y) x (dir j) := pd3_symm hu i j k
  rw [hsym] at hi
  -- `Γ` is symmetric in its lower indices, so the `Π_{sk}`-corrections agree
  have hΓ : ∀ s : Fin n, christoffelSecond B u s i j x = christoffelSecond B u s j i x := by
    intro s
    simp only [christoffelSecond, christoffelFirst]
    exact Finset.sum_congr rfl fun t _ => by rw [pd2_symm hu i j]
  have hcancel : ∑ s, christoffelSecond B u s i j x * shapeForm B u N s k x
      = ∑ s, christoffelSecond B u s j i x * shapeForm B u N s k x :=
    Finset.sum_congr rfl fun s _ => by rw [hΓ s]
  rw [hcancel]
  linarith [hi, hj]

/-- **Exercise 3.4.21/3.4.22, the converse half of part (4).**  Suppose the normal is
the *position field*, `N = R⁻¹·u` — that is, the immersion lands in the sphere of
radius `R` about the origin (`ε = +1`), respectively in the hyperboloid `H^n(R)`
(`ε = −1`).  Then `Π = R⁻¹·g` (the immersion is *totally umbilic*) and the induced
metric has **constant curvature `ε·R⁻²`**:
`R_{ijkl} = ε·R⁻²·(g_{jk}g_{il} − g_{ik}g_{jl})`,
giving `+R⁻²` for the sphere in `ℝ^{n+1}` and `−R⁻²` for `H^n(R)` in `ℝ^{n,1}`.

(Petersen's part (4) proper is the *existence* statement — that a metric of constant
curvature `±R⁻²` *admits* such an immersion — which needs Frobenius; see the module
`## Scope` note.) -/
theorem umbilic_constantCurvature (hB : ∀ v w : F, B v w = B w v)
    (hBnd : ∀ v : F, (∀ w, B v w = 0) → v = 0) (hu : ContDiff ℝ ∞ u) (hN : ContDiff ℝ ∞ N)
    (hdet : ∀ x : EuclideanSpace ℝ (Fin n), (gmat B u x).det ≠ 0)
    (hspan : ∀ x : EuclideanSpace ℝ (Fin n),
      Submodule.span ℝ (insert (N x) (Set.range fun i => pd1 u i x)) = ⊤)
    (hNperp : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n), B (N x) (pd1 u i x) = 0)
    {ε : ℝ} (hε : ε * ε = 1)
    (hNunit : ∀ x : EuclideanSpace ℝ (Fin n), B (N x) (N x) = ε)
    {R : ℝ} (hpos : ∀ x : EuclideanSpace ℝ (Fin n), N x = R⁻¹ • u x)
    (x : EuclideanSpace ℝ (Fin n)) (i j k l : Fin n) :
    curvatureLower B u i j k l x
      = ε * (R⁻¹ * R⁻¹)
          * (gm B u j k x * gm B u i l x - gm B u i k x * gm B u j l x) := by
  -- totally umbilic: `Π_{jk} = R⁻¹ g_{jk}`
  have humb : ∀ a b : Fin n, shapeForm B u N a b x = R⁻¹ * gm B u a b x := by
    intro a b
    have hfield : N = fun y => R⁻¹ • u y := funext hpos
    have hd : pd1 N a x = R⁻¹ • pd1 u a x := by
      simp only [pd1, hfield]
      have hcs : fderiv ℝ (fun y => R⁻¹ • u y) x = R⁻¹ • fderiv ℝ u x :=
        fderiv_const_smul (hu.contDiffAt.differentiableAt (by norm_cast)) R⁻¹
      rw [hcs]
      rfl
    simp only [shapeForm, gm, hd, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [gaussEquation_hypersurface hB hBnd hu hN hdet hspan hNperp hε hNunit x i j k l,
    humb j k, humb i l, humb i k, humb j l]
  ring

end Main

/-! ## The exercise, bundled

Exercise 3.4.21 is the Euclidean ambient (`B = ⟪·,·⟫`, `ε = +1`); Exercise 3.4.22 is
the Minkowski ambient (`B = minkowskiForm`, `ε = −1`, i.e. `|N|² = −1`).  Both are the
`Main` results above at the corresponding `(B, ε)`. -/

section Euclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A real inner product is nondegenerate. -/
theorem euclideanForm_nondegenerate (v : F) (h : ∀ w, (euclideanForm v) w = 0) : v = 0 :=
  inner_self_eq_zero.mp (h v)

/-- **Exercise 3.4.21 — fundamental theorem of hypersurface theory, necessity half.**
For a Riemannian immersion `u = (u¹,…,u^{n+1}) : Mⁿ ↪ ℝ^{n+1}` with unit normal `N`
(`⟪N,N⟫ = 1`) and second fundamental form `Π_{jk} = ⟪∇_j N, ∂_k⟫`:

* `(1)` the **Gauss formula** `∂U^i_j/∂xᵏ = ∑ₛ Γˢ_{kj}U^i_s − Π_{jk}Nⁱ`, where
  `U^i_k = ∂uⁱ/∂xᵏ`;
* `(2)` the **integrability conditions** are the Gauss and Codazzi equations,
  `R_{ijkl} = Π_{jk}Π_{il} − Π_{ik}Π_{jl}` and `(∇_iΠ)_{jk} = (∇_jΠ)_{ik}`.

Codimension one enters as `hspan`: `{N(x)} ∪ {∂ᵢu(x)}` spans `ℝ^{n+1}`.

(Parts `(3)` and `(4)` are the *existence* — Bonnet — statements: reconstructing an
immersion from a Gauss–Codazzi-compatible `(g, Π)`, and realizing a constant-curvature
metric in a sphere.  They need a Frobenius/integral-manifold PDE-existence theorem
absent from Mathlib and `PetersenLib`, and are not formalized here; the converse
direction of `(4)` is `umbilic_constantCurvature` at `ε = 1`.) -/
theorem exercise3_4_21 {u N : EuclideanSpace ℝ (Fin n) → F} (hu : ContDiff ℝ ∞ u)
    (hN : ContDiff ℝ ∞ N)
    (hdet : ∀ x, (gmat (euclideanForm (F := F)) u x).det ≠ 0)
    (hspan : ∀ x, Submodule.span ℝ (insert (N x) (Set.range fun i => pd1 u i x)) = ⊤)
    (hNperp : ∀ x i, ⟪N x, pd1 u i x⟫_ℝ = 0) (hNunit : ∀ x, ⟪N x, N x⟫_ℝ = 1) :
    (∀ (x : EuclideanSpace ℝ (Fin n)) (k j : Fin n),
        pd2 u k j x = (∑ s, christoffelSecond euclideanForm u s k j x • pd1 u s x)
          - shapeForm euclideanForm u N j k x • N x)
    ∧ (∀ (x : EuclideanSpace ℝ (Fin n)) (i j k l : Fin n),
        curvatureLower euclideanForm u i j k l x
          = shapeForm euclideanForm u N j k x * shapeForm euclideanForm u N i l x
            - shapeForm euclideanForm u N i k x * shapeForm euclideanForm u N j l x)
    ∧ (∀ (x : EuclideanSpace ℝ (Fin n)) (i j k : Fin n),
        shapeFormCovDeriv euclideanForm u N i j k x
          = shapeFormCovDeriv euclideanForm u N j i k x) := by
  have hε : (1 : ℝ) * 1 = 1 := by norm_num
  refine ⟨fun x k j => ?_, fun x i j k l => ?_, fun x i j k => ?_⟩
  · have := gaussFormula euclideanForm_symm euclideanForm_nondegenerate hu hN hdet hspan
      hNperp hε hNunit x k j
    simpa using this
  · have := gaussEquation_hypersurface euclideanForm_symm euclideanForm_nondegenerate hu hN
      hdet hspan hNperp hε hNunit x i j k l
    simpa using this
  · exact codazziEquation euclideanForm_symm euclideanForm_nondegenerate hu hN hdet hspan
      hNperp hε hNunit x i j k

end Euclidean

section Minkowski

variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂]

/-- The Minkowski form is nondegenerate: pair `v` against its time-reflection. -/
theorem minkowskiForm_nondegenerate (v : F₁ × F₂)
    (h : ∀ w, (minkowskiForm F₁ F₂ v) w = 0) : v = 0 := by
  by_contra hv
  exact minkowskiForm_self_flip_ne_zero F₁ F₂ hv (h (v.1, -v.2))

/-- **Exercise 3.4.22.**  Exercise 3.4.21 repeated for an immersion
`u : Mⁿ ↪ ℝ^{n,1}` into Minkowski space, with a normal `N` satisfying `|N|² = −1`.
Everything is the same except the sign `ε = −1`, which flips the Gauss equation:

* `(1)` the **Gauss formula** `∂²_{kj}u = ∑ₛ Γˢ_{kj}∂ₛu + Π_{jk}·N`;
* `(2)` the **Gauss equation** `R_{ijkl} = −(Π_{jk}Π_{il} − Π_{ik}Π_{jl})` and the
  **Codazzi equation** `(∇_iΠ)_{jk} = (∇_jΠ)_{ik}` (which is sign-independent).

Taking `F₂ = ℝ` gives Petersen's `ℝ^{n,1}`.  The *local characterization of the
hyperbolic spaces* `H^n(R)` is the `ε = −1` case of `umbilic_constantCurvature`: an
immersion with `N = ±R⁻¹·u` has constant curvature `−R⁻²`.

(As in `exercise3_4_21`, the existence half — that every metric of constant curvature
`−R⁻²` is locally realized this way — needs Frobenius and is not formalized.) -/
theorem exercise3_4_22 {u N : EuclideanSpace ℝ (Fin n) → F₁ × F₂} (hu : ContDiff ℝ ∞ u)
    (hN : ContDiff ℝ ∞ N)
    (hdet : ∀ x, (gmat (minkowskiForm F₁ F₂) u x).det ≠ 0)
    (hspan : ∀ x, Submodule.span ℝ (insert (N x) (Set.range fun i => pd1 u i x)) = ⊤)
    (hNperp : ∀ x i, minkowskiForm F₁ F₂ (N x) (pd1 u i x) = 0)
    (hNunit : ∀ x, minkowskiForm F₁ F₂ (N x) (N x) = -1) :
    (∀ (x : EuclideanSpace ℝ (Fin n)) (k j : Fin n),
        pd2 u k j x = (∑ s, christoffelSecond (minkowskiForm F₁ F₂) u s k j x • pd1 u s x)
          + shapeForm (minkowskiForm F₁ F₂) u N j k x • N x)
    ∧ (∀ (x : EuclideanSpace ℝ (Fin n)) (i j k l : Fin n),
        curvatureLower (minkowskiForm F₁ F₂) u i j k l x
          = -(shapeForm (minkowskiForm F₁ F₂) u N j k x * shapeForm (minkowskiForm F₁ F₂) u N i l x
            - shapeForm (minkowskiForm F₁ F₂) u N i k x
              * shapeForm (minkowskiForm F₁ F₂) u N j l x))
    ∧ (∀ (x : EuclideanSpace ℝ (Fin n)) (i j k : Fin n),
        shapeFormCovDeriv (minkowskiForm F₁ F₂) u N i j k x
          = shapeFormCovDeriv (minkowskiForm F₁ F₂) u N j i k x) := by
  have hε : (-1 : ℝ) * (-1) = 1 := by norm_num
  refine ⟨fun x k j => ?_, fun x i j k l => ?_, fun x i j k => ?_⟩
  · have := gaussFormula (minkowskiForm_comm F₁ F₂) (minkowskiForm_nondegenerate) hu hN hdet
      hspan hNperp hε hNunit x k j
    simpa using this
  · have := gaussEquation_hypersurface (minkowskiForm_comm F₁ F₂) (minkowskiForm_nondegenerate)
      hu hN hdet hspan hNperp hε hNunit x i j k l
    simpa using this
  · exact codazziEquation (minkowskiForm_comm F₁ F₂) (minkowskiForm_nondegenerate) hu hN hdet
      hspan hNperp hε hNunit x i j k

end Minkowski

end Hypersurface

/-- **Exercise 3.4.21** (Petersen `rem:pet-ch3-ex-21`), necessity half: for a
Riemannian immersion `Mⁿ ↪ ℝ^{n+1}` with unit normal `N`, the Gauss formula
`∂U^i_j/∂xᵏ = ∑ₛ Γˢ_{kj}U^i_s − Π_{jk}Nⁱ` holds (part (1)) and the integrability
conditions are the Gauss and Codazzi equations (part (2)). -/
alias exercise3_4_21 := Hypersurface.exercise3_4_21

/-- **Exercise 3.4.22** (Petersen `rem:pet-ch3-ex-22`): Exercise 3.4.21 for an
immersion `Mⁿ ↪ ℝ^{n,1}` into Minkowski space with `|N|² = −1`; the Gauss equation
acquires a sign, the Codazzi equation does not. -/
alias exercise3_4_22 := Hypersurface.exercise3_4_22

end PetersenLib
