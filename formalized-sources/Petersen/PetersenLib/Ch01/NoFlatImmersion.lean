import PetersenLib.Ch01.Sphere
import PetersenLib.Ch01.HyperbolicSpace
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# No flat Riemannian immersion into a space form

Petersen §1.6, Exercises 1.6.20 (5) and 1.6.21 (5): *there is no Riemannian
immersion of an open set `U ⊆ ℝⁿ` into `Sⁿ` (resp. into `Hⁿ`) when `n ≥ 2`*.

## The argument

Petersen's hint proves this by comparing angles of equilateral triangles.
That route needs to know that a local isometry carries straight segments to
*geodesics* of the target — a fact of Chapter 5, not of Chapter 1.  We give
instead a self-contained proof that stays strictly inside Chapter 1: it is the
computation of the second fundamental form of an umbilic hypersurface, run
backwards.

Let `β` be a symmetric (continuous) bilinear form on an `(n+1)`-dimensional
space `E` — the Euclidean inner product for `Sⁿ ⊆ ℝⁿ⁺¹`, the Minkowski form
for `Hⁿ ⊆ ℝ^{n,1}` — and let `G : U → E` be the immersion read in the ambient
space, so that

* `β (G x) (G x) = c` (a nonzero constant: `c = 1` on the unit sphere,
  `c = -1` on the unit hyperboloid), and
* `β (∂ᵢG) (∂ⱼG) = δᵢⱼ` (the immersion is isometric for the *flat* metric).

Differentiating the first identity gives `β (∂ᵢG) G = 0`; differentiating the
second and combining it with the symmetry of second partials gives the
classical cancellation

`A(v,u,w) := β (∂ᵥ∂ᵤG) (∂_w G) = -A(v,w,u) = -A(u,v,w) = ⋯ = -A(v,u,w)`,

hence `A ≡ 0`: the second derivative of `G` is `β`-orthogonal to the tangent
directions.  Since `∂₁G, …, ∂ₙG, G` is a `β`-orthogonal basis of `E`
(here `dim E = n + 1` is essential — a *flat torus does* sit isometrically in
`S³`), the second derivative is a multiple of the normal `G`, and pairing with
`G` computes the multiple:

`∂ᵤ∂ᵥ G = -(⟪u,v⟫ / c) • G`  (`fderiv_fderiv_eq_smul_of_isometric`).

This is an *overdetermined* system as soon as `n ≥ 2`, and one more
differentiation exposes it: the map `Φ y := ∂_{e₂} G y` has derivative
`v ↦ -c⁻¹⟪e₂,v⟫ • G y`, whose own derivative `(w,v) ↦ -c⁻¹⟪e₂,v⟫ • ∂_w G` is
*not* symmetric in `(v,w)` unless `∂_{e₁}G = 0` — which is impossible, because
`β (∂_{e₁}G) (∂_{e₁}G) = 1`.  The symmetry of the second derivative of `Φ`
therefore yields the contradiction.

The `n ≥ 2` hypothesis enters exactly once, in the choice of two distinct
basis directions `e₁ ≠ e₂`; for `n = 1` no contradiction is available, and
indeed great circles and hyperbolas *are* isometric immersions of `ℝ`.

## Main results

* `eq_zero_of_bilin_orthogonalFamily`: a vector `β`-orthogonal to a
  `β`-orthogonal family of `dim E` vectors with nonzero `β`-squares is zero.
* `no_isometricImmersion_flat_to_umbilic`: the ambient core lemma above.
* `no_isometricImmersion_flat_to_sphere`,
  `no_isometricImmersion_flat_to_hyperboloid`: the two instances, phrased with
  the manifold data of `sphereMetricUnit` and `hyperbolicSpace`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.6, Exercises 1.6.20,
1.6.21.
-/

open Metric Module Set
open scoped ContDiff Manifold Topology InnerProductSpace

noncomputable section

namespace PetersenLib

section OrthogonalFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Math.** In an `(m+1)`-dimensional space carrying a bilinear form `β`, a
family `v` of `m+1` vectors that is `β`-orthogonal and has nonzero
`β`-squares is a basis, and pairing against it detects vectors: a `z` with
`β z (v k) = 0` for every `k` vanishes.  (No nondegeneracy of `β` is assumed:
the invertible Gram matrix of the family supplies it.) -/
theorem eq_zero_of_bilin_orthogonalFamily {m : ℕ} (hdim : finrank ℝ E = m + 1)
    (β : E →L[ℝ] E →L[ℝ] ℝ) (v : Fin (m + 1) → E)
    (horth : ∀ k l, k ≠ l → β (v k) (v l) = 0) (hnz : ∀ k, β (v k) (v k) ≠ 0)
    {z : E} (hz : ∀ k, β z (v k) = 0) : z = 0 := by
  classical
  have hli : LinearIndependent ℝ v := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    have h : ∑ j ∈ s, g j * β (v j) (v i) = 0 := by
      have := congrArg (fun w : E => β.flip (v i) w) hsum
      simpa [map_sum, ContinuousLinearMap.flip_apply, smul_eq_mul] using this
    have h2 : ∑ j ∈ s, g j * β (v j) (v i) = g i * β (v i) (v i) :=
      Finset.sum_eq_single_of_mem i hi fun j _ hji => by rw [horth j i hji, mul_zero]
    rw [h2] at h
    exact (mul_eq_zero.mp h).resolve_right (hnz i)
  have hcard : Fintype.card (Fin (m + 1)) = finrank ℝ E := by simp [hdim]
  set b := basisOfLinearIndependentOfCardEqFinrank hli hcard with hb_def
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hsum : ∑ k, b.repr z k • v k = z := by
    conv_rhs => rw [← b.sum_repr z]
    simp [hb]
  have hrepr : ∀ i, b.repr z i = 0 := by
    intro i
    have h : ∑ k, b.repr z k * β (v k) (v i) = 0 := by
      have := congrArg (fun w : E => β.flip (v i) w) hsum
      simp only [map_sum, map_smul, smul_eq_mul, ContinuousLinearMap.flip_apply] at this
      rw [this]
      exact hz i
    have h2 : ∑ k, b.repr z k * β (v k) (v i) = b.repr z i * β (v i) (v i) :=
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hji => by
        rw [horth j i hji, mul_zero]
    rw [h2] at h
    exact (mul_eq_zero.mp h).resolve_right (hnz i)
  have hz0 : b.repr z = 0 := by ext i; exact hrepr i
  simpa using congrArg b.repr.symm hz0

end OrthogonalFamily

section AmbientCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {β : E →L[ℝ] E →L[ℝ] ℝ} {c : ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
  {G : EuclideanSpace ℝ (Fin n) → E}

/-- **Math.** The normal relation: if `β(G, G)` is constant on the open set
`U`, then every first derivative of `G` is `β`-orthogonal to `G` — the curve
stays on the level set `{β(·,·) = c}`, so its velocity is tangent to it. -/
theorem bilin_fderiv_self_eq_zero (hβ : ∀ u v : E, β u v = β v u) (hU : IsOpen U)
    (hG : ∀ x ∈ U, ContDiffAt ℝ ∞ G x) (hGG : ∀ x ∈ U, β (G x) (G x) = c) :
    ∀ x ∈ U, ∀ u, β (fderiv ℝ G x u) (G x) = 0 := by
  intro x hx u
  have hGx : HasFDerivAt G (fderiv ℝ G x) x :=
    ((hG x hx).differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun y => β (G y)) (β.comp (fderiv ℝ G x)) x :=
    β.hasFDerivAt.comp x hGx
  have h2 : HasFDerivAt (fun y => β (G y) (G y))
      ((β (G x)).comp (fderiv ℝ G x) + (β.comp (fderiv ℝ G x)).flip (G x)) x :=
    h1.clm_apply hGx
  have h3 : HasFDerivAt (fun y => β (G y) (G y))
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x := by
    refine (hasFDerivAt_const c x).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy using hGG y hy
  have h4 := h2.unique h3
  have h5 := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L u) h4
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply] at h5
  rw [hβ (G x) (fderiv ℝ G x u)] at h5
  linarith

/-- **Math.** Second-order form of the normal relation: pairing the second
derivative of `G` with the normal `G` recovers (minus) the flat metric.  This
is the statement that the second fundamental form of the level set
`{β(·,·) = c}` is `-1/c` times its first fundamental form (umbilicity). -/
theorem bilin_fderiv_fderiv_self (hβ : ∀ u v : E, β u v = β v u) (hU : IsOpen U)
    (hG : ∀ x ∈ U, ContDiffAt ℝ ∞ G x) (hGG : ∀ x ∈ U, β (G x) (G x) = c)
    (hiso : ∀ x ∈ U, ∀ u v : EuclideanSpace ℝ (Fin n),
      β (fderiv ℝ G x u) (fderiv ℝ G x v) = ⟪u, v⟫_ℝ) :
    ∀ x ∈ U, ∀ u v, β (fderiv ℝ (fderiv ℝ G) x v u) (G x) = -⟪u, v⟫_ℝ := by
  intro x hx u v
  have hnormal := bilin_fderiv_self_eq_zero hβ hU hG hGG
  have hGx : HasFDerivAt G (fderiv ℝ G x) x :=
    ((hG x hx).differentiableAt (by simp)).hasFDerivAt
  have hDx : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x :=
    (((hG x hx).fderiv_right (m := 1) (by norm_cast)).differentiableAt one_ne_zero).hasFDerivAt
  have hu : HasFDerivAt (fun y => fderiv ℝ G y u)
      ((ContinuousLinearMap.apply ℝ E u).comp (fderiv ℝ (fderiv ℝ G) x)) x :=
    (ContinuousLinearMap.apply ℝ E u).hasFDerivAt.comp x hDx
  have h1 : HasFDerivAt (fun y => β (fderiv ℝ G y u))
      (β.comp ((ContinuousLinearMap.apply ℝ E u).comp (fderiv ℝ (fderiv ℝ G) x))) x :=
    β.hasFDerivAt.comp x hu
  have h2 : HasFDerivAt (fun y => β (fderiv ℝ G y u) (G y))
      ((β (fderiv ℝ G x u)).comp (fderiv ℝ G x)
        + (β.comp ((ContinuousLinearMap.apply ℝ E u).comp
            (fderiv ℝ (fderiv ℝ G) x))).flip (G x)) x :=
    h1.clm_apply hGx
  have h3 : HasFDerivAt (fun y => β (fderiv ℝ G y u) (G y))
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x := by
    refine (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy using hnormal y hy u
  have h4 := h2.unique h3
  have h5 := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) h4
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.apply_apply] at h5
  rw [hiso x hx u v] at h5
  linarith

/-- **Math.** The tangential part of the second derivative vanishes:
`β (∂ᵥ∂ᵤG) (∂_w G) = 0`.  This is the coordinate-free form of the vanishing of
the Christoffel symbols of a flat isometric immersion, obtained from the
antisymmetry `A(v,u,w) = -A(v,w,u)` (differentiate `β(∂ᵤG, ∂_wG) = δᵤ_w`)
together with the symmetry `A(v,u,w) = A(u,v,w)` of second partials. -/
theorem bilin_fderiv_fderiv_fderiv_eq_zero (hβ : ∀ u v : E, β u v = β v u) (hU : IsOpen U)
    (hG : ∀ x ∈ U, ContDiffAt ℝ ∞ G x)
    (hiso : ∀ x ∈ U, ∀ u v : EuclideanSpace ℝ (Fin n),
      β (fderiv ℝ G x u) (fderiv ℝ G x v) = ⟪u, v⟫_ℝ) :
    ∀ x ∈ U, ∀ u v w, β (fderiv ℝ (fderiv ℝ G) x v u) (fderiv ℝ G x w) = 0 := by
  -- the derivative of the constant function `y ↦ β (∂ᵤG y) (∂_w G y) = ⟪u,w⟫`
  have hA : ∀ x ∈ U, ∀ u w v,
      β (fderiv ℝ (fderiv ℝ G) x v u) (fderiv ℝ G x w)
        + β (fderiv ℝ G x u) (fderiv ℝ (fderiv ℝ G) x v w) = 0 := by
    intro x hx u w v
    have hDx : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x :=
      (((hG x hx).fderiv_right (m := 1) (by norm_cast)).differentiableAt one_ne_zero).hasFDerivAt
    have hu : HasFDerivAt (fun y => fderiv ℝ G y u)
        ((ContinuousLinearMap.apply ℝ E u).comp (fderiv ℝ (fderiv ℝ G) x)) x :=
      (ContinuousLinearMap.apply ℝ E u).hasFDerivAt.comp x hDx
    have hw : HasFDerivAt (fun y => fderiv ℝ G y w)
        ((ContinuousLinearMap.apply ℝ E w).comp (fderiv ℝ (fderiv ℝ G) x)) x :=
      (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp x hDx
    have h1 : HasFDerivAt (fun y => β (fderiv ℝ G y u))
        (β.comp ((ContinuousLinearMap.apply ℝ E u).comp (fderiv ℝ (fderiv ℝ G) x))) x :=
      β.hasFDerivAt.comp x hu
    have h2 : HasFDerivAt (fun y => β (fderiv ℝ G y u) (fderiv ℝ G y w))
        ((β (fderiv ℝ G x u)).comp
            ((ContinuousLinearMap.apply ℝ E w).comp (fderiv ℝ (fderiv ℝ G) x))
          + (β.comp ((ContinuousLinearMap.apply ℝ E u).comp
              (fderiv ℝ (fderiv ℝ G) x))).flip (fderiv ℝ G x w)) x :=
      h1.clm_apply hw
    have h3 : HasFDerivAt (fun y => β (fderiv ℝ G y u) (fderiv ℝ G y w))
        (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x := by
      refine (hasFDerivAt_const (⟪u, w⟫_ℝ) x).congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds hx] with y hy using hiso y hy u w
    have h4 := h2.unique h3
    have h5 := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) h4
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply,
      ContinuousLinearMap.apply_apply] at h5
    linarith
  intro x hx u v w
  have hsymm2 : ∀ a b : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fderiv ℝ G) x a b = fderiv ℝ (fderiv ℝ G) x b a :=
    (hG x hx).isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  -- the six-term cyclic cancellation
  have R : ∀ a b d : EuclideanSpace ℝ (Fin n),
      β (fderiv ℝ (fderiv ℝ G) x a b) (fderiv ℝ G x d)
        = -β (fderiv ℝ (fderiv ℝ G) x a d) (fderiv ℝ G x b) := by
    intro a b d
    have h := hA x hx b d a
    rw [hβ (fderiv ℝ G x b) (fderiv ℝ (fderiv ℝ G) x a d)] at h
    linarith
  have S : ∀ a b d : EuclideanSpace ℝ (Fin n),
      β (fderiv ℝ (fderiv ℝ G) x a b) (fderiv ℝ G x d)
        = β (fderiv ℝ (fderiv ℝ G) x b a) (fderiv ℝ G x d) := by
    intro a b d; rw [hsymm2 a b]
  have e1 := R v u w
  have e2 := S v w u
  have e3 := R w v u
  have e4 := S w u v
  have e5 := R u w v
  have e6 := S u v w
  linarith

/-- **Math.** The **normal form of the second derivative** of a flat isometric
immersion into the level set `{β(·,·) = c}` of a symmetric bilinear form on an
`(n+1)`-dimensional space: `∂ᵥ∂ᵤ G = -(⟪u,v⟫ / c) • G`.  For the unit sphere
(`c = 1`, `β = ⟪·,·⟫`) this is `∂ᵢ∂ⱼG = -δᵢⱼ G`; for the unit hyperboloid
(`c = -1`, `β = η`) it is `∂ᵢ∂ⱼG = +δᵢⱼ G`. -/
theorem fderiv_fderiv_eq_smul_of_isometric (hdim : finrank ℝ E = n + 1)
    (hβ : ∀ u v : E, β u v = β v u) (hc : c ≠ 0) (hU : IsOpen U)
    (hG : ∀ x ∈ U, ContDiffAt ℝ ∞ G x) (hGG : ∀ x ∈ U, β (G x) (G x) = c)
    (hiso : ∀ x ∈ U, ∀ u v : EuclideanSpace ℝ (Fin n),
      β (fderiv ℝ G x u) (fderiv ℝ G x v) = ⟪u, v⟫_ℝ) :
    ∀ x ∈ U, ∀ u v, fderiv ℝ (fderiv ℝ G) x v u = (-(⟪u, v⟫_ℝ / c)) • G x := by
  intro x hx u v
  have hnormal := bilin_fderiv_self_eq_zero hβ hU hG hGG
  have hsecond := bilin_fderiv_fderiv_self hβ hU hG hGG hiso
  have htang := bilin_fderiv_fderiv_fderiv_eq_zero hβ hU hG hiso
  set e := EuclideanSpace.basisFun (Fin n) ℝ with he_def
  have hortho : ∀ i j : Fin n, ⟪(e i : EuclideanSpace ℝ (Fin n)), e j⟫_ℝ
      = if i = j then 1 else 0 := fun i j => orthonormal_iff_ite.mp e.orthonormal i j
  -- the `β`-orthogonal frame `∂₁G, …, ∂ₙG, G`
  set V : Fin (n + 1) → E := Fin.snoc (fun i : Fin n => fderiv ℝ G x (e i)) (G x) with hV_def
  have hVcast : ∀ i : Fin n, V i.castSucc = fderiv ℝ G x (e i) := fun i => by
    simp [hV_def]
  have hVlast : V (Fin.last n) = G x := by simp [hV_def]
  have horth : ∀ k l, k ≠ l → β (V k) (V l) = 0 := by
    intro k l hkl
    induction k using Fin.lastCases with
    | last =>
      induction l using Fin.lastCases with
      | last => exact absurd rfl hkl
      | cast j =>
        rw [hVlast, hVcast j, hβ (G x) _]
        exact hnormal x hx (e j)
    | cast i =>
      induction l using Fin.lastCases with
      | last => rw [hVcast i, hVlast]; exact hnormal x hx (e i)
      | cast j =>
        have hij : i ≠ j := fun h => hkl (by rw [h])
        rw [hVcast i, hVcast j, hiso x hx (e i) (e j), hortho i j, if_neg hij]
  have hnzV : ∀ k, β (V k) (V k) ≠ 0 := by
    intro k
    induction k using Fin.lastCases with
    | last => rw [hVlast, hGG x hx]; exact hc
    | cast i =>
      rw [hVcast i, hiso x hx (e i) (e i), hortho i i, if_pos rfl]
      exact one_ne_zero
  -- the candidate error term is `β`-orthogonal to the whole frame, hence zero
  have hz : ∀ k, β (fderiv ℝ (fderiv ℝ G) x v u + (⟪u, v⟫_ℝ / c) • G x) (V k) = 0 := by
    intro k
    induction k using Fin.lastCases with
    | last =>
      rw [hVlast]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hsecond x hx u v, hGG x hx]
      field_simp
      ring
    | cast i =>
      rw [hVcast i]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [htang x hx u v (e i), hβ (G x) (fderiv ℝ G x (e i)), hnormal x hx (e i)]
      ring
  have hzero := eq_zero_of_bilin_orthogonalFamily hdim β V horth hnzV hz
  rw [add_eq_zero_iff_eq_neg, ← neg_smul] at hzero
  exact hzero

/-- **Math.** Petersen §1.6, Exercises 1.6.20 (5) / 1.6.21 (5), ambient core.
For `n ≥ 2` there is **no isometric immersion of an open set of flat `ℝⁿ` into
the level set `{β(·,·) = c}`** (`c ≠ 0`) of a symmetric bilinear form on an
`(n+1)`-dimensional space `E`: no `G : U → E` can satisfy both
`β (G, G) = c` and `β (∂ᵤG, ∂ᵥG) = ⟪u, v⟫` at every point of `U`.

Applied to `E = ℝⁿ⁺¹`, `β = ⟪·,·⟫`, `c = 1` this rules out a Riemannian
immersion into `Sⁿ`; applied to `E = ℝ^{n,1}`, `β = η`, `c = -1` it rules out
one into `Hⁿ`.  The `(n+1)`-dimensionality of `E` is essential: in higher
codimension flat submanifolds of the sphere exist (the Clifford torus in
`S³`). -/
theorem no_isometricImmersion_flat_to_umbilic (hn : 2 ≤ n) (hdim : finrank ℝ E = n + 1)
    (hβ : ∀ u v : E, β u v = β v u) (hc : c ≠ 0) (hU : IsOpen U) (hne : U.Nonempty)
    (hG : ∀ x ∈ U, ContDiffAt ℝ ∞ G x) (hGG : ∀ x ∈ U, β (G x) (G x) = c)
    (hiso : ∀ x ∈ U, ∀ u v : EuclideanSpace ℝ (Fin n),
      β (fderiv ℝ G x u) (fderiv ℝ G x v) = ⟪u, v⟫_ℝ) :
    False := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hform := fderiv_fderiv_eq_smul_of_isometric hdim hβ hc hU hG hGG hiso
  set e := EuclideanSpace.basisFun (Fin n) ℝ with he_def
  have hortho : ∀ i j : Fin n, ⟪(e i : EuclideanSpace ℝ (Fin n)), e j⟫_ℝ
      = if i = j then 1 else 0 := fun i j => orthonormal_iff_ite.mp e.orthonormal i j
  -- two distinct flat directions — the only place `n ≥ 2` is used
  set i₁ : Fin n := ⟨0, by omega⟩ with hi₁_def
  set i₂ : Fin n := ⟨1, by omega⟩ with hi₂_def
  have hi : i₂ ≠ i₁ := by
    simp only [hi₁_def, hi₂_def, ne_eq, Fin.mk.injEq]
    omega
  set e₁ : EuclideanSpace ℝ (Fin n) := e i₁ with he₁_def
  set e₂ : EuclideanSpace ℝ (Fin n) := e i₂ with he₂_def
  have h₂₂ : ⟪e₂, e₂⟫_ℝ = 1 := by rw [he₂_def, hortho i₂ i₂, if_pos rfl]
  have h₂₁ : ⟪e₂, e₁⟫_ℝ = 0 := by rw [he₂_def, he₁_def, hortho i₂ i₁, if_neg hi]
  -- `Φ y = ∂_{e₂} G y` has derivative `v ↦ -c⁻¹ ⟪e₂,v⟫ • G y`
  set C : E →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] E) :=
    ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin n)) E ((-c⁻¹) • innerSL ℝ e₂)
    with hC_def
  have hCapply : ∀ (z : E) (v : EuclideanSpace ℝ (Fin n)),
      C z v = (-(⟪e₂, v⟫_ℝ / c)) • z := by
    intro z v
    simp only [hC_def, ContinuousLinearMap.smulRightL_apply_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have hΦ : ∀ y ∈ U, HasFDerivAt (fun z => fderiv ℝ G z e₂) (C (G y)) y := by
    intro y hy
    have hDy : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) y) y :=
      (((hG y hy).fderiv_right (m := 1) (by norm_cast)).differentiableAt one_ne_zero).hasFDerivAt
    have h := (ContinuousLinearMap.apply ℝ E e₂).hasFDerivAt.comp y hDy
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    rw [hform y hy e₂ v, hCapply (G y) v]
  have hΦ' : HasFDerivAt (fun y => C (G y)) (C.comp (fderiv ℝ G x₀)) x₀ :=
    C.hasFDerivAt.comp x₀ (((hG x₀ hx₀).differentiableAt (by simp)).hasFDerivAt)
  have hsym := second_derivative_symmetric_of_eventually
    (f := fun z => fderiv ℝ G z e₂) (f' := fun y => C (G y))
    (f'' := C.comp (fderiv ℝ G x₀))
    (by filter_upwards [hU.mem_nhds hx₀] with y hy using hΦ y hy) hΦ' e₁ e₂
  simp only [ContinuousLinearMap.comp_apply] at hsym
  rw [hCapply (fderiv ℝ G x₀ e₁) e₂, hCapply (fderiv ℝ G x₀ e₂) e₁, h₂₂, h₂₁] at hsym
  -- `-(1/c) • ∂_{e₁}G = 0`, so `∂_{e₁}G = 0` — impossible for an isometry
  have hcne : -(1 / c) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, one_div, inv_eq_zero]
    exact hc
  have hDe₁ : fderiv ℝ G x₀ e₁ = 0 := by
    have h0 : (-(1 / c)) • fderiv ℝ G x₀ e₁ = 0 := by
      rw [hsym]
      simp
    exact (smul_eq_zero.mp h0).resolve_left hcne
  have h11 := hiso x₀ hx₀ e₁ e₁
  rw [hDe₁, he₁_def, hortho i₁ i₁, if_pos rfl] at h11
  simp at h11

end AmbientCore

/-! ## The two space-form instances

`Sⁿ ⊆ ℝⁿ⁺¹` is the level set `⟪x,x⟫ = 1` of the Euclidean inner product, and
`Hⁿ ⊆ ℝ^{n,1}` is (the upper branch of) the level set `η(x,x) = -1` of the
Minkowski form; both ambient spaces have dimension `n + 1`, and both induced
metrics are, by definition, the pullbacks of the ambient form along the
inclusion.  So both exercises are instances of
`no_isometricImmersion_flat_to_umbilic`, once the manifold differential
`mfderiv` of the immersion is transported to the ambient Fréchet derivative of
`ι ∘ F` by the chain rule. -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Math.** Petersen §1.6, Exercise 1.6.20 (5): for `n ≥ 2` there is **no
Riemannian immersion of an open set `U ⊆ ℝⁿ` into the unit sphere `Sⁿ`**.  The
immersion is a smooth map `F` whose differential is isometric from the flat
metric to `sphereMetricUnit` (injectivity of `DF` is then automatic). -/
theorem no_isometricImmersion_flat_to_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (hn : 2 ≤ n) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hne : U.Nonempty)
    (F : EuclideanSpace ℝ (Fin n) → sphere (0 : E) 1)
    (hF : ∀ x ∈ U, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ F x)
    (hFiso : ∀ x ∈ U, ∀ u v : EuclideanSpace ℝ (Fin n),
      ⟪u, v⟫_ℝ = (sphereMetricUnit (n := n) E).metricInner (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) F x u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) F x v)) :
    False := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ (K := ℝ) (V := E) n
  -- read the immersion in the ambient space `E`
  have hGsm : ∀ x ∈ U, ContDiffAt ℝ ∞ (fun y => ((F y : sphere (0 : E) 1) : E)) x := by
    intro x hx
    exact contMDiffAt_iff_contDiffAt.mp
      ((contMDiff_coe_sphere (E := E) (n := n) (F x)).comp x (hF x hx))
  -- chain rule: `D(ι ∘ F) = Dι ∘ DF`
  have hmf : ∀ x ∈ U, ∀ u, fderiv ℝ (fun y => ((F y : sphere (0 : E) 1) : E)) x u
      = mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (F x)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) F x u) := by
    intro x hx u
    have h := mfderiv_comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (I' := 𝓡 n) (I'' := 𝓘(ℝ, E))
      (g := ((↑) : sphere (0 : E) 1 → E)) (f := F) (x := x)
      ((contMDiff_coe_sphere (m := 1) (F x)).mdifferentiableAt one_ne_zero)
      ((hF x hx).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at h
    exact congrArg (fun L => L u) h
  refine no_isometricImmersion_flat_to_umbilic (E := E) (β := innerSL ℝ) (c := 1)
    hn (Fact.out) (fun u v => real_inner_comm v u) one_ne_zero hU hne hGsm ?_ ?_
  · intro x hx
    have hnorm : ‖((F x : sphere (0 : E) 1) : E)‖ = 1 := mem_sphere_zero_iff_norm.mp (F x).2
    show ⟪((F x : sphere (0 : E) 1) : E), ((F x : sphere (0 : E) 1) : E)⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow]
  · intro x hx u v
    show ⟪fderiv ℝ (fun y => ((F y : sphere (0 : E) 1) : E)) x u,
        fderiv ℝ (fun y => ((F y : sphere (0 : E) 1) : E)) x v⟫_ℝ = ⟪u, v⟫_ℝ
    rw [hmf x hx u, hmf x hx v, ← sphereMetricUnit_apply]
    exact (hFiso x hx u v).symm

end Sphere

section Hyperboloid

/-- **Math.** Petersen §1.6, Exercise 1.6.21 (5): for `n ≥ 2` there is **no
Riemannian immersion of an open set `U ⊆ ℝⁿ` into hyperbolic space `Hⁿ`**.
Same proof as for the sphere, with the Minkowski form in place of the inner
product and `c = -1` in place of `c = 1`: the sign of the ambient form is
irrelevant to the obstruction, only its nondegeneracy on the normal is. -/
theorem no_isometricImmersion_flat_to_hyperboloid {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hne : U.Nonempty)
    (F : EuclideanSpace ℝ (Fin n) → hyperboloid n 1)
    (hF : ∀ x ∈ U, ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ F x)
    (hFiso : ∀ x ∈ U, ∀ u v : EuclideanSpace ℝ (Fin n),
      ⟪u, v⟫_ℝ = (hyperbolicSpace n 1).metricInner (F x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F x u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F x v)) :
    False := by
  have hGsm : ∀ x ∈ U, ContDiffAt ℝ ∞ (fun y => hyperboloidInclusion n 1 (F y)) x := by
    intro x hx
    exact contMDiffAt_iff_contDiffAt.mp
      (((hyperboloidInclusion_contMDiff n 1) (F x)).comp x (hF x hx))
  have hmf : ∀ x ∈ U, ∀ u, fderiv ℝ (fun y => hyperboloidInclusion n 1 (F y)) x u
      = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
          (hyperboloidInclusion n 1) (F x)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F x u) := by
    intro x hx u
    have h := mfderiv_comp (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ))
      (g := hyperboloidInclusion n 1) (f := F) (x := x)
      ((hyperboloidInclusion_contMDiff n 1).mdifferentiableAt (by simp))
      ((hF x hx).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at h
    exact congrArg (fun L => L u) h
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) = n + 1 := by
    simp [Module.finrank_prod]
  refine no_isometricImmersion_flat_to_umbilic
    (E := EuclideanSpace ℝ (Fin n) × ℝ) (β := minkowskiForm (EuclideanSpace ℝ (Fin n)) ℝ)
    (c := -1) hn hdim (fun u v => minkowskiForm_comm _ _ u v) (by norm_num) hU hne hGsm ?_ ?_
  · intro x hx
    have h := (F x).2.1
    simp only [hyperboloidInclusion, minkowskiForm_apply, real_inner_self_eq_norm_sq,
      Real.norm_eq_abs, sq_abs]
    linarith
  · intro x hx u v
    rw [hmf x hx u, hmf x hx v, ← hyperbolicSpace_metricInner]
    exact (hFiso x hx u v).symm

end Hyperboloid

end PetersenLib
