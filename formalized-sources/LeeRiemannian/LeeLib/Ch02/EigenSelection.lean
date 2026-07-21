/-
Copyright (c) 2026 OpenGA-Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth selection of a simple eigenvalue and its eigenvector

A self-adjoint operator `S₀` on a finite-dimensional real inner product space with a **simple**
eigenvalue `l₀` (eigenvector `v₀`) determines, for every nearby operator `S`, a distinguished
eigenpair depending smoothly on `S`.  This is the analytic core of Lee's Theorem 2.69: recovering
a rank-1 distribution from a Lorentz metric means selecting the negative-eigenvalue eigenline of
`ḡ_x` relative to an auxiliary Riemannian metric, smoothly in `x`.

## The route

The blueprint's proof of necessity in Theorem 2.69 stops at the observation that "simple
eigenvalues and their eigenlines depend smoothly on the operator", calling it a
perturbation-theoretic statement where "the argument leaves elementary territory".  Nothing of
the sort is in mathlib: there is no Rellich/Kato theory, and no continuity — let alone
smoothness — of eigenvalues or eigenvectors as a function of the operator.

The route taken here keeps the argument elementary, at the cost of nothing.  Rather than
building a spectral projection (which needs an operator square root, a contour integral, or a
holomorphic functional calculus, none of which are available with the required smoothness), we
apply the **inverse function theorem** to the augmented map

  `eigenAug v₀ : (S, v, l) ↦ (S, S v - l • v, ⟪v₀, v⟫ - 1)`

on `(E →L[ℝ] E) × E × ℝ`.  Its zero set in the last two slots is exactly "`v` is an eigenvector
of `S` for the eigenvalue `l`, normalized by `⟪v₀, v⟫ = 1`".  The operator is carried along as a
*parameter in a normed space*, so the derivative is block lower triangular
(`ContinuousLinearEquiv.skewProd`): the identity on the `S` block, and `eigenLin` on the `(v, l)`
block.  Simplicity of the eigenvalue is precisely what makes `eigenLin` injective
(`eigenLin_injective`), hence — in finite dimensions — an equivalence.  The inverse function
theorem then produces the selection, and its smoothness, with no perturbation theory at all.

Because the operator is a normed-space parameter, **no manifold inverse function theorem is
needed**: the selection is a map between normed spaces, and the manifold application composes it
with the smooth map `x ↦ S x`.

## Smoothness on an open set

Mathlib's `ContDiffAt.to_localInverse` gives smoothness of the local inverse *only at the single
point* `f a`; there is no `ContDiffOn` version anywhere in the pin.  A local frame, however, must
be smooth on a whole neighbourhood.  We therefore re-derive smoothness at every point via
`OpenPartialHomeomorph.contDiffAt_symm`, whose hypothesis — invertibility of the derivative at
the preimage — is `eigenLin_injective` again.

Note that invertibility genuinely *fails* at nearby non-self-adjoint operators, so the selection
is **not** smooth on a full neighbourhood of `S₀` in `E →L[ℝ] E`.  This is why
`ContDiffAt_eigenSelection` is stated conditionally, at those `S` where the selected pair is
still a simple eigenpair: in the Lorentz application that hypothesis holds at every point of the
manifold, because the signature is constant.

## Main results

* `IsSimpleEigenpair`: `S v = l • v` with `v ≠ 0`, `S` symmetric, and `ker (S - l)` spanned by `v`.
* `eigenLin_injective`: the linearisation is injective exactly when the eigenvalue is simple.
* `exists_eigenSelection`: the selection `V`, `Λ` on an open set of operators, with
  `S (V S) = Λ S • V S`, `⟪v₀, V S⟫ = 1`, agreeing with `(v₀, l₀)` at `S₀`, continuous, and
  `ContDiffAt` at every `S` where the selected pair is a simple eigenpair.
-/

namespace LeeLib.Ch02

open scoped RealInnerProductSpace
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A simple eigenpair.**  `S` is symmetric, `v` is a nonzero `l`-eigenvector, and the
`l`-eigenspace is exactly the line spanned by `v`.

Simplicity is stated as "every `l`-eigenvector lies on the line `ℝ ∙ v`" rather than as
`finrank (eigenspace S l) = 1`; the two are equivalent, but this form is what the injectivity
argument consumes directly, and it is what the Lorentz application produces. -/
structure IsSimpleEigenpair (S : E →L[ℝ] E) (v : E) (l : ℝ) : Prop where
  /-- `S` is symmetric — for a real inner product space, the same as self-adjoint. -/
  isSymmetric : (S : E →ₗ[ℝ] E).IsSymmetric
  /-- The eigenvector is nonzero. -/
  ne_zero : v ≠ 0
  /-- `v` is an `l`-eigenvector. -/
  apply_eq : S v = l • v
  /-- The `l`-eigenspace is no bigger than `ℝ ∙ v`. -/
  mem_span : ∀ w : E, S w = l • w → w ∈ Submodule.span ℝ ({v} : Set E)

namespace IsSimpleEigenpair

variable {S : E →L[ℝ] E} {v : E} {l : ℝ}

theorem inner_self_ne_zero (h : IsSimpleEigenpair S v l) : ⟪v, v⟫ ≠ 0 := by
  simpa [real_inner_self_eq_norm_sq, pow_eq_zero_iff] using h.ne_zero

/-- Symmetry, restated through the continuous-linear-map coercion rather than the bare linear
map, so that it is directly usable by `rw` in goals mentioning `S x`. -/
theorem inner_apply_left (h : IsSimpleEigenpair S v l) (x y : E) : ⟪S x, y⟫ = ⟪x, S y⟫ :=
  h.isSymmetric x y

end IsSimpleEigenpair

variable {S : E →L[ℝ] E} {v : E} {l : ℝ}

/-! ### The linearisation in the eigenvector/eigenvalue slot -/

/-- The derivative of `(v, l) ↦ (S v - l • v, ⟪v₀, v⟫ - 1)` at a point where the eigenvector
equals `v`:

  `(w, μ) ↦ (S w - l • w - μ • v, ⟪v₀, w⟫)`.

The vector `v₀` is the fixed normalization functional's representative; it is *not* the same as
the base eigenvector `v` once the base point moves away from `S₀`, which is why both appear. -/
noncomputable def eigenLin (S : E →L[ℝ] E) (v : E) (l : ℝ) (v₀ : E) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  ((S - l • ContinuousLinearMap.id ℝ E).comp (ContinuousLinearMap.fst ℝ E ℝ)
      - (ContinuousLinearMap.snd ℝ E ℝ).smulRight v).prod
    ((innerSL ℝ v₀).comp (ContinuousLinearMap.fst ℝ E ℝ))

@[simp]
theorem eigenLin_apply (S : E →L[ℝ] E) (v : E) (l : ℝ) (v₀ : E) (p : E × ℝ) :
    eigenLin S v l v₀ p = (S p.1 - l • p.1 - p.2 • v, ⟪v₀, p.1⟫) := by
  simp [eigenLin]

/-- **Simplicity makes the linearisation injective.**  This is the one place where simplicity of
the eigenvalue is used, and it is the entire analytic content of the smooth selection.

Given `S w - l • w = μ • v` and `⟪v₀, w⟫ = 0`, pairing the first equation with `v` and using
symmetry of `S` together with `S v = l • v` kills the left side, forcing `μ ⟪v, v⟫ = 0` and hence
`μ = 0`.  Then `w` is an `l`-eigenvector, so simplicity puts it on the line `ℝ ∙ v`, and the
normalization `⟪v₀, v⟫ = 1` forces the coefficient to vanish. -/
theorem eigenLin_eq_zero (h : IsSimpleEigenpair S v l) {v₀ : E} (hv₀ : ⟪v₀, v⟫ = 1)
    {p : E × ℝ} (hp : eigenLin S v l v₀ p = 0) : p = 0 := by
  obtain ⟨w, μ⟩ := p
  simp only [eigenLin_apply, Prod.mk_eq_zero] at hp
  obtain ⟨h1, h2⟩ := hp
  -- Pair the eigen-equation with `v`; symmetry makes the left-hand side vanish.
  have hsub : S w - l • w = μ • v := sub_eq_zero.mp h1
  have hpair : ⟪S w - l • w, v⟫ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, h.inner_apply_left w v, h.apply_eq,
      real_inner_smul_right]
    ring
  have hμ : μ = 0 := by
    have : μ * ⟪v, v⟫ = 0 := by
      rw [← real_inner_smul_left, ← hsub]; exact hpair
    exact (mul_eq_zero.mp this).resolve_right h.inner_self_ne_zero
  subst hμ
  -- Now `w` is an `l`-eigenvector, so simplicity places it on the line `ℝ ∙ v`.
  have hev : S w = l • w := by
    rw [zero_smul, sub_eq_zero] at hsub
    exact hsub
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (h.mem_span w hev)
  rw [real_inner_smul_right, hv₀, mul_one] at h2
  simp [h2]

theorem eigenLin_injective (h : IsSimpleEigenpair S v l) {v₀ : E} (hv₀ : ⟪v₀, v⟫ = 1) :
    Function.Injective (eigenLin S v l v₀) := by
  intro p q hpq
  have : p - q = 0 :=
    eigenLin_eq_zero h hv₀ (by rw [map_sub, hpq, sub_self])
  rwa [sub_eq_zero] at this

/-! ### The augmented map and its derivative -/

/-- **The augmented eigen-equation.**  `eigenAug v₀ (S, v, l) = (S, S v - l • v, ⟪v₀, v⟫ - 1)`.

Carrying `S` along unchanged in the first slot turns the *implicit* function problem (solve
`S v = l • v` for `(v, l)` in terms of `S`) into an *inverse* function problem for a self-map of
a single normed space, so mathlib's inverse function theorem applies directly. -/
noncomputable def eigenAug (v₀ : E) :
    ((E →L[ℝ] E) × (E × ℝ)) → ((E →L[ℝ] E) × (E × ℝ)) :=
  fun p => (p.1, (p.1 p.2.1 - p.2.2 • p.2.1, ⟪v₀, p.2.1⟫ - 1))

@[simp]
theorem eigenAug_apply (v₀ : E) (p : (E →L[ℝ] E) × (E × ℝ)) :
    eigenAug v₀ p = (p.1, (p.1 p.2.1 - p.2.2 • p.2.1, ⟪v₀, p.2.1⟫ - 1)) := rfl

theorem contDiff_eigenAug (v₀ : E) : ContDiff ℝ (⊤ : ℕ∞) (eigenAug v₀) :=
  contDiff_fst.prodMk
    ((((contDiff_fst.clm_apply (contDiff_fst.comp contDiff_snd)).sub
        ((contDiff_snd.comp contDiff_snd).smul (contDiff_fst.comp contDiff_snd)))).prodMk
      (((innerSL ℝ v₀).contDiff.comp (contDiff_fst.comp contDiff_snd)).sub contDiff_const))

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The linearisation as a continuous linear equivalence: injective on a finite-dimensional
space, hence bijective, hence — again by finite-dimensionality — a homeomorphism. -/
noncomputable def eigenLinEquiv (h : IsSimpleEigenpair S v l) {v₀ : E} (hv₀ : ⟪v₀, v⟫ = 1) :
    (E × ℝ) ≃L[ℝ] (E × ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofBijective (eigenLin S v l v₀ : (E × ℝ) →ₗ[ℝ] (E × ℝ))
      ⟨eigenLin_injective h hv₀,
        (LinearMap.injective_iff_surjective (K := ℝ)).mp (eigenLin_injective h hv₀)⟩)

@[simp]
theorem eigenLinEquiv_apply (h : IsSimpleEigenpair S v l) {v₀ : E} (hv₀ : ⟪v₀, v⟫ = 1)
    (p : E × ℝ) : eigenLinEquiv h hv₀ p = eigenLin S v l v₀ p := rfl

/-- The block lower triangular derivative of `eigenAug` at a simple eigenpair: the identity on
the operator block, `eigenLin` on the `(v, l)` block, and the shear `T ↦ (T v, 0)` below the
diagonal. -/
noncomputable def eigenAugDerivEquiv (h : IsSimpleEigenpair S v l) {v₀ : E}
    (hv₀ : ⟪v₀, v⟫ = 1) :
    ((E →L[ℝ] E) × (E × ℝ)) ≃L[ℝ] ((E →L[ℝ] E) × (E × ℝ)) :=
  (ContinuousLinearEquiv.refl ℝ (E →L[ℝ] E)).skewProd (eigenLinEquiv h hv₀)
    ((ContinuousLinearMap.apply ℝ E v).prod 0)

theorem hasFDerivAt_eigenAug (h : IsSimpleEigenpair S v l) {v₀ : E} (hv₀ : ⟪v₀, v⟫ = 1) :
    HasFDerivAt (eigenAug v₀) (eigenAugDerivEquiv h hv₀ : _ →L[ℝ] _) (S, (v, l)) := by
  -- The three coordinate projections, as `HasFDerivAt` facts.
  have hfst : HasFDerivAt (fun p : (E →L[ℝ] E) × (E × ℝ) => p.1)
      (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E × ℝ)) (S, (v, l)) :=
    (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E × ℝ)).hasFDerivAt
  have hv' : HasFDerivAt (fun p : (E →L[ℝ] E) × (E × ℝ) => p.2.1)
      ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) (E × ℝ)))
      (S, (v, l)) :=
    hasFDerivAt_fst.comp _ hasFDerivAt_snd
  have hl' : HasFDerivAt (fun p : (E →L[ℝ] E) × (E × ℝ) => p.2.2)
      ((ContinuousLinearMap.snd ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) (E × ℝ)))
      (S, (v, l)) :=
    hasFDerivAt_snd.comp _ hasFDerivAt_snd
  have hG := hfst.clm_apply hv'
  have hH := hl'.smul hv'
  have hI := ((innerSL ℝ v₀).hasFDerivAt (x := v)).comp (S, (v, l)) hv'
  -- The assembled derivative is defeq to `eigenAug`'s, so only the linear maps must be matched.
  refine HasFDerivAt.congr_fderiv (hfst.prodMk ((hG.sub hH).prodMk (hI.sub_const 1))) ?_
  apply ContinuousLinearMap.ext
  rintro ⟨T, w, μ⟩
  simp [eigenAugDerivEquiv, eigenLin, Prod.ext_iff]
  abel

/-! ### The selection -/

/-- **Smooth selection of a simple eigenpair.**

Let `S₀` be a symmetric operator on a finite-dimensional real inner product space with a simple
eigenvalue `l₀` and unit eigenvector `v₀`.  Then on an open set `W` of operators around `S₀`
there are maps `V` and `Λ` selecting, for each `S ∈ W`, an eigenvector `V S` and eigenvalue `Λ S`
of `S`, normalized by `⟪v₀, V S⟫ = 1` (so `V S ≠ 0`), reducing to `(v₀, l₀)` at `S₀`, continuous
on `W`, and **smooth at every `S ∈ W` at which the selected pair is again a simple eigenpair**.

The conditional form of the smoothness clause is not an artifact.  Simplicity is what makes the
linearisation invertible, and the derivative of `eigenAug` genuinely fails to be invertible at
nearby *non-symmetric* operators, of which every neighbourhood of `S₀` in `E →L[ℝ] E` is full.
Callers supply the missing hypothesis from whatever keeps their operators symmetric with a simple
eigenvalue — in Lee's Theorem 2.69, constancy of the signature of the Lorentz metric. -/
theorem exists_eigenSelection {S₀ : E →L[ℝ] E} {v₀ : E} {l₀ : ℝ}
    (h : IsSimpleEigenpair S₀ v₀ l₀) (hv₀ : ⟪v₀, v₀⟫ = 1) :
    ∃ (W : Set (E →L[ℝ] E)) (V : (E →L[ℝ] E) → E) (Λ : (E →L[ℝ] E) → ℝ),
      IsOpen W ∧ S₀ ∈ W ∧ V S₀ = v₀ ∧ Λ S₀ = l₀ ∧
      (∀ S ∈ W, S (V S) = Λ S • V S) ∧ (∀ S ∈ W, ⟪v₀, V S⟫ = 1) ∧
      ContinuousOn V W ∧ ContinuousOn Λ W ∧
      ∀ S ∈ W, IsSimpleEigenpair S (V S) (Λ S) →
        ContDiffAt ℝ (⊤ : ℕ∞) V S ∧ ContDiffAt ℝ (⊤ : ℕ∞) Λ S := by
  classical
  -- The inverse function theorem, applied to `eigenAug` at the given simple eigenpair.
  have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (eigenAug v₀) (S₀, (v₀, l₀)) :=
    (contDiff_eigenAug v₀).contDiffAt
  have hfd := hasFDerivAt_eigenAug h hv₀
  set pe := hcd.toOpenPartialHomeomorph (eigenAug v₀) hfd (by simp) with hpe
  have hcoe : ∀ p, pe p = eigenAug v₀ p := fun _ => rfl
  -- `eigenAug` sends the eigenpair to `(S₀, 0, 0)`: that is exactly the eigen-equation.
  have hbase : eigenAug v₀ (S₀, (v₀, l₀)) = (S₀, ((0 : E), (0 : ℝ))) := by
    rw [eigenAug_apply]
    simp only [h.apply_eq, hv₀, sub_self]
  have hsrc : (S₀, (v₀, l₀)) ∈ pe.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source hcd hfd (by simp)
  -- Slice the target at `(0, 0)`: `W` is the set of operators whose eigen-equation is solved by
  -- the branch the inverse function theorem produced.
  set W : Set (E →L[ℝ] E) := (fun S : E →L[ℝ] E => (S, ((0 : E), (0 : ℝ)))) ⁻¹' pe.target with hW
  have hS₀W : S₀ ∈ W := by
    show (S₀, ((0 : E), (0 : ℝ))) ∈ pe.target
    rw [← hbase, ← hcoe]
    exact pe.map_source hsrc
  have hsymm₀ : pe.symm (S₀, ((0 : E), (0 : ℝ))) = (S₀, (v₀, l₀)) := by
    rw [← hbase, ← hcoe, pe.left_inv hsrc]
  -- Everything about the selected pair is read off from `pe (pe.symm y) = y`.
  have key : ∀ S ∈ W,
      (pe.symm (S, ((0 : E), (0 : ℝ)))).1 = S ∧
      S (pe.symm (S, ((0 : E), (0 : ℝ)))).2.1
        = (pe.symm (S, ((0 : E), (0 : ℝ)))).2.2 • (pe.symm (S, ((0 : E), (0 : ℝ)))).2.1 ∧
      ⟪v₀, (pe.symm (S, ((0 : E), (0 : ℝ)))).2.1⟫ = 1 := by
    intro S hS
    have hr : eigenAug v₀ (pe.symm (S, ((0 : E), (0 : ℝ)))) = (S, ((0 : E), (0 : ℝ))) := by
      rw [← hcoe]; exact pe.right_inv hS
    rw [eigenAug_apply] at hr
    have h1 : (pe.symm (S, ((0 : E), (0 : ℝ)))).1 = S := congrArg Prod.fst hr
    have h2 := congrArg (fun q => q.2.1) hr
    have h3 := congrArg (fun q => q.2.2) hr
    simp only at h2 h3
    rw [sub_eq_zero] at h2 h3
    rw [h1] at h2
    exact ⟨h1, h2, h3⟩
  refine ⟨W, fun S => (pe.symm (S, ((0 : E), (0 : ℝ)))).2.1,
    fun S => (pe.symm (S, ((0 : E), (0 : ℝ)))).2.2,
    pe.open_target.preimage (continuous_id.prodMk continuous_const), hS₀W, ?_, ?_,
    fun S hS => (key S hS).2.1, fun S hS => (key S hS).2.2, ?_, ?_, ?_⟩
  · show (pe.symm (S₀, ((0 : E), (0 : ℝ)))).2.1 = v₀
    rw [hsymm₀]
  · show (pe.symm (S₀, ((0 : E), (0 : ℝ)))).2.2 = l₀
    rw [hsymm₀]
  -- Continuity, from continuity of `pe.symm` on the (open) target.
  · exact ((pe.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
      fun _ hS => hS).snd).fst
  · exact ((pe.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
      fun _ hS => hS).snd).snd
  -- Smoothness: re-run the inverse function theorem's derivative hypothesis at the new point.
  · intro S hS hsimple
    obtain ⟨h1, _, h3⟩ := key S hS
    have hpt : pe.symm (S, ((0 : E), (0 : ℝ)))
        = (S, ((pe.symm (S, ((0 : E), (0 : ℝ)))).2.1, (pe.symm (S, ((0 : E), (0 : ℝ)))).2.2)) :=
      Prod.ext h1 (Prod.mk.eta).symm
    -- `hasFDerivAt_eigenAug` at the *selected* pair: this is the one use of `hsimple`.
    have hfd' : HasFDerivAt (eigenAug v₀) ((eigenAugDerivEquiv hsimple h3 : _ →L[ℝ] _))
        (pe.symm (S, ((0 : E), (0 : ℝ)))) := by
      rw [hpt]; exact hasFDerivAt_eigenAug hsimple h3
    have hsymm : ContDiffAt ℝ (⊤ : ℕ∞) pe.symm (S, ((0 : E), (0 : ℝ))) :=
      pe.contDiffAt_symm hS hfd' ((contDiff_eigenAug v₀).contDiffAt)
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun S : E →L[ℝ] E => pe.symm (S, ((0 : E), (0 : ℝ)))) S :=
      hsymm.comp S (contDiffAt_id.prodMk contDiffAt_const)
    exact ⟨hcomp.snd.fst, hcomp.snd.snd⟩

end FiniteDimensional

end LeeLib.Ch02
