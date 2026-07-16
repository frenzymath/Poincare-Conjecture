/-
Copyright (c) 2026 OpenGA-Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeeLib.Ch02.LorentzMetric
import LeeLib.Ch02.SignatureSpectrum
import LeeLib.Ch02.MusicalIsomorphism
import LeeLib.Ch02.OrthonormalFrame
import LeeLib.Ch02.MetricExistence
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Lee's Theorem 2.69, necessity: a Lorentz metric determines a rank-1 distribution

`LorentzMetric.lean` proves the sufficiency half of Lee's Theorem 2.69 — a rank-1 tangent
distribution produces a Lorentz metric by flipping the sign of an auxiliary Riemannian metric
along the distribution.  This file proves the converse, and assembles the two into the theorem.

Let `ḡ` be a Lorentz metric and `g` an auxiliary Riemannian metric
(`exists_riemannianMetric`).  Lowering an index of `ḡ` with `g` gives at each `x` a
`g`-self-adjoint operator `A x` on `T_x M` with `g(A x v, w) = ḡ(v, w)`
(`metricOperator`).  Being Lorentz means `ḡ` has index `1` everywhere, so
`exists_isSimpleEigenpair_of_sigNeg_eq_one` says `A x` has exactly one negative eigenvalue and
its eigenspace is a line.  That line is the distribution.

## The two design choices

**The distribution is defined without choosing an eigenvalue.**  Lee writes
`D_x = ker (A_x - λ(x))` for "the" negative eigenvalue `λ(x)`, which reads as a choice.  We
instead take the *sum of all the negative eigenspaces*,

  `lorentzDistribution g ḡ x = ⨆ μ < 0, eigenspace (A x) μ`,

which mentions no eigenvalue at all and is manifestly canonical in `g`.  Index `1` collapses
the supremum to a single line: `lorentzDistribution_eq_span` says that *any* nonzero
`μ`-eigenvector with `μ < 0` spans it.  That lemma is the engine of the whole file — it is
what makes the local eigenvector produced below span `D` on the nose, and it is proved from
mathlib's `LinearMap.IsSymmetric.exists_eigenvalues_eq` (every eigenvalue occurs in the
spectral list) plus the uniqueness clause of `exists_isSimpleEigenpair_of_sigNeg_eq_one`.

**The frame is read by its coefficient map, not by an isometry.**  Lee reads `A` in a
`g`-orthonormal frame `E_1, …, E_n` through "the resulting isometry `ι_x : ℝⁿ → T_x M`".  An
isometry is more than is needed: all that the argument uses is that `ι_x` is *injective* and
intertwines `A x` with the matrix `ḡ(E_i, E_j)`.  So `frameCoeff` is the plain linear
coefficient map `c ↦ ∑ cᵢ E_i(x)`, injective because a frame is a basis
(`IsLocalFrameOn.toBasisAt`), and `metricOperator_frameCoeff` is the intertwining relation

  `A x (frameCoeff Y x c) = frameCoeff Y x (frameOperator ḡ Y x c)`.

Orthonormality of the frame is still used — it is what makes the matrix of `A` equal to
`ḡ(E_i, E_j)` — but only through `g(E_i, E_j) = δ_ij`, never through a bundled
`OrthonormalBasis`.  This keeps `EuclideanSpace`'s inner product out of every statement except
the two (`isSymmetric_frameOperator`, and the unit vector fed to `exists_eigenSelection`) that
genuinely need it.

## Main results

* `metricOperator`: the `g`-self-adjoint operator of a pseudo-Riemannian metric.
* `lorentzDistribution`: the sum of the negative eigenspaces of `metricOperator`.
* `lorentzDistribution_eq_span`: index `1` makes it the line of any negative eigenvector.
* `metricOperator_frameCoeff`: `A` intertwines with its matrix in a `g`-orthonormal frame.
* `exists_isRankOneDistribution_of_isLorentzMetric`: **necessity in Lee's Theorem 2.69**.
* `exists_isLorentzMetric_iff_exists_isRankOneDistribution`: **Lee's Theorem 2.69**.
-/

namespace LeeLib.Ch02

open Bundle Manifold Module Submodule QuadraticMap QuadraticForm
open scoped Manifold ContDiff RealInnerProductSpace
open LinearMap (BilinForm)

/-! ### The pointwise linear algebra: index 1 makes the negative eigenspace a line -/

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {B : BilinForm ℝ V} {A : V →L[ℝ] V} {n : ℕ}

/-- **The sum of the negative eigenspaces of a symmetric operator whose form has index `1`
is the line of any negative eigenvector.**

This packages the uniqueness clause of `exists_isSimpleEigenpair_of_sigNeg_eq_one` into the
form the manifold argument consumes: it needs no eigenvalue to be named, and it identifies the
canonical object `⨆ μ < 0, eigenspace A μ` with the span of whichever eigenvector happens to be
at hand.  The bridge from "`μ` is an eigenvalue" to "`μ` occurs in the spectral list", which is
what lets an arbitrary eigenvector be compared with the spectral one, is mathlib's
`LinearMap.IsSymmetric.exists_eigenvalues_eq`. -/
theorem iSup_neg_eigenspace_eq_span [FiniteDimensional ℝ V]
    (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric) (hn : finrank ℝ V = n)
    (hA : ∀ v w, ⟪A v, w⟫ = B v w) (hnd : B.Nondegenerate)
    (hsig : sigNeg (LinearMap.BilinMap.toQuadraticMap B) = 1)
    {v : V} {μ : ℝ} (hv : v ≠ 0) (hev : A v = μ • v) (hμ : μ < 0) :
    ⨆ ν ∈ Set.Iio (0 : ℝ), Module.End.eigenspace (A : V →ₗ[ℝ] V) ν = span ℝ {v} := by
  obtain ⟨i₀, hi₀neg, hi₀simple, hi₀uniq⟩ :=
    exists_isSimpleEigenpair_of_sigNeg_eq_one hsymm hn hA hnd hsig
  -- every negative eigenvalue is `eigenvalues hn i₀`: it occurs in the spectral list, and the
  -- list carries exactly one negative entry
  have key : ∀ (w : V) (ν : ℝ), w ≠ 0 → A w = ν • w → ν < 0 → ν = hsymm.eigenvalues hn i₀ := by
    intro w ν hw hew hνneg
    have hhas : Module.End.HasEigenvalue (A : V →ₗ[ℝ] V) ν :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hew, hw⟩
    obtain ⟨j, hj⟩ := hsymm.exists_eigenvalues_eq hn hhas
    have hjν : hsymm.eigenvalues hn j = ν := by exact_mod_cast hj
    have : j = i₀ := hi₀uniq j (by rw [hjν]; exact hνneg)
    rw [← hjν, this]
  -- `v` spans the same line as the spectral eigenvector
  have hμeq : μ = hsymm.eigenvalues hn i₀ := key v μ hv hev hμ
  have hvmem : v ∈ span ℝ ({hsymm.eigenvectorBasis hn i₀} : Set V) :=
    hi₀simple.mem_span v (by rw [hev, hμeq])
  obtain ⟨c, hc⟩ := mem_span_singleton.1 hvmem
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hv hc.symm
  have hspan : span ℝ ({v} : Set V) = span ℝ ({hsymm.eigenvectorBasis hn i₀} : Set V) := by
    rw [← hc]; exact span_singleton_smul_eq (isUnit_iff_ne_zero.2 hc0) _
  refine le_antisymm (iSup_le fun ν => iSup_le fun (hν : ν ∈ Set.Iio (0:ℝ)) => ?_) ?_
  · intro w hw
    rw [Module.End.mem_eigenspace_iff] at hw
    rcases eq_or_ne w 0 with rfl | hw0
    · exact zero_mem _
    · have hνeq : ν = hsymm.eigenvalues hn i₀ := key w ν hw0 hw hν
      rw [hspan]
      rw [hνeq] at hw
      exact hi₀simple.mem_span w hw
  · rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ
      (Module.End.mem_eigenspace_iff.2 hev))

end Pointwise

/-! ### The operator of a pseudo-Riemannian metric relative to a Riemannian one -/

section MetricOperator

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Lowering an index of `gL` with `g`**: the operator `A x` with
`g(A x v, w) = gL(v, w)`.

This is Lee's `A_x`.  It is `♯ ∘ ♭` for the two metrics — mathlib's Riesz-representation
packaging `InnerProductSpace.continuousLinearMapOfBilin` is exactly this construction and
gives it as a genuine continuous linear map, which `LeeLib.Ch02.sharp` (a bare function) does
not. -/
noncomputable def metricOperator (g : RiemannianMetric I M) (gL : PseudoRiemannianMetric I M)
    (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  InnerProductSpace.continuousLinearMapOfBilin
    (gL.form x : TangentSpace I x →L⋆[ℝ] TangentSpace I x →L[ℝ] ℝ)

/-- **The defining property of `metricOperator`** — Lee's `ḡ_x(v,w) = g_x(A_x v, w)`. -/
theorem innerAt_metricOperator (g : RiemannianMetric I M) (gL : PseudoRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    g.innerAt x (metricOperator g gL x v) w = gL.form x v w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  show (inner ℝ (metricOperator g gL x v) w : ℝ) = gL.form x v w
  rw [metricOperator]
  exact InnerProductSpace.continuousLinearMapOfBilin_apply
    (𝕜 := ℝ) (B := (gL.form x : TangentSpace I x →L⋆[ℝ] TangentSpace I x →L[ℝ] ℝ)) v w

/-- `metricOperator` is `g`-self-adjoint, because `gL` is symmetric. -/
theorem isSymmetric_metricOperator (g : RiemannianMetric I M) (gL : PseudoRiemannianMetric I M)
    (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ((metricOperator g gL x : TangentSpace I x →L[ℝ] TangentSpace I x) :
        TangentSpace I x →ₗ[ℝ] TangentSpace I x).IsSymmetric := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  refine isSymmetric_of_inner_eq (B := gL.bilin x) (fun v w => ?_) (gL.bilin_isSymm x)
  rw [gL.bilin_apply]
  exact innerAt_metricOperator g gL x v w

/-- The `⟪·,·⟫`-form of `innerAt_metricOperator`, matching the shape the `SignatureSpectrum`
lemmas take as their `hA` argument. -/
theorem inner_metricOperator (g : RiemannianMetric I M) (gL : PseudoRiemannianMetric I M)
    (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ v w : TangentSpace I x, ⟪metricOperator g gL x v, w⟫ = (gL.bilin x v) w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro v w
  rw [gL.bilin_apply]
  exact innerAt_metricOperator g gL x v w

end MetricOperator

/-! ### The distribution -/

section Distribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The line field of a Lorentz metric** — Lee's `D_x = ker(A_x - λ(x))`, written as the sum
of *all* the negative eigenspaces of `A_x` so that no eigenvalue has to be chosen.  Index `1`
makes this a line (`lorentzDistribution_eq_span`); for a general pseudo-Riemannian `gL` it is
the maximal `gL`-negative-definite `A`-invariant subspace, and nothing below uses it. -/
noncomputable def lorentzDistribution (g : RiemannianMetric I M) (gL : PseudoRiemannianMetric I M)
    (x : M) : Submodule ℝ (TangentSpace I x) :=
  ⨆ μ ∈ Set.Iio (0 : ℝ),
    Module.End.eigenspace
      ((metricOperator g gL x : TangentSpace I x →L[ℝ] TangentSpace I x) :
        TangentSpace I x →ₗ[ℝ] TangentSpace I x) μ

variable (g : RiemannianMetric I M) (gL : PseudoRiemannianMetric I M)

omit [FiniteDimensional ℝ E] in
/-- At a point, "`gL` is Lorentz" says exactly that its fibre form has index `1`. -/
theorem sigNeg_bilin_eq_one (hL : IsLorentzMetric gL) (x : M) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap (gL.bilin x)) = 1 := by
  obtain ⟨r, hsig⟩ := hL
  exact (hsig x).2

/-- **Any negative eigenvector of `A x` spans the distribution.**  The manifold-level form of
`iSup_neg_eigenspace_eq_span`. -/
theorem lorentzDistribution_eq_span (hL : IsLorentzMetric gL) {x : M}
    {v : TangentSpace I x} {μ : ℝ} (hv : v ≠ 0)
    (hev : metricOperator g gL x v = μ • v) (hμ : μ < 0) :
    lorentzDistribution g gL x = span ℝ {v} := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  exact iSup_neg_eigenspace_eq_span (n := finrank ℝ E) (isSymmetric_metricOperator g gL x) rfl
    (inner_metricOperator g gL x) (gL.bilin_nondegenerate x) (sigNeg_bilin_eq_one gL hL x)
    hv hev hμ

/-- **Every point carries a negative eigenvector** — the pointwise content of "index `1`". -/
theorem exists_neg_eigenvector (hL : IsLorentzMetric gL) (x : M) :
    ∃ (v : TangentSpace I x) (μ : ℝ), v ≠ 0 ∧ μ < 0 ∧ metricOperator g gL x v = μ • v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  obtain ⟨i₀, hneg, hsimple, -⟩ :=
    exists_isSimpleEigenpair_of_sigNeg_eq_one (n := finrank ℝ E)
      (isSymmetric_metricOperator g gL x) rfl (inner_metricOperator g gL x)
      (gL.bilin_nondegenerate x) (sigNeg_bilin_eq_one gL hL x)
  exact ⟨_, _, hsimple.ne_zero, hneg, hsimple.apply_eq⟩

end Distribution

/-! ### Reading the operator in a frame -/

section FrameOperator

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ}

/-- The matrix of `gL` in a frame: `m i j = gL(Y i, Y j)`.  When the frame is `g`-orthonormal
this is also the matrix of `metricOperator g gL`, which is the point of `frameOperator`. -/
noncomputable def frameMatrix (gL : PseudoRiemannianMetric I M)
    (Y : Fin n → (x : M) → TangentSpace I x) (x : M) (i j : Fin n) : ℝ :=
  gL.form x (Y i x) (Y j x)

omit [FiniteDimensional ℝ E] in
theorem frameMatrix_symm (gL : PseudoRiemannianMetric I M)
    (Y : Fin n → (x : M) → TangentSpace I x) (x : M) (i j : Fin n) :
    frameMatrix gL Y x i j = frameMatrix gL Y x j i :=
  gL.symm x (Y i x) (Y j x)

/-- The operator on `EuclideanSpace ℝ (Fin n)` with matrix `frameMatrix gL Y x`.  This is
Lee's `S(x) = ι_x⁻¹ ∘ A_x ∘ ι_x`, but *defined* by its matrix rather than by conjugation, which
is what makes its smoothness in `x` immediate (`contMDiffOn_frameOperator`); that it really is
the conjugate is `metricOperator_frameCoeff`. -/
noncomputable def frameOperator (gL : PseudoRiemannianMetric I M)
    (Y : Fin n → (x : M) → TangentSpace I x) (x : M) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ∑ i, ∑ j, (frameMatrix gL Y x i j) •
    (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (EuclideanSpace.single j (1 : ℝ))

/-- `(∑ i, f i) l = ∑ i, f i l` on `EuclideanSpace`, which is *not* `rfl` in this pin
(`WithLp` is a structure). -/
theorem euclideanSpace_sum_apply {ι : Type*} [Fintype ι] (f : ι → EuclideanSpace ℝ (Fin n))
    (l : Fin n) : (∑ i, f i) l = ∑ i, f i l := by
  change WithLp.ofLp (∑ i, f i) l = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

omit [FiniteDimensional ℝ E] in
/-- **The matrix action**: the `j`-th coordinate of `frameOperator gL Y x c` is `∑ i, cᵢ mᵢⱼ`. -/
theorem frameOperator_apply_coord (gL : PseudoRiemannianMetric I M)
    (Y : Fin n → (x : M) → TangentSpace I x) (x : M) (c : EuclideanSpace ℝ (Fin n))
    (l : Fin n) :
    (frameOperator gL Y x c) l = ∑ i, c i * frameMatrix gL Y x i l := by
  simp only [frameOperator, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, EuclideanSpace.proj, PiLp.proj_apply]
  rw [euclideanSpace_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [euclideanSpace_sum_apply]
  rw [Finset.sum_eq_single l]
  · simp [mul_comm]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h; exact absurd (Finset.mem_univ l) h

omit [FiniteDimensional ℝ E] in
/-- `frameOperator` is smooth wherever the frame is, because its entries are `gL`-pairings of
smooth sections. -/
theorem contMDiffOn_frameOperator (gL : PseudoRiemannianMetric I M)
    {Y : Fin n → (x : M) → TangentSpace I x} {u : Set M}
    (hY : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x => TotalSpace.mk' E x (Y i x)) u) :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (frameOperator gL Y) u := by
  have hm : ∀ i j, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => frameMatrix gL Y x i j) u := fun i j =>
    gL.contMDiffOn_pairing (b := id) contMDiffOn_id (hY i) (hY j)
  have hinner : ∀ i : Fin n,
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
        (fun x => ∑ j, (frameMatrix gL Y x i j) •
          (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (EuclideanSpace.single j (1:ℝ))) u := by
    intro i
    apply contMDiffOn_finset_sum
    intro j _
    exact (hm i j).smul contMDiffOn_const
  unfold frameOperator
  apply contMDiffOn_finset_sum
  intro i _
  exact hinner i

omit [FiniteDimensional ℝ E] in
/-- `frameOperator` is symmetric, because `gL` is. -/
theorem isSymmetric_frameOperator (gL : PseudoRiemannianMetric I M)
    (Y : Fin n → (x : M) → TangentSpace I x) (x : M) :
    ((frameOperator gL Y x : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric := by
  intro v w
  show ⟪frameOperator gL Y x v, w⟫ = ⟪v, frameOperator gL Y x w⟫
  rw [PiLp.inner_apply, PiLp.inner_apply]
  -- the fibre inner product of `ℝ` over `ℝ`: `⟪a, b⟫ = b * a`
  simp only [inner, star_trivial, RCLike.re_to_real]
  have hL : ∀ i, w i * (frameOperator gL Y x v) i
      = ∑ k, w i * (v k * frameMatrix gL Y x k i) := fun i => by
    rw [frameOperator_apply_coord, Finset.mul_sum]
  have hR : ∀ i, (frameOperator gL Y x w) i * v i
      = ∑ k, w k * frameMatrix gL Y x k i * v i := fun i => by
    rw [frameOperator_apply_coord, Finset.sum_mul]
  simp only [hL, hR]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [frameMatrix_symm gL Y x k i]
  ring

/-! ### The frame coefficient map -/

/-- The coefficient map `c ↦ ∑ cᵢ Y i x` of a frame — Lee's `ι_x`, with the isometry forgotten.
Only its linearity and injectivity are used. -/
noncomputable def frameCoeff (Y : Fin n → (x : M) → TangentSpace I x) (x : M)
    (c : EuclideanSpace ℝ (Fin n)) : TangentSpace I x :=
  ∑ i, c i • Y i x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
@[simp] theorem frameCoeff_zero (Y : Fin n → (x : M) → TangentSpace I x) (x : M) :
    frameCoeff Y x 0 = 0 := by simp [frameCoeff]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem frameCoeff_smul (Y : Fin n → (x : M) → TangentSpace I x) (x : M) (t : ℝ)
    (c : EuclideanSpace ℝ (Fin n)) :
    frameCoeff Y x (t • c) = t • frameCoeff Y x c := by
  simp only [frameCoeff, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [PiLp.smul_apply, smul_eq_mul, mul_smul]

omit [FiniteDimensional ℝ E] in
/-- `frameCoeff` through a local frame is `Basis.equivFun.symm` of the induced pointwise basis,
hence bijective.

No `finrank ℝ E = n` hypothesis is needed: `IsLocalFrameOn` already makes `(Y · x)` a basis of
`T_x M` indexed by `Fin n`, which forces the rank. -/
theorem frameCoeff_bijective {Y : Fin n → (x : M) → TangentSpace I x} {u : Set M} {x : M}
    (hY : IsLocalFrameOn I E ∞ Y u) (hx : x ∈ u) :
    Function.Bijective (frameCoeff Y x) := by
  have hb : ∀ c : EuclideanSpace ℝ (Fin n),
      frameCoeff Y x c = (hY.toBasisAt hx).equivFun.symm (WithLp.ofLp c) := by
    intro c
    rw [Basis.equivFun_symm_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [hY.toBasisAt_coe hx i]
  have : (frameCoeff Y x) = (hY.toBasisAt hx).equivFun.symm ∘ WithLp.ofLp := funext hb
  rw [this]
  exact (hY.toBasisAt hx).equivFun.symm.bijective.comp (WithLp.linearEquiv 2 ℝ _).bijective

omit [FiniteDimensional ℝ E] in
theorem frameCoeff_injective {Y : Fin n → (x : M) → TangentSpace I x} {u : Set M} {x : M}
    (hY : IsLocalFrameOn I E ∞ Y u) (hx : x ∈ u) :
    Function.Injective (frameCoeff Y x) := (frameCoeff_bijective hY hx).1

/-- **The intertwining relation** — Lee's `S(x) = ι_x⁻¹ ∘ A_x ∘ ι_x`, in the form
`A_x ∘ ι_x = ι_x ∘ S(x)` which needs no inverse.

This is the one place the frame's `g`-orthonormality is used: it forces `⟪ι_x c', Y j x⟫` to be
the `j`-th coordinate of `c'`, which is what identifies the matrix of `A_x` with
`ḡ(Y i, Y j)`. -/
theorem metricOperator_frameCoeff (g : RiemannianMetric I M) (gL : PseudoRiemannianMetric I M)
    {Y : Fin n → (x : M) → TangentSpace I x} {u : Set M} {x : M}
    (hY : IsLocalFrameOn I E ∞ Y u) (hx : x ∈ u)
    (hon : ∀ i j, g.innerAt x (Y i x) (Y j x) = if i = j then 1 else 0)
    (c : EuclideanSpace ℝ (Fin n)) :
    metricOperator g gL x (frameCoeff Y x c) = frameCoeff Y x (frameOperator gL Y x c) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  refine InnerProductSpace.ext_inner_right_basis (hY.toBasisAt hx) fun j => ?_
  rw [hY.toBasisAt_coe hx j]
  -- left: `⟪A (∑ cᵢ Yᵢ), Yⱼ⟫ = ḡ(∑ cᵢ Yᵢ, Yⱼ) = ∑ cᵢ mᵢⱼ`
  have hleft : ⟪metricOperator g gL x (frameCoeff Y x c), Y j x⟫
      = ∑ i, c i * frameMatrix gL Y x i j := by
    show g.innerAt x (metricOperator g gL x (frameCoeff Y x c)) (Y j x) = _
    rw [innerAt_metricOperator]
    show (gL.form x) (∑ i, c i • Y i x) (Y j x) = _
    rw [map_sum]
    simp only [ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rfl
  -- right: `⟪∑ (Sc)ᵢ Yᵢ, Yⱼ⟫ = (Sc)ⱼ = ∑ cᵢ mᵢⱼ` by orthonormality
  have hright : ⟪frameCoeff Y x (frameOperator gL Y x c), Y j x⟫
      = ∑ i, c i * frameMatrix gL Y x i j := by
    show g.innerAt x (∑ i, (frameOperator gL Y x c) i • Y i x) (Y j x) = _
    rw [← frameOperator_apply_coord]
    have hsum : g.innerAt x (∑ i, (frameOperator gL Y x c) i • Y i x) (Y j x)
        = ∑ i, (frameOperator gL Y x c) i * g.innerAt x (Y i x) (Y j x) := by
      show (g.inner x) (∑ i, (frameOperator gL Y x c) i • Y i x) (Y j x) = _
      rw [map_sum]
      simp only [ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      rfl
    rw [hsum]
    rw [Finset.sum_eq_single j]
    · rw [hon j j, if_pos rfl, mul_one]
    · intro k _ hk
      rw [hon k j, if_neg hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hleft, hright]

/-- **Simplicity transfers from `A x` to its matrix.**  A negative eigenvector of
`frameOperator` is a *simple* eigenvector of it, because `frameCoeff` carries it to a negative
eigenvector of `metricOperator`, whose negative eigenspace is a line
(`lorentzDistribution_eq_span`).

This is what discharges the conditional smoothness clause of `exists_eigenSelection`: that
lemma is only smooth where the selected pair is again simple, and constancy of the signature of
the Lorentz metric is exactly what guarantees it. -/
theorem isSimpleEigenpair_frameOperator (g : RiemannianMetric I M)
    (gL : PseudoRiemannianMetric I M) (hL : IsLorentzMetric gL)
    {Y : Fin n → (x : M) → TangentSpace I x} {u : Set M} {x : M}
    (hY : IsLocalFrameOn I E ∞ Y u) (hx : x ∈ u)
    (hon : ∀ i j, g.innerAt x (Y i x) (Y j x) = if i = j then 1 else 0)
    {c : EuclideanSpace ℝ (Fin n)} {l : ℝ} (hc : c ≠ 0) (hl : l < 0)
    (hev : frameOperator gL Y x c = l • c) :
    IsSimpleEigenpair (frameOperator gL Y x) c l := by
  -- the image of any `l`-eigenvector of the matrix is an `l`-eigenvector of `A x`
  have himg : ∀ d : EuclideanSpace ℝ (Fin n), frameOperator gL Y x d = l • d →
      metricOperator g gL x (frameCoeff Y x d) = l • frameCoeff Y x d := by
    intro d hd
    rw [metricOperator_frameCoeff g gL hY hx hon, hd, frameCoeff_smul]
  have hinj := frameCoeff_injective hY hx
  have hcne : frameCoeff Y x c ≠ 0 := fun h => hc (hinj (by rw [h, frameCoeff_zero]))
  have hspanc : lorentzDistribution g gL x = span ℝ {frameCoeff Y x c} :=
    lorentzDistribution_eq_span g gL hL hcne (himg c hev) hl
  refine ⟨isSymmetric_frameOperator gL Y x, hc, hev, fun w hw => ?_⟩
  rcases eq_or_ne w 0 with rfl | hw0
  · exact zero_mem _
  · have hwne : frameCoeff Y x w ≠ 0 := fun h => hw0 (hinj (by rw [h, frameCoeff_zero]))
    have hspanw : lorentzDistribution g gL x = span ℝ {frameCoeff Y x w} :=
      lorentzDistribution_eq_span g gL hL hwne (himg w hw) hl
    -- both eigenvectors span the same line, so their coefficient vectors are proportional
    have : frameCoeff Y x w ∈ span ℝ ({frameCoeff Y x c} : Set (TangentSpace I x)) := by
      rw [← hspanc, hspanw]; exact mem_span_singleton_self _
    obtain ⟨t, ht⟩ := mem_span_singleton.1 this
    rw [mem_span_singleton]
    exact ⟨t, hinj (by rw [frameCoeff_smul, ht])⟩

end FrameOperator

/-! ### Lee's Theorem 2.69 -/

section Main

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Lee's Theorem 2.69, necessity half**: a smooth manifold carrying a Lorentz metric carries
a rank-1 tangent distribution.

The distribution is `lorentzDistribution g ḡ` for an arbitrary auxiliary Riemannian metric `g`:
the field of negative eigenlines of the operator `A` obtained by lowering an index of `ḡ` with
`g`.  That this is a *line* field is pointwise linear algebra (`lorentzDistribution_eq_span`);
all the work here is producing the smooth local sections that `IsRankOneDistribution` demands,
which is Lee's "it remains to produce smooth local spanning sections, which is a local
question".

Near a point, a `g`-orthonormal frame turns `A` into the matrix `ḡ(E_i, E_j)`
(`metricOperator_frameCoeff`), which is smooth in the base point and symmetric.  The eigenline
of a symmetric matrix with a simple negative eigenvalue is selected smoothly by
`exists_eigenSelection`, whose conditional simplicity hypothesis is discharged by
`isSimpleEigenpair_frameOperator` — i.e. by the constancy of the signature of `ḡ`.  Pushing the
selected eigenvector back through the frame gives the section. -/
theorem exists_isRankOneDistribution_of_isLorentzMetric
    (gL : PseudoRiemannianMetric I M) (hL : IsLorentzMetric gL) :
    ∃ D : ∀ x : M, Submodule ℝ (TangentSpace I x), IsRankOneDistribution I M D := by
  obtain ⟨g⟩ := exists_riemannianMetric (I := I) (M := M)
  refine ⟨lorentzDistribution g gL, ⟨fun p => ?_⟩⟩
  -- a `g`-orthonormal frame near `p`
  obtain ⟨u, Y, hu, hpu, hY, hon⟩ := exists_orthonormalFrame_nhds g p
  have hon' : ∀ x ∈ u, ∀ i j, g.innerAt x (Y i x) (Y j x) = if i = j then 1 else 0 := hon
  -- a negative eigenvector at `p`, read in the frame
  obtain ⟨w₀, l₀, hw₀ne, hl₀neg, hw₀ev⟩ := exists_neg_eigenvector g gL hL p
  obtain ⟨c₀, hc₀⟩ := (frameCoeff_bijective hY hpu).2 w₀
  have hinjp := frameCoeff_injective hY hpu
  have hc₀ne : c₀ ≠ 0 := fun h => hw₀ne (by rw [← hc₀, h, frameCoeff_zero])
  have hSev : frameOperator gL Y p c₀ = l₀ • c₀ := by
    refine hinjp ?_
    rw [← metricOperator_frameCoeff g gL hY hpu (hon' p hpu), hc₀, hw₀ev, frameCoeff_smul, hc₀]
  -- normalize it: `exists_eigenSelection` needs a unit eigenvector
  set v₀ : EuclideanSpace ℝ (Fin (finrank ℝ E)) := (‖c₀‖)⁻¹ • c₀ with hv₀def
  have hv₀norm : ‖v₀‖ = 1 := norm_smul_inv_norm hc₀ne
  have hv₀ne : v₀ ≠ 0 := by intro h; rw [h, norm_zero] at hv₀norm; norm_num at hv₀norm
  have hv₀unit : ⟪v₀, v₀⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv₀norm]; norm_num
  have hv₀ev : frameOperator gL Y p v₀ = l₀ • v₀ := by
    rw [hv₀def, map_smul, hSev, smul_comm]
  have hsimple₀ : IsSimpleEigenpair (frameOperator gL Y p) v₀ l₀ :=
    isSimpleEigenpair_frameOperator g gL hL hY hpu (hon' p hpu) hv₀ne hl₀neg hv₀ev
  -- the smooth eigen-selection around the matrix at `p`
  obtain ⟨W, Vsel, Λ, hWopen, hSpW, -, hΛS₀, hevW, hnormW, -, hΛcont, hsmooth⟩ :=
    exists_eigenSelection hsimple₀ hv₀unit
  -- shrink `u` to where the matrix lies in `W` and the selected eigenvalue is still negative
  have hScont : ContinuousOn (frameOperator gL Y) u :=
    (contMDiffOn_frameOperator gL hY.contMDiffOn).continuousOn
  set u₁ : Set M := u ∩ (frameOperator gL Y) ⁻¹' W with hu₁def
  have hu₁open : IsOpen u₁ := hScont.isOpen_inter_preimage hu hWopen
  have hΛcomp : ContinuousOn (fun x => Λ (frameOperator gL Y x)) u₁ :=
    hΛcont.comp (hScont.mono Set.inter_subset_left) fun x hx => hx.2
  set u' : Set M := u₁ ∩ (fun x => Λ (frameOperator gL Y x)) ⁻¹' (Set.Iio 0) with hu'def
  have hu'open : IsOpen u' := hΛcomp.isOpen_inter_preimage hu₁open isOpen_Iio
  have hpu' : p ∈ u' := ⟨⟨hpu, hSpW⟩, by simp only [Set.mem_preimage, Set.mem_Iio, hΛS₀]; exact hl₀neg⟩
  have hu'u : u' ⊆ u := fun x hx => hx.1.1
  -- the selected eigenvector is nowhere zero, and at each `x ∈ u'` the selected pair is simple
  have hVne : ∀ x ∈ u', Vsel (frameOperator gL Y x) ≠ 0 := by
    intro x hx h
    have := hnormW _ hx.1.2
    rw [h, inner_zero_right] at this
    norm_num at this
  have hsimplex : ∀ x ∈ u', IsSimpleEigenpair (frameOperator gL Y x)
      (Vsel (frameOperator gL Y x)) (Λ (frameOperator gL Y x)) := fun x hx =>
    isSimpleEigenpair_frameOperator g gL hL hY (hu'u hx) (hon' x (hu'u hx))
      (hVne x hx) hx.2 (hevW _ hx.1.2)
  refine ⟨u', fun x => frameCoeff Y x (Vsel (frameOperator gL Y x)), hu'open, hpu', ?_, ?_⟩
  · -- smoothness: smooth coefficients in a smooth frame
    have hSsmooth : ∀ x ∈ u', ContMDiffAt I
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E)) →L[ℝ]
          EuclideanSpace ℝ (Fin (finrank ℝ E))) ∞ (frameOperator gL Y) x := fun x hx =>
      ((contMDiffOn_frameOperator gL hY.contMDiffOn) x (hu'u hx)).contMDiffAt
        (hu.mem_nhds (hu'u hx))
    have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x => (Vsel (frameOperator gL Y x)) i) u' := by
      intro i x hx
      have hV : ContDiffAt ℝ (⊤ : ℕ∞) Vsel (frameOperator gL Y x) :=
        (hsmooth _ hx.1.2 (hsimplex x hx)).1
      have hcomp : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E))) ∞
          (fun x => Vsel (frameOperator gL Y x)) x := hV.comp_contMDiffAt (hSsmooth x hx)
      have := (contMDiffAt_const
        (c := EuclideanSpace.proj (𝕜 := ℝ) i)).clm_apply hcomp
      exact (by simpa using this : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x => (Vsel (frameOperator gL Y x)) i) x).contMDiffWithinAt
    exact ContMDiffOn.sum_section fun i _ =>
      (hcoeff i).smul_section ((hY.contMDiffOn i).mono hu'u)
  · intro x hx
    have hne : frameCoeff Y x (Vsel (frameOperator gL Y x)) ≠ 0 := fun h =>
      hVne x hx (frameCoeff_injective hY (hu'u hx) (by rw [h, frameCoeff_zero]))
    refine ⟨hne, ?_⟩
    have hev : metricOperator g gL x (frameCoeff Y x (Vsel (frameOperator gL Y x)))
        = Λ (frameOperator gL Y x) • frameCoeff Y x (Vsel (frameOperator gL Y x)) := by
      rw [metricOperator_frameCoeff g gL hY (hu'u hx) (hon' x (hu'u hx)), hevW _ hx.1.2,
        frameCoeff_smul]
    exact (lorentzDistribution_eq_span g gL hL hne hev hx.2).symm

/-- **Lee's Theorem 2.69**: a smooth manifold admits a Lorentz metric if and only if it admits
a rank-1 tangent distribution.

Sufficiency is `exists_isLorentzMetric_of_isRankOneDistribution` (`LorentzMetric.lean`) and
necessity is `exists_isRankOneDistribution_of_isLorentzMetric`. -/
theorem exists_isLorentzMetric_iff_exists_isRankOneDistribution :
    (∃ gL : PseudoRiemannianMetric I M, IsLorentzMetric gL) ↔
      ∃ D : ∀ x : M, Submodule ℝ (TangentSpace I x), IsRankOneDistribution I M D :=
  ⟨fun ⟨gL, hL⟩ => exists_isRankOneDistribution_of_isLorentzMetric gL hL,
    fun ⟨_, hD⟩ => exists_isLorentzMetric_of_isRankOneDistribution I M hD⟩

end Main

end LeeLib.Ch02
