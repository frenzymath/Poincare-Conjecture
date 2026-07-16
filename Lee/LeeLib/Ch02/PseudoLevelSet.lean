/-
Chapter 2, "Riemannian Metrics", §"The Pseudo-Riemannian Case": Lee's Corollary
2.71, the embedding criterion for level sets, in full.

Lee 2.71.  Let `(M̃, g̃)` be a pseudo-Riemannian manifold of signature `(r,s)`, let
`f ∈ C^∞(M̃)` and `M = f^{-1}(c)`.  If `g̃(grad f, grad f) > 0` everywhere on `M`
then `M` is an embedded pseudo-Riemannian submanifold of signature `(r-1,s)`; if
`g̃(grad f, grad f) < 0` everywhere then the signature is `(r,s-1)`.  In either
case `grad f` is normal to `M`.

`EmbeddingCriterion` holds the pointwise linear algebra; this file supplies the
two globalizations Lee performs silently and then assembles the corollary.

* **The gradient.**  `pseudoGrad` is `bilinGrad` applied fibrewise to `df_p` and
  `g̃_p`.  It is the indefinite analogue of `LeeLib.Ch02.grad`
  (`MusicalIsomorphism`), which raises indices with the Riesz isomorphism and so
  needs positive definiteness; `bilinGrad` needs only nondegeneracy.

* **The level set.**  `LeeLib.Ch02.LevelSetChartedSpace` makes `f^{-1}(c)` a smooth
  `n`-manifold, gives the inclusion's smoothness and immersion, and identifies
  `T_p(f^{-1}(c))` with `ker df_p` (`range_mfderiv_levelSet_val`).  Here that data
  is packaged as a bundled `C^∞⟮𝓡 n, f ⁻¹' {c}; I, M⟯` — `levelSetInclMap` —
  because `PseudoHypersurface`'s Proposition 2.70 consumes a bundled map.

The one step Lee leaves implicit is that the hypothesis `g̃(grad f, grad f) > 0`
is *equivalent* to Proposition 2.70's "every nonzero normal is positive": the
normal space is the line `⟨grad f⟩` (`orthogonal_ker_eq_span_bilinGrad`), on which
`g̃(v,v)` scales by a square and so has constant sign.  That is
`pos_apply_self_of_mem_orthogonal_ker`, and `forall_normal_pos_of_pseudoGrad_pos`
below transports it across the pullback fibre.

Both hypotheses of the old `EmbeddingCriterion` header — a pseudo-Riemannian
metric on a manifold, and the regular level set theorem — now exist
(`PseudoRiemannianMetric`, `LevelSetChartedSpace`), so 2.71 is no longer pointwise
only.
-/
import LeeLib.Ch02.EmbeddingCriterion
import LeeLib.Ch02.PseudoHypersurface
import LeeLib.Ch02.LevelSetChartedSpace

namespace LeeLib.Ch02

open Bundle Manifold Module
open scoped Manifold ContDiff
open LinearMap (BilinForm)

section PseudoGrad

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (I) in
/-- **The differential `df_p` as an element of the algebraic dual of `T_pM`.**

`mfderiv I 𝓘(ℝ, ℝ) f p` is a continuous linear map into `TangentSpace 𝓘(ℝ, ℝ) (f p)`,
which is definitionally `ℝ`; `bilinGrad` consumes a bare `Module.Dual`, so the
continuity and the target synonym are both discarded here.  Compare
`levelDifferential` (`LevelSetChartedSpace`), which performs the same retyping over
the model space `E`. -/
noncomputable def dualDifferential (f : M → ℝ) (p : M) : Module.Dual ℝ (TangentSpace I p) :=
  (mfderiv I 𝓘(ℝ, ℝ) f p : TangentSpace I p →L[ℝ] ℝ).toLinearMap

theorem dualDifferential_eq_zero_iff (f : M → ℝ) (p : M) :
    dualDifferential I f p = 0 ↔ mfderiv I 𝓘(ℝ, ℝ) f p = 0 := by
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun v => ?_
    exact congrArg (fun a : Module.Dual ℝ (TangentSpace I p) => a v) h
  · intro h
    refine LinearMap.ext fun v => ?_
    exact congrArg (fun a : TangentSpace I p →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (f p) => a v) h

theorem dualDifferential_ne_zero {f : M → ℝ} {p : M} (hdf : mfderiv I 𝓘(ℝ, ℝ) f p ≠ 0) :
    dualDifferential I f p ≠ 0 :=
  fun h => hdf ((dualDifferential_eq_zero_iff f p).1 h)

variable (g : PseudoRiemannianMetric I M) (f : M → ℝ) (p : M)

/-- **The pseudo-Riemannian gradient of `f`**, Lee's `grad f` for an indefinite metric.

Defined fibrewise as `bilinGrad`, the `g_p`-representative of `df_p`.  Lee's `grad`
(`LeeLib.Ch02.grad`) uses the Riesz isomorphism, which needs an inner product; for an
indefinite `g` nondegeneracy alone suffices, and that is what `bilinGrad` uses. -/
noncomputable def pseudoGrad : TangentSpace I p :=
  bilinGrad (g.bilin p) (g.bilin_nondegenerate p) (dualDifferential I f p)

/-- **The defining property of the pseudo-gradient**: `g(grad f, w) = df(w)` — Lee's
(2.14) for an indefinite metric. -/
@[simp] theorem form_pseudoGrad (w : TangentSpace I p) :
    g.form p (pseudoGrad g f p) w = dualDifferential I f p w :=
  apply_bilinGrad (g.bilin p) (g.bilin_nondegenerate p) (dualDifferential I f p) w

/-- The pseudo-gradient is nonzero exactly where `f` is regular: Lee's observation
that `g̃(grad f, grad f) ≠ 0` on `M` forces `c` to be a regular value. -/
theorem pseudoGrad_ne_zero (hdf : mfderiv I 𝓘(ℝ, ℝ) f p ≠ 0) : pseudoGrad g f p ≠ 0 :=
  bilinGrad_ne_zero (g.bilin p) (g.bilin_nondegenerate p) (dualDifferential_ne_zero hdf)

/-- **A non-null gradient forces regularity.**  This is the first sentence of Lee's proof:
"The hypothesis `g̃(grad f, grad f) ≠ 0` on `M` forces `df_p ≠ 0` at each `p ∈ M`, so `c` is a
regular value of `f`."  Contrapositive of `form_pseudoGrad`: if `df_p = 0` then `grad f|_p`
represents the zero functional, so `g(grad f, grad f) = df(grad f) = 0`. -/
theorem mfderiv_ne_zero_of_form_pseudoGrad_ne_zero
    (h : g.form p (pseudoGrad g f p) (pseudoGrad g f p) ≠ 0) :
    mfderiv I 𝓘(ℝ, ℝ) f p ≠ 0 := by
  intro hdf
  refine h ?_
  rw [form_pseudoGrad, (dualDifferential_eq_zero_iff f p).2 hdf]
  rfl

/-- The pseudo-gradient is `g`-orthogonal to `ker df_p` — "`grad f` is normal to `M`" at `p`,
since `T_pM = ker df_p`. -/
theorem form_pseudoGrad_eq_zero_of_mem_ker (w : TangentSpace I p)
    (hw : w ∈ LinearMap.ker (dualDifferential I f p)) :
    g.form p (pseudoGrad g f p) w = 0 := by
  rw [form_pseudoGrad]
  exact hw

end PseudoGrad

section LevelSet

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

variable {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
  (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)] (c : ℝ)

/-- **The level-set inclusion as a bundled smooth map.**

`contMDiff_levelSet_val` is an unbundled `ContMDiff` proposition, but Lee's Proposition 2.70
(`hasSignature_pseudoPullbackMetric_of_forall_normal_pos`) consumes a bundled
`C^∞⟮𝓡 n, _; I, M⟯`.  Packaging it here keeps the `letI` for the charted-space instance in one
place. -/
def levelSetInclMap (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    letI := levelSetChartedSpace hf n c hreg
    C^∞⟮𝓡 n, (f ⁻¹' {c} : Set M); I, M⟯ :=
  letI := levelSetChartedSpace hf n c hreg
  ⟨((↑) : (f ⁻¹' {c} : Set M) → M), contMDiff_levelSet_val hf n c hreg⟩

@[simp] theorem levelSetInclMap_apply (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (p : (f ⁻¹' {c} : Set M)) :
    (levelSetInclMap hf n c hreg : (f ⁻¹' {c} : Set M) → M) p = ↑p := rfl

omit [FiniteDimensional ℝ E] in
/-- **The codimension of the level set is one** — the `hcodim` hypothesis of Proposition 2.70,
in the form it is stated: `finrank (𝓡 n)'s model + 1 = finrank E`. -/
theorem finrank_euclidean_add_one :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + 1 = Module.finrank ℝ E := by
  rw [finrank_euclideanSpace_fin, (Fact.out : Module.finrank ℝ E = n + 1)]

/-- **`T_pM = ker df_p` for the level set**, in the form Proposition 2.70 consumes it: the
tangent range of the inclusion, read inside the pullback fibre, is exactly `ker df_p`.

This is `range_mfderiv_levelSet_val` transported across the fibre synonym
`(ι *ᵖ TM) p = T_{ι p}M`.  The transport is definitional unfolding only — `Bundle.Pullback f E x`
reduces to `E (f x)` — but the `Module` instances on the two sides are not *syntactically* equal,
so the statement is elementwise and the transport is done by `show`/`exact`, never by rewriting
one submodule into the other. -/
theorem mem_tangentRange_levelSetInclMap
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (p : (f ⁻¹' {c} : Set M)) (w : E) :
    letI := levelSetChartedSpace hf n c hreg
    (show ((levelSetInclMap hf n c hreg : (f ⁻¹' {c} : Set M) → M) *ᵖ
        (TangentSpace I : M → Type _)) p from w)
        ∈ tangentRange (levelSetInclMap hf n c hreg) p ↔
      w ∈ levelHyperplane (I := I) f ↑p := by
  letI := levelSetChartedSpace hf n c hreg
  constructor
  · -- `df ∘ dι = d(f ∘ ι) = d(const c) = 0`.
    rintro ⟨u, rfl⟩
    exact (mem_levelHyperplane_iff (I := I) f ↑p _).2
      (mfderivReal_mfderiv_levelSet_val hf n c hreg p u)
  · -- Conversely `ker df_p` is the *whole* range — the dimension count of
    -- `range_mfderiv_levelSet_val`, not a computation.
    intro hw
    rw [← range_mfderiv_levelSet_val hf n c hreg p] at hw
    obtain ⟨u, hu⟩ := hw
    exact ⟨u, hu⟩

variable (g : PseudoRiemannianMetric I M)

/-- **The normal space of the level set is `g`-orthogonal to `ker df_p`.**

The pullback-fibre reading of "`T_pM = ker df_p`": a normal vector at `p`, viewed in `T_pM̃`, is
exactly a vector `g`-orthogonal to `ker df_p`.  This is `mem_tangentRange_levelSetInclMap` plus
the symmetry of `g`, and it is the last step before the pointwise theory of `EmbeddingCriterion`
applies verbatim. -/
theorem mem_orthogonal_ker_of_mem_pseudoNormalSpace
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (p : (f ⁻¹' {c} : Set M))
    (v : letI := levelSetChartedSpace hf n c hreg
      ((levelSetInclMap hf n c hreg : (f ⁻¹' {c} : Set M) → M) *ᵖ
        (TangentSpace I : M → Type _)) p)
    (hv : letI := levelSetChartedSpace hf n c hreg
      haveI := isManifold_levelSet hf n c hreg
      v ∈ pseudoNormalSpace g (levelSetInclMap hf n c hreg) p) :
    (show TangentSpace I (↑p : M) from v)
      ∈ (g.bilin ↑p).orthogonal (LinearMap.ker (dualDifferential I f ↑p)) := by
  letI := levelSetChartedSpace hf n c hreg
  haveI := isManifold_levelSet hf n c hreg
  intro w hw
  -- Unfold `pseudoNormalSpace` by an explicitly ascribed `have`: applying `hv` directly leaves
  -- the domain's `ChartedSpace`/model-space metavariables for instance search to guess, and in a
  -- pullback fibre it guesses the ambient `H`.  Ascription pins every implicit from the goal.
  have hv' : ∀ w ∈ tangentRange (levelSetInclMap hf n c hreg) p, g.form ↑p v w = 0 := hv
  -- `w ∈ ker df_p` is tangent to the level set, so `g(v, w) = 0` because `v` is normal ...
  have hmem := (mem_tangentRange_levelSetInclMap hf n c hreg p (show E from w)).2
    ((mem_levelHyperplane_iff (I := I) f ↑p _).2 hw)
  have h0 : g.form ↑p v (show TangentSpace I (↑p : M) from w) = 0 := hv' _ hmem
  -- ... and `g` is symmetric, which is the side `orthogonal` is stated on.
  show g.bilin ↑p w v = 0
  rw [ContMDiffPseudoMetric.bilin_apply, ← g.symm ↑p v w]
  exact h0

/-- **Lee's hypothesis discharges Proposition 2.70's**, positive case.

Lee assumes only `g̃(grad f, grad f) > 0`; Proposition 2.70 requires *every* nonzero normal to be
positive.  The two agree because the normal space is the line `⟨grad f⟩`, on which `g̃(v,v)` scales
by a square — `pos_apply_self_of_mem_orthogonal_ker`.  This lemma is that pointwise fact
transported across the pullback fibre. -/
theorem forall_normal_pos_of_pseudoGrad_pos
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hpos : ∀ x : M, f x = c → 0 < g.form x (pseudoGrad g f x) (pseudoGrad g f x)) :
    letI := levelSetChartedSpace hf n c hreg
    haveI := isManifold_levelSet hf n c hreg
    ∀ p : (f ⁻¹' {c} : Set M), ∀ v ∈ pseudoNormalSpace g (levelSetInclMap hf n c hreg) p, v ≠ 0 →
      0 < (g.pullback (levelSetInclMap hf n c hreg)).bilin p v v := by
  letI := levelSetChartedSpace hf n c hreg
  haveI := isManifold_levelSet hf n c hreg
  intro p v hv hv0
  exact pos_apply_self_of_mem_orthogonal_ker (g.bilin ↑p) (g.bilin_isSymm ↑p)
    (g.bilin_nondegenerate ↑p) (dualDifferential_ne_zero (hreg ↑p (levelSet_prop c p)))
    (hpos ↑p (levelSet_prop c p))
    (mem_orthogonal_ker_of_mem_pseudoNormalSpace hf n c g hreg p v hv) hv0

/-- **Lee's hypothesis discharges Proposition 2.70's**, negative case — the mirror of
`forall_normal_pos_of_pseudoGrad_pos`, giving the `(r, s-1)` half of Corollary 2.71. -/
theorem forall_normal_neg_of_pseudoGrad_neg
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hneg : ∀ x : M, f x = c → g.form x (pseudoGrad g f x) (pseudoGrad g f x) < 0) :
    letI := levelSetChartedSpace hf n c hreg
    haveI := isManifold_levelSet hf n c hreg
    ∀ p : (f ⁻¹' {c} : Set M), ∀ v ∈ pseudoNormalSpace g (levelSetInclMap hf n c hreg) p, v ≠ 0 →
      (g.pullback (levelSetInclMap hf n c hreg)).bilin p v v < 0 := by
  letI := levelSetChartedSpace hf n c hreg
  haveI := isManifold_levelSet hf n c hreg
  intro p v hv hv0
  exact neg_apply_self_of_mem_orthogonal_ker (g.bilin ↑p) (g.bilin_isSymm ↑p)
    (g.bilin_nondegenerate ↑p) (dualDifferential_ne_zero (hreg ↑p (levelSet_prop c p)))
    (hneg ↑p (levelSet_prop c p))
    (mem_orthogonal_ker_of_mem_pseudoNormalSpace hf n c g hreg p v hv) hv0

/-! ### Lee's Corollary 2.71

Lee assumes only the sign of `g̃(grad f, grad f)` on `M`; that `c` is a regular value — which is
what makes `f^{-1}(c)` a manifold at all — is *derived*, in the first sentence of his proof.  So
`regular_of_pseudoGrad_pos`/`_neg` come first, and the statements below take no `hreg`.
-/

omit [I.Boundaryless] in
/-- **A positive gradient makes `c` a regular value** — the first sentence of Lee's proof of
Corollary 2.71.  This is what lets the corollary be stated with no regularity hypothesis. -/
theorem regular_of_pseudoGrad_pos
    (hpos : ∀ x : M, f x = c → 0 < g.form x (pseudoGrad g f x) (pseudoGrad g f x)) :
    ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 :=
  fun x hx => mfderiv_ne_zero_of_form_pseudoGrad_ne_zero g f x (hpos x hx).ne'

omit [I.Boundaryless] in
/-- **A negative gradient makes `c` a regular value** — the mirror of `regular_of_pseudoGrad_pos`. -/
theorem regular_of_pseudoGrad_neg
    (hneg : ∀ x : M, f x = c → g.form x (pseudoGrad g f x) (pseudoGrad g f x) < 0) :
    ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 :=
  fun x hx => mfderiv_ne_zero_of_form_pseudoGrad_ne_zero g f x (hneg x hx).ne

/-- **Lee, Corollary 2.71, last clause: `grad f` is everywhere normal to `M`.**

For every tangent vector `w` of the level set at `p`, the pseudo-gradient is `g̃`-orthogonal to the
corresponding ambient vector `dι(w)`.  This is the pseudo-Riemannian twin of
`innerAt_grad_mfderiv_levelSet_val_eq_zero` (Proposition 2.37), and needs only the easy inclusion
`T_pM ⊆ ker df_p`. -/
theorem form_pseudoGrad_mfderiv_levelSet_val_eq_zero
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (p : (f ⁻¹' {c} : Set M)) (w : EuclideanSpace ℝ (Fin n)) :
    letI := levelSetChartedSpace hf n c hreg
    g.form (↑p : M) (pseudoGrad g f ↑p)
        (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) p w) = 0 := by
  letI := levelSetChartedSpace hf n c hreg
  rw [form_pseudoGrad]
  exact mfderivReal_mfderiv_levelSet_val hf n c hreg p w

/-- **Lee, Corollary 2.71**, positive case, in full.

If `g̃(grad f, grad f) > 0` everywhere on `M = f^{-1}(c)`, then `M` is an embedded
pseudo-Riemannian submanifold of `M̃` of signature `(r-1, s)`.

Every hypothesis is one a caller actually has: an ambient pseudo-Riemannian metric of signature
`(r,s)`, a smooth `f`, and the sign of `g̃(grad f, grad f)` on the level set.  Regularity of `c` is
*derived* (`regular_of_pseudoGrad_pos`), and the induced metric is *built* — it is
`pseudoPullbackMetric`, the pullback of `g̃` along the inclusion, whose nondegeneracy comes from
the normals being non-null.  That `grad f` is normal to `M` is
`form_pseudoGrad_mfderiv_levelSet_val_eq_zero`.

Truncated subtraction is harmless: Proposition 2.70 delivers `sigPosAt + 1 = r`, forcing `1 ≤ r`. -/
theorem hasSignature_pseudoPullbackMetric_levelSet_of_pseudoGrad_pos {r s : ℕ}
    (hsig : HasSignature g r s)
    (hpos : ∀ x : M, f x = c → 0 < g.form x (pseudoGrad g f x) (pseudoGrad g f x)) :
    letI := levelSetChartedSpace hf n c (regular_of_pseudoGrad_pos c g hpos)
    haveI := isManifold_levelSet hf n c (regular_of_pseudoGrad_pos c g hpos)
    HasSignature (pseudoPullbackMetric g
      (levelSetInclMap hf n c (regular_of_pseudoGrad_pos c g hpos))
      (exists_pseudoPullbackForm_ne_zero g
        (levelSetInclMap hf n c (regular_of_pseudoGrad_pos c g hpos))
        (fun p => mfderiv_levelSet_val_injective hf n c (regular_of_pseudoGrad_pos c g hpos) p)
        (finrank_euclidean_add_one n)
        (fun p v hv hv0 => (forall_normal_pos_of_pseudoGrad_pos hf n c g
          (regular_of_pseudoGrad_pos c g hpos) hpos p v hv hv0).ne'))) (r - 1) s := by
  letI := levelSetChartedSpace hf n c (regular_of_pseudoGrad_pos c g hpos)
  haveI := isManifold_levelSet hf n c (regular_of_pseudoGrad_pos c g hpos)
  exact hasSignature_pseudoPullbackMetric_of_forall_normal_pos g
    (levelSetInclMap hf n c (regular_of_pseudoGrad_pos c g hpos))
    (fun p => mfderiv_levelSet_val_injective hf n c (regular_of_pseudoGrad_pos c g hpos) p)
    (finrank_euclidean_add_one n) hsig
    (forall_normal_pos_of_pseudoGrad_pos hf n c g (regular_of_pseudoGrad_pos c g hpos) hpos)

/-- **Lee, Corollary 2.71**, negative case, in full: if `g̃(grad f, grad f) < 0` everywhere on
`M = f^{-1}(c)`, then `M` is an embedded pseudo-Riemannian submanifold of signature `(r, s-1)`. -/
theorem hasSignature_pseudoPullbackMetric_levelSet_of_pseudoGrad_neg {r s : ℕ}
    (hsig : HasSignature g r s)
    (hneg : ∀ x : M, f x = c → g.form x (pseudoGrad g f x) (pseudoGrad g f x) < 0) :
    letI := levelSetChartedSpace hf n c (regular_of_pseudoGrad_neg c g hneg)
    haveI := isManifold_levelSet hf n c (regular_of_pseudoGrad_neg c g hneg)
    HasSignature (pseudoPullbackMetric g
      (levelSetInclMap hf n c (regular_of_pseudoGrad_neg c g hneg))
      (exists_pseudoPullbackForm_ne_zero g
        (levelSetInclMap hf n c (regular_of_pseudoGrad_neg c g hneg))
        (fun p => mfderiv_levelSet_val_injective hf n c (regular_of_pseudoGrad_neg c g hneg) p)
        (finrank_euclidean_add_one n)
        (fun p v hv hv0 => (forall_normal_neg_of_pseudoGrad_neg hf n c g
          (regular_of_pseudoGrad_neg c g hneg) hneg p v hv hv0).ne))) r (s - 1) := by
  letI := levelSetChartedSpace hf n c (regular_of_pseudoGrad_neg c g hneg)
  haveI := isManifold_levelSet hf n c (regular_of_pseudoGrad_neg c g hneg)
  exact hasSignature_pseudoPullbackMetric_of_forall_normal_neg g
    (levelSetInclMap hf n c (regular_of_pseudoGrad_neg c g hneg))
    (fun p => mfderiv_levelSet_val_injective hf n c (regular_of_pseudoGrad_neg c g hneg) p)
    (finrank_euclidean_add_one n) hsig
    (forall_normal_neg_of_pseudoGrad_neg hf n c g (regular_of_pseudoGrad_neg c g hneg) hneg)

end LevelSet

end LeeLib.Ch02
