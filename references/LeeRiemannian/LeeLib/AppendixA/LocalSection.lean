/-
Appendix A, Theorem A.17: **a smooth submersion admits smooth local sections**.

Lee states this as part of the rank theorem package: if `f : M → M'` is a smooth
submersion and `f x = y`, then there is a smooth local section `σ` of `f`
defined on a neighbourhood of `y` with `σ y = x`.  He derives it from the local
normal form `f(x¹,…,xᵐ) = (x¹,…,xⁿ)` supplied by the rank theorem.

Mathlib has neither the rank theorem nor any notion of submersion (a grep over
the pinned `Mathlib/Geometry/` finds `IsImmersionAt`, whose `mfderiv` API is
entirely TODO, and nothing else), so both halves are built here.  The route
avoids the rank theorem entirely:

* `exists_localSection_of_surjective_fderiv` is the Euclidean statement, proved
  from the inverse function theorem.  Given `f : E → E'` with `fderiv ℝ f a`
  surjective, pair `f` with a continuous linear projection `P` onto
  `ker (fderiv ℝ f a)` to get `G x = (f x, P x)`.  Then `dG a = (df a, P)` is a
  linear *isomorphism* — this is the only computation in the file — so `G` has a
  smooth local inverse `G⁻¹`, and `σ y = G⁻¹(y, P a)` is a local section of `f`.

* `exists_localSection` transports that to manifolds through `extChartAt`.  This
  costs nothing beyond bookkeeping because `mfderiv` is *defined* as
  `fderivWithin ℝ (writtenInExtChartAt I I' x f) (range I) (extChartAt I x x)`,
  and `range I = univ` for a boundaryless model, so the surjectivity hypothesis
  on `mfderiv` *is* the Euclidean hypothesis on the chart representation.

## Why boundaryless

`fderivWithin ℝ · (range I)` collapses to `fderiv ℝ ·` exactly when
`range I = univ`, and `(extChartAt I x).target` is a neighbourhood of
`extChartAt I x x` — needed to compose with `(extChartAt I x).symm` — only then
as well.  Both are `ModelWithCorners.Boundaryless`.  This matches Lee, who
states the rank theorem for manifolds without boundary.

The two-sided conclusion is deliberately `∀ᶠ y in 𝓝 (f x), f (σ y) = y` rather
than a section defined on a named open set: every consumer (the smoothness of a
quotient metric, Lee's Theorem 2.28) needs only `ContMDiffAt` at the one point,
for which a germ is enough.
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

namespace LeeLib.AppendixA

open Set Filter
open scoped Manifold ContDiff Topology

/-! ## The linear algebra: a surjection paired with a projection onto its kernel

If `A : E →L[ℝ] E'` is surjective and `P : E →L[ℝ] ker A` is any projection onto
the kernel, then `v ↦ (A v, P v)` is a linear isomorphism `E ≃ E' × ker A`.  This
is the standard splitting `E ≅ E/ker A ⊕ ker A`, written so that the first
component is literally `A` — which is what makes `σ` below a section of `f`
rather than of something conjugate to it.

Mathlib already has the equivalence itself, as
`ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl`; all that is added here is
the projection `kerProj` to feed it, which exists because a subspace of a
finite-dimensional space is complemented. -/

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']

variable (A : E →L[ℝ] E')

/-- A complement of `ker A`, chosen once so that `kerProj` is a definition rather
than an existential. -/
private noncomputable def kerCompl : Submodule ℝ E :=
  (Submodule.exists_isCompl (LinearMap.ker (A : E →ₗ[ℝ] E'))).choose

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
private theorem isCompl_kerCompl :
    IsCompl (LinearMap.ker (A : E →ₗ[ℝ] E')) (kerCompl A) :=
  (Submodule.exists_isCompl (LinearMap.ker (A : E →ₗ[ℝ] E'))).choose_spec

/-- **A continuous linear projection of `E` onto `ker A`.**  It exists because
every subspace of a finite-dimensional space is complemented, and it is
continuous because every linear map out of a finite-dimensional space is. -/
noncomputable def kerProj : E →L[ℝ] (LinearMap.ker (A : E →ₗ[ℝ] E')) :=
  LinearMap.toContinuousLinearMap
    (Submodule.linearProjOfIsCompl _ _ (isCompl_kerCompl A))

omit [FiniteDimensional ℝ E'] in
@[simp]
theorem kerProj_coe_apply (v : LinearMap.ker (A : E →ₗ[ℝ] E')) : kerProj A (v : E) = v :=
  Submodule.linearProjOfIsCompl_apply_left (isCompl_kerCompl A) v

omit [FiniteDimensional ℝ E'] in
theorem kerProj_range :
    LinearMap.range ((kerProj A : E →ₗ[ℝ] (LinearMap.ker (A : E →ₗ[ℝ] E')))) = ⊤ :=
  Submodule.linearProjOfIsCompl_range (isCompl_kerCompl A)

omit [FiniteDimensional ℝ E'] in
theorem kerProj_ker :
    LinearMap.ker ((kerProj A : E →ₗ[ℝ] (LinearMap.ker (A : E →ₗ[ℝ] E')))) = kerCompl A :=
  Submodule.linearProjOfIsCompl_ker (isCompl_kerCompl A)

/-- **`A` paired with the projection onto its kernel is a linear isomorphism**,
when `A` is surjective.  This is the splitting `E ≅ E' × ker A` induced by `A`. -/
noncomputable def prodKerProjEquiv (hA : Function.Surjective A) :
    E ≃L[ℝ] E' × (LinearMap.ker (A : E →ₗ[ℝ] E')) :=
  ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl A (kerProj A)
    (LinearMap.range_eq_top.mpr hA) (kerProj_range A)
    (by rw [kerProj_ker]; exact isCompl_kerCompl A)

@[simp]
theorem prodKerProjEquiv_coe (hA : Function.Surjective A) :
    ((prodKerProjEquiv A hA : E ≃L[ℝ] E' × (LinearMap.ker (A : E →ₗ[ℝ] E')))
        : E →L[ℝ] E' × (LinearMap.ker (A : E →ₗ[ℝ] E')))
      = A.prod (kerProj A) :=
  ContinuousLinearMap.ext fun _ => rfl

end Linear

/-! ## The Euclidean local section theorem -/

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']

/-- **Local sections of a map with surjective differential** (Euclidean form; the
analytic content of Lee's Theorem A.17).

If `f : E → E'` is `C^∞` at `a` and `fderiv ℝ f a` is surjective, then `f` has a
`C^∞` local section through `a`: a map `σ` defined near `f a`, smooth at `f a`,
with `σ (f a) = a` and `f (σ y) = y` for all `y` near `f a`.

The proof is the inverse function theorem applied to `G x = (f x, P x)`, where
`P` projects onto `ker (fderiv ℝ f a)`; then `σ y = G⁻¹ (y, P a)`. -/
theorem exists_localSection_of_surjective_fderiv {f : E → E'} {a : E}
    (hf : ContDiffAt ℝ ∞ f a) (hsurj : Function.Surjective (fderiv ℝ f a)) :
    ∃ σ : E' → E, ContDiffAt ℝ ∞ σ (f a) ∧ σ (f a) = a ∧ ∀ᶠ y in 𝓝 (f a), f (σ y) = y := by
  set A := fderiv ℝ f a with hAdef
  set P := kerProj A with hPdef
  have hfd : HasFDerivAt f A a := (hf.differentiableAt (by simp)).hasFDerivAt
  -- `G` pairs `f` with the projection onto `ker (df a)`; its derivative is an isomorphism.
  set G : E → E' × (LinearMap.ker (A : E →ₗ[ℝ] E')) := fun x => (f x, P x) with hGdef
  have hGd : ContDiffAt ℝ ∞ G a := hf.prodMk (P.contDiff.contDiffAt)
  set Fe := prodKerProjEquiv A hsurj with hFedef
  have hGf : HasFDerivAt G (Fe : E →L[ℝ] E' × (LinearMap.ker (A : E →ₗ[ℝ] E'))) a := by
    rw [hFedef, prodKerProjEquiv_coe]
    exact hfd.prodMk P.hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hs : HasStrictFDerivAt G (Fe : E →L[ℝ] E' × (LinearMap.ker (A : E →ₗ[ℝ] E'))) a :=
    hGd.hasStrictFDerivAt' hGf hn
  -- The inverse function theorem inverts `G`; freezing the second slot at `P a` sections `f`.
  refine ⟨fun y => hGd.localInverse hGf hn (y, P a), ?_, ?_, ?_⟩
  · have ht : ContDiffAt ℝ ∞ (fun y : E' => (y, P a)) (f a) :=
      contDiffAt_id.prodMk contDiffAt_const
    exact (hGd.to_localInverse hGf hn).comp (f a) ht
  · exact hGd.localInverse_apply_image hGf hn
  · have ht : Tendsto (fun y : E' => (y, P a)) (𝓝 (f a)) (𝓝 (G a)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    filter_upwards [ht.eventually hs.eventually_right_inverse] with y hy
    exact congrArg Prod.fst hy

end Euclidean

/-! ## The manifold local section theorem -/

section Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

omit [IsManifold I' ∞ M'] in
/-- **Lee, Theorem A.17**: *a smooth map whose differential at `x` is surjective
admits a smooth local section through `x`.*

There is a map `σ : M' → M`, smooth at `f x`, with `σ (f x) = x` and
`f (σ y) = y` for every `y` near `f x`.  Applied at every point of a submersion,
this is the statement that a submersion is locally a projection — which is how
Lee uses it, and it is what makes the quotient metric of Theorem 2.28 smooth.

Mathlib has no rank theorem, so this is proved directly from the inverse function
theorem via `exists_localSection_of_surjective_fderiv`: because `mfderiv` *is*
`fderivWithin` of the chart representation over `range I = univ`, the hypothesis
here is literally the Euclidean hypothesis there.

Only the *source* model `I` need be boundaryless: `range I'` never enters, since
the chart of `M'` is used only through `extChartAt I' (f x)` and its injectivity
on its source.  So `M'` is allowed to have boundary, which is slightly stronger
than Lee's statement. -/
theorem exists_localSection {f : M → M'} (hf : ContMDiff I I' ∞ f) {x : M}
    (hsurj : Function.Surjective (mfderiv I I' f x)) :
    ∃ σ : M' → M, ContMDiffAt I' I ∞ σ (f x) ∧ σ (f x) = x ∧
      ∀ᶠ y in 𝓝 (f x), f (σ y) = y := by
  set φ := extChartAt I x with hφdef
  set ψ := extChartAt I' (f x) with hψdef
  set a := φ x with hadef
  set F := writtenInExtChartAt I I' x f with hFdef
  have hxs : x ∈ φ.source := mem_extChartAt_source (I := I) x
  have hys : f x ∈ ψ.source := mem_extChartAt_source (I := I') (f x)
  have hinv : φ.symm a = x := extChartAt_to_inv (I := I) x
  -- `F a = ψ (f x)`: the chart round-trip at the centre is the identity.
  have hFa : F a = ψ (f x) := by rw [hFdef, writtenInExtChartAt, Function.comp_apply,
    Function.comp_apply, hinv]
  -- The chart representation is `C^∞` at `a` (`range I = univ` kills the `Within`).
  have hFd : ContDiffAt ℝ ∞ F a := by
    have h := (contMDiffAt_iff (I := I) (I' := I') (n := ∞) (f := f) (x := x)).mp hf.contMDiffAt
    have h2 := h.2
    rw [I.range_eq_univ, contDiffWithinAt_univ] at h2
    exact h2
  -- The submersion hypothesis, read in the chart: `mfderiv` *is* this `fderivWithin`.
  have hFsurj : Function.Surjective (fderiv ℝ F a) := by
    have hmd : MDifferentiableAt I I' f x := hf.mdifferentiableAt (by simp)
    rw [mfderiv, if_pos hmd, I.range_eq_univ, fderivWithin_univ] at hsurj
    exact hsurj
  obtain ⟨σE, hσEd, hσEa, hσEr⟩ := exists_localSection_of_surjective_fderiv hFd hFsurj
  refine ⟨fun y => φ.symm (σE (ψ y)), ?_, ?_, ?_⟩
  · -- `σ` is a composite of `ψ` (smooth), `σE` (smooth), and `φ.symm` (smooth on the
    -- chart target, which is open and contains `σE (ψ (f x)) = a`).
    have h1 : ContMDiffAt I' 𝓘(ℝ, E') ∞ ψ (f x) := contMDiffAt_extChartAt (I := I') (x := f x)
    have h2 : ContMDiffAt 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ σE (ψ (f x)) := by
      rw [← hFa]; exact hσEd.contMDiffAt
    have hσa : σE (ψ (f x)) = a := by rw [← hFa]; exact hσEa
    have h3 : ContMDiffAt 𝓘(ℝ, E) I ∞ φ.symm (σE (ψ (f x))) := by
      rw [hσa]
      exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).contMDiffAt
        ((isOpen_extChartAt_target (I := I) x).mem_nhds
          (by rw [hadef]; exact mem_extChartAt_target (I := I) x))
    exact (h3.comp (f x) (h2.comp (f x) h1))
  · show φ.symm (σE (ψ (f x))) = x
    rw [← hFa, hσEa, hinv]
  · -- `ψ (f (σ y)) = ψ y` near `f x`; cancel `ψ`, which is injective on its source.
    have hcont : ContinuousAt ψ (f x) := continuousAt_extChartAt (I := I') (f x)
    have hpull : ∀ᶠ y in 𝓝 (f x), F (σE (ψ y)) = ψ y := by
      have ht : Tendsto ψ (𝓝 (f x)) (𝓝 (F a)) := by rw [hFa]; exact hcont
      exact ht.eventually hσEr
    -- `y` and `f (σ y)` must both sit in `ψ.source` for cancellation.
    have hy : ∀ᶠ y in 𝓝 (f x), y ∈ ψ.source := extChartAt_source_mem_nhds (I := I') (f x)
    have hfσ : ∀ᶠ y in 𝓝 (f x), f (φ.symm (σE (ψ y))) ∈ ψ.source := by
      have hc : ContinuousAt (fun y => f (φ.symm (σE (ψ y)))) (f x) := by
        have h1 : ContMDiffAt I' 𝓘(ℝ, E') ∞ ψ (f x) := contMDiffAt_extChartAt (I := I') (x := f x)
        have h2 : ContMDiffAt 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ σE (ψ (f x)) := by
          rw [← hFa]; exact hσEd.contMDiffAt
        have hσa : σE (ψ (f x)) = a := by rw [← hFa]; exact hσEa
        have h3 : ContMDiffAt 𝓘(ℝ, E) I ∞ φ.symm (σE (ψ (f x))) := by
          rw [hσa]
          exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).contMDiffAt
            ((isOpen_extChartAt_target (I := I) x).mem_nhds
              (by rw [hadef]; exact mem_extChartAt_target (I := I) x))
        exact (hf.contMDiffAt.comp (f x) (h3.comp (f x) (h2.comp (f x) h1))).continuousAt
      have hval : f (φ.symm (σE (ψ (f x)))) = f x := by
        rw [← hFa, hσEa, hinv]
      exact hc.preimage_mem_nhds (by rw [hval]; exact extChartAt_source_mem_nhds (I := I') (f x))
    filter_upwards [hpull, hy, hfσ] with y hy1 hy2 hy3
    -- `F (σE (ψ y)) = ψ (f (φ.symm (σE (ψ y))))` by definition of `writtenInExtChartAt`.
    have hFdef' : F (σE (ψ y)) = ψ (f (φ.symm (σE (ψ y)))) := rfl
    rw [hFdef'] at hy1
    exact ψ.injOn hy3 hy2 hy1

end Manifold

end LeeLib.AppendixA
