import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Smooth local sections of a submersion

If `q : M → M'` is smooth and its differential `mfderiv I I' q p` is
**surjective** (i.e. `q` is a submersion at `p`), then `q` admits a smooth
**local section** through `p`: a map `s : M' → M`, smooth at `q p`, with
`s (q p) = p` and `q (s y) = y` for all `y` near `q p`.

This is the missing ingredient behind the manifold inverse function theorem,
which Mathlib currently lists only as a TODO in
`Mathlib/Geometry/Manifold/LocalDiffeomorph.lean`:

> if `f` is `C^n` at `x` and `mfderiv I J n f x` is a linear isomorphism,
> `f` is a local diffeomorphism at `x` (using the inverse function theorem).

The submersion statement proved here is strictly stronger than that TODO:
a bijective differential is in particular surjective, so
`exists_localSection_of_mfderiv_surjective` also covers the local-diffeomorphism
(and hence the smooth-covering) case, which is what Petersen's quotient
constructions in §1.3 need.

## Proof

Everything happens in the extended charts.  Write `F := writtenInExtChartAt I I' p q`
for the chart representative of `q`, `a := extChartAt I p p` and `b := F a = extChartAt I' (q p) (q p)`.
Boundarylessness turns `mfderiv` into an honest `fderiv` and `ContMDiffAt` into an
honest `ContDiffAt`, so `DF a := fderiv ℝ F a : E →L[ℝ] E'` is surjective.

The point is that one does **not** need the rank theorem or any submanifold
structure.  Pick a continuous-linear **right inverse** `R : E' →L[ℝ] E` of `DF a`
(available because `E'` is finite dimensional), and set

  `G : E' → E',   G y := F (a + R (y - b))`.

Then `G b = F a = b` and, by the chain rule, `D G b = (DF a) ∘ R = id`, which is a
linear *isomorphism*.  So the ordinary **normed-space** inverse function theorem
(`ContDiffAt.to_localInverse`) applies to `G` and produces a local inverse `Ginv`,
smooth at `b`, with `G (Ginv y) = y` near `b`.  Unwinding,

  `σ : E' → E,   σ y := a + R (Ginv y - b)`

satisfies `F (σ y) = G (Ginv y) = y` near `b` and `σ b = a`: a smooth local section
of `F`.  Transporting `σ` back through the charts gives `s`.

## Main results

* `exists_localSection_of_mfderiv_surjective`: the smooth local section.
* `mfderiv_comp_mfderiv_localSection`: along such a section, `Dq ∘ Ds = id`; in
  particular `Ds y` is a right inverse of `Dq (s y)`, and a two-sided inverse as
  soon as `Dq (s y)` is injective.

## Tags

submersion, local section, inverse function theorem, local diffeomorphism
-/

open Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

section LocalSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ### From `ContMDiffAt` / `mfderiv` to `ContDiffAt` / `fderiv` in the charts -/

variable [I.Boundaryless] [I'.Boundaryless]

/-- **Eng.** In the boundaryless case, `ContMDiffAt` of `q` at `p` gives honest
`ContDiffAt` of the chart representative `writtenInExtChartAt I I' p q` at
`extChartAt I p p` (the model-space differentiability is `ContDiffWithinAt` on
`range I = univ`). -/
theorem contDiffAt_writtenInExtChartAt {q : M → M'} {p : M} {n : ℕ∞ω}
    (hq : ContMDiffAt I I' n q p) :
    ContDiffAt ℝ n (writtenInExtChartAt I I' p q) (extChartAt I p p) := by
  have h := (contMDiffAt_iff.mp hq).2
  rwa [I.range_eq_univ, contDiffWithinAt_univ] at h

/-- **Eng.** In the boundaryless case, the manifold differential *is* the
`fderiv` of the chart representative: `mfderiv I I' q p = fderiv ℝ (writtenInExtChartAt I I' p q) (extChartAt I p p)`,
under the definitional identifications `TangentSpace I p = E`, `TangentSpace I' (q p) = E'`. -/
theorem mfderiv_eq_fderiv_writtenInExtChartAt {q : M → M'} {p : M}
    (hq : MDifferentiableAt I I' q p) :
    (mfderiv I I' q p : E →L[ℝ] E') =
      fderiv ℝ (writtenInExtChartAt I I' p q) (extChartAt I p p) := by
  rw [mfderiv, if_pos hq, I.range_eq_univ, fderivWithin_univ]

end LocalSection

section Existence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Eng.** A surjective continuous linear map out of a space into a
*finite-dimensional* space admits a continuous-linear right inverse.  (Choose any
linear right inverse; it is automatically continuous since its domain `E'` is
finite dimensional.) -/
theorem exists_continuousLinear_rightInverse {A : E →L[ℝ] E'}
    (hA : Function.Surjective A) :
    ∃ R : E' →L[ℝ] E, ∀ y : E', A (R y) = y := by
  obtain ⟨R₀, hR₀⟩ := (A : E →ₗ[ℝ] E').exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hA)
  refine ⟨R₀.toContinuousLinearMap, fun y => ?_⟩
  have := LinearMap.congr_fun hR₀ y
  simpa using this

/-- **Eng.** The affine map `y ↦ a + R (y - b)` has derivative `R` everywhere; we
only need it at `b`, where it takes the value `a`. -/
theorem hasFDerivAt_affineLift (a : E) (R : E' →L[ℝ] E) (b y : E') :
    HasFDerivAt (fun z : E' => a + R (z - b)) R y := by
  have h1 : HasFDerivAt (fun z : E' => z - b) (ContinuousLinearMap.id ℝ E') y :=
    (hasFDerivAt_id y).sub_const b
  have h2 : HasFDerivAt (fun z : E' => R (z - b)) R y := by
    have h := R.hasFDerivAt.comp y h1
    rwa [ContinuousLinearMap.comp_id] at h
  exact h2.const_add a

/-- **Eng.** The affine map `y ↦ a + R (y - b)` is `C^∞`. -/
theorem contDiff_affineLift (a : E) (R : E' →L[ℝ] E) (b : E') :
    ContDiff ℝ ∞ (fun z : E' => a + R (z - b)) := by fun_prop

/-- **Math.** **Smooth local sections of a submersion.**  If `q` is `C^∞` at `p`
and `mfderiv I I' q p` is surjective, then `q` has a smooth local section through
`p`: there is `s : M' → M` with `s (q p) = p`, `s` smooth at `q p`, and
`q (s y) = y` for all `y` in a neighbourhood of `q p`.

This is the manifold inverse function theorem in the form Petersen's quotient
constructions need; a *bijective* differential is in particular surjective, so
this also yields smooth local inverses of local diffeomorphisms and of smooth
covering maps.  See the module docstring for the (rank-theorem-free) proof. -/
theorem exists_localSection_of_mfderiv_surjective {q : M → M'} {p : M}
    (hq : ContMDiffAt I I' ∞ q p)
    (hsurj : Function.Surjective (mfderiv I I' q p)) :
    ∃ s : M' → M, s (q p) = p ∧ ContMDiffAt I' I ∞ s (q p) ∧
      (∀ᶠ y in 𝓝 (q p), q (s y) = y) ∧
      (∀ᶠ y in 𝓝 (q p), MDifferentiableAt I' I s y) := by
  -- Notation for the two extended charts and the chart representative of `q`.
  set φ := extChartAt I p with hφ
  set ψ := extChartAt I' (q p) with hψ
  set a : E := φ p with ha
  set b : E' := ψ (q p) with hb
  set F : E → E' := writtenInExtChartAt I I' p q with hF
  -- `F` is literally `ψ ∘ q ∘ φ.symm`, and it sends `a` to `b`.
  have hFapp : ∀ w : E, F w = ψ (q (φ.symm w)) := fun w => rfl
  have hFa : F a = b := by rw [hFapp, ha, hφ, extChartAt_to_inv]
  -- Chart-level smoothness and differential of `q`.
  have hFdiff : ContDiffAt ℝ ∞ F a := contDiffAt_writtenInExtChartAt hq
  have hqmd : MDifferentiableAt I I' q p := hq.mdifferentiableAt (by simp)
  set A : E →L[ℝ] E' := fderiv ℝ F a with hA
  have hAeq : (mfderiv I I' q p : E →L[ℝ] E') = A :=
    mfderiv_eq_fderiv_writtenInExtChartAt hqmd
  have hAsurj : Function.Surjective A := by rw [← hAeq]; exact hsurj
  -- A continuous-linear right inverse `R` of `A` (here `E'` is finite dimensional).
  obtain ⟨R, hR⟩ := exists_continuousLinear_rightInverse hAsurj
  -- The affine "lift" `T y = a + R (y - b)`, with `T b = a` and `DT = R`.
  set T : E' → E := fun y => a + R (y - b) with hT
  have hTb : T b = a := by simp [hT]
  have hThas : HasFDerivAt T R b := hasFDerivAt_affineLift a R b b
  have hTdiffEvery : ∀ z : E', ContDiffAt ℝ ∞ T z := fun z =>
    (contDiff_affineLift a R b).contDiffAt
  have hTdiff : ContDiffAt ℝ ∞ T b := hTdiffEvery b
  -- `G := F ∘ T` fixes `b` and has derivative `A ∘ R = id` there: the normed-space
  -- inverse function theorem applies to `G`.
  set G : E' → E' := fun y => F (T y) with hG
  have hGb : G b = b := by rw [hG]; simp only []; rw [hTb, hFa]
  have hFhas : HasFDerivAt F A a := (hFdiff.differentiableAt (by simp)).hasFDerivAt
  have hGhas : HasFDerivAt G ((ContinuousLinearEquiv.refl ℝ E' : E' ≃L[ℝ] E') :
      E' →L[ℝ] E') b := by
    have h := (hTb ▸ hFhas : HasFDerivAt F A (T b)).comp b hThas
    have hid : A.comp R = ((ContinuousLinearEquiv.refl ℝ E' : E' ≃L[ℝ] E') : E' →L[ℝ] E') := by
      ext y; simpa using hR y
    rwa [hid] at h
  have hGdiff : ContDiffAt ℝ ∞ G b := (hTb ▸ hFdiff : ContDiffAt ℝ ∞ F (T b)).comp b hTdiff
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  -- The local inverse of `G`, smooth at `b`, fixing `b`, right-inverting `G` near `b`.
  set Ginv : E' → E' := hGdiff.localInverse hGhas hn with hGinv
  have hGinvdiff : ContDiffAt ℝ ∞ Ginv b := by
    have := hGdiff.to_localInverse (f' := (ContinuousLinearEquiv.refl ℝ E')) hGhas hn
    rwa [hGb] at this
  have hGinvb : Ginv b = b := by
    have := hGdiff.localInverse_apply_image (f' := (ContinuousLinearEquiv.refl ℝ E')) hGhas hn
    rwa [hGb] at this
  have hGright : ∀ᶠ z in 𝓝 b, G (Ginv z) = z := by
    have hstrict : HasStrictFDerivAt G
        ((ContinuousLinearEquiv.refl ℝ E' : E' ≃L[ℝ] E') : E' →L[ℝ] E') b :=
      hGdiff.hasStrictFDerivAt' hGhas hn
    have := hstrict.eventually_right_inverse
    rwa [hGb] at this
  -- `σ := T ∘ Ginv` is a smooth local section of the chart representative `F`.
  set σ : E' → E := fun z => T (Ginv z) with hσ
  have hσb : σ b = a := by rw [hσ]; simp only []; rw [hGinvb, hTb]
  have hσdiff : ContDiffAt ℝ ∞ σ b := (hTdiffEvery (Ginv b)).comp b hGinvdiff
  have hσsec : ∀ᶠ z in 𝓝 b, F (σ z) = z := hGright
  -- Transport `σ` back through the charts.
  set s : M' → M := fun y => φ.symm (σ (ψ y)) with hs
  have hsqp : s (q p) = p := by rw [hs]; simp only []; rw [← hb, hσb, ha, hφ, extChartAt_to_inv]
  -- Continuity of the three factors, hence of `s`, at the relevant points.
  have hψcont : ContinuousAt ψ (q p) := continuousAt_extChartAt (q p)
  have hσcont : ContinuousAt σ b := hσdiff.continuousAt
  have hφsymmcont : ContinuousAt φ.symm a := continuousAt_extChartAt_symm p
  have hσψ : ContinuousAt (fun y : M' => σ (ψ y)) (q p) :=
    ContinuousAt.comp (g := σ) (f := fun y : M' => ψ y) hσcont hψcont
  have hscont : ContinuousAt s (q p) := by
    have h2 : ContinuousAt (φ.symm : E → M) (σ (ψ (q p))) := by
      rw [← hb, hσb]; exact hφsymmcont
    exact ContinuousAt.comp (g := (φ.symm : E → M)) (f := fun y : M' => σ (ψ y)) h2 hσψ
  -- The two chart neighbourhoods we keep landing in.
  have hψtgt : ∀ᶠ z in 𝓝 b, z ∈ ψ.target := extChartAt_target_mem_nhds (q p)
  have hφtgt : ∀ᶠ z in 𝓝 b, σ z ∈ φ.target :=
    hσcont.eventually (by rw [hσb]; exact extChartAt_target_mem_nhds p)
  refine ⟨s, hsqp, ?_, ?_, ?_⟩
  · -- `s` is smooth at `q p`: in the charts it *is* `σ`.
    rw [contMDiffAt_iff]
    refine ⟨hscont, ?_⟩
    rw [hsqp, I'.range_eq_univ, contDiffWithinAt_univ, ← hφ, ← hψ, ← hb]
    refine hσdiff.congr_of_eventuallyEq ?_
    filter_upwards [hψtgt, hφtgt] with z hz hσz
    show φ (s (ψ.symm z)) = σ z
    rw [hs]
    simp only []
    rw [ψ.right_inv hz]
    exact φ.right_inv hσz
  · -- `q (s y) = y` near `q p`: apply `ψ` and use that `σ` sections `F`.
    have h1 : ∀ᶠ y in 𝓝 (q p), F (σ (ψ y)) = ψ y := hψcont.eventually hσsec
    have h2 : ∀ᶠ y in 𝓝 (q p), y ∈ ψ.source := extChartAt_source_mem_nhds (q p)
    have h3 : ∀ᶠ y in 𝓝 (q p), q (s y) ∈ ψ.source := by
      have hqcont : ContinuousAt q (s (q p)) := by rw [hsqp]; exact hq.continuousAt
      have hqs : ContinuousAt (fun y => q (s y)) (q p) :=
        ContinuousAt.comp (g := q) (f := s) hqcont hscont
      refine hqs.eventually ?_
      show ∀ᶠ z in 𝓝 (q (s (q p))), z ∈ ψ.source
      rw [hsqp]
      exact extChartAt_source_mem_nhds (q p)
    filter_upwards [h1, h2, h3] with y hy hys hqsy
    -- `ψ (q (s y)) = F (σ (ψ y)) = ψ y`, and `ψ` is injective on its source.
    refine ψ.injOn hqsy hys ?_
    rw [← hy, hFapp, hs]
  · -- `s` is differentiable at every point *near* `q p`.
    -- `C^∞`-at-a-point does not propagate (the neighbourhood depends on the order),
    -- but `C^1` does, and `C^1` is all that `MDifferentiableAt` needs.
    have hσ1 : ∀ᶠ z in 𝓝 b, ContDiffAt ℝ 1 σ z :=
      (hσdiff.of_le (by exact_mod_cast le_top)).eventually (by simp)
    have e1 : ∀ᶠ y in 𝓝 (q p), y ∈ (chartAt H' (q p)).source :=
      (chartAt H' (q p)).open_source.mem_nhds (mem_chart_source H' (q p))
    have e2 : ∀ᶠ y in 𝓝 (q p), ContDiffAt ℝ 1 σ (ψ y) := hψcont.eventually hσ1
    have e3 : ∀ᶠ y in 𝓝 (q p), σ (ψ y) ∈ φ.target := hψcont.eventually hφtgt
    filter_upwards [e1, e2, e3] with y hy hσy hφy
    -- `s = φ.symm ∘ σ ∘ ψ`, each factor differentiable at the relevant point.
    have h1 : MDifferentiableAt I' 𝓘(ℝ, E') (ψ : M' → E') y :=
      (contMDiffAt_extChartAt' (n := 1) hy).mdifferentiableAt (by simp)
    have h2 : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, E) σ (ψ y) :=
      (contMDiffAt_iff_contDiffAt.mpr hσy).mdifferentiableAt (by simp)
    have h3 : MDifferentiableAt 𝓘(ℝ, E) I (φ.symm : E → M) (σ (ψ y)) :=
      ((contMDiffOn_extChartAt_symm (n := 1) p).contMDiffAt
        (extChartAt_target_mem_nhds' hφy)).mdifferentiableAt (by simp)
    have h21 : MDifferentiableAt I' 𝓘(ℝ, E) (fun w : M' => σ (ψ w)) y :=
      MDifferentiableAt.comp (g := σ) (f := fun w : M' => ψ w) (x := y) h2 h1
    exact MDifferentiableAt.comp (g := (φ.symm : E → M)) (f := fun w : M' => σ (ψ w))
      (x := y) h3 h21

end Existence

section ChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** Along a local section, the differentials compose to the identity:
if `q (s y) = y` near `y₀`, then `Dq_{s y₀} ∘ Ds_{y₀} = id`.  In particular
`Ds_{y₀}` is a right inverse of `Dq_{s y₀}` — and a two-sided inverse whenever
`Dq_{s y₀}` is injective, which is what identifies the quotient metric with the
pullback of `g` along `s`. -/
theorem mfderiv_comp_mfderiv_localSection {q : M → M'} {s : M' → M} {y₀ : M'}
    (hs : MDifferentiableAt I' I s y₀) (hq : MDifferentiableAt I I' q (s y₀))
    (hsec : ∀ᶠ y in 𝓝 y₀, q (s y) = y) :
    (mfderiv I I' q (s y₀)).comp (mfderiv I' I s y₀) =
      ContinuousLinearMap.id ℝ (TangentSpace I' y₀) := by
  have hcomp : mfderiv I' I' (q ∘ s) y₀ =
      (mfderiv I I' q (s y₀)).comp (mfderiv I' I s y₀) := mfderiv_comp y₀ hq hs
  have hEq : (q ∘ s) =ᶠ[𝓝 y₀] id := by
    filter_upwards [hsec] with y hy using hy
  have hid : mfderiv I' I' (q ∘ s) y₀ = ContinuousLinearMap.id ℝ (TangentSpace I' y₀) := by
    rw [hEq.mfderiv_eq, mfderiv_id]
  rw [← hcomp, hid]

/-- **Math.** If moreover `Dq_{s y₀}` is *injective* (so bijective, `q` being a
submersion there), the section's differential is exactly its inverse:
`Ds_{y₀} u` is the unique `Dq`-preimage of `u`. -/
theorem mfderiv_localSection_eq_symm {q : M → M'} {s : M' → M} {y₀ : M'}
    (hs : MDifferentiableAt I' I s y₀) (hq : MDifferentiableAt I I' q (s y₀))
    (hsec : ∀ᶠ y in 𝓝 y₀, q (s y) = y) (u : TangentSpace I' y₀) :
    mfderiv I I' q (s y₀) (mfderiv I' I s y₀ u) = u := by
  have h := mfderiv_comp_mfderiv_localSection hs hq hsec
  exact congrArg (fun L : TangentSpace I' y₀ →L[ℝ] TangentSpace I' y₀ => L u) h

end ChainRule

/-! ## The manifold inverse function theorem

Applying the local-section theorem *twice* — once to `q`, once to the section it
produces — upgrades a right inverse to a genuine two-sided local inverse.  This is
exactly Mathlib's `LocalDiffeomorph.lean` TODO ("if `f` is `C^n` at `x` and
`mfderiv I J n f x` is a linear isomorphism, `f` is a local diffeomorphism at
`x`"), and also the "injective differential + equal dimension ⇒ local
diffeomorphism" gap that `Mathlib/Geometry/Manifold/Immersion.lean` records. -/

section InverseFunctionTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** **The inverse function theorem for manifolds.**  If `q` is `C^∞` at
`p` and its differential `mfderiv I I' q p` is *bijective*, then `q` is a local
diffeomorphism at `p`: there is `s : M' → M`, smooth at `q p`, which is a
two-sided local inverse of `q` — `q (s y) = y` near `q p` **and** `s (q x) = x`
near `p`.

The right inverse is `exists_localSection_of_mfderiv_surjective` applied to `q`.
For the *left* inverse, apply the same theorem again to `s`: its differential at
`q p` is bijective (it is injective because `Dq ∘ Ds = id`, hence surjective since
`E` and `E'` have equal dimension), producing `t` with `s (t x) = x` near `p`.
Then `q (s (t x)) = q x` while `q ∘ s = id` forces `q (s (t x)) = t x`, so `t = q`
near `p` and therefore `s (q x) = s (t x) = x`. -/
theorem exists_localInverse_of_mfderiv_bijective {q : M → M'} {p : M}
    (hq : ContMDiffAt I I' ∞ q p)
    (hbij : Function.Bijective (mfderiv I I' q p)) :
    ∃ s : M' → M, s (q p) = p ∧ ContMDiffAt I' I ∞ s (q p) ∧
      (∀ᶠ y in 𝓝 (q p), q (s y) = y) ∧ (∀ᶠ x in 𝓝 p, s (q x) = x) := by
  obtain ⟨s, hs0, hsdiff, hssec, hsmd⟩ :=
    exists_localSection_of_mfderiv_surjective hq hbij.2
  -- `Dq_p` is a linear equivalence, so `E` and `E'` have the same dimension.
  set Dq : E →L[ℝ] E' := mfderiv I I' q p with hDq
  have hDqbij : Function.Bijective Dq := hbij
  have hrank : Module.finrank ℝ E = Module.finrank ℝ E' :=
    LinearEquiv.finrank_eq (LinearEquiv.ofBijective Dq.toLinearMap hDqbij)
  -- `Ds` at `q p` is injective (a right inverse of `Dq`), hence bijective.
  have hqmd : MDifferentiableAt I I' q (s (q p)) := by
    rw [hs0]; exact hq.mdifferentiableAt (by simp)
  have hsmd0 : MDifferentiableAt I' I s (q p) := hsdiff.mdifferentiableAt (by simp)
  set Ds : E' →L[ℝ] E := mfderiv I' I s (q p) with hDs
  have hDs_left : ∀ u : E',
      (mfderiv I I' q (s (q p)) : E →L[ℝ] E') (Ds u) = u :=
    mfderiv_localSection_eq_symm hsmd0 hqmd hssec
  have hsinj : Function.Injective Ds := by
    intro u v huv
    rw [← hDs_left u, ← hDs_left v, huv]
  have hsbij : Function.Bijective Ds := by
    refine ⟨hsinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := Ds.toLinearMap) hrank.symm).mp hsinj
  -- Apply the section theorem to `s`, at the point `q p`.
  obtain ⟨t, ht0, htdiff, htsec, -⟩ :=
    exists_localSection_of_mfderiv_surjective (q := s) (p := q p) hsdiff hsbij.2
  rw [hs0] at ht0 htdiff htsec
  refine ⟨s, hs0, hsdiff, hssec, ?_⟩
  -- Near `p`: `s (t x) = x`, and `t x = q x` because `q ∘ s = id`.
  have hq_cont : ContinuousAt q p := hq.continuousAt
  have h1 : ∀ᶠ x in 𝓝 p, q (s (t x)) = t x := by
    have : ∀ᶠ x in 𝓝 p, t x ∈ {y | q (s y) = y} := by
      refine (htdiff.continuousAt.eventually ?_)
      rw [ht0]
      exact hssec
    exact this
  filter_upwards [htsec, h1] with x hx hqx
  -- `t x = q (s (t x)) = q x`, so `s (q x) = s (t x) = x`.
  have : t x = q x := by rw [← hqx, hx]
  rw [← this, hx]

end InverseFunctionTheorem

end PetersenLib
