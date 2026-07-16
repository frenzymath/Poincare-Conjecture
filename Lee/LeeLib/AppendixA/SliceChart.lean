/-
Appendix A: **slice charts for a map with surjective differential** — the chart in
which a regular level set becomes a linear slice.

This is the geometric half of the package whose analytic half is
`LocalSection.lean`.  Both rest on the same observation, which is Lee's proof of
the rank theorem specialised to a submersion: if `f : E → E'` has `df a`
surjective and `P` projects onto `ker (df a)`, then

  `G x = (f x, P x)`

has `dG a = (df a, P)` an *isomorphism*, so `G` is a diffeomorphism near `a`.
`LocalSection.lean` uses that to invert `G` and freeze the second slot, producing
a section of `f`.  Here the same `G` is packaged as a **chart**, and the point is
what it does to level sets: since the first component of `G` is literally `f`,

  `f x = c  ↔  (G x).1 = c`      (`sliceChart_fst`)

so `G` carries `f ⁻¹' {c}` onto the slice `{c} × ker (df a)` — which is exactly
Lee's slice condition for an embedded submanifold, and hence the local model for
the regular level set theorem (Lee, Corollary A.26).

Mathlib has no submersion, no rank theorem, and no submanifolds: the file
`Mathlib/Geometry/Manifold/SmoothEmbedding.lean` says of its `IsSmoothEmbedding`
that it "will be useful to define embedded submanifolds", and its
`IsSmoothEmbedding.contMDiff` is still a `proof_wanted`.  So the chart is built
here.

## What mathlib does supply

`HasStrictFDerivAt.toOpenPartialHomeomorph` (the inverse function theorem in
bundled form) turns a map with invertible strict derivative into an
`OpenPartialHomeomorph` whose `toFun` is *definitionally* the map itself and
whose source is an open neighbourhood of the point.  That is precisely the chart
wanted, so the content of this file is the identification of `dG a` with the
isomorphism `prodKerProjEquiv` — the one computation — plus the level-set
statements that make the chart a *slice* chart.

## Scope

Everything here is Euclidean.  Transporting it to manifolds costs only the
`extChartAt` bookkeeping already carried out in `LocalSection.lean`
(`exists_localSection`), where the point is that `mfderiv` *is* the `fderivWithin`
of the chart representation.  The remaining step to Lee's A.26 — assembling these
charts into a `ChartedSpace` on the subtype `f ⁻¹' {c}` and checking smooth
compatibility of overlaps — is not attempted here.
-/
import LeeLib.AppendixA.LocalSection

namespace LeeLib.AppendixA

open Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']

/-- The **slice map** of `f` at `a`: `f` paired with a projection onto
`ker (df a)`.

Its first component is `f` on the nose, which is the whole point — it is what
makes `sliceChart` carry level sets of `f` to slices (`sliceChart_fst`). -/
def sliceMap (f : E → E') (a : E) : E → E' × (LinearMap.ker (fderiv ℝ f a : E →ₗ[ℝ] E')) :=
  fun x => (f x, kerProj (fderiv ℝ f a) x)

omit [FiniteDimensional ℝ E'] in
@[simp] theorem sliceMap_apply (f : E → E') (a x : E) :
    sliceMap f a x = (f x, kerProj (fderiv ℝ f a) x) := rfl

omit [FiniteDimensional ℝ E'] in
@[simp] theorem sliceMap_fst (f : E → E') (a x : E) : (sliceMap f a x).1 = f x := rfl

variable {f : E → E'} {a : E}

/-- **The differential of the slice map at `a` is the isomorphism
`prodKerProjEquiv`.**  This is the only computation in the file: `d(f, P) = (df, P)`,
and `(df a, P)` is invertible exactly because `df a` is surjective and `P` projects
onto its kernel. -/
theorem hasFDerivAt_sliceMap (hf : ContDiffAt ℝ ∞ f a)
    (hsurj : Function.Surjective (fderiv ℝ f a)) :
    HasFDerivAt (sliceMap f a)
      ((prodKerProjEquiv (fderiv ℝ f a) hsurj :
        E →L[ℝ] E' × (LinearMap.ker (fderiv ℝ f a : E →ₗ[ℝ] E')))) a := by
  rw [prodKerProjEquiv_coe]
  exact ((hf.differentiableAt (by simp)).hasFDerivAt).prodMk
    (kerProj (fderiv ℝ f a)).hasFDerivAt

omit [FiniteDimensional ℝ E'] in
theorem contDiffAt_sliceMap (hf : ContDiffAt ℝ ∞ f a) : ContDiffAt ℝ ∞ (sliceMap f a) a :=
  hf.prodMk (kerProj (fderiv ℝ f a)).contDiff.contDiffAt

theorem hasStrictFDerivAt_sliceMap (hf : ContDiffAt ℝ ∞ f a)
    (hsurj : Function.Surjective (fderiv ℝ f a)) :
    HasStrictFDerivAt (sliceMap f a)
      ((prodKerProjEquiv (fderiv ℝ f a) hsurj :
        E →L[ℝ] E' × (LinearMap.ker (fderiv ℝ f a : E →ₗ[ℝ] E')))) a :=
  (contDiffAt_sliceMap hf).hasStrictFDerivAt' (hasFDerivAt_sliceMap hf hsurj) (by decide)

/-- **The slice chart of `f` at `a`**: a diffeomorphism of an open neighbourhood of
`a` onto an open subset of `E' × ker (df a)`, whose first component is `f`.

This is Lee's local normal form for a submersion, obtained from the inverse
function theorem rather than from the rank theorem (which mathlib does not have).
Its defining property is `sliceChart_fst`: the level set `f ⁻¹' {c}` is the
preimage of the slice `{c} × ker (df a)`. -/
def sliceChart (hf : ContDiffAt ℝ ∞ f a) (hsurj : Function.Surjective (fderiv ℝ f a)) :
    OpenPartialHomeomorph E (E' × (LinearMap.ker (fderiv ℝ f a : E →ₗ[ℝ] E'))) :=
  (hasStrictFDerivAt_sliceMap hf hsurj).toOpenPartialHomeomorph _

@[simp] theorem sliceChart_coe (hf : ContDiffAt ℝ ∞ f a)
    (hsurj : Function.Surjective (fderiv ℝ f a)) :
    (sliceChart hf hsurj : E → E' × (LinearMap.ker (fderiv ℝ f a : E →ₗ[ℝ] E')))
      = sliceMap f a := rfl

theorem mem_sliceChart_source (hf : ContDiffAt ℝ ∞ f a)
    (hsurj : Function.Surjective (fderiv ℝ f a)) : a ∈ (sliceChart hf hsurj).source :=
  (hasStrictFDerivAt_sliceMap hf hsurj).mem_toOpenPartialHomeomorph_source

/-- **The chart's first component is `f`.**  Everything the slice chart is for
follows from this one equation. -/
@[simp] theorem sliceChart_fst (hf : ContDiffAt ℝ ∞ f a)
    (hsurj : Function.Surjective (fderiv ℝ f a)) (x : E) :
    ((sliceChart hf hsurj) x).1 = f x := rfl

/-- **The slice chart straightens the level sets of `f`**: on the chart's domain,
lying in the level set `f ⁻¹' {c}` is exactly having first coordinate `c`.

This is the slice condition of Lee's Theorem A.24, and the local model for the
regular level set theorem A.26: in these coordinates `f ⁻¹' {c}` is the affine
slice `{c} × ker (df a)`. -/
theorem sliceChart_mem_levelSet_iff (hf : ContDiffAt ℝ ∞ f a)
    (hsurj : Function.Surjective (fderiv ℝ f a)) (c : E') (x : E) :
    x ∈ f ⁻¹' {c} ↔ ((sliceChart hf hsurj) x).1 = c := Iff.rfl

/-- The slice `{c} × ker (df a)` **is the image of the level set** under the slice
chart, in mathlib's `IsImage` sense. -/
theorem sliceChart_isImage (hf : ContDiffAt ℝ ∞ f a)
    (hsurj : Function.Surjective (fderiv ℝ f a)) (c : E') :
    (sliceChart hf hsurj).IsImage (f ⁻¹' {c}) ({c} ×ˢ (univ : Set _)) :=
  fun _ _ => ⟨fun h => h.1, fun h => ⟨h, mem_univ _⟩⟩

/-- **The slice chart carries the level set onto the slice**, as a genuine equality
of sets:

  `G '' (source ∩ f ⁻¹' {c}) = target ∩ ({c} × ker (df a))`.

This is the usable form of the slice condition — the statement a `ChartedSpace` on
`f ⁻¹' {c}` consumes — and it is the reason the level set is an embedded
submanifold of dimension `dim (ker (df a))` near `a`. -/
theorem sliceChart_image_levelSet (hf : ContDiffAt ℝ ∞ f a)
    (hsurj : Function.Surjective (fderiv ℝ f a)) (c : E') :
    (sliceChart hf hsurj) '' ((sliceChart hf hsurj).source ∩ f ⁻¹' {c})
      = (sliceChart hf hsurj).target ∩ ({c} ×ˢ (univ : Set _)) :=
  (sliceChart_isImage hf hsurj c).image_eq

/-- The chart is `C^∞` at `a` — it *is* `sliceMap f a`. -/
theorem contDiffAt_sliceChart (hf : ContDiffAt ℝ ∞ f a)
    (hsurj : Function.Surjective (fderiv ℝ f a)) :
    ContDiffAt ℝ ∞ (sliceChart hf hsurj) a := contDiffAt_sliceMap hf

/-- **The chart's inverse is `C^∞`** at the image of `a`.  With
`contDiffAt_sliceChart` this is the statement that `sliceChart` is a
diffeomorphism near `a`, which is what makes the slice coordinates *smooth*
coordinates. -/
theorem contDiffAt_sliceChart_symm (hf : ContDiffAt ℝ ∞ f a)
    (hsurj : Function.Surjective (fderiv ℝ f a)) :
    ContDiffAt ℝ ∞ (sliceChart hf hsurj).symm (sliceMap f a a) :=
  (contDiffAt_sliceMap hf).to_localInverse (hasFDerivAt_sliceMap hf hsurj) (by decide)

end Euclidean

end

end LeeLib.AppendixA
