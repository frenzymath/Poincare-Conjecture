/-
Chapter 2, Proposition 2.37: **the regular part of an arbitrary level set is an
embedded hypersurface, and `grad f` is normal to it.**

`LevelSetChartedSpace.lean` proves this for a *regular value* `c` — one at which
`df_x ≠ 0` holds at every point of `f ⁻¹' {c}`.  Lee's Proposition 2.37 asks for
no such hypothesis: `c` is arbitrary, `f ⁻¹' {c}` may contain critical points, and
only the regular part

  `M_c = f ⁻¹' {c} ∩ ℛ`,   `ℛ = {x : df_x ≠ 0}`

is retained.  This file carries out the reduction of the second statement to the
first, which is the "outstanding work" the closing note of `RegularLevelSet.lean`
identified.

## The reduction

It is Lee's own: `ℛ` is open (`isOpen_regularSet`), hence an open submanifold of
`M` of the same dimension; `M_c` is then the level set of the *restriction*
`f|_ℛ` at `c`; and `c` is a regular value of `f|_ℛ` **by construction**, since
every point of `ℛ` is regular for `f` and restricting to an open set does not
change the differential (`mfderiv_opens_restrict`).  The regular-value machinery
then applies to `f|_ℛ` on `ℛ` verbatim, and the conclusions are transported back
to `M` by composing with the open inclusion `ℛ ↪ M`.

That last step is what needed `mfderiv_opens_restrict` and
`mfderiv_opens_subtypeVal` (`OpenSubmanifold.lean`), which until now existed only
for an open subset of a *normed space* — the flat case `W : Opens F` used by
`PolarCoordinates.lean`.  Here `ℛ` is an open subset of an arbitrary manifold, so
the general form was required; the note previously left in `RegularLevelSet.lean`
cited `OpenSubmanifold.lean` for it prematurely.

## How `M_c` is presented

`M_c` appears here as `regularLevelSet hf c`, the subtype
`{y : ℛ // f ↑y = c}` — that is, as a level set *of `f|_ℛ`, inside `ℛ`*, which is
exactly how Lee's proof presents it ("Regard `ℛ` as an open submanifold of `M`.
Then `M_c = (f|_ℛ)⁻¹(c)").  The identification with Lee's subset of `M` is not
left implicit: `range_regularLevelSetIncl` proves that the image of `M_c` in `M`
under the inclusion is literally `f ⁻¹' {c} ∩ regularSet I f`.

Presenting it this way rather than on the literal subtype `↥(f ⁻¹' {c} ∩ ℛ)` of
`M` avoids transporting a `ChartedSpace` along a homeomorphism, which mathlib has
no combinator for (verified: nothing transfers `ChartedSpace`/`IsManifold` along a
`Homeomorph` in the pin).  Nothing is lost: "embedded smooth hypersurface in `M`"
*means* that the set carries a smooth `n`-manifold structure whose inclusion into
`M` is a smooth immersion and a topological embedding, and that is proved below
for this presentation, with the image identified.
-/
import LeeLib.Ch02.LevelSetChartedSpace
import LeeLib.Ch02.OpenSubmanifold
import LeeLib.Ch02.RegularLevelSet

open Set Function TopologicalSpace
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace LeeLib.Ch02

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

section RegularSetHypersurface

variable {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (c : ℝ)

/-! ### The regular set as an open submanifold -/

/-- **Lee's `ℛ`, as an open submanifold of `M`** — the regular set of `f` bundled
with its openness (`isOpen_regularSet`), so that mathlib's charted-space and
manifold instances for an open subset apply to it. -/
def regularOpens : Opens M := ⟨regularSet I f, isOpen_regularSet hf⟩

@[simp] theorem mem_regularOpens (x : M) : x ∈ regularOpens hf ↔ mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 :=
  Iff.rfl

@[simp] theorem coe_regularOpens : (regularOpens hf : Set M) = regularSet I f := rfl

/-- **`f` restricted to its regular set.** -/
def regularRestrict (y : regularOpens hf) : ℝ := f ↑y

theorem contMDiff_regularRestrict : ContMDiff I 𝓘(ℝ, ℝ) ∞ (regularRestrict hf) :=
  hf.comp contMDiff_subtype_val

/-- **The differential of `f|_ℛ` is the differential of `f`** — restricting to an
open set changes nothing, because `d(ℛ ↪ M) = id`. -/
theorem mfderiv_regularRestrict (y : regularOpens hf) :
    mfderiv I 𝓘(ℝ, ℝ) (regularRestrict hf) y = mfderiv I 𝓘(ℝ, ℝ) f ↑y :=
  mfderiv_opens_restrict _ f ((hf ↑y).mdifferentiableAt (by simp))

/-- **Every value is a regular value of `f|_ℛ`** — this is the point of passing to
`ℛ`.  There is no hypothesis on `c`: the regularity that Lee's Proposition 2.37
must *assume* about `f ⁻¹' {c}` holds on `ℛ` by construction. -/
theorem regularRestrict_regular (y : regularOpens hf) :
    mfderiv I 𝓘(ℝ, ℝ) (regularRestrict hf) y ≠ 0 := by
  rw [mfderiv_regularRestrict]
  exact y.2

/-- The regular-value hypothesis of the codimension-one machinery, discharged for
`f|_ℛ` at the value `c`. -/
theorem regularRestrict_hreg :
    ∀ y : regularOpens hf, regularRestrict hf y = c → mfderiv I 𝓘(ℝ, ℝ) (regularRestrict hf) y ≠ 0 :=
  fun y _ => regularRestrict_regular hf y

/-! ### `M_c` and its smooth structure -/

/-- **Lee's `M_c = f⁻¹(c) ∩ ℛ`**, presented as the level set of `f|_ℛ` inside the
open submanifold `ℛ` — which is how Lee's proof presents it.  Its image in `M` is
identified with `f ⁻¹' {c} ∩ regularSet I f` by `range_regularLevelSetIncl`. -/
abbrev regularLevelSet : Set (regularOpens hf) := regularRestrict hf ⁻¹' {c}

variable (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]

/-- The slice-chart atlas on `M_c`, obtained from the regular-value construction
applied to `f|_ℛ` on the open submanifold `ℛ`. -/
@[reducible] def regularLevelSetChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) (regularLevelSet hf c) :=
  levelSetChartedSpace (contMDiff_regularRestrict hf) n c (regularRestrict_hreg hf c)

/-- **Proposition 2.37, first half — `M_c` is a smooth `n`-manifold.**

No regularity hypothesis on `c` appears: the reduction to the regular-value case
of `isManifold_levelSet` is exactly the passage to `ℛ`. -/
theorem isManifold_regularLevelSet :
    letI := regularLevelSetChartedSpace hf c n
    IsManifold (𝓡 n) ∞ (regularLevelSet hf c) :=
  isManifold_levelSet (contMDiff_regularRestrict hf) n c (regularRestrict_hreg hf c)

/-! ### The inclusion into `M` -/

/-- **The inclusion `M_c ↪ M`**, the composite `M_c ↪ ℛ ↪ M`. -/
def regularLevelSetIncl (z : regularLevelSet hf c) : M := ((z : regularOpens hf) : M)

/-- **The image of `M_c` in `M` is Lee's set `f⁻¹(c) ∩ ℛ`** — the identification
that makes the presentation above a faithful rendering of the statement. -/
theorem range_regularLevelSetIncl :
    range (regularLevelSetIncl hf c) = f ⁻¹' {c} ∩ regularSet I f := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.2, (z : regularOpens hf).2⟩
  · rintro ⟨hxc, hxr⟩
    exact ⟨⟨⟨x, hxr⟩, hxc⟩, rfl⟩

/-- The inclusion `M_c ↪ M` is injective. -/
theorem injective_regularLevelSetIncl : Injective (regularLevelSetIncl hf c) := by
  rintro ⟨⟨x, hx⟩, hxc⟩ ⟨⟨y, hy⟩, hyc⟩ h
  simpa [regularLevelSetIncl, Subtype.ext_iff] using h

/-- **`M_c` is topologically embedded in `M`** — the composite of two subtype
inclusions, each an embedding. -/
theorem isEmbedding_regularLevelSetIncl :
    letI := regularLevelSetChartedSpace hf c n
    Topology.IsEmbedding (regularLevelSetIncl hf c) :=
  Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal

/-- **Proposition 2.37, second half — the inclusion `M_c ↪ M` is smooth.** -/
theorem contMDiff_regularLevelSetIncl :
    letI := regularLevelSetChartedSpace hf c n
    ContMDiff (𝓡 n) I ∞ (regularLevelSetIncl hf c) := by
  letI := regularLevelSetChartedSpace hf c n
  exact contMDiff_subtype_val.comp
    (contMDiff_levelSet_val (contMDiff_regularRestrict hf) n c (regularRestrict_hreg hf c))

/-- **The differential of the inclusion `M_c ↪ M`** is the differential of
`M_c ↪ ℛ`, since `d(ℛ ↪ M) = id`. -/
theorem mfderiv_regularLevelSetIncl (z : regularLevelSet hf c) :
    letI := regularLevelSetChartedSpace hf c n
    mfderiv (𝓡 n) I (regularLevelSetIncl hf c) z
      = mfderiv (𝓡 n) I ((↑) : regularLevelSet hf c → regularOpens hf) z := by
  letI := regularLevelSetChartedSpace hf c n
  have hval : MDifferentiableAt (𝓡 n) I
      ((↑) : regularLevelSet hf c → regularOpens hf) z :=
    (contMDiff_levelSet_val (contMDiff_regularRestrict hf) n c
      (regularRestrict_hreg hf c) z).mdifferentiableAt (by simp)
  have hcomp : mfderiv (𝓡 n) I
      ((fun y : regularOpens hf => (y : M)) ∘ ((↑) : regularLevelSet hf c → regularOpens hf)) z
      = (mfderiv I I (fun y : regularOpens hf => (y : M)) ↑z).comp
          (mfderiv (𝓡 n) I ((↑) : regularLevelSet hf c → regularOpens hf) z) :=
    mfderiv_comp z
      (hasMFDerivAt_opens_subtypeVal (regularOpens hf) (↑z : regularOpens hf)).mdifferentiableAt
      hval
  rw [Function.comp_def] at hcomp
  rw [show regularLevelSetIncl hf c = fun z : regularLevelSet hf c => ((z : regularOpens hf) : M)
    from rfl, hcomp, mfderiv_opens_subtypeVal]
  ext v
  rfl

/-- **`M_c` is an immersed — hence, with `isEmbedding_regularLevelSetIncl`, an
embedded — hypersurface**: the differential of the inclusion is injective. -/
theorem injective_mfderiv_regularLevelSetIncl (z : regularLevelSet hf c) :
    letI := regularLevelSetChartedSpace hf c n
    Injective (mfderiv (𝓡 n) I (regularLevelSetIncl hf c) z) := by
  letI := regularLevelSetChartedSpace hf c n
  rw [mfderiv_regularLevelSetIncl hf c n z]
  exact mfderiv_levelSet_val_injective (contMDiff_regularRestrict hf) n c
    (regularRestrict_hreg hf c) z

/-- **`df` annihilates every vector tangent to `M_c`**: `f` is constant on `M_c`,
so `df_x ∘ d(incl)_z = 0`. -/
theorem mfderivReal_mfderiv_regularLevelSetIncl (z : regularLevelSet hf c)
    (w : EuclideanSpace ℝ (Fin n)) :
    letI := regularLevelSetChartedSpace hf c n
    mfderivReal (I := I) f (regularLevelSetIncl hf c z)
      (mfderiv (𝓡 n) I (regularLevelSetIncl hf c) z w) = 0 := by
  letI := regularLevelSetChartedSpace hf c n
  have h := mfderivReal_mfderiv_levelSet_val (contMDiff_regularRestrict hf) n c
    (regularRestrict_hreg hf c) z w
  rw [mfderivReal, mfderiv_regularRestrict] at h
  rw [mfderiv_regularLevelSetIncl hf c n z, mfderivReal]
  exact h

/-- **`T_z M_c = ker df_x`** — the tangent space of `M_c` is the kernel of the
differential, exactly as for a regular level set (`range_mfderiv_levelSet_val`),
since `d(ℛ ↪ M) = id` identifies the two differentials. -/
theorem range_mfderiv_regularLevelSetIncl (z : regularLevelSet hf c) :
    letI := regularLevelSetChartedSpace hf c n
    (mfderiv (𝓡 n) I (regularLevelSetIncl hf c) z :
        EuclideanSpace ℝ (Fin n) →L[ℝ] E).range
      = levelHyperplane (I := I) f (regularLevelSetIncl hf c z) := by
  letI := regularLevelSetChartedSpace hf c n
  have h := range_mfderiv_levelSet_val (contMDiff_regularRestrict hf) n c
    (regularRestrict_hreg hf c) z
  have hhyp : levelHyperplane (I := I) (regularRestrict hf) ↑z
      = levelHyperplane (I := I) f (regularLevelSetIncl hf c z) := by
    show LinearMap.ker (levelDifferential (I := I) (regularRestrict hf) ↑z : E →ₗ[ℝ] ℝ)
      = LinearMap.ker (levelDifferential (I := I) f (regularLevelSetIncl hf c z) : E →ₗ[ℝ] ℝ)
    rw [levelDifferential, levelDifferential, mfderiv_regularRestrict]
    rfl
  rw [mfderiv_regularLevelSetIncl hf c n z, ← hhyp]
  exact h

/-- **Proposition 2.37, final clause — `grad f` is everywhere normal to `M_c`.**

For every tangent vector `w` of `M_c` at `z`, the gradient of `f` at the
corresponding point of `M` is `g`-orthogonal to `dι(w)`.  This is
`innerAt_grad_eq_zero_of_mem_ker` fed by
`mfderivReal_mfderiv_regularLevelSetIncl`; no restriction of `g` to `ℛ` is
needed, because the statement is about `M`'s own metric and gradient at a point
of `M`. -/
theorem innerAt_grad_mfderiv_regularLevelSetIncl_eq_zero (g : RiemannianMetric I M)
    (z : regularLevelSet hf c) (w : EuclideanSpace ℝ (Fin n)) :
    letI := regularLevelSetChartedSpace hf c n
    g.innerAt (regularLevelSetIncl hf c z) (grad g f (regularLevelSetIncl hf c z))
        (mfderiv (𝓡 n) I (regularLevelSetIncl hf c) z w) = 0 := by
  letI := regularLevelSetChartedSpace hf c n
  exact innerAt_grad_eq_zero_of_mem_ker g f _ _
    (mfderivReal_mfderiv_regularLevelSetIncl hf c n z w)

/-- **`grad f` does not vanish anywhere on `M_c`** — every point of `M_c` lies in
the regular set, so this is `mem_regularSet_iff_grad_ne_zero`.  Together with
`innerAt_grad_mfderiv_regularLevelSetIncl_eq_zero` and
`range_mfderiv_regularLevelSetIncl` this says `grad f` spans the normal line of
the hypersurface `M_c`. -/
theorem grad_ne_zero_regularLevelSet (g : RiemannianMetric I M) (z : regularLevelSet hf c) :
    grad g f (regularLevelSetIncl hf c z) ≠ 0 :=
  (mem_regularSet_iff_grad_ne_zero g f _).1 (z : regularOpens hf).2

end RegularSetHypersurface

end LeeLib.Ch02

end
