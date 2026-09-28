/-
Chapter 2, "Riemannian Metrics", §"Riemannian Submersions": **Proposition 2.25**,
*properties of horizontal vector fields*.

Lee states three assertions about a smooth submersion `π : M → M'` carrying a
Riemannian metric `g` on the total space:

  (a) every smooth vector field `W` on `M` splits uniquely as `W = W^H + W^V`
      with `W^H` horizontal, `W^V` vertical, and **both smooth**;
  (b) every smooth vector field on `M'` has a unique smooth horizontal lift;
  (c) every horizontal vector `v ∈ H_x` is the value at `x` of the horizontal
      lift of some *global* vector field on `M'`.

Part (b) is already `LeeLib.Ch02.exists_unique_horizontalLift`
(`RiemannianSubmersion.lean`).  This file adds (a) and (c) and assembles the
three into `existsUnique_horizontal_add_vertical_field` and
`exists_horizontalLift_eq`.

## How this proof departs from Lee's

Lee proves all three parts from the **rank theorem**: he puts `π` in the normal
form `(x¹,…,xᵐ) ↦ (x¹,…,xⁿ)`, reads off that `V_q` is spanned by the last `m - n`
coordinate vectors, applies Gram–Schmidt to the reordered coordinate frame to get
an adapted orthonormal frame `(E_1,…,E_m)`, and then reads smoothness of `W^H`
and `W^V` off the frame components.

The pinned mathlib has **no constant rank theorem**, so that route is unavailable.
It is also unnecessary.  The replacement, already set up in
`RiemannianSubmersion.lean`, is the *explicit formula* for the horizontal lift,
`L_x = B⁻¹Aᵗ(AB⁻¹Aᵗ)⁻¹` — a rational expression in `g` and `dπ` — whose smooth
dependence on `x` is `contMDiffAt_horizontalLift`.  With it:

* `W^H_x = L_x (dπ_x W_x)` **by definition** (`horizontalProj`), so (a) reduces to
  the smoothness of `x ↦ L_x (dπ_x W_x)`.  This is *not* the lift of a vector
  field on `M'` — the vector `dπ_x W_x` depends on `x`, not merely on `π x`,
  because `W` need not be `π`-related to anything.  It is a section of the
  pullback `π^*TM'`, i.e. a **section along `π`**, which is exactly the generality
  of `contMDiffAt_horizontalLiftAlong`.  Its smoothness is the smoothness of the
  bundled derivative, `ContMDiff.contMDiff_tangentMap`.
* `W^V = W - W^H` is then smooth by `ContMDiff.sub_section`, and no adapted frame
  is ever constructed.

So the frame in Lee's proof is a device for smoothness, and the formula supplies
smoothness directly.  Note the resulting statement is *stronger* than Lee's in one
respect: no orthonormal frame, hence no local trivialization of the fibre, is
needed anywhere.

Part (c) needs one genuinely new ingredient, which is not about submersions at
all: the **extension lemma** `LeeLib.AppendixA.exists_contMDiffVectorField_eq`
(every tangent vector is the value of a global smooth vector field).  Given
`v ∈ H_x`, extend `dπ_x v ∈ T_{π x}M'` to a global field `X` on `M'`; then the
lift of `X` takes the value `L_x (dπ_x v) = v` at `x`, the last equality because
`L_x` inverts `dπ_x` *on horizontal vectors* (`horizontalLiftAt_mfderiv_of_mem`)
— which is precisely where the hypothesis `v ∈ H_x` is used, and without it the
statement is false.
-/
import LeeLib.AppendixA.VectorFieldExtension
import LeeLib.Ch02.RiemannianSubmersion

namespace LeeLib.Ch02

-- `Bundle` is deliberately *not* opened: its scoped `π` notation for the bundle
-- projection would shadow Lee's name for the submersion itself.
open Manifold
open scoped Manifold ContDiff

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

variable (g : RiemannianMetric I M) (π : C^∞⟮I, M; I', M'⟯)

/-! ## The pushforward of a vector field is a smooth section along `π` -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **The pushforward of a smooth vector field along `π` is smooth.**

If `W` is a smooth vector field on `M`, then `x ↦ dπ_x (W_x)` is a smooth section
of `π^*TM'` — a *section along `π`*.  Note this is generally **not** a vector
field on `M'`: `dπ_x (W_x)` need not depend on `x` only through `π x`, since two
points of a fibre can carry unrelated values of `W`.

This is exactly mathlib's `ContMDiff.contMDiff_tangentMap` — smoothness of the
bundled derivative `Tπ : TM → TM'` — composed with `W` viewed as a map `M → TM`,
after observing that `tangentMap I I' π ⟨x, W x⟩ = ⟨π x, dπ_x (W x)⟩` by
definition. -/
theorem contMDiff_mfderivAlong {W : ∀ x : M, TangentSpace I x}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => Bundle.TotalSpace.mk' E x (W x))) :
    ContMDiff I (I'.prod 𝓘(ℝ, E')) ∞
      (fun x => Bundle.TotalSpace.mk' E' (π x) (mfderiv I I' π x (W x))) :=
  (π.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).comp hW

/-! ## Proposition 2.25(a): the smooth horizontal/vertical splitting -/

/-- **Lee, Proposition 2.25(a)**, the horizontal half: *`W^H` is smooth*.

`W^H_x = L_x (dπ_x W_x)` is the horizontal lift of the section `x ↦ dπ_x W_x`
along `π`, so this is `contMDiffAt_horizontalLiftAlong` applied to
`contMDiff_mfderivAlong`. -/
theorem contMDiff_horizontalProjField (hπ : IsSubmersion π)
    {W : ∀ x : M, TangentSpace I x}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => Bundle.TotalSpace.mk' E x (W x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => Bundle.TotalSpace.mk' E x (horizontalProj g π x (W x))) :=
  fun x₀ => contMDiffAt_horizontalLiftAlong g π hπ x₀ (contMDiff_mfderivAlong π hW x₀)

/-- **Lee, Proposition 2.25(a)**, the vertical half: *`W^V` is smooth*.

`W^V = W - W^H`, so this is `ContMDiff.sub_section` applied to `hW` and
`contMDiff_horizontalProjField`. -/
theorem contMDiff_verticalProjField (hπ : IsSubmersion π)
    {W : ∀ x : M, TangentSpace I x}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => Bundle.TotalSpace.mk' E x (W x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => Bundle.TotalSpace.mk' E x (verticalProj g π x (W x))) :=
  hW.sub_section (contMDiff_horizontalProjField g π hπ hW)

/-- **Lee, Proposition 2.25(a)**: *every smooth vector field `W` on `M` can be
expressed uniquely as `W = W^H + W^V` with `W^H` horizontal, `W^V` vertical, and
both smooth.*

Existence is `horizontalProj`/`verticalProj`, smooth by
`contMDiff_horizontalProjField` and `contMDiff_verticalProjField`; uniqueness is
the pointwise statement `existsUnique_horizontal_add_vertical`, which needs no
smoothness at all — a rough splitting into a horizontal and a vertical field is
already unique, and the content of (a) is that the unique one is smooth. -/
theorem existsUnique_horizontal_add_vertical_field (hπ : IsSubmersion π)
    {W : ∀ x : M, TangentSpace I x}
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => Bundle.TotalSpace.mk' E x (W x))) :
    ∃ WH WV : ∀ x : M, TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => Bundle.TotalSpace.mk' E x (WH x)) ∧
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => Bundle.TotalSpace.mk' E x (WV x)) ∧
      (∀ x, WH x ∈ horizontalSpace g π x) ∧
      (∀ x, WV x ∈ verticalSpace π x) ∧
      (∀ x, W x = WH x + WV x) ∧
      (∀ ZH ZV : ∀ x : M, TangentSpace I x,
        (∀ x, ZH x ∈ horizontalSpace g π x) → (∀ x, ZV x ∈ verticalSpace π x) →
        (∀ x, W x = ZH x + ZV x) → (∀ x, ZH x = WH x) ∧ (∀ x, ZV x = WV x)) := by
  refine ⟨fun x => horizontalProj g π x (W x), fun x => verticalProj g π x (W x),
    contMDiff_horizontalProjField g π hπ hW, contMDiff_verticalProjField g π hπ hW,
    fun x => horizontalProj_mem g π x _, fun x => verticalProj_mem g π hπ x _,
    fun x => (horizontalProj_add_verticalProj g π x (W x)).symm, ?_⟩
  intro ZH ZV hZH hZV hZ
  -- At each point, apply the pointwise uniqueness to the vector `W x`.
  have key : ∀ x, ZH x = horizontalProj g π x (W x) ∧ ZV x = verticalProj g π x (W x) := by
    intro x
    obtain ⟨p, -, huniq⟩ := existsUnique_horizontal_add_vertical g π hπ x (W x)
    -- Both pairs satisfy the defining property, so both equal the unique witness `p`.
    have h1 := huniq (ZH x, ZV x) ⟨hZH x, hZV x, hZ x⟩
    have h2 := huniq (horizontalProj g π x (W x), verticalProj g π x (W x))
      ⟨horizontalProj_mem g π x _, verticalProj_mem g π hπ x _,
        (horizontalProj_add_verticalProj g π x (W x)).symm⟩
    have h := h1.trans h2.symm
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  exact ⟨fun x => (key x).1, fun x => (key x).2⟩

/-! ## Proposition 2.25(c): realizing a horizontal vector by a lift -/

/-- **Lee, Proposition 2.25(c)**: *for every `x : M` and every horizontal vector
`v ∈ H_x`, there is a vector field `X` on `M'` whose horizontal lift takes the
value `v` at `x`.*

Push `v` down to `dπ_x v ∈ T_{π x}M'`, extend that vector to a global smooth
vector field `X` on `M'` (`LeeLib.AppendixA.exists_contMDiffVectorField_eq`), and
lift `X` back up.  At `x` the lift is `L_x (dπ_x v)`, which is `v` because `L_x`
inverts `dπ_x` on horizontal vectors.

The hypothesis `v ∈ H_x` is essential and not a convenience: the lift of any
field is horizontal at every point, so a non-horizontal `v` cannot be a value of
any lift.

`SigmaCompactSpace M'` and `T2Space M'` are Lee's standing assumptions on
manifolds; they are what make the extension lemma's partition of unity
available. -/
theorem exists_horizontalLift_eq [SigmaCompactSpace M'] [T2Space M'] (hπ : IsSubmersion π)
    {x : M} {v : TangentSpace I x} (hv : v ∈ horizontalSpace g π x) :
    ∃ X : ∀ y : M', TangentSpace I' y,
      ContMDiff I' (I'.prod 𝓘(ℝ, E')) ∞ (fun y => Bundle.TotalSpace.mk' E' y (X y)) ∧
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun z => Bundle.TotalSpace.mk' E z (horizontalLiftAt g π z (X (π z)))) ∧
      horizontalLiftAt g π x (X (π x)) = v := by
  obtain ⟨X, hX, hXeq⟩ :=
    LeeLib.AppendixA.exists_contMDiffVectorField_eq (I := I') (π x) (mfderiv I I' π x v)
  refine ⟨X, hX, contMDiff_horizontalLiftField g π hπ hX, ?_⟩
  rw [hXeq]
  exact horizontalLiftAt_mfderiv_of_mem g π hπ hv

end

end LeeLib.Ch02
