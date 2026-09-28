import DoCarmoLib.Riemannian.Manifold.Extendible

/-!
# do Carmo Ch. 8, §4 — a local isometry is determined by a point datum

do Carmo's Lemma 4.2: two local isometries `f₁, f₂ : M → M'` of a **connected** `M` that agree
at one point `p` together with their differentials there — `f₁ p = f₂ p` and `(df₁)_p = (df₂)_p`
— are equal.

## The argument, and where the work is

do Carmo runs a `sup A` argument along a path. The clean formulation is open/closed: the
**agreement locus**

  `A = {x | f₁ x = f₂ x ∧ (df₁)_x = (df₂)_x}`

is nonempty (it contains `p`), open, and closed; `M` connected forces `A = M`.

* **Closed** is the part that looks hard and is not. The naive set above does typecheck — mathlib
  reducibly identifies `TangentSpace I' (f₁ x)` with `E'`, so the equation lands in `E →L[ℝ] E'`
  — but `x ↦ mfderiv I I' f x` is genuinely **not** continuous into `E →L[ℝ] E'`: the
  identification runs through `chartAt x`, which jumps. The fix is to stop working fibrewise and
  take the equalizer upstairs, in the single non-dependent type `TangentBundle I' M'`, where
  `ContMDiff.continuous_tangentMap` applies. `AgreeLocus` below is the complement of the
  projection of the *dis*agreement set; `FiberBundle.isOpenMap_proj` turns the open disagreement
  set into an open image, so `AgreeLocus` is closed. Since
  `tangentMap I I' f ⟨x, v⟩ = ⟨f x, mfderiv I I' f x v⟩`, the equalizer encodes **both** clauses
  of `A` at once — the base gives `f₁ x = f₂ x`, the fibre the derivative equality.
  (`Exponential/Defs.lean`'s `hTsub_clopen` already dodges dependent types with the same move.)

* **Open** is the geometric content, and it is the whole of do Carmo's proof: it is the statement
  that the point datum propagates to a whole normal neighbourhood. It is isolated here as the
  hypothesis `hprop` — see `eq_of_pointDatum_of_preconnected`.

Splitting at `hprop` is deliberate: the topological skeleton is generic (it needs only
`ContMDiff` of the two maps, not a metric), so it is stated once here and is reusable for any
rigidity argument of this shape, while the Riemannian input enters only through `hprop`.

## Main results

* `AgreeLocus`, `mem_agreeLocus_iff` — the agreement locus and its fibrewise reading.
* `isClosed_agreeLocus` — it is closed.
* `eq_of_pointDatum_of_preconnected` — do Carmo Ch. 8, Lemma 4.2, modulo `hprop`.

Blueprint: `lem:dc-ch8-4-2`.
-/

open Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** The **agreement locus** of two maps `f₁, f₂ : M → M'`: the set of points at which
`f₁` and `f₂` agree *to first order*, i.e. both the values and the differentials coincide.

It is defined as the complement of the projection of the locus where the tangent maps differ.
That indirection is what makes the set tractable: `tangentMap I I' f` takes values in the single
type `TangentBundle I' M'`, whereas the fibrewise differential `mfderiv I I' f x` lives in a type
depending on `x`. By `mem_agreeLocus_iff` the two descriptions agree. -/
def AgreeLocus (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (f₁ f₂ : M → M') : Set M :=
  (Bundle.TotalSpace.proj ''
    {z : TangentBundle I M | tangentMap I I' f₁ z ≠ tangentMap I I' f₂ z})ᶜ

/-- **Math.** A point lies in the agreement locus exactly when the two maps and their
differentials agree there.

`tangentMap I I' f ⟨x, v⟩ = ⟨f x, mfderiv I I' f x v⟩`, so asking the tangent maps to agree over
`x` for every `v` is asking for `f₁ x = f₂ x` (the base) together with `(df₁)_x = (df₂)_x` (the
fibre). No smoothness is needed. -/
theorem mem_agreeLocus_iff (f₁ f₂ : M → M') (x : M) :
    x ∈ AgreeLocus (M := M) (M' := M') I I' f₁ f₂ ↔
      (f₁ x = f₂ x ∧ mfderiv I I' f₁ x = mfderiv I I' f₂ x) := by
  constructor
  · intro hx
    simp only [AgreeLocus, mem_compl_iff, mem_image, not_exists, not_and] at hx
    have hx' : ∀ v : TangentSpace I x,
        tangentMap I I' f₁ (⟨x, v⟩ : TangentBundle I M)
          = tangentMap I I' f₂ (⟨x, v⟩ : TangentBundle I M) := by
      intro v
      by_contra hne
      exact hx ⟨x, v⟩ hne rfl
    have hbase : f₁ x = f₂ x := congrArg Bundle.TotalSpace.proj (hx' 0)
    refine ⟨hbase, ?_⟩
    ext v
    have hv : (⟨f₁ x, mfderiv I I' f₁ x v⟩ : TangentBundle I' M')
        = ⟨f₂ x, mfderiv I I' f₂ x v⟩ := hx' v
    rw [Bundle.TotalSpace.mk.injEq] at hv
    exact eq_of_heq hv.2
  · rintro ⟨hb, hd⟩
    simp only [AgreeLocus, mem_compl_iff, mem_image, not_exists, not_and]
    rintro ⟨y, v⟩ hne rfl
    have hb' : f₁ y = f₂ y := hb
    have hd' : mfderiv I I' f₁ y = mfderiv I I' f₂ y := hd
    refine hne ?_
    simp only [tangentMap, hd']
    exact congrArg (fun z => (⟨z, (mfderiv I I' f₂ y) v⟩ : TangentBundle I' M')) hb'

/-- **Math.** **The agreement locus is closed.** If `f₁` and `f₂` are `C²`, their tangent maps
are continuous into `TangentBundle I' M'`; if that bundle is Hausdorff, the locus where the
tangent maps *differ* is open, its projection is open (`FiberBundle.isOpenMap_proj`), and the
agreement locus — the complement of that projection — is closed.

Continuity is taken upstairs on purpose: `x ↦ mfderiv I I' f x` is not continuous into
`E →L[ℝ] E'`, because the identification of `TangentSpace I' (f x)` with `E'` jumps with the
chart. -/
theorem isClosed_agreeLocus [T2Space (TangentBundle I' M')] {f₁ f₂ : M → M'}
    (h₁ : ContMDiff I I' 2 f₁) (h₂ : ContMDiff I I' 2 f₂) :
    IsClosed (AgreeLocus (M := M) (M' := M') I I' f₁ f₂) :=
  isClosed_compl_iff.mpr <| FiberBundle.isOpenMap_proj E (TangentSpace I) _
    (isClosed_eq (h₁.continuous_tangentMap (by norm_num))
      (h₂.continuous_tangentMap (by norm_num))).isOpen_compl

/-- **Math.** **do Carmo Ch. 8, Lemma 4.2** (topological skeleton). Let `f₁, f₂ : M → M'` be `C²`
maps of a preconnected `M` agreeing to first order at some `p`. If the point datum **propagates**
— hypothesis `hprop`: wherever `f₁` and `f₂` agree to first order they agree on a whole
neighbourhood — then `f₁ = f₂`.

`hprop` is the geometric content and is exactly what do Carmo supplies for local isometries: on a
normal neighbourhood `V` of `q`, every point is `exp_q v` for a unique `v`, and both maps carry
the geodesic `t ↦ exp_q(tv)` to the geodesic in `M'` with the same initial position and velocity,
so they agree throughout `V`.

Proof: the agreement locus is nonempty (it contains `p`), closed (`isClosed_agreeLocus`) and open
(`hprop`, since agreement on a neighbourhood gives both clauses at every nearby point via
`Filter.EventuallyEq.eq_of_nhds` and `Filter.EventuallyEq.mfderiv_eq`). A nonempty clopen subset
of a preconnected space is everything. This replaces do Carmo's `sup A` argument along a path;
the open/closed form is the same argument without the choice of path.

Blueprint: `lem:dc-ch8-4-2`. -/
theorem eq_of_pointDatum_of_preconnected [PreconnectedSpace M] [T2Space (TangentBundle I' M')]
    {f₁ f₂ : M → M'} (h₁ : ContMDiff I I' 2 f₁) (h₂ : ContMDiff I I' 2 f₂)
    (hprop : ∀ q : M, f₁ q = f₂ q → mfderiv I I' f₁ q = mfderiv I I' f₂ q → f₁ =ᶠ[𝓝 q] f₂)
    (p : M) (hp : f₁ p = f₂ p) (hdp : mfderiv I I' f₁ p = mfderiv I I' f₂ p) :
    f₁ = f₂ := by
  have hclosed : IsClosed (AgreeLocus (M := M) (M' := M') I I' f₁ f₂) :=
    isClosed_agreeLocus h₁ h₂
  have hopen : IsOpen (AgreeLocus (M := M) (M' := M') I I' f₁ f₂) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨hb, hd⟩ := (mem_agreeLocus_iff (I := I) (I' := I') f₁ f₂ x).mp hx
    obtain ⟨U, hU, hUeq⟩ := Filter.eventually_iff_exists_mem.mp (hprop x hb hd)
    obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
    refine Filter.mem_of_superset (hVo.mem_nhds hxV) (fun y hy => ?_)
    have hy' : f₁ =ᶠ[𝓝 y] f₂ :=
      Filter.eventually_iff_exists_mem.mpr ⟨V, hVo.mem_nhds hy, fun z hz => hUeq z (hVU hz)⟩
    exact (mem_agreeLocus_iff (I := I) (I' := I') f₁ f₂ y).mpr ⟨hy'.eq_of_nhds, hy'.mfderiv_eq⟩
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩
    ⟨p, (mem_agreeLocus_iff (I := I) (I' := I') f₁ f₂ p).mpr ⟨hp, hdp⟩⟩
  funext x
  exact ((mem_agreeLocus_iff (I := I) (I' := I') f₁ f₂ x).mp (huniv ▸ Set.mem_univ x)).1

end Riemannian

end
