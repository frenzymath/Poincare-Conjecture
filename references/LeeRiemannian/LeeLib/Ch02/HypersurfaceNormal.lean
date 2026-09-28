/-
Chapter 2, "Riemannian Metrics", §5 "The Volume Form": the *converse* half of Lee's
Proposition 2.43 — an orientation of a hypersurface selects a smooth global unit
normal — and the umbrella statement that closes the proposition.

`HypersurfaceVolumeForm.lean` builds the pointwise theory (the orientation
`inducedOrientation` a unit normal puts on each `T_x M`, and equation (2.17) for it)
and `HypersurfaceOrientation.lean` the "if" half: a hypersurface carrying a smooth
global unit normal is orientable.  What is missing for Lee's "if and only if" is the
opposite direction:

  `M` orientable  ⇒  a smooth global unit normal exists,

together with (2.17) for the *given* orientation.  That is this file.

## The argument

At each `x` the normal space `N_x M` is a **line**: `exists_orthonormalFrame_normalSpace`
supplies `finrank E' - finrank E` orthonormal sections spanning it, and codimension one
makes that index type `Fin 1`.  So `N_x M` contains exactly two unit vectors, `±w₀`
(`eq_or_eq_neg_of_isUnitNormalVecAt`).

Negating the normal negates the top form `(N ⌟ dV_g̃)|_M` (`normalRestrictVec_neg`, plain
multilinearity in slot `0`), hence flips its ray.  Since that ray *is*
`inducedOrientation`, exactly one of `±w₀` induces the given orientation `o x`
(`existsUnique_isOrientedUnitNormalVecAt`).  This determines `N` pointwise, with
no reference to any neighbourhood, so `N := unitNormalOfOrientation` is a global field by
`Classical.choose` — the choice is canonical, not arbitrary.

Smoothness is then local and is where the work of the "if" half is reused.  Near `p`:

* `IsSmoothOrientation o` gives a smooth local frame `Y` realizing `o` on `u`;
* `exists_orthonormalFrame_normalSpace` gives a smooth local unit normal `W` on `v`;
* `s(x) = (W ⌟ dV_g̃)|_M|_x (Y_· x)` is smooth on `u ∩ v` by
  `contMDiffAt_normalRestrict_frame` — the analytic theorem the "if" half was built around —
  and never zero, so its sign is locally constant;
* by the uniqueness above, `N = W` on the piece where `s > 0` and `N = -W` where `s < 0`.
  Both are smooth sections, so `N` is smooth at `p`.

This is exactly why `IsSmoothNormalAt` was localized to a point when the "if" half was
built: `W` is smooth only on `v`, so a global smoothness hypothesis would have been
undischargeable here.

## Why `0 < finrank ℝ E`

The same reason as in `HypersurfaceOrientation.lean`, and it enters through
`Basis.adjustToOrientation`: the sign of the normal is pinned by comparing an *adapted
basis* against `o x`, and on a `0`-manifold the only basis is the empty one, whose
orientation is always the ray of the constant `1`.  `Orientation ℝ V (Fin 0)` nevertheless
has two elements, so no basis expresses the other one and the selection cannot be made.
Lee's hypersurfaces have `n ≥ 1`.

## Pointwise API

`IsUnitNormalAt`, `consNormal` and `normalRestrict` all take a *field* `N` but use only its
value `N x`.  Stating "exactly two unit normals at `x`" and "exactly one of them induces
`o x`" quantifies over a bare vector, so this file adds the pointwise primitives
`IsUnitNormalVecAt`, `consNormalVec` and `normalRestrictVec`.  The field versions are left
untouched, and each is bridged to its pointwise counterpart: `consNormal_eq_consNormalVec` and
`normalRestrict_eq_normalRestrictVec` are `rfl`, while `isUnitNormalAt_iff_vec` destructures —
`IsUnitNormalAt` and `IsUnitNormalVecAt` are two distinct structures, so they are equivalent but
not definitionally equal.

To use a *field*-level lemma at a bare vector, feed it
`Function.update (fun y => (0 : TangentSpace I' (F y))) x w`, which is a field with value `w` at
`x`; `Function.update` is dependent, whereas a constant `fun _ => w` does not typecheck, the fibre
varying with `y`.  `normalRestrictVec_toAlternatingMap_ne_zero` is the one place this is needed.
-/
import LeeLib.Ch02.HypersurfaceOrientation

namespace LeeLib.Ch02

open Bundle InnerProductSpace Module Submodule
open scoped Manifold ContDiff RealInnerProductSpace Topology

noncomputable section HyperNormal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

variable {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'} {F : M → M'}
  {o : PointwiseOrientation I M} {o' : PointwiseOrientation I' M'} {x : M}
  {N : (y : M) → TangentSpace I' (F y)}

/-! ## Unit normals as bare vectors -/

variable (I) in
/-- **`w` is a unit normal to the immersed `F : M → M̃` at `x`** — the pointwise form of
`IsUnitNormalAt`, taking the vector rather than a field.

`IsUnitNormalAt` uses only the value `N x`, but its shape prevents quantifying over the vector,
which is what "the normal space contains exactly two unit vectors" and the selection of a normal
by an orientation both need.  The two agree by `isUnitNormalAt_iff_vec` (`Iff.rfl` up to
destructuring).

`I` is explicit for the reason recorded on `IsUnitNormalAt`: `TangentSpace I x` is a reducible
synonym for `E` and retains neither `I` nor `x`. -/
structure IsUnitNormalVecAt (I : ModelWithCorners ℝ E H) (g' : RiemannianMetric I' M')
    (F : M → M') (x : M) (w : TangentSpace I' (F x)) : Prop where
  /-- `w` is orthogonal to every vector tangent to `M`. -/
  normal : ∀ v : TangentSpace I x, g'.inner (F x) w (mfderiv I I' F x v) = 0
  /-- `w` has unit length. -/
  unit : g'.inner (F x) w w = 1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] in
/-- A field is a unit normal at `x` exactly when its value there is. -/
theorem isUnitNormalAt_iff_vec :
    IsUnitNormalAt I g' F N x ↔ IsUnitNormalVecAt I g' F x (N x) :=
  ⟨fun h => ⟨h.normal, h.unit⟩, fun h => ⟨h.normal, h.unit⟩⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] in
/-- **Negating a unit normal leaves a unit normal.**  The two signs are the only choices, so
this is what makes the selection of a normal by an orientation a genuine dichotomy. -/
theorem IsUnitNormalVecAt.neg {w : TangentSpace I' (F x)} (hw : IsUnitNormalVecAt I g' F x w) :
    IsUnitNormalVecAt I g' F x (-w) where
  normal v := by
    have h : g'.inner (F x) (-w) = -(g'.inner (F x) w) := map_neg _ _
    rw [h, ContinuousLinearMap.neg_apply, hw.normal v, neg_zero]
  unit := by
    have h : g'.inner (F x) (-w) = -(g'.inner (F x) w) := map_neg _ _
    rw [h, ContinuousLinearMap.neg_apply, map_neg, neg_neg, hw.unit]

/-! ## The pointwise adapted frame and `(w ⌟ dV_g̃)|_M` -/

variable (I) in
/-- **The adapted frame `(w, dF b_1, …, dF b_n)`**, taking the normal as a bare vector — the
pointwise form of `consNormal`, to which it is `rfl`-equal (`consNormal_eq_consNormalVec`). -/
def consNormalVec (I : ModelWithCorners ℝ E H) (F : M → M')
    (hdim : finrank ℝ E' = finrank ℝ E + 1) (x : M) (w : TangentSpace I' (F x))
    (b : Fin (finrank ℝ E) → TangentSpace I x) :
    Fin (finrank ℝ E') → TangentSpace I' (F x) :=
  fun a => Fin.cons (α := fun _ => TangentSpace I' (F x)) w
    (fun i => mfderiv I I' F x (b i)) (finCongr hdim a)

variable {hdim : finrank ℝ E' = finrank ℝ E + 1}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M]
  [IsManifold I' ∞ M'] in
theorem consNormal_eq_consNormalVec (b : Fin (finrank ℝ E) → TangentSpace I x) :
    consNormal I F hdim N x b = consNormalVec I F hdim x (N x) b := rfl

variable (I) in
/-- **`(w ⌟ dV_g̃)|_M` at `x`**, taking the normal as a bare vector — the pointwise form of
`normalRestrict`, to which it is `rfl`-equal (`normalRestrict_eq_normalRestrictVec`).

Like `normalRestrict` this is defined for *any* vector `w`: no normality, no unit length and no
smoothness are needed to write it down, because `volumeForm` accepts an arbitrary
`PointwiseOrientation` and `mfderiv` is total. -/
def normalRestrictVec (I : ModelWithCorners ℝ E H) (g' : RiemannianMetric I' M')
    (o' : PointwiseOrientation I' M') (F : M → M')
    (hdim : finrank ℝ E' = finrank ℝ E + 1) (x : M) (w : TangentSpace I' (F x)) :
    (TangentSpace I x) [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ :=
  (camContract (camDomDomCongr (finCongr hdim) (g'.volumeForm o' (F x))) w)
    |>.compContinuousLinearMap (mfderiv I I' F x)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] in
theorem normalRestrict_eq_normalRestrictVec :
    normalRestrict I g' o' F hdim N x = normalRestrictVec I g' o' F hdim x (N x) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] in
@[simp]
theorem normalRestrictVec_apply (w : TangentSpace I' (F x))
    (v : Fin (finrank ℝ E) → TangentSpace I x) :
    normalRestrictVec I g' o' F hdim x w v =
      g'.volumeForm o' (F x) (consNormalVec I F hdim x w v) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M]
  [IsManifold I' ∞ M'] in
/-- The normal occupies slot `0` of the adapted frame, before the codimension-one re-indexing. -/
theorem consNormalVec_symm_zero (w : TangentSpace I' (F x))
    (b : Fin (finrank ℝ E) → TangentSpace I x) :
    consNormalVec I F hdim x w b ((finCongr hdim).symm 0) = w := by
  simp [consNormalVec]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M]
  [IsManifold I' ∞ M'] in
/-- **Negating the normal updates slot `0` of the adapted frame and nothing else.** -/
theorem consNormalVec_neg (w : TangentSpace I' (F x))
    (b : Fin (finrank ℝ E) → TangentSpace I x) :
    consNormalVec I F hdim x (-w) b
      = Function.update (consNormalVec I F hdim x w b) ((finCongr hdim).symm 0) (-w) := by
  classical
  funext a
  rcases Fin.eq_zero_or_eq_succ (finCongr hdim a) with h | ⟨i, h⟩
  · have ha : a = (finCongr hdim).symm 0 := by rw [← h]; simp
    subst ha
    rw [Function.update_self]
    simp [consNormalVec]
  · have hne : a ≠ (finCongr hdim).symm 0 := by
      intro hc
      rw [hc] at h
      simp only [Equiv.apply_symm_apply] at h
      exact absurd h.symm (Fin.succ_ne_zero i)
    rw [Function.update_of_ne hne]
    simp [consNormalVec, h]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] in
/-- **Negating the normal negates `(w ⌟ dV_g̃)|_M`** — multilinearity in slot `0`, hence the ray
of the form, hence the induced orientation, flips.  This is what makes the selection of a normal
by an orientation possible at all.

No continuity, metric or orientation is involved; compare `normalRestrict_negMember`, which
negates a member of the *tangent* frame instead. -/
theorem normalRestrictVec_neg (w : TangentSpace I' (F x)) :
    normalRestrictVec I g' o' F hdim x (-w) = - normalRestrictVec I g' o' F hdim x w := by
  classical
  ext b
  rw [normalRestrictVec_apply, consNormalVec_neg]
  rw [show (-w) = -(consNormalVec I F hdim x w b ((finCongr hdim).symm 0)) by
    rw [consNormalVec_symm_zero]]
  show (g'.volumeForm o' (F x)).toAlternatingMap
      (Function.update (consNormalVec I F hdim x w b) ((finCongr hdim).symm 0)
        (-(consNormalVec I F hdim x w b ((finCongr hdim).symm 0)))) = _
  rw [AlternatingMap.map_update_neg, Function.update_eq_self]
  rfl

/-! ## The normal space of a hypersurface is a line -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] in
/-- A unit normal, viewed as a member of the normal space.  This is the equivalence the docstring
of `IsUnitNormalAt` promises (under the name `isUnitNormalAt_iff_mem_normalSpace`, which was never
written); `normalSpace` states orthogonality against `tangentRange f x` while `IsUnitNormalVecAt`
states it against the vectors `dF_x v`, and the two ranges are the same set. -/
theorem IsUnitNormalVecAt.mem_normalSpace {f : C^∞⟮I, M; I', M'⟯} {w : TangentSpace I' (f x)}
    (hw : IsUnitNormalVecAt I g' (f : M → M') x w) : w ∈ normalSpace g' f x := by
  intro z hz
  obtain ⟨v, rfl⟩ := hz
  exact hw.normal v

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] in
/-- **A hypersurface has exactly two unit normals at each point**: if the normal space is the line
spanned by the unit normal `w₀`, every unit normal is `±w₀`.

This is the whole content of codimension one for the converse of Proposition 2.43.  The proof is
that `w = c • w₀` for a scalar `c`, and `1 = ⟨w, w⟩ = c²⟨w₀, w₀⟩ = c²`.

The singleton is ascribed to the *pullback fibre* rather than to `TangentSpace I' (f x)`: the two
are defeq, but `normalSpace` lives over the former and `rw` matches syntactically, so an
unascribed `span ℝ {w₀}` elaborates against the latter and every rewrite against `hspan` fails.
Expanding `⟨c • w₀, c • w₀⟩` needs explicitly type-ascribed `have`s for the same reason — `simp`
and `rw` cannot fire `map_smul` through the fibre instance diamond. -/
theorem eq_or_eq_neg_of_isUnitNormalVecAt {f : C^∞⟮I, M; I', M'⟯}
    {w₀ w : TangentSpace I' (f x)} (hw₀ : IsUnitNormalVecAt I g' (f : M → M') x w₀)
    (hspan : span ℝ ({w₀} : Set (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x))
      = normalSpace g' f x)
    (hw : IsUnitNormalVecAt I g' (f : M → M') x w) : w = w₀ ∨ w = -w₀ := by
  have hmem : w ∈ normalSpace g' f x := hw.mem_normalSpace
  rw [← hspan] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  -- `hc` lives in the pullback fibre; re-ascribing it to `TangentSpace I' (f x)` is `rfl` and is
  -- what lets `subst` see a variable on the right.
  have hc' : (c • w₀ : TangentSpace I' (f x)) = w := hc
  subst hc'
  have hcc : c * c = 1 := by
    have e1 : g'.inner (f x) (c • w₀) = c • (g'.inner (f x) w₀) :=
      (g'.inner (f x)).map_smul c w₀
    have e2 : g'.inner (f x) w₀ (c • w₀) = c • (g'.inner (f x) w₀ w₀) :=
      (g'.inner (f x) w₀).map_smul c w₀
    have h1 : g'.inner (f x) (c • w₀) (c • w₀) = c * (c * g'.inner (f x) w₀ w₀) := by
      rw [e1, ContinuousLinearMap.smul_apply, e2]
      simp [smul_eq_mul]
    rw [hw.unit, hw₀.unit] at h1
    simpa using h1.symm
  rcases mul_self_eq_one_iff.mp hcc with rfl | rfl
  · left; simp
  · right; simp

/-- **Every point of a hypersurface has a unit normal spanning its normal space** — the pointwise
consequence of the local normal frames of Proposition 2.16.

Codimension one turns the frame's index type `Fin (finrank ℝ E' - finrank ℝ E)` into `Fin 1`, so
the frame has a single member; this is where `hdim` is spent, and the arithmetic is `omega`
rather than a `Fin`-cast. -/
theorem exists_isUnitNormalVecAt_span (g' : RiemannianMetric I' M') (f : C^∞⟮I, M; I', M'⟯)
    (himm : ∀ y : M, Function.Injective (mfderiv I I' f y))
    (hdim : finrank ℝ E' = finrank ℝ E + 1) (x : M) :
    ∃ w₀ : TangentSpace I' (f x), IsUnitNormalVecAt I g' (f : M → M') x w₀ ∧
      span ℝ ({w₀} : Set (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x))
        = normalSpace g' f x := by
  obtain ⟨v, hn, Nl, hvopen, hxv, hsmooth, hon, hnormal, hspan⟩ :=
    exists_orthonormalFrame_normalSpace g' f himm x
  have h0 : 0 < finrank ℝ E' - finrank ℝ E := by omega
  refine ⟨Nl ⟨0, h0⟩ x, ⟨?_, ?_⟩, ?_⟩
  · intro z
    exact hnormal x hxv ⟨0, h0⟩ _ ⟨z, rfl⟩
  · simpa using hon x hxv ⟨0, h0⟩ ⟨0, h0⟩
  · rw [← hspan x hxv]
    congr 1
    ext z
    simp only [Set.mem_range]
    constructor
    · rintro rfl
      exact ⟨_, rfl⟩
    · rintro ⟨j, rfl⟩
      have hj := j.isLt
      congr 2
      exact Fin.ext (by omega)

/-! ## An orientation selects a unit normal -/

/-- **`w` is a unit normal at `x` inducing the orientation `o x`.**

The condition is stated against *every* basis realizing `o x` rather than through
`rayOfNeZero`, whose proof argument would itself depend on `w`.  It is equivalent to
`inducedOrientation … x = o x` once a basis realizing `o x` exists, which is what
`0 < finrank ℝ E` buys; that is `inducedOrientation_unitNormalOfOrientation`.

Every binder is written out rather than inherited from the section: `variable (I g o o') in`
silently drops the ones the body does not mention (here `g`), which shifts every later argument
and produces baffling type errors at each use site. -/
structure IsOrientedUnitNormalVecAt (I : ModelWithCorners ℝ E H) (g' : RiemannianMetric I' M')
    (o : PointwiseOrientation I M) (o' : PointwiseOrientation I' M') (F : M → M')
    (hdim : finrank ℝ E' = finrank ℝ E + 1)
    (x : M) (w : TangentSpace I' (F x)) : Prop where
  /-- `w` is a unit normal. -/
  isUnitNormal : IsUnitNormalVecAt I g' F x w
  /-- `(w ⌟ dV_g̃)|_M` is positive on every basis realizing `o x`. -/
  pos : ∀ b : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x), b.orientation = o x →
    0 < normalRestrictVec I g' o' F hdim x w b

omit [FiniteDimensional ℝ E'] [IsManifold I ∞ M] in
/-- **A basis realizing a prescribed orientation exists** when `M` is positive-dimensional.

`Module.finBasis ℝ E` is a basis of `TangentSpace I x` by reducibility, and
`Basis.adjustToOrientation` flips it if needed.  The `[Nonempty ι]` that lemma carries is exactly
`0 < finrank ℝ E`; on a `0`-manifold the conclusion is false, which is the root of the
dimension hypothesis throughout this file. -/
theorem exists_basis_orientation_eq (hpos : 0 < finrank ℝ E) (o : PointwiseOrientation I M)
    (x : M) : ∃ b : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x), b.orientation = o x := by
  classical
  haveI : Nonempty (Fin (finrank ℝ E)) := Fin.pos_iff_nonempty.mp hpos
  exact ⟨(Module.finBasis ℝ E : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x)).adjustToOrientation
      (o x), Module.Basis.orientation_adjustToOrientation _ _⟩

/-- **`(w ⌟ dV_g̃)|_M` is a nonzero top form** when `w` is a unit normal — the pointwise form of
`normalRestrict_toAlternatingMap_ne_zero`.

The field version is reused rather than reproved: `Function.update` is dependent, so
`Function.update (fun y => 0) x w` is a genuine normal *field* whose value at `x` is `w`, and
`normalRestrict` reads only that value.  (A constant `fun _ => w` does not typecheck: the fibre
`TangentSpace I' (F y)` varies with `y`.) -/
theorem normalRestrictVec_toAlternatingMap_ne_zero {w : TangentSpace I' (F x)}
    (h : IsMetricPreserving g g' F) (hw : IsUnitNormalVecAt I g' F x w)
    (hdim : finrank ℝ E' = finrank ℝ E + 1) :
    (normalRestrictVec I g' o' F hdim x w).toAlternatingMap ≠ 0 := by
  classical
  set N₀ : (y : M) → TangentSpace I' (F y) :=
    Function.update (fun y => (0 : TangentSpace I' (F y))) x w with hN₀
  have hval : N₀ x = w := by rw [hN₀, Function.update_self]
  have hN : IsUnitNormalAt I g' F N₀ x := by
    rw [isUnitNormalAt_iff_vec, hval]; exact hw
  have hkey := normalRestrict_toAlternatingMap_ne_zero (g := g) (o' := o') h hN hdim
  rwa [normalRestrict_eq_normalRestrictVec, hval] at hkey

/-- **One basis suffices**: a unit normal induces `o x` exactly when `(w ⌟ dV_g̃)|_M` is positive
on *any single* basis realizing `o x`.

This is what makes the `∀ b` in the `pos` clause of `IsOrientedUnitNormalVecAt` cheap to
discharge — positivity on `b` is equivalent to an equality of *rays*
(`rayOfNeZero_eq_basis_orientation_iff`), and a ray mentions no basis, so it transfers to every
other basis realizing `o x` for free.  Both the selection of the normal and its smoothness read
the sign off whatever frame is at hand, so both go through this lemma. -/
theorem isOrientedUnitNormalVecAt_iff_pos (o : PointwiseOrientation I M) {g : RiemannianMetric I M}
    {f : C^∞⟮I, M; I', M'⟯} (h : IsMetricPreserving g g' (f : M → M')) {x : M}
    {w : TangentSpace I' (f x)} (hw : IsUnitNormalVecAt I g' (f : M → M') x w)
    (hdim : finrank ℝ E' = finrank ℝ E + 1)
    (b : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x)) (hb : b.orientation = o x) :
    IsOrientedUnitNormalVecAt I g' o o' (f : M → M') hdim x w ↔
      0 < normalRestrictVec I g' o' (f : M → M') hdim x w b := by
  have hform : (normalRestrictVec I g' o' (f : M → M') hdim x w).toAlternatingMap ≠ 0 :=
    normalRestrictVec_toAlternatingMap_ne_zero (g := g) h hw hdim
  refine ⟨fun hor => hor.pos b hb, fun hp => ⟨hw, ?_⟩⟩
  intro b' hb'
  have hray : rayOfNeZero ℝ (normalRestrictVec I g' o' (f : M → M') hdim x w).toAlternatingMap
      hform = b.orientation :=
    (rayOfNeZero_eq_basis_orientation_iff b
      (normalRestrictVec I g' o' (f : M → M') hdim x w).toAlternatingMap hform).mpr hp
  rw [hb, ← hb'] at hray
  exact (rayOfNeZero_eq_basis_orientation_iff b'
    (normalRestrictVec I g' o' (f : M → M') hdim x w).toAlternatingMap hform).mp hray

/-- **`(w ⌟ dV_g̃)|_M` never vanishes on a basis** when `w` is a unit normal — the form is a
nonzero top form, and a nonzero top form is nonzero on every basis. -/
theorem normalRestrictVec_apply_basis_ne_zero {g : RiemannianMetric I M} {f : C^∞⟮I, M; I', M'⟯}
    (h : IsMetricPreserving g g' (f : M → M')) {x : M} {w : TangentSpace I' (f x)}
    (hw : IsUnitNormalVecAt I g' (f : M → M') x w) (hdim : finrank ℝ E' = finrank ℝ E + 1)
    (b : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x)) :
    normalRestrictVec I g' o' (f : M → M') hdim x w b ≠ 0 :=
  (AlternatingMap.map_basis_ne_zero_iff b
    (normalRestrictVec I g' o' (f : M → M') hdim x w).toAlternatingMap).mpr
    (normalRestrictVec_toAlternatingMap_ne_zero (g := g) h hw hdim)

/-- **Exactly one of the two unit normals at `x` induces the given orientation** — the pointwise
heart of the converse of Proposition 2.43.

Existence: the two candidates are `±w₀`, and `(w₀ ⌟ dV_g̃)|_M` does not vanish on a basis (a
nonzero top form never does), so its value there is either positive — take `w₀` — or negative,
and then negating the normal negates the value (`normalRestrictVec_neg`).

Uniqueness: a second such normal is `±w₀` too, and the two signs give values of opposite sign,
only one of which is positive. -/
theorem existsUnique_isOrientedUnitNormalVecAt (hpos : 0 < finrank ℝ E)
    {g : RiemannianMetric I M} {f : C^∞⟮I, M; I', M'⟯} (h : IsMetricPreserving g g' (f : M → M'))
    (himm : ∀ y : M, Function.Injective (mfderiv I I' f y))
    (hdim : finrank ℝ E' = finrank ℝ E + 1) (x : M) :
    ∃! w : TangentSpace I' (f x),
      IsOrientedUnitNormalVecAt I g' o o' (f : M → M') hdim x w := by
  classical
  obtain ⟨w₀, hw₀, hspan⟩ := exists_isUnitNormalVecAt_span g' f himm hdim x
  obtain ⟨b, hb⟩ := exists_basis_orientation_eq hpos o x
  have hchar : ∀ w : TangentSpace I' (f x), (hw : IsUnitNormalVecAt I g' (f : M → M') x w) →
      (IsOrientedUnitNormalVecAt I g' o o' (f : M → M') hdim x w ↔
        0 < normalRestrictVec I g' o' (f : M → M') hdim x w b) :=
    fun w hw => isOrientedUnitNormalVecAt_iff_pos (o' := o') o h hw hdim b hb
  -- pick the sign
  rcases lt_or_gt_of_ne (normalRestrictVec_apply_basis_ne_zero (o' := o') h hw₀ hdim b)
    with hlt | hgt
  · refine ⟨-w₀, (hchar _ hw₀.neg).mpr ?_, ?_⟩
    · rw [normalRestrictVec_neg]
      exact neg_pos.mpr hlt
    · intro w hw
      rcases eq_or_eq_neg_of_isUnitNormalVecAt hw₀ hspan hw.isUnitNormal with rfl | rfl
      · exact absurd ((hchar _ hw₀).mp hw) (asymm hlt)
      · rfl
  · refine ⟨w₀, (hchar _ hw₀).mpr hgt, ?_⟩
    intro w hw
    rcases eq_or_eq_neg_of_isUnitNormalVecAt hw₀ hspan hw.isUnitNormal with rfl | rfl
    · rfl
    · have := (hchar _ hw₀.neg).mp hw
      rw [normalRestrictVec_neg] at this
      exact absurd (neg_pos.mp this) (asymm hgt)

variable (I g g' o o') in
/-- **The unit normal an orientation selects.**

Well defined by `existsUnique_isOrientedUnitNormalVecAt`: at each point the normal space is a
line, so there are two unit normals, and exactly one of them induces `o x`.  The choice is
canonical rather than arbitrary, which is why this is a *global* field with no gluing: no
neighbourhood, partition of unity or connectedness enters anywhere.  Smoothness is a separate
matter and is `isSmoothNormalField_unitNormalOfOrientation`.

`o` is an explicit argument because it does not appear in the result type — the selected normal
is a vector, and nothing about a vector records which orientation chose it. -/
def unitNormalOfOrientation
    (hpos : 0 < finrank ℝ E) {f : C^∞⟮I, M; I', M'⟯}
    (h : IsMetricPreserving g g' (f : M → M'))
    (himm : ∀ y : M, Function.Injective (mfderiv I I' f y))
    (hdim : finrank ℝ E' = finrank ℝ E + 1) (y : M) : TangentSpace I' (f y) :=
  (existsUnique_isOrientedUnitNormalVecAt (o := o) (o' := o') hpos h himm hdim y).exists.choose

variable (I g g' o o') in
theorem isOrientedUnitNormalVecAt_unitNormalOfOrientation
    (hpos : 0 < finrank ℝ E) {f : C^∞⟮I, M; I', M'⟯}
    (h : IsMetricPreserving g g' (f : M → M'))
    (himm : ∀ y : M, Function.Injective (mfderiv I I' f y))
    (hdim : finrank ℝ E' = finrank ℝ E + 1) (y : M) :
    IsOrientedUnitNormalVecAt I g' o o' (f : M → M') hdim y
      (unitNormalOfOrientation I g g' o o' hpos h himm hdim y) :=
  (existsUnique_isOrientedUnitNormalVecAt (o := o) (o' := o') hpos h himm hdim y).exists.choose_spec

variable (I g g' o o') in
/-- Uniqueness, in the form the smoothness proof consumes: any unit normal inducing `o` at `y`
*is* the selected one.  This is what turns the local unit normals of Proposition 2.16 into
local *formulas* for the global `unitNormalOfOrientation`. -/
theorem eq_unitNormalOfOrientation
    (hpos : 0 < finrank ℝ E) {f : C^∞⟮I, M; I', M'⟯}
    (h : IsMetricPreserving g g' (f : M → M'))
    (himm : ∀ y : M, Function.Injective (mfderiv I I' f y))
    (hdim : finrank ℝ E' = finrank ℝ E + 1) {y : M} {w : TangentSpace I' (f y)}
    (hw : IsOrientedUnitNormalVecAt I g' o o' (f : M → M') hdim y w) :
    w = unitNormalOfOrientation I g g' o o' hpos h himm hdim y :=
  (existsUnique_isOrientedUnitNormalVecAt (o := o) (o' := o') hpos h himm hdim y).unique hw
    (isOrientedUnitNormalVecAt_unitNormalOfOrientation I g g' o o' hpos h himm hdim y)

/-! ## The selected normal is smooth -/

/-- **The unit normal an orientation selects is smooth** — the analytic half of the converse of
Proposition 2.43.

Near `p`, two local objects are available: a smooth frame `Y` realizing `o` on `u`
(`IsSmoothOrientation o`), and a smooth local unit normal `W` on `v` (Proposition 2.16).  Their
pairing `s(y) = (W ⌟ dV_g̃)|_M|_y (Y_· y)` is smooth on `u ∩ v` by
`contMDiffAt_normalRestrict_frame` — the theorem the "if" half was built around — and never zero,
because a nonzero top form does not vanish on a basis.

So the sign of `s` is locally constant, and by `isOrientedUnitNormalVecAt_iff_pos` it decides
which of `±W` is the selected normal: uniqueness then turns `W` (or `-W`) into a *formula* for
`unitNormalOfOrientation` on a whole neighbourhood of `p`, where it is manifestly smooth.

No gluing, partition of unity or connectedness is involved: the field itself was already global
and canonical: only the local *formula* for it changes from `W` to `-W`. -/
theorem isSmoothNormalField_unitNormalOfOrientation (hpos : 0 < finrank ℝ E)
    {g : RiemannianMetric I M} {f : C^∞⟮I, M; I', M'⟯} (h : IsMetricPreserving g g' (f : M → M'))
    (himm : ∀ y : M, Function.Injective (mfderiv I I' f y))
    (hdim : finrank ℝ E' = finrank ℝ E + 1)
    (ho : IsSmoothOrientation o) (ho' : IsSmoothOrientation o') :
    IsSmoothNormalField I f (unitNormalOfOrientation I g g' o o' hpos h himm hdim) := by
  classical
  intro p
  obtain ⟨u, Y, huopen, hpu, hY, hYo⟩ := ho p
  obtain ⟨v, hn, Nl, hvopen, hpv, hsmooth, hon, hnormal, hspan⟩ :=
    exists_orthonormalFrame_normalSpace g' f himm p
  have h0 : 0 < finrank ℝ E' - finrank ℝ E := by omega
  set W : (y : M) → TangentSpace I' (f y) := Nl ⟨0, h0⟩ with hWdef
  have hWunit : ∀ y ∈ v, IsUnitNormalVecAt I g' (f : M → M') y (W y) := by
    intro y hy
    exact ⟨fun z => hnormal y hy ⟨0, h0⟩ _ ⟨z, rfl⟩, by simpa using hon y hy ⟨0, h0⟩ ⟨0, h0⟩⟩
  have hWsmooth : ∀ y ∈ v, IsSmoothNormalAt I f W y :=
    fun y hy => (hsmooth ⟨0, h0⟩).contMDiffAt (hvopen.mem_nhds hy)
  set c : Set M := u ∩ v with hcdef
  have hcopen : IsOpen c := huopen.inter hvopen
  have hpc : p ∈ c := ⟨hpu, hpv⟩
  set s : M → ℝ := fun y => normalRestrict I g' o' (f : M → M') hdim W y (Y · y) with hsdef
  have hscont : ContinuousOn s c :=
    (contMDiffOn_normalRestrict_frame (hdim := hdim) ho' (hY.mono Set.inter_subset_left) hcopen
      (fun y hy => hWsmooth y hy.2)).continuousOn
  -- the value of the form on the frame `Y` *is* `s`, once the frame is read as a basis
  have hsval : ∀ y, ∀ hy : y ∈ c,
      normalRestrictVec I g' o' (f : M → M') hdim y (W y) ⇑(hY.toBasisAt hy.1) = s y := by
    intro y hy
    have hcoe : ⇑(hY.toBasisAt hy.1) = fun i => Y i y := funext fun i => hY.toBasisAt_coe hy.1 i
    -- `normalRestrict … W y` *is* `normalRestrictVec … y (W y)`, so only beta remains
    rw [hcoe, hsdef]
    rfl
  have hsne : ∀ y, ∀ hy : y ∈ c, s y ≠ 0 := by
    intro y hy
    rw [← hsval y hy]
    exact normalRestrictVec_apply_basis_ne_zero (o' := o') h (hWunit y hy.2) hdim _
  -- the sign of `s` decides which of `±W` is the selected normal
  have hcharW : ∀ y, ∀ hy : y ∈ c,
      (IsOrientedUnitNormalVecAt I g' o o' (f : M → M') hdim y (W y) ↔ 0 < s y) := by
    intro y hy
    rw [← hsval y hy]
    exact isOrientedUnitNormalVecAt_iff_pos (o' := o') o h (hWunit y hy.2) hdim _ (hYo y hy.1)
  have hcharNegW : ∀ y, ∀ hy : y ∈ c,
      (IsOrientedUnitNormalVecAt I g' o o' (f : M → M') hdim y (-(W y)) ↔ s y < 0) := by
    intro y hy
    rw [isOrientedUnitNormalVecAt_iff_pos (o' := o') o h (hWunit y hy.2).neg hdim _ (hYo y hy.1),
      normalRestrictVec_neg]
    show 0 < -(normalRestrictVec I g' o' (f : M → M') hdim y (W y) ⇑(hY.toBasisAt hy.1)) ↔ _
    rw [hsval y hy, neg_pos]
  rcases lt_or_gt_of_ne (hsne p hpc) with hlt | hgt
  · -- near `p` the form is negative on `Y`, so the selected normal is `-W` there
    have hopen : IsOpen (c ∩ s ⁻¹' (Set.Iio 0)) := hscont.isOpen_inter_preimage hcopen isOpen_Iio
    have heq : ∀ y ∈ c ∩ s ⁻¹' (Set.Iio 0),
        unitNormalOfOrientation I g g' o o' hpos h himm hdim y = (-W) y := fun y hy =>
      (eq_unitNormalOfOrientation I g g' o o' hpos h himm hdim
        ((hcharNegW y hy.1).mpr hy.2)).symm
    refine ContMDiffAt.congr_of_eventuallyEq ((hWsmooth p hpv).neg_section) ?_
    filter_upwards [hopen.mem_nhds ⟨hpc, hlt⟩] with y hy
    exact congrArg (TotalSpace.mk' E' y) (heq y hy)
  · -- near `p` the form is positive on `Y`, so the selected normal is `W` itself
    have hopen : IsOpen (c ∩ s ⁻¹' (Set.Ioi 0)) := hscont.isOpen_inter_preimage hcopen isOpen_Ioi
    have heq : ∀ y ∈ c ∩ s ⁻¹' (Set.Ioi 0),
        unitNormalOfOrientation I g g' o o' hpos h himm hdim y = W y := fun y hy =>
      (eq_unitNormalOfOrientation I g g' o o' hpos h himm hdim
        ((hcharW y hy.1).mpr hy.2)).symm
    refine ContMDiffAt.congr_of_eventuallyEq (hWsmooth p hpv) ?_
    filter_upwards [hopen.mem_nhds ⟨hpc, hgt⟩] with y hy
    exact congrArg (TotalSpace.mk' E' y) (heq y hy)

/-! ## Lee's Proposition 2.43 -/

/-- The orientation `unitNormalOfOrientation` was selected against is the one it induces — this
is the `pos` clause of `IsOrientedUnitNormalVecAt` read through
`rayOfNeZero_eq_basis_orientation_iff`, and it is what makes (2.17) hold for the *given* `o`
rather than only for the normal's own induced orientation. -/
theorem inducedOrientation_unitNormalOfOrientation (hpos : 0 < finrank ℝ E)
    {g : RiemannianMetric I M} {f : C^∞⟮I, M; I', M'⟯} (h : IsMetricPreserving g g' (f : M → M'))
    (himm : ∀ y : M, Function.Injective (mfderiv I I' f y))
    (hdim : finrank ℝ E' = finrank ℝ E + 1)
    (hN : ∀ y, IsUnitNormalAt I g' (f : M → M')
      (unitNormalOfOrientation I g g' o o' hpos h himm hdim) y) :
    inducedOrientation g g' o' (f : M → M') hdim
      (unitNormalOfOrientation I g g' o o' hpos h himm hdim) h hN = o := by
  funext x
  obtain ⟨b, hb⟩ := exists_basis_orientation_eq hpos o x
  rw [inducedOrientation, ← hb, rayOfNeZero_eq_basis_orientation_iff]
  exact (isOrientedUnitNormalVecAt_unitNormalOfOrientation I g g' o o' hpos h himm hdim x).pos b hb

/-- **Lee, Proposition 2.43, the "only if" half**: an orientable hypersurface carries a smooth
global unit normal, and equation (2.17) `dV_g = (N ⌟ dV_g̃)|_M` holds for the *given* orientation.

The normal is `unitNormalOfOrientation`, selected pointwise by the orientation with no choices
beyond the two-element sign. -/
theorem exists_isSmoothNormalField_volumeForm_eq_normalRestrict (hpos : 0 < finrank ℝ E)
    {g : RiemannianMetric I M} {f : C^∞⟮I, M; I', M'⟯} (h : IsMetricPreserving g g' (f : M → M'))
    (himm : ∀ y : M, Function.Injective (mfderiv I I' f y))
    (hdim : finrank ℝ E' = finrank ℝ E + 1)
    (ho : IsSmoothOrientation o) (ho' : IsSmoothOrientation o') :
    ∃ N : (y : M) → TangentSpace I' (f y),
      (∀ y, IsUnitNormalAt I g' (f : M → M') N y) ∧ IsSmoothNormalField I f N ∧
        ∀ x, g.volumeForm o x = normalRestrict I g' o' (f : M → M') hdim N x := by
  refine ⟨unitNormalOfOrientation I g g' o o' hpos h himm hdim, ?_, ?_, ?_⟩
  · exact fun y => isUnitNormalAt_iff_vec.mpr
      ((isOrientedUnitNormalVecAt_unitNormalOfOrientation I g g' o o' hpos h himm hdim
        y).isUnitNormal)
  · exact isSmoothNormalField_unitNormalOfOrientation hpos h himm hdim ho ho'
  · intro x
    have hN : ∀ y, IsUnitNormalAt I g' (f : M → M')
        (unitNormalOfOrientation I g g' o o' hpos h himm hdim) y := fun y =>
      isUnitNormalAt_iff_vec.mpr
        ((isOrientedUnitNormalVecAt_unitNormalOfOrientation I g g' o o' hpos h himm hdim
          y).isUnitNormal)
    have hor := inducedOrientation_unitNormalOfOrientation (o' := o') hpos h himm hdim hN
    have hkey := volumeForm_inducedOrientation_eq_normalRestrict g h hN hdim (o' := o') x
    rwa [hor] at hkey

/-- **Lee, Proposition 2.43**: a hypersurface `M` in an oriented Riemannian manifold `(M̃, g̃)` is
orientable *if and only if* it admits a smooth global unit normal vector field.

The "if" half is `isSmoothOrientation_inducedOrientation` (the normal induces a smooth
orientation) and the "only if" half is `isSmoothNormalField_unitNormalOfOrientation` (an
orientation selects a smooth normal).  Equation (2.17) accompanies each direction — see
`exists_smoothOrientation_volumeForm_eq_normalRestrict` and
`exists_isSmoothNormalField_volumeForm_eq_normalRestrict` — and cannot be stated here, since it
mentions the `N` and the `o` that the two sides respectively produce. -/
theorem exists_isSmoothOrientation_iff_exists_isSmoothNormalField (hpos : 0 < finrank ℝ E)
    {g : RiemannianMetric I M} {f : C^∞⟮I, M; I', M'⟯} (h : IsMetricPreserving g g' (f : M → M'))
    (himm : ∀ y : M, Function.Injective (mfderiv I I' f y))
    (hdim : finrank ℝ E' = finrank ℝ E + 1) (ho' : IsSmoothOrientation o') :
    (∃ o : PointwiseOrientation I M, IsSmoothOrientation o) ↔
      ∃ N : (y : M) → TangentSpace I' (f y),
        (∀ y, IsUnitNormalAt I g' (f : M → M') N y) ∧ IsSmoothNormalField I f N := by
  constructor
  · rintro ⟨o, ho⟩
    obtain ⟨N, hN, hNsmooth, -⟩ :=
      exists_isSmoothNormalField_volumeForm_eq_normalRestrict (o := o) (o' := o')
        hpos h himm hdim ho ho'
    exact ⟨N, hN, hNsmooth⟩
  · rintro ⟨N, hN, hNsmooth⟩
    exact ⟨inducedOrientation g g' o' (f : M → M') hdim N h hN,
      isSmoothOrientation_inducedOrientation (hdim := hdim) hpos h hN hNsmooth ho'⟩

end HyperNormal

end LeeLib.Ch02
