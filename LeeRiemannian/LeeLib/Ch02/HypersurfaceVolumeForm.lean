/-
Chapter 2, "Riemannian Metrics", §5 "The Volume Form": Lee's Proposition 2.43,
the volume form of a Riemannian hypersurface,

  dV_g = (N ⌟ dV_g̃)|_M.                                                 (2.17)

`M` is presented, as everywhere in this chapter, by a smooth immersion
`F : M → M̃` with `g = F^* g̃` the induced metric (`pullbackMetric`); "hypersurface"
is the codimension-one condition `finrank ℝ E' = finrank ℝ E + 1` on the model
spaces.  A *unit normal* is a family `N` with `N x ⊥ dF_x(T_x M)` and `|N x| = 1`.

Both sides of (2.17) are `n`-forms on `T_x M`.  The right-hand side is the
composite of two operations, neither of which exists in mathlib for these types:

* **interior multiplication** `w ↦ N ⌟ w`, contracting an `(n+1)`-form with a
  vector, and
* **restriction to `M`**, which for an immersed `M` means precomposition of each
  argument with `dF_x` (`ContinuousAlternatingMap.compContinuousLinearMap`).

`camContract` below is the first.  Mathlib's `ContinuousAlternatingMap.curryLeft`
looks like it should serve and does not: it is built by `mkContinuousLinear` from
an operator-norm bound, so it demands `NormedAddCommGroup` on the domain, and
`TangentSpace I x` **carries no norm**.  The *algebraic* `AlternatingMap.curryLeft`
has no such hypothesis (only `Module`), so the fix is to curry on the alternating
layer and re-attach continuity by hand: `v ↦ Fin.cons x v` is continuous, so the
composite is, and the `cont` field is discharged directly.  This is the same
norm-free discipline the wedge product in `VolumeForm.lean` needed, and for the
same reason.

`camDomDomCongr` is the second missing piece: `dV_g̃` has degree `Fin (finrank ℝ E')`
while contraction consumes degree `Fin (n+1)`, and mathlib has `AlternatingMap.domDomCongr`
but **no** `ContinuousAlternatingMap.domDomCongr` (only `ContinuousMultilinearMap.domDomCongr`
— the gap is specific to the bundled alternating type).  Same fix, same reason.

The mathematical content is Lee's hint to Problem 2-13: run an adapted orthonormal
frame.  If `(E_1, …, E_n)` is an oriented orthonormal basis of `T_x M`, then
`(N_x, dF E_1, …, dF E_n)` is an orthonormal basis of `T_{F x} M̃` — orthonormal
because `F` is metric-preserving for the induced metric (`inner_mfderiv`) and `N`
is a unit normal.  Evaluating the right-hand side of (2.17) on `(E_i)` therefore
gives `dV_g̃(N_x, dF E_1, …, dF E_n) = ±1`, and `+1` exactly when that basis is
positively oriented — which is the compatibility hypothesis, and is what the
induced orientation is *defined* to make true.  An `n`-form taking the value `1`
on one oriented orthonormal frame is `dV_g` (`volumeForm_unique`), so (2.17)
follows with no smoothness anywhere: `volumeForm` accepts an arbitrary
`PointwiseOrientation`.
-/
import Mathlib.LinearAlgebra.Alternating.Curry
import LeeLib.Ch02.IsometryVolumeForm
import LeeLib.Ch02.NormalBundle

namespace LeeLib.Ch02

open Bundle InnerProductSpace Module Submodule
open scoped Manifold ContDiff RealInnerProductSpace Topology

/-! ## Norm-free contraction and re-indexing of continuous alternating forms -/

section Cam

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- Re-indexing the arguments of a continuous alternating form along `σ : ι ≃ ι'`.

Mathlib has `AlternatingMap.domDomCongr` and `ContinuousMultilinearMap.domDomCongr`, but no
`ContinuousAlternatingMap.domDomCongr`: the re-indexing gap is specific to the bundled
*alternating* continuous type.  Continuity is free — precomposing with `σ` permutes the
coordinates of `ι' → V`. -/
noncomputable def camDomDomCongr {ι ι' : Type*} (σ : ι ≃ ι') (w : V [⋀^ι]→L[ℝ] ℝ) :
    V [⋀^ι']→L[ℝ] ℝ where
  toAlternatingMap := w.toAlternatingMap.domDomCongr σ
  cont := w.cont.comp (continuous_pi fun i => continuous_apply (σ i))

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
@[simp]
theorem camDomDomCongr_apply {ι ι' : Type*} (σ : ι ≃ ι') (w : V [⋀^ι]→L[ℝ] ℝ)
    (v : ι' → V) : camDomDomCongr σ w v = w fun i => v (σ i) := rfl

/-- **Interior multiplication** `x ⌟ w`: the `n`-form obtained from an `(n+1)`-form `w` by
freezing its first argument to `x` (Lee, p. 401).

Mathlib's `ContinuousAlternatingMap.curryLeft` is *not* usable here: it is built from an
operator-norm bound and so requires `NormedAddCommGroup V`, whereas `TangentSpace I x` has
no norm.  The algebraic `AlternatingMap.curryLeft` needs only `Module`, so we curry there and
re-attach continuity: `v ↦ Fin.cons x v` is continuous coordinatewise (`Fin.cases`), hence
so is `v ↦ w (Fin.cons x v)`. -/
noncomputable def camContract {n : ℕ} (w : V [⋀^Fin (n + 1)]→L[ℝ] ℝ) (x : V) :
    V [⋀^Fin n]→L[ℝ] ℝ where
  toAlternatingMap := AlternatingMap.curryLeft w.toAlternatingMap x
  cont := by
    refine w.cont.comp (continuous_pi fun i => ?_)
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using continuous_const
    · simpa using continuous_apply j

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
@[simp]
theorem camContract_apply {n : ℕ} (w : V [⋀^Fin (n + 1)]→L[ℝ] ℝ) (x : V)
    (v : Fin n → V) : camContract w x v = w (Fin.cons x v) := rfl

end Cam

/-! ## Orientations from a nonvanishing top form -/

section Ray

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-- **A nonvanishing top form orients the space**, and a basis is positively oriented for the
resulting orientation exactly when the form is positive on it.

`Orientation ℝ V (Fin n)` *is* `Module.Ray ℝ (V [⋀^Fin n]→ₗ[ℝ] ℝ)`, so a nonzero `n`-form
determines an orientation with no choices; this lemma is what makes that orientation usable.
It is the un-bundled analogue of `Basis.orientation_eq_iff_det_pos`, and has the same proof:
`ω = ω(b) • b.det`, and scaling a nonzero vector preserves its ray exactly when the scalar is
positive. -/
theorem rayOfNeZero_eq_basis_orientation_iff (b : Basis (Fin n) ℝ V)
    (w : V [⋀^Fin n]→ₗ[ℝ] ℝ) (hw : w ≠ 0) :
    rayOfNeZero ℝ w hw = b.orientation ↔ 0 < w b := by
  have hcoef : w b ≠ 0 := fun hz => hw (by rw [w.eq_smul_basis_det b, hz, zero_smul])
  rw [Module.Basis.orientation, ray_eq_iff]
  conv_lhs => rw [w.eq_smul_basis_det b]
  exact sameRay_smul_left_iff_of_ne b.det_ne_zero hcoef

end Ray

section VolumeFormNegOne

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)]

/-- The volume form takes the value `-1` on an orthonormal basis inducing the *opposite*
orientation — the companion of `volumeFormL_apply_eq_one`.  Together the two say that the value
of `dV` on an orthonormal basis is `±1`, with the sign reading off the orientation, which is what
lets an orientation be recovered from the sign of a volume. -/
theorem volumeFormL_apply_eq_neg_one (o : Orientation ℝ V (Fin n))
    (e : OrthonormalBasis (Fin n) ℝ V) (he : e.toBasis.orientation ≠ o) :
    o.volumeFormL (e ·) = -1 := by
  rw [Orientation.volumeFormL_apply, o.volumeForm_robust_neg e he]
  simpa using e.toBasis.det_self

end VolumeFormNegOne

/-! ## Unit normals along an immersed hypersurface -/

noncomputable section Hypersurface

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
  {b : Fin (finrank ℝ E) → TangentSpace I x}

/-- **`N` is a unit normal for the immersed submanifold `F : M → M̃` at `x`.**

`normal` is Lee's `N_x ⊥ T_x M`, spelled directly against the vectors `dF_x v` that make up
`T_x M ⊆ T_{F x} M̃` rather than through the submodule `normalSpace`; `unit` is `|N_x|²_g̃ = 1`,
squared so that no square root — hence no fibrewise inner product instance — is needed to
state it.  See `IsUnitNormalVecAt.mem_normalSpace` (`HypersurfaceNormal.lean`) for the
equivalence with `normalSpace`.

`I` is explicit because `TangentSpace I x` is a reducible synonym for `E`: it retains neither
`I` nor `x`, so neither can be recovered from the types of the fields. -/
structure IsUnitNormalAt (I : ModelWithCorners ℝ E H) (g' : RiemannianMetric I' M') (F : M → M')
    (N : (y : M) → TangentSpace I' (F y)) (x : M) : Prop where
  /-- `N_x` is orthogonal to every vector tangent to `M`. -/
  normal : ∀ v : TangentSpace I x, g'.inner (F x) (N x) (mfderiv I I' F x v) = 0
  /-- `N_x` has unit length. -/
  unit : g'.inner (F x) (N x) (N x) = 1

omit [FiniteDimensional ℝ E'] in
/-- **The metric induced by an immersion is preserved by it** — `F^* g̃ = F^* g̃`, so the statement
is `rfl`.  Trivial, but load-bearing: it is what lets every `IsMetricPreserving` lemma be applied
to the induced metric of a submanifold, which is the only metric Lee ever puts on one. -/
theorem isMetricPreserving_pullbackMetric (g' : RiemannianMetric I' M') (F : M → M')
    (hF : ContMDiff I I' ∞ F) (himm : ∀ p : M, Function.Injective (mfderiv I I' F p)) :
    IsMetricPreserving (pullbackMetric g' F hF himm) g' F := fun _ => rfl

/-- **The adapted frame `(N_x, dF E_1, …, dF E_n)`** of the ambient tangent space along a
hypersurface, re-indexed by `Fin (finrank ℝ E')` through the codimension-one hypothesis so that
it can be an ambient basis.  This is the frame Lee's hint to Problem 2-13 asks for.

`Fin.cons` is dependent, so its motive has to be pinned to the constant family; and `I` and `x`
are explicit for the reason recorded on `IsUnitNormalAt`. -/
def consNormal (I : ModelWithCorners ℝ E H) (F : M → M')
    (hdim : finrank ℝ E' = finrank ℝ E + 1) (N : (y : M) → TangentSpace I' (F y)) (x : M)
    (b : Fin (finrank ℝ E) → TangentSpace I x) :
    Fin (finrank ℝ E') → TangentSpace I' (F x) :=
  fun a => Fin.cons (α := fun _ => TangentSpace I' (F x)) (N x)
    (fun i => mfderiv I I' F x (b i)) (finCongr hdim a)

variable {hdim : finrank ℝ E' = finrank ℝ E + 1}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The adapted frame is orthonormal, before re-indexing: `N_x` is a unit vector orthogonal to
each `dF E_i`, and `(dF E_i)` is orthonormal because `F` preserves the metric. -/
theorem inner_cons_normal (h : IsMetricPreserving g g' F) (hN : IsUnitNormalAt I g' F N x)
    (hon : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0)
    (a c : Fin (finrank ℝ E + 1)) :
    g'.inner (F x)
        (Fin.cons (α := fun _ => TangentSpace I' (F x)) (N x)
          (fun i => mfderiv I I' F x (b i)) a)
        (Fin.cons (α := fun _ => TangentSpace I' (F x)) (N x)
          (fun i => mfderiv I I' F x (b i)) c) = if a = c then 1 else 0 := by
  induction a using Fin.cases with
  | zero =>
    induction c using Fin.cases with
    | zero => simpa using hN.unit
    | succ j => simpa using hN.normal (b j)
  | succ i =>
    induction c using Fin.cases with
    | zero =>
      rw [Fin.cons_succ, Fin.cons_zero, g'.symm (F x), hN.normal (b i)]
      simp [Fin.succ_ne_zero]
    | succ j =>
      rw [Fin.cons_succ, Fin.cons_succ, h.inner_mfderiv x (b i) (b j), hon i j]
      simp [Fin.succ_inj]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The adapted frame is orthonormal, stated through `g̃` itself so that using it does not force
the caller to install the fibrewise inner product. -/
theorem inner_consNormal (h : IsMetricPreserving g g' F) (hN : IsUnitNormalAt I g' F N x)
    (hon : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0)
    (a c : Fin (finrank ℝ E')) :
    g'.inner (F x) (consNormal I F hdim N x b a) (consNormal I F hdim N x b c) =
      if a = c then 1 else 0 := by
  simp only [consNormal]
  rw [inner_cons_normal h hN hon]
  simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The adapted frame is orthonormal in the sense of mathlib's `Orthonormal`, once the ambient
metric is installed as a fibrewise inner product. -/
theorem orthonormal_consNormal (h : IsMetricPreserving g g' F) (hN : IsUnitNormalAt I g' F N x)
    (hon : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
    Orthonormal ℝ (consNormal I F hdim N x b) := by
  letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  rw [orthonormal_iff_ite]
  intro a c
  show ⟪consNormal I F hdim N x b a, consNormal I F hdim N x b c⟫_ℝ = _
  rw [show ⟪consNormal I F hdim N x b a, consNormal I F hdim N x b c⟫_ℝ
      = g'.inner (F x) (consNormal I F hdim N x b a) (consNormal I F hdim N x b c) from rfl]
  exact inner_consNormal (hdim := hdim) h hN hon a c

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The adapted frame is linearly independent.  Stated separately from `orthonormal_consNormal`
so that its statement carries no fibrewise inner product: `consNormalBasis` must not depend on
the `RiemannianBundle` instance, or its type would. -/
theorem linearIndependent_consNormal (h : IsMetricPreserving g g' F)
    (hN : IsUnitNormalAt I g' F N x)
    (hon : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    LinearIndependent ℝ (consNormal I F hdim N x b) := by
  letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  exact (orthonormal_consNormal (hdim := hdim) h hN hon).linearIndependent

/-- **The adapted frame as a basis of the ambient tangent space.**

`finrank ℝ E'` many linearly independent vectors span, so they form a basis.  As in
`IsMetricPreserving.pushBasis` the route is `Basis.mk` on `span_eq_top_of_card_eq_finrank'`
rather than `basisOfLinearIndependentOfCardEqFinrank`, whose `[Nonempty ι]` hypothesis would
exclude `0`-dimensional `M` for no reason. -/
def consNormalBasis (h : IsMetricPreserving g g' F) (hN : IsUnitNormalAt I g' F N x)
    (hdim : finrank ℝ E' = finrank ℝ E + 1)
    (hon : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    Basis (Fin (finrank ℝ E')) ℝ (TangentSpace I' (F x)) :=
  haveI : FiniteDimensional ℝ (TangentSpace I' (F x)) := inferInstanceAs (FiniteDimensional ℝ E')
  Basis.mk (linearIndependent_consNormal (hdim := hdim) h hN hon)
    ((linearIndependent_consNormal (hdim := hdim) h hN hon).span_eq_top_of_card_eq_finrank'
      (by simp only [Fintype.card_fin]; rfl)).ge

omit [FiniteDimensional ℝ E] in
@[simp]
theorem coe_consNormalBasis (h : IsMetricPreserving g g' F) (hN : IsUnitNormalAt I g' F N x)
    (hdim : finrank ℝ E' = finrank ℝ E + 1)
    (hon : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    ⇑(consNormalBasis h hN hdim hon) = consNormal I F hdim N x b :=
  Basis.coe_mk _ _

/-! ## Lee's equation (2.17) -/

/-- **The right-hand side of Lee's (2.17), `(N ⌟ dV_g̃)|_M`.**

Two operations, applied in order: contract the ambient volume form with the unit normal
(`camContract`, after `camDomDomCongr` matches the degree `Fin (finrank ℝ E')` of `dV_g̃` with
the `Fin (n+1)` that contraction consumes), then restrict to `M` — which for an immersed `M`
means precomposing each remaining argument with `dF_x`.

Nothing here is smooth or even continuous in `x`: `volumeForm` accepts an arbitrary
`PointwiseOrientation` and `mfderiv` is total, so (2.17) is an identity of *pointwise* forms.
That is the whole reason it costs nothing — cf. `pullbackAlternating`, which is definable for
the same reason. -/
def normalRestrict (I : ModelWithCorners ℝ E H) (g' : RiemannianMetric I' M')
    (o' : PointwiseOrientation I' M') (F : M → M')
    (hdim : finrank ℝ E' = finrank ℝ E + 1) (N : (y : M) → TangentSpace I' (F y)) (x : M) :
    (TangentSpace I x) [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ :=
  (camContract (camDomDomCongr (finCongr hdim) (g'.volumeForm o' (F x))) (N x))
    |>.compContinuousLinearMap (mfderiv I I' F x)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I ∞ M] in
@[simp]
theorem normalRestrict_apply (g' : RiemannianMetric I' M') (o' : PointwiseOrientation I' M')
    (F : M → M') (hdim : finrank ℝ E' = finrank ℝ E + 1)
    (N : (y : M) → TangentSpace I' (F y)) (x : M)
    (v : Fin (finrank ℝ E) → TangentSpace I x) :
    normalRestrict I g' o' F hdim N x v = g'.volumeForm o' (F x) (consNormal I F hdim N x v) :=
  rfl

variable {u : Set M} {Y : Fin (finrank ℝ E) → (y : M) → TangentSpace I y}

/-- **Lee, Proposition 2.43 — equation (2.17): `dV_g = (N ⌟ dV_g̃)|_M`.**

`M` is a hypersurface immersed by `F` in the oriented Riemannian manifold `(M̃, g̃)`, `g` is any
metric that `F` preserves — in particular the induced metric `F^* g̃`, by
`isMetricPreserving_pullbackMetric` — and `N` is a unit normal at `x`.

The proof is Lee's hint to Problem 2-13.  Evaluate the right-hand side on an oriented
orthonormal frame `(E_i)` of `T_x M`: by construction it is `dV_g̃(N_x, dF E_1, …, dF E_n)`, and
`(N_x, dF E_1, …, dF E_n)` is an orthonormal basis of `T_{F x} M̃` — `N_x` is a unit vector
orthogonal to each `dF E_i`, and `(dF E_i)` is orthonormal because `F` preserves the metric.  It
is positively oriented by `hor'`, so the value is `1`.  An `n`-form taking the value `1` on one
oriented orthonormal frame *is* `dV_g` (`volumeForm_unique`), which gives (2.17).

`hor'` — that the adapted basis is positively oriented in `M̃` — is exactly the compatibility
between `o` and `o'` that the induced orientation is *defined* to satisfy; it is not decorative,
and is discharged by `inducedOrientation_consNormalBasis` below. -/
theorem volumeForm_eq_normalRestrict (h : IsMetricPreserving g g' F)
    (hN : IsUnitNormalAt I g' F N x) (hdim : finrank ℝ E' = finrank ℝ E + 1)
    (hY : IsLocalFrameOn I E ∞ Y u)
    (hon : ∀ y ∈ u, ∀ i j, g.inner y (Y i y) (Y j y) = if i = j then 1 else 0) (hx : x ∈ u)
    (hor : (hY.toBasisAt hx).orientation = o x)
    (hor' : (consNormalBasis (b := fun i => Y i x) h hN hdim (hon x hx)).orientation =
      o' (F x)) :
    normalRestrict I g' o' F hdim N x = g.volumeForm o x := by
  letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I' (F x)) = finrank ℝ E') := ⟨rfl⟩
  refine RiemannianMetric.volumeForm_unique g o hY hon hx hor _ ?_
  rw [normalRestrict_apply]
  have hon' : Orthonormal ℝ ⇑(consNormalBasis (b := fun i => Y i x) h hN hdim (hon x hx)) := by
    rw [coe_consNormalBasis]
    exact orthonormal_consNormal (hdim := hdim) h hN (hon x hx)
  have hval := volumeFormL_apply_eq_one (o' (F x))
    ((consNormalBasis (b := fun i => Y i x) h hN hdim (hon x hx)).toOrthonormalBasis hon')
    (by rwa [Basis.toBasis_toOrthonormalBasis])
  simpa only [Basis.coe_toOrthonormalBasis, coe_consNormalBasis] using hval

/-! ## The orientation induced on a hypersurface by a unit normal

The orientation hypothesis `hor'` of `volumeForm_eq_normalRestrict` is not decorative: this
section constructs the orientation of `M` that satisfies it, so that (2.17) has content on every
hypersurface carrying a unit normal.  This is the "if" half of Lee's orientability criterion,
minus smoothness.

Mathlib has no orientation of a subspace, and no orientation induced on a hyperplane by a
transverse vector, so the construction is built from scratch.  It costs nothing, because
`Orientation ℝ V (Fin n)` *is* a ray of `n`-forms and `(N ⌟ dV_g̃)|_M` is already a nonvanishing
`n`-form on `T_x M`: the induced orientation is simply its ray. -/

/-- Every tangent space of a Riemannian manifold carries a `g`-orthonormal basis, with
orthonormality stated through `g` itself. -/
theorem exists_orthonormalBasis_inner (g : RiemannianMetric I M) (x : M) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  refine ⟨(stdOrthonormalBasis ℝ (TangentSpace I x)).toBasis, fun i j => ?_⟩
  have hon := (stdOrthonormalBasis ℝ (TangentSpace I x)).orthonormal
  rw [orthonormal_iff_ite] at hon
  simpa only [OrthonormalBasis.coe_toBasis] using hon i j

/-- `(N ⌟ dV_g̃)|_M` does not vanish at any point: its value on a `g`-orthonormal basis of
`T_x M` is the value of `dV_g̃` on the adapted orthonormal basis of `T_{F x} M̃`, hence `±1`. -/
theorem normalRestrict_toAlternatingMap_ne_zero (h : IsMetricPreserving g g' F)
    (hN : IsUnitNormalAt I g' F N x) (hdim : finrank ℝ E' = finrank ℝ E + 1) :
    (normalRestrict I g' o' F hdim N x).toAlternatingMap ≠ 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I' (F x)) = finrank ℝ E') := ⟨rfl⟩
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_inner g x
  have hon' : Orthonormal ℝ ⇑(consNormalBasis (b := ⇑b) h hN hdim hb) := by
    rw [coe_consNormalBasis]
    exact orthonormal_consNormal (hdim := hdim) h hN hb
  have habs := (o' (F x)).abs_volumeForm_apply_of_orthonormal
    ((consNormalBasis (b := ⇑b) h hN hdim hb).toOrthonormalBasis hon')
  intro hzero
  have hval : (normalRestrict I g' o' F hdim N x) ⇑b = 0 := by
    show (normalRestrict I g' o' F hdim N x).toAlternatingMap ⇑b = 0
    rw [hzero]; rfl
  rw [normalRestrict_apply] at hval
  rw [show ⇑((consNormalBasis (b := ⇑b) h hN hdim hb).toOrthonormalBasis hon')
      = consNormal I F hdim N x ⇑b by
        rw [Basis.coe_toOrthonormalBasis, coe_consNormalBasis]] at habs
  rw [show (o' (F x)).volumeForm (consNormal I F hdim N x ⇑b)
      = g'.volumeForm o' (F x) (consNormal I F hdim N x ⇑b) from rfl, hval] at habs
  norm_num at habs

/-- **The orientation induced on a hypersurface by a unit normal** — the ray of the nonvanishing
`n`-form `(N ⌟ dV_g̃)|_M`.

Lee describes this orientation by the condition that `(E_1, …, E_n)` is positively oriented on
`M` exactly when `(N_x, dF E_1, …, dF E_n)` is positively oriented on `M̃`; that this is what the
ray does is `consNormalBasis_orientation_eq_iff`. -/
def inducedOrientation (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (o' : PointwiseOrientation I' M') (F : M → M')
    (hdim : finrank ℝ E' = finrank ℝ E + 1) (N : (y : M) → TangentSpace I' (F y))
    (h : IsMetricPreserving g g' F) (hN : ∀ y, IsUnitNormalAt I g' F N y) :
    PointwiseOrientation I M := fun x =>
  rayOfNeZero ℝ (normalRestrict I g' o' F hdim N x).toAlternatingMap
    (normalRestrict_toAlternatingMap_ne_zero h (hN x) hdim)

/-- **The induced orientation is Lee's**: a `g`-orthonormal basis of `T_x M` is positively
oriented for `inducedOrientation` exactly when the adapted basis `(N_x, dF E_1, …, dF E_n)` is
positively oriented in `M̃`.

This is what discharges the orientation hypothesis `hor'` of `volumeForm_eq_normalRestrict`, so
(2.17) is not vacuous.  The proof is the `±1` dichotomy: `dV_g̃` takes the value `1` on the
adapted basis if it is positively oriented and `-1` otherwise, and the induced orientation is the
ray of exactly that number times `b.det`. -/
theorem consNormalBasis_orientation_eq_iff (g : RiemannianMetric I M)
    (h : IsMetricPreserving g g' F) (hN : ∀ y, IsUnitNormalAt I g' F N y)
    (hdim : finrank ℝ E' = finrank ℝ E + 1)
    (b : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    (consNormalBasis (b := ⇑b) h (hN x) hdim hb).orientation = o' (F x) ↔
      b.orientation = inducedOrientation g g' o' F hdim N h hN x := by
  letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I' (F x)) = finrank ℝ E') := ⟨rfl⟩
  have hon' : Orthonormal ℝ ⇑(consNormalBasis (b := ⇑b) h (hN x) hdim hb) := by
    rw [coe_consNormalBasis]
    exact orthonormal_consNormal (hdim := hdim) h (hN x) hb
  have hcoe : ⇑((consNormalBasis (b := ⇑b) h (hN x) hdim hb).toOrthonormalBasis hon')
      = consNormal I F hdim N x ⇑b := by
    rw [Basis.coe_toOrthonormalBasis, coe_consNormalBasis]
  rw [inducedOrientation]
  conv_rhs => rw [eq_comm]
  rw [rayOfNeZero_eq_basis_orientation_iff]
  show _ ↔ 0 < (normalRestrict I g' o' F hdim N x) ⇑b
  rw [normalRestrict_apply]
  constructor
  · intro hpos
    have hval := volumeFormL_apply_eq_one (o' (F x))
      ((consNormalBasis (b := ⇑b) h (hN x) hdim hb).toOrthonormalBasis hon')
      (by rwa [Basis.toBasis_toOrthonormalBasis])
    rw [show ((consNormalBasis (b := ⇑b) h (hN x) hdim hb).toOrthonormalBasis hon' ·)
        = consNormal I F hdim N x ⇑b from hcoe] at hval
    rw [show g'.volumeForm o' (F x) (consNormal I F hdim N x ⇑b)
        = (o' (F x)).volumeFormL (consNormal I F hdim N x ⇑b) from rfl, hval]
    norm_num
  · intro hpos
    by_contra hne
    have hval := volumeFormL_apply_eq_neg_one (o' (F x))
      ((consNormalBasis (b := ⇑b) h (hN x) hdim hb).toOrthonormalBasis hon')
      (by rwa [Basis.toBasis_toOrthonormalBasis])
    rw [show ((consNormalBasis (b := ⇑b) h (hN x) hdim hb).toOrthonormalBasis hon' ·)
        = consNormal I F hdim N x ⇑b from hcoe] at hval
    rw [show g'.volumeForm o' (F x) (consNormal I F hdim N x ⇑b)
        = (o' (F x)).volumeFormL (consNormal I F hdim N x ⇑b) from rfl, hval] at hpos
    norm_num at hpos

/-! ### (2.17) with no orientation hypothesis -/

/-- A family orthonormal for `g` is orthonormal for the fibrewise inner product `g` installs. -/
theorem orthonormal_of_inner (g : RiemannianMetric I M) {x : M}
    {c : Fin (finrank ℝ E) → TangentSpace I x}
    (hc : ∀ i j, g.inner x (c i) (c j) = if i = j then 1 else 0) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    Orthonormal ℝ c := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [orthonormal_iff_ite]
  intro i j
  show ⟪c i, c j⟫_ℝ = _
  rw [show ⟪c i, c j⟫_ℝ = g.inner x (c i) (c j) from rfl]
  exact hc i j

/-- **Basis-level uniqueness for `dV_g`**: an `n`-form taking the value `1` on one oriented
orthonormal *basis* of `T_x M` is `dV_g|_x`.

`RiemannianMetric.volumeForm_unique` is the local-frame version of this; it asks for an
`IsLocalFrameOn`, but uses it only through `toBasisAt`, so the basis-level statement is strictly
more general and is what a purely pointwise argument needs. -/
theorem volumeForm_unique_basis (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    {x : M} (b : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0)
    (hor : b.orientation = o x) (θ : (TangentSpace I x) [⋀^Fin (finrank ℝ E)]→L[ℝ] ℝ)
    (hθ : θ ⇑b = 1) : θ = g.volumeForm o x := by
  have hbasis : ∀ v : Fin (finrank ℝ E) → TangentSpace I x, θ v = b.det v * θ ⇑b := by
    intro v
    have hsm := (θ.toAlternatingMap).eq_smul_basis_det b
    have hv := congrArg (fun f => f v) hsm
    simpa [Basis.det_apply, mul_comm] using hv
  ext v
  rw [hbasis v, hθ, mul_one]
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  have hon' : Orthonormal ℝ ⇑b := orthonormal_of_inner g hb
  have hrob := (o x).volumeForm_robust (b.toOrthonormalBasis hon')
    (by rwa [Basis.toBasis_toOrthonormalBasis])
  show _ = (o x).volumeForm v
  rw [hrob, Basis.toBasis_toOrthonormalBasis]

/-- **Two top forms agreeing on one basis are equal.**  Top-degree alternating forms on an
`n`-dimensional space are a line, so a single basis pins one down — no orientation, no
orthonormality, no metric.  This is the orientation-free core of `volumeForm_unique_basis`. -/
theorem eq_of_apply_basis {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {n : ℕ}
    (b : Basis (Fin n) ℝ V) (θ η : V [⋀^Fin n]→L[ℝ] ℝ) (hval : θ ⇑b = η ⇑b) : θ = η := by
  ext v
  have hθ := congrArg (fun f => f v) (θ.toAlternatingMap.eq_smul_basis_det b)
  have hη := congrArg (fun f => f v) (η.toAlternatingMap.eq_smul_basis_det b)
  simp only [AlternatingMap.smul_apply, smul_eq_mul] at hθ hη
  rw [show θ v = θ.toAlternatingMap v from rfl, hθ,
    show η v = η.toAlternatingMap v from rfl, hη]
  exact congrArg (fun c => c * b.det v) hval

/-- `dV_g` takes the value `1` on a positively oriented orthonormal basis of `T_x M` — the
basis-level form of `volumeForm_apply_eq_one`. -/
theorem volumeForm_apply_basis_eq_one (g : RiemannianMetric I M) (o : PointwiseOrientation I M)
    {x : M} (b : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0)
    (hor : b.orientation = o x) : g.volumeForm o x ⇑b = 1 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  have hon' : Orthonormal ℝ ⇑b := orthonormal_of_inner g hb
  have hval := volumeFormL_apply_eq_one (o x) (b.toOrthonormalBasis hon')
    (by rwa [Basis.toBasis_toOrthonormalBasis])
  simpa only [Basis.coe_toOrthonormalBasis] using hval

/-- `dV_g` takes the value `-1` on a negatively oriented orthonormal basis of `T_x M`. -/
theorem volumeForm_apply_basis_eq_neg_one (g : RiemannianMetric I M)
    (o : PointwiseOrientation I M) {x : M} (b : Basis (Fin (finrank ℝ E)) ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0)
    (hor : b.orientation ≠ o x) : g.volumeForm o x ⇑b = -1 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I x) = finrank ℝ E) := ⟨rfl⟩
  have hon' : Orthonormal ℝ ⇑b := orthonormal_of_inner g hb
  have hval := volumeFormL_apply_eq_neg_one (o x) (b.toOrthonormalBasis hon')
    (by rwa [Basis.toBasis_toOrthonormalBasis])
  simpa only [Basis.coe_toOrthonormalBasis] using hval

/-- **Lee, Proposition 2.43, equation (2.17), with the orientation hypothesis discharged.**

For the orientation a unit normal `N` induces on the hypersurface, `dV_g = (N ⌟ dV_g̃)|_M` holds
outright: no compatibility between the two orientations has to be assumed, because
`inducedOrientation` is built to satisfy it, and no orientability of `M` has to be assumed
either — the statement supplies its own orientation.

The proof needs no *oriented* frame, only some orthonormal basis `b`, which always exists.  The
two sides agree on `b` whichever way `b` happens to be oriented, because flipping `b` negates
both at once: `dV_g` by `volumeForm_apply_basis_eq_neg_one`, and `(N ⌟ dV_g̃)|_M` because its ray
*is* the induced orientation.  Two top forms agreeing on one basis are equal. -/
theorem volumeForm_inducedOrientation_eq_normalRestrict (g : RiemannianMetric I M)
    (h : IsMetricPreserving g g' F) (hN : ∀ y, IsUnitNormalAt I g' F N y)
    (hdim : finrank ℝ E' = finrank ℝ E + 1) (x : M) :
    g.volumeForm (inducedOrientation g g' o' F hdim N h hN) x =
      normalRestrict I g' o' F hdim N x := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  haveI : Fact (finrank ℝ (TangentSpace I' (F x)) = finrank ℝ E') := ⟨rfl⟩
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_inner g x
  set o := inducedOrientation g g' o' F hdim N h hN with ho
  have hon' : Orthonormal ℝ ⇑(consNormalBasis (b := ⇑b) h (hN x) hdim hb) := by
    rw [coe_consNormalBasis]
    exact orthonormal_consNormal (hdim := hdim) h (hN x) hb
  have hcoe : ((consNormalBasis (b := ⇑b) h (hN x) hdim hb).toOrthonormalBasis hon' ·)
      = consNormal I F hdim N x ⇑b := by
    rw [Basis.coe_toOrthonormalBasis, coe_consNormalBasis]
  refine eq_of_apply_basis b _ _ ?_
  rw [normalRestrict_apply]
  rcases eq_or_ne (b.orientation) (o x) with hbo | hbo
  · -- `b` is positively oriented: both sides are `1`.
    rw [volumeForm_apply_basis_eq_one g o b hb hbo]
    have hval := volumeFormL_apply_eq_one (o' (F x))
      ((consNormalBasis (b := ⇑b) h (hN x) hdim hb).toOrthonormalBasis hon')
      (by rw [Basis.toBasis_toOrthonormalBasis]
          exact (consNormalBasis_orientation_eq_iff g h hN hdim b hb).mpr hbo)
    rw [hcoe] at hval
    exact hval.symm
  · -- `b` is negatively oriented: both sides are `-1`.
    rw [volumeForm_apply_basis_eq_neg_one g o b hb hbo]
    have hval := volumeFormL_apply_eq_neg_one (o' (F x))
      ((consNormalBasis (b := ⇑b) h (hN x) hdim hb).toOrthonormalBasis hon')
      (by rw [Basis.toBasis_toOrthonormalBasis]
          exact fun hc => hbo ((consNormalBasis_orientation_eq_iff g h hN hdim b hb).mp hc))
    rw [hcoe] at hval
    exact hval.symm

end Hypersurface

end LeeLib.Ch02
