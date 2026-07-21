/-
Chapter 2, "Riemannian Metrics", §5 "The Volume Form": the smoothness half of
Lee's Proposition 2.43 — a hypersurface carrying a smooth global unit normal is
*orientable*, and the orientation the normal induces is a smooth one.

`HypersurfaceVolumeForm.lean` builds the pointwise theory: the orientation
`inducedOrientation` a unit normal puts on each `T_x M` (the ray of the
nonvanishing `n`-form `(N ⌟ dV_g̃)|_M`), and equation (2.17)

  dV_g = (N ⌟ dV_g̃)|_M                                                  (2.17)

for it.  Nothing there is smooth in `x`: `volumeForm` accepts an arbitrary
`PointwiseOrientation` and `mfderiv` is total, so (2.17) costs nothing.  What is
missing — and is the whole content of Lee's orientability claim — is that
`inducedOrientation` is a *smooth* orientation, i.e. that it is realized near
each point by a smooth local frame.  That is `isSmoothOrientation_inducedOrientation`.

## The argument

Near `p`, take a smooth local `g`-orthonormal frame `(E_i)` of `TM`
(`exists_orthonormalFrame_nhds`, Lee's Proposition 2.8).  The adapted frame
`(N, dF E_1, …, dF E_n)` is then an orthonormal *basis* of `T_{F x} M̃` at every
`x`, so the scalar

  s(x) = dV_g̃|_{F x}(N_x, dF_x E_1, …, dF_x E_n) = (N ⌟ dV_g̃)|_M|_x (E_· x)

is `±1`, and by construction `inducedOrientation x` is the ray of that form: `(E_i)`
is positively oriented exactly when `s(x) > 0`.  So it suffices that `s` be
*continuous*: it is then locally constant, and on the neighbourhood where it is
negative one negates a single member of the frame, which negates `s` and fixes
the orientation.  This is where `0 < finrank ℝ E` is genuinely needed — see below.

## Why the smoothness of `s` is the real work

Smoothness of `s` is "apply a smooth section of the bundle of `n`-forms to `n`
smooth vector fields", and **mathlib has no such lemma**: `clm_bundle_apply` and
`clm_bundle_apply₂` exist only for the bundle of continuous *linear* maps, and
there is no bundle of alternating maps upstream at all (its own TODO in
`Analysis/Calculus/DifferentialForm/Basic.lean` says so).  `contMDiffAt_volumeForm`
sidesteps the same gap by a trick special to top degree, and that trick does not
help here because the frame is not the one `dV_g̃` was trivialized against.

The route taken instead never mentions the alternating bundle.  Lee's own
determinant formula `volumeForm_apply_eq_det` expresses `dV_g̃|_y(v)` against a
local oriented orthonormal frame `(Z_a)` of `T M̃` as

  dV_g̃|_y(v) = det [ ⟨Z_a|_y, v_b⟩_g̃ ],

so `s` becomes a determinant whose entries are inner products of two smooth
sections of the *pullback* bundle `F *ᵖ T M̃`:

* `x ↦ Z_a|_{F x}` — a smooth section of `T M̃` composed with `F`
  (`contMDiffAt_comp_section`);
* `x ↦ (N_x, dF_x E_i)` — the unit normal (hypothesis) and the pushforwards of the
  frame (`contMDiffAt_pushforward`), assembled by `contMDiffAt_consNormal`.

Mathlib's `ContMDiffWithinAt.inner_bundle` is stated for an *arbitrary* bundle and
an *arbitrary* base map, so it applies to `F *ᵖ T M̃` once the pulled-back metric is
installed as a `RiemannianBundle` instance; and the determinant is expanded by hand
(`Matrix.det_apply'`), the pin having no smoothness lemma for `Matrix.det`.  This is
the same shape as `contMDiffOn_densityAt`.

## `0 < finrank ℝ E` is not a technicality

`IsSmoothOrientation` asks for a local frame realizing the orientation, and a
`0`-dimensional manifold has exactly one frame — the empty one — whose orientation
is always the ray of the constant `1`.  But `Orientation ℝ V (Fin 0)` still has two
elements, and a unit normal on a `0`-manifold in a `1`-manifold may well induce the
other one (`dV_g̃(N_x) = -1`).  So `IsSmoothOrientation (inducedOrientation …)` is
*false* in that degenerate case, and the hypothesis is necessary rather than an
artefact of the proof.  (`M` is of course still orientable; it is the *induced*
orientation that is not expressible.)  Lee's hypersurfaces have `n ≥ 1`.

## New infrastructure

`isLocalFrameOn_negMember` — negating one member of a smooth local frame leaves a
smooth local frame.  Mathlib has no way to modify a member of an `IsLocalFrameOn`
at all (only `congr`, for pointwise-equal families, and `mono`); it is stated here
over an arbitrary smooth vector bundle because nothing about it is Riemannian.
-/
import LeeLib.Ch02.HypersurfaceVolumeForm
import LeeLib.Ch02.NormalBundle

namespace LeeLib.Ch02

open Bundle InnerProductSpace Module Submodule
open scoped Manifold ContDiff RealInnerProductSpace Topology

/-! ## Sections of a pullback bundle -/

section Comp

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EB' : Type*} [NormedAddCommGroup EB'] [NormedSpace ℝ EB']
  {HB' : Type*} [TopologicalSpace HB'] {IB' : ModelWithCorners ℝ EB' HB'}
  {B' : Type*} [TopologicalSpace B'] [ChartedSpace HB' B']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ∞ω}

omit [∀ b, Module ℝ (E b)] [∀ b, IsTopologicalAddGroup (E b)]
  [∀ b, ContinuousConstSMul ℝ (E b)] [VectorBundle ℝ F E] in
/-- **A smooth section of `E`, composed with a smooth map `f`, is a smooth section of `f *ᵖ E`.**

The proof is three lines because the trivialization of `f *ᵖ E` at `x₀` *is* the one of `E` at
`f x₀` (`trivializationAt_pullback`), so reading both sides in trivializations turns the claim
into "a smooth map composed with `f` is smooth".  Note no cast intervenes: the fibre `(f *ᵖ E) x`
is `E (f x)` by definition. -/
theorem contMDiffAt_comp_section (f : C^n⟮IB', B'; IB, B⟯) {s : (y : B) → E y} {x₀ : B'}
    (hs : ContMDiffAt IB (IB.prod 𝓘(ℝ, F)) n (fun y => TotalSpace.mk' F y (s y)) (f x₀)) :
    ContMDiffAt IB' (IB'.prod 𝓘(ℝ, F)) n
      (fun x => TotalSpace.mk' F (E := (f : B' → B) *ᵖ E) x (s (f x))) x₀ := by
  rw [contMDiffAt_section]
  rw [contMDiffAt_section] at hs
  exact hs.comp x₀ f.contMDiff.contMDiffAt

end Comp

/-! ## Negating one member of a local frame -/

section NegFrame

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} {ι : Type*} [DecidableEq ι] {Y : ι → (x : B) → V x} {u : Set B}

/-- The family of sections `Y` with its `i₀`-th member negated. -/
def negMember (Y : ι → (x : B) → V x) (i₀ : ι) : ι → (x : B) → V x :=
  Function.update Y i₀ (-(Y i₀))

omit [TopologicalSpace B] [∀ x, TopologicalSpace (V x)] in
theorem negMember_apply (Y : ι → (x : B) → V x) (i₀ : ι) (x : B) :
    (fun i => negMember Y i₀ i x) = Function.update (fun i => Y i x) i₀ (-(Y i₀ x)) := by
  funext i
  rcases eq_or_ne i i₀ with rfl | h
  · simp [negMember]
  · simp [negMember, h]

/-- **Negating one member of a smooth local frame leaves a smooth local frame.**

Mathlib cannot modify a member of an `IsLocalFrameOn` at all: `congr` only replaces a family by a
pointwise-equal one and `mono` only shrinks the set.  Nothing here is Riemannian, so this is
stated over an arbitrary smooth vector bundle.

Each field is separate work: smoothness is `ContMDiffOn.neg_section`; independence is
`LinearIndependent.units_smul` for the units `Function.update 1 i₀ (-1)`, once the negated family
is recognized as that scaling; spanning holds because `-v` and `v` span the same line. -/
theorem isLocalFrameOn_negMember (hY : IsLocalFrameOn IB F n Y u) (i₀ : ι) :
    IsLocalFrameOn IB F n (negMember Y i₀) u where
  linearIndependent := fun {x} hx => by
    rw [negMember_apply]
    have hw : Function.update (fun i => Y i x) i₀ (-(Y i₀ x))
        = (Function.update (1 : ι → 𝕜ˣ) i₀ (-1)) • (fun i => Y i x) := by
      funext i
      rcases eq_or_ne i i₀ with rfl | h
      · simp
      · simp [h]
    rw [hw]
    exact (hY.linearIndependent hx).units_smul _
  generating := fun {x} hx => by
    refine le_trans (hY.generating hx) (Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    rcases eq_or_ne i i₀ with rfl | h
    · have hmem : -(Y i x) ∈ Submodule.span 𝕜 (Set.range fun j => negMember Y i j x) :=
        Submodule.subset_span ⟨i, by simp [negMember]⟩
      simpa using Submodule.neg_mem _ hmem
    · exact Submodule.subset_span ⟨i, by simp [negMember, h]⟩
  contMDiffOn i := by
    rcases eq_or_ne i i₀ with rfl | h
    · have hi : negMember Y i i = -(Y i) := by simp [negMember]
      rw [hi]
      exact (hY.contMDiffOn i).neg_section
    · have hi : negMember Y i₀ i = Y i := by simp [negMember, h]
      rw [hi]
      exact hY.contMDiffOn i

end NegFrame

/-! ## The induced orientation is smooth -/

noncomputable section Hyper

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

variable {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'} {f : C^∞⟮I, M; I', M'⟯}
  {o' : PointwiseOrientation I' M'} {hdim : finrank ℝ E' = finrank ℝ E + 1}
  {N : (y : M) → TangentSpace I' (f y)}

variable (I f N) in
/-- **`N` varies smoothly along `M` near `x₀`** — it is a smooth section of the ambient tangent
bundle along `f`, i.e. of the pullback bundle `f *ᵖ T M̃`, at `x₀`.

`IsUnitNormalAt` is purely pointwise, so this is the extra regularity Lee's "smooth unit normal
vector field" carries.  It is stated *at a point* rather than globally on purpose: the converse
half of Proposition 2.43 constructs its normal out of the local ones supplied by
`exists_orthonormalFrame_normalSpace`, which are smooth only on a neighbourhood, and a global
hypothesis would be undischargeable there.

`f` is bundled (`C^∞⟮I, M; I', M'⟯` rather than `F : M → M'`) because the pullback bundle's
instances are keyed on the bundled type. -/
def IsSmoothNormalAt (x₀ : M) : Prop :=
  ContMDiffAt I (I.prod 𝓘(ℝ, E')) ∞
    (fun x => TotalSpace.mk' E' (E := (f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x (N x)) x₀

variable (I f N) in
/-- **`N` is a smooth global normal field**: it varies smoothly at every point of `M`. -/
def IsSmoothNormalField : Prop := ∀ x₀ : M, IsSmoothNormalAt I f N x₀

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **Each member of the adapted frame `(N, dF E_1, …, dF E_n)` is a smooth section of `f *ᵖ T M̃`.**

The zeroth is `N` itself; the rest are pushforwards of the frame, smooth by
`contMDiffAt_pushforward`.  The case split is on `finCongr hdim j`, which is what the
codimension-one re-indexing of `consNormal` consumes. -/
theorem contMDiffAt_consNormal {Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x} {u : Set M}
    (hY : IsLocalFrameOn I E ∞ Y u) (hu : IsOpen u) {x₀ : M} (hx₀ : x₀ ∈ u)
    (hN : IsSmoothNormalAt I f N x₀) (j : Fin (finrank ℝ E')) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E')) ∞
      (fun x => TotalSpace.mk' E' (E := (f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x
        (consNormal I (f : M → M') hdim N x (Y · x) j)) x₀ := by
  simp only [consNormal]
  rcases Fin.eq_zero_or_eq_succ (finCongr hdim j) with h | ⟨i, h⟩
  · rw [h]
    simpa using hN
  · rw [h]
    simp only [Fin.cons_succ]
    exact contMDiffAt_pushforward (f := f) (X := Y i) (hY.contMDiffAt hu hx₀ i)

omit [FiniteDimensional ℝ E] in
/-- **The value of `(N ⌟ dV_g̃)|_M` on a smooth local frame is a smooth function of the base
point** — the analytic heart of Lee's orientability criterion.

There is no lemma anywhere for "a smooth section of the bundle of `n`-forms, applied to `n` smooth
vector fields, is smooth" (see the file header).  So `dV_g̃` is not treated as a section at all:
Lee's own `volumeForm_apply_eq_det` turns its value into a determinant against a local *oriented*
orthonormal frame `(Z_a)` of `T M̃` (which is exactly what `IsSmoothOrientation o'` supplies, via
`exists_orientedOrthonormalFrame_nhds`), and each entry `⟨Z_a|_{f x}, ·⟩_g̃` is an inner product of
two smooth sections of `f *ᵖ T M̃`, hence smooth by mathlib's `ContMDiffWithinAt.inner_bundle` —
which is general enough because it quantifies over the bundle *and* the base map.  The determinant
is then expanded by hand, the pin having no smoothness lemma for `Matrix.det`. -/
theorem contMDiffAt_normalRestrict_frame (ho' : IsSmoothOrientation o')
    {Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x} {u : Set M}
    (hY : IsLocalFrameOn I E ∞ Y u) (hu : IsOpen u) {x₀ : M} (hx₀ : x₀ ∈ u)
    (hN : ∀ x ∈ u, IsSmoothNormalAt I f N x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => normalRestrict I g' o' (f : M → M') hdim N x (Y · x)) x₀ := by
  classical
  letI : Bundle.RiemannianBundle ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) :=
    ⟨(g'.pullback f).toRiemannianMetric⟩
  obtain ⟨w, Z, hwopen, hfx₀, hZ, hZon, hZor⟩ := exists_orientedOrthonormalFrame_nhds g' ho' (f x₀)
  set v : Set M := u ∩ (f : M → M') ⁻¹' w with hv
  have hvopen : IsOpen v := hu.inter (hwopen.preimage f.contMDiff.continuous)
  have hx₀v : x₀ ∈ v := ⟨hx₀, hfx₀⟩
  refine ContMDiffOn.contMDiffAt ?_ (hvopen.mem_nhds hx₀v)
  -- On `v`, Lee's determinant formula expresses the value against the ambient oriented frame.
  have hrepr : ∀ x ∈ v, normalRestrict I g' o' (f : M → M') hdim N x (Y · x)
      = (Matrix.of fun i j =>
          g'.inner (f x) (Z i (f x)) (consNormal I (f : M → M') hdim N x (Y · x) j)).det := by
    intro x hx
    rw [normalRestrict_apply]
    exact g'.volumeForm_apply_eq_det o' hZ hZon hx.2 (hZor _ hx.2) _
  refine ContMDiffOn.congr ?_ hrepr
  intro x hx
  have hentry : ∀ i j, ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
      (fun y => g'.inner (f y) (Z i (f y)) (consNormal I (f : M → M') hdim N y (Y · y) j)) v x := by
    intro i j
    have h1 : ContMDiffAt I (I.prod 𝓘(ℝ, E')) ∞
        (fun y => TotalSpace.mk' E' (E := (f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) y
          (Z i (f y))) x :=
      contMDiffAt_comp_section f (hZ.contMDiffAt hwopen hx.2 i)
    have h2 := contMDiffAt_consNormal (hdim := hdim) hY hu hx.1 (hN x hx.1) j
    exact ContMDiffWithinAt.inner_bundle (IB := I) (F := E')
      (E := ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _))) (b := fun y => y) (IM := I)
      h1.contMDiffWithinAt h2.contMDiffWithinAt
  simp only [Matrix.det_apply']
  refine ContMDiffWithinAt.sum fun σ _ => ?_
  exact contMDiffWithinAt_const.mul (ContMDiffWithinAt.prod fun i _ => hentry (σ i) i)

omit [FiniteDimensional ℝ E] in
/-- `contMDiffAt_normalRestrict_frame`, on an open set. -/
theorem contMDiffOn_normalRestrict_frame (ho' : IsSmoothOrientation o')
    {Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x} {u : Set M}
    (hY : IsLocalFrameOn I E ∞ Y u) (hu : IsOpen u)
    (hN : ∀ x ∈ u, IsSmoothNormalAt I f N x) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x => normalRestrict I g' o' (f : M → M') hdim N x (Y · x)) u := fun _ hx =>
  (contMDiffAt_normalRestrict_frame (hdim := hdim) ho' hY hu hx hN).contMDiffWithinAt

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] in
/-- **Negating one member of the frame negates the value of `(N ⌟ dV_g̃)|_M` on it** — which is
what lets a negatively oriented frame be repaired.  This is multilinearity in one slot
(`AlternatingMap.map_update_neg`); no continuity, metric or orientation is involved. -/
theorem normalRestrict_negMember
    {Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x} (i₀ : Fin (finrank ℝ E)) (x : M) :
    normalRestrict I g' o' (f : M → M') hdim N x (negMember Y i₀ · x)
      = - normalRestrict I g' o' (f : M → M') hdim N x (Y · x) := by
  classical
  rw [negMember_apply]
  show (normalRestrict I g' o' (f : M → M') hdim N x).toAlternatingMap
      (Function.update (fun i => Y i x) i₀ (-(Y i₀ x))) = _
  rw [AlternatingMap.map_update_neg, Function.update_eq_self]
  rfl

/-- **The orientation a smooth global unit normal induces on a hypersurface is smooth** — the
orientability half of Lee's Proposition 2.43.

Near `p`, a smooth `g`-orthonormal frame `(E_i)` exists (Proposition 2.8).  It realizes
`inducedOrientation` at exactly the points where `s(x) = (N ⌟ dV_g̃)|_M|_x(E_· x)` is positive,
because that orientation *is* the ray of that form.  `s` is smooth, hence continuous, and never
zero (a nonzero top form does not vanish on a basis), so its sign is locally constant: on the
piece where `s > 0` the frame does the job, and on the piece where `s < 0` negating one member
negates `s` and repairs it.

`0 < finrank ℝ E` supplies the member to negate, and is genuinely necessary — see the file
header: on a `0`-manifold the statement is false, since the only frame is the empty one. -/
theorem isSmoothOrientation_inducedOrientation (hpos : 0 < finrank ℝ E)
    (h : IsMetricPreserving g g' (f : M → M')) (hN : ∀ y, IsUnitNormalAt I g' (f : M → M') N y)
    (hNsmooth : IsSmoothNormalField I f N) (ho' : IsSmoothOrientation o') :
    IsSmoothOrientation (inducedOrientation g g' o' (f : M → M') hdim N h hN) := by
  classical
  -- a frame realizes the induced orientation exactly where the form is positive on it
  have hchar : ∀ {u' : Set M} {Z : Fin (finrank ℝ E) → (x : M) → TangentSpace I x}
      (hZ : IsLocalFrameOn I E ∞ Z u') {x : M} (hx : x ∈ u'),
      ((hZ.toBasisAt hx).orientation = inducedOrientation g g' o' (f : M → M') hdim N h hN x
        ↔ 0 < normalRestrict I g' o' (f : M → M') hdim N x (Z · x)) := by
    intro u' Z hZ x hx
    have hcoe : ⇑(hZ.toBasisAt hx) = fun i => Z i x := funext fun i => hZ.toBasisAt_coe hx i
    rw [inducedOrientation, eq_comm, rayOfNeZero_eq_basis_orientation_iff, hcoe]
    exact Iff.rfl
  intro p
  obtain ⟨u, Y, huopen, hpu, hY, hYon⟩ := exists_orthonormalFrame_nhds g p
  set s : M → ℝ := fun x => normalRestrict I g' o' (f : M → M') hdim N x (Y · x) with hsdef
  have hcont : ContinuousOn s u :=
    (contMDiffOn_normalRestrict_frame (hdim := hdim) ho' hY huopen
      (fun x _ => hNsmooth x)).continuousOn
  -- `(N ⌟ dV_g̃)|_M` is a nonzero top form, so it does not vanish on a basis
  have hne : ∀ x ∈ u, s x ≠ 0 := by
    intro x hx
    have h1 := normalRestrict_toAlternatingMap_ne_zero (o' := o') h (hN x) hdim
    have h2 := (AlternatingMap.map_basis_ne_zero_iff (hY.toBasisAt hx)
      (normalRestrict I g' o' (f : M → M') hdim N x).toAlternatingMap).mpr h1
    have hcoe : ⇑(hY.toBasisAt hx) = fun i => Y i x := funext fun i => hY.toBasisAt_coe hx i
    rw [hcoe] at h2
    exact h2
  rcases lt_or_gt_of_ne (hne p hpu) with hlt | hgt
  · -- the frame is negatively oriented near `p`: negate one member
    refine ⟨u ∩ s ⁻¹' (Set.Iio 0), negMember Y ⟨0, hpos⟩,
      hcont.isOpen_inter_preimage huopen isOpen_Iio, ⟨hpu, hlt⟩,
      (isLocalFrameOn_negMember hY ⟨0, hpos⟩).mono Set.inter_subset_left, ?_⟩
    intro x hx
    rw [hchar _ hx, normalRestrict_negMember]
    exact neg_pos.mpr hx.2
  · -- the frame is already positively oriented near `p`
    refine ⟨u ∩ s ⁻¹' (Set.Ioi 0), Y, hcont.isOpen_inter_preimage huopen isOpen_Ioi, ⟨hpu, hgt⟩,
      hY.mono Set.inter_subset_left, ?_⟩
    intro x hx
    rw [hchar _ hx]
    exact hx.2

/-- **Lee, Proposition 2.43, the "if" half**: a hypersurface carrying a smooth global unit normal
`N` is orientable, and for the orientation `N` induces, `dV_g = (N ⌟ dV_g̃)|_M` — equation (2.17).

The orientation is not an extra input: it is `inducedOrientation`, built from `N` itself. -/
theorem exists_smoothOrientation_volumeForm_eq_normalRestrict (hpos : 0 < finrank ℝ E)
    (h : IsMetricPreserving g g' (f : M → M')) (hN : ∀ y, IsUnitNormalAt I g' (f : M → M') N y)
    (hNsmooth : IsSmoothNormalField I f N) (ho' : IsSmoothOrientation o') :
    ∃ o : PointwiseOrientation I M, IsSmoothOrientation o ∧
      ∀ x, g.volumeForm o x = normalRestrict I g' o' (f : M → M') hdim N x :=
  ⟨inducedOrientation g g' o' (f : M → M') hdim N h hN,
    isSmoothOrientation_inducedOrientation hpos h hN hNsmooth ho',
    volumeForm_inducedOrientation_eq_normalRestrict g h hN hdim⟩

end Hyper

end LeeLib.Ch02
