/-
Appendix A, Lemma A.34: the **local frame criterion for subbundles**.

Given a smooth vector bundle `V → B` and, for each `x : B`, a `k`-dimensional
subspace `D x ⊆ V x`, Lee's Lemma A.34 says that if every point has a
neighbourhood carrying `k` smooth sections of `V` whose values form a basis of
`D` at each point, then `D` is a smooth rank-`k` subbundle of `V`.

mathlib has no notion of a smooth vector subbundle — `grep -ri subbundle` over
the pin returns nothing — so the conclusion has to be spelled out as the bundle
structure itself: a topology on `TotalSpace (EuclideanSpace ℝ (Fin k)) (fun x => ↥(D x))`
together with `FiberBundle`, `VectorBundle` and `ContMDiffVectorBundle`
structures for it.  `Bundle.VectorPrebundle` is the tool for exactly this: it
asks for an atlas of *pre*trivializations (fibrewise-linear partial equivalences,
with no continuity demanded of them), continuity of the coordinate changes, and
the compatibility `totalSpaceMk_isInducing` of the fibre topologies; it then
manufactures the total-space topology and the bundle.  Note that mathlib
constructs no `VectorPrebundle` anywhere, so there is no worked example to
follow; the fields below are discharged from first principles.

`VectorBundleCore` is *not* an alternative here.  It builds a synthetic fibre
type out of the coordinate changes, so it cannot express `D` **as a family of
subspaces of `V`** — which is the whole content of A.34.  Mathlib's
`IsLocalFrameOn` is also unusable on `D`: its variable block already carries
`[TopologicalSpace (TotalSpace F V)]` and `[FiberBundle F V]`, i.e. it presumes
precisely the bundle structure A.34 is supposed to produce.  Hence the
`D`-valued frame predicates `IsLocalSubframeOn` / `IsOrthonormalSubframeOn`
below.

**The route, and where it departs from Lee.**  Lee proves A.34 for a bare smooth
vector bundle, completing an arbitrary local `D`-frame to a frame of `V` and
reading coordinate changes off A.33.  We instead assume the ambient bundle is
Riemannian (`IsContMDiffRiemannianBundle`) and *normalize the frame to be
orthonormal* (Gram-Schmidt, Lee's Prop. 2.8, already formalized as
`gramSchmidtFrame`).  The payoff is that the fibre coordinates become inner
products,

  `subframeCoord s x v = (⟪s i x, v⟫)_i`,

so that (i) the coordinate map is visibly linear at *every* point, with no
appeal to A.33, (ii) the coordinate change between two orthonormal `D`-frames is
the Gram matrix `⟪t j b, s i b⟫`, whose smoothness is one application of the
existing `ContMDiffOn.inner_bundle`, and (iii) with model fibre
`EuclideanSpace ℝ (Fin k)` the coordinate map is a linear *isometry*
(`OrthonormalBasis.repr`), which is what discharges `totalSpaceMk_isInducing`.

The extra hypothesis costs nothing where A.34 is used.  Proposition 2.16 applies
it to the normal spaces inside the ambient tangent bundle `F *ᵖ T M̃`, which is
Riemannian by `Bundle.ContMDiffRiemannianMetric.pullback`.  Removing it again
would need "every smooth vector bundle over a manifold admits a metric", which
is not in the pin (we have `exists_riemannianMetric` for tangent bundles only).

**Total data, propositional hypotheses.**  `subframeSection`, `subframeCoord`
and `subframeComb` are defined for *every* point of `B`, using a junk value
where the frame is not a `D`-basis.  This keeps the pretrivialization *data*
independent of the frame's defining hypotheses — only its *proof* fields mention
them — which is what makes the atlas and the coordinate changes manageable.
-/
import LeeLib.Ch02.OrthonormalFrame

namespace LeeLib.AppendixA

open Bundle InnerProductSpace LeeLib.Ch02 Module Set Submodule Topology
open scoped Manifold ContDiff RealInnerProductSpace Topology

/-! ### A finite-sum rule for `ContMDiffOn` into a normed space

mathlib has `ContMDiffOn.sum_section` for sections of a vector bundle, but no
finite-sum rule for maps into a normed space.  The coordinate change below is a
finite sum of scalar multiples of constant continuous linear maps, so it needs
one. -/

section FinsetSum

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {n : ℕ∞ω} {u : Set B}

/-- A finite sum of `C^n` maps into a normed space is `C^n`. -/
theorem contMDiffOn_finset_sum {ι : Type*} (t : Finset ι) {f : ι → B → W}
    (h : ∀ i ∈ t, ContMDiffOn IB 𝓘(ℝ, W) n (f i) u) :
    ContMDiffOn IB 𝓘(ℝ, W) n (fun x => ∑ i ∈ t, f i x) u := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using contMDiffOn_const
  | insert i t hi IH =>
      simp only [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i t)).add
        (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

end FinsetSum

section Subbundle

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [IsContMDiffRiemannianBundle IB n F V]
  {k : ℕ} {D : (x : B) → Submodule ℝ (V x)}
  {s t : Fin k → (x : B) → V x} {u w : Set B} {x : B}

/-! ### Local frames for a family of subspaces -/

variable (IB F n) in
/-- A **local frame for the family of subspaces `D`** over `u`: `k` smooth sections of the
ambient bundle `V` whose values at each `x ∈ u` form a basis of `D x`.

This is the hypothesis of Lee's Lemma A.34.  It cannot be phrased with mathlib's
`IsLocalFrameOn` applied to `D`, because that predicate presumes `D` already carries the
`FiberBundle` structure A.34 is meant to construct. -/
structure IsLocalSubframeOn (D : (x : B) → Submodule ℝ (V x)) (s : Fin k → (x : B) → V x)
    (u : Set B) : Prop extends IsLocalIndepOn IB F n s u where
  span_eq {x : B} (hx : x ∈ u) : span ℝ (range (s · x)) = D x

variable (IB F n) in
/-- An **orthonormal local frame for the family of subspaces `D`** over `u`: the values form an
orthonormal basis of `D x` at each `x ∈ u`.

Every local `D`-frame can be normalized to one (`IsLocalSubframeOn.gramSchmidt`), and doing so
is what makes the fibre coordinates inner products. -/
structure IsOrthonormalSubframeOn (D : (x : B) → Submodule ℝ (V x)) (s : Fin k → (x : B) → V x)
    (u : Set B) : Prop where
  contMDiffOn (i : Fin k) : ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (s i)) u
  orthonormal {x : B} (hx : x ∈ u) : Orthonormal ℝ (s · x)
  span_eq {x : B} (hx : x ∈ u) : span ℝ (range (s · x)) = D x

namespace IsOrthonormalSubframeOn

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
/-- The members of a local `D`-frame lie in `D`; this is `span_eq` read through `subset_span`,
which is why membership is not a separate field. -/
theorem mem (hs : IsOrthonormalSubframeOn IB F n D s u) (hx : x ∈ u) (i : Fin k) :
    s i x ∈ D x :=
  hs.span_eq hx ▸ subset_span (mem_range_self i)

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
theorem toIsLocalIndepOn (hs : IsOrthonormalSubframeOn IB F n D s u) :
    IsLocalIndepOn IB F n s u where
  linearIndependent hx := (hs.orthonormal hx).linearIndependent
  contMDiffOn i := hs.contMDiffOn i

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
theorem mono (hs : IsOrthonormalSubframeOn IB F n D s u) (h : w ⊆ u) :
    IsOrthonormalSubframeOn IB F n D s w where
  contMDiffOn i := (hs.contMDiffOn i).mono h
  orthonormal hx := hs.orthonormal (h hx)
  span_eq hx := hs.span_eq (h hx)

end IsOrthonormalSubframeOn

/-- **Gram-Schmidt normalizes a local `D`-frame.**  Orthonormality and smoothness are Lee's
Proposition 2.8 (`gramSchmidtFrame_orthonormal`, `contMDiffOn_gramSchmidtFrame`); that the span
is unchanged is `span_gramSchmidtNormed_range` followed by `span_gramSchmidt`, both of which
hold with no linear-independence hypothesis and in particular for `k = 0`. -/
theorem IsLocalSubframeOn.gramSchmidt (hs : IsLocalSubframeOn IB F n D s u) :
    IsOrthonormalSubframeOn IB F n D (gramSchmidtFrame s) u where
  contMDiffOn i := contMDiffOn_gramSchmidtFrame hs.toIsLocalIndepOn i
  orthonormal hx := gramSchmidtFrame_orthonormal hs.toIsLocalIndepOn hx
  span_eq {x} hx := by
    rw [← hs.span_eq hx]
    show span ℝ (range fun j => gramSchmidtNormed ℝ (s · x) j) = _
    rw [show (fun j => gramSchmidtNormed ℝ (s · x) j) = gramSchmidtNormed ℝ (s · x) from rfl]
    exact (span_gramSchmidtNormed_range (𝕜 := ℝ) (s · x)).trans (span_gramSchmidt (𝕜 := ℝ) (s · x))

/-! ### The fibre coordinates of a local `D`-frame

All three of `subframeSection`, `subframeCoord`, `subframeComb` are total: they are defined at
every `x : B`, with a junk value where `s` is not a `D`-basis.  This is what lets the
pretrivialization data below be written without reference to the frame's domain. -/

open scoped Classical in
/-- The `i`-th member of the frame `s`, read as an element of the fibre `D x` — junk `0` where
`s i x` does not lie in `D x`. -/
noncomputable def subframeSection (D : (x : B) → Submodule ℝ (V x)) (s : Fin k → (x : B) → V x)
    (i : Fin k) (x : B) : ↥(D x) :=
  if h : s i x ∈ D x then ⟨s i x, h⟩ else 0

omit [TopologicalSpace B] in
theorem subframeSection_of_mem {i : Fin k} (h : s i x ∈ D x) :
    subframeSection D s i x = ⟨s i x, h⟩ :=
  dif_pos h

omit [TopologicalSpace B] in
theorem coe_subframeSection_of_mem {i : Fin k} (h : s i x ∈ D x) :
    ((subframeSection D s i x : ↥(D x)) : V x) = s i x := by
  rw [subframeSection_of_mem h]

/-- The coordinates of a vector of `D x` in the frame `s`: the inner products `⟪s i x, v⟫`.

Linear in `v` at *every* `x` (`subframeCoord_add`, `subframeCoord_smul`) — no hypothesis on the
frame is needed for that, only for it to be a bijection. -/
noncomputable def subframeCoord (D : (x : B) → Submodule ℝ (V x)) (s : Fin k → (x : B) → V x)
    (x : B) (v : ↥(D x)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 fun i => ⟪s i x, (v : V x)⟫_ℝ

omit [TopologicalSpace B] in
@[simp]
theorem subframeCoord_apply (v : ↥(D x)) (i : Fin k) :
    subframeCoord D s x v i = ⟪s i x, (v : V x)⟫_ℝ := rfl

/-- The vector of `D x` with coordinates `c` in the frame `s`. -/
noncomputable def subframeComb (D : (x : B) → Submodule ℝ (V x)) (s : Fin k → (x : B) → V x)
    (x : B) (c : EuclideanSpace ℝ (Fin k)) : ↥(D x) :=
  ∑ i, c i • subframeSection D s i x

omit [TopologicalSpace B] in
theorem subframeCoord_add (v v' : ↥(D x)) :
    subframeCoord D s x (v + v') = subframeCoord D s x v + subframeCoord D s x v' := by
  ext i
  simp [subframeCoord, inner_add_right]

omit [TopologicalSpace B] in
theorem subframeCoord_smul (c : ℝ) (v : ↥(D x)) :
    subframeCoord D s x (c • v) = c • subframeCoord D s x v := by
  ext i
  simp [subframeCoord, inner_smul_right]

omit [TopologicalSpace B] in
theorem subframeCoord_sum {ι : Type*} (t' : Finset ι) (f : ι → ↥(D x)) :
    subframeCoord D s x (∑ i ∈ t', f i) = ∑ i ∈ t', subframeCoord D s x (f i) := by
  classical
  induction t' using Finset.induction_on with
  | empty => ext i; simp [subframeCoord]
  | insert a t' ha IH => rw [Finset.sum_insert ha, Finset.sum_insert ha, subframeCoord_add, IH]

/-! ### The fibre isomorphism supplied by an orthonormal `D`-frame -/

namespace IsOrthonormalSubframeOn

/-- The orthonormal basis of the fibre `D x` given by an orthonormal local `D`-frame. -/
noncomputable def basisAt (hs : IsOrthonormalSubframeOn IB F n D s u) (hx : x ∈ u) :
    OrthonormalBasis (Fin k) ℝ ↥(D x) :=
  OrthonormalBasis.mk (v := fun i => (⟨s i x, hs.mem hx i⟩ : ↥(D x)))
    ((hs.orthonormal hx).codRestrict (D x) fun i => hs.mem hx i)
    (by
      rw [top_le_iff, Submodule.span_range_subtype_eq_top_iff (D x) fun i => hs.mem hx i]
      exact hs.span_eq hx)

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
@[simp]
theorem basisAt_apply (hs : IsOrthonormalSubframeOn IB F n D s u) (hx : x ∈ u) (i : Fin k) :
    hs.basisAt hx i = (⟨s i x, hs.mem hx i⟩ : ↥(D x)) :=
  congrFun (OrthonormalBasis.coe_mk _ _) i

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
theorem basisAt_eq_subframeSection (hs : IsOrthonormalSubframeOn IB F n D s u) (hx : x ∈ u)
    (i : Fin k) : hs.basisAt hx i = subframeSection D s i x := by
  rw [basisAt_apply, subframeSection_of_mem (hs.mem hx i)]

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
/-- On the frame's domain the coordinate map is the coordinate *isometry* of the orthonormal
basis — this is `OrthonormalBasis.repr_apply_apply`, the statement that the coefficients of an
orthonormal expansion are the inner products. -/
theorem subframeCoord_eq_repr (hs : IsOrthonormalSubframeOn IB F n D s u) (hx : x ∈ u)
    (v : ↥(D x)) : subframeCoord D s x v = (hs.basisAt hx).repr v := by
  ext i
  rw [OrthonormalBasis.repr_apply_apply, subframeCoord_apply, hs.basisAt_apply hx i,
    Submodule.coe_inner]

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
theorem subframeComb_eq_repr_symm (hs : IsOrthonormalSubframeOn IB F n D s u) (hx : x ∈ u)
    (c : EuclideanSpace ℝ (Fin k)) : subframeComb D s x c = (hs.basisAt hx).repr.symm c := by
  rw [subframeComb, ← OrthonormalBasis.sum_repr_symm]
  exact Finset.sum_congr rfl fun i _ => by rw [hs.basisAt_eq_subframeSection hx i]

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
theorem subframeComb_subframeCoord (hs : IsOrthonormalSubframeOn IB F n D s u) (hx : x ∈ u)
    (v : ↥(D x)) : subframeComb D s x (subframeCoord D s x v) = v := by
  rw [hs.subframeComb_eq_repr_symm hx, hs.subframeCoord_eq_repr hx,
    LinearIsometryEquiv.symm_apply_apply]

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
theorem subframeCoord_subframeComb (hs : IsOrthonormalSubframeOn IB F n D s u) (hx : x ∈ u)
    (c : EuclideanSpace ℝ (Fin k)) : subframeCoord D s x (subframeComb D s x c) = c := by
  rw [hs.subframeComb_eq_repr_symm hx, hs.subframeCoord_eq_repr hx,
    LinearIsometryEquiv.apply_symm_apply]

end IsOrthonormalSubframeOn

/-! ### The pretrivialization attached to an orthonormal `D`-frame -/

/-- The pretrivialization of `D` determined by an orthonormal local `D`-frame on an open set:
over `u` it reads a vector of `D x` in the frame's coordinates. -/
noncomputable def subPretrivialization (hs : IsOrthonormalSubframeOn IB F n D s u) (hu : IsOpen u) :
    Pretrivialization (EuclideanSpace ℝ (Fin k))
      (π (EuclideanSpace ℝ (Fin k)) fun x => ↥(D x)) where
  toFun z := (z.proj, subframeCoord D s z.proj z.snd)
  invFun p := TotalSpace.mk p.1 (subframeComb D s p.1 p.2)
  source := π (EuclideanSpace ℝ (Fin k)) (fun x => ↥(D x)) ⁻¹' u
  target := u ×ˢ univ
  map_source' _ hz := ⟨hz, mem_univ _⟩
  map_target' _ hp := hp.1
  left_inv' := by
    rintro ⟨b, v⟩ hz
    exact congrArg (TotalSpace.mk b) (hs.subframeComb_subframeCoord hz v)
  right_inv' := by
    rintro ⟨b, c⟩ hp
    exact Prod.ext rfl (hs.subframeCoord_subframeComb hp.1 c)
  open_target := hu.prod isOpen_univ
  baseSet := u
  open_baseSet := hu
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
@[simp]
theorem subPretrivialization_apply (hs : IsOrthonormalSubframeOn IB F n D s u) (hu : IsOpen u)
    (b : B) (v : ↥(D b)) :
    subPretrivialization hs hu ⟨b, v⟩ = (b, subframeCoord D s b v) := rfl

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
@[simp]
theorem subPretrivialization_baseSet (hs : IsOrthonormalSubframeOn IB F n D s u) (hu : IsOpen u) :
    (subPretrivialization hs hu).baseSet = u := rfl

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
theorem subPretrivialization_symm (hs : IsOrthonormalSubframeOn IB F n D s u) (hu : IsOpen u)
    {b : B} (hb : b ∈ u) (c : EuclideanSpace ℝ (Fin k)) :
    (subPretrivialization hs hu).symm b c = subframeComb D s b c := by
  rw [Pretrivialization.symm_apply _ hb]
  rfl

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
/-- The pretrivializations are fibrewise linear — because the fibre coordinates are inner
products, which are linear in the vector at every point. -/
theorem subPretrivialization_isLinear (hs : IsOrthonormalSubframeOn IB F n D s u) (hu : IsOpen u) :
    (subPretrivialization hs hu).IsLinear ℝ where
  linear _ _ :=
    { map_add := fun v v' => subframeCoord_add v v'
      map_smul := fun c v => subframeCoord_smul c v }

/-! ### The coordinate change is the Gram matrix -/

/-- The coordinate change from the frame `s` to the frame `t`: the Gram matrix
`⟪t j b, s i b⟫`, written as a finite sum of scalar multiples of *constant* continuous linear
maps so that its smoothness is the smoothness of its entries. -/
noncomputable def gramCoordChange (s t : Fin k → (x : B) → V x) (b : B) : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  ∑ i, ∑ j, ⟪t j b, s i b⟫_ℝ •
    (EuclideanSpace.proj i).smulRight (EuclideanSpace.single j (1 : ℝ))

/-- A finite sum in `EuclideanSpace` is computed coordinatewise.  Needed because `WithLp` is a
structure in this mathlib pin, so `(∑ i, g i) l` is not syntactically `∑ i, g i l`. -/
theorem euclideanSpace_sum_apply {ι : Type*} (t' : Finset ι) (g : ι → EuclideanSpace ℝ (Fin k))
    (l : Fin k) : (∑ i ∈ t', g i) l = ∑ i ∈ t', g i l := by
  change WithLp.ofLp (∑ i ∈ t', g i) l = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

omit [TopologicalSpace B] in
theorem gramCoordChange_apply (b : B) (c : EuclideanSpace ℝ (Fin k)) (l : Fin k) :
    gramCoordChange s t b c l = ∑ i, c i * ⟪t l b, s i b⟫_ℝ := by
  classical
  rw [gramCoordChange, ContinuousLinearMap.sum_apply, euclideanSpace_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.sum_apply, euclideanSpace_sum_apply, Finset.sum_eq_single l]
  · simp [mul_comm]
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ l) h

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
/-- The Gram matrix really is the coordinate change: reading the `s`-combination with coordinates
`c` in the frame `t` gives `Gram · c`.  Only linearity of the coordinate map is used, so this
holds at every point of the frames' common domain. -/
theorem gramCoordChange_eq (hs : IsOrthonormalSubframeOn IB F n D s u) {b : B} (hb : b ∈ u)
    (c : EuclideanSpace ℝ (Fin k)) :
    gramCoordChange s t b c = subframeCoord D t b (subframeComb D s b c) := by
  ext l
  rw [gramCoordChange_apply, subframeComb, subframeCoord_sum, euclideanSpace_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [subframeCoord_smul]
  show c i * ⟪t l b, s i b⟫_ℝ = c i * subframeCoord D t b (subframeSection D s i b) l
  rw [subframeCoord_apply, coe_subframeSection_of_mem (hs.mem hb i)]

/-- **Smoothness of the coordinate change** — the analytic heart of the construction, and the
reason for normalizing the frames.  Each Gram entry `b ↦ ⟪t j b, s i b⟫` is smooth by
`ContMDiffOn.inner_bundle`, and the coordinate change is a finite sum of such scalars times
constant continuous linear maps. -/
theorem contMDiffOn_gramCoordChange (hs : IsOrthonormalSubframeOn IB F n D s u)
    (ht : IsOrthonormalSubframeOn IB F n D t w) :
    ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) n
      (gramCoordChange s t) (u ∩ w) := by
  refine contMDiffOn_finset_sum _ fun i _ => contMDiffOn_finset_sum _ fun j _ => ?_
  exact ContMDiffOn.smul
    (((ht.contMDiffOn j).mono inter_subset_right).inner_bundle
      ((hs.contMDiffOn i).mono inter_subset_left))
    contMDiffOn_const

/-! ### The prebundle -/

variable (IB F n D) in
/-- The atlas: every pretrivialization of `D` coming from an orthonormal local `D`-frame on an
open set. -/
def subAtlas : Set (Pretrivialization (EuclideanSpace ℝ (Fin k))
    (π (EuclideanSpace ℝ (Fin k)) fun x => ↥(D x))) :=
  {e | ∃ (u : Set B) (s : Fin k → (x : B) → V x) (hu : IsOpen u)
        (hs : IsOrthonormalSubframeOn IB F n D s u), e = subPretrivialization hs hu}

variable (IB F n k D) in
/-- **The hypothesis of Lemma A.34**: every point has a neighbourhood on which `D` is spanned by
`k` smooth sections of the ambient bundle.

A structure rather than a plain `def ... : Prop` so that the chosen-frame API below is available
through dot notation. -/
structure HasLocalSubframes : Prop where
  exists_subframe (p : B) : ∃ (u : Set B) (s : Fin k → (x : B) → V x),
    IsOpen u ∧ p ∈ u ∧ IsLocalSubframeOn IB F n D s u

namespace HasLocalSubframes

/-- Lee's hypothesis, with the frames normalized: Gram-Schmidt does not move the spans. -/
theorem orthonormal (h : HasLocalSubframes IB F n k D) (p : B) :
    ∃ (u : Set B) (s : Fin k → (x : B) → V x),
      IsOpen u ∧ p ∈ u ∧ IsOrthonormalSubframeOn IB F n D s u := by
  obtain ⟨u, s, hu, hp, hs⟩ := h.exists_subframe p
  exact ⟨u, gramSchmidtFrame s, hu, hp, hs.gramSchmidt⟩

/-- The domain of a chosen orthonormal local `D`-frame around `p`. -/
noncomputable def dom (h : HasLocalSubframes IB F n k D) (p : B) : Set B :=
  (h.orthonormal p).choose

/-- A chosen orthonormal local `D`-frame around `p`. -/
noncomputable def frame (h : HasLocalSubframes IB F n k D) (p : B) : Fin k → (x : B) → V x :=
  (h.orthonormal p).choose_spec.choose

theorem isOpen_dom (h : HasLocalSubframes IB F n k D) (p : B) : IsOpen (h.dom p) :=
  (h.orthonormal p).choose_spec.choose_spec.1

theorem mem_dom (h : HasLocalSubframes IB F n k D) (p : B) : p ∈ h.dom p :=
  (h.orthonormal p).choose_spec.choose_spec.2.1

theorem frame_spec (h : HasLocalSubframes IB F n k D) (p : B) :
    IsOrthonormalSubframeOn IB F n D (h.frame p) (h.dom p) :=
  (h.orthonormal p).choose_spec.choose_spec.2.2

end HasLocalSubframes

/-- The pretrivialization of `D` around `p` given by a chosen orthonormal local `D`-frame. -/
noncomputable def subPretrivializationAt (h : HasLocalSubframes IB F n k D) (p : B) :
    Pretrivialization (EuclideanSpace ℝ (Fin k))
      (π (EuclideanSpace ℝ (Fin k)) fun x => ↥(D x)) :=
  subPretrivialization (h.frame_spec p) (h.isOpen_dom p)

/-- **The fibre topologies are compatible** — the last `VectorPrebundle` field.  Over its own
point the pretrivialization is `v ↦ (b, repr v)` with `repr` the coordinate isometry of an
orthonormal basis, hence a homeomorphism; this is exactly why the model fibre is
`EuclideanSpace ℝ (Fin k)` rather than `Fin k → ℝ`. -/
theorem isInducing_subPretrivializationAt (h : HasLocalSubframes IB F n k D) (b : B) :
    IsInducing (subPretrivializationAt h b ∘ TotalSpace.mk b) := by
  have hb : b ∈ h.dom b := h.mem_dom b
  have key : (subPretrivializationAt h b ∘ TotalSpace.mk b)
      = Prod.mk b ∘ ((h.frame_spec b).basisAt hb).repr := by
    funext v
    exact Prod.ext rfl ((h.frame_spec b).subframeCoord_eq_repr hb v)
  rw [key]
  exact (isInducing_prodMkRight b).comp
    ((h.frame_spec b).basisAt hb).repr.toHomeomorph.isInducing

/-- **Lemma A.34, the construction.**  The vector prebundle of the family of subspaces `D`. -/
noncomputable def subVectorPrebundle (h : HasLocalSubframes IB F n k D) :
    VectorPrebundle ℝ (EuclideanSpace ℝ (Fin k)) (fun x => ↥(D x)) where
  pretrivializationAtlas := subAtlas IB F n D
  pretrivialization_linear' := by
    rintro e ⟨u, s, hu, hs, rfl⟩
    exact subPretrivialization_isLinear hs hu
  pretrivializationAt := subPretrivializationAt h
  mem_base_pretrivializationAt p := h.mem_dom p
  pretrivialization_mem_atlas p :=
    ⟨h.dom p, h.frame p, h.isOpen_dom p, h.frame_spec p, rfl⟩
  exists_coordChange := by
    rintro e ⟨u, s, hu, hs, rfl⟩ e' ⟨w, t, hw, ht, rfl⟩
    refine ⟨gramCoordChange s t, (contMDiffOn_gramCoordChange hs ht).continuousOn, ?_⟩
    rintro b hb v
    rw [subPretrivialization_symm hs hu hb.1, subPretrivialization_apply,
      gramCoordChange_eq hs hb.1]
  totalSpaceMk_isInducing := isInducing_subPretrivializationAt h

@[simp]
theorem subVectorPrebundle_pretrivializationAtlas (h : HasLocalSubframes IB F n k D) :
    (subVectorPrebundle h).pretrivializationAtlas = subAtlas IB F n D := rfl

/-- **The coordinate changes are smooth** — the `IsContMDiff` mixin, supplied by the Gram
matrix. -/
theorem subVectorPrebundle_isContMDiff (h : HasLocalSubframes IB F n k D) :
    (subVectorPrebundle h).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    intro e he e' he'
    rw [subVectorPrebundle_pretrivializationAtlas] at he he'
    obtain ⟨u, s, hu, hs, rfl⟩ := he
    obtain ⟨w, t, hw, ht, rfl⟩ := he'
    refine ⟨gramCoordChange s t, contMDiffOn_gramCoordChange hs ht, ?_⟩
    rintro b hb v
    rw [subPretrivialization_symm hs hu hb.1, subPretrivialization_apply,
      gramCoordChange_eq hs hb.1]

/-! ### Lemma A.34 -/

/-- The topology on the total space of `D` produced by Lemma A.34.

Deliberately **not** an `instance`: its head would be
`TopologicalSpace (TotalSpace _ fun x => ↥(D x))` for a *variable* family `D`, so it would fire
on every goal of that shape.  Consumers `letI` it — the idiom mathlib itself uses inside
`VectorPrebundle.toVectorBundle`.  Same for the three below. -/
@[implicit_reducible]
noncomputable def subTotalSpaceTopology (h : HasLocalSubframes IB F n k D) :
    TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin k)) fun x => ↥(D x)) :=
  (subVectorPrebundle h).totalSpaceTopology

/-- `D` is a fibre bundle of rank `k` over `B`. -/
@[implicit_reducible]
noncomputable def subFiberBundle (h : HasLocalSubframes IB F n k D) :
    letI := subTotalSpaceTopology h
    FiberBundle (EuclideanSpace ℝ (Fin k)) (fun x => ↥(D x)) :=
  (subVectorPrebundle h).toFiberBundle

/-- `D` is a vector bundle: the fibrewise linear structure of the subspaces `D x` is the one the
bundle sees. -/
theorem subVectorBundle (h : HasLocalSubframes IB F n k D) :
    letI := subTotalSpaceTopology h
    letI := subFiberBundle h
    VectorBundle ℝ (EuclideanSpace ℝ (Fin k)) (fun x => ↥(D x)) :=
  (subVectorPrebundle h).toVectorBundle

/-- **Lee's Lemma A.34: the local frame criterion for subbundles** (Riemannian form).

Let `V → B` be a `C^n` Riemannian vector bundle and, for each `x : B`, let `D x ⊆ V x` be a
`k`-dimensional subspace of the fibre.  If every point of `B` has a neighbourhood on which `D`
is spanned by `k` smooth sections of `V` — `HasLocalSubframes` — then `D` is itself a `C^n`
rank-`k` vector bundle over `B`, i.e. a smooth subbundle of `V`.

The conclusion is spelled out as the bundle structure because mathlib has no notion of a smooth
vector subbundle to assert membership in.  The topology, the `FiberBundle` and the
`VectorBundle` structures are `subTotalSpaceTopology`, `subFiberBundle`, `subVectorBundle`; this
is the remaining `C^n` statement about them.

Departure from Lee: he proves this for a bare smooth vector bundle, whereas we assume `V` is
Riemannian and normalize the frames.  See the file header for why, and why it costs nothing at
the point of use (Proposition 2.16). -/
theorem subContMDiffVectorBundle (h : HasLocalSubframes IB F n k D) :
    letI := subTotalSpaceTopology h
    letI := subFiberBundle h
    letI := subVectorBundle h
    ContMDiffVectorBundle n (EuclideanSpace ℝ (Fin k)) (fun x => ↥(D x)) IB :=
  letI := subVectorPrebundle_isContMDiff h
  (subVectorPrebundle h).contMDiffVectorBundle IB

end Subbundle

end LeeLib.AppendixA
