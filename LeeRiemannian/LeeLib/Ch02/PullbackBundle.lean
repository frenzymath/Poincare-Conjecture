/-
Chapter 2, "Riemannian Metrics", §3 "Methods for Constructing Riemannian
Metrics": the ambient tangent bundle restricted to a submanifold.

Lee's Proposition 2.16 is a statement about the bundle he writes `T M̃|_M`: for a
submanifold `M ⊆ M̃`, the ambient tangent bundle restricted to `M`, whose fibre
at `p ∈ M` is the *ambient* tangent space `T_p M̃` rather than `T_p M`.  This is
the bundle in which the splitting

  `T_p M̃ = T_p M ⊕ N_p M`

lives, and it is where the tangential and normal projections `π^⊤`, `π^⊥` are
defined.

In the formalization a submanifold is presented, as everywhere else in this
chapter, by a smooth immersion `F : M → M̃` (Lee's Lemma 2.11 and
`LeeLib.Ch02.pullbackMetric`).  Under that presentation `T M̃|_M` is exactly the
**pullback bundle** `F *ᵖ T M̃`, whose fibre at `p` is `T_{F p} M̃` — mathlib's
`Bundle.Pullback`, which is already a `ContMDiffVectorBundle`
(`ContMDiffVectorBundle.pullback`).

What is missing upstream, and what this file supplies, is that `T M̃|_M` is a
*Riemannian* bundle: the ambient metric `g̃` restricts to an inner product on each
fibre `T_{F p} M̃`, and does so smoothly in `p`.  That is
`ContMDiffRiemannianMetric.pullback`.  Fibrewise there is nothing to prove —
`(f *ᵖ E) p` is by definition `E (f p)`, so the inner product is literally the
ambient one — and the content is the smooth dependence on `p`: the ambient metric
read in a trivialization of `f *ᵖ E` at `p₀` is the ambient metric read in a
trivialization of `E` at `f p₀`, precomposed with `f`, a composite of smooth maps.

## How the fibrewise inner product is installed, and why it is done this way

The naive route — declaring `NormedAddCommGroup ((f *ᵖ E) x)` and
`InnerProductSpace ℝ ((f *ᵖ E) x)` directly, by transfer from `E (f x)` — is the
one mathlib explicitly warns against (`Bundle.RiemannianMetric.toCore`: "Do not
use this `Core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm
instance").  It was tried here and it does not work, for a reason worth recording
because it is invisible until the two halves are needed at once:

* `InnerProductSpace ℝ V` extends `NormedSpace ℝ V` and hence *carries* a
  `Module ℝ V`.  A transferred `InnerProductSpace ℝ ((f *ᵖ E) x)` therefore gives
  `Module ℝ ((f *ᵖ E) x)` a second path, alongside mathlib's `instModulePullback`.
* Nothing goes wrong until a `RiemannianBundle` is installed on the *ambient*
  bundle — which for `T M̃` is the only way to have a metric at all.  From that
  point `Module ℝ ((f *ᵖ E) x)` resolves through the transferred inner product,
  while `VectorBundle.pullback` supplies `VectorBundle ℝ F (f *ᵖ E)` over
  `instModulePullback`; the two are definitionally equal but not syntactically,
  so `VectorBundle ℝ F (f *ᵖ E)` stops synthesizing and Gram-Schmidt can no
  longer be run in the ambient fibres.  (Absent a `RiemannianBundle` it
  synthesizes fine, which is why the defect hid for so long.)

The fix is mathlib's own: `RiemannianBundle` takes the *existing* `Module` as an
input and builds the norm and inner product on top of it, so the `Module` reduct
of the resulting `InnerProductSpace` is the one it started from and no second
path is created.  Using it requires the pre-normed fibre structures that
`Bundle.RiemannianMetric` asks for — `TopologicalSpace`, `AddCommGroup`,
`Module`, `IsTopologicalAddGroup`, `ContinuousConstSMul` — and mathlib supplies
only the first and the third for a pullback.  The other three are added below.

`AddCommGroup` is the delicate one.  Adding it makes `AddCommMonoid ((f *ᵖ E) x)`
reachable two ways (mathlib's `instAddCommMonoidPullback`, and via the new
`AddCommGroup`), and `Bundle.RiemannianMetric` binds `AddCommGroup` *before*
`Module`, so it demands a `Module` over the `AddCommMonoid` reduct of the
`AddCommGroup` — which `instModulePullback`, sitting over
`instAddCommMonoidPullback`, does not provide.  Rather than leave two towers that
differ by a beta-reduction and hope typeclass resolution picks consistently, this
file retires mathlib's per-point pair and rebuilds a single coherent tower on top
of `Pullback.addCommGroup`.  Every pullback bundle in this development is
Riemannian, so its fibres are always groups and nothing is lost; the erasure is
persistent to modules importing this one, which is the reason it is called out
here rather than buried.

Two further implementation notes, both forced by upstream:

* `FiberBundle.pullback` and `VectorBundle.pullback` are keyed on a bundled map
  `f : K` for an arbitrary `[FunLike K B' B] [ContinuousMapClass K B' B]`.  That
  pattern does not unify when the bundle instances are sought as *arguments* of
  another class, so `ContMDiffMap`-specialized copies are declared below.
* `symm_pullback` needs `cast_heq`: trivializing `f *ᵖ E` over `x` and
  trivializing `E` over `f x` are the same operation, but `Trivialization.symm`
  carries a cast between `(f *ᵖ E) x` and `E (f x)`.

Everything is stated for a general Riemannian vector bundle `E → B` pulled back
along a smooth map `f : B' → B`, not just for `T M̃` and an immersion: nothing in
the argument uses either, and the extra generality costs nothing.
-/
import LeeLib.Ch02.OrthonormalFrame
import LeeLib.Ch02.PseudoRiemannianMetric
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

namespace LeeLib.Ch02

open Bundle Manifold
open scoped Manifold ContDiff Topology

/-! ### Fibrewise structure on a pullback bundle

`(f *ᵖ E) x` is by definition `E (f x)`, so every fibrewise structure transfers.
mathlib declares `TopologicalSpace`, `AddCommMonoid` and `Module` this way; the
remaining three that `Bundle.RiemannianMetric` requires are added here.

The `AddCommMonoid` and `Module` instances are rebuilt rather than reused: see
the file header.  Retiring them is what keeps a single tower over each fibre. -/

attribute [-instance] instAddCommMonoidPullback instModulePullback

section Fibre

variable {B B' : Type*} {E : B → Type*} {f : B' → B}

/-- The fibres of a pullback bundle inherit the additive group of the fibres they
are copies of: `(f *ᵖ E) x` is `E (f x)`.

mathlib stops at `AddCommMonoid`, but `Bundle.RiemannianMetric` — the diamond-free
way to put an inner product on the fibres — needs a group. -/
instance Pullback.addCommGroup [i : ∀ x : B, AddCommGroup (E x)] (x : B') :
    AddCommGroup ((f *ᵖ E) x) := i _

/-- The fibres of a pullback bundle inherit the module structure of the fibres
they are copies of.

This replaces mathlib's `instModulePullback`, and differs from it only in being
stated over the `AddCommMonoid` reduct of `Pullback.addCommGroup` instead of over
`instAddCommMonoidPullback`.  The pinning is not cosmetic: `Bundle.RiemannianMetric`
binds `AddCommGroup` before `Module` and so asks for exactly this form. -/
instance Pullback.module {R : Type*} [Semiring R] [∀ x : B, AddCommGroup (E x)]
    [i : ∀ x : B, Module R (E x)] (x : B') :
    @Module R ((f *ᵖ E) x) _ (@AddCommGroup.toAddCommMonoid _ (Pullback.addCommGroup (f := f) x)) :=
  i _

/-- Addition on a pullback fibre is continuous, being the addition of `E (f x)`. -/
instance Pullback.isTopologicalAddGroup [∀ x : B, TopologicalSpace (E x)]
    [∀ x : B, AddCommGroup (E x)] [i : ∀ x : B, IsTopologicalAddGroup (E x)] (x : B') :
    IsTopologicalAddGroup ((f *ᵖ E) x) := i _

/-- Scalar multiplication on a pullback fibre is continuous, being that of `E (f x)`. -/
instance Pullback.continuousConstSMul {R : Type*} [Semiring R]
    [∀ x : B, TopologicalSpace (E x)] [∀ x : B, AddCommGroup (E x)] [∀ x : B, Module R (E x)]
    [i : ∀ x : B, ContinuousConstSMul R (E x)] (x : B') :
    ContinuousConstSMul R ((f *ᵖ E) x) := i _

/-- Scalar multiplication on a pullback fibre is jointly continuous, being that of `E (f x)`.

`Pullback.continuousConstSMul` is the weaker separate-continuity used by
`Bundle.RiemannianMetric`; the indefinite frame machinery of
`LeeLib.Ch02.PseudoOrthonormalFrame` asks for this joint form instead, so both are supplied. -/
instance Pullback.continuousSMul {R : Type*} [Semiring R] [TopologicalSpace R]
    [∀ x : B, TopologicalSpace (E x)] [∀ x : B, AddCommGroup (E x)] [∀ x : B, Module R (E x)]
    [i : ∀ x : B, ContinuousSMul R (E x)] (x : B') :
    ContinuousSMul R ((f *ᵖ E) x) := i _

end Fibre

section Pullback

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

/-- `FiberBundle.pullback`, specialized to a `ContMDiffMap`.

mathlib's instance is keyed on an arbitrary bundled-map class `K`, whose
conclusion `FiberBundle F (⇑?f *ᵖ ?E)` does not unify when the instance is
sought as an argument of another class.  This copy has `C^n⟮IB', B'; IB, B⟯` as
a rigid head and therefore does. -/
noncomputable instance ContMDiffMap.fiberBundlePullback (f : C^n⟮IB', B'; IB, B⟯) :
    FiberBundle F ((f : B' → B) *ᵖ E) :=
  FiberBundle.pullback (F := F) (E := E) f

/-- A pulled-back trivialization is linear.

mathlib's `Bundle.Trivialization.pullback_linear` says exactly this, but is stated
over the retired tower; the proof is its proof. -/
instance Pullback.trivialization_isLinear (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (f : C^n⟮IB', B'; IB, B⟯) : (e.pullback (B' := B') f).IsLinear ℝ where
  linear _ h := e.linear ℝ h

/-- `VectorBundle.pullback`, specialized to a `ContMDiffMap`; see
`ContMDiffMap.fiberBundlePullback`.

The definitional content is nil, but the *statement* matters: its `Module` is the
one from `Pullback.module`, so this is the `VectorBundle` instance that
`Bundle.RiemannianMetric (f *ᵖ E)` and `Bundle.ContMDiffRiemannianMetric` ask for.
mathlib's `VectorBundle.pullback` is stated over its own tower and is accepted
here only up to unfolding. -/
instance ContMDiffMap.vectorBundlePullback (f : C^n⟮IB', B'; IB, B⟯) :
    VectorBundle ℝ F ((f : B' → B) *ᵖ E) :=
  VectorBundle.pullback ℝ (F := F) (E := E) f

/-- `ContMDiffVectorBundle.pullback` over the tower of `Pullback.module`.

mathlib's instance is already keyed on a `ContMDiffMap`, but is stated over its own retired
tower, so it no longer matches the goals arising here; its content is reused verbatim. -/
noncomputable instance ContMDiffMap.contMDiffVectorBundlePullback [ContMDiffVectorBundle n F E IB]
    (f : C^n⟮IB', B'; IB, B⟯) : ContMDiffVectorBundle n F ((f : B' → B) *ᵖ E) IB' :=
  ContMDiffVectorBundle.pullback (𝕜 := ℝ) F E IB' f

variable (f : C^n⟮IB', B'; IB, B⟯)

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [VectorBundle ℝ F E] in
/-- The trivialization of `f *ᵖ E` at `x₀` is the pullback of the trivialization
of `E` at `f x₀`.  True by definition, but worth naming: it is the only fact
about the pullback bundle's smooth structure the file uses. -/
theorem trivializationAt_pullback (x₀ : B') :
    trivializationAt F ((f : B' → B) *ᵖ E) x₀ = (trivializationAt F E (f x₀)).pullback f :=
  rfl

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] in
/-- Trivializing `f *ᵖ E` over `x` and trivializing `E` over `f x` are the same
operation: both send `v : F` into the single fibre `E (f x)`.  The two sides are
not definitionally equal only because `Trivialization.symm` carries a cast
between `(f *ᵖ E) x` and `E (f x)`. -/
theorem symm_pullback (e : Trivialization F (π F E)) (x : B') (v : F) :
    (e.pullback (B' := B') f).symm x v = e.symm (f x) v := by
  by_cases hx : f x ∈ e.baseSet
  · rw [Trivialization.symm_apply _ (show x ∈ (e.pullback (B' := B') f).baseSet from hx)]
    exact eq_of_heq (cast_heq _ _)
  · rw [Trivialization.symm_apply_of_notMem _
      (show x ∉ (e.pullback (B' := B') f).baseSet from hx),
      Trivialization.symm_apply_of_notMem _ hx]

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [VectorBundle ℝ F E] in
/-- `symm_pullback`, as an equality of continuous linear maps. -/
theorem symmL_pullback (e : Trivialization F (π F E)) [e.IsLinear ℝ] (x : B') :
    (e.pullback (B' := B') f).symmL ℝ x = e.symmL ℝ (f x) :=
  ContinuousLinearMap.ext fun v => symm_pullback f e x v

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [VectorBundle ℝ F E] in
/-- The dual of `symmL_pullback`; here the two sides are definitionally equal,
because no cast intervenes on the way out of the fibre. -/
theorem continuousLinearMapAt_pullback (e : Trivialization F (π F E)) [e.IsLinear ℝ] (x : B') :
    (e.pullback (B' := B') f).continuousLinearMapAt ℝ x = e.continuousLinearMapAt ℝ (f x) :=
  rfl

/-- **The ambient metric makes `T M̃|_M` a Riemannian bundle** (Lee, §2.3): if `g`
is a smooth Riemannian metric on a vector bundle `E → B` and `f : B' → B` is
smooth, then `f *ᵖ E` carries the pulled-back metric `(f^* g)_x = g_{f x}`, again
smooth.

Fibrewise there is nothing to do: `(f *ᵖ E) x` *is* `E (f x)`, so `g (f x)` is
already a bilinear form on it, and symmetry, positive definiteness and
boundedness are those of `g` at `f x` verbatim.  The content is that the form
still varies smoothly with `x ∈ B'`: read in a trivialization of `f *ᵖ E` at
`x₀`, it is the metric of `E` read in the trivialization at `f x₀` and
precomposed with `f`, hence smooth as a composite.

Installing this as `RiemannianBundle (f *ᵖ E) := ⟨(g.pullback f).toRiemannianMetric⟩`
puts the inner product on the fibres and, by mathlib's own instance, an
`IsContMDiffRiemannianBundle IB' n F (f *ᵖ E)` alongside it — which is what lets
`LeeLib.Ch02.gramSchmidtFrame` run inside the ambient fibres.

When `f` is the inclusion of a submanifold `M ⊆ M̃`, this bundle is the *ambient
tangent bundle along `M`*, written `T M̃|_M`: the bundle in which the splitting
`T_p M̃ = T_p M ⊕ N_p M` and the projections `π^⊤`, `π^⊥` of Lee's Proposition
2.16 live. -/
noncomputable def _root_.Bundle.ContMDiffRiemannianMetric.pullback
    (g : ContMDiffRiemannianMetric IB n F E) (f : C^n⟮IB', B'; IB, B⟯) :
    ContMDiffRiemannianMetric IB' n F ((f : B' → B) *ᵖ E) where
  inner x := g.inner (f x)
  symm x v w := g.symm (f x) v w
  pos x v hv := g.pos (f x) v hv
  isVonNBounded x := g.isVonNBounded (f x)
  contMDiff := by
    intro x₀
    -- the ambient metric, read in a trivialization at `f x₀`, is smooth
    have hbase := ((contMDiffAt_hom_bundle (IB := IB) (n := n) (F₁ := F) (E₁ := E)
      (F₂ := F →L[ℝ] ℝ) (E₂ := fun b => E b →L[ℝ] ℝ)
      (fun b => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g.inner b)) (x₀ := f x₀)).1
        (g.contMDiff (f x₀))).2
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    -- ... and precomposing with `f` keeps it smooth.  It remains to see that the
    -- composite is the metric of `f *ᵖ E` read in a trivialization at `x₀` — which
    -- it is, on the neighbourhood of `x₀` where `f x` stays in the base set of the
    -- trivialization of `E` at `f x₀`.
    refine (hbase.comp x₀ f.contMDiff.contMDiffAt).congr_of_eventuallyEq ?_
    have hU : {x : B' | f x ∈ (trivializationAt F E (f x₀)).baseSet} ∈ 𝓝 x₀ :=
      f.contMDiff.continuous.continuousAt
        ((trivializationAt F E (f x₀)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt F E (f x₀)))
    filter_upwards [hU] with x hx
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
    -- the base set of `trivializationAt F (f *ᵖ E) x₀` is `f ⁻¹'` the base set at `f x₀`
    have hxp : x ∈ (trivializationAt F ((f : B' → B) *ᵖ E) x₀).baseSet := hx
    have htrivB' : trivializationAt ℝ (Bundle.Trivial B' ℝ) x₀ = Bundle.Trivial.trivialization B' ℝ :=
      Bundle.Trivial.eq_trivialization B' ℝ _
    have htrivB : trivializationAt ℝ (Bundle.Trivial B ℝ) (f x₀)
        = Bundle.Trivial.trivialization B ℝ :=
      Bundle.Trivial.eq_trivialization B ℝ _
    -- read both sides through `inCoordinates_apply_eq₂`: the `ℝ` factor is a trivial
    -- bundle on both sides, so `linearMapAt` there is the identity, and what is left
    -- is `symm_pullback`.
    rw [_root_.inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial B' ℝ) hxp hxp (by simp)]
    show _ = ContinuousLinearMap.inCoordinates F E (F →L[ℝ] ℝ) (fun b => E b →L[ℝ] ℝ)
        (f x₀) (f x) (f x₀) (f x) (g.inner (f x)) a b
    rw [_root_.inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial B ℝ) hx hx (by simp)]
    simp only [htrivB', htrivB, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
      trivializationAt_pullback, symm_pullback]
    rfl

@[simp] theorem _root_.Bundle.ContMDiffRiemannianMetric.pullback_inner
    (g : ContMDiffRiemannianMetric IB n F E) (f : C^n⟮IB', B'; IB, B⟯) (x : B') :
    (g.pullback f).inner x = g.inner (f x) := rfl

/-- **The ambient pseudo-metric makes `T M̃|_M` a bundle of scalar product spaces**
(Lee, §"Pseudo-Riemannian Submanifolds"): the indefinite counterpart of
`Bundle.ContMDiffRiemannianMetric.pullback`.

The two proofs are the same because the two structures differ only in which fibrewise
condition they carry — positive definiteness against nondegeneracy — and *both* transfer
verbatim, the fibre `(f *ᵖ E) x` simply *being* `E (f x)`.  The smoothness field is literally
the same statement in both structures, so its proof is reproduced unchanged.

This is what lets Lee's Proposition 2.72 run Gram-Schmidt in the ambient fibres along `M`.
Unlike the Riemannian case there is no `RiemannianBundle` instance to install — an indefinite
form induces no `InnerProductSpace` — so the metric is passed explicitly instead. -/
noncomputable def _root_.Bundle.ContMDiffPseudoMetric.pullback
    (g : ContMDiffPseudoMetric IB n F E) (f : C^n⟮IB', B'; IB, B⟯) :
    ContMDiffPseudoMetric IB' n F ((f : B' → B) *ᵖ E) where
  form x := g.form (f x)
  symm x v w := g.symm (f x) v w
  nondegenerate x v hv := g.nondegenerate (f x) v hv
  contMDiff := by
    intro x₀
    have hbase := ((contMDiffAt_hom_bundle (IB := IB) (n := n) (F₁ := F) (E₁ := E)
      (F₂ := F →L[ℝ] ℝ) (E₂ := fun b => E b →L[ℝ] ℝ)
      (fun b => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (g.form b)) (x₀ := f x₀)).1
        (g.contMDiff (f x₀))).2
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    refine (hbase.comp x₀ f.contMDiff.contMDiffAt).congr_of_eventuallyEq ?_
    have hU : {x : B' | f x ∈ (trivializationAt F E (f x₀)).baseSet} ∈ 𝓝 x₀ :=
      f.contMDiff.continuous.continuousAt
        ((trivializationAt F E (f x₀)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt F E (f x₀)))
    filter_upwards [hU] with x hx
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
    have hxp : x ∈ (trivializationAt F ((f : B' → B) *ᵖ E) x₀).baseSet := hx
    have htrivB' : trivializationAt ℝ (Bundle.Trivial B' ℝ) x₀ = Bundle.Trivial.trivialization B' ℝ :=
      Bundle.Trivial.eq_trivialization B' ℝ _
    have htrivB : trivializationAt ℝ (Bundle.Trivial B ℝ) (f x₀)
        = Bundle.Trivial.trivialization B ℝ :=
      Bundle.Trivial.eq_trivialization B ℝ _
    rw [_root_.inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial B' ℝ) hxp hxp (by simp)]
    show _ = ContinuousLinearMap.inCoordinates F E (F →L[ℝ] ℝ) (fun b => E b →L[ℝ] ℝ)
        (f x₀) (f x) (f x₀) (f x) (g.form (f x)) a b
    rw [_root_.inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial B ℝ) hx hx (by simp)]
    simp only [htrivB', htrivB, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
      trivializationAt_pullback, symm_pullback]
    rfl

@[simp] theorem _root_.Bundle.ContMDiffPseudoMetric.pullback_form
    (g : ContMDiffPseudoMetric IB n F E) (f : C^n⟮IB', B'; IB, B⟯) (x : B') :
    (g.pullback f).form x = g.form (f x) := rfl

@[simp] theorem _root_.Bundle.ContMDiffPseudoMetric.pullback_bilin
    (g : ContMDiffPseudoMetric IB n F E) (f : C^n⟮IB', B'; IB, B⟯) (x : B') :
    (g.pullback f).bilin x = g.bilin (f x) := rfl

end Pullback

end LeeLib.Ch02
