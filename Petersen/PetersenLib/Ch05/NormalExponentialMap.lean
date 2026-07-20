import PetersenLib.Ch05.IsometryUniqueness

/-!
# Petersen Ch. 5, §5.5 — the normal exponential map of a submanifold

`def:pet-ch5-normal-exponential-map` (Petersen pp. 206–207): for a submanifold
`N ⊆ M` with normal bundle `T^⊥N = {v ∈ T_pM | p ∈ N, v ⟂ T_pN}`, the **normal
exponential map** `exp^⊥ : O ∩ T^⊥N → M` is the restriction of `exp` to `T^⊥N`.

## The layer

The submanifold is presented, as everywhere else in this development, by a smooth
map `F : N → M` out of an abstract manifold `N` (an immersion / embedding when one
wants `F` to present a genuine submanifold), *not* as a subtype of `M`.  The
"tangent space of the submanifold" at `q` is then the image `T_qN = DF_q(T_qN)`
(`tangentSpaceImage`), a submodule of `T_{F q}M`, and

* `normalSpace g F q : Submodule ℝ (T_{F q}M)` is its `g`-orthogonal complement,
* `normalBundle g F : Set (TangentBundle I M)` collects these fibres,
* `normalExpDomain g F = normalBundle g F ∩ intrinsicExpDomain g` is `O ∩ T^⊥N`,
* `normalExpMap g F = (normalExpDomain g F).restrict (intrinsicExpMap g)`

so that `exp^⊥` *is*, definitionally, the restriction of `exp` to the normal
bundle (`normalExpMap_eq_intrinsicExpMap`, an `rfl`).

## The exponential map used

`exp` here is the **intrinsic** moving-foot exponential — `intrinsicExpMap g v =
geodesicMaximalCurve g v.proj v.2 1`, defined exactly on `intrinsicExpDomain g`,
where time `1` lies in the maximal existence domain of the geodesic with initial
datum `v`.  It is *never* `PetersenLib.expMap` / `PetersenLib.expDomain`, whose
chart-anchored domain is an artifact of the single chart at the base point (see
`rem:pet-ch5-injectivity-radius-chart-artifact`): a statement about `exp^⊥`
quantified over `expDomain` would be about the junk-extended equation of one
chart, not about `M`.  This matches
`PetersenLib/Ch05/UniformInjectivityRadius{,Diffeo}.lean` and
`PetersenLib/Ch05/IsometryUniqueness.lean`.

## What is proved

* `isCompl_tangentSpaceImage_normalSpace` — the orthogonal splitting
  `T_pM = T_pN ⊕ (T_pN)^⊥` asserted in the definition.  Proved by a rank count:
  `normalSpace` is the kernel of `v ↦ g(v, ·)|_{T_pN}`, so its rank is at least
  `dim T_pM - dim T_pN`, while positive-definiteness of `g` forces the
  intersection to be trivial.  (No immersion hypothesis is needed for the
  splitting itself; `F` an immersion is what makes `tangentSpaceImage` a faithful
  copy of `T_qN`.)
* `normalExpMap_eq_intrinsicExpMap`, `normalExpMap_apply` — `exp^⊥` agrees with
  `exp` on normal vectors, definitionally.
* `zero_mem_normalExpDomain`, `normalExpMap_zero` — the zero section lies in the
  domain and `exp^⊥(0_p) = p`; so `exp^⊥` is defined on the zero section, the
  set the tubular neighbourhood theorem thickens.
* `exists_normalExp_ball_subset_domain`, `exists_injOn_contMDiffOn_normalExp` —
  around each `q : N` a `g`-ball of normal vectors on which `exp^⊥` is defined,
  injective, and `C^∞` (`compactSet_uniformCInftyDiffeo` at `{F q}`).  This is the
  **fibrewise** half of `cor:pet-ch5-tubular-neighborhood`; the corollary's
  content beyond it is injectivity *across nearby fibres* and a uniform radius,
  which is not claimed here.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §5.5.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]
variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
variable {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]

/-! ## The intrinsic exponential map as a map on the tangent bundle -/

/-- **Math.** Petersen §5.5 (`def:pet-ch5-exponential-map`): the domain
`O = ⋃_p O_p ⊆ TM` of the exponential map — the vectors `v ∈ T_pM` for which the
geodesic with initial datum `v` exists up to time `1`.

This is the **intrinsic** (moving-foot) domain, built from
`geodesicMaximalDomain`, not the chart-anchored `PetersenLib.expDomain`. -/
def intrinsicExpDomain (g : RiemannianMetric I M) : Set (TangentBundle I M) :=
  {v | (1 : ℝ) ∈ geodesicMaximalDomain (I := I) g v.proj v.2}

/-- **Math.** Petersen §5.5: the **exponential map** `exp : O → M`,
`exp(v) = c_v(1)`, collected over all base points.  Off `intrinsicExpDomain g`
this junks to the value of the constant curve at the foot. -/
def intrinsicExpMap (g : RiemannianMetric I M) (v : TangentBundle I M) : M :=
  geodesicMaximalCurve (I := I) g v.proj v.2 1

theorem intrinsicExpMap_apply (g : RiemannianMetric I M) (v : TangentBundle I M) :
    intrinsicExpMap (I := I) g v = geodesicMaximalCurve (I := I) g v.proj v.2 1 :=
  rfl

theorem mem_intrinsicExpDomain_iff (g : RiemannianMetric I M) (v : TangentBundle I M) :
    v ∈ intrinsicExpDomain (I := I) g ↔
      (1 : ℝ) ∈ geodesicMaximalDomain (I := I) g v.proj v.2 :=
  Iff.rfl

/-- **Math.** The zero vector at `p` lies in `O_p`: the constant curve at `p` is a
geodesic defined for all time. -/
theorem zero_mem_intrinsicExpDomain (g : RiemannianMetric I M) (p : M) :
    (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M) ∈ intrinsicExpDomain (I := I) g :=
  ⟨Set.univ, ⟨isOpen_univ, Set.ordConnected_univ, Set.mem_univ 0,
    fun _ : ℝ => p, isGeodesicWithInitialOn_const (I := I) g p⟩, Set.mem_univ 1⟩

/-- **Math.** `exp_p(0) = p`. -/
@[simp]
theorem intrinsicExpMap_zero (g : RiemannianMetric I M) (p : M) :
    intrinsicExpMap (I := I) g (⟨p, (0 : TangentSpace I p)⟩ : TangentBundle I M) = p :=
  geodesicMaximalCurve_zero (I := I) g p 1

/-! ## The tangent and normal spaces of a submanifold -/

/-- **Math.** Petersen §5.5: the **tangent space of the submanifold** presented by
`F : N → M` at `q`, read inside `T_{F q}M` as the image `DF_q(T_qN)`.  When `F` is
an immersion this is a faithful copy of `T_qN`. -/
def tangentSpaceImage (F : N → M) (q : N) : Submodule ℝ (TangentSpace I (F q)) :=
  LinearMap.range (mfderiv IN I F q).toLinearMap

theorem mem_tangentSpaceImage_iff (F : N → M) (q : N) (v : TangentSpace I (F q)) :
    v ∈ tangentSpaceImage (I := I) (IN := IN) F q ↔
      ∃ w : TangentSpace IN q, mfderiv IN I F q w = v :=
  Iff.rfl

/-- **Math.** Petersen §5.5 (`def:pet-ch5-normal-exponential-map`): the **normal
space** `(T_qN)^⊥ ⊆ T_{F q}M` of the submanifold presented by `F`, i.e. the
`g`-orthogonal complement of `DF_q(T_qN)`. -/
def normalSpace (g : RiemannianMetric I M) (F : N → M) (q : N) :
    Submodule ℝ (TangentSpace I (F q)) where
  carrier := {v | ∀ w : TangentSpace IN q, g.metricInner (F q) v (mfderiv IN I F q w) = 0}
  add_mem' {a b} ha hb w := by
    rw [g.metricInner_add_left, ha w, hb w, add_zero]
  zero_mem' w := g.metricInner_zero_left _ _
  smul_mem' c a ha w := by
    rw [g.metricInner_smul_left, ha w, mul_zero]

@[simp]
theorem mem_normalSpace_iff (g : RiemannianMetric I M) (F : N → M) (q : N)
    (v : TangentSpace I (F q)) :
    v ∈ normalSpace (I := I) (IN := IN) g F q ↔
      ∀ w : TangentSpace IN q, g.metricInner (F q) v (mfderiv IN I F q w) = 0 :=
  Iff.rfl

/-- **Math.** A vector is normal iff it is `g`-orthogonal to every vector of the
submanifold's tangent space. -/
theorem mem_normalSpace_iff_forall_mem_tangentSpaceImage (g : RiemannianMetric I M)
    (F : N → M) (q : N) (v : TangentSpace I (F q)) :
    v ∈ normalSpace (I := I) (IN := IN) g F q ↔
      ∀ u ∈ tangentSpaceImage (I := I) (IN := IN) F q, g.metricInner (F q) v u = 0 := by
  constructor
  · rintro hv u ⟨w, rfl⟩
    exact hv w
  · intro hv w
    exact hv _ ⟨w, rfl⟩

/-! ### The orthogonal splitting `T_pM = T_pN ⊕ (T_pN)^⊥` -/

section Splitting

/-- **Eng.** The linear map `v ↦ g(v, ·)|_{S}` from `T_xM` to the dual of a
submodule `S ⊆ T_xM`.  Its kernel is the `g`-orthogonal complement of `S`. -/
def metricRestrictedDual (g : RiemannianMetric I M) (x : M)
    (S : Submodule ℝ (TangentSpace I x)) :
    TangentSpace I x →ₗ[ℝ] (S →ₗ[ℝ] ℝ) :=
  (LinearMap.lcomp ℝ ℝ S.subtype).comp
    (((ContinuousLinearMap.coeLM ℝ).comp (g.metricToDual x).toLinearMap))

theorem metricRestrictedDual_apply (g : RiemannianMetric I M) (x : M)
    (S : Submodule ℝ (TangentSpace I x)) (v : TangentSpace I x) (w : S) :
    metricRestrictedDual (I := I) g x S v w = g.metricInner x v (w : TangentSpace I x) :=
  rfl

theorem mem_ker_metricRestrictedDual (g : RiemannianMetric I M) (x : M)
    (S : Submodule ℝ (TangentSpace I x)) (v : TangentSpace I x) :
    v ∈ LinearMap.ker (metricRestrictedDual (I := I) g x S) ↔
      ∀ u ∈ S, g.metricInner x v u = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h u hu
    have := congrArg (fun f : S →ₗ[ℝ] ℝ => f (⟨u, hu⟩ : S)) h
    simpa [metricRestrictedDual_apply] using this
  · intro h
    ext w
    simpa [metricRestrictedDual_apply] using h (w : TangentSpace I x) w.2

/-- **Math.** Petersen §5.5: the submanifold's tangent space and its normal space
are **complementary** in `T_{F q}M`: `T_pM = T_pN ⊕ (T_pN)^⊥`.

Disjointness is positive-definiteness of `g` (a tangent vector orthogonal to
itself vanishes); codisjointness is a rank count — the normal space is the kernel
of `v ↦ g(v, ·)|_{T_qN}`, whose range sits in a space of dimension
`dim T_qN`. -/
theorem isCompl_tangentSpaceImage_normalSpace (g : RiemannianMetric I M) (F : N → M)
    (q : N) :
    IsCompl (tangentSpaceImage (I := I) (IN := IN) F q)
      (normalSpace (I := I) (IN := IN) g F q) := by
  set x := F q with hx
  set S : Submodule ℝ (TangentSpace I x) := tangentSpaceImage (I := I) (IN := IN) F q with hS
  set T : Submodule ℝ (TangentSpace I x) := normalSpace (I := I) (IN := IN) g F q with hT
  have hmem : ∀ v : TangentSpace I x, v ∈ T ↔ ∀ u ∈ S, g.metricInner x v u = 0 :=
    fun v => mem_normalSpace_iff_forall_mem_tangentSpaceImage (I := I) (IN := IN) g F q v
  have hker : T = LinearMap.ker (metricRestrictedDual (I := I) g x S) := by
    refine SetLike.ext fun v => ?_
    rw [mem_ker_metricRestrictedDual, hmem]
  -- disjointness: a vector orthogonal to itself vanishes
  have hdisj : S ⊓ T = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hvS, hvT⟩
    by_contra hv
    exact absurd ((hmem v).mp hvT v hvS) (ne_of_gt (g.metricInner_self_pos x v hv))
  -- rank count
  have hdual : Module.finrank ℝ (S →ₗ[ℝ] ℝ) = Module.finrank ℝ S := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  have hrk := LinearMap.finrank_range_add_finrank_ker
    (metricRestrictedDual (I := I) g x S)
  have hle : Module.finrank ℝ (LinearMap.range (metricRestrictedDual (I := I) g x S)) ≤
      Module.finrank ℝ (S →ₗ[ℝ] ℝ) := Submodule.finrank_le _
  have hrank : Module.finrank ℝ (TangentSpace I x) ≤
      Module.finrank ℝ S + Module.finrank ℝ T := by
    rw [hker]
    omega
  refine ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr ?_⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq S T
  rw [hdisj, finrank_bot] at hsup
  refine Submodule.eq_top_of_finrank_eq ?_
  have hle' : Module.finrank ℝ (S ⊔ T : Submodule ℝ (TangentSpace I x)) ≤
      Module.finrank ℝ (TangentSpace I x) := Submodule.finrank_le _
  omega

end Splitting

/-! ## The normal bundle and the normal exponential map -/

/-- **Math.** Petersen §5.5 (`def:pet-ch5-normal-exponential-map`): the **normal
bundle** `T^⊥N = {v ∈ T_pM | p ∈ N, v ⟂ T_pN}`, read inside `TM` for the
submanifold presented by `F : N → M`. -/
def normalBundle (g : RiemannianMetric I M) (F : N → M) : Set (TangentBundle I M) :=
  {v | ∃ q : N, ∃ _ : F q = v.proj,
    ((v.2 : E) : TangentSpace I (F q)) ∈ normalSpace (I := I) (IN := IN) g F q}

/-- **Math.** Petersen §5.5: the domain `O ∩ T^⊥N` of the normal exponential map. -/
def normalExpDomain (g : RiemannianMetric I M) (F : N → M) : Set (TangentBundle I M) :=
  normalBundle (I := I) (IN := IN) g F ∩ intrinsicExpDomain (I := I) g

/-- **Math.** Petersen §5.5 (`def:pet-ch5-normal-exponential-map`): the **normal
exponential map** `exp^⊥ : O ∩ T^⊥N → M`, the restriction of the (intrinsic)
exponential map to the normal bundle. -/
def normalExpMap (g : RiemannianMetric I M) (F : N → M) :
    normalExpDomain (I := I) (IN := IN) g F → M :=
  (normalExpDomain (I := I) (IN := IN) g F).restrict (intrinsicExpMap (I := I) g)

/-- **Math.** `exp^⊥` *is* `exp` on normal vectors — the content of "restricts
`exp` to `T^⊥N`". -/
theorem normalExpMap_eq_intrinsicExpMap (g : RiemannianMetric I M) (F : N → M)
    (v : normalExpDomain (I := I) (IN := IN) g F) :
    normalExpMap (I := I) (IN := IN) g F v = intrinsicExpMap (I := I) g (v : TangentBundle I M) :=
  rfl

theorem normalExpMap_apply (g : RiemannianMetric I M) (F : N → M)
    (v : normalExpDomain (I := I) (IN := IN) g F) :
    normalExpMap (I := I) (IN := IN) g F v =
      geodesicMaximalCurve (I := I) g (v : TangentBundle I M).proj (v : TangentBundle I M).2 1 :=
  rfl

/-- **Math.** The zero section of `T^⊥N` lies in the domain of `exp^⊥`. -/
theorem zero_mem_normalExpDomain (g : RiemannianMetric I M) (F : N → M) (q : N) :
    (⟨F q, (0 : TangentSpace I (F q))⟩ : TangentBundle I M) ∈
      normalExpDomain (I := I) (IN := IN) g F :=
  ⟨⟨q, rfl, Submodule.zero_mem _⟩, zero_mem_intrinsicExpDomain (I := I) g (F q)⟩

/-- **Math.** `exp^⊥(0_p) = p`: the normal exponential map restricted to the zero
section is the inclusion of `N`. -/
theorem normalExpMap_zero (g : RiemannianMetric I M) (F : N → M) (q : N) :
    normalExpMap (I := I) (IN := IN) g F
      ⟨(⟨F q, (0 : TangentSpace I (F q))⟩ : TangentBundle I M),
        zero_mem_normalExpDomain (I := I) (IN := IN) g F q⟩ = F q :=
  intrinsicExpMap_zero (I := I) g (F q)

/-! ## The fibrewise half of the tubular neighbourhood theorem -/

/-- **Math.** Petersen §5.5, towards `cor:pet-ch5-tubular-neighborhood`: around
every point `q` of the submanifold, `exp^⊥` is **defined, injective and `C^∞` on a
whole ball of normal vectors** at `F q`.

This is `compactSet_uniformCInftyDiffeo` (Cor. 5.5.2) at the compact set `{F q}`,
restricted to the normal fibre `(T_qN)^⊥ ⊆ T_{F q}M`.  It is the *fibrewise* half
of the tubular neighbourhood theorem: what it does **not** give is injectivity of
`exp^⊥` across nearby fibres, nor a radius uniform in `q`; both are needed for the
corollary and are not claimed here.

As always, `exp` is the intrinsic moving-foot exponential
(`intrinsicExpMap = geodesicMaximalCurve · 1`), never the chart artifact
`PetersenLib.expMap`. -/
theorem exists_ball_normalExp_defined_injOn_contMDiffOn (g : RiemannianMetric I M)
    (F : N → M) (q : N) :
    ∃ ε > (0 : ℝ),
      (∀ v : TangentSpace I (F q), v ∈ normalSpace (I := I) (IN := IN) g F q →
          g.metricInner (F q) v v < ε ^ 2 →
          (⟨F q, v⟩ : TangentBundle I M) ∈ normalExpDomain (I := I) (IN := IN) g F) ∧
      Set.InjOn
        (fun v : TangentSpace I (F q) =>
          intrinsicExpMap (I := I) g (⟨F q, v⟩ : TangentBundle I M))
        {v : TangentSpace I (F q) | v ∈ normalSpace (I := I) (IN := IN) g F q ∧
          g.metricInner (F q) v v < ε ^ 2} ∧
      ContMDiffOn 𝓘(ℝ, E) I ∞
        (fun w : E =>
          intrinsicExpMap (I := I) g
            (⟨F q, (w : TangentSpace I (F q))⟩ : TangentBundle I M))
        {w : E | (w : TangentSpace I (F q)) ∈ normalSpace (I := I) (IN := IN) g F q ∧
          g.metricInner (F q) (w : TangentSpace I (F q)) (w : TangentSpace I (F q)) <
            ε ^ 2} := by
  obtain ⟨ε, hε, hspec⟩ :=
    compactSet_uniformCInftyDiffeo (I := I) g (isCompact_singleton (x := F q))
  obtain ⟨hdom, hinj, hsmooth, -, -⟩ := hspec (F q) rfl
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · exact fun v hv hlt => ⟨⟨q, rfl, hv⟩, hdom v hlt⟩
  · exact hinj.mono fun v hv => hv.2
  · exact hsmooth.mono fun w hw => hw.2

end PetersenLib
