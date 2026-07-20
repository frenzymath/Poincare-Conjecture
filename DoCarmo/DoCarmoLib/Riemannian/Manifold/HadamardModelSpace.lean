import DoCarmoLib.Riemannian.Manifold.HadamardAssembly
import DoCarmoLib.Riemannian.Manifold.PullbackMetric
import DoCarmoLib.Riemannian.Exponential.GlobalExp
import DoCarmoLib.Riemannian.Metric.RiemannianDistance
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# The model space as a Riemannian manifold for the Hadamard/poles theorem (do Carmo Ch. 7, §3)

do Carmo's proof of the Hadamard theorem (`thm:dc-ch7-3-1`) and of the poles remark
(`rem:dc-ch7-3-4`) equips the tangent space `T_pM` — a copy of the model space `E` — with the
**pulled-back metric** `(\exp_p)^* g`, making `\exp_p : T_pM → M` a local isometry, and then
applies the abstract Hadamard assembly `DCExpandsMetric.diffeomorphOfSimplyConnectedOfGeodesicCompleteAt`.

The obstruction to *instantiating* that assembly at `\exp_p` is purely bookkeeping about
type-class instances: the assembly needs its **source** manifold to carry a `MetricSpace`
whose distance is the *Riemannian distance of the pulled-back metric*, but `T_pM = E` already
carries `E`'s **flat** metric-space structure. The two cannot both be the ambient `MetricSpace`
on the same type. This file resolves the collision the standard way — via a **type synonym**
`HadamardModel E := E` that is *not* reducible, so `E`'s flat structure does not leak into it,
and onto which we place:

* `HadamardModel E`'s topology (`= E`'s), connectedness, `T3`, preconnectedness,
  local path connectedness;
* a `ChartedSpace E (HadamardModel E)` and `IsManifold 𝓘(ℝ,E) ∞ (HadamardModel E)` structure
  built from the single global identity chart `HadamardModel E → E` (an open embedding), via
  mathlib's `Topology.IsOpenEmbedding.singletonChartedSpace` / `.isManifold_singleton`;
* the **flat reference metric** `flatMetric` (`E`'s inner product on each tangent fibre),
  the reference fibre-metric the pullback construction runs against.

On top of this carrier we build the pulled-back metric `(\exp_p)^* g` (`pullbackMetric`) and
prove **do Carmo's poles theorem** (`diffeomorphOfPole`): a smooth local diffeomorphism out of
`HadamardModel E` (the pole hypothesis) whose radial lines are geodesics of the pulled-back
metric is a diffeomorphism. The two analytic inputs — that `\exp_p` is a local diffeomorphism
(the pole) and that the rays are pullback-geodesics (local isometry) — are do Carmo's own; the
whole topological/smooth remainder is discharged by the assembly.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §3, proof of Theorem 3.1 (Hadamard) and
Remark 3.4 (poles).
-/

open Bundle Manifold Set Function
open scoped Manifold Topology ContDiff RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

/-- **Math.** A copy of the model space `E`, kept as a *non-reducible* type synonym so that it
does **not** inherit `E`'s flat metric-space structure. It is do Carmo's `T_pM` regarded as a
manifold in its own right, onto which the pulled-back metric `(\exp_p)^* g` of the Hadamard
proof is placed (do Carmo Ch. 7, §3.4). -/
def HadamardModel (E : Type*) : Type _ := E

namespace HadamardModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Eng.** `HadamardModel E` carries `E`'s topology (they are the same underlying type). -/
instance : TopologicalSpace (HadamardModel E) := inferInstanceAs (TopologicalSpace E)

instance : ConnectedSpace (HadamardModel E) := inferInstanceAs (ConnectedSpace E)

instance : T3Space (HadamardModel E) := inferInstanceAs (T3Space E)

instance : PreconnectedSpace (HadamardModel E) := inferInstanceAs (PreconnectedSpace E)

instance : LocPathConnectedSpace (HadamardModel E) := inferInstanceAs (LocPathConnectedSpace E)

instance : Nonempty (HadamardModel E) := inferInstanceAs (Nonempty E)

/-- **Math.** The single global chart `HadamardModel E → E`, the identity of the underlying
type. -/
def toModel : HadamardModel E → E := id

/-- **Math.** The identity chart is an open embedding (the identity map between two copies of the
same topological space), so it exhibits `HadamardModel E` as a one-chart manifold. -/
theorem isOpenEmbedding_toModel : Topology.IsOpenEmbedding (toModel (E := E)) :=
  Topology.IsOpenEmbedding.id

/-- **Eng.** The single-chart `ChartedSpace` structure on `HadamardModel E`, modelled on `E`. -/
instance instChartedSpace : ChartedSpace E (HadamardModel E) :=
  (isOpenEmbedding_toModel (E := E)).singletonChartedSpace

/-- **Eng.** `HadamardModel E` is a smooth manifold modelled on `𝓘(ℝ, E)` via its single global
chart. -/
instance instIsManifold : IsManifold (𝓘(ℝ, E)) ∞ (HadamardModel E) :=
  (isOpenEmbedding_toModel (E := E)).isManifold_singleton

/-- **Math.** The tangent space of `HadamardModel E` at any point is the model space `E`. -/
example (x : HadamardModel E) : TangentSpace (𝓘(ℝ, E)) x = E := rfl

/-! ## The flat reference metric

`RiemannianMetric.pullback` (used to build the pulled-back metric `(\exp_p)^* g`) requires the
**source** manifold to already carry a `[Bundle.RiemannianBundle (TangentSpace I)]` — a
reference family of fibre inner products — purely to run its von-Neumann-boundedness argument
(the pulled-back metric's boundedness is transported from the target's across the injective
differential, which needs a fibre norm on the source). We supply the obvious such reference on
`HadamardModel E`: the **flat metric** given by `E`'s own inner product on every tangent
fibre, mirroring mathlib's `riemannianMetricVectorSpace`. The final pulled-back metric is a
*different* inner product; this one only fixes the fibre norms. -/

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The **flat Riemannian metric** on `HadamardModel E`: `E`'s inner product on every
tangent fibre, constant in the base point. This mirrors mathlib's `riemannianMetricVectorSpace`
for the single-chart manifold `HadamardModel E`, and serves only as the reference fibre-metric
needed to run the pullback construction. -/
def flatMetric (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : HadamardModel E => TangentSpace 𝓘(ℝ, E) x) where
  inner _ := (innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ)
  symm _ v w := real_inner_comm _ _
  pos _ v hv := real_inner_self_pos.2 hv
  isVonNBounded _ := by
    change Bornology.IsVonNBounded ℝ {v : E | ⟪v, v⟫ < 1}
    have hball : Metric.ball (0 : E) 1 = {v : E | ⟪v, v⟫ < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
        RCLike.re_to_real, Set.mem_setOf_eq]
      conv_lhs => rw [show (1 : ℝ) = √1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← hball]
    exact NormedSpace.isVonNBounded_ball ℝ E 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert contMDiffAt_const (c := innerSL ℝ (E := E))
    ext v w
    have hid : (HadamardModel.toModel (E := E) ∘
        ⇑((HadamardModel.isOpenEmbedding_toModel (E := E)).toOpenPartialHomeomorph
          (HadamardModel.toModel (E := E))).symm) = id := by
      funext y
      exact (HadamardModel.isOpenEmbedding_toModel (E := E)).toOpenPartialHomeomorph_right_inv
        (HadamardModel.toModel (E := E)) ⟨y, rfl⟩
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]
    rw [hid, fderiv_id]
    simp

/-- **Math.** The flat reference `RiemannianBundle` on `HadamardModel E`'s tangent bundle,
supplying the fibre norms the pullback construction runs against. Kept as a **`def`, not a
global instance**, so it never competes with the pulled-back `⟨gM⟩` bundle that the metric-space
construction registers: it is switched on locally (via `letI`) only inside the pullback-metric
construction, where it is the ambient bundle, and the resulting metric's *type* is independent
of it. -/
@[reducible] def flatBundle (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Bundle.RiemannianBundle (fun x : HadamardModel E => TangentSpace 𝓘(ℝ, E) x) :=
  ⟨(flatMetric E).toRiemannianMetric⟩

end HadamardModel

/-! ## The poles theorem: `exp_p` a local diffeomorphism ⟹ a diffeomorphism (do Carmo Ch. 7,
Remark 3.4)

do Carmo's Remark 3.4: *if a complete simply connected Riemannian manifold `N` has a pole `p`
(a point with no conjugate points, i.e. `exp_p` is a local diffeomorphism), then `exp_p : T_pN → N`
is a diffeomorphism, so `N` is diffeomorphic to `ℝⁿ`*.

We formalise this by instantiating the abstract Hadamard assembly
`DCExpandsMetric.diffeomorphOfSimplyConnectedOfGeodesicCompleteAt` at
`f = exp_p : HadamardModel (T_pN) → N`, where `HadamardModel (T_pN)` carries the **pulled-back
metric** `(exp_p)^* g` built below. The two analytic inputs the assembly consumes — that `exp_p`
is a smooth local diffeomorphism (the *pole* hypothesis, `hf`) and that the radial lines
`s ↦ s • v` of `T_pN` are geodesics of the pulled-back metric (`hrays`) — are taken as
explicit hypotheses: they are precisely do Carmo's own inputs (`hf` is the definition of a
pole; `hrays` is "the geodesics of `T_pN` through the origin are straight lines", i.e. that
`exp_p` is a *local isometry*, cf. Theorem 2.8 (a) ⟹ (d) read on `T_pN`). Everything
topological and smooth downstream — properness of `T_pN`, the covering-map structure, and
bijectivity onto the simply connected `N` — is discharged by the assembly. -/
section Poles

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Module.Finite ℝ F] [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

open RiemannianMetric

/-- **Math.** A smooth local diffeomorphism `f : HadamardModel F → N` is in particular a smooth
immersion (do Carmo Ch. 0/1: smooth with injective differential): its differential is a linear
equivalence at every point (`IsLocalDiffeomorph.mfderivToContinuousLinearEquiv`), hence
injective. -/
theorem HadamardModel.dcSmoothImmersion_of_isLocalDiffeomorph {f : HadamardModel F → N}
    (hf : IsLocalDiffeomorph 𝓘(ℝ, F) I ∞ f) :
    DCSmoothImmersion (I := 𝓘(ℝ, F)) (I' := I) f :=
  ⟨hf.contMDiff, fun x => by
    have hc := hf.mfderivToContinuousLinearEquiv_coe (n := ∞) (by simp) x
    simp only [← hc, ContinuousLinearEquiv.coe_coe]
    exact (hf.mfderivToContinuousLinearEquiv (by simp) x).injective⟩

/-- **Math.** The **pulled-back metric** `f^*g` on `HadamardModel F` for a smooth local
diffeomorphism `f : HadamardModel F → N` (do Carmo's metric on `T_pN`, making `f` a local
isometry). The flat reference bundle is switched on locally, so the resulting metric's type is
independent of it. -/
@[reducible] def HadamardModel.pullbackMetric {f : HadamardModel F → N}
    (g : RiemannianMetric I N) (hf : IsLocalDiffeomorph 𝓘(ℝ, F) I ∞ f) :
    RiemannianMetric 𝓘(ℝ, F) (HadamardModel F) :=
  letI : Bundle.RiemannianBundle (fun x : HadamardModel F => TangentSpace 𝓘(ℝ, F) x) :=
    HadamardModel.flatBundle F
  RiemannianMetric.pullbackOfSmoothImmersion g f
    (HadamardModel.dcSmoothImmersion_of_isLocalDiffeomorph hf)

/-- **Math.** `f` **expands** (indeed preserves) its own pulled-back metric — the
`DCExpandsMetric` input consumed by the Hadamard assembly. -/
theorem HadamardModel.dcExpandsMetric_pullbackMetric {f : HadamardModel F → N}
    (g : RiemannianMetric I N) (hf : IsLocalDiffeomorph 𝓘(ℝ, F) I ∞ f) :
    DCExpandsMetric (HadamardModel.pullbackMetric g hf) g f :=
  letI : Bundle.RiemannianBundle (fun x : HadamardModel F => TangentSpace 𝓘(ℝ, F) x) :=
    HadamardModel.flatBundle F
  RiemannianMetric.dcExpandsMetric_pullbackOfSmoothImmersion g f
    (HadamardModel.dcSmoothImmersion_of_isLocalDiffeomorph hf)

/-- **Math.** do Carmo Ch. 7, **Remark 3.4 (poles)**. Let `N` be a complete, simply connected
Riemannian manifold and `f : HadamardModel F → N` a **smooth local diffeomorphism** (the pole
hypothesis: for `f = exp_p` this is "`p` has no conjugate points") which is metric-expanding for
its own pulled-back metric. If the radial lines of `HadamardModel F` are geodesics of that
pulled-back metric (`hrays` — do Carmo's "the geodesics of `T_pN` through the origin are straight
lines", i.e. `f` is a local isometry), then `f` is a **diffeomorphism** `HadamardModel F ≃ N`.

Instantiates `DCExpandsMetric.diffeomorphOfSimplyConnectedOfGeodesicCompleteAt` at
`M = HadamardModel F` with the pulled-back metric, deriving properness of `HadamardModel F`
from `hrays` (geodesic completeness at the origin) internally. This is the exact content of
do Carmo's proof of the Hadamard theorem specialised to a pole, modulo the two analytic inputs
`hf`/`hrays` it consumes. -/
def HadamardModel.diffeomorphOfPole [ConnectedSpace N] [SimplyConnectedSpace N]
    [LocPathConnectedSpace N] {f : HadamardModel F → N} (g : RiemannianMetric I N)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, F) I ∞ f)
    (hrays : ∀ v : TangentSpace 𝓘(ℝ, F) (0 : HadamardModel F),
      ∃ γ : ℝ → HadamardModel F, γ 0 = 0 ∧
        HasDerivAt (fun s => extChartAt 𝓘(ℝ, F) (0 : HadamardModel F) (γ s)) v 0 ∧
          Continuous γ ∧ Geodesic.IsGeodesic (I := 𝓘(ℝ, F)) (HadamardModel.pullbackMetric g hf) γ) :
    Diffeomorph 𝓘(ℝ, F) I (HadamardModel F) N ∞ :=
  letI gM : RiemannianMetric 𝓘(ℝ, F) (HadamardModel F) := HadamardModel.pullbackMetric g hf
  letI : Bundle.RiemannianBundle (fun x : HadamardModel F => TangentSpace 𝓘(ℝ, F) x) :=
    ⟨(gM.toContinuousRiemannianMetric).toRiemannianMetric⟩
  letI : MetricSpace (HadamardModel F) := MetricSpace.ofRiemannianMetric 𝓘(ℝ, F) (HadamardModel F)
  haveI hgM : gM.IsRiemannianDist := ⟨fun _ _ => rfl⟩
  (HadamardModel.dcExpandsMetric_pullbackMetric g hf).diffeomorphOfSimplyConnectedOfGeodesicCompleteAt
    hgM (0 : HadamardModel F) hrays hf

/-- **Math.** The diffeomorphism produced by `diffeomorphOfPole` **is** `f` itself (for the pole
application, `f = exp_p`): it is `f`, upgraded, not a new map. This is the anti-vacuity guard —
the conclusion genuinely upgrades `f` to a diffeomorphism. -/
theorem HadamardModel.diffeomorphOfPole_coe [ConnectedSpace N] [SimplyConnectedSpace N]
    [LocPathConnectedSpace N] {f : HadamardModel F → N} (g : RiemannianMetric I N)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, F) I ∞ f)
    (hrays : ∀ v : TangentSpace 𝓘(ℝ, F) (0 : HadamardModel F),
      ∃ γ : ℝ → HadamardModel F, γ 0 = 0 ∧
        HasDerivAt (fun s => extChartAt 𝓘(ℝ, F) (0 : HadamardModel F) (γ s)) v 0 ∧
          Continuous γ ∧ Geodesic.IsGeodesic (I := 𝓘(ℝ, F)) (HadamardModel.pullbackMetric g hf) γ) :
    ⇑(HadamardModel.diffeomorphOfPole g hf hrays) = f := rfl

/-- **Math.** do Carmo Ch. 7, **Remark 3.4**, for the exponential map itself. On a complete,
simply connected Riemannian manifold `N`, if `p` is a **pole** — i.e. `exp_p : T_pN → N` is a
smooth local diffeomorphism — and the radial lines of `T_pN` are geodesics of the pulled-back
metric `exp_p^*g` (i.e. `exp_p` is a local isometry), then `exp_p` is a **diffeomorphism**
`T_pN ≃ N`; in particular `N` is diffeomorphic to `ℝⁿ`. This is `diffeomorphOfPole` applied to
`f = exp_p`. -/
def HadamardModel.expDiffeomorphOfPole [CompleteSpace N] [ConnectedSpace N]
    [SimplyConnectedSpace N] [LocPathConnectedSpace N] (g : RiemannianMetric I N)
    (hg : g.IsRiemannianDist) (p : N)
    (hpole : IsLocalDiffeomorph 𝓘(ℝ, F) I ∞
      (fun v : HadamardModel F => Exponential.expMapGlobal g hg p (HadamardModel.toModel v)))
    (hrays : ∀ v : TangentSpace 𝓘(ℝ, F) (0 : HadamardModel F),
      ∃ γ : ℝ → HadamardModel F, γ 0 = 0 ∧
        HasDerivAt (fun s => extChartAt 𝓘(ℝ, F) (0 : HadamardModel F) (γ s)) v 0 ∧
          Continuous γ ∧ Geodesic.IsGeodesic (I := 𝓘(ℝ, F))
            (HadamardModel.pullbackMetric g hpole) γ) :
    Diffeomorph 𝓘(ℝ, F) I (HadamardModel F) N ∞ :=
  HadamardModel.diffeomorphOfPole g hpole hrays

end Poles

end Riemannian

end
