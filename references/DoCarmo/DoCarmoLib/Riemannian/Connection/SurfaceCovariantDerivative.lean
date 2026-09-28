import DoCarmoLib.Riemannian.Connection.CovariantDerivativeAlong
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3SurfaceBoundary
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3SurfaceSymmetry
import DoCarmoLib.Riemannian.Variation.SurfaceSymmetryManifold

/-!
# Intrinsic covariant derivatives on a parametrized surface

The existing `Geodesic.ParametrizedSurface` is already manifold-valued, but its
legacy regularity field records only `C^1` regularity on the parameter set.  This
file bundles do Carmo's full smooth open-extension and boundary data as
`IntrinsicParametrizedSurface`, and also packages slice velocities and mixed
covariant derivatives for the legacy type using `covDerivAlong`.

The final symmetry theorem is do Carmo Ch. 3, Lemma 3.4 in operator form:
`D/du (ds/dv) = D/dv (ds/du)`.  Its proof transports the existing coordinate
core through the fixed-chart formula for `covDerivAlong`; the public equality is
between vectors in `T_(s q) M` and mentions no coordinate operator.
-/

open Bundle Manifold Set Filter
open scoped ContDiff Manifold Topology ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A do Carmo Ch. 3, Definition 3.3 parametrized surface, bundled
intrinsically: a manifold-valued map together with its smooth open-neighborhood
extension, connected planar domain, and piecewise-`C^1` non-straight boundary
data. -/
structure IntrinsicParametrizedSurface where
  domain : Set (ℝ × ℝ)
  toFun : ℝ × ℝ → M
  regularity : IsSmoothParametrizedSurfaceWithBoundary I domain toFun

namespace IntrinsicParametrizedSurface

instance : CoeFun (IntrinsicParametrizedSurface (I := I) (M := M))
    (fun _ => ℝ × ℝ → M) := ⟨toFun⟩

@[simp] theorem coe_apply (S : IntrinsicParametrizedSurface (I := I) (M := M))
    (q : ℝ × ℝ) : S q = S.toFun q := rfl

/-- **Math.** Forget the faithful smooth and boundary data, retaining the
legacy bundled surface used by the coordinate core. -/
def toParametrizedSurface (S : IntrinsicParametrizedSurface (I := I) (M := M)) :
    ParametrizedSurface (I := I) (M := M) where
  domain := S.domain
  toFun := S.toFun
  smooth := S.regularity.isParametrizedSurface (by simp)

@[simp] theorem toParametrizedSurface_domain
    (S : IntrinsicParametrizedSurface (I := I) (M := M)) :
    S.toParametrizedSurface.domain = S.domain := rfl

@[simp] theorem toParametrizedSurface_toFun
    (S : IntrinsicParametrizedSurface (I := I) (M := M)) :
    S.toParametrizedSurface.toFun = S.toFun := rfl

end IntrinsicParametrizedSurface

namespace ParametrizedSurface

/-- **Math.** The intrinsic velocity `ds/du` of the fixed-`v` slice through
`q`, as a vector in `T_(s q) M`. -/
def velocityU (S : ParametrizedSurface (I := I) (M := M))
    (q : ℝ × ℝ) : TangentSpace I (S q) :=
  mfderiv 𝓘(ℝ, ℝ) I (surfaceSliceU S.toFun q.2) q.1 1

/-- **Math.** The intrinsic velocity `ds/dv` of the fixed-`u` slice through
`q`, as a vector in `T_(s q) M`. -/
def velocityV (S : ParametrizedSurface (I := I) (M := M))
    (q : ℝ × ℝ) : TangentSpace I (S q) :=
  mfderiv 𝓘(ℝ, ℝ) I (surfaceSliceV S.toFun q.1) q.2 1

/-- **Math.** The intrinsic mixed derivative `D/du (ds/dv)` at `q`.  The
outer covariant derivative is taken along the fixed-`v` slice. -/
def covariantDerivativeUOfVelocityV (g : RiemannianMetric I M)
    (S : ParametrizedSurface (I := I) (M := M)) (q : ℝ × ℝ) :
    TangentSpace I (S q) :=
  covDerivAlong (I := I) g (surfaceSliceU S.toFun q.2)
    (fun u => S.velocityV (u, q.2)) q.1

/-- **Math.** The intrinsic mixed derivative `D/dv (ds/du)` at `q`.  The
outer covariant derivative is taken along the fixed-`u` slice. -/
def covariantDerivativeVOfVelocityU (g : RiemannianMetric I M)
    (S : ParametrizedSurface (I := I) (M := M)) (q : ℝ × ℝ) :
    TangentSpace I (S q) :=
  covDerivAlong (I := I) g (surfaceSliceV S.toFun q.1)
    (fun v => S.velocityU (q.1, v)) q.2

variable {r : ℕ∞ω}

/-- **Math.** On an extended surface of order at least one, the intrinsic
fixed-`v` slice velocity is the legacy two-parameter `partialU`. -/
theorem velocityU_eq_partialU (S : ParametrizedSurface (I := I) (M := M))
    (hS : IsExtendedParametrizedSurfaceOfOrder I r S.domain S.toFun)
    (hr : (1 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ S.domain) :
    S.velocityU q = S.partialU q :=
  (S.partialU_eq_slice_mfderiv hS hr hq).symm

/-- **Math.** On an extended surface of order at least one, the intrinsic
fixed-`u` slice velocity is the legacy two-parameter `partialV`. -/
theorem velocityV_eq_partialV (S : ParametrizedSurface (I := I) (M := M))
    (hS : IsExtendedParametrizedSurfaceOfOrder I r S.domain S.toFun)
    (hr : (1 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ S.domain) :
    S.velocityV q = S.partialV q :=
  (S.partialV_eq_slice_mfderiv hS hr hq).symm

section Boundaryless

variable [I.Boundaryless]

/-- **Math.** Intrinsic mixed-covariant-derivative symmetry at a point, under
explicit local chart regularity.  If `F = extChartAt I alpha ∘ S` has the
eventual first derivative `DF` near `(u₀,v₀)` and `DF` has derivative `D2F`
there, then

`D/du (ds/dv) = D/dv (ds/du)`

as an equality in `T_(S (u₀,v₀)) M`.  The continuity hypothesis is stated
separately because it is what identifies the intrinsic slice velocities with
the derivatives of the chart reading.  The coordinate symmetry theorem remains
the proof engine, but neither side of this statement is coordinate-valued. -/
theorem covariantDerivativeUOfVelocityV_eq_covariantDerivativeVOfVelocityU_of_hasFDerivAt
    (g : RiemannianMetric I M) (S : ParametrizedSurface (I := I) (M := M)) (α : M)
    (DF : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E))
    (D2F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E) {u₀ v₀ : ℝ}
    (hcont : ∀ᶠ p in 𝓝 (u₀, v₀), ContinuousAt S.toFun p)
    (hsrc : S.toFun (u₀, v₀) ∈ (chartAt H α).source)
    (hF : ∀ᶠ p in 𝓝 (u₀, v₀),
      HasFDerivAt (fun q => extChartAt I α (S.toFun q)) (DF p) p)
    (hF2 : HasFDerivAt DF D2F (u₀, v₀)) :
    S.covariantDerivativeUOfVelocityV g (u₀, v₀) =
      S.covariantDerivativeVOfVelocityU g (u₀, v₀) := by
  have hcont₀ : ContinuousAt S.toFun (u₀, v₀) := hcont.self_of_nhds
  have hsrc_ev : ∀ᶠ p in 𝓝 (u₀, v₀), S.toFun p ∈ (chartAt H α).source :=
    hcont₀.eventually_mem ((chartAt H α).open_source.mem_nhds hsrc)
  have htendU : Tendsto (fun u : ℝ => (u, v₀)) (𝓝 u₀) (𝓝 (u₀, v₀)) :=
    (continuous_id.prodMk continuous_const).tendsto u₀
  have htendV : Tendsto (fun v : ℝ => (u₀, v)) (𝓝 v₀) (𝓝 (u₀, v₀)) :=
    (continuous_const.prodMk continuous_id).tendsto v₀

  have hevU : chartFieldRep (I := I) (surfaceSliceU S.toFun v₀) α
      (fun u => S.velocityV (u, v₀)) =ᶠ[𝓝 u₀]
        fun u => DF (u, v₀) (0, 1) := by
    filter_upwards [htendU.eventually hcont, htendU.eventually hF,
      htendU.eventually hsrc_ev] with u hcontu hFu hsrcu
    have hvel := mfderiv_snd_eq_of_hasFDerivAt_extChartAt
      (I := I) (s := S.toFun) (q := (u, v₀)) hcontu hsrcu hFu
    have hvel' : S.velocityV (u, v₀) =
        tangentCoordChange I α (S.toFun (u, v₀)) (S.toFun (u, v₀))
          (DF (u, v₀) (0, 1)) := by
      simpa only [velocityV, surfaceSliceV] using hvel
    show tangentCoordChange I (S.toFun (u, v₀)) α (S.toFun (u, v₀))
        (S.velocityV (u, v₀)) = DF (u, v₀) (0, 1)
    rw [hvel']
    exact Riemannian.Variation.tangentCoordChange_readback (I := I) hsrcu _
  have hevV : chartFieldRep (I := I) (surfaceSliceV S.toFun u₀) α
      (fun v => S.velocityU (u₀, v)) =ᶠ[𝓝 v₀]
        fun v => DF (u₀, v) (1, 0) := by
    filter_upwards [htendV.eventually hcont, htendV.eventually hF,
      htendV.eventually hsrc_ev] with v hcontv hFv hsrcv
    have hvel := mfderiv_fst_eq_of_hasFDerivAt_extChartAt
      (I := I) (s := S.toFun) (q := (u₀, v)) hcontv hsrcv hFv
    have hvel' : S.velocityU (u₀, v) =
        tangentCoordChange I α (S.toFun (u₀, v)) (S.toFun (u₀, v))
          (DF (u₀, v) (1, 0)) := by
      simpa only [velocityU, surfaceSliceU] using hvel
    show tangentCoordChange I (S.toFun (u₀, v)) α (S.toFun (u₀, v))
        (S.velocityU (u₀, v)) = DF (u₀, v) (1, 0)
    rw [hvel']
    exact Riemannian.Variation.tangentCoordChange_readback (I := I) hsrcv _

  have hcurveU : ContinuousAt (surfaceSliceU S.toFun v₀) u₀ := by
    have hpair : ContinuousAt (fun u : ℝ => (u, v₀)) u₀ := by fun_prop
    exact show ContinuousAt (S.toFun ∘ fun u : ℝ => (u, v₀)) u₀ from
      hcont₀.comp (x := u₀) (by simpa using hpair)
  have hcurveV : ContinuousAt (surfaceSliceV S.toFun u₀) v₀ := by
    have hpair : ContinuousAt (fun v : ℝ => (u₀, v)) v₀ := by fun_prop
    exact show ContinuousAt (S.toFun ∘ fun v : ℝ => (u₀, v)) v₀ from
      hcont₀.comp (x := v₀) (by simpa using hpair)
  have hchartU : DifferentiableAt ℝ
      (fun u => extChartAt I α (surfaceSliceU S.toFun v₀ u)) u₀ := by
    simpa [surfaceSliceU] using
      (Riemannian.Jacobi.hasDerivAt_comp_fst hF.self_of_nhds).differentiableAt
  have hchartV : DifferentiableAt ℝ
      (fun v => extChartAt I α (surfaceSliceV S.toFun u₀ v)) v₀ := by
    simpa [surfaceSliceV] using
      (Riemannian.Jacobi.hasDerivAt_comp_snd hF.self_of_nhds).differentiableAt

  have hDFU : HasDerivAt (fun u => DF (u, v₀)) (D2F (1, 0)) u₀ :=
    Riemannian.Jacobi.hasDerivAt_comp_fst hF2
  have hDFV : HasDerivAt (fun v => DF (u₀, v)) (D2F (0, 1)) v₀ :=
    Riemannian.Jacobi.hasDerivAt_comp_snd hF2
  have hvelU : HasDerivAt (fun u => DF (u, v₀) (0, 1))
      (D2F (1, 0) (0, 1)) u₀ :=
    HasFDerivAt.comp_hasDerivAt
      (hl := (ContinuousLinearMap.apply ℝ E ((0, 1) : ℝ × ℝ)).hasFDerivAt)
      (hf := hDFU)
  have hvelV : HasDerivAt (fun v => DF (u₀, v) (1, 0))
      (D2F (0, 1) (1, 0)) v₀ :=
    HasFDerivAt.comp_hasDerivAt
      (hl := (ContinuousLinearMap.apply ℝ E ((1, 0) : ℝ × ℝ)).hasFDerivAt)
      (hf := hDFV)
  have hfieldU : DifferentiableAt ℝ
      (chartFieldRep (I := I) (surfaceSliceU S.toFun v₀) α
        (fun u => S.velocityV (u, v₀))) u₀ :=
    (hvelU.congr_of_eventuallyEq hevU).differentiableAt
  have hfieldV : DifferentiableAt ℝ
      (chartFieldRep (I := I) (surfaceSliceV S.toFun u₀) α
        (fun v => S.velocityU (u₀, v))) v₀ :=
    (hvelV.congr_of_eventuallyEq hevV).differentiableAt

  have hcovU := covDerivAlong_eq_chart (I := I) g α hcurveU hsrc hchartU hfieldU
  have hcovV := covDerivAlong_eq_chart (I := I) g α hcurveV hsrc hchartV hfieldV
  have hcoordU : covariantDerivCoord (I := I) g α
      (fun u => extChartAt I α (S.toFun (u, v₀)))
      (chartFieldRep (I := I) (surfaceSliceU S.toFun v₀) α
        (fun u => S.velocityV (u, v₀))) u₀ =
      Riemannian.Jacobi.surfaceCovariantDerivS (I := I) g α
        (fun p => extChartAt I α (S.toFun p)) (fun p => DF p (0, 1)) (u₀, v₀) :=
    Riemannian.Variation.covariantDerivCoord_congr_of_eventuallyEq
      (I := I) g α _ hevU
  have hcoordV : covariantDerivCoord (I := I) g α
      (fun v => extChartAt I α (S.toFun (u₀, v)))
      (chartFieldRep (I := I) (surfaceSliceV S.toFun u₀) α
        (fun v => S.velocityU (u₀, v))) v₀ =
      Riemannian.Jacobi.surfaceCovariantDerivT (I := I) g α
        (fun p => extChartAt I α (S.toFun p)) (fun p => DF p (1, 0)) (u₀, v₀) :=
    Riemannian.Variation.covariantDerivCoord_congr_of_eventuallyEq
      (I := I) g α _ hevV
  have hsymm :=
    Riemannian.Variation.surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst
      (I := I) g α (fun p => extChartAt I α (S.toFun p)) DF D2F u₀ v₀ hF hF2
  have hcoord : covariantDerivCoord (I := I) g α
      (fun u => extChartAt I α (S.toFun (u, v₀)))
      (chartFieldRep (I := I) (surfaceSliceU S.toFun v₀) α
        (fun u => S.velocityV (u, v₀))) u₀ =
      covariantDerivCoord (I := I) g α
      (fun v => extChartAt I α (S.toFun (u₀, v)))
      (chartFieldRep (I := I) (surfaceSliceV S.toFun u₀) α
        (fun v => S.velocityU (u₀, v))) v₀ :=
    hcoordU.trans (hsymm.trans hcoordV.symm)
  have htransport := congrArg
    (tangentCoordChange I α (S.toFun (u₀, v₀)) (S.toFun (u₀, v₀))) hcoord
  have hcovU' : S.covariantDerivativeUOfVelocityV g (u₀, v₀) =
      tangentCoordChange I α (S.toFun (u₀, v₀)) (S.toFun (u₀, v₀))
        (covariantDerivCoord (I := I) g α
          (fun u => extChartAt I α (S.toFun (u, v₀)))
          (chartFieldRep (I := I) (surfaceSliceU S.toFun v₀) α
            (fun u => S.velocityV (u, v₀))) u₀) := by
    simpa [covariantDerivativeUOfVelocityV, surfaceSliceU] using hcovU
  have hcovV' : S.covariantDerivativeVOfVelocityU g (u₀, v₀) =
      tangentCoordChange I α (S.toFun (u₀, v₀)) (S.toFun (u₀, v₀))
        (covariantDerivCoord (I := I) g α
          (fun v => extChartAt I α (S.toFun (u₀, v)))
          (chartFieldRep (I := I) (surfaceSliceV S.toFun u₀) α
            (fun v => S.velocityU (u₀, v))) v₀) := by
    simpa [covariantDerivativeVOfVelocityU, surfaceSliceV] using hcovV
  exact hcovU'.trans (htransport.trans hcovV'.symm)

/-- **Math.** do Carmo Ch. 3, Lemma 3.4 for a bundled intrinsic
parametrized surface:

`D/du (ds/dv) = D/dv (ds/du)`.

The statement exposes neither a chart nor coordinate derivative data.  The
surface's open `C²` extension supplies those data in the canonical chart at
`S q`, and the preceding theorem transports the coordinate symmetry back to
the tangent space `T_(S q) M`. -/
theorem covariantDerivativeUOfVelocityV_eq_covariantDerivativeVOfVelocityU
    (g : RiemannianMetric I M) (S : ParametrizedSurface (I := I) (M := M))
    (hS : IsExtendedParametrizedSurfaceOfOrder I r S.domain S.toFun)
    (hr : (2 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ S.domain) :
    S.covariantDerivativeUOfVelocityV g q =
      S.covariantDerivativeVOfVelocityU g q := by
  obtain ⟨U, hU, hAU, hSU⟩ := hS.exists_extension
  have hcont : ∀ᶠ p in 𝓝 q, ContinuousAt S.toFun p := by
    filter_upwards [hU.mem_nhds (hAU hq)] with p hp
    exact hSU.continuousOn.continuousAt (hU.mem_nhds hp)
  let F : ℝ × ℝ → E := fun p => extChartAt I (S.toFun q) (S.toFun p)
  let DF : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E) := fun p => fderiv ℝ F p
  let D2F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E := fderiv ℝ DF q
  have hr1 : (1 : ℕ∞ω) ≤ r := le_trans (by norm_num) hr
  have hF : ∀ᶠ p in 𝓝 q, HasFDerivAt F (DF p) p := by
    simpa only [F, DF] using
      hS.eventually_hasFDerivAt_extChartAt hr1 hq
        (mem_chart_source H (S.toFun q))
  have hF2 : HasFDerivAt DF D2F q := by
    simpa only [F, DF, D2F] using
      hS.hasFDerivAt_fderiv_extChartAt hr hq
        (mem_chart_source H (S.toFun q))
  simpa only [Prod.eta] using
    S.covariantDerivativeUOfVelocityV_eq_covariantDerivativeVOfVelocityU_of_hasFDerivAt
      g (S.toFun q) DF D2F (u₀ := q.1) (v₀ := q.2)
        (by simpa only [Prod.eta] using hcont)
        (by simpa only [Prod.eta] using (mem_chart_source H (S.toFun q)))
        (by simpa only [F, Prod.eta] using hF)
        (by simpa only [Prod.eta] using hF2)

end Boundaryless

end ParametrizedSurface

namespace IntrinsicParametrizedSurface

variable [I.Boundaryless]

/-- **Math.** The intrinsic `u`-slice velocity of a faithful parametrized
surface. -/
def velocityU (S : IntrinsicParametrizedSurface (I := I) (M := M))
    (q : ℝ × ℝ) : TangentSpace I (S q) :=
  S.toParametrizedSurface.velocityU q

/-- **Math.** The intrinsic `v`-slice velocity of a faithful parametrized
surface. -/
def velocityV (S : IntrinsicParametrizedSurface (I := I) (M := M))
    (q : ℝ × ℝ) : TangentSpace I (S q) :=
  S.toParametrizedSurface.velocityV q

/-- **Math.** The intrinsic mixed derivative `D/du (ds/dv)` of a faithful
parametrized surface. -/
def covariantDerivativeUOfVelocityV
    (g : RiemannianMetric I M)
    (S : IntrinsicParametrizedSurface (I := I) (M := M)) (q : ℝ × ℝ) :
    TangentSpace I (S q) :=
  S.toParametrizedSurface.covariantDerivativeUOfVelocityV g q

/-- **Math.** The intrinsic mixed derivative `D/dv (ds/du)` of a faithful
parametrized surface. -/
def covariantDerivativeVOfVelocityU
    (g : RiemannianMetric I M)
    (S : IntrinsicParametrizedSurface (I := I) (M := M)) (q : ℝ × ℝ) :
    TangentSpace I (S q) :=
  S.toParametrizedSurface.covariantDerivativeVOfVelocityU g q

/-- **Math.** do Carmo Ch. 3, Lemma 3.4 for the faithful intrinsic surface
type: the two mixed Levi-Civita covariant derivatives agree at every point of
the parameter domain. -/
theorem mixedCovariantDerivatives_commute
    (g : RiemannianMetric I M)
    (S : IntrinsicParametrizedSurface (I := I) (M := M))
    {q : ℝ × ℝ} (hq : q ∈ S.domain) :
    S.covariantDerivativeUOfVelocityV g q =
      S.covariantDerivativeVOfVelocityU g q := by
  exact S.toParametrizedSurface
    |>.covariantDerivativeUOfVelocityV_eq_covariantDerivativeVOfVelocityU
      g S.regularity.toExtended (WithTop.coe_le_coe.mpr le_top) hq

end IntrinsicParametrizedSurface

end Geodesic
end Riemannian
