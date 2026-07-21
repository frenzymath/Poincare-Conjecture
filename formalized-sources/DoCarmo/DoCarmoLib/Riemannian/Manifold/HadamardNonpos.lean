import DoCarmoLib.Riemannian.Jacobi.JacobiNonpositiveManifold
import DoCarmoLib.Riemannian.Manifold.HadamardPoleClosure

/-!
# do Carmo Ch. 7 — the Cartan–Hadamard theorem, modulo global smoothness of `exp_p`

`thm:dc-ch7-3-1` (Cartan–Hadamard) and the local-diffeomorphism half of `lem:dc-ch7-3-2`,
assembled from the two already-landed halves of the Hadamard machine:

* the **differential of `exp_p` is a linear isomorphism** at every `v` under `K ≤ 0`
  (`expDifferential_isEquiv_of_nonpos`, `JacobiNonpositiveManifold.lean` — the Jacobi-field
  energy content of `lem:dc-ch7-3-2`: no conjugate points ⟹ `d(exp_p)_v` invertible), and
* the **poles / covering-space assembly** upgrading a smooth local diffeomorphism `exp_p` on a
  complete simply connected manifold to a diffeomorphism `T_pM ≃ M`
  (`expDiffeomorphOfPole_of_pole`, `HadamardPoleClosure.lean`, do Carmo `rem:dc-ch7-3-4`).

## The one remaining input: global `C^∞` smoothness of `exp_p`

The bridge between the two is the observation that a globally `C^∞` map whose differential is a
linear isomorphism at a point is a `C^∞` local diffeomorphism there (the manifold inverse
function theorem `isLocalDiffeomorphAt_of_mfderiv_equiv`, applied here through an arbitrary target
chart via `isLocalDiffeomorphAt_of_hasFDerivAt_equiv`). The differential-isomorphism is supplied
by `expDifferential_isEquiv_of_nonpos`. The remaining ingredient is the **global `C^∞`
smoothness** of the exponential map, `ContMDiff 𝓘(ℝ,E) I ∞ (expMapGlobal g hg p)`.

This is a standard consequence of the smooth dependence of the geodesic flow on its initial
conditions. That theorem is **not in mathlib** — mathlib's ODE library provides only *Lipschitz*
dependence of the solution on the initial condition (`Mathlib.Analysis.ODE.PicardLindelof`) and
`C^n` regularity in *time* (`ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt`) — and DoCarmoLib
currently establishes it only to `C¹`/`C²` on small balls (`FlowC1Dependence`, `FlowC2Dependence`,
`C2LocalDiffeo`). We therefore carry it as an explicit hypothesis `hsmooth`, isolating it as the
**sole** obstruction between the present state and a fully unconditional Cartan–Hadamard theorem:
everything else — the differential isomorphism, the inverse function theorem, and the entire
covering-space upgrade — is proved here.

Blueprint: `lem:dc-ch7-3-2`, `thm:dc-ch7-3-1`, `rem:dc-ch7-3-4`.
Reference: do Carmo, *Riemannian Geometry*, Ch. 7, §3.
-/

open Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian Riemannian.Geodesic Riemannian.Exponential Riemannian.HadamardModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M]

/-! ### `exp_p` is a `C^∞` local diffeomorphism at each `v` (given global smoothness) -/

/-- **Math.** **do Carmo `lem:dc-ch7-3-2` (local-diffeomorphism form), pointwise.** On a complete
manifold of nonpositive curvature, if `exp_p` is globally `C^∞` then it is a `C^∞` local
diffeomorphism **at** every `v ∈ T_pM`.

The differential `d(exp_p)_v` is a continuous linear isomorphism (`expDifferential_isEquiv_of_nonpos`,
the Jacobi/energy half of `lem:dc-ch7-3-2`): concretely, some target chart `ζ` reads `exp_p` as a
map with **strict** Fréchet derivative the isomorphism `D` at `v`. That chart reading is `C^∞` on
an open neighbourhood of `v` (from `hsmooth`), so the normed-space inverse function theorem makes
it a local diffeomorphism; composing with the chart inverse `(extChartAt I ζ).symm` (itself a local
diffeomorphism) recovers `exp_p`.

The global-smoothness hypothesis `hsmooth` is the sole non-`\leanok` input; see the module header. -/
theorem isLocalDiffeomorphAt_expMapGlobal_of_nonpos
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) (v : E)
    (hsmooth : ContMDiff 𝓘(ℝ, E) I ∞ (fun w : E => expMapGlobal (I := I) g hg p w))
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (fun w : E => expMapGlobal (I := I) g hg p w) v := by
  classical
  obtain ⟨ζ, D, hζ, hFD⟩ := expDifferential_isEquiv_of_nonpos (I := I) g hg p v hK
  set f : E → M := fun w : E => expMapGlobal (I := I) g hg p w with hfdef
  set gζ : E → E := fun w => extChartAt I ζ (f w) with hgζdef
  have hsrc : f v ∈ (extChartAt I ζ).source := by
    rw [extChartAt_source]; exact hζ
  set s : Set E := f ⁻¹' (extChartAt I ζ).source with hsdef
  have hs_open : IsOpen s :=
    hsmooth.continuous.isOpen_preimage _ (isOpen_extChartAt_source ζ)
  have hvs : v ∈ s := hsrc
  have hmaps : Set.MapsTo f s (chartAt H ζ).source := by
    intro w hw
    rw [← extChartAt_source (I := I)]; exact hw
  -- the target-chart reading of `exp_p` is `C^∞` on `s`
  have hgζ_cd : ContDiffOn ℝ ∞ gζ s := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_extChartAt (I := I) (x := ζ)).comp hsmooth.contMDiffOn hmaps
  -- and has the isomorphism `D` as its (strict, hence Fréchet) derivative at `v`
  have hFD' : HasFDerivAt gζ (D : E →L[ℝ] E) v := hFD.hasFDerivAt
  -- normed-space inverse function theorem: the reading is a local diffeomorphism at `v`
  have hg_ld : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ gζ v :=
    isLocalDiffeomorphAt_of_hasFDerivAt_equiv hs_open hvs hgζ_cd hFD'
  -- the chart inverse is a local diffeomorphism at `gζ v`
  have htgt : gζ v ∈ (extChartAt I ζ).target := PartialEquiv.map_source _ hsrc
  have hc2 : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (extChartAt I ζ).symm (gζ v) :=
    isLocalDiffeomorphAt_extChartAt_symm htgt
  have hcomp : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ ((extChartAt I ζ).symm ∘ gζ) v := hc2.comp hg_ld
  -- and `(extChartAt I ζ).symm ∘ gζ = exp_p` near `v`
  refine IsLocalDiffeomorphAt.congr_of_eventuallyEq hcomp ?_
  filter_upwards [hs_open.mem_nhds hvs] with w hw
  show f w = (extChartAt I ζ).symm (gζ w)
  exact ((extChartAt I ζ).left_inv hw).symm

/-! ### `exp_p` is a `C^∞` local diffeomorphism on `T_pM`, as a map out of `HadamardModel E` -/

/-- **Math.** **do Carmo `lem:dc-ch7-3-2` (global local-diffeomorphism form).** On a complete
manifold of nonpositive curvature, if `exp_p` is globally `C^∞`, then `exp_p : T_pM → M` — viewed
as the map out of the manifold `HadamardModel E` consumed by the poles theorem — is a `C^∞` local
diffeomorphism. Assembles the pointwise `isLocalDiffeomorphAt_expMapGlobal_of_nonpos` with the fact
that `toModel : HadamardModel E → E` is a diffeomorphism (its identity chart). -/
theorem isLocalDiffeomorph_expMapGlobal_hadamard_of_nonpos
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M)
    (hsmooth : ContMDiff 𝓘(ℝ, E) I ∞ (fun w : E => expMapGlobal (I := I) g hg p w))
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    IsLocalDiffeomorph 𝓘(ℝ, E) I ∞
      (fun v : HadamardModel E => expMapGlobal (I := I) g hg p (HadamardModel.toModel v)) := by
  intro v
  -- `toModel` is the identity chart of `HadamardModel E`, hence a local diffeomorphism at `v`
  have htoModel : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (HadamardModel.toModel (E := E)) v := by
    refine IsLocalDiffeomorphAt.congr_of_eventuallyEq
      (isLocalDiffeomorphAt_extChartAt (I := 𝓘(ℝ, E)) (x := v)) ?_
    filter_upwards with y
    exact (HadamardModel.extChartAt_hadamard v y).symm
  exact (isLocalDiffeomorphAt_expMapGlobal_of_nonpos g hg p (HadamardModel.toModel v) hsmooth hK).comp
    htoModel

/-! ### The Cartan–Hadamard theorem -/

/-- **Math.** **do Carmo Ch. 7, Theorem 3.1 (Cartan–Hadamard), modulo global smoothness of
`exp_p`.** Let `M` be a complete, simply connected Riemannian manifold of nonpositive sectional
curvature (`K ≤ 0`, in the operator form `0 ≤ ⟨R(a,c)c, a⟩`). If `exp_p` is globally `C^∞`, then
`exp_p : T_pM → M` is a **diffeomorphism**; in particular `M` is diffeomorphic to `ℝⁿ`.

Feeds the local-diffeomorphism `isLocalDiffeomorph_expMapGlobal_hadamard_of_nonpos`
(`lem:dc-ch7-3-2`) into the poles/covering assembly `expDiffeomorphOfPole_of_pole`
(`rem:dc-ch7-3-4`), which discharges the ray-geodesic input internally. The only non-`\leanok`
hypothesis is `hsmooth`; see the module header. -/
def hadamardDiffeomorphOfNonpos
    [ConnectedSpace M] [SimplyConnectedSpace M] [LocPathConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M)
    (hsmooth : ContMDiff 𝓘(ℝ, E) I ∞ (fun w : E => expMapGlobal (I := I) g hg p w))
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    Diffeomorph 𝓘(ℝ, E) I (HadamardModel E) M ∞ :=
  HadamardModel.expDiffeomorphOfPole_of_pole g hg p
    (isLocalDiffeomorph_expMapGlobal_hadamard_of_nonpos g hg p hsmooth hK)

/-- **Math.** The Cartan–Hadamard diffeomorphism **is** `exp_p` itself (anti-vacuity guard): it is
`exp_p`, upgraded to a diffeomorphism, not a new map. -/
theorem hadamardDiffeomorphOfNonpos_coe
    [ConnectedSpace M] [SimplyConnectedSpace M] [LocPathConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M)
    (hsmooth : ContMDiff 𝓘(ℝ, E) I ∞ (fun w : E => expMapGlobal (I := I) g hg p w))
    (hK : ∀ x : M, ∀ a c : TangentSpace I x,
      0 ≤ g.metricInner x (g.leviCivitaConnection.curvatureOperatorAt x a c c) a) :
    ⇑(hadamardDiffeomorphOfNonpos g hg p hsmooth hK)
      = fun v : HadamardModel E => expMapGlobal (I := I) g hg p (HadamardModel.toModel v) := rfl

end Riemannian.Jacobi

end
