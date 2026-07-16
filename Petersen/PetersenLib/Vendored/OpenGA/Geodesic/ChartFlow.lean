/- Vendored from DoCarmo `OpenGALib/Riemannian/Geodesic/ChartFlow.lean`. Namespace `Riemannian` mapped to
   `PetersenLib`; engineering infrastructure only, not a blueprint node. -/
import PetersenLib.Vendored.OpenGA.Geodesic.InitialVelocity

set_option linter.unusedSectionVars false

/-!
# The chart-`p` geodesic flow: spray in chart coordinates and transfer of solutions

The geodesic spray of `(M, g)` fixed in the chart at `p` has, in the tangent-bundle
chart at `⟨p, 0⟩`, the coordinate expression

`F(x, w) = (w, -Γ_p(w, w)(x))  :  E × E → E × E`

(`geodesicSprayCoord g p`). This file makes the passage between solutions of the
genuine ODE `z' = F(z)` on the model space `E × E` and geodesic witnesses on `M`
usable in both directions, with quantitative chart control:

* `extChartAt_tangent_target` / `extChartAt_tangent_source` — the tangent-bundle
  chart at `⟨p, 0⟩` has target `(extChartAt I p).target ×ˢ univ` and source the
  chart-`p` spray domain.
* `contDiffOn_geodesicSprayCoord_prod` — the coordinate spray is `C^∞` on the
  chart target, by reading the (already established) smoothness of the
  chart-fixed spray on `TM` through the chart.
* `isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord` — **chart solutions descend
  to geodesic witnesses**: a solution `z` of `z' = F(z)` on an open `J ∋ 0` with
  values in the chart target and `z 0 = (φ_p(p), v)` projects to a geodesic
  witness with initial data `(p, v)` whose foot stays in the chart at `p`, and
  whose chart reading is `(z t).1`. This is do Carmo's local construction of
  geodesics from the first-order system (Ch. 3, §2.5), run through mathlib's
  construction of manifold integral curves from Picard–Lindelöf chart solutions.
* `maximalGeodesic_eq_witness_of_mem_chart` — **the canonical maximal geodesic
  agrees with any witness whose own foot stays in the chart**, unconditionally:
  unlike `maximalGeodesic_eq_witness`, no chart-validity clause quantified over
  all witnesses is required, because the clopen uniqueness propagation
  (`IsGeodesicOnWithInitial.eqOn`) only constrains its first curve.
* `maximalGeodesic_eq_of_hasDerivAt_sprayCoord` /
  `extChartAt_maximalGeodesic_of_hasDerivAt_sprayCoord` — the combination: the
  canonical maximal geodesic through `(p, v)` is computed, on the interval of
  any in-chart solution of the coordinate spray ODE, by that solution; in
  particular its chart reading is `(z t).1`, and the solution interval is
  contained in the maximal interval.

These are the inputs for uniform-time existence and for the strict
differentiability of the exponential map (do Carmo Ch. 3, Prop. 2.7 and 2.9).
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace PetersenLib
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section ChartTarget

variable [I.Boundaryless]

/-- **Math.** The tangent-bundle chart at a basepoint over `p` has target the product
of the base chart target with the full fibre: `φ_{⟨p,0⟩}(TM) = φ_p(U_p) × E`. -/
lemma extChartAt_tangent_target (p : M) :
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target =
      (extChartAt I p).target ×ˢ (univ : Set E) := by
  rw [FiberBundle.extChartAt_target]
  congr 1
  refine inter_eq_left.mpr ?_
  intro y hy
  rw [mem_preimage, TangentBundle.trivializationAt_baseSet, ← extChartAt_source I]
  exact (extChartAt I p).map_target hy

/-- **Math.** The tangent-bundle chart at a basepoint over `p` has source the
chart-`p` spray domain: the tangent vectors whose foot lies in the chart at `p`. -/
lemma extChartAt_tangent_source (p : M) :
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).source =
      geodesicChartDomain (I := I) p := by
  ext q
  rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
  exact Iff.rfl

/-- **Math.** The tangent-bundle chart target at `⟨p, 0⟩` is open (the base chart
target is open on a boundaryless manifold, and the fibre factor is everything). -/
lemma isOpen_extChartAt_tangent_target (p : M) :
    IsOpen (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
  rw [extChartAt_tangent_target]
  exact (isOpen_extChartAt_target p).prod isOpen_univ

/-- **Math.** Reading a tangent vector through the tangent-bundle chart at `⟨p, 0⟩`
and back: the foot of `φ_{⟨p,0⟩}⁻¹(ζ)` has chart-`p` image the first component of
`ζ`, for `ζ` in the chart target. -/
lemma extChartAt_proj_extChartAt_tangent_symm (p : M) {ζ : E × E}
    (hζ : ζ ∈ (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target) :
    extChartAt I p
        (((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm ζ).proj) =
      ζ.1 := by
  set Ψ := extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) with hΨ
  have hsrc : Ψ.symm ζ ∈ Ψ.source := Ψ.map_target hζ
  have hfoot : (Ψ.symm ζ).proj ∈
      (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    have := (extChartAt_tangent_source (I := I) p) ▸ hsrc
    exact proj_mem_chartAt_source_of_mem_geodesicChartDomain (I := I) this
  have happ := extChartAt_tangent_apply (I := I)
    (⟨p, (0 : E)⟩ : TangentBundle I M) (r := Ψ.symm ζ) hfoot
  have hri : Ψ (Ψ.symm ζ) = ζ := Ψ.right_inv hζ
  rw [← hΨ] at happ
  rw [happ] at hri
  exact congrArg Prod.fst hri

/-- **Math.** The foot of a chart-read tangent vector stays in the chart at `p`:
for `ζ` in the tangent-bundle chart target, the foot of `φ_{⟨p,0⟩}⁻¹(ζ)` lies in
the chart source at `p`. -/
lemma proj_extChartAt_tangent_symm_mem_chartAt_source (p : M) {ζ : E × E}
    (hζ : ζ ∈ (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target) :
    (((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm ζ).proj) ∈
      (chartAt H p).source := by
  have hsrc := (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).map_target hζ
  rw [extChartAt_tangent_source (I := I) p] at hsrc
  exact proj_mem_chartAt_source_of_mem_geodesicChartDomain (I := I) hsrc

/-- **Math.** The tangent-bundle chart at `⟨p, 0⟩` sends the initial point `⟨p, v⟩`
to `(φ_p(p), v)`; equivalently, its inverse sends `(φ_p(p), v)` back to `⟨p, v⟩`. -/
lemma extChartAt_tangent_symm_mk (p : M) (v : TangentSpace I p) :
    (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        (extChartAt I p p, v) = (⟨p, v⟩ : TangentBundle I M) := by
  set Ψ := extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) with hΨ
  have hbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H p
  have happ : Ψ (⟨p, v⟩ : TangentBundle I M) = (extChartAt I p p, v) := by
    have := extChartAt_tangent_apply (I := I)
      (⟨p, (0 : E)⟩ : TangentBundle I M) (r := (⟨p, v⟩ : TangentBundle I M)) hbase
    rw [← hΨ] at this
    rw [this]
    congr 1
    exact chartFiberCoord_mk (I := I) p v
  have hsrc : (⟨p, v⟩ : TangentBundle I M) ∈ Ψ.source := by
    rw [hΨ, extChartAt_tangent_source (I := I) p]
    exact mem_geodesicChartDomain_of_proj (mem_chart_source H p)
  have hli := Ψ.left_inv hsrc
  rw [happ] at hli
  exact hli

end ChartTarget

section SprayCoordSmooth

variable [I.Boundaryless]

/-- **Math.** On the tangent-bundle chart target, the coordinate spray
`(x, w) ↦ (w, -Γ_p(w, w)(x))` is the chart-fixed spray fibre read through the
chart: `F = (geodesicVectorFieldChartFiber g p) ∘ φ_{⟨p,0⟩}⁻¹`. -/
lemma geodesicSprayCoord_eqOn_chartFiber_comp (g : RiemannianMetric I M) (p : M) :
    EqOn (fun ζ : E × E => geodesicSprayCoord (I := I) g p ζ.1 ζ.2)
      (geodesicVectorFieldChartFiber (I := I) g p ∘
        (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm)
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
  intro ζ hζ
  set Ψ := extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) with hΨ
  have hsrc : Ψ.symm ζ ∈ Ψ.source := Ψ.map_target hζ
  have hdom : Ψ.symm ζ ∈ geodesicChartDomain (I := I) p := by
    rw [hΨ, extChartAt_tangent_source (I := I) p] at hsrc
    exact hsrc
  have hfoot : (Ψ.symm ζ).proj ∈
      (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact proj_mem_chartAt_source_of_mem_geodesicChartDomain (I := I) hdom
  have happ := extChartAt_tangent_apply (I := I)
    (⟨p, (0 : E)⟩ : TangentBundle I M) (r := Ψ.symm ζ) hfoot
  rw [← hΨ] at happ
  have hri : Ψ (Ψ.symm ζ) = ζ := Ψ.right_inv hζ
  rw [happ] at hri
  show geodesicSprayCoord (I := I) g p ζ.1 ζ.2 =
    geodesicVectorFieldChartFiber (I := I) g p (Ψ.symm ζ)
  rw [geodesicVectorFieldChartFiber_eq_sprayCoord (I := I) g p (Ψ.symm ζ)]
  have h1 : extChartAt I p ((Ψ.symm ζ)).proj = ζ.1 := congrArg Prod.fst hri
  have h2 : chartFiberCoord (I := I) p (Ψ.symm ζ) = ζ.2 := congrArg Prod.snd hri
  rw [h1, h2]

/-- **Math.** **Smoothness of the coordinate geodesic spray.** The map
`(x, w) ↦ (w, -Γ_p(w, w)(x)) : E × E → E × E` is `C^∞` on the chart target
`φ_p(U_p) × E`: it is the chart reading of the chart-fixed spray fibre on `TM`,
which is smooth on the spray domain. -/
theorem contDiffOn_geodesicSprayCoord_prod (g : RiemannianMetric I M) (p : M) :
    ContDiffOn ℝ ∞ (fun ζ : E × E => geodesicSprayCoord (I := I) g p ζ.1 ζ.2)
      ((extChartAt I p).target ×ˢ (univ : Set E)) := by
  rw [← extChartAt_tangent_target (I := I) p]
  set Ψ := extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M) with hΨ
  have hsymm : ContMDiffOn 𝓘(ℝ, E × E) I.tangent ∞ Ψ.symm Ψ.target :=
    contMDiffOn_extChartAt_symm (⟨p, (0 : E)⟩ : TangentBundle I M)
  have hfiber : ContMDiffOn I.tangent 𝓘(ℝ, E × E) ∞
      (geodesicVectorFieldChartFiber (I := I) g p)
      (geodesicChartDomain (I := I) p) :=
    geodesicVectorFieldChartFiber_contMDiffOn (I := I) g p
  have hmaps : MapsTo Ψ.symm Ψ.target (geodesicChartDomain (I := I) p) := by
    intro ζ hζ
    have := Ψ.map_target hζ
    rwa [hΨ, extChartAt_tangent_source (I := I) p] at this
  have hcomp : ContMDiffOn 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) ∞
      (geodesicVectorFieldChartFiber (I := I) g p ∘ Ψ.symm) Ψ.target :=
    hfiber.comp hsymm hmaps
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp.congr fun ζ hζ =>
    geodesicSprayCoord_eqOn_chartFiber_comp (I := I) g p hζ

end SprayCoordSmooth

section ReverseBridge

variable [I.Boundaryless]

/-- **Math.** **Chart solutions of the spray ODE are integral curves of the
chart-fixed spray.** If `z : ℝ → E × E` solves `z' = (z₂, -Γ_p(z₂, z₂)(z₁))` on an
open set `J` with values in the tangent-bundle chart target at `⟨p, 0⟩`, then
`t ↦ φ_{⟨p,0⟩}⁻¹(z t)` is an integral curve of the chart-`p` geodesic spray on `J`.
This is the reverse of the chart reading `eventually_hasDerivAt_geodesic_reading`,
following mathlib's construction of integral curves from chart ODE solutions. -/
theorem isMIntegralCurveOn_extChartAt_tangent_symm
    (g : RiemannianMetric I M) (p : M) {z : ℝ → E × E} {J : Set ℝ}
    (hd : ∀ t ∈ J, HasDerivAt z (geodesicSprayCoord (I := I) g p (z t).1 (z t).2) t)
    (hmem : ∀ t ∈ J, z t ∈
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target) :
    IsMIntegralCurveOn
      (fun t => (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm (z t))
      (geodesicVectorFieldChart (I := I) g p) J := by
  set b₀ : TangentBundle I M := ⟨p, (0 : E)⟩ with hb₀
  set Ψ := extChartAt I.tangent b₀ with hΨ
  intro t ht
  set q : TangentBundle I M := Ψ.symm (z t) with hq
  have hζ : z t ∈ Ψ.target := hmem t ht
  have hq_src : q ∈ Ψ.source := Ψ.map_target hζ
  have hq_dom : q ∈ geodesicChartDomain (I := I) p := by
    rw [hq]
    have := hq_src
    rwa [hΨ, hb₀, extChartAt_tangent_source (I := I) p] at this
  have hq_foot : q.proj ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact proj_mem_chartAt_source_of_mem_geodesicChartDomain (I := I) hq_dom
  have hΨq : Ψ q = z t := Ψ.right_inv hζ
  -- the chart derivative, rewritten as the coordinate change of the spray
  have h : HasDerivAt z
      (tangentCoordChange I.tangent q b₀ q
        (geodesicVectorFieldChart (I := I) g p q)) t := by
    have hval : tangentCoordChange I.tangent q b₀ q
        (geodesicVectorFieldChart (I := I) g p q) =
        geodesicSprayCoord (I := I) g p (z t).1 (z t).2 := by
      rw [hb₀]
      rw [tangentCoordChange_geodesicVectorFieldChart (I := I) g p (0 : E) hq_dom]
      rw [geodesicVectorFieldChartFiber_eq_sprayCoord (I := I) g p q]
      have happ := extChartAt_tangent_apply (I := I) b₀ (r := q) hq_foot
      rw [← hΨ] at happ
      rw [happ] at hΨq
      have h1 : extChartAt I p q.proj = (z t).1 := congrArg Prod.fst hΨq
      have h2 : chartFiberCoord (I := I) p q = (z t).2 := congrArg Prod.snd hΨq
      rw [h1, h2]
    rw [hval]
    exact hd t ht
  -- membership facts for the coordinate-change composition
  have hq_self : q ∈ (extChartAt I.tangent q).source := mem_extChartAt_source q
  -- assemble the manifold derivative, following mathlib's integral-curve construction
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hζ).comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I.tangent q ∘ Ψ.symm) ∘ z)
    (geodesicVectorFieldChart (I := I) g p q) t
  rw [← tangentCoordChange_self (I := I.tangent) (x := q) (z := q)
      (v := geodesicVectorFieldChart (I := I) g p q) hq_self,
    ← tangentCoordChange_comp (x := b₀) ⟨⟨hq_self, hq_src⟩, hq_self⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I.tangent) _ <|
    mem_nhds_iff.mpr ⟨Ψ.target,
      extChartAt_target_subset_range b₀,
      isOpen_extChartAt_tangent_target (I := I) p, hζ⟩
  rw [← Ψ.right_inv hζ]
  exact hasFDerivWithinAt_tangentCoordChange ⟨hq_src, hq_self⟩

/-- **Math.** **Chart solutions descend to geodesic witnesses.** A solution
`z : ℝ → E × E` of the coordinate spray ODE on an open `J ∋ 0` with values in the
tangent-bundle chart target and initial value `z 0 = (φ_p(p), v)` projects to a
geodesic witness with initial data `(p, v)`, whose foot stays in the chart at `p`
and whose chart-`p` reading is `t ↦ (z t).1` (do Carmo Ch. 3, §2.5). -/
theorem isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {z : ℝ → E × E} {J : Set ℝ}
    (hz0 : z 0 = (extChartAt I p p, v))
    (hd : ∀ t ∈ J, HasDerivAt z (geodesicSprayCoord (I := I) g p (z t).1 (z t).2) t)
    (hmem : ∀ t ∈ J, z t ∈
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target) :
    IsGeodesicOnWithInitial (I := I) g
      (fun t =>
        ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm (z t)).proj)
      J p v ∧
    (∀ t ∈ J,
      ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm (z t)).proj ∈
        (chartAt H p).source) ∧
    (∀ t ∈ J, extChartAt I p
        (((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm (z t)).proj) =
      (z t).1) := by
  refine ⟨⟨fun t =>
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm (z t),
      fun t => rfl, ?_, isMIntegralCurveOn_extChartAt_tangent_symm (I := I) g p hd hmem⟩,
    fun t ht => proj_extChartAt_tangent_symm_mem_chartAt_source (I := I) p (hmem t ht),
    fun t ht => extChartAt_proj_extChartAt_tangent_symm (I := I) p (hmem t ht)⟩
  show (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm (z 0) = _
  rw [hz0]
  exact extChartAt_tangent_symm_mk (I := I) p v

end ReverseBridge

section UnconditionalValue

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The canonical maximal geodesic agrees with any in-chart witness,
unconditionally.** If `γ₀` is a geodesic witness with initial data `(p, v)` on an
open preconnected `J₀ ∋ 0` whose own foot stays in the chart at `p`, then the
canonical maximal geodesic equals `γ₀` on `J₀`. In contrast to
`maximalGeodesic_eq_witness`, no chart-validity clause about *all* witnesses is
needed: the clopen uniqueness propagation only constrains the given witness. -/
theorem maximalGeodesic_eq_witness_of_mem_chart
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {γ₀ : ℝ → M} {J₀ : Set ℝ}
    (hγ₀ : IsGeodesicOnWithInitial (I := I) g γ₀ J₀ p v)
    (hJo : IsOpen J₀) (hJc : IsPreconnected J₀) (h0 : (0 : ℝ) ∈ J₀)
    (hsrc₀ : ∀ t ∈ J₀, γ₀ t ∈ (chartAt H p).source)
    {s : ℝ} (hs : s ∈ J₀) :
    maximalGeodesic (I := I) g p v s = γ₀ s := by
  classical
  have hmem : s ∈ maximalGeodesicInterval (I := I) g p v :=
    ⟨γ₀, J₀, hJo, hJc, h0, hs, hγ₀⟩
  rw [maximalGeodesic_of_mem (I := I) hmem]
  obtain ⟨J₁, hJ₁o, hJ₁c, h0₁, hs₁, hγ₁⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p v hmem
  have heq := IsGeodesicOnWithInitial.eqOn (I := I) hγ₀ hγ₁
    (hJo.inter hJ₁o)
    ((hJc.ordConnected.inter hJ₁c.ordConnected).isPreconnected)
    ⟨h0, h0₁⟩ inter_subset_left inter_subset_right
    (fun t ht => hsrc₀ t (inter_subset_left ht))
  exact (heq ⟨hs, hs₁⟩).symm

/-- **Math.** The interval of any geodesic witness is contained in the maximal
interval. -/
theorem subset_maximalGeodesicInterval_of_witness
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {γ₀ : ℝ → M} {J₀ : Set ℝ}
    (hγ₀ : IsGeodesicOnWithInitial (I := I) g γ₀ J₀ p v)
    (hJo : IsOpen J₀) (hJc : IsPreconnected J₀) (h0 : (0 : ℝ) ∈ J₀) :
    J₀ ⊆ maximalGeodesicInterval (I := I) g p v :=
  fun _ hs => ⟨γ₀, J₀, hJo, hJc, h0, hs, hγ₀⟩

/-- **Math.** **The canonical maximal geodesic is computed by chart solutions of the
spray ODE.** If `z` solves the coordinate spray ODE on an open preconnected
`J ∋ 0` inside the chart target with `z 0 = (φ_p(p), v)`, then on `J` the
canonical maximal geodesic through `(p, v)` is the projection of `φ_{⟨p,0⟩}⁻¹ ∘ z`;
in particular `J` is contained in the maximal interval, and the chart-`p` reading
of the maximal geodesic on `J` is `t ↦ (z t).1`. -/
theorem maximalGeodesic_eq_of_hasDerivAt_sprayCoord
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {z : ℝ → E × E} {J : Set ℝ}
    (hJ : IsOpen J) (hJc : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hz0 : z 0 = (extChartAt I p p, v))
    (hd : ∀ t ∈ J, HasDerivAt z (geodesicSprayCoord (I := I) g p (z t).1 (z t).2) t)
    (hmem : ∀ t ∈ J, z t ∈
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target)
    {s : ℝ} (hs : s ∈ J) :
    maximalGeodesic (I := I) g p v s =
      ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm (z s)).proj := by
  obtain ⟨hwit, hsrc, -⟩ :=
    isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord (I := I) g p v hz0 hd hmem
  exact maximalGeodesic_eq_witness_of_mem_chart (I := I) hwit hJ hJc h0J hsrc hs

/-- **Math.** The chart-`p` reading of the canonical maximal geodesic along a chart
solution of the spray ODE: `φ_p(γ(s, p, v)) = (z s).1` on the solution interval. -/
theorem extChartAt_maximalGeodesic_of_hasDerivAt_sprayCoord
    {g : RiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {z : ℝ → E × E} {J : Set ℝ}
    (hJ : IsOpen J) (hJc : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hz0 : z 0 = (extChartAt I p p, v))
    (hd : ∀ t ∈ J, HasDerivAt z (geodesicSprayCoord (I := I) g p (z t).1 (z t).2) t)
    (hmem : ∀ t ∈ J, z t ∈
      (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target)
    {s : ℝ} (hs : s ∈ J) :
    extChartAt I p (maximalGeodesic (I := I) g p v s) = (z s).1 := by
  rw [maximalGeodesic_eq_of_hasDerivAt_sprayCoord (I := I)
    hJ hJc h0J hz0 hd hmem hs]
  exact extChartAt_proj_extChartAt_tangent_symm (I := I) p (hmem s hs)

end UnconditionalValue

end Geodesic
end PetersenLib
