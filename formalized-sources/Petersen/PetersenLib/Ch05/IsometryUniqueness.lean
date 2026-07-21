import PetersenLib.Ch05.LocalIsometryGeodesics
import PetersenLib.Ch05.UniformInjectivityRadiusDiffeo

/-!
# Petersen Ch. 5, §5.6.1 — a local isometry is determined by its 1-jet at one point

`prop:pet-ch5-isometry-uniqueness` (Petersen Prop. 5.6.2): two local Riemannian
isometries `F, G : (M, g_M) → (N, g_N)` out of a connected manifold that agree at
one point `p` together with their differentials there are equal.

The proof is Petersen's connectedness argument.  The agreement set

  `A = {x | F x = G x and DF_x = DG_x}`

is packaged through the **tangent map** rather than through `mfderiv`, as
`A = {x | ∀ v, Tf F ⟨x, v⟩ = Tf G ⟨x, v⟩}`: the map `x ↦ mfderiv I I' F x` into
`E →L[ℝ] E'` is not continuous (it is read in the charts at `x` and `F x`, which
jump with `x`), whereas `tangentMap` is continuous
(`ContMDiff.continuous_tangentMap`) because the bundle topology absorbs the chart
twisting.  Closedness of `A` then follows from openness of `{z | Tf F z ≠ Tf G z}`
and openness of the bundle projection (`FiberBundle.isOpenMap_proj`).

Openness of `A` is exponential naturality (`localIsometry_expNaturality`,
Prop. 5.6.1 (2)) together with the fact that a small exponential ball around `x`
is a neighbourhood of `x` (`compactSet_uniformCInftyDiffeo` at the compact set
`{x}`): on that ball `F` and `G` agree, and on the interior of `{F = G}` the
differentials agree for free (`Filter.EventuallyEq.mfderiv_eq`) — this is what
discharges the differential clause that Petersen's proof glosses over.

As in `PetersenLib/Ch05/LocalIsometryGeodesics.lean` and
`PetersenLib/Ch05/UniformInjectivityRadius.lean`, the exponential map used here is
the **intrinsic** moving-foot maximal geodesic `geodesicMaximalCurve g x v` at
time `1`, never `PetersenLib.expMap` / `expDomain`, whose chart-anchored domains
are artifacts.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open Bundle Manifold Set Filter Function

open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [CompleteSpace E'] [T2Space (TangentBundle I' M')] [T2Space M']

/-- **Math.** The constant curve at `p` realises the geodesic initial datum
`(p, 0)` at every time: it is a geodesic (`Geodesic.isGeodesic_const`) with zero
initial velocity. -/
theorem isGeodesicWithInitialOn_const (g : RiemannianMetric I M) (p : M) :
    IsGeodesicWithInitialOn (I := I) g (fun _ : ℝ => p) Set.univ 0 p
      (0 : TangentSpace I p) :=
  ⟨continuous_const.continuousOn, rfl,
    by simpa using hasDerivAt_const (0 : ℝ) (extChartAt I p p),
    fun t _ => Geodesic.isGeodesic_const (I := I) g p t⟩

/-- **Math.** The maximal geodesic with zero initial velocity is the constant
curve at its foot; in particular the intrinsic exponential map at `p` sends the
zero vector to `p`. -/
theorem geodesicMaximalCurve_zero (g : RiemannianMetric I M) (p : M) (t : ℝ) :
    geodesicMaximalCurve (I := I) g p (0 : TangentSpace I p) t = p :=
  geodesicMaximalCurve_eqOn (I := I) g isOpen_univ Set.ordConnected_univ
    (Set.mem_univ 0) (isGeodesicWithInitialOn_const (I := I) g p) (Set.mem_univ t)

variable {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {F G : M → M'}

/-- **Math.** The intrinsic exponential image of a small `g`-ball at `x` is a
neighbourhood of `x`: it is open (`compactSet_uniformCInftyDiffeo` at `{x}`) and
contains `x = exp_x 0`.  The accompanying clause records that `exp_x v` is defined
(time `1` lies in the maximal domain) for every `v` in that ball. -/
theorem exists_isOpen_image_geodesicMaximalCurve_mem_nhds (g : RiemannianMetric I M)
    (x : M) :
    ∃ ε > (0 : ℝ),
      (∀ v : TangentSpace I x, g.metricInner x v v < ε ^ 2 →
          (1 : ℝ) ∈ geodesicMaximalDomain (I := I) g x v) ∧
        (fun v : TangentSpace I x => geodesicMaximalCurve (I := I) g x v 1) ''
          {v : TangentSpace I x | g.metricInner x v v < ε ^ 2} ∈ 𝓝 x := by
  obtain ⟨ε, hε, hspec⟩ :=
    compactSet_uniformCInftyDiffeo (I := I) g (isCompact_singleton (x := x))
  obtain ⟨hdom, -, -, hopen, -⟩ := hspec x rfl
  refine ⟨ε, hε, hdom, hopen.mem_nhds ⟨(0 : TangentSpace I x), ?_, ?_⟩⟩
  · show g.metricInner x 0 0 < ε ^ 2
    rw [g.metricInner_zero_left]
    positivity
  · exact geodesicMaximalCurve_zero (I := I) g x 1

/-- **Math.** Petersen Ch. 5, Prop. 5.6.2 (`prop:pet-ch5-isometry-uniqueness`):
a local Riemannian isometry out of a **connected** manifold is uniquely
determined by its value and its differential at a single point.  If `F` and `G`
are local Riemannian isometries `(M, g_M) → (N, g_N)` with `F p = G p` and
`DF_p = DG_p`, then `F = G`.

The set on which the two 1-jets agree is nonempty by hypothesis, closed by
continuity of the tangent maps, and open by naturality of the exponential map
(`localIsometry_expNaturality`); connectedness finishes. -/
theorem localIsometry_uniquelyDeterminedByOnePoint [PreconnectedSpace M]
    (hF : IsLocalRiemannianIsometry gM gN F) (hG : IsLocalRiemannianIsometry gM gN G)
    (p : M) (hp : F p = G p) (hdp : mfderiv I I' F p = mfderiv I I' G p) :
    F = G := by
  set A : Set M := {x : M | ∀ v : TangentSpace I x,
    tangentMap I I' F ⟨x, v⟩ = tangentMap I I' G ⟨x, v⟩} with hA
  have hmem : ∀ x : M, x ∈ A ↔ (F x = G x ∧ mfderiv I I' F x = mfderiv I I' G x) := by
    intro x
    constructor
    · intro hx
      have h0 := hx 0
      have hbase : F x = G x := by
        have := congrArg Bundle.TotalSpace.proj h0
        simpa [tangentMap] using this
      refine ⟨hbase, ?_⟩
      ext v
      have hv := hx v
      simp only [tangentMap] at hv
      have h2 := congrArg Bundle.TotalSpace.snd hv
      simpa [hbase] using h2
    · rintro ⟨h1, h2⟩ v
      simp only [tangentMap]
      congr 1
      exact DFunLike.congr_fun h2 v
  have hpA : p ∈ A := (hmem p).2 ⟨hp, hdp⟩
  have hclosed : IsClosed A := by
    have hcF : Continuous (tangentMap I I' F) :=
      hF.contMDiff.continuous_tangentMap (by simp)
    have hcG : Continuous (tangentMap I I' G) :=
      hG.contMDiff.continuous_tangentMap (by simp)
    have hEopen : IsOpen {z : TangentBundle I M |
        tangentMap I I' F z ≠ tangentMap I I' G z} :=
      isOpen_ne_fun hcF hcG
    have hproj : IsOpenMap (Bundle.TotalSpace.proj :
        TangentBundle I M → M) := FiberBundle.isOpenMap_proj E (TangentSpace I)
    have hcompl : Aᶜ = (Bundle.TotalSpace.proj) ''
        {z : TangentBundle I M | tangentMap I I' F z ≠ tangentMap I I' G z} := by
      ext x
      simp only [hA, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, Set.mem_image]
      constructor
      · rintro ⟨v, hv⟩; exact ⟨⟨x, v⟩, hv, rfl⟩
      · rintro ⟨⟨y, v⟩, hv, rfl⟩; exact ⟨v, hv⟩
    rw [← isOpen_compl_iff, hcompl]
    exact hproj _ hEopen
  have hcong : ∀ {q q' : M'} (w : TangentSpace I' q) (w' : TangentSpace I' q'),
      q = q' → (w : E') = (w' : E') →
      geodesicMaximalCurve (I := I') gN q w 1
        = geodesicMaximalCurve (I := I') gN q' w' 1 := by
    intro q q' w w' hq hw
    subst hq
    exact congrArg (fun u : TangentSpace I' q => geodesicMaximalCurve (I := I') gN q u 1) hw
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨hFx, hdFx⟩ := (hmem x).1 hx
    obtain ⟨ε, hε, hdom, hball⟩ :=
      exists_isOpen_image_geodesicMaximalCurve_mem_nhds (I := I) gM x
    have hsub : (fun v : TangentSpace I x => geodesicMaximalCurve (I := I) gM x v 1) ''
        {v : TangentSpace I x | gM.metricInner x v v < ε ^ 2} ⊆ {y : M | F y = G y} := by
      rintro _ ⟨v, hv, rfl⟩
      have h1 : (1 : ℝ) ∈ geodesicMaximalDomain (I := I) gM x v := hdom v hv
      show F (geodesicMaximalCurve (I := I) gM x v 1)
        = G (geodesicMaximalCurve (I := I) gM x v 1)
      rw [(localIsometry_expNaturality hF x v).2 1 h1,
        (localIsometry_expNaturality hG x v).2 1 h1]
      exact hcong _ _ hFx (DFunLike.congr_fun hdFx v)
    have hS : {y : M | F y = G y} ∈ 𝓝 x := Filter.mem_of_superset hball hsub
    have hint : interior {y : M | F y = G y} ⊆ A := by
      intro y hy
      have hyeq : F y = G y := by have h := interior_subset hy; simpa using h
      have hev : F =ᶠ[𝓝 y] G :=
        Filter.eventually_of_mem (isOpen_interior.mem_nhds hy)
          (fun z hz => by have h := interior_subset hz; simpa using h)
      exact (hmem y).2 ⟨hyeq, hev.mfderiv_eq⟩
    exact Filter.mem_of_superset (interior_mem_nhds.2 hS) hint
  have huniv : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨p, hpA⟩
  funext x
  exact ((hmem x).1 (huniv ▸ Set.mem_univ x)).1

end PetersenLib

end
