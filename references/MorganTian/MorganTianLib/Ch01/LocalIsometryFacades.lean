import DoCarmoLib.Riemannian.Manifold.LocalIsometryRigidity
import DoCarmoLib.Riemannian.Manifold.CoveringMapConclusion
import DoCarmoLib.Riemannian.Geodesic.HopfRinow
import DoCarmoLib.Riemannian.Geodesic.ClosedSubmanifoldComplete
import DoCarmoLib.Riemannian.Exponential.GlobalExp

/-!
# Local-isometry facades for Morgan--Tian Chapter 1

The chapter's local-isometry definition is represented by the existing do Carmo
notion `DCPreservesMetric`, together with the local-diffeomorphism clause which
the inverse-function theorem supplies in the equidimensional case.  The
wrappers below keep that representation at the Morgan--Tian boundary and do
not introduce a second metric API.

The geodesic, length, and rigidity statements are direct consequences of the
DoCarmo development.  The covering statement records the metric hypotheses
needed by the formal Hopf--Rinow/covering assembly (`g.IsRiemannianDist` and
properness of the source); this is the precise formal strengthening of the
chapter's informal phrase "complete Riemannian manifold".

The model spaces are shared by source and target, as in the DoCarmo transfer
API.  A general equal-dimensional statement can be obtained by transporting
along a linear equivalence of models, but that transport is not part of the
chapter facade.
-/

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

noncomputable section

namespace MorganTianLib

namespace LocalIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'} [I'.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]

/-! ### Definition -/

/-- **Math.** A smooth equidimensional map is a **local isometry** when it is a local
diffeomorphism and its differential preserves the Riemannian inner products.

This is the formal version of `def:local-isometry`; `DCPreservesMetric` is
exactly the pullback-metric clause. -/
def IsLocalIsometry (gN : Riemannian.RiemannianMetric I N)
    (gM : Riemannian.RiemannianMetric I' M) (F : N → M) : Prop :=
  IsLocalDiffeomorph I I' ∞ F ∧ Riemannian.DCPreservesMetric gN gM F

/-- **Math.** A (global) isometry is a bijective local isometry. -/
def IsIsometry (gN : Riemannian.RiemannianMetric I N)
    (gM : Riemannian.RiemannianMetric I' M) (F : N → M) : Prop :=
  Function.Bijective F ∧ IsLocalIsometry gN gM F

variable {gN : Riemannian.RiemannianMetric I N}
  {gM : Riemannian.RiemannianMetric I' M} {F : N → M}

/-! The chapter defines a local isometry first as a smooth metric-preserving map and
then invokes the inverse function theorem to obtain local diffeomorphisms.  The
working predicate above stores that derived local-diffeomorphism clause, so the
following bridge records the equivalence rather than hiding it in the definition. -/

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** A smooth equidimensional map preserving the Riemannian metric is a
local isometry.  Positive definiteness makes its differential injective; finite
dimensionality upgrades this to a continuous linear equivalence, and the
DoCarmo manifold inverse-function theorem supplies the local diffeomorphism. -/
theorem IsLocalIsometry.of_contMDiff_preservesMetric
    (hF : ContMDiff I I' ∞ F)
    (hpres : Riemannian.DCPreservesMetric gN gM F) :
    IsLocalIsometry gN gM F := by
  have hAinj : ∀ p : N, Function.Injective (mfderiv I I' F p) := by
    intro p u v huv
    have hzero : mfderiv I I' F p (u - v) = 0 := by
      calc
        mfderiv I I' F p (u - v) =
            mfderiv I I' F p u - mfderiv I I' F p v := map_sub _ _ _
        _ = 0 := by rw [huv, sub_self]
    have hinner : gN.metricInner p (u - v) (u - v) = 0 := by
      calc
        gN.metricInner p (u - v) (u - v) =
            gM.metricInner (F p)
              (mfderiv I I' F p (u - v))
              (mfderiv I I' F p (u - v)) := hpres p (u - v) (u - v)
        _ = 0 := by rw [hzero]; simp
    have huv0 : u - v = 0 := by
      by_contra hne
      exact (not_lt_of_ge hinner.le)
        (gN.metricInner_self_pos p (u - v) hne)
    exact sub_eq_zero.mp huv0
  refine ⟨?_, hpres⟩
  intro p
  let A : E →L[ℝ] E := mfderiv I I' F p
  have hbij : Function.Bijective (A : E →ₗ[ℝ] E) := by
    refine ⟨hAinj p, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp (hAinj p)
  let e : E ≃L[ℝ] E :=
    (LinearEquiv.ofBijective (A : E →ₗ[ℝ] E) hbij).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E) = mfderiv I I' F p := by
    change (e : E →L[ℝ] E) = A
    ext u
    rfl
  exact Riemannian.isLocalDiffeomorphAt_of_mfderiv_equiv hF he.symm

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** For smooth maps between equal-dimensional Riemannian manifolds,
`IsLocalIsometry` is equivalent to the pullback-metric condition. -/
theorem isLocalIsometry_iff_contMDiff_preservesMetric
    (hF : ContMDiff I I' ∞ F) :
    IsLocalIsometry gN gM F ↔ Riemannian.DCPreservesMetric gN gM F := by
  constructor
  · exact And.right
  · exact IsLocalIsometry.of_contMDiff_preservesMetric hF

/-! ### Geodesics and length -/

omit [CompleteSpace E] in
/-- **Math.** A local isometry carries a geodesic on an open set of times to a
geodesic on the same set of times. -/
theorem IsLocalIsometry.isGeodesicOn_comp
    (hF : IsLocalIsometry gN gM F) {γ : ℝ → N} {s : Set ℝ}
    (hs : IsOpen s) (hγc : ContinuousOn γ s)
    (hγ : Riemannian.Geodesic.IsGeodesicOn (I := I) gN γ s) :
    Riemannian.Geodesic.IsGeodesicOn (I := I') gM (fun t => F (γ t)) s := by
  letI : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) :=
    ⟨gN.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) :=
    ⟨gM.toRiemannianMetric⟩
  exact Riemannian.Geodesic.isGeodesicOn_comp_of_isLocalDiffeomorph
    hF.1 gN gM hF.2 hs hγc hγ

omit [CompleteSpace E] in
/-- **Math.** A local isometry carries a continuous geodesic curve on an open
set of times to a continuous geodesic curve on the same set. -/
theorem IsLocalIsometry.isGeodesicCurveOn_comp
    (hF : IsLocalIsometry gN gM F) {γ : ℝ → N} {s : Set ℝ}
    (hs : IsOpen s)
    (hγ : Riemannian.Geodesic.IsGeodesicCurveOn (I := I) gN γ s) :
    Riemannian.Geodesic.IsGeodesicCurveOn (I := I') gM (fun t => F (γ t)) s := by
  exact ⟨hF.1.contMDiff.continuous.comp_continuousOn hγ.1,
    hF.isGeodesicOn_comp hs hγ.1 hγ.2⟩

/-- **Math.** A local isometry carries a global geodesic to a global geodesic. -/
theorem IsLocalIsometry.isGeodesic_comp
    (hF : IsLocalIsometry gN gM F) {γ : ℝ → N}
    (hγc : Continuous γ) (hγ : Riemannian.Geodesic.IsGeodesic (I := I) gN γ) :
    Riemannian.Geodesic.IsGeodesic (I := I') gM (fun t => F (γ t)) :=
  by
    letI : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) :=
      ⟨gN.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) :=
      ⟨gM.toRiemannianMetric⟩
    exact Riemannian.Geodesic.isGeodesic_comp_of_isLocalDiffeomorph
      hF.1 gN gM hF.2 hγc hγ

/-- **Math.** Exponential-map naturality for a local isometry with complete
source.  Besides the endpoint identity, the first conjunct records that the
target exponential is genuinely defined at the transported vector; this is
essential because `expMapIntrinsic` has a conventional value off its domain.
-/
theorem IsLocalIsometry.expMapIntrinsic_naturality_of_complete
    [CompleteSpace N] (hgN : gN.IsRiemannianDist)
    (hF : IsLocalIsometry gN gM F) (x : N) (v : TangentSpace I x) (t : ℝ) :
    t • mfderiv I I' F x v ∈
        Riemannian.Exponential.expDomainIntrinsic (I := I') gM (F x) ∧
      F (Riemannian.Exponential.expMapIntrinsic (I := I) gN x (t • v)) =
        Riemannian.Exponential.expMapIntrinsic (I := I') gM (F x)
          (t • mfderiv I I' F x v) := by
  letI : Bundle.RiemannianBundle (fun y : N ↦ TangentSpace I y) :=
    ⟨gN.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun y : M ↦ TangentSpace I' y) :=
    ⟨gM.toRiemannianMetric⟩
  let γ : ℝ → N :=
    Riemannian.Geodesic.globalGeodesic (I := I) gN hgN x (t • v)
  let δ : ℝ → M := fun s => F (γ s)
  have hγ0 : γ 0 = x :=
    Riemannian.Geodesic.globalGeodesic_zero gN hgN x (t • v)
  have hγv : HasDerivAt
      (Riemannian.Geodesic.chartReading (I := I) x γ) ((t • v : TangentSpace I x) : E) 0 :=
    Riemannian.Geodesic.hasDerivAt_chartReading_globalGeodesic gN hgN x (t • v)
  have hγc : Continuous γ :=
    Riemannian.Geodesic.continuous_globalGeodesic gN hgN x (t • v)
  have hγgeo : Riemannian.Geodesic.IsGeodesic (I := I) gN γ :=
    Riemannian.Geodesic.isGeodesic_globalGeodesic gN hgN x (t • v)
  have hδc : Continuous δ := hF.1.contMDiff.continuous.comp hγc
  have hδgeo : Riemannian.Geodesic.IsGeodesic (I := I') gM δ :=
    hF.isGeodesic_comp hγc hγgeo
  have hδ0 : δ 0 = F x := by
    simp only [δ, hγ0]
  have hdiff : MDifferentiableAt I I' F x :=
    hF.1.contMDiff.contMDiffAt.mdifferentiableAt (by norm_num)
  have hδvRaw : HasDerivAt
      (fun s => extChartAt I' (F x) (F (γ s)))
      (mfderiv I I' F x (t • v)) 0 :=
    Riemannian.hasDerivAt_extChartAt_comp_of_hasFDerivAt_mapReading
      (Riemannian.hasFDerivAt_mapReading_self hdiff) hγ0 hγc.continuousAt hγv
  have hδv : HasDerivAt
      (Riemannian.Geodesic.chartReading (I := I') (F x) δ)
      ((t • mfderiv I I' F x v : TangentSpace I' (F x)) : E) 0 := by
    have hfun : Riemannian.Geodesic.chartReading (I := I') (F x) δ =
        fun s => extChartAt I' (F x) (F (γ s)) := by
      funext s
      rfl
    rw [hfun]
    simpa only [map_smul] using hδvRaw
  have hδinit : Riemannian.Geodesic.IsIntrinsicGeodesicOnWithInitial
      (I := I') gM δ Set.univ (F x) (t • mfderiv I I' F x v) :=
    ⟨hδ0, hδv, hδc.continuousOn, hδgeo.isGeodesicOn Set.univ⟩
  have htarget :
      Riemannian.Exponential.expMapIntrinsic (I := I') gM (F x)
          (t • mfderiv I I' F x v) = δ 1 :=
    Riemannian.Exponential.expMapIntrinsic_eq_of_witness gM
      isOpen_univ isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ 1) hδinit
  have hsource :
      Riemannian.Exponential.expMapIntrinsic (I := I) gN x (t • v) = γ 1 := by
    rw [Riemannian.Exponential.expMapIntrinsic_eq_expMapGlobal]
    rfl
  constructor
  · exact ⟨δ, Set.univ, isOpen_univ, isPreconnected_univ,
      Set.mem_univ 0, Set.mem_univ 1, hδinit⟩
  · calc
      F (Riemannian.Exponential.expMapIntrinsic (I := I) gN x (t • v)) =
          F (γ 1) := congrArg F hsource
      _ = δ 1 := rfl
      _ = Riemannian.Exponential.expMapIntrinsic (I := I') gM (F x)
          (t • mfderiv I I' F x v) := htarget.symm

/-- **Math.** A local isometry preserves the Riemannian path length of every `C¹` curve. -/
theorem IsLocalIsometry.pathELength_comp_eq
    (hF : IsLocalIsometry gN gM F) {γ : ℝ → N} {a b : ℝ}
    (hγ₁ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    letI : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) :=
      ⟨gN.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) :=
      ⟨gM.toRiemannianMetric⟩
    Manifold.pathELength I γ a b =
      Manifold.pathELength I' (F ∘ γ) a b := by
  letI : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) :=
    ⟨gN.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) :=
    ⟨gM.toRiemannianMetric⟩
  simpa using hF.2.pathELength_comp_eq
    (hF.1.contMDiff.mdifferentiable (by norm_num)) hγ₁

/-! ### Rigidity -/

/-- **Math.** Two local isometries which agree to first order at one point agree
everywhere on a preconnected source. -/
theorem IsLocalIsometry.eq_of_pointDatum
    [PreconnectedSpace N] [T2Space (TangentBundle I' M)]
    {F₁ F₂ : N → M}
    (hF₁ : IsLocalIsometry gN gM F₁) (hF₂ : IsLocalIsometry gN gM F₂)
    (p : N) (hp : F₁ p = F₂ p)
    (hdp : mfderiv I I' F₁ p = mfderiv I I' F₂ p) :
    F₁ = F₂ := by
  letI : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) :=
    ⟨gN.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) :=
    ⟨gM.toRiemannianMetric⟩
  exact Riemannian.eq_of_pointDatum_of_localIsometry
    gN gM hF₁.1 hF₂.1 hF₁.2 hF₂.2 p hp hdp

/-! ### Coverings -/

/-- **Math.** A proper source plus the DoCarmo metric hypotheses turns a local isometry
into a covering map. -/
theorem IsLocalIsometry.isCoveringMap_of_proper
    [ProperSpace N]
    (hgN : gN.IsRiemannianDist) (hF : IsLocalIsometry gN gM F) :
    IsCoveringMap F :=
  (hF.2.dcExpandsMetric).isCoveringMap hgN hF.1

/-- **Math.** A local isometry from a nonempty proper source onto a
preconnected target is surjective. -/
theorem IsLocalIsometry.surjective_of_proper
    [ProperSpace N] [Nonempty N] [PreconnectedSpace M]
    (hgN : gN.IsRiemannianDist) (hF : IsLocalIsometry gN gM F) :
    Function.Surjective F :=
  (hF.2.dcExpandsMetric).surjective hgN hF.1

/-- **Math.** Complete connected source form of the covering theorem.  The explicit
`ConnectedSpace N` and `IsRiemannianDist` assumptions are what allow
Hopf--Rinow to manufacture the `ProperSpace N` instance consumed above. -/
theorem IsLocalIsometry.isCoveringMap_of_complete
    [ConnectedSpace N] [CompleteSpace N]
    (hgN : gN.IsRiemannianDist) (hF : IsLocalIsometry gN gM F) :
    IsCoveringMap F := by
  let p : N := Classical.choice (inferInstance : Nonempty N)
  letI : ProperSpace N :=
    Riemannian.Geodesic.properSpace_of_geodesicallyComplete_at
      gN hgN p ((Riemannian.Geodesic.isGeodesicallyComplete_of_complete gN hgN) p)
  exact hF.isCoveringMap_of_proper hgN

/-- **Math.** A local isometry from a complete connected source to a
connected target is a surjective covering map. -/
theorem IsLocalIsometry.surjectiveCovering_of_complete
    [ConnectedSpace N] [CompleteSpace N] [ConnectedSpace M]
    (hgN : gN.IsRiemannianDist) (hF : IsLocalIsometry gN gM F) :
    Function.Surjective F ∧ IsCoveringMap F := by
  let p : N := Classical.choice (inferInstance : Nonempty N)
  letI : ProperSpace N :=
    Riemannian.Geodesic.properSpace_of_geodesicallyComplete_at
      gN hgN p ((Riemannian.Geodesic.isGeodesicallyComplete_of_complete gN hgN) p)
  exact ⟨hF.surjective_of_proper hgN, hF.isCoveringMap_of_proper hgN⟩

end LocalIsometry

end MorganTianLib
