import MorganTianLib.Ch01.HopfRinow
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Path
import Mathlib.Order.Zorn

/-!
# Morgan--Tian Chapter 5: convergence foundations

This module records the source definitions whose formal content is independent
of the still-missing Hamilton--Cheeger compactness and pointed-limit producers.
The definitions are deliberately generic over metric spaces; geometric and
Ricci-flow instances are supplied only when the corresponding upstream
theorems are available.
-/

open Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal unitInterval

namespace MorganTianLib

universe u

/-! ## Geometric convergence: the regular-locus and exhaustion data -/

/-- **Math.** A point is `δ`-regular when every ball of radius less than `δ`
has compact closure.  This is the metric-topological part of
`def:delta-regular-point`; the exponential-map equivalence belongs to the
geodesic completeness producer. -/
def IsDeltaRegular {X : Type*} [MetricSpace X] (δ : ℝ) (p : X) : Prop :=
  ∀ r : ℝ, r < δ → IsCompact (closure (Metric.ball p r))

/-- **Math.** The intrinsic exponential-map formulation of regularity: every
tangent vector of Riemannian norm less than `δ` lies in the natural domain of
the exponential map at `p`. -/
def IsIntrinsicExpRegularAt
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    (g : Riemannian.RiemannianMetric I' M) (δ : ℝ) (p : M) : Prop :=
  {v : TangentSpace I' p | Real.sqrt (g.metricInner p v v) < δ} ⊆
    Riemannian.Exponential.expDomainIntrinsic g p

theorem IsIntrinsicExpRegularAt.mono
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    {g : Riemannian.RiemannianMetric I' M} {p : M}
    {δ₁ δ₂ : ℝ} (hδ : δ₂ ≤ δ₁)
    (hregular : IsIntrinsicExpRegularAt g δ₁ p) :
    IsIntrinsicExpRegularAt g δ₂ p := by
  intro v hv
  exact hregular (lt_of_lt_of_le hv hδ)

theorem IsIntrinsicExpRegularAt.mem_expDomainIntrinsic
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    {g : Riemannian.RiemannianMetric I' M} {p : M} {δ : ℝ}
    (hregular : IsIntrinsicExpRegularAt g δ p) {v : TangentSpace I' p}
    (hv : Real.sqrt (g.metricInner p v v) < δ) :
    v ∈ Riemannian.Exponential.expDomainIntrinsic g p :=
  hregular hv

/-- **Math.** Completeness makes the intrinsic exponential map defined on the
whole tangent space, hence gives exponential regularity at every scale. -/
theorem isIntrinsicExpRegularAt_of_completeRiemannian
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    [CompleteSpace M]
    (g : Riemannian.RiemannianMetric I' M) (hg : g.IsRiemannianDist)
    (δ : ℝ) (p : M) :
    IsIntrinsicExpRegularAt g δ p := by
  rw [IsIntrinsicExpRegularAt,
    Riemannian.Geodesic.expDomainIntrinsic_eq_univ_of_complete g hg p]
  exact Set.subset_univ _

@[simp]
theorem isDeltaRegular_zero {X : Type*} [MetricSpace X] (p : X) :
    IsDeltaRegular 0 p := by
  intro r hr
  rw [Metric.ball_eq_empty.mpr hr.le, closure_empty]
  exact isCompact_empty

theorem IsDeltaRegular.mono {X : Type*} [MetricSpace X] {p : X}
    {δ₁ δ₂ : ℝ} (hδ : δ₂ ≤ δ₁) (hp : IsDeltaRegular δ₁ p) :
    IsDeltaRegular δ₂ p := by
  intro r hr
  exact hp r (lt_of_lt_of_le hr hδ)

/-- **Math.** Every point of a proper metric space is regular at every finite scale. -/
theorem isDeltaRegular_of_properSpace {X : Type*} [MetricSpace X]
    [ProperSpace X] (δ : ℝ) (p : X) :
    IsDeltaRegular δ p := by
  intro r _
  exact (isCompact_closedBall p r).of_isClosed_subset
    isClosed_closure Metric.closure_ball_subset_closedBall

/-- **Math.** The regular locus at scale `δ`. -/
def regLocus {X : Type*} [MetricSpace X] (δ : ℝ) : Set X :=
  {p | IsDeltaRegular δ p}

theorem regLocus_eq_univ_of_properSpace {X : Type*} [MetricSpace X]
    [ProperSpace X] (δ : ℝ) :
    regLocus (X := X) δ = Set.univ := by
  ext p
  simp [regLocus, isDeltaRegular_of_properSpace]

/-! The metric-topological closedness argument for the regular locus. -/

theorem isClosed_regLocus {X : Type*} [MetricSpace X]
    (δ : ℝ) : IsClosed (regLocus (X := X) δ) := by
  rw [isClosed_iff_nhds]
  intro p hp r hr
  by_cases hδr : δ ≤ r
  · have hrnonpos : r ≤ 0 := by linarith
    rw [Metric.ball_eq_empty.mpr hrnonpos, closure_empty]
    exact isCompact_empty
  · have hε : 0 < (δ - r) / 2 := by linarith
    have hball : Metric.ball p ((δ - r) / 2) ∈ 𝓝 p :=
      Metric.ball_mem_nhds p hε
    obtain ⟨q, hqball, hqreg⟩ := hp (Metric.ball p ((δ - r) / 2)) hball
    have hpq : dist p q < (δ - r) / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hqball
    have hsubset : closure (Metric.ball p r) ⊆
        closure (Metric.ball q ((δ + r) / 2)) := by
      apply closure_mono
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      calc
        dist y q ≤ dist y p + dist p q := dist_triangle _ _ _
        _ < r + (δ - r) / 2 := add_lt_add hy hpq
        _ = (δ + r) / 2 := by ring
    exact (hqreg ((δ + r) / 2) (by linarith)).of_isClosed_subset
      isClosed_closure hsubset

/-- **Math.** The component-based regular locus used by the source definition. -/
def regComponent {X : Type*} [MetricSpace X] (δ : ℝ) (x : X) : Set X :=
  connectedComponentIn (regLocus δ) x

theorem mem_regComponent {X : Type*} [MetricSpace X]
    {δ : ℝ} {x : X} (hx : IsDeltaRegular δ x) :
    x ∈ regComponent δ x :=
  mem_connectedComponentIn hx

theorem regComponent_subset_regLocus {X : Type*} [MetricSpace X]
    (δ : ℝ) (x : X) :
    regComponent δ x ⊆ regLocus δ :=
  connectedComponentIn_subset _ _

theorem isPreconnected_regComponent {X : Type*} [MetricSpace X]
    (δ : ℝ) (x : X) :
    IsPreconnected (regComponent δ x) :=
  isPreconnected_connectedComponentIn

theorem regComponent_eq_univ_of_properSpace {X : Type*} [MetricSpace X]
    [ProperSpace X] [ConnectedSpace X] (δ : ℝ) (x : X) :
    regComponent δ x = Set.univ := by
  rw [regComponent, regLocus_eq_univ_of_properSpace,
    connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]

theorem isDeltaRegular_mem_regLocus {X : Type*} [MetricSpace X]
    {δ : ℝ} {p : X} : IsDeltaRegular δ p ↔ p ∈ regLocus δ :=
  Iff.rfl

theorem isDeltaRegular_mem_regComponent {X : Type*} [MetricSpace X]
    {δ : ℝ} {x p : X} (hp : p ∈ regComponent δ x) :
    IsDeltaRegular δ p :=
  regComponent_subset_regLocus δ x hp

/-- **Math.** On a connected complete Riemannian manifold, Hopf--Rinow makes every
point regular at every scale. -/
theorem isDeltaRegular_of_completeRiemannian
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    [ConnectedSpace M] [CompleteSpace M]
    (g : Riemannian.RiemannianMetric I' M) (hg : g.IsRiemannianDist)
    (δ : ℝ) (p : M) :
    IsDeltaRegular δ p := by
  letI : ProperSpace M := hopfRinow_properSpace g hg p
  exact isDeltaRegular_of_properSpace δ p

/-- **Math.** On a connected complete Riemannian manifold, compact-ball and
intrinsic-exponential regularity are equivalent at every scale. -/
theorem isDeltaRegular_iff_isIntrinsicExpRegularAt_of_completeRiemannian
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    [ConnectedSpace M] [CompleteSpace M]
    (g : Riemannian.RiemannianMetric I' M) (hg : g.IsRiemannianDist)
    (δ : ℝ) (p : M) :
    IsDeltaRegular δ p ↔ IsIntrinsicExpRegularAt g δ p := by
  exact ⟨fun _ => isIntrinsicExpRegularAt_of_completeRiemannian g hg δ p,
    fun _ => isDeltaRegular_of_completeRiemannian g hg δ p⟩

/-- **Math.** The fixed-radius endpoint needs only the two metric consequences used by
the proof: completeness for the intrinsic exponential domain and properness
for compact metric balls.  Keeping these instances explicit makes the local
equivalence available without silently deriving either one from a stronger
global manifold hypothesis. -/
theorem isDeltaRegular_iff_isIntrinsicExpRegularAt_of_complete_and_proper
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    [CompleteSpace M] [ProperSpace M]
    (g : Riemannian.RiemannianMetric I' M) (hg : g.IsRiemannianDist)
    (δ : ℝ) (p : M) :
    IsDeltaRegular δ p ↔ IsIntrinsicExpRegularAt g δ p := by
  constructor
  · intro _
    exact isIntrinsicExpRegularAt_of_completeRiemannian g hg δ p
  · intro _
    exact isDeltaRegular_of_properSpace δ p

/-! The scale-uniform exponential formulation is the non-vacuous local
completeness bridge behind the source's delta-regular equivalence. -/

/-- **Math.** Intrinsic exponential regularity at every scale is equivalent to
geodesic completeness at the chosen point.  The converse direction uses the
genuine intrinsic exponential domain, rather than a chart-dependent surrogate. -/
theorem isIntrinsicExpRegularAt_all_iff_isGeodesicallyCompleteAt
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    (g : Riemannian.RiemannianMetric I' M) (p : M) :
    (∀ δ : ℝ, IsIntrinsicExpRegularAt g δ p) ↔
      Riemannian.Geodesic.IsGeodesicallyCompleteAt g p := by
  constructor
  · intro hregular
    apply (Riemannian.Geodesic.expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt
      g p).mp
    apply Set.eq_univ_of_forall
    intro v
    have hnorm : Real.sqrt (g.metricInner p v v) <
        Real.sqrt (g.metricInner p v v) + 1 := by
      linarith
    exact hregular (Real.sqrt (g.metricInner p v v) + 1) hnorm
  · intro hcomplete δ
    rw [IsIntrinsicExpRegularAt,
      (Riemannian.Geodesic.expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt
        g p).mpr hcomplete]
    exact Set.subset_univ _

/-- **Math.** At a geodesically complete point of a connected Riemannian
manifold, metric delta-regularity and intrinsic exponential regularity agree at
each scale.  Hopf--Rinow supplies the proper metric space structure used by the
metric formulation. -/
theorem isDeltaRegular_iff_isIntrinsicExpRegularAt_of_geodesicallyComplete
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    [ConnectedSpace M]
    (g : Riemannian.RiemannianMetric I' M) (hg : g.IsRiemannianDist)
    (δ : ℝ) (p : M)
    (hcomplete : Riemannian.Geodesic.IsGeodesicallyCompleteAt g p) :
    IsDeltaRegular δ p ↔ IsIntrinsicExpRegularAt g δ p := by
  have hexp : Riemannian.Exponential.expDomainIntrinsic g p = Set.univ :=
    (Riemannian.Geodesic.expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt
      g p).mpr hcomplete
  letI : CompleteSpace M :=
    Riemannian.Geodesic.complete_of_expDomainIntrinsic_eq_univ g hg p hexp
  letI : ProperSpace M := hopfRinow_properSpace g hg p
  constructor
  · intro _
    exact isIntrinsicExpRegularAt_of_completeRiemannian g hg δ p
  · intro _
    exact isDeltaRegular_of_properSpace δ p

/-- **Math.** Regularity at every positive scale around one point forces the
metric space to be proper.  Compactness of a closed ball of radius `n` is
obtained from the regularity of the slightly larger open ball. -/
theorem properSpace_of_isDeltaRegular_all
    {X : Type*} [MetricSpace X] {p : X}
    (hregular : ∀ δ : ℝ, 0 < δ → IsDeltaRegular δ p) :
    ProperSpace X := by
  refine ProperSpace.of_seq_closedBall (x := p)
      (r := fun n : ℕ => (n : ℝ)) tendsto_natCast_atTop_atTop ?_
  exact Filter.Eventually.of_forall (fun n => by
    have hcompact : IsCompact (closure
        (Metric.ball p ((n : ℝ) + 1))) :=
      hregular ((n : ℝ) + 2) (by positivity) ((n : ℝ) + 1) (by linarith)
    exact hcompact.of_isClosed_subset Metric.isClosed_closedBall
      ((Metric.closedBall_subset_ball (x := p)
        (ε₁ := (n : ℝ)) (ε₂ := (n : ℝ) + 1) (by linarith)).trans
        subset_closure))

/-- **Math.** The source delta-regular condition at every positive scale is
equivalent to global intrinsic exponential-domain completeness at the base
point.  This is the scale-uniform form of the local exponential equivalence. -/
theorem isDeltaRegular_all_iff_expDomainIntrinsic_eq_univ
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    [ConnectedSpace M]
    (g : Riemannian.RiemannianMetric I' M) (hg : g.IsRiemannianDist)
    (p : M) :
    (∀ δ : ℝ, 0 < δ → IsDeltaRegular δ p) ↔
      Riemannian.Exponential.expDomainIntrinsic g p = Set.univ := by
  constructor
  · intro hregular
    letI : ProperSpace M := properSpace_of_isDeltaRegular_all hregular
    letI : CompleteSpace M := complete_of_proper
    exact Riemannian.Geodesic.expDomainIntrinsic_eq_univ_of_complete g hg p
  · intro hexp δ hδ
    letI : ProperSpace M :=
      Riemannian.Geodesic.properSpace_of_expDomainIntrinsic_eq_univ g hg p hexp
    exact isDeltaRegular_of_properSpace δ p

/-- **Math.** The same scale-uniform bridge phrased using geodesic completeness. -/
theorem isDeltaRegular_all_iff_isGeodesicallyCompleteAt
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    [ConnectedSpace M]
    (g : Riemannian.RiemannianMetric I' M) (hg : g.IsRiemannianDist)
    (p : M) :
    (∀ δ : ℝ, 0 < δ → IsDeltaRegular δ p) ↔
      Riemannian.Geodesic.IsGeodesicallyCompleteAt g p := by
  rw [isDeltaRegular_all_iff_expDomainIntrinsic_eq_univ g hg p,
    Riemannian.Geodesic.expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt]

/-- **Math.** An exhaustion by relatively compact connected open sets containing
the base point, as in item (1) of `def:geometric-limit`. -/
structure CompactExhaustion (X : Type*) [TopologicalSpace X] (x : X) where
  set : ℕ → Set X
  open_set : ∀ k, IsOpen (set k)
  connected_set : ∀ k, IsPreconnected (set k)
  contains_base : ∀ k, x ∈ set k
  increasing : ∀ {k l}, k ≤ l → set k ⊆ set l
  compact_closure : ∀ k, IsCompact (closure (set k))
  nested_closure : ∀ k, closure (set k) ⊆ set (k + 1)
  union_eq : ⋃ k, set k = Set.univ

/-- **Math.** Regard an exhaustion stage as an open subspace. -/
def CompactExhaustion.opens {X : Type*} [TopologicalSpace X] {x : X}
    (V : CompactExhaustion X x) (k : ℕ) : TopologicalSpace.Opens X :=
  ⟨V.set k, V.open_set k⟩

/-- **Math.** The closures in a source-style exhaustion form Mathlib's compact
exhaustion. -/
def CompactExhaustion.toMathlib {X : Type*} [TopologicalSpace X] {x : X}
    (V : CompactExhaustion X x) : _root_.CompactExhaustion X where
  toFun k := closure (V.set k)
  isCompact' := V.compact_closure
  subset_interior_succ' k :=
    (V.nested_closure k).trans (V.open_set (k + 1)).subset_interior_closure
  iUnion_eq' := by
    apply Set.eq_univ_of_univ_subset
    intro y _
    have hy' : y ∈ ⋃ k, V.set k := by
      rw [V.union_eq]
      exact mem_univ y
    obtain ⟨k, hy⟩ := mem_iUnion.mp hy'
    exact mem_iUnion_of_mem k (subset_closure hy)

theorem CompactExhaustion.mem_some {X : Type*} [TopologicalSpace X] {x : X}
    (V : CompactExhaustion X x) (y : X) : ∃ k, y ∈ V.set k := by
  have hy : y ∈ (⋃ k, V.set k) := by
    rw [V.union_eq]
    exact mem_univ y
  exact mem_iUnion.mp hy

theorem CompactExhaustion.eventually_mem {X : Type*} [TopologicalSpace X]
    {x : X} (V : CompactExhaustion X x) (y : X) :
    ∃ k, ∀ l, k ≤ l → y ∈ V.set l := by
  obtain ⟨k, hk⟩ := V.mem_some y
  refine ⟨k, ?_⟩
  intro l hkl
  exact V.increasing hkl hk

/-- **Math.** Every compact subset is contained in a later open stage of the
exhaustion. -/
theorem CompactExhaustion.compact_subset_some
    {X : Type*} [TopologicalSpace X] {x : X}
    (V : CompactExhaustion X x) {K : Set X} (hK : IsCompact K) :
    ∃ k, K ⊆ V.set k := by
  obtain ⟨k, hk⟩ := V.toMathlib.exists_superset_of_isCompact hK
  exact ⟨k + 1, hk.trans (V.nested_closure k)⟩

/-! The source's partial-limit completion assertion needs an image-coverage
hypothesis.  The literal definition allows arbitrary smooth maps, so no
completion or surjectivity conclusion is derived from smoothness alone. -/

def PartialLimitImageCovers {X Y : Type*} [TopologicalSpace X]
    {x : X} (V : CompactExhaustion X x) (f : X → Y) : Prop :=
  ∀ y : Y, ∃ k, y ∈ f '' V.set k

theorem partialLimit_surjective_of_imageCovers {X Y : Type*}
    [TopologicalSpace X] {x : X} (V : CompactExhaustion X x)
    (f : X → Y) (hcover : PartialLimitImageCovers V f) :
    Function.Surjective f := by
  intro y
  obtain ⟨k, ⟨z, hz, rfl⟩⟩ := hcover y
  exact ⟨z, rfl⟩

theorem partialLimit_imageCovers_of_compactBuffer {X Y : Type*}
    [TopologicalSpace X] {x : X} (V : CompactExhaustion X x)
    (f : X → Y)
    (hbuffer : ∀ y : Y, ∃ k, ∃ z ∈ V.set k, f z = y) :
    PartialLimitImageCovers V f := by
  intro y
  obtain ⟨k, z, hz, hzy⟩ := hbuffer y
  exact ⟨k, ⟨z, hz, hzy⟩⟩

/-- **Math.** Compact-buffer image coverage upgrades an injective partial-limit
map to a bijection.  The coverage hypothesis is the explicit missing
surjectivity clause in the incomplete-limit definition. -/
theorem partialLimit_equiv_of_injective_of_imageCovers
    {X Y : Type*} [TopologicalSpace X] {x : X}
    (V : CompactExhaustion X x) (f : X → Y)
    (hinj : Function.Injective f)
    (hcover : PartialLimitImageCovers V f) :
    ∃ e : X ≃ Y, (e : X → Y) = f := by
  have hsurj : Function.Surjective f :=
    partialLimit_surjective_of_imageCovers V f hcover
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  rfl

/-- **Math.** If the limiting map is an isometry, compact-buffer image coverage
upgrades it to an isometry equivalence. -/
theorem partialLimit_isometryEquiv_of_isometry_of_imageCovers
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {x : X}
    (V : CompactExhaustion X x) (f : X → Y)
    (hf : Isometry f)
    (hcover : PartialLimitImageCovers V f) :
    ∃ e : X ≃ᵢ Y, (e : X → Y) = f := by
  have hsurj : Function.Surjective f :=
    partialLimit_surjective_of_imageCovers V f hcover
  refine ⟨IsometryEquiv.mk' f (Function.surjInv hsurj)
      (Function.surjInv_eq hsurj) hf, ?_⟩
  rfl

/-- **Math.** Metric balls in a connected complete Riemannian manifold are
path connected: a minimizing geodesic from the center stays inside the ball. -/
theorem isPathConnected_ball_of_completeRiemannian
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    [ConnectedSpace M] [CompleteSpace M]
    (g : Riemannian.RiemannianMetric I' M) (hg : g.IsRiemannianDist)
    (x : M) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball x r) := by
  refine ⟨x, Metric.mem_ball_self hr, ?_⟩
  intro y hy
  obtain ⟨γ, hγ0, hγ1, hγgeo, hγdist, _⟩ :=
    hopfRinow_minimizing_geodesic g hg x y
  refine JoinedIn.ofLine hγgeo.1 hγ0 hγ1 ?_
  rintro z ⟨t, ht, rfl⟩
  rw [Metric.mem_ball, ← hγ0, hγdist t ht 0 (by constructor <;> norm_num),
    sub_zero, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left dist_nonneg ht.2).trans_lt (by
    simpa [Metric.mem_ball, dist_comm] using hy)

/-- **Math.** The natural-radius balls centered at a point give the source
compact exhaustion on a connected complete Riemannian manifold. -/
noncomputable def completeRiemannianBallExhaustion
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H]
    {I' : ModelWithCorners ℝ E H} [I'.Boundaryless]
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I' ∞ M]
    [ConnectedSpace M] [CompleteSpace M]
    (g : Riemannian.RiemannianMetric I' M) (hg : g.IsRiemannianDist)
    (x : M) : CompactExhaustion M x := by
  letI : ProperSpace M := hopfRinow_properSpace g hg x
  exact
    { set := fun k => Metric.ball x ((k : ℝ) + 1)
      open_set := fun _ => Metric.isOpen_ball
      connected_set := fun k =>
        (isPathConnected_ball_of_completeRiemannian g hg x (by positivity)).isConnected.isPreconnected
      contains_base := fun k => Metric.mem_ball_self (by positivity)
      increasing := by
        intro k l hkl
        apply Metric.ball_subset_ball
        exact_mod_cast Nat.add_le_add_right hkl 1
      compact_closure := fun k =>
        (isCompact_closedBall x ((k : ℝ) + 1)).of_isClosed_subset
          isClosed_closure Metric.closure_ball_subset_closedBall
      nested_closure := fun k =>
        Metric.closure_ball_subset_closedBall.trans
          (Metric.closedBall_subset_ball (by norm_num))
      union_eq := by
        simpa only [Nat.cast_add, Nat.cast_one] using Metric.iUnion_ball_nat_succ x }

/-- **Math.** A proper metric space whose centered open balls are preconnected
admits the same natural-radius compact exhaustion as a complete Riemannian
manifold.  This adapter isolates the only geometric input needed by the
source-style exhaustion: compactness comes from properness and connectedness
from the supplied ball hypothesis. -/
noncomputable def properBallExhaustion
    {X : Type*} [MetricSpace X] [ProperSpace X]
    (x : X)
    (hball : ∀ r : ℝ, 0 < r → IsPreconnected (Metric.ball x r)) :
    CompactExhaustion X x := by
  exact
    { set := fun k => Metric.ball x ((k : ℝ) + 1)
      open_set := fun _ => Metric.isOpen_ball
      connected_set := fun k => hball ((k : ℝ) + 1) (by positivity)
      contains_base := fun k => Metric.mem_ball_self (by positivity)
      increasing := by
        intro k l hkl
        apply Metric.ball_subset_ball
        exact_mod_cast Nat.add_le_add_right hkl 1
      compact_closure := fun k =>
        (isCompact_closedBall x ((k : ℝ) + 1)).of_isClosed_subset
          isClosed_closure Metric.closure_ball_subset_closedBall
      nested_closure := fun k =>
        Metric.closure_ball_subset_closedBall.trans
          (Metric.closedBall_subset_ball (by norm_num))
      union_eq := by
        simpa only [Nat.cast_add, Nat.cast_one] using Metric.iUnion_ball_nat_succ x }

/-! ## Nets -/

/-- **Math.** A `δ`-net containing the base point and uniformly separated from
itself.  This is the exact two-clause content of `def:delta-net`. -/
def IsDeltaNet {X : Type*} [MetricSpace X] (δ : ℝ) (x : X) (L : Set X) : Prop :=
  x ∈ L ∧ (∀ y : X, ∃ z ∈ L, dist y z < δ) ∧
    ∃ ε > 0, ∀ ⦃u v : X⦄, u ∈ L → v ∈ L → u ≠ v → ε ≤ dist u v

theorem IsDeltaNet.mono {X : Type*} [MetricSpace X] {x : X} {L : Set X}
    {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) (hL : IsDeltaNet δ₁ x L) :
    IsDeltaNet δ₂ x L := by
  rcases hL with ⟨hx, hcover, hsep⟩
  refine ⟨hx, ?_, hsep⟩
  intro y
  rcases hcover y with ⟨z, hz, hyz⟩
  exact ⟨z, hz, lt_of_lt_of_le hyz hδ⟩

theorem IsDeltaNet.nonempty {X : Type*} [MetricSpace X] {δ : ℝ} {x : X}
    {L : Set X} (hL : IsDeltaNet δ x L) : L.Nonempty :=
  ⟨x, hL.1⟩

/-! The maximal-net construction following `def:delta-net`. -/

/-- **Math.** A maximal `δ`-separated set containing the base point is a
`δ`-net, with the separation scale exposed explicitly.  The explicit clause
is used by the packing-to-cover bridge; `exists_isDeltaNet` below retains the
source-facing existential separation interface. -/
theorem exists_isDeltaNet_separated {X : Type*} [MetricSpace X]
    (δ : ℝ) (hδ : 0 < δ) (x : X) :
    ∃ L : Set X,
      x ∈ L ∧
      (∀ y : X, ∃ z ∈ L, dist y z < δ) ∧
      (∀ ⦃u v : X⦄, u ∈ L → v ∈ L → u ≠ v → δ ≤ dist u v) := by
  let P : Set (Set X) :=
    {L | x ∈ L ∧ ∀ ⦃u v : X⦄, u ∈ L → v ∈ L → u ≠ v → δ ≤ dist u v}
  have hstart : ({x} : Set X) ∈ P := by
    constructor
    · exact mem_singleton x
    · intro u v hu hv huv
      have hu' : u = x := mem_singleton_iff.mp hu
      have hv' : v = x := mem_singleton_iff.mp hv
      exact (huv (hu'.trans hv'.symm)).elim
  have hchain : ∀ c ⊆ P, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ P, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hcc hcn
    let ub : Set X := ⋃₀ c
    refine ⟨ub, ?_, ?_⟩
    · constructor
      · obtain ⟨s, hs⟩ := hcn
        exact mem_sUnion_of_mem ((hc hs).1) hs
      · intro u v hu hv huv
        obtain ⟨s, hs, hus⟩ := mem_sUnion.mp hu
        obtain ⟨t, ht, hvt⟩ := mem_sUnion.mp hv
        have horder : s ⊆ t ∨ t ⊆ s := by
          by_cases hst : s = t
          · exact Or.inl (hst ▸ Subset.rfl)
          · exact hcc hs ht hst
        rcases horder with hst | hts
        · exact (hc ht).2 (hst hus) hvt huv
        · exact (hc hs).2 hus (hts hvt) huv
    · intro s hs
      exact subset_sUnion_of_mem hs
  obtain ⟨L, hsub, hmax⟩ := zorn_subset_nonempty P hchain ({x} : Set X) hstart
  have hLP : L ∈ P := hmax.prop
  refine ⟨L, hLP.1, ?_, hLP.2⟩
  intro y
  by_contra hnot
  have hfar : ∀ z ∈ L, δ ≤ dist y z := by
    intro z hz
    exact le_of_not_gt (fun hlt => hnot ⟨z, hz, hlt⟩)
  have hinsert : insert y L ∈ P := by
    refine ⟨mem_insert_of_mem y hLP.1, ?_⟩
    intro u v hu hv huv
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · exact (huv rfl).elim
      · exact hfar v hv
    · rcases hv with rfl | hv
      · rw [dist_comm]
        exact hfar u hu
      · exact hLP.2 hu hv huv
  have hEq : insert y L = L := hmax.eq_of_superset hinsert (subset_insert y L)
  have hyL : y ∈ L := by
    rw [← hEq]
    exact mem_insert y L
  exact hnot ⟨y, hyL, by simpa using hδ⟩

theorem exists_isDeltaNet {X : Type*} [MetricSpace X]
    (δ : ℝ) (hδ : 0 < δ) (x : X) :
    ∃ L : Set X, IsDeltaNet δ x L := by
  obtain ⟨L, hx, hcover, hsep⟩ := exists_isDeltaNet_separated δ hδ x
  exact ⟨L, ⟨hx, hcover, ⟨δ, hδ, hsep⟩⟩⟩

/-! ## Length spaces -/

/-- **Math.** A length space in the sense of `def:length-space`: a connected
metric space in which every pair of points is joined by a rectifiable path
whose metric variation attains their distance.

This is strictly stronger than an infimum-only intrinsic metric condition: the
path realizing the distance is part of the proposition. -/
class LengthSpace (X : Type*) [MetricSpace X] : Prop extends ConnectedSpace X where
  exists_rectifiable_arc :
    ∀ x y : X, ∃ γ : Path x y,
      BoundedVariationOn (γ : I → X) Set.univ ∧
        (eVariationOn (γ : I → X) Set.univ).toReal = dist x y

/-- **Math.** The distance-realizing arcs in a length space make the space
path-connected.  This is the topological bridge used by the compact-ball and
pointed precompactness adapters; no local compactness or geodesic uniqueness
is inferred. -/
instance LengthSpace.pathConnectedSpace (X : Type*) [MetricSpace X]
    [hX : LengthSpace X] : PathConnectedSpace X where
  nonempty := inferInstance
  joined x y := by
    obtain ⟨γ, _, _⟩ := hX.exists_rectifiable_arc x y
    exact ⟨γ⟩

theorem LengthSpace.isPathConnected_univ (X : Type*) [MetricSpace X]
    [LengthSpace X] : IsPathConnected (Set.univ : Set X) :=
  pathConnectedSpace_iff_univ.mp inferInstance

theorem LengthSpace.exists_path_realizing_dist (X : Type*) [MetricSpace X]
    [hX : LengthSpace X] (x y : X) :
    ∃ γ : Path x y,
      BoundedVariationOn (γ : I → X) Set.univ ∧
        (eVariationOn (γ : I → X) Set.univ).toReal = dist x y :=
  hX.exists_rectifiable_arc x y

/-! ## Pointed compact spaces and the Mathlib GH producer -/

/-- **Math.** A bundled metric space used for dependent ambient families. -/
structure MetricSpaceBundle where
  carrier : Type*
  metric : MetricSpace carrier

instance (X : MetricSpaceBundle) : MetricSpace X.carrier := X.metric

/-! A based metric-space bundle for sequences with varying carriers. -/

structure BasedMetricSpaceBundle where
  carrier : Type u
  metric : MetricSpace carrier
  base : carrier

instance (X : BasedMetricSpaceBundle) : MetricSpace X.carrier := X.metric

/-- **Math.** Metric pullback convergence on every compact exhaustion stage.  This
is the metric-space analogue of the source's compact-open smooth convergence;
Riemannian smoothness can be added by a later manifold adapter.  The embedding
argument is total on the limit carrier, which is a deliberate strengthening of
the source's stage-wise maps `V_k ↪ U_k`. -/
def PullbackDistanceConverges
    (U : ℕ → BasedMetricSpaceBundle.{u})
    (Y : BasedMetricSpaceBundle.{u})
    (V : CompactExhaustion Y.carrier Y.base)
    (embedding : ∀ k, Y.carrier ↪ (U k).carrier) : Prop :=
  ∀ j, ∀ y ∈ closure (V.set j), ∀ z ∈ closure (V.set j),
    Tendsto (fun k => dist (embedding k y) (embedding k z))
      atTop (𝓝 (dist y z))

/-- **Math.** A metric adapter for the partial geometric-limit witness: a compact
exhaustion, total injective basepoint-preserving maps, and convergence of the
pulled-back distances on each compact stage.  Total maps are stronger than the
source's smooth maps whose domains are only the exhaustion stages; the source
smooth and `C^∞` clauses are intentionally left to a later manifold adapter. -/
structure PartialGeometricLimitData
    (U : ℕ → BasedMetricSpaceBundle.{u})
    (Y : BasedMetricSpaceBundle.{u}) where
  exhaustion : CompactExhaustion Y.carrier Y.base
  embedding : ∀ k, Y.carrier ↪ (U k).carrier
  embedding_base : ∀ k, embedding k Y.base = (U k).base
  pullback_distance_converges :
    PullbackDistanceConverges U Y exhaustion embedding

/-- **Math.** The regular-locus image-coverage condition (2b) in the geometric
limit definition, separated from the partial-limit data.  The eventual
basepoint-regularity conjunct prevents the coverage implication from becoming
vacuous when `regComponent` is empty. -/
def GeometricLimitImageCoverage
    {U : ℕ → BasedMetricSpaceBundle.{u}}
    {Y : BasedMetricSpaceBundle.{u}}
    (P : PartialGeometricLimitData U Y) : Prop :=
  ∀ δ R : ℝ, 0 < δ →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      (U k).base ∈ regLocus δ ∧
      ∀ ℓ, k ≤ ℓ →
        ∀ y : (U ℓ).carrier,
          y ∈ Metric.ball (U ℓ).base R →
          y ∈ regComponent δ (U ℓ).base →
          ∃ z ∈ P.exhaustion.set k, P.embedding ℓ z = y

/-- **Math.** A complete geometric-limit witness consists of the partial data
plus the regular-locus image-coverage clause. -/
structure GeometricLimitData
    (U : ℕ → BasedMetricSpaceBundle.{u})
    (Y : BasedMetricSpaceBundle.{u})
    extends PartialGeometricLimitData U Y where
  image_coverage : GeometricLimitImageCoverage toPartialGeometricLimitData

namespace PartialGeometricLimitData

/-- **Math.** Forget the image-coverage field of a geometric-limit witness. -/
def ofGeometricLimit
    {U : ℕ → BasedMetricSpaceBundle.{u}}
    {Y : BasedMetricSpaceBundle.{u}}
    (G : GeometricLimitData U Y) : PartialGeometricLimitData U Y :=
  G.toPartialGeometricLimitData

/-- **Math.** Add the regular-locus coverage field to a partial witness. -/
def complete
    {U : ℕ → BasedMetricSpaceBundle.{u}}
    {Y : BasedMetricSpaceBundle.{u}}
    (P : PartialGeometricLimitData U Y)
    (hcoverage : GeometricLimitImageCoverage P) :
    GeometricLimitData U Y :=
  { P with image_coverage := hcoverage }

theorem complete_toPartial
    {U : ℕ → BasedMetricSpaceBundle.{u}}
    {Y : BasedMetricSpaceBundle.{u}}
    (P : PartialGeometricLimitData U Y)
    (hcoverage : GeometricLimitImageCoverage P) :
    (complete P hcoverage).toPartialGeometricLimitData = P := by
  rfl

end PartialGeometricLimitData

/-- **Math.** A compact nonempty metric space with a distinguished base point. -/
structure PointedCompactMetricSpace where
  carrier : Type*
  metric : MetricSpace carrier
  compact : CompactSpace carrier
  nonempty : Nonempty carrier
  base : carrier

namespace PointedCompactMetricSpace

instance (X : PointedCompactMetricSpace) : MetricSpace X.carrier := X.metric
instance (X : PointedCompactMetricSpace) : CompactSpace X.carrier := X.compact
instance (X : PointedCompactMetricSpace) : Nonempty X.carrier := X.nonempty

/-- **Math.** The unpointed Gromov--Hausdorff distance supplied by Mathlib.  The base
point is retained in the bundle; the pointed distance used by the source is a
separate producer and is intentionally not identified with this quantity. -/
noncomputable def unpointedGH (X Y : PointedCompactMetricSpace) : ℝ :=
  letI : MetricSpace X.carrier := X.metric
  letI : CompactSpace X.carrier := X.compact
  letI : Nonempty X.carrier := X.nonempty
  letI : MetricSpace Y.carrier := Y.metric
  letI : CompactSpace Y.carrier := Y.compact
  letI : Nonempty Y.carrier := Y.nonempty
  GromovHausdorff.ghDist X.carrier Y.carrier

theorem unpointedGH_nonneg (X Y : PointedCompactMetricSpace) :
    0 ≤ unpointedGH X Y := by
  change 0 ≤ dist (GromovHausdorff.toGHSpace X.carrier)
    (GromovHausdorff.toGHSpace Y.carrier)
  exact dist_nonneg

theorem unpointedGH_triangle (X Y Z : PointedCompactMetricSpace) :
    unpointedGH X Z ≤ unpointedGH X Y + unpointedGH Y Z := by
  change dist (GromovHausdorff.toGHSpace X.carrier)
      (GromovHausdorff.toGHSpace Z.carrier) ≤
    dist (GromovHausdorff.toGHSpace X.carrier)
      (GromovHausdorff.toGHSpace Y.carrier) +
      dist (GromovHausdorff.toGHSpace Y.carrier)
        (GromovHausdorff.toGHSpace Z.carrier)
  exact dist_triangle _ _ _

end PointedCompactMetricSpace

/-- **Math.** Unpointed compact GH convergence, exposed only as an auxiliary
producer because the book's contract is pointed. -/
def UnpointedGHConverges (X : ℕ → PointedCompactMetricSpace)
    (Y : PointedCompactMetricSpace) : Prop :=
  Tendsto (fun k => PointedCompactMetricSpace.unpointedGH (X k) Y) atTop (𝓝 0)

/-! ## A source-faithful abstract realization interface -/

/-- **Math.** A realization sequence for pointed metric spaces.  The ambient metric
spaces and the two isometric embeddings are explicit data; the Hausdorff
convergence field is kept separate from the pointed GH producer. -/
structure RealizationSequence (X Y : Type u) [MetricSpace X] [MetricSpace Y]
    (x : X) (y : Y) where
  ambient : ℕ → MetricSpaceBundle.{u}
  left : ∀ k, X → (ambient k).carrier
  right : ∀ k, Y → (ambient k).carrier
  left_isometry : ∀ k, Isometry (left k)
  right_isometry : ∀ k, Isometry (right k)
  base_agree : ∀ k, left k x = right k y
  hausdorff_tendsto_zero :
    Tendsto (fun k => @Metric.hausdorffDist (ambient k).carrier inferInstance
      (Set.range (left k)) (Set.range (right k))) atTop (𝓝 0)

/-! The source-faithful varying-space realization data.  The pointed
Gromov--Hausdorff convergence predicate and its independence theorem are
deliberately separate contracts. -/

structure VaryingRealizationSequence
    (X : ℕ → BasedMetricSpaceBundle.{u}) (Y : BasedMetricSpaceBundle.{u}) where
  ambient : ℕ → MetricSpaceBundle.{u}
  left : ∀ k, (X k).carrier → (ambient k).carrier
  right : ∀ k, Y.carrier → (ambient k).carrier
  left_isometry : ∀ k, Isometry (left k)
  right_isometry : ∀ k, Isometry (right k)
  base_agree : ∀ k, left k (X k).base = right k Y.base
  hausdorff_tendsto_zero :
    Tendsto (fun k => @Metric.hausdorffDist (ambient k).carrier inferInstance
      (Set.range (left k)) (Set.range (right k))) atTop (𝓝 0)

end MorganTianLib
