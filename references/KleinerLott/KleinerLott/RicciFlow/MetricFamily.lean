import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.MetricSpace.ProperSpace
import KleinerLott.RicciFlow.CompleteGeometry

/-!
# Families of metric spaces

This file turns a family of genuine metric distances, continuous on a chosen
time set, into the scalar flow data used by the point-selection argument.
-/

namespace KleinerLott

/-- A time-dependent family of metric distances inducing a fixed topology. -/
structure MetricFamily (M : Type*) [TopologicalSpace M] where
  dist : ℝ → M → M → ℝ
  dist_self : ∀ t x, dist t x x = 0
  dist_comm : ∀ t x y, dist t x y = dist t y x
  dist_triangle : ∀ t x y z, dist t x z ≤ dist t x y + dist t y z
  eq_of_dist_eq_zero : ∀ t x y, dist t x y = 0 → x = y
  isOpen_iff : ∀ t s, IsOpen s ↔
    ∀ x ∈ s, ∃ epsilon > 0, ∀ y, dist t x y < epsilon → y ∈ s

namespace MetricFamily

/-- The metric-space structure at a fixed time. -/
@[reducible]
def metricSpaceAt {M : Type*} [TopologicalSpace M]
    (d : MetricFamily M) (t : ℝ) : MetricSpace M :=
  MetricSpace.ofDistTopology (d.dist t) (d.dist_self t) (d.dist_comm t)
    (d.dist_triangle t) (d.isOpen_iff t) (d.eq_of_dist_eq_zero t)

/-- Every time slice in `I` is a proper metric space. -/
def IsProperOn {M : Type*} [TopologicalSpace M]
    (d : MetricFamily M) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, @ProperSpace M (d.metricSpaceAt t).toPseudoMetricSpace

/-- The distance is jointly continuous in time and both endpoints on `I`. -/
def IsContinuousOn {M : Type*} [TopologicalSpace M]
    (d : MetricFamily M) (I : Set ℝ) : Prop :=
  ContinuousOn (fun p : ℝ × (M × M) ↦ d.dist p.1 p.2.1 p.2.2)
    (I ×ˢ Set.univ)

/-- Closed balls in every time slice in `I` are path connected. -/
def HasPathConnectedClosedBallsOn {M : Type*} [TopologicalSpace M]
    (d : MetricFamily M) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, ∀ x r, 0 ≤ r → IsPathConnected {y | d.dist t x y ≤ r}

/-- Scalar flow data built from a continuous metric family and a continuous
curvature score. -/
noncomputable def toFlowData {M : Type*} [TopologicalSpace M]
    (d : MetricFamily M) (curvatureScore : M → ℝ → ℝ)
    (volume : ℝ → Set M → ℝ) : RicciFlowData M where
  dist := d.dist
  curvatureNorm := curvatureScore
  volume := volume

/-- Properness of a time slice supplies compact closed balls for its scalar
flow data. -/
theorem IsProperOn.isProperAt
    {M : Type*} [TopologicalSpace M] {d : MetricFamily M}
    {I : Set ℝ} (hproper : d.IsProperOn I)
    (curvatureScore : M → ℝ → ℝ) (volume : ℝ → Set M → ℝ)
    (x₀ : M) {t : ℝ} (ht : t ∈ I) :
    (d.toFlowData curvatureScore volume).IsProperAt x₀ t := by
  letI : MetricSpace M := d.metricSpaceAt t
  letI : ProperSpace M := hproper t ht
  intro r
  have hball : {x | d.dist t x₀ x ≤ r} = Metric.closedBall x₀ r := by
    ext x
    change (d.dist t x₀ x ≤ r) ↔ (d.dist t x x₀ ≤ r)
    rw [d.dist_comm]
  change IsCompact {x | d.dist t x₀ x ≤ r}
  rw [hball]
  exact isCompact_closedBall x₀ r

/-- The scalar flow distance vanishes at equal endpoints. -/
@[simp]
theorem toFlowData_dist_self
    {M : Type*} [TopologicalSpace M] (d : MetricFamily M)
    (curvatureScore : M → ℝ → ℝ) (volume : ℝ → Set M → ℝ)
    (t : ℝ) (x : M) :
    (d.toFlowData curvatureScore volume).dist t x x = 0 :=
  d.dist_self t x

/-- Distance from a fixed basepoint is jointly continuous in time and the
other endpoint. -/
theorem IsContinuousOn.continuousOn_toFlowData_dist
    {M : Type*} [TopologicalSpace M] {d : MetricFamily M} {I : Set ℝ}
    (hcontinuous : d.IsContinuousOn I)
    (curvatureScore : M → ℝ → ℝ) (volume : ℝ → Set M → ℝ)
    (x₀ : M) :
    ContinuousOn (Function.uncurry fun t x ↦
      (d.toFlowData curvatureScore volume).dist t x₀ x)
        (I ×ˢ Set.univ) := by
  have hmap : Continuous (fun p : ℝ × M ↦ (p.1, (x₀, p.2))) :=
    continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
  change ContinuousOn (fun p : ℝ × M ↦ d.dist p.1 x₀ p.2)
    (I ×ˢ Set.univ)
  unfold IsContinuousOn at hcontinuous
  simpa using hcontinuous.comp' hmap.continuousOn
    (fun p hp ↦ ⟨hp.1, Set.mem_univ (p.1, (x₀, p.2))⟩)

/-- Interval-local continuity of a curvature score is preserved by conversion
to scalar flow data. -/
theorem continuousOn_toFlowData_curvatureNorm
    {M : Type*} [TopologicalSpace M] (d : MetricFamily M)
    (curvatureScore : M → ℝ → ℝ) (volume : ℝ → Set M → ℝ)
    {I : Set ℝ}
    (hcurvature :
      ContinuousOn (Function.uncurry curvatureScore) (Set.univ ×ˢ I)) :
    ContinuousOn
      (Function.uncurry (d.toFlowData curvatureScore volume).curvatureNorm)
      (Set.univ ×ˢ I) := by
  simpa [toFlowData] using hcurvature

/-- Path-connected closed balls supply radial paths that remain in the closed
distance sublevel of their endpoint. -/
theorem HasPathConnectedClosedBallsOn.hasRadialDistancePathsOn
    {M : Type*} [TopologicalSpace M] {d : MetricFamily M}
    {I : Set ℝ} (hpaths : d.HasPathConnectedClosedBallsOn I)
    (curvatureScore : M → ℝ → ℝ) (volume : ℝ → Set M → ℝ)
    (x₀ : M) :
    (d.toFlowData curvatureScore volume).HasRadialDistancePathsOn x₀ I := by
  intro t ht x
  letI : MetricSpace M := d.metricSpaceAt t
  have hnonneg : 0 ≤ d.dist t x₀ x := by
    change 0 ≤ Dist.dist x₀ x
    exact dist_nonneg
  have hjoined :
      JoinedIn {y | d.dist t x₀ y ≤ d.dist t x₀ x} x₀ x :=
    (hpaths t ht x₀ (d.dist t x₀ x) hnonneg).joinedIn x₀
      (by
        change d.dist t x₀ x₀ ≤ d.dist t x₀ x
        rw [d.dist_self]
        exact hnonneg)
      x (by
        change d.dist t x₀ x ≤ d.dist t x₀ x
        exact le_rfl)
  refine ⟨hjoined.somePath, ?_⟩
  intro u
  exact hjoined.somePath_mem u

/-- A proper continuous metric family with path-connected closed balls carries
the smooth-complete geometry used by point selection. -/
theorem IsProperOn.hasSmoothCompleteGeometryOn
    {M : Type*} [TopologicalSpace M] {d : MetricFamily M}
    {I : Set ℝ} (hproper : d.IsProperOn I)
    (curvatureScore : M → ℝ → ℝ) (volume : ℝ → Set M → ℝ)
    (hdist_continuous : d.IsContinuousOn I)
    (hcurvature_continuous :
      ContinuousOn (Function.uncurry curvatureScore) (Set.univ ×ˢ I))
    (hpaths : d.HasPathConnectedClosedBallsOn I) :
    (d.toFlowData curvatureScore volume).HasSmoothCompleteGeometryOn I where
  curvature_continuous :=
    d.continuousOn_toFlowData_curvatureNorm curvatureScore volume
      hcurvature_continuous
  proper := fun x₀ _ ht ↦ hproper.isProperAt curvatureScore volume x₀ ht
  dist_self_eq_zero := fun _ t _ ↦ d.toFlowData_dist_self curvatureScore volume t _
  dist_continuous := fun x₀ ↦ hdist_continuous.continuousOn_toFlowData_dist
    curvatureScore volume x₀
  radial_paths := hpaths.hasRadialDistancePathsOn curvatureScore volume

end MetricFamily

/-- Point selection for a jointly continuous family of proper metric spaces
whose closed balls are path connected. -/
theorem exists_point_selection_of_metric_family
    {M : Type*} [TopologicalSpace M]
    (d : MetricFamily M) (curvatureScore : M → ℝ → ℝ)
    (volume : ℝ → Set M → ℝ) (n : ℕ)
    {alpha A epsilon t : ℝ} {x₀ x : M}
    (halpha : 0 < alpha) (hA : 0 < A) (hepsilon : 0 < epsilon)
    (hAepsilon : A * epsilon < (100 * (n : ℝ))⁻¹)
    (ht : t ∈ Set.Ioc 0 (epsilon ^ 2))
    (hdist : (d.toFlowData curvatureScore volume).dist t x₀ x ≤ epsilon)
    (hcurvature : alpha * t⁻¹ + (epsilon⁻¹) ^ 2 ≤
      (d.toFlowData curvatureScore volume).curvatureNorm x t)
    (hdist_continuous : d.IsContinuousOn (Set.Icc 0 (epsilon ^ 2)))
    (hcurvature_continuous :
      ContinuousOn (Function.uncurry curvatureScore)
        (Set.univ ×ˢ Set.Icc 0 (epsilon ^ 2)))
    (hproper : d.IsProperOn (Set.Icc 0 (epsilon ^ 2)))
    (hpaths : d.HasPathConnectedClosedBallsOn (Set.Icc 0 (epsilon ^ 2))) :
    ∃ xbar tbar,
      (xbar, tbar) ∈
          (d.toFlowData curvatureScore volume).highCurvatureRegion alpha ∧
        tbar ∈ Set.Ioc 0 (epsilon ^ 2) ∧
        (d.toFlowData curvatureScore volume).dist tbar x₀ xbar <
          (2 * A + 1) * epsilon ∧
        ∀ x' t',
          (x', t') ∈
              (d.toFlowData curvatureScore volume).highCurvatureRegion alpha →
            t' ∈ Set.Ioc 0 tbar →
              (d.toFlowData curvatureScore volume).dist t' x₀ x' ≤
                  (d.toFlowData curvatureScore volume).dist tbar x₀ xbar +
                    A * (Real.sqrt
                      ((d.toFlowData curvatureScore volume).curvatureNorm
                        xbar tbar))⁻¹ →
                (d.toFlowData curvatureScore volume).curvatureNorm x' t' ≤
                  4 * (d.toFlowData curvatureScore volume).curvatureNorm
                    xbar tbar := by
  exact exists_point_selection_of_smooth_complete_geometry
    (d.toFlowData curvatureScore volume) n halpha hA hepsilon hAepsilon ht
    hdist hcurvature
    (hproper.hasSmoothCompleteGeometryOn curvatureScore volume hdist_continuous
      hcurvature_continuous hpaths)

end KleinerLott
