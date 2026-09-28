import MorganTianLib.Ch04.ConvexProjection
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Morgan--Tian Ch. 4 - compact support pairs

For a closed convex set `Z` in a finite-dimensional real inner-product space,
this module records the contact point and unit supporting normal used by the
Hamilton tensor maximum principle.  The support pairs are represented as a
subtype of a closed subset of `E × E`; consequently they form a compact
parameter space whenever `Z` is compact.
-/

open Set
open scoped InnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-! ### The support-pair carrier -/

/-- The set of pairs `(k,n)` for which `k` is a point of `Z` and `n` is a unit
normal supporting `Z` at `k`. -/
def convexSupportPairSet (Z : Set E) : Set (E × E) :=
  {q | q.1 ∈ Z ∧ ‖q.2‖ = 1 ∧ ∀ z, z ∈ Z → ⟪q.2, z - q.1⟫_ℝ ≤ 0}

/-- The type of unit support pairs for `Z`. -/
abbrev ConvexSupportPair (Z : Set E) := {q : E × E // q ∈ convexSupportPairSet Z}

@[simp] theorem convexSupportPair_mem (Z : Set E) (q : ConvexSupportPair Z) :
    q.1 ∈ convexSupportPairSet Z := q.2

@[simp] theorem convexSupportPair_point_mem (Z : Set E) (q : ConvexSupportPair Z) :
    q.1.1 ∈ Z := q.2.1

@[simp] theorem convexSupportPair_normal_unit (Z : Set E) (q : ConvexSupportPair Z) :
    ‖q.1.2‖ = 1 := q.2.2.1

theorem convexSupportPair_support (Z : Set E) (q : ConvexSupportPair Z)
    (z : E) (hz : z ∈ Z) :
    ⟪q.1.2, z - q.1.1⟫_ℝ ≤ 0 := q.2.2.2 z hz

/-- The carrier of support pairs is closed whenever `Z` is closed. -/
theorem isClosed_convexSupportPairSet (Z : Set E) (hZ : IsClosed Z) :
    IsClosed (convexSupportPairSet Z) := by
  have hpoint : IsClosed {q : E × E | q.1 ∈ Z} :=
    hZ.preimage continuous_fst
  have hnorm : IsClosed {q : E × E | ‖q.2‖ = 1} := by
    exact isClosed_singleton.preimage (continuous_norm.comp continuous_snd)
  have hsupport : IsClosed
      {q : E × E | ∀ z, z ∈ Z → ⟪q.2, z - q.1⟫_ℝ ≤ 0} := by
    rw [show {q : E × E | ∀ z, z ∈ Z → ⟪q.2, z - q.1⟫_ℝ ≤ 0} =
        ⋂ z ∈ Z, {q : E × E | ⟪q.2, z - q.1⟫_ℝ ≤ 0} by
      ext q
      simp]
    apply isClosed_biInter
    intro z hz
    apply isClosed_le
    · have hsub : Continuous (fun q : E × E => z - q.1) :=
        continuous_const.sub continuous_fst
      exact continuous_snd.inner hsub
    · exact continuous_const
  have hset : convexSupportPairSet Z =
      {q : E × E | q.1 ∈ Z} ∩ {q : E × E | ‖q.2‖ = 1} ∩
        {q : E × E | ∀ z, z ∈ Z → ⟪q.2, z - q.1⟫_ℝ ≤ 0} := by
    ext q
    simp only [convexSupportPairSet, mem_setOf_eq, mem_inter_iff]
    constructor
    · rintro ⟨hqZ, hqn, hqs⟩
      exact ⟨⟨hqZ, hqn⟩, hqs⟩
    · rintro ⟨⟨hqZ, hqn⟩, hqs⟩
      exact ⟨hqZ, hqn, hqs⟩
  rw [hset]
  exact (hpoint.inter hnorm).inter hsupport

/-- The support-pair type is nonempty exactly when the carrier is nonempty. -/
theorem nonempty_convexSupportPair_iff (Z : Set E) :
    Nonempty (ConvexSupportPair Z) ↔ (convexSupportPairSet Z).Nonempty := by
  constructor
  · rintro ⟨q⟩
    exact ⟨q.1, q.2⟩
  · rintro ⟨q, hq⟩
    exact ⟨⟨q, hq⟩⟩

/-- A compact set `Z` gives a compact support-pair carrier. -/
theorem isCompact_convexSupportPairSet (Z : Set E) (hZ : IsCompact Z) :
    IsCompact (convexSupportPairSet Z) := by
  have hprod : IsCompact (Z ×ˢ Metric.closedBall (0 : E) 1) :=
    hZ.prod (isCompact_closedBall (0 : E) 1)
  apply hprod.of_isClosed_subset (isClosed_convexSupportPairSet Z hZ.isClosed)
  intro q hq
  refine ⟨hq.1, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq hq.2.1

/-- Compactness of the support-pair subtype. -/
theorem compactSpace_convexSupportPair (Z : Set E) (hZ : IsCompact Z) :
    CompactSpace (ConvexSupportPair Z) :=
  isCompact_iff_compactSpace.mp (isCompact_convexSupportPairSet Z hZ)

/-! ### Support evaluations -/

/-- Every support pair evaluates nonpositively on every point of `Z`. -/
theorem convexSupportPair_eval_nonpos (Z : Set E) (q : ConvexSupportPair Z)
    (z : E) (hz : z ∈ Z) :
    ⟪q.1.2, z - q.1.1⟫_ℝ ≤ 0 :=
  convexSupportPair_support Z q z hz

/-- A support pair is bounded above by the distance envelope at every point. -/
theorem convexSupportPair_eval_le_infDist (Z : Set E) (hZne : Z.Nonempty)
    (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z) (q : ConvexSupportPair Z) (v : E) :
    ⟪q.1.2, v - q.1.1⟫_ℝ ≤ Metric.infDist v Z := by
  let p := convexProjection Z hZne hZclosed hZconv v
  have hpmem : p ∈ Z := convexProjection_mem Z hZne hZclosed hZconv v
  have hnorm : ‖q.1.2‖ = 1 := convexSupportPair_normal_unit Z q
  have hsupport := convexSupportPair_support Z q p hpmem
  have hinner_le : ⟪q.1.2, v - p⟫_ℝ ≤ ‖v - p‖ := by
    calc
      ⟪q.1.2, v - p⟫_ℝ ≤ |⟪q.1.2, v - p⟫_ℝ| := le_abs_self _
      _ ≤ ‖q.1.2‖ * ‖v - p‖ := abs_real_inner_le_norm _ _
      _ = ‖v - p‖ := by rw [hnorm, one_mul]
  calc
    ⟪q.1.2, v - q.1.1⟫_ℝ =
        ⟪q.1.2, v - p⟫_ℝ + ⟪q.1.2, p - q.1.1⟫_ℝ := by
      rw [show v - q.1.1 = (v - p) + (p - q.1.1) by abel, inner_add_right]
    _ ≤ ⟪q.1.2, v - p⟫_ℝ := by linarith
    _ ≤ ‖v - p‖ := hinner_le
    _ = dist v p := (dist_eq_norm v p).symm
    _ = Metric.infDist v Z := convexProjection_dist_eq_infDist Z hZne hZclosed hZconv v

/-- Every exterior point has a support pair attaining the distance envelope. -/
noncomputable def exteriorSupportPair (Z : Set E) (hZne : Z.Nonempty)
    (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z) (v : E) (hv : v ∉ Z) :
    ConvexSupportPair Z := by
  let s := convexProjection_unit_support Z hZne hZclosed hZconv v hv
  exact ⟨(s.point, s.normal), s.point_mem, s.normal_unit, s.support⟩

theorem exteriorSupportPair_eval_eq_infDist (Z : Set E) (hZne : Z.Nonempty)
    (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z) (v : E) (hv : v ∉ Z) :
    ⟪(exteriorSupportPair Z hZne hZclosed hZconv v hv).1.2,
      v - (exteriorSupportPair Z hZne hZclosed hZconv v hv).1.1⟫_ℝ =
      Metric.infDist v Z := by
  let s := convexProjection_unit_support Z hZne hZclosed hZconv v hv
  change ⟪s.normal, v - s.point⟫_ℝ = Metric.infDist v Z
  exact s.value

end MorganTianLib
