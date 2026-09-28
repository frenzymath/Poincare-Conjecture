import MorganTianLib.Ch03.RicciFlow.GeneralizedSpaceTime
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Morgan--Tian Ch. 3 - generalized time-slices

The time-slices of a generalized space-time are the level sets of its time
function. Their tangent distribution is the kernel of `d time`. The adapted
product charts make these level sets into a codimension-one foliation, and the
unit-speed time vector gives a canonical splitting of every tangent space into
horizontal and time directions.
-/

open scoped ContDiff Manifold Topology
open Set Riemannian

noncomputable section

namespace MorganTianLib

private theorem subsingleton_of_isPreconnected_subset_frontier_ordConnected
    {s c : Set ℝ} (hs : s.OrdConnected) (hc : IsPreconnected c)
    (hcs : c ⊆ frontier s) : c.Subsingleton := by
  have no_lt : ∀ {a b : ℝ}, a ∈ c → b ∈ c → ¬ a < b := by
    intro a b ha hb hab
    let z := (a + b) / 2
    have haz : a < z := by dsimp [z]; linarith
    have hzb : z < b := by dsimp [z]; linarith
    have hzc : z ∈ c :=
      hc.ordConnected.out ha hb ⟨haz.le, hzb.le⟩
    have haclosure : a ∈ closure s := frontier_subset_closure (hcs ha)
    have hbclosure : b ∈ closure s := frontier_subset_closure (hcs hb)
    obtain ⟨u, huz, hus⟩ :=
      (mem_closure_iff_nhds.mp haclosure) (Iio z) (Iio_mem_nhds haz)
    obtain ⟨v, hzv, hvs⟩ :=
      (mem_closure_iff_nhds.mp hbclosure) (Ioi z) (Ioi_mem_nhds hzb)
    have huv : Icc u v ⊆ s := hs.out hus hvs
    have hzInterior : z ∈ interior s := mem_interior_iff_mem_nhds.mpr <|
      Filter.mem_of_superset
        (Filter.inter_mem (Ioi_mem_nhds huz) (Iio_mem_nhds hzv))
        (Ioo_subset_Icc_self.trans huv)
    have hzFrontier := hcs hzc
    rw [frontier] at hzFrontier
    exact hzFrontier.2 hzInterior
  intro a ha b hb
  exact le_antisymm (le_of_not_gt (no_lt hb ha)) (le_of_not_gt (no_lt ha hb))

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- **Math.** The time-slice `M_t` of a generalized space-time. -/
def GeneralizedSpaceTime.timeSlice (S : GeneralizedSpaceTime n (N := N))
    (t : ℝ) : Set N :=
  S.time ⁻¹' {t}

@[simp]
theorem GeneralizedSpaceTime.mem_timeSlice_iff
    (S : GeneralizedSpaceTime n (N := N)) {t : ℝ} {x : N} :
    x ∈ S.timeSlice n t ↔ S.time x = t := by
  simp [GeneralizedSpaceTime.timeSlice]

/-- **Math.** The horizontal tangent space at `x`, namely `ker(d time_x)`. -/
abbrev GeneralizedSpaceTime.HorizontalTangentSpace
    (S : GeneralizedSpaceTime n (N := N)) (x : N) :=
  (S.timeDifferential (n := n) x).ker

/-- **Math.** A tangent vector is horizontal exactly when it is killed by the
time differential. -/
def GeneralizedSpaceTime.IsHorizontal
    (S : GeneralizedSpaceTime n (N := N)) (x : N)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) : Prop :=
  S.timeDifferential (n := n) x v = 0

@[simp]
theorem GeneralizedSpaceTime.isHorizontal_iff_mem_ker
    (S : GeneralizedSpaceTime n (N := N)) (x : N)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    S.IsHorizontal n x v ↔ v ∈ (S.timeDifferential (n := n) x).ker :=
  Iff.rfl

/-- **Math.** The time vector is transverse to the horizontal distribution. -/
theorem GeneralizedSpaceTime.not_isHorizontal_timeVector
    (S : GeneralizedSpaceTime n (N := N)) (x : N) :
    ¬ S.IsHorizontal n x (S.timeVector x) := by
  rw [GeneralizedSpaceTime.IsHorizontal,
    S.timeDifferential_timeVector (n := n) x]
  exact one_ne_zero

/-- **Math.** Projection onto `ker(d time_x)` along the time vector `chi_x`. -/
def GeneralizedSpaceTime.horizontalProjectionAt
    (S : GeneralizedSpaceTime n (N := N)) (x : N) :
    TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x →L[ℝ]
      TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x :=
  ContinuousLinearMap.id ℝ _ -
    (S.timeDifferential (n := n) x).smulRight (S.timeVector x)

@[simp]
theorem GeneralizedSpaceTime.horizontalProjectionAt_apply
    (S : GeneralizedSpaceTime n (N := N)) (x : N)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    S.horizontalProjectionAt n x v =
      v - S.timeDifferential (n := n) x v • S.timeVector x := by
  rfl

/-- **Math.** The horizontal projection has zero time derivative. -/
@[simp]
theorem GeneralizedSpaceTime.timeDifferential_horizontalProjectionAt
    (S : GeneralizedSpaceTime n (N := N)) (x : N)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    S.timeDifferential (n := n) x (S.horizontalProjectionAt n x v) = 0 := by
  rw [S.horizontalProjectionAt_apply (n := n) x v, map_sub, map_smul,
    S.timeDifferential_timeVector (n := n) x, smul_eq_mul, mul_one, sub_self]

/-- **Math.** Horizontal vectors are fixed by the horizontal projection. -/
theorem GeneralizedSpaceTime.horizontalProjectionAt_eq_self
    (S : GeneralizedSpaceTime n (N := N)) (x : N)
    {v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x}
    (hv : S.IsHorizontal n x v) :
    S.horizontalProjectionAt n x v = v := by
  rw [S.horizontalProjectionAt_apply (n := n) x v, hv, zero_smul, sub_zero]

/-- **Math.** Every tangent vector splits into its horizontal component and
its scalar time component times `chi`. -/
theorem GeneralizedSpaceTime.horizontalProjectionAt_add_time
    (S : GeneralizedSpaceTime n (N := N)) (x : N)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    S.horizontalProjectionAt n x v +
        S.timeDifferential (n := n) x v • S.timeVector x = v := by
  rw [S.horizontalProjectionAt_apply (n := n) x v, sub_add_cancel]

/-- **Math.** The horizontal projection is idempotent. -/
theorem GeneralizedSpaceTime.horizontalProjectionAt_idempotent
    (S : GeneralizedSpaceTime n (N := N)) (x : N)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    S.horizontalProjectionAt n x (S.horizontalProjectionAt n x v) =
      S.horizontalProjectionAt n x v :=
  S.horizontalProjectionAt_eq_self n x
    (S.timeDifferential_horizontalProjectionAt (n := n) x v)

/-- **Math.** The image of the projection is exactly the horizontal tangent
space. -/
theorem GeneralizedSpaceTime.range_horizontalProjectionAt
    (S : GeneralizedSpaceTime n (N := N)) (x : N) :
    Set.range (S.horizontalProjectionAt n x) =
      (S.timeDifferential (n := n) x).ker := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact S.timeDifferential_horizontalProjectionAt (n := n) x w
  · intro hv
    exact ⟨v, S.horizontalProjectionAt_eq_self n x hv⟩

/-- **Math.** The time differential is onto, with right inverse
`a |-> a chi_x`. -/
theorem GeneralizedSpaceTime.timeDifferential_surjective
    (S : GeneralizedSpaceTime n (N := N)) (x : N) :
    Function.Surjective (S.timeDifferential (n := n) x) := by
  intro a
  refine ⟨a • S.timeVector x, ?_⟩
  rw [map_smul, S.timeDifferential_timeVector (n := n) x, smul_eq_mul, mul_one]

/-- **Math.** The horizontal tangent distribution has codimension one. -/
theorem GeneralizedSpaceTime.horizontal_finrank_add_one
    (S : GeneralizedSpaceTime n (N := N)) (x : N) :
    Module.finrank ℝ (S.HorizontalTangentSpace n x) + 1 =
      Module.finrank ℝ
        (TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) := by
  letI : FiniteDimensional ℝ
      (TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n.succ))
    infer_instance
  let f := (S.timeDifferential (n := n) x).toLinearMap
  have hrange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr (S.timeDifferential_surjective (n := n) x)
  have hrank := f.finrank_range_add_finrank_ker
  rw [hrange] at hrank
  simpa [add_comm] using hrank

/-- **Math.** In an adapted chart, a time-slice is a spatial plaque: within
the chart source, its preimage is `V x (J intersection {t})`. -/
theorem GeneralizedSpaceTimeLocalChart.preimage_timeSlice
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x) (t : ℝ) :
    c.equiv ⁻¹' S.timeSlice n t ∩ c.equiv.source =
      c.spatialSource ×ˢ (c.timeSource ∩ {t}) := by
  ext z
  simp only [mem_inter_iff, mem_preimage, S.mem_timeSlice_iff (n := n),
    c.source_eq, mem_prod, mem_singleton_iff]
  constructor
  · rintro ⟨ht, hzV, hzJ⟩
    exact ⟨hzV, hzJ, (c.time_eq z (c.source_eq ▸ ⟨hzV, hzJ⟩)).symm.trans ht⟩
  · rintro ⟨hzV, hzJ, ht⟩
    have hz : z ∈ c.equiv.source := c.source_eq ▸ ⟨hzV, hzJ⟩
    exact ⟨(c.time_eq z hz).trans ht, hzV, hzJ⟩

/-- **Math.** Every connected component of the space-time boundary is
contained in one time-slice. -/
theorem GeneralizedSpaceTime.boundary_connectedComponent_time_eq
    (S : GeneralizedSpaceTime n (N := N)) {x y : N}
    (hx : x ∈ (modelWithCornersEuclideanHalfSpace n.succ).boundary N)
    (hy : y ∈ connectedComponentIn
      ((modelWithCornersEuclideanHalfSpace n.succ).boundary N) x) :
    S.time y = S.time x := by
  let B := (modelWithCornersEuclideanHalfSpace n.succ).boundary N
  let C := S.time '' connectedComponentIn B x
  have hCpre : IsPreconnected C :=
    isPreconnected_connectedComponentIn.image S.time
      S.time_contMDiff.continuous.continuousOn
  have hCfrontier : C ⊆ frontier (range S.time) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzB : z ∈ B := connectedComponentIn_subset B x hz
    rw [show B = S.time ⁻¹' frontier (range S.time) from S.boundary_eq] at hzB
    exact hzB
  have hCsub : C.Subsingleton :=
    subsingleton_of_isPreconnected_subset_frontier_ordConnected
      S.timeRange_ordConnected hCpre hCfrontier
  apply hCsub
  · exact ⟨y, hy, rfl⟩
  · exact ⟨x, mem_connectedComponentIn hx, rfl⟩

end MorganTianLib
