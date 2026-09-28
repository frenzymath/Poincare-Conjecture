import MorganTianLib.Ch03.RicciFlow.GeneralizedTimeSlice
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-!
# Morgan--Tian Ch. 3 - compatible embeddings and regular times

A compatible embedding transports a subset of one time-slice along the time
vector field.  The topology is recorded on the actual restricted domain
`C x J`, while each time line is required to be a manifold integral curve.
Regular times are those admitting a compatible smooth product
diffeomorphism onto a full open time slab.
-/

open scoped ContDiff Manifold Topology
open Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- **Math.** A compatible embedding of `C x J` into a generalized
space-time.  Its second coordinate is time, and its lines with fixed spatial
coordinate are integral curves of the time vector field.

The ambient map is only used on `C x J`; representing it on `N x R` lets the
integral-curve condition use Mathlib's manifold ODE API without imposing a
manifold structure on an arbitrary subset `C`. -/
structure GeneralizedSpaceTime.CompatibleEmbedding
    (S : GeneralizedSpaceTime n (N := N)) (C : Set N) (J : Set ℝ) where
  /-- An ambient representative of the embedding on `C x J`. -/
  toFun : N × ℝ → N
  /-- The restriction to `C x J` is a topological embedding. -/
  isEmbedding : Topology.IsEmbedding (Set.restrict (C ×ˢ J) toFun)
  /-- The time function is the second projection on the image. -/
  time_eq : ∀ z ∈ C ×ˢ J, S.time (toFun z) = z.2
  /-- Every line with fixed spatial coordinate follows the time vector field. -/
  isIntegralCurveOn : ∀ x ∈ C,
    IsMIntegralCurveOn (fun s => toFun (x, s)) (fun y => S.timeVector y) J

/-- **Math.** The image of a compatible embedding. -/
def GeneralizedSpaceTime.CompatibleEmbedding.image
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) : Set N :=
  e.toFun '' (C ×ˢ J)

@[simp]
theorem GeneralizedSpaceTime.CompatibleEmbedding.time_toFun
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) {x : N} {t : ℝ}
    (hx : x ∈ C) (ht : t ∈ J) :
    S.time (e.toFun (x, t)) = t :=
  e.time_eq (x, t) ⟨hx, ht⟩

theorem GeneralizedSpaceTime.CompatibleEmbedding.toFun_mem_timeSlice
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) {x : N} {t : ℝ}
    (hx : x ∈ C) (ht : t ∈ J) :
    e.toFun (x, t) ∈ S.timeSlice n t :=
  (S.mem_timeSlice_iff (n := n)).2 (e.time_toFun n hx ht)

theorem GeneralizedSpaceTime.CompatibleEmbedding.image_subset_time_preimage
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) :
    e.image n ⊆ S.time ⁻¹' J := by
  rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
  change S.time (e.toFun (x, t)) ∈ J
  simpa only [e.time_toFun n hx ht] using ht

/-- **Math.** If the spatial source is nonempty, the times occurring in a
compatible embedding are exactly the prescribed interval. -/
theorem GeneralizedSpaceTime.CompatibleEmbedding.time_image
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) (hC : C.Nonempty) :
    S.time '' e.image n = J := by
  ext t
  constructor
  · rintro ⟨y, ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩, hyt⟩
    have hst : s = t := by
      simpa only [e.time_toFun n hx hs] using hyt
    exact hst ▸ hs
  · intro ht
    obtain ⟨x, hx⟩ := hC
    exact ⟨e.toFun (x, t), ⟨(x, t), ⟨hx, ht⟩, rfl⟩,
      e.time_toFun n hx ht⟩

/-- **Math.** Points reached by a compatible embedding at an interior time of
an open interval are interior manifold points. -/
theorem GeneralizedSpaceTime.CompatibleEmbedding.isInteriorPoint_toFun_Ioo
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {a b : ℝ}
    (e : S.CompatibleEmbedding n C (Ioo a b)) {x : N} {s : ℝ}
    (hx : x ∈ C) (hs : s ∈ Ioo a b) :
    (modelWithCornersEuclideanHalfSpace n.succ).IsInteriorPoint
      (e.toFun (x, s)) := by
  have hIoo_subset : Ioo a b ⊆ Set.range S.time := by
    intro u hu
    exact ⟨e.toFun (x, u), e.time_toFun n hx hu⟩
  have hsInterior : s ∈ interior (Set.range S.time) :=
    mem_interior_iff_mem_nhds.mpr <|
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) hIoo_subset
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
  change e.toFun (x, s) ∉
    (modelWithCornersEuclideanHalfSpace n.succ).boundary N
  rw [S.boundary_eq]
  change S.time (e.toFun (x, s)) ∉ frontier (Set.range S.time)
  rw [e.time_toFun n hx hs]
  exact fun hsFrontier =>
    Set.disjoint_left.1 disjoint_interior_frontier hsInterior hsFrontier

/-- **Math.** A compatible embedding based at `C ⊆ M_t`: its interval
contains `t` and its restriction to `C x {t}` is the identity. -/
structure GeneralizedSpaceTime.CompatibleTimeSliceEmbedding
    (S : GeneralizedSpaceTime n (N := N)) (C : Set N) (t : ℝ) (J : Set ℝ)
    extends S.CompatibleEmbedding n C J where
  /-- The central time belongs to the interval of definition. -/
  center_mem : t ∈ J
  /-- The spatial source lies in the central time-slice. -/
  source_subset : C ⊆ S.timeSlice n t
  /-- The embedding is the identity at its central time. -/
  center_eq : ∀ x ∈ C, toFun (x, t) = x

@[simp]
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.toFun_center
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t : ℝ} {J : Set ℝ}
    (e : S.CompatibleTimeSliceEmbedding n C t J) {x : N} (hx : x ∈ C) :
    e.toFun (x, t) = x :=
  e.center_eq x hx

/-- **Math.** The central time-slice of a compatible time-slice embedding is
exactly its spatial source `C`. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.image_inter_timeSlice
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t : ℝ} {J : Set ℝ}
    (e : S.CompatibleTimeSliceEmbedding n C t J) :
    e.toCompatibleEmbedding.image n ∩ S.timeSlice n t = C := by
  ext y
  constructor
  · rintro ⟨⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩, hslice⟩
    have hst : s = t :=
      (e.toCompatibleEmbedding.time_toFun n hx hs).symm.trans
        ((S.mem_timeSlice_iff (n := n)).1 hslice)
    subst s
    simpa only [e.center_eq x hx] using hx
  · intro hy
    refine ⟨⟨(y, t), ⟨hy, e.center_mem⟩, e.center_eq y hy⟩,
      e.source_subset hy⟩

/-- **Math.** Two compatible embeddings based on the same spatial subset and
central time agree on their common open interval of definition. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.eqOn_Ioo
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t a b : ℝ}
    (e₁ e₂ : S.CompatibleTimeSliceEmbedding n C t (Ioo a b))
    (ht : t ∈ Ioo a b) :
    Set.EqOn e₁.toFun e₂.toFun (C ×ˢ Ioo a b) := by
  letI : T2Space N := S.t2Space
  have htimeVector : ContMDiff
      (modelWithCornersEuclideanHalfSpace n.succ)
      (modelWithCornersEuclideanHalfSpace n.succ).tangent 1
      (fun x => (⟨x, S.timeVector x⟩ :
        TangentBundle (modelWithCornersEuclideanHalfSpace n.succ) N)) :=
    fun p => (S.timeVector.smooth p).of_le (by norm_num)
  rintro ⟨x, s⟩ ⟨hx, hs⟩
  have hcurves : Set.EqOn
      (fun u => e₁.toFun (x, u)) (fun u => e₂.toFun (x, u)) (Ioo a b) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff ht
      (fun u hu => e₁.toCompatibleEmbedding.isInteriorPoint_toFun_Ioo n hx hu)
      htimeVector
      (e₁.toCompatibleEmbedding.isIntegralCurveOn x hx)
      (e₂.toCompatibleEmbedding.isIntegralCurveOn x hx)
      ((e₁.center_eq x hx).trans (e₂.center_eq x hx).symm)
  exact hcurves hs

/-! The same uniqueness argument works when the two embeddings are defined on
different open intervals: restrict both integral curves to the common
interval.  This is the overlap statement used when assembling maximal flow
lines from local pieces. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.eqOn_common_Ioo
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t a b a' b' : ℝ}
    (e₁ : S.CompatibleTimeSliceEmbedding n C t (Ioo a b))
    (e₂ : S.CompatibleTimeSliceEmbedding n C t (Ioo a' b'))
    (ht : t ∈ Ioo a b ∩ Ioo a' b') :
    Set.EqOn e₁.toFun e₂.toFun
      (C ×ˢ Ioo (max a a') (min b b')) := by
  letI : T2Space N := S.t2Space
  have htimeVector : ContMDiff
      (modelWithCornersEuclideanHalfSpace n.succ)
      (modelWithCornersEuclideanHalfSpace n.succ).tangent 1
      (fun x => (⟨x, S.timeVector x⟩ :
        TangentBundle (modelWithCornersEuclideanHalfSpace n.succ) N)) :=
    fun p => (S.timeVector.smooth p).of_le (by norm_num)
  have htcommon : t ∈ Ioo (max a a') (min b b') := by
    exact ⟨max_lt ht.1.1 ht.2.1, lt_min ht.1.2 ht.2.2⟩
  rintro ⟨x, s⟩ ⟨hx, hs⟩
  have hcurves : Set.EqOn
      (fun u => e₁.toFun (x, u)) (fun u => e₂.toFun (x, u))
      (Ioo (max a a') (min b b')) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff htcommon
      (fun u hu =>
        e₁.toCompatibleEmbedding.isInteriorPoint_toFun_Ioo n hx
          ((Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)) hu))
      htimeVector
      ((e₁.toCompatibleEmbedding.isIntegralCurveOn x hx).mono
        (Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)))
      ((e₂.toCompatibleEmbedding.isIntegralCurveOn x hx).mono
        (Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)))
      ((e₁.center_eq x hx).trans (e₂.center_eq x hx).symm)
  exact hcurves hs

/-- **Math.** A flow line through `x ∈ M_t` is a compatible embedding of the
singleton `{x}`, based at time `t`. -/
abbrev GeneralizedSpaceTime.FlowLine
    (S : GeneralizedSpaceTime n (N := N)) (x : N) (t : ℝ) (J : Set ℝ) :=
  S.CompatibleTimeSliceEmbedding n ({x} : Set N) t J

/-- **Math.** A compatible diffeomorphism from `C x J` onto the full time
slab `time⁻¹(J)`.  Smoothness and the inverse identities are stated on the
ambient subsets, so no manifold structure is imposed on an arbitrary `C`. -/
structure GeneralizedSpaceTime.CompatibleTimeSliceDiffeomorphism
    (S : GeneralizedSpaceTime n (N := N)) (C : Set N) (t : ℝ) (J : Set ℝ)
    extends S.CompatibleTimeSliceEmbedding n C t J where
  /-- The inverse, represented on ambient space-time. -/
  invFun : N → N × ℝ
  /-- The compatible map is smooth on `C x J`. -/
  toFun_contMDiffOn : ContMDiffOn
    ((modelWithCornersEuclideanHalfSpace n.succ).prod 𝓘(ℝ, ℝ))
    (modelWithCornersEuclideanHalfSpace n.succ) ∞ toFun (C ×ˢ J)
  /-- The inverse is smooth on the full time slab. -/
  invFun_contMDiffOn : ContMDiffOn
    (modelWithCornersEuclideanHalfSpace n.succ)
    ((modelWithCornersEuclideanHalfSpace n.succ).prod 𝓘(ℝ, ℝ)) ∞ invFun
    (S.time ⁻¹' J)
  /-- The inverse maps the full time slab back into `C x J`. -/
  invFun_mapsTo : MapsTo invFun (S.time ⁻¹' J) (C ×ˢ J)
  /-- The inverse is a left inverse on `C x J`. -/
  left_inv : ∀ z ∈ C ×ˢ J, invFun (toFun z) = z
  /-- The inverse is a right inverse on the full time slab. -/
  right_inv : ∀ y ∈ S.time ⁻¹' J, toFun (invFun y) = y

/-- **Math.** A compatible time-slice diffeomorphism has image precisely the
full time slab. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceDiffeomorphism.image_eq
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t : ℝ} {J : Set ℝ}
    (e : S.CompatibleTimeSliceDiffeomorphism n C t J) :
    e.toCompatibleTimeSliceEmbedding.toCompatibleEmbedding.image n =
      S.time ⁻¹' J := by
  apply Set.Subset.antisymm
  · exact e.toCompatibleTimeSliceEmbedding.toCompatibleEmbedding
      |>.image_subset_time_preimage n
  · intro y hy
    exact ⟨e.invFun y, e.invFun_mapsTo hy, e.right_inv y hy⟩

/-- **Math.** A time is regular when a neighborhood of its full time-slice is
a compatible product diffeomorphism. -/
def GeneralizedSpaceTime.IsRegularTime
    (S : GeneralizedSpaceTime n (N := N)) (t : ℝ) : Prop :=
  t ∈ Set.range S.time ∧
    ∃ ε : ℝ, 0 < ε ∧
      Nonempty (S.CompatibleTimeSliceDiffeomorphism n (S.timeSlice n t) t
        (Ioo (t - ε) (t + ε)))

/-- **Math.** A time is singular exactly when it is not regular. -/
def GeneralizedSpaceTime.IsSingularTime
    (S : GeneralizedSpaceTime n (N := N)) (t : ℝ) : Prop :=
  t ∈ Set.range S.time ∧ ¬ S.IsRegularTime n t

@[simp]
theorem GeneralizedSpaceTime.isSingularTime_iff
    (S : GeneralizedSpaceTime n (N := N)) (t : ℝ) :
    S.IsSingularTime n t ↔
      t ∈ Set.range S.time ∧ ¬ S.IsRegularTime n t :=
  Iff.rfl

theorem GeneralizedSpaceTime.IsRegularTime.mem_timeRange
    {S : GeneralizedSpaceTime n (N := N)} {t : ℝ}
    (ht : S.IsRegularTime n t) : t ∈ Set.range S.time :=
  ht.1

theorem GeneralizedSpaceTime.IsSingularTime.mem_timeRange
    {S : GeneralizedSpaceTime n (N := N)} {t : ℝ}
    (ht : S.IsSingularTime n t) : t ∈ Set.range S.time :=
  ht.1

theorem GeneralizedSpaceTime.IsRegularTime.not_isSingularTime
    {S : GeneralizedSpaceTime n (N := N)} {t : ℝ}
    (ht : S.IsRegularTime n t) : ¬ S.IsSingularTime n t :=
  fun hs => hs.2 ht

/-- **Math.** Every time occurring in space-time is either regular or
singular. -/
theorem GeneralizedSpaceTime.regular_or_singular
    (S : GeneralizedSpaceTime n (N := N)) {t : ℝ}
    (ht : t ∈ Set.range S.time) :
    S.IsRegularTime n t ∨ S.IsSingularTime n t := by
  by_cases hreg : S.IsRegularTime n t
  · exact Or.inl hreg
  · exact Or.inr ⟨ht, hreg⟩

/-- **Math.** A finite initial time is the greatest lower bound of the time
image.  It need not itself occur in space-time. -/
def GeneralizedSpaceTime.IsInitialTime
    (S : GeneralizedSpaceTime n (N := N)) (t₀ : ℝ) : Prop :=
  IsGLB (Set.range S.time) t₀

/-- **Math.** The generalized space-time has initial time `-∞` when its time
image contains a whole half-line `(-∞, A]`. -/
def GeneralizedSpaceTime.HasInitialTimeNegInfinity
    (S : GeneralizedSpaceTime n (N := N)) : Prop :=
  ∃ A : ℝ, Iic A ⊆ Set.range S.time

theorem GeneralizedSpaceTime.isInitialTime_unique
    {S : GeneralizedSpaceTime n (N := N)} {s t : ℝ}
    (hs : S.IsInitialTime n s) (ht : S.IsInitialTime n t) : s = t :=
  hs.unique ht

end MorganTianLib

end
