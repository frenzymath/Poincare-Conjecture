import MorganTianLib.Ch03.RicciFlow.GeneralizedEmbedding
import MorganTianLib.Ch03.RicciFlow.GeneralizedRicciFlow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Morgan--Tian Ch. 3 - generalized parabolic neighborhoods

The horizontal metric gives an intrinsic length to smooth curves contained in
one time-slice.  Taking the infimum of their lengths produces the extended
slice distance and hence the metric balls used as the spatial bases of
generalized parabolic neighborhoods.
-/

open scoped ContDiff ENNReal Manifold Topology
open Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- **Math.** The speed of a smooth space-time curve measured by a horizontal
metric.  On a curve contained in one time-slice its velocity is horizontal,
so this is the ordinary Riemannian speed in that slice. -/
def GeneralizedSpaceTime.HorizontalMetric.horizontalCurveSpeed
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (γ : ℝ → N) (s : ℝ) : ℝ :=
  let v := mfderiv 𝓘(ℝ, ℝ) (modelWithCornersEuclideanHalfSpace n.succ) γ s
    (show ℝ from 1)
  Real.sqrt (G.inner (γ s) v v)

/-- **Math.** The horizontal length of a curve on the unit parameter
interval. -/
def GeneralizedSpaceTime.HorizontalMetric.horizontalCurveLength
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (γ : ℝ → N) : ℝ :=
  ∫ s in (0 : ℝ)..1, G.horizontalCurveSpeed n γ s

/-- **Math.** A smooth curve from `x` to `y` contained in the time-slice
`M_t`. -/
def GeneralizedSpaceTime.IsTimeSliceCurve
    (S : GeneralizedSpaceTime n (N := N)) (t : ℝ) (x y : N)
    (γ : ℝ → N) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) (modelWithCornersEuclideanHalfSpace n.succ) 1 γ
      (Icc 0 1) ∧
    γ 0 = x ∧ γ 1 = y ∧ ∀ s ∈ Icc (0 : ℝ) 1, S.time (γ s) = t

/-- **Math.** The intrinsic extended distance on `M_t`, defined as the
infimum of horizontal lengths of smooth curves in that slice.  It is `∞` when
there is no such curve. -/
def GeneralizedSpaceTime.HorizontalMetric.timeSliceEDist
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (t : ℝ) (x y : N) : ℝ≥0∞ :=
  sInf {d : ℝ≥0∞ | ∃ γ : ℝ → N,
    S.IsTimeSliceCurve n t x y γ ∧
      d = ENNReal.ofReal (G.horizontalCurveLength n γ)}

/-- **Math.** The extended slice distance from a point to itself is zero. -/
@[simp]
theorem GeneralizedSpaceTime.HorizontalMetric.timeSliceEDist_self
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    {t : ℝ} {x : N} (hx : S.time x = t) :
    G.timeSliceEDist n t x x = 0 := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨fun _ => x, ?_, ?_⟩
    · refine ⟨contMDiffOn_const, rfl, rfl, ?_⟩
      intro s hs
      exact hx
    · simp [GeneralizedSpaceTime.HorizontalMetric.horizontalCurveLength,
        GeneralizedSpaceTime.HorizontalMetric.horizontalCurveSpeed]
  · exact bot_le

/-- **Math.** The open metric ball of radius `r` in the generalized
time-slice through `x`. -/
def GeneralizedRicciFlow.timeSliceBall
    (F : GeneralizedRicciFlow n (N := N)) (x : N) (r : ℝ) : Set N :=
  {y | F.spaceTime.time y = F.spaceTime.time x ∧
    F.metric.timeSliceEDist n (F.spaceTime.time x) x y < ENNReal.ofReal r}

theorem GeneralizedRicciFlow.timeSliceBall_subset_timeSlice
    (F : GeneralizedRicciFlow n (N := N)) (x : N) (r : ℝ) :
    F.timeSliceBall n x r ⊆ F.spaceTime.timeSlice n (F.spaceTime.time x) := by
  intro y hy
  exact (F.spaceTime.mem_timeSlice_iff (n := n)).2 hy.1

theorem GeneralizedRicciFlow.mem_timeSliceBall_self
    (F : GeneralizedRicciFlow n (N := N)) (x : N) {r : ℝ} (hr : 0 < r) :
    x ∈ F.timeSliceBall n x r := by
  refine ⟨rfl, ?_⟩
  rw [F.metric.timeSliceEDist_self (n := n) rfl]
  exact ENNReal.ofReal_pos.mpr hr

/-- **Math.** Data exhibiting the existence of the forward parabolic
neighborhood `P(x,t,r,deltaT)`: a compatible embedding of the central metric
ball along the closed forward time interval. -/
structure GeneralizedRicciFlow.ForwardParabolicNeighborhood
    (F : GeneralizedRicciFlow n (N := N)) (x : N) (r deltaT : ℝ) where
  /-- The spatial radius is positive. -/
  radius_pos : 0 < r
  /-- The forward time length is positive. -/
  timeLength_pos : 0 < deltaT
  /-- The compatible embedding whose image is the neighborhood. -/
  embedding : F.spaceTime.CompatibleTimeSliceEmbedding n
    (F.timeSliceBall n x r) (F.spaceTime.time x)
    (Icc (F.spaceTime.time x) (F.spaceTime.time x + deltaT))

/-- **Math.** The forward parabolic neighborhood is the image of its
compatible embedding. -/
def GeneralizedRicciFlow.ForwardParabolicNeighborhood.image
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P : F.ForwardParabolicNeighborhood n x r deltaT) : Set N :=
  P.embedding.toCompatibleEmbedding.image n

/-- **Math.** Data exhibiting the existence of the backward parabolic
neighborhood `P(x,t,r,-deltaT)`: a compatible embedding of the central metric
ball along the closed backward time interval. -/
structure GeneralizedRicciFlow.BackwardParabolicNeighborhood
    (F : GeneralizedRicciFlow n (N := N)) (x : N) (r deltaT : ℝ) where
  /-- The spatial radius is positive. -/
  radius_pos : 0 < r
  /-- The backward time length is positive. -/
  timeLength_pos : 0 < deltaT
  /-- The compatible embedding whose image is the neighborhood. -/
  embedding : F.spaceTime.CompatibleTimeSliceEmbedding n
    (F.timeSliceBall n x r) (F.spaceTime.time x)
    (Icc (F.spaceTime.time x - deltaT) (F.spaceTime.time x))

/-- **Math.** The backward parabolic neighborhood is the image of its
compatible embedding. -/
def GeneralizedRicciFlow.BackwardParabolicNeighborhood.image
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P : F.BackwardParabolicNeighborhood n x r deltaT) : Set N :=
  P.embedding.toCompatibleEmbedding.image n

/-- **Math.** The center belongs to every existing forward parabolic
neighborhood. -/
theorem GeneralizedRicciFlow.ForwardParabolicNeighborhood.center_mem
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P : F.ForwardParabolicNeighborhood n x r deltaT) : x ∈ P.image n := by
  refine ⟨(x, F.spaceTime.time x), ?_, ?_⟩
  · exact ⟨F.mem_timeSliceBall_self n x P.radius_pos,
      left_mem_Icc.mpr (by linarith [P.timeLength_pos])⟩
  · exact P.embedding.center_eq x (F.mem_timeSliceBall_self n x P.radius_pos)

/-- **Math.** The center belongs to every existing backward parabolic
neighborhood. -/
theorem GeneralizedRicciFlow.BackwardParabolicNeighborhood.center_mem
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P : F.BackwardParabolicNeighborhood n x r deltaT) : x ∈ P.image n := by
  refine ⟨(x, F.spaceTime.time x), ?_, ?_⟩
  · exact ⟨F.mem_timeSliceBall_self n x P.radius_pos,
      right_mem_Icc.mpr (sub_le_self _ P.timeLength_pos.le)⟩
  · exact P.embedding.center_eq x (F.mem_timeSliceBall_self n x P.radius_pos)

/-- **Math.** The central slice of a forward parabolic neighborhood is
exactly its defining metric ball. -/
theorem GeneralizedRicciFlow.ForwardParabolicNeighborhood.image_inter_centerSlice
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P : F.ForwardParabolicNeighborhood n x r deltaT) :
    P.image n ∩ F.spaceTime.timeSlice n (F.spaceTime.time x) =
      F.timeSliceBall n x r := by
  exact P.embedding.image_inter_timeSlice n

/-- **Math.** A forward parabolic neighborhood realizes its whole declared
closed time interval. -/
theorem GeneralizedRicciFlow.ForwardParabolicNeighborhood.time_image
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P : F.ForwardParabolicNeighborhood n x r deltaT) :
    F.spaceTime.time '' P.image n =
      Icc (F.spaceTime.time x) (F.spaceTime.time x + deltaT) := by
  exact P.embedding.toCompatibleEmbedding.time_image n
    ⟨x, F.mem_timeSliceBall_self n x P.radius_pos⟩

/-- **Math.** The central slice of a backward parabolic neighborhood is
exactly its defining metric ball. -/
theorem GeneralizedRicciFlow.BackwardParabolicNeighborhood.image_inter_centerSlice
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P : F.BackwardParabolicNeighborhood n x r deltaT) :
    P.image n ∩ F.spaceTime.timeSlice n (F.spaceTime.time x) =
      F.timeSliceBall n x r := by
  exact P.embedding.image_inter_timeSlice n

/-- **Math.** A backward parabolic neighborhood realizes its whole declared
closed time interval. -/
theorem GeneralizedRicciFlow.BackwardParabolicNeighborhood.time_image
    {F : GeneralizedRicciFlow n (N := N)} {x : N} {r deltaT : ℝ}
    (P : F.BackwardParabolicNeighborhood n x r deltaT) :
    F.spaceTime.time '' P.image n =
      Icc (F.spaceTime.time x - deltaT) (F.spaceTime.time x) := by
  exact P.embedding.toCompatibleEmbedding.time_image n
    ⟨x, F.mem_timeSliceBall_self n x P.radius_pos⟩

end MorganTianLib

end
