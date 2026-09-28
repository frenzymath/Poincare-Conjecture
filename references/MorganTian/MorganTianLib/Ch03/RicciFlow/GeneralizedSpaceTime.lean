import DoCarmoLib.Riemannian.TangentBundle.TangentSmooth
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.Compactness.Paracompact

/-!
# Morgan--Tian Ch. 3 - generalized space-time

The generalized notion is not the product space-time of an ordinary Ricci
flow.  Its carrier is an arbitrary paracompact Hausdorff smooth manifold with
boundary.  A time function and a smooth time vector field are locally
straightened simultaneously by product charts, while the global topology need
not be a product.
-/

open scoped ContDiff Manifold Topology
open Set Riemannian

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- **Math.** A local product chart adapted to a time function and its time
vector field.  Its source is `V x J`, where `V` is open in `R^n` and `J` is an
interval.  In these coordinates time is the second projection and the time
vector field is the pushforward of the positive unit time vector. -/
structure GeneralizedSpaceTimeLocalChart
    (time : N → ℝ)
    (timeVector : SmoothVectorField (modelWithCornersEuclideanHalfSpace n.succ) N)
    (x : N) where
  /-- The spatial coordinate domain `V`. -/
  spatialSource : Set (EuclideanSpace ℝ (Fin n))
  /-- The time coordinate interval `J`. -/
  timeSource : Set ℝ
  /-- The spatial coordinate domain is open. -/
  spatialSource_isOpen : IsOpen spatialSource
  /-- The time coordinate domain is an interval. -/
  timeSource_ordConnected : timeSource.OrdConnected
  /-- The equivalence between `V x J` and its image neighborhood. -/
  equiv : PartialEquiv (EuclideanSpace ℝ (Fin n) × ℝ) N
  /-- The equivalence has source exactly `V x J`. -/
  source_eq : equiv.source = spatialSource ×ˢ timeSource
  /-- The image is an open neighborhood in space-time. -/
  target_isOpen : IsOpen equiv.target
  /-- The center lies in the image neighborhood. -/
  center_mem : x ∈ equiv.target
  /-- The adapted coordinate domain has unique differentials. -/
  source_uniqueMDiffOn : UniqueMDiffOn
    ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
      (modelWithCornersSelf ℝ ℝ)) equiv.source
  /-- The chart map is smooth on `V x J`. -/
  to_contMDiffOn :
    ContMDiffOn
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersEuclideanHalfSpace n.succ) ∞ equiv equiv.source
  /-- The inverse chart map is smooth on the image neighborhood. -/
  inv_contMDiffOn :
    ContMDiffOn (modelWithCornersEuclideanHalfSpace n.succ)
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
        (modelWithCornersSelf ℝ ℝ))
      ∞ equiv.symm equiv.target
  /-- In the adapted chart, time is the second coordinate. -/
  time_eq : ∀ z ∈ equiv.source, time (equiv z) = z.2
  /-- The adapted chart sends the positive unit time vector to `timeVector`. -/
  timeVector_eq : ∀ z ∈ equiv.source,
    mfderivWithin
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersEuclideanHalfSpace n.succ)
      equiv equiv.source z (0, 1) = timeVector (equiv z)

/-- **Math.** An `n`-dimensional generalized space-time in the sense of
Morgan--Tian: a paracompact Hausdorff smooth `(n+1)`-manifold, possibly with
boundary, equipped with a smooth time function and a smooth time vector field.
The time image is an interval, the manifold boundary lies exactly over the
boundary of that interval, and adapted local product charts straighten both
time and the time vector field. -/
structure GeneralizedSpaceTime where
  /-- The space-time carrier is paracompact. -/
  paracompactSpace : ParacompactSpace N
  /-- The space-time carrier is Hausdorff. -/
  t2Space : T2Space N
  /-- The time function. -/
  time : N → ℝ
  /-- The smooth time vector field. -/
  timeVector : SmoothVectorField (modelWithCornersEuclideanHalfSpace n.succ) N
  /-- The time function is smooth. -/
  time_contMDiff : ContMDiff (modelWithCornersEuclideanHalfSpace n.succ)
    (modelWithCornersSelf ℝ ℝ) ∞ time
  /-- The image of time is an interval. -/
  timeRange_ordConnected : (range time).OrdConnected
  /-- The manifold boundary is the preimage of the boundary of the time
  interval. -/
  boundary_eq : (modelWithCornersEuclideanHalfSpace n.succ).boundary N =
    time ⁻¹' frontier (range time)
  /-- Every point has a product chart adapted to time and the time vector
  field. -/
  localProduct : ∀ x, GeneralizedSpaceTimeLocalChart n time timeVector x

/-- **Math.** The differential of time, regarded as a real-valued linear
functional on the tangent space. -/
def GeneralizedSpaceTime.timeDifferential (S : GeneralizedSpaceTime n (N := N))
    (x : N) : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x →L[ℝ] ℝ :=
  mfderiv (modelWithCornersEuclideanHalfSpace n.succ)
    (modelWithCornersSelf ℝ ℝ) S.time x

/-- **Math.** The time vector field advances the time function at unit speed:
`d time (timeVector) = 1`. -/
theorem GeneralizedSpaceTime.timeDifferential_timeVector
    (S : GeneralizedSpaceTime n (N := N)) (x : N) :
    S.timeDifferential (n := n) x (S.timeVector x) = 1 := by
  let c := S.localProduct x
  let z := c.equiv.symm x
  have hz : z ∈ c.equiv.source := c.equiv.map_target c.center_mem
  have hzx : c.equiv z = x := c.equiv.right_inv c.center_mem
  have htime : MDifferentiableAt (modelWithCornersEuclideanHalfSpace n.succ)
      (modelWithCornersSelf ℝ ℝ) S.time (c.equiv z) :=
    S.time_contMDiff.mdifferentiableAt (by simp)
  have hchart : MDifferentiableWithinAt
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersEuclideanHalfSpace n.succ) c.equiv c.equiv.source z :=
    (c.to_contMDiffOn z hz).mdifferentiableWithinAt (by simp)
  have hchain := mfderiv_comp_mfderivWithin (x := z) htime hchart
    (c.source_uniqueMDiffOn z hz)
  have hcongr :
      mfderivWithin
          ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
            (modelWithCornersSelf ℝ ℝ))
          (modelWithCornersSelf ℝ ℝ) (S.time ∘ c.equiv) c.equiv.source z =
        mfderivWithin
          ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
            (modelWithCornersSelf ℝ ℝ))
          (modelWithCornersSelf ℝ ℝ) Prod.snd c.equiv.source z :=
    mfderivWithin_congr_of_mem (fun q hq => c.time_eq q hq) hz
  rw [← hzx]
  calc
    S.timeDifferential (n := n) (c.equiv z) (S.timeVector (c.equiv z)) =
        S.timeDifferential (n := n) (c.equiv z)
          (mfderivWithin
            ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
              (modelWithCornersSelf ℝ ℝ))
            (modelWithCornersEuclideanHalfSpace n.succ)
            c.equiv c.equiv.source z (0, 1)) := by
      rw [c.timeVector_eq z hz]
    _ = (show ℝ from mfderivWithin
          ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
            (modelWithCornersSelf ℝ ℝ))
          (modelWithCornersSelf ℝ ℝ) (S.time ∘ c.equiv) c.equiv.source z (0, 1)) := by
      rw [hchain]
      rfl
    _ = (show ℝ from mfderivWithin
          ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))).prod
            (modelWithCornersSelf ℝ ℝ))
          (modelWithCornersSelf ℝ ℝ) Prod.snd c.equiv.source z (0, 1)) := by
      rw [hcongr]
      rfl
    _ = 1 := by
      rw [mfderivWithin_snd (hxs := c.source_uniqueMDiffOn z hz)]
      rfl

end MorganTianLib
