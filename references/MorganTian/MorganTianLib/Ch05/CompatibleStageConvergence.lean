import MorganTianLib.Ch05.ClosedBallStageBridge
import MorganTianLib.Ch05.UnboundedAssembly

/-!
# Morgan--Tian Chapter 5: convergence of compatible compact stages

Radial coverage identifies every fixed ball in the completed inductive limit
with the corresponding ball in all sufficiently late compact stages.  This
module records that identification on open balls and turns eventual pointed
isometry into unbounded pointed Gromov--Hausdorff convergence of the stage
sequence to the completed limit.
-/

open Set Filter Topology Metric
open scoped Topology

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Forget compactness while retaining a stage's metric and
distinguished point. -/
def stageBundle (S : CompatiblePointedCompactSystem.{u}) (k : Nat) :
    BasedMetricSpaceBundle.{u} :=
  { carrier := (S.stage k).carrier
    metric := (S.stage k).metric
    base := (S.stage k).base }

/-- **Math.** Restrict a stage embedding to equal-radius open balls around the
common basepoint. -/
def stageBallMap
    (S : CompatiblePointedCompactSystem.{u}) (k : Nat) (R : Real) :
    Metric.ball (S.stage k).base R ->
      Metric.ball S.completedLimit.base R :=
  fun x =>
    ⟨S.stageEmbedding k x, by
      rw [Metric.mem_ball, S.dist_stageEmbedding_base k x]
      exact x.property⟩

/-- **Math.** The restricted stage map preserves distances. -/
theorem stageBallMap_isometry
    (S : CompatiblePointedCompactSystem.{u}) (k : Nat) (R : Real) :
    Isometry (S.stageBallMap k R) := by
  intro x y
  change edist (S.stageEmbedding k x) (S.stageEmbedding k y) = edist x y
  exact (S.stageEmbedding_isometry k).edist_eq _ _

/-- **Math.** Coverage of the ambient closed ball makes the restricted open-ball
stage map surjective. -/
theorem stageBallMap_surjective_of_coverage
    (S : CompatiblePointedCompactSystem.{u}) (k : Nat) (R : Real)
    (hcover : Metric.closedBall S.completedLimit.base R <=
      Set.range (S.stageEmbedding k)) :
    Function.Surjective (S.stageBallMap k R) := by
  intro y
  obtain ⟨x, hx⟩ := hcover (Metric.mem_closedBall.mpr y.property.le)
  have hxball : x ∈ Metric.ball (S.stage k).base R := by
    rw [Metric.mem_ball, ← S.dist_stageEmbedding_base k x, hx]
    exact y.property
  refine ⟨⟨x, hxball⟩, ?_⟩
  apply Subtype.ext
  exact hx

/-- **Math.** A stage covering the ambient closed ball is pointed-isometric to
the ambient open ball of the same radius. -/
noncomputable def stageBallEquiv_of_coverage
    (S : CompatiblePointedCompactSystem.{u}) (k : Nat) (R : Real)
    (hcover : Metric.closedBall S.completedLimit.base R <=
      Set.range (S.stageEmbedding k)) :
    Metric.ball (S.stage k).base R ≃ᵢ
      Metric.ball S.completedLimit.base R :=
  IsometryEquiv.mk' (S.stageBallMap k R)
    (Function.surjInv (S.stageBallMap_surjective_of_coverage k R hcover))
    (Function.surjInv_eq
      (S.stageBallMap_surjective_of_coverage k R hcover))
    (S.stageBallMap_isometry k R)

/-- **Math.** The open-ball equivalence preserves the distinguished point. -/
theorem stageBallEquiv_of_coverage_base
    (S : CompatiblePointedCompactSystem.{u}) (k : Nat) (R : Real)
    (hR : 0 < R)
    (hcover : Metric.closedBall S.completedLimit.base R <=
      Set.range (S.stageEmbedding k)) :
    S.stageBallEquiv_of_coverage k R hcover
        (ballModel (S.stageBundle k) R hR).base =
      (ballModel S.completedLimit R hR).base := by
  apply Subtype.ext
  exact S.stageEmbedding_base k

/-- **Math.** Under radial coverage, the equal-radius open balls in the compact
stages converge to the corresponding ball in the completed common ambient.
Indeed, after one stage covers the target closed ball, every later stage ball
is pointed-isometric to the target ball. -/
theorem pointedGHConverges_ballModel_stage_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : forall R : Real, exists n : Nat,
      Metric.closedBall S.completedLimit.base R <=
        Set.range (S.stageEmbedding n))
    (R : Real) (hR : 0 < R) :
    PointedGHConverges
      (fun k => ballModel (S.stageBundle k) R hR)
      (ballModel S.completedLimit R hR) := by
  constructor
  · simpa using
      (uniformlyBoundedDiameter_ballModel_of_radiusBound
        (fun k => S.stageBundle k) (fun _ => R) (fun _ => hR)
        ⟨R, fun _ => le_rfl⟩)
  · obtain ⟨n, hn⟩ := hcover R
    have hzero : ∀ᶠ k : Nat in atTop,
        pointedGHDistance
            (ballModel (S.stageBundle k) R hR)
            (ballModel S.completedLimit R hR) = 0 := by
      filter_upwards [Filter.eventually_atTop.2 ⟨n, fun k hk => hk⟩] with k hk
      have hkcover : Metric.closedBall S.completedLimit.base R <=
          Set.range (S.stageEmbedding k) :=
        hn.trans (S.range_stageEmbedding_mono hk)
      exact pointedGHDistance_eq_zero_of_basedIsometry
        (ballModel (S.stageBundle k) R hR)
        (ballModel S.completedLimit R hR)
        (S.stageBallEquiv_of_coverage k R hkcover)
        (S.stageBallEquiv_of_coverage_base k R hR hkcover)
    exact Tendsto.congr'
      (hzero.mono fun _ hk => hk.symm) tendsto_const_nhds

/-- **Math.** A radially covered compatible compact-stage system converges in
the unbounded pointed Gromov--Hausdorff sense to its completed inductive limit.
The radius perturbation is identically zero. -/
theorem pointedGHConvergesUnbounded_stage_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : forall R : Real, exists n : Nat,
      Metric.closedBall S.completedLimit.base R <=
        Set.range (S.stageEmbedding n)) :
    PointedGHConvergesUnbounded (fun k => S.stageBundle k) S.completedLimit := by
  intro R hR
  let delta : Nat -> Real := fun _ => 0
  have hdelta : Tendsto delta atTop (nhds 0) := by
    simp [delta]
  have hpos : forall k, 0 < R + delta k := by
    intro k
    simpa [delta] using hR
  refine ⟨delta, hdelta, hpos, ?_⟩
  simp [delta]
  exact S.pointedGHConverges_ballModel_stage_of_radial_stage_coverage hcover R hR

end CompatiblePointedCompactSystem

end MorganTianLib

end

#print axioms MorganTianLib.CompatiblePointedCompactSystem.stageBallMap_isometry
#print axioms MorganTianLib.CompatiblePointedCompactSystem.stageBallEquiv_of_coverage_base
#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.pointedGHConverges_ballModel_stage_of_radial_stage_coverage
#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.pointedGHConvergesUnbounded_stage_of_radial_stage_coverage
