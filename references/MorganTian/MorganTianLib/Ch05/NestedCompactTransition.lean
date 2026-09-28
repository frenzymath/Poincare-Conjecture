import MorganTianLib.Ch05.ClosedBallTransition
import MorganTianLib.Ch05.CompactStageDiagonal
import MorganTianLib.Ch05.CompatibleStageConvergence

/-!
# Morgan--Tian Chapter 5: concrete nested-system transition stability

The nested compact-system constructor chooses an arbitrary based isometry
between each stage and its inner model.  This module keeps that choice
explicit, recovers its basepoint law from the constructor's transition law,
and proves the finite-radius transition stability that follows once the
radius sequence is cofinal.  The independent compact-limit and ambient
identification hypotheses remain outside this producer.
-/

open Set Filter Topology Metric

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

private theorem surjective_transitionChain_of_factorization
    (S : CompatiblePointedCompactSystem.{u})
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (inner : ℕ → PointedCompactMetricSpace.{u})
    (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hmono : ∀ i, r i ≤ r (i + 1))
    (inner_to_ball : ∀ i,
      (inner i).carrier ≃ᵢ (closedBallModel X (r i) (hr i)).carrier)
    (inner_to_ball_base : ∀ i,
      inner_to_ball i (inner i).base =
        (closedBallModel X (r i) (hr i)).base)
    (ball_to_stage : ∀ i,
      (closedBallModel X (r i) (hr i)).carrier ≃ᵢ (S.stage i).carrier)
    (ball_to_stage_base : ∀ i,
      ball_to_stage i (closedBallModel X (r i) (hr i)).base =
        (S.stage i).base)
    (e : ∀ i, (S.stage i).carrier ≃ᵢ (inner i).carrier)
    (e_base : ∀ i, e i (S.stage i).base = (inner i).base)
    (hfac : ∀ i, S.transition i =
      (ball_to_stage (i + 1)) ∘
        (closedBallModelInclusion X (r i) (r (i + 1)) (hr i) (hr (i + 1))
          (hmono i)) ∘ (inner_to_ball i) ∘ e i)
    (n : ℕ) (R : ℝ) (hRn : R ≤ r n) :
    ∀ k : ℕ, Function.Surjective (S.transitionChainClosedBallMap n k R) := by
  have hmono_le : ∀ {a b : ℕ}, a ≤ b → r a ≤ r b := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih =>
        exact ih.trans (hmono b)
  have hRtail : ∀ k : ℕ, R ≤ r (n + k) := by
    intro k
    exact hRn.trans (hmono_le (Nat.le_add_right n k))
  have hstep : ∀ m : ℕ, R ≤ r m →
      Function.Surjective (S.transitionChainClosedBallMap m 1 R) := by
    intro m hRm y
    have hyR : dist (y : (S.stage (m + 1)).carrier)
        (S.stage (m + 1)).base ≤ R :=
      Metric.mem_closedBall.mp y.property
    have hbase_inv :
        (ball_to_stage (m + 1)).symm ((S.stage (m + 1)).base) =
          (closedBallModel X (r (m + 1)) (hr (m + 1))).base := by
      apply (ball_to_stage (m + 1)).injective
      simp [ball_to_stage_base (m + 1)]
    let z : (closedBallModel X (r (m + 1)) (hr (m + 1))).carrier :=
      (ball_to_stage (m + 1)).symm (y : (S.stage (m + 1)).carrier)
    have hzR : dist z (closedBallModel X (r (m + 1)) (hr (m + 1))).base ≤ R := by
      dsimp [z]
      rw [← hbase_inv]
      calc
        dist ((ball_to_stage (m + 1)).symm (y : (S.stage (m + 1)).carrier))
            ((ball_to_stage (m + 1)).symm ((S.stage (m + 1)).base)) =
          dist (y : (S.stage (m + 1)).carrier) ((S.stage (m + 1)).base) :=
            (ball_to_stage (m + 1)).symm.isometry.dist_eq _ _
        _ ≤ R := hyR
    have hzR' : dist z.1 X.base ≤ R := by
      change dist z.1 X.base ≤ R at hzR
      exact hzR
    have hzRm : dist z.1 X.base ≤ r m := hzR'.trans hRm
    let q : (closedBallModel X (r m) (hr m)).carrier := ⟨z.1, hzRm⟩
    obtain ⟨u, hu⟩ := (inner_to_ball m).surjective q
    have huR : dist (u : (inner m).carrier) (inner m).base ≤ R := by
      calc
        dist (u : (inner m).carrier) (inner m).base =
            dist ((inner_to_ball m) u) ((inner_to_ball m) (inner m).base) :=
          ((inner_to_ball m).isometry.dist_eq _ _).symm
        _ = dist q (closedBallModel X (r m) (hr m)).base := by
          rw [hu, inner_to_ball_base m]
        _ ≤ R := by
          change dist q.1 X.base ≤ R
          exact hzR'
    obtain ⟨x, hx⟩ := (e m).surjective u
    have hxR : dist (x : (S.stage m).carrier) (S.stage m).base ≤ R := by
      calc
        dist (x : (S.stage m).carrier) (S.stage m).base =
            dist ((e m) x) ((e m) (S.stage m).base) :=
          ((e m).isometry.dist_eq _ _).symm
        _ = dist u (inner m).base := by rw [hx, e_base m]
        _ ≤ R := huR
    let x' : Metric.closedBall (S.stage m).base R := ⟨x, hxR⟩
    refine ⟨x', ?_⟩
    apply Subtype.ext
    change S.transitionChain m 1 x = y
    simp only [transitionChain, Function.comp_apply, id_eq, Nat.add_zero]
    rw [hfac m]
    simp only [Function.comp_apply]
    rw [hx, hu]
    calc
      (ball_to_stage (m + 1))
          (closedBallModelInclusion X (r m) (r (m + 1))
            (hr m) (hr (m + 1)) (hmono m) q) =
          (ball_to_stage (m + 1)) z := by
            congr 1
      _ = y := by
        simp [z]
  intro k
  induction k with
  | zero =>
      intro y
      exact ⟨y, rfl⟩
  | succ k ih =>
      intro y
      obtain ⟨z, hz⟩ := hstep (n + k) (hRtail k) y
      obtain ⟨x, hx⟩ := ih z
      refine ⟨x, ?_⟩
      apply Subtype.ext
      have hx' := congrArg Subtype.val hx
      change S.transitionChain n k (x : (S.stage n).carrier) =
        (z : (S.stage (n + k)).carrier) at hx'
      have hz' := congrArg Subtype.val hz
      change S.transition (n + k) (z : (S.stage (n + k)).carrier) =
        (y : (S.stage ((n + k) + 1)).carrier) at hz'
      change S.transition (n + k)
          (S.transitionChain n k (x : (S.stage n).carrier)) =
        (y : (S.stage (n + (k + 1))).carrier)
      rw [hx', hz']

/-- **Math.** If the compact stages and inner models are explicitly identified
with cofinal nested closed balls, the constructor `nestedCompactSystem` has
surjective restricted transition chains at every prescribed radius.  The
cofinal radius hypothesis and all common-limit identifications are explicit;
this does not perform the independent compact-limit extraction or ambient
pointed assembly.
-/
theorem exists_transitionChainClosedBallMap_surjective_of_nestedCompactSystem
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (radius : ℕ → ℝ) (hradius : ∀ n, 0 ≤ radius n)
    (hradius_mono : ∀ n, radius n ≤ radius (n + 1))
    (inner_to_ball : ∀ n,
      (inner n).carrier ≃ᵢ
        (closedBallModel X (radius n) (hradius n)).carrier)
    (inner_to_ball_base : ∀ n,
      inner_to_ball n (inner n).base =
        (closedBallModel X (radius n) (hradius n)).base)
    (ball_to_stage : ∀ n,
      (closedBallModel X (radius n) (hradius n)).carrier ≃ᵢ
        (stage n).carrier)
    (ball_to_stage_base : ∀ n,
      ball_to_stage n (closedBallModel X (radius n) (hradius n)).base =
        (stage n).base)
    (hradius_cofinal : Tendsto radius atTop atTop) :
    ∀ R : ℝ, ∃ n : ℕ, ∀ k : ℕ,
      Function.Surjective
        ((nestedCompactSystem X stage inner source hstage hinner radius
          hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
          ball_to_stage_base).transitionChainClosedBallMap n k R) := by
  let S := nestedCompactSystem X stage inner source hstage hinner radius
    hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
    ball_to_stage_base
  have hfactor :
      ∃ e : ∀ i, (S.stage i).carrier ≃ᵢ (inner i).carrier,
        ∀ i, S.transition i =
          (ball_to_stage (i + 1)) ∘
            (closedBallModelInclusion X (radius i) (radius (i + 1))
              (hradius i) (hradius (i + 1)) (hradius_mono i)) ∘
              (inner_to_ball i) ∘ e i := by
    dsimp [S, nestedCompactSystem]
    exact ⟨_, by intro i; rfl⟩
  obtain ⟨e, hfac⟩ := hfactor
  have e_base : ∀ i, e i (S.stage i).base = (inner i).base := by
    intro i
    let embed : (inner i).carrier → (S.stage (i + 1)).carrier :=
      (ball_to_stage (i + 1)) ∘
        (closedBallModelInclusion X (radius i) (radius (i + 1))
          (hradius i) (hradius (i + 1)) (hradius_mono i)) ∘
          (inner_to_ball i)
    have hembed_inj : Function.Injective embed := by
      exact ((ball_to_stage (i + 1)).isometry.comp
        ((closedBallModelInclusion_isometry X (radius i) (radius (i + 1))
          (hradius i) (hradius (i + 1)) (hradius_mono i)).comp
          (inner_to_ball i).isometry)).injective
    have hembed_base :
        embed (inner i).base = (S.stage (i + 1)).base := by
      dsimp [embed]
      rw [inner_to_ball_base i]
      rw [closedBallModelInclusion_base X (radius i) (radius (i + 1))
        (hradius i) (hradius (i + 1)) (hradius_mono i)]
      exact ball_to_stage_base (i + 1)
    have ht := S.transition_base i
    have hte : embed (e i (S.stage i).base) = (S.stage (i + 1)).base := by
      rw [← ht, hfac i]
      rfl
    exact hembed_inj (hte.trans hembed_base.symm)
  intro R
  have hev : ∀ᶠ n : ℕ in atTop, R ≤ radius n :=
    (Filter.tendsto_atTop.1 hradius_cofinal) R
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hev
  refine ⟨n, ?_⟩
  exact surjective_transitionChain_of_factorization S X inner radius hradius
    hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
    ball_to_stage_base e e_base hfac n R (hn n le_rfl)

/-- **Math.** Cofinal nested closed-ball identifications make the completed
inductive limit radially exhausted by its compact stage images.  This is the
constructor-specific coverage conclusion extracted from finite transition-chain
stability; no external ambient identification is assumed. -/
theorem radial_stage_coverage_of_nestedCompactSystem
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (radius : ℕ → ℝ) (hradius : ∀ n, 0 ≤ radius n)
    (hradius_mono : ∀ n, radius n ≤ radius (n + 1))
    (inner_to_ball : ∀ n,
      (inner n).carrier ≃ᵢ
        (closedBallModel X (radius n) (hradius n)).carrier)
    (inner_to_ball_base : ∀ n,
      inner_to_ball n (inner n).base =
        (closedBallModel X (radius n) (hradius n)).base)
    (ball_to_stage : ∀ n,
      (closedBallModel X (radius n) (hradius n)).carrier ≃ᵢ
        (stage n).carrier)
    (ball_to_stage_base : ∀ n,
      ball_to_stage n (closedBallModel X (radius n) (hradius n)).base =
        (stage n).base)
    (hradius_cofinal : Tendsto radius atTop atTop) :
    ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall
          (nestedCompactSystem X stage inner source hstage hinner radius
            hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
            ball_to_stage_base).completedLimit.base R ⊆
        Set.range
          ((nestedCompactSystem X stage inner source hstage hinner radius
            hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
            ball_to_stage_base).stageEmbedding n) := by
  let S := nestedCompactSystem X stage inner source hstage hinner radius
    hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
    ball_to_stage_base
  have hstable : ∀ R : ℝ, ∃ n : ℕ, ∀ k : ℕ,
      Function.Surjective (S.transitionChainClosedBallMap n k (R + 1)) := by
    intro R
    obtain ⟨n, hn⟩ :=
      exists_transitionChainClosedBallMap_surjective_of_nestedCompactSystem
        X stage inner source hstage hinner radius hradius hradius_mono
        inner_to_ball inner_to_ball_base ball_to_stage ball_to_stage_base
        hradius_cofinal (R + 1)
    exact ⟨n, hn⟩
  exact S.radial_stage_coverage_of_transitionChainClosedBallMap_surjective
    hstable

/-! The constructor-specific stability now has direct completed-limit consumers.
It gives properness, gives the length-space property when the compact stages
are length spaces, and identifies the compatible stage sequence's unbounded
pointed-GH limit.  Extracting these compatible stages from an independent
source sequence remains a separate compactness problem.
-/

/-- **Math.** Cofinal nested closed-ball identifications make the completed
inductive-limit carrier proper.  The proof routes the constructor-specific
transition stability through radial coverage; no target-space identification
or unbounded convergence is inferred here.
-/
theorem properSpace_completedLimit_of_nestedCompactSystem
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (radius : ℕ → ℝ) (hradius : ∀ n, 0 ≤ radius n)
    (hradius_mono : ∀ n, radius n ≤ radius (n + 1))
    (inner_to_ball : ∀ n,
      (inner n).carrier ≃ᵢ
        (closedBallModel X (radius n) (hradius n)).carrier)
    (inner_to_ball_base : ∀ n,
      inner_to_ball n (inner n).base =
        (closedBallModel X (radius n) (hradius n)).base)
    (ball_to_stage : ∀ n,
      (closedBallModel X (radius n) (hradius n)).carrier ≃ᵢ
        (stage n).carrier)
    (ball_to_stage_base : ∀ n,
      ball_to_stage n (closedBallModel X (radius n) (hradius n)).base =
        (stage n).base)
    (hradius_cofinal : Tendsto radius atTop atTop) :
    ProperSpace
      (nestedCompactSystem X stage inner source hstage hinner radius
        hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
        ball_to_stage_base).completedLimit.carrier := by
  let S := nestedCompactSystem X stage inner source hstage hinner radius
    hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
    ball_to_stage_base
  have hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n) :=
    radial_stage_coverage_of_nestedCompactSystem
      X stage inner source hstage hinner radius hradius hradius_mono
      inner_to_ball inner_to_ball_base ball_to_stage ball_to_stage_base
      hradius_cofinal
  exact S.properSpace_completedLimit_of_radial_stage_coverage hcover

/-- **Math.** If the cofinal nested compact stages are length spaces, then the
completed inductive limit is a length space.  Constructor stability supplies
the radial coverage needed to push distance-realizing stage paths into the
completion. -/
theorem lengthSpace_completedLimit_of_nestedCompactSystem
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (radius : ℕ → ℝ) (hradius : ∀ n, 0 ≤ radius n)
    (hradius_mono : ∀ n, radius n ≤ radius (n + 1))
    (inner_to_ball : ∀ n,
      (inner n).carrier ≃ᵢ
        (closedBallModel X (radius n) (hradius n)).carrier)
    (inner_to_ball_base : ∀ n,
      inner_to_ball n (inner n).base =
        (closedBallModel X (radius n) (hradius n)).base)
    (ball_to_stage : ∀ n,
      (closedBallModel X (radius n) (hradius n)).carrier ≃ᵢ
        (stage n).carrier)
    (ball_to_stage_base : ∀ n,
      ball_to_stage n (closedBallModel X (radius n) (hradius n)).base =
        (stage n).base)
    (hradius_cofinal : Tendsto radius atTop atTop)
    (hstage_length : ∀ n, LengthSpace (stage n).carrier) :
    LengthSpace
      (nestedCompactSystem X stage inner source hstage hinner radius
        hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
        ball_to_stage_base).completedLimit.carrier := by
  let S := nestedCompactSystem X stage inner source hstage hinner radius
    hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
    ball_to_stage_base
  have hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n) :=
    radial_stage_coverage_of_nestedCompactSystem
      X stage inner source hstage hinner radius hradius hradius_mono
      inner_to_ball inner_to_ball_base ball_to_stage ball_to_stage_base
      hradius_cofinal
  have hstage_lengthS : ∀ n, LengthSpace (S.stage n).carrier := by
    intro n
    change LengthSpace (stage n).carrier
    exact hstage_length n
  exact S.lengthSpace_completedLimit_of_radial_stage_coverage
    hcover hstage_lengthS

/-- **Math.** The compatible compact stages built from cofinal nested ball
limits converge in the unbounded pointed Gromov--Hausdorff sense to their
completed inductive limit.  Every fixed open ball is eventually pointed-
isometric to the corresponding limit ball, with zero radius perturbation. -/
theorem pointedGHConvergesUnbounded_stage_of_nestedCompactSystem
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (radius : ℕ → ℝ) (hradius : ∀ n, 0 ≤ radius n)
    (hradius_mono : ∀ n, radius n ≤ radius (n + 1))
    (inner_to_ball : ∀ n,
      (inner n).carrier ≃ᵢ
        (closedBallModel X (radius n) (hradius n)).carrier)
    (inner_to_ball_base : ∀ n,
      inner_to_ball n (inner n).base =
        (closedBallModel X (radius n) (hradius n)).base)
    (ball_to_stage : ∀ n,
      (closedBallModel X (radius n) (hradius n)).carrier ≃ᵢ
        (stage n).carrier)
    (ball_to_stage_base : ∀ n,
      ball_to_stage n (closedBallModel X (radius n) (hradius n)).base =
        (stage n).base)
    (hradius_cofinal : Tendsto radius atTop atTop) :
    PointedGHConvergesUnbounded
      (fun n =>
        (nestedCompactSystem X stage inner source hstage hinner radius
          hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
          ball_to_stage_base).stageBundle n)
      (nestedCompactSystem X stage inner source hstage hinner radius
        hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
        ball_to_stage_base).completedLimit := by
  let S := nestedCompactSystem X stage inner source hstage hinner radius
    hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
    ball_to_stage_base
  have hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n) :=
    radial_stage_coverage_of_nestedCompactSystem
      X stage inner source hstage hinner radius hradius hradius_mono
      inner_to_ball inner_to_ball_base ball_to_stage ball_to_stage_base
      hradius_cofinal
  exact S.pointedGHConvergesUnbounded_stage_of_radial_stage_coverage hcover

end CompatiblePointedCompactSystem

end MorganTianLib

end

#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.exists_transitionChainClosedBallMap_surjective_of_nestedCompactSystem
#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.radial_stage_coverage_of_nestedCompactSystem
#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.properSpace_completedLimit_of_nestedCompactSystem
#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.lengthSpace_completedLimit_of_nestedCompactSystem
#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.pointedGHConvergesUnbounded_stage_of_nestedCompactSystem
