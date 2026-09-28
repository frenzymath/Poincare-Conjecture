import MorganTianLib.Ch05.ClosedBallCompatibility
import MorganTianLib.Ch05.FinitePackingNets

/-!
# Morgan--Tian Chapter 5: finite nets on proper metric balls

This adapter packages the compactness supplied by properness with the finite-net
and pointed-GH producers.  It is useful when a finite-radius limit is obtained
independently: each proper closed ball has an explicit shrinking sequence of
finite based nets converging to its canonical closed-ball model.
-/

open Set Filter Topology
open scoped Topology

namespace MorganTianLib

universe u

/-- **Math.** Every nonnegative-radius closed ball in a proper metric space has
an explicit shrinking sequence of finite based nets whose finite models
converge in pointed Gromov--Hausdorff distance to the closed-ball model.

The net sets live in the closed-ball subtype, so the based point and all
metric restrictions are retained definitionally. -/
theorem exists_finite_deltaNet_approximation_of_proper_closedBall
    (X : BasedMetricSpaceBundle.{u}) [ProperSpace X.carrier]
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ delta : ℕ → ℝ, ∃ L : ℕ → Set (Metric.closedBall X.base r),
      Tendsto delta atTop (𝓝 0) ∧
      (∀ k, 0 < delta k) ∧
      (∃ hL : ∀ k, IsDeltaNet (delta k)
          (closedBallModel X r hr).base (L k),
        (∀ k, (L k).Finite) ∧
        PointedGHConverges
          (fun k => deltaNetModel (closedBallModel X r hr) (L k)
            (hL k).1)
          (closedBallModel X r hr)) := by
  letI : CompactSpace (closedBallModel X r hr).carrier :=
    isCompact_iff_compactSpace.mp (ProperSpace.isCompact_closedBall X.base r)
  let delta : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hdelta_pos : ∀ k, 0 < delta k := by
    intro k
    simp only [delta]
    positivity
  have hdelta : Tendsto delta atTop (𝓝 0) := by
    simpa [delta] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose L hspec using fun k =>
    exists_finite_isDeltaNet_of_compactSpace
      (delta k) (hdelta_pos k) (closedBallModel X r hr).base
  let hL' : ∀ k, IsDeltaNet (delta k)
      (closedBallModel X r hr).base (L k) := fun k => (hspec k).2
  refine ⟨delta, L, hdelta, hdelta_pos, ?_⟩
  refine ⟨hL', ?_, ?_⟩
  · exact fun k => (hspec k).1
  · apply pointedGHConverges_deltaNet
      (closedBallModel X r hr) delta
      (fun k => (hdelta_pos k).le) hdelta L hL'

/-! The cardinal-bounded variant is the form consumed by uniform-cover and
packing arguments.  Properness supplies the all-scale packing bound because
every closed ball in the closed-ball subtype is compact. -/

/-- **Math.** Properness gives a shrinking finite-net approximation of each
closed ball with an explicit cardinal bound at every mesh scale. -/
theorem exists_finite_deltaNet_approximation_of_proper_closedBall_with_card
    (X : BasedMetricSpaceBundle.{u}) [ProperSpace X.carrier]
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ delta : ℕ → ℝ, ∃ L : ℕ → Set (Metric.closedBall X.base r),
      ∃ bound : ℕ → ℕ,
        Tendsto delta atTop (𝓝 0) ∧
        (∀ k, 0 < delta k) ∧
        (∃ hL : ∀ k, IsDeltaNet (delta k)
            (closedBallModel X r hr).base (L k),
          (∀ k, (L k).Finite) ∧
          (∀ k, (L k).ncard ≤ bound k) ∧
          PointedGHConverges
            (fun k => deltaNetModel (closedBallModel X r hr) (L k)
              (hL k).1)
            (closedBallModel X r hr)) := by
  have hpack : ∀ (δ' S : ℝ), 0 < δ' →
      ∃ N : ℕ, ∀ n,
        n ∈ packingAdmissible X.base δ' S → n ≤ N := by
    intro δ' S hδ'
    exact exists_packing_bound_of_totallyBounded_closedBall
      X.base hδ' (ProperSpace.isCompact_closedBall X.base S).totallyBounded
  let delta : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hdelta_pos : ∀ k, 0 < delta k := by
    intro k
    simp only [delta]
    positivity
  have hdelta : Tendsto delta atTop (𝓝 0) := by
    simpa [delta] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose bound L hdata using fun k =>
    exists_finite_isDeltaNet_closedBall_of_uniform_packing_bound
      X.base (R := r) (δ := delta k)
      hr (hdelta_pos k) hpack
  have hLfin : ∀ k, (L k).Finite := fun k => (hdata k).1
  have hLcard : ∀ k, (L k).ncard ≤ bound k :=
    fun k => (hdata k).2.1
  have hLnet : ∀ k, IsDeltaNet (delta k)
      (closedBallModel X r hr).base (L k) :=
    fun k => (hdata k).2.2
  refine ⟨delta, L, bound, hdelta, hdelta_pos, ?_⟩
  refine ⟨hLnet, hLfin, hLcard, ?_⟩
  exact pointedGHConverges_deltaNet
    (closedBallModel X r hr) delta
    (fun k => (hdelta_pos k).le) hdelta L hLnet

end MorganTianLib

#print axioms MorganTianLib.exists_finite_deltaNet_approximation_of_proper_closedBall
#print axioms MorganTianLib.exists_finite_deltaNet_approximation_of_proper_closedBall_with_card
