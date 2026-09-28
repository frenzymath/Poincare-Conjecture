import MorganTianLib.Ch05.Precompactness
import MorganTianLib.Ch05.MarkedGHExtraction

/-!
# Morgan--Tian Chapter 5: marked packing diagonal

This adapter composes the uniform-packing compact-ball diagonal with the
marked realization extraction.  It closes the common-subsequence/basepoint
part of the finite-radius argument; cross-radius identifications are still
explicit data for the nested-system constructor.
-/

open Set Filter Topology

noncomputable section

namespace MorganTianLib

/-! **Math.** Uniform packing bounds on a complete based sequence yield, after
one common subsequence, a pointed compact GH realization at every integer
radius.  The theorem deliberately leaves compatibility between radii to the
subsequent nested-assembly producer. -/
theorem exists_subseq_common_marked_closedBall_limits_of_uniform_packing_bounds
    (X : ℕ → BasedMetricSpaceBundle.{0})
    [∀ k, CompleteSpace (X k).carrier]
    (hpack : ∀ δ S, 0 < δ → ∃ N : ℕ, ∀ k n,
      n ∈ packingAdmissible (X k).base δ S → n ≤ N) :
    ∃ φ : ℕ → ℕ, ∃ Y : ℕ → PointedCompactMetricSpace.{0},
      StrictMono φ ∧
      ∀ i, ∃ S : VaryingRealizationSequence
          (fun n =>
            (uniformPackingBoundedClosedBall X hpack (φ n) i).toFiniteDiameterBasedMetricSpace.toBasedMetricSpaceBundle)
          (PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace
            (Y i)).toBasedMetricSpaceBundle,
        Tendsto
          (fun n => @Metric.hausdorffDist (S.ambient n).carrier inferInstance
            (Set.range (S.left n)) (Set.range (S.right n)))
          atTop (𝓝 0) ∧
        PointedGHConverges
          (fun n =>
            (uniformPackingBoundedClosedBall X hpack (φ n) i).toFiniteDiameterBasedMetricSpace)
          (PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace (Y i)) := by
  obtain ⟨p, φ₀, hφ₀, hgh₀⟩ :=
    exists_subseq_tendsto_closedBallGHSpace_of_uniform_packing_bounds X hpack
  let A : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{0} := fun i n =>
    (uniformPackingBoundedClosedBall X hpack (φ₀ n) i).toFiniteDiameterBasedMetricSpace
  letI compactA : ∀ i n, CompactSpace (A i n).carrier := fun i n => by
    dsimp [A]
    exact (uniformPackingBoundedClosedBall X hpack (φ₀ n) i).compact
  have hbounded : ∀ i, UniformlyBoundedDiameter (A i) := by
    intro i
    refine ⟨2 * (i : ℝ), ?_⟩
    intro n x y
    change dist (x.1 : (X (φ₀ n)).carrier) (y.1 : (X (φ₀ n)).carrier) ≤ 2 * (i : ℝ)
    calc
      dist (x.1 : (X (φ₀ n)).carrier) (y.1 : (X (φ₀ n)).carrier) ≤
          dist (x.1 : (X (φ₀ n)).carrier) (X (φ₀ n)).base +
            dist (X (φ₀ n)).base (y.1 : (X (φ₀ n)).carrier) := dist_triangle _ _ _
      _ ≤ (i : ℝ) + (i : ℝ) := by
        apply add_le_add
        · exact Metric.mem_closedBall.mp x.property
        · simpa [dist_comm] using Metric.mem_closedBall.mp y.property
      _ = 2 * (i : ℝ) := by ring
  have hgh : ∀ i, Tendsto
      (fun n => GromovHausdorff.toGHSpace (A i n).carrier)
      atTop (𝓝 (p i)) := by
    intro i
    change Tendsto
      (fun n => GromovHausdorff.toGHSpace
        (uniformPackingBoundedClosedBall X hpack (φ₀ n) i).carrier)
      atTop (𝓝 (p i))
    exact hgh₀ i
  obtain ⟨φ₁, Y, hφ₁, _, hmarked⟩ :=
    exists_common_subseq_marked_realizations A hbounded p hgh
  let φ : ℕ → ℕ := fun n => φ₀ (φ₁ n)
  have hφ : StrictMono φ := hφ₀.comp hφ₁
  refine ⟨φ, Y, hφ, ?_⟩
  intro i
  obtain ⟨S, hS, hconv⟩ := hmarked i
  refine ⟨S, ?_, ?_⟩
  · simpa [φ, A] using hS
  · simpa [φ, A] using hconv

end MorganTianLib
