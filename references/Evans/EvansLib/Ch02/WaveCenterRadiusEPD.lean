import EvansLib.Ch02.WaveCenterRadiusMean
import EvansLib.Ch02.LaplaceRadialPointwise

/-!
# The center-radius Darboux equation

The sourced weak radial identity for a spatial function becomes a pointwise
equation for its normalized spherical averages.  The source is the spherical
average of the spatial Laplacian; joint center-radius differentiation then
identifies it with the center Laplacian of the average.
-/

open Filter MeasureTheory Metric Set
open scoped Real ContDiff Topology
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : ℕ}

private lemma laplacian_comp_add_left_data
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Δ (fun z => f (x + z)) = fun z => Δ f (x + z) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  funext z
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_comp_add_left]

/-- Divergence form of the center-radius Darboux equation. -/
theorem deriv_weightedDeriv_unitSphereRadialAverageAt_eq_laplacian
    [Nonempty (Fin n)]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hn : 0 < n) (hf : ContDiff ℝ 2 f)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    deriv (fun s : ℝ => s ^ (n - 1) *
        deriv (unitSphereRadialAverageAt f x) s) r =
      r ^ (n - 1) *
        Δ (fun y => unitSphereRadialAverageAt f y r) x := by
  let c : ℝ :=
    (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹
  let A : ℝ → ℝ := unitSphereRadialAverageAt f x
  let B : ℝ → ℝ := fun s => s ^ (n - 1) *
    unitSphereRadialAverageAt (Δ f) x s
  let v : EuclideanSpace ℝ (Fin n) → ℝ := fun z => f (x + z)
  let R : ℝ := r + 1
  have hA : ContDiff ℝ 2 A :=
    unitSphereRadialAverageAt_contDiff_of_order hf x
  have hlapcont : Continuous (Δ f) := by
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    fun_prop
  have hlapC0 : ContDiff ℝ 0 (Δ f) :=
    contDiff_zero.mpr hlapcont
  have hB : Continuous B := by
    exact (continuous_id.pow (n - 1)).mul
      (unitSphereRadialAverageAt_contDiff_of_order hlapC0 x).continuous
  have hv : ContDiff ℝ 2 v :=
    hf.comp (contDiff_const.add contDiff_id)
  have hweak : ∀ (phi : ℝ → ℝ), ContDiff ℝ ∞ phi →
      HasCompactSupport phi → tsupport phi ⊆ Ioo (0 : ℝ) R →
      ∫ s in Ioi (0 : ℝ), A s *
          deriv (fun q : ℝ => q ^ (n - 1) * deriv phi q) s =
        ∫ s in Ioi (0 : ℝ), B s * phi s := by
    intro phi hphi _hphic hphiSupp
    have hsourced :=
      integral_unitSphereRadialIntegral_mul_deriv_weightedDeriv_eq_source
        hn isOpen_univ hv.contDiffOn
        (show 0 ≤ R by dsimp [R]; linarith) (subset_univ _)
        hphi hphiSupp
    have hlap : Δ v = fun z => Δ f (x + z) := by
      exact laplacian_comp_add_left_data f x
    have hscaled := congrArg (fun z : ℝ => c * z) hsourced
    calc
      ∫ s in Ioi (0 : ℝ), A s *
          deriv (fun q : ℝ => q ^ (n - 1) * deriv phi q) s =
          c * ∫ s in Ioi (0 : ℝ),
            unitSphereRadialIntegral v s *
              deriv (fun q : ℝ => q ^ (n - 1) * deriv phi q) s := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with s
        rw [show A s = c * unitSphereRadialIntegral v s by
          simp [A, c, v, unitSphereRadialAverageAt_eq,
            unitSphereRadialIntegralAt, unitSphereRadialIntegral]]
        ring
      _ = c * ∫ s in Ioi (0 : ℝ), s ^ (n - 1) *
          unitSphereRadialIntegral (Δ v) s * phi s := hscaled
      _ = ∫ s in Ioi (0 : ℝ), B s * phi s := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with s
        rw [show B s = c * (s ^ (n - 1) *
            unitSphereRadialIntegral (Δ v) s) by
          rw [hlap]
          simp [B, c, unitSphereRadialAverageAt_eq,
            unitSphereRadialIntegralAt, unitSphereRadialIntegral]
          ring]
        ring
  have hpoint :=
    deriv_weightedDeriv_eq_of_integral_mul_deriv_weightedDeriv_eq
      hA hB hweak r (show r ∈ Ioo (0 : ℝ) R by
        constructor
        · exact hr
        · dsimp [R]
          linarith)
  rw [laplacian_unitSphereRadialAverageAt hf x r]
  exact hpoint

/-- A normalized spherical average satisfies
`Δ_x M = M_rr + (n - 1) / r * M_r` at every positive radius. -/
theorem unitSphereRadialAverageAt_euler_poisson_darboux
    [Nonempty (Fin n)]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hn : 2 ≤ n) (hf : ContDiff ℝ 2 f)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    Δ (fun y => unitSphereRadialAverageAt f y r) x =
      deriv (deriv (unitSphereRadialAverageAt f x)) r +
        ((n : ℝ) - 1) / r * deriv (unitSphereRadialAverageAt f x) r := by
  let A : ℝ → ℝ := unitSphereRadialAverageAt f x
  let T : ℝ := Δ (fun y => unitSphereRadialAverageAt f y r) x
  have hA : ContDiff ℝ 2 A :=
    unitSphereRadialAverageAt_contDiff_of_order hf x
  have hweighted :
      deriv (fun s : ℝ => s ^ (n - 1) * deriv A s) r =
        r ^ (n - 1) * T :=
    deriv_weightedDeriv_unitSphereRadialAverageAt_eq_laplacian
      (lt_of_lt_of_le Nat.zero_lt_two hn) hf x r hr
  have hA' : ContDiff ℝ 1 (deriv A) :=
    (contDiff_succ_iff_deriv.mp hA).2.2
  have hpow : HasDerivAt (fun s : ℝ => s ^ (n - 1))
      ((n - 1 : ℕ) * r ^ (n - 2)) r := by
    convert (hasDerivAt_id r).pow (n - 1) using 1
    · rfl
    · exact Module.ext rfl
    · rfl
    · simp only [id_eq, Nat.sub_sub, Nat.reduceAdd]
      simp
  have hderivA : HasDerivAt (deriv A) (deriv (deriv A) r) r :=
    (hA'.differentiable (by simp) r).hasDerivAt
  have hproduct :
      deriv (fun s : ℝ => s ^ (n - 1) * deriv A s) r =
        ((n - 1 : ℕ) : ℝ) * r ^ (n - 2) * deriv A r +
          r ^ (n - 1) * deriv (deriv A) r := by
    change deriv ((fun s : ℝ => s ^ (n - 1)) * deriv A) r = _
    exact (hpow.mul hderivA).deriv
  rw [hproduct] at hweighted
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hpowRel : r ^ (n - 1) = r ^ (n - 2) * r := by
    rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
  have heq : r ^ (n - 2) *
        (((n : ℝ) - 1) * deriv A r + r * deriv (deriv A) r) =
      r ^ (n - 2) * (r * T) := by
    calc
      r ^ (n - 2) *
          (((n : ℝ) - 1) * deriv A r + r * deriv (deriv A) r) =
        ((n - 1 : ℕ) : ℝ) * r ^ (n - 2) * deriv A r +
          r ^ (n - 1) * deriv (deriv A) r := by
            rw [hcast, hpowRel]
            ring
      _ = r ^ (n - 1) * T := hweighted
      _ = r ^ (n - 2) * (r * T) := by rw [hpowRel]; ring
  have hcancel :
      ((n : ℝ) - 1) * deriv A r + r * deriv (deriv A) r = r * T :=
    mul_left_cancel₀ (ne_of_gt (pow_pos hr (n - 2))) heq
  change T = deriv (deriv A) r + ((n : ℝ) - 1) / r * deriv A r
  field_simp [hr.ne']
  linarith

end EvansLib
