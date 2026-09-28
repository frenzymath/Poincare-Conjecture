import EvansLib.Ch02.WaveSphericalMeans
import EvansLib.Ch02.WaveMixedDerivatives

/-!
# Time derivatives of Evans's odd-dimensional radial transform

The explicit finite-sum expansion of the transform, together with Schwarz
commutation for smooth coordinate slices, shows that every time derivative
passes through the radial transform at positive radii.
-/

open Filter
open scoped ContDiff BigOperators Topology

noncomputable section

namespace EvansLib

/-- Evans's transformed radial profile in odd dimension `2 * k + 1`. -/
def waveRadialTransform (k : ℕ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  radialIter (k - 1) (fun s => s ^ (2 * k - 1) * F (s, p.2)) p.1

/-- Evans's radial transform commutes with multiplication by a constant. -/
theorem waveRadialTransform_const_smul (k : ℕ) (c : ℝ) (F : ℝ × ℝ → ℝ) :
    waveRadialTransform k (c • F) = c • waveRadialTransform k F := by
  funext p
  unfold waveRadialTransform
  have hprofile :
      (fun s : ℝ => s ^ (2 * k - 1) * (c • F) (s, p.2)) =
        c • (fun s : ℝ => s ^ (2 * k - 1) * F (s, p.2)) := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hprofile, radialIter_const_smul]
  rfl

/-- Finite-order time derivatives commute with Evans's radial transform at a
positive radius.  The input has exactly the joint regularity needed by the
radial and time derivatives used below. -/
theorem iteratedDeriv_waveRadialTransform_time_of_order {k order : ℕ}
    (hk : 1 ≤ k) {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ (k - 1 + order : ℕ) F)
    {r t : ℝ} (hr : 0 < r) :
    iteratedDeriv order (fun tau => waveRadialTransform k F (r, tau)) t =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        iteratedDeriv order (fun tau => F (s, tau)) t) r := by
  let C : ℕ → ℝ := fun j => evansRadialCoeff k j * r ^ (j + 1)
  have hslice (tau : ℝ) : ContDiff ℝ (k - 1 : ℕ) (fun s => F (s, tau)) := by
    exact (hF.comp (contDiff_id.prodMk contDiff_const)).of_le
      (by exact_mod_cast (show k - 1 ≤ k - 1 + order by omega))
  have htransform : (fun tau => waveRadialTransform k F (r, tau)) =
      fun tau => ∑ j ∈ Finset.range k,
        C j * iteratedDeriv j (fun s => F (s, tau)) r := by
    funext tau
    simpa [waveRadialTransform, C, mul_assoc] using
      waveRadial_expansion_of_order hk (hslice tau) hr
  rw [htransform]
  rw [iteratedDeriv_fun_sum]
  · simp_rw [iteratedDeriv_const_mul_field]
    have hprofile : ContDiff ℝ (k - 1 : ℕ)
        (fun s => iteratedDeriv order (fun tau => F (s, tau)) t) := by
      apply contDiff_iteratedDeriv_snd_slice_of_order
      simpa [Nat.add_comm] using hF
    rw [waveRadial_expansion_of_order hk hprofile hr]
    apply Finset.sum_congr rfl
    intro j hj
    rw [iteratedDeriv_slices_comm_of_order
      (hF.of_le (by
        exact_mod_cast (show order + j ≤ k - 1 + order by
          have := Finset.mem_range.mp hj
          omega))) r t]
  · intro j hj
    have hbase : ContDiff ℝ order
        (fun tau => iteratedDeriv j (fun s => F (s, tau)) r) := by
      apply contDiff_iteratedDeriv_fst_slice_of_order
      exact hF.of_le (by
        exact_mod_cast (show j + order ≤ k - 1 + order by
          have := Finset.mem_range.mp hj
          omega))
    simpa only [smul_eq_mul] using
      ContDiffAt.const_smul (C j) hbase.contDiffAt

/-- Every finite-order time derivative commutes with Evans's radial transform
at a positive radius. -/
theorem iteratedDeriv_waveRadialTransform_time {k order : ℕ} (hk : 1 ≤ k)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {r t : ℝ} (hr : 0 < r) :
    iteratedDeriv order (fun tau => waveRadialTransform k F (r, tau)) t =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        iteratedDeriv order (fun tau => F (s, tau)) t) r := by
  let C : ℕ → ℝ := fun j => evansRadialCoeff k j * r ^ (j + 1)
  have hslice (tau : ℝ) : ContDiff ℝ k (fun s => F (s, tau)) := by
    apply (hF.comp (contDiff_id.prodMk contDiff_const)).of_le
    exact WithTop.coe_le_coe.mpr (show (k : ℕ∞) ≤ ⊤ from le_top)
  have htransform : (fun tau => waveRadialTransform k F (r, tau)) =
      fun tau => ∑ j ∈ Finset.range k,
        C j * iteratedDeriv j (fun s => F (s, tau)) r := by
    funext tau
    simpa [waveRadialTransform, C, mul_assoc] using
      waveRadial_expansion hk (hslice tau) hr
  rw [htransform]
  rw [iteratedDeriv_fun_sum]
  · simp_rw [iteratedDeriv_const_mul_field]
    have hprofile : ContDiff ℝ k
        (fun s => iteratedDeriv order (fun tau => F (s, tau)) t) := by
      apply (contDiff_iteratedDeriv_snd_slice hF order t).of_le
      exact WithTop.coe_le_coe.mpr (show (k : ℕ∞) ≤ ⊤ from le_top)
    rw [waveRadial_expansion hk hprofile hr]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [iteratedDeriv_slices_comm hF order j r t]
  · intro j _hj
    have hinfty : ContDiffAt ℝ ∞
        (fun tau => C j * iteratedDeriv j (fun s => F (s, tau)) r) t := by
      simpa only [smul_eq_mul] using
        ContDiffAt.const_smul (C j)
          (contDiff_iteratedDeriv_fst_slice hF j r).contDiffAt
    apply hinfty.of_le
    exact WithTop.coe_le_coe.mpr (show (order : ℕ∞) ≤ ⊤ from le_top)

/-- Finite-order form of the genuine right-hand boundary trace.  Only the
`k` radial derivatives appearing in the finite expansion are required. -/
theorem waveRadialTransform_tendsto_zero_right_of_order {k : ℕ} (hk : 1 ≤ k)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ k F) (t : ℝ) :
    Tendsto (fun r => waveRadialTransform k F (r, t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let phi : ℝ → ℝ := fun r => F (r, t)
  let S : ℝ → ℝ := fun r =>
    ∑ j ∈ Finset.range k,
      evansRadialCoeff k j * r ^ (j + 1) * iteratedDeriv j phi r
  have hphi : ContDiff ℝ k phi :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have hScont : Continuous S := by
    apply continuous_finsetSum (Finset.range k)
    intro j hj
    exact (continuous_const.mul (continuous_id.pow (j + 1))).mul
      (hphi.continuous_iteratedDeriv j (by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))))
  have hSzero : S 0 = 0 := by
    simp [S]
  have heq : (fun r => waveRadialTransform k F (r, t)) =ᶠ[𝓝[>] (0 : ℝ)] S := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa [waveRadialTransform, phi] using waveRadial_expansion hk hphi hr
  apply Filter.Tendsto.congr'
    (f₁ := S) (f₂ := fun r => waveRadialTransform k F (r, t))
  · exact heq.symm
  · have ht : Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 (S 0)) :=
      hScont.continuousAt.tendsto.mono_left inf_le_left
    simpa [hSzero] using ht

/-- The transformed profile has the genuine right-hand boundary trace zero.
This uses the finite radial expansion, rather than the totalized value of
division at `r = 0`. -/
theorem waveRadialTransform_tendsto_zero_right {k : ℕ} (hk : 1 ≤ k)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    Tendsto (fun r => waveRadialTransform k F (r, t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let phi : ℝ → ℝ := fun r => F (r, t)
  let S : ℝ → ℝ := fun r =>
    ∑ j ∈ Finset.range k,
      evansRadialCoeff k j * r ^ (j + 1) * iteratedDeriv j phi r
  have hphi : ContDiff ℝ ∞ phi :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have hphik : ContDiff ℝ k phi := by
    apply hphi.of_le
    exact WithTop.coe_le_coe.mpr (show (k : ℕ∞) ≤ ⊤ from le_top)
  have hScont : Continuous S := by
    apply continuous_finsetSum (Finset.range k)
    intro j _hj
    exact (continuous_const.mul (continuous_id.pow (j + 1))).mul
      (hphi.continuous_iteratedDeriv j
        (WithTop.coe_le_coe.mpr (show (j : ℕ∞) ≤ ⊤ from le_top)))
  have hSzero : S 0 = 0 := by
    simp [S]
  have heq : (fun r => waveRadialTransform k F (r, t)) =ᶠ[𝓝[>] (0 : ℝ)] S := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa [waveRadialTransform, phi] using waveRadial_expansion hk hphik hr
  apply Filter.Tendsto.congr'
    (f₁ := S) (f₂ := fun r => waveRadialTransform k F (r, t))
  · exact heq.symm
  · have ht : Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 (S 0)) :=
      hScont.continuousAt.tendsto.mono_left inf_le_left
    simpa [hSzero] using ht

end EvansLib
