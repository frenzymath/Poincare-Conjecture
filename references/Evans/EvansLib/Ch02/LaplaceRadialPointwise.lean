import EvansLib.Ch02.LaplaceRadialProfile
import EvansLib.Ch02.LaplaceRadialSource

/-!
# The weak radial Laplace equation in standard test-function form

The sourced shell identity is phrased using a smooth profile in the squared
radius.  This file converts a smooth test function `phi`, compactly supported
away from zero, into such a profile by pulling it back along `sqrt`.  The
resulting radial operator is the derivative of `r^(n - 1) * phi'`, which is
the usual distributional form of the radial Laplace equation.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- A smooth extension of `rho |-> phi (sqrt rho)` when `phi` is supported
away from zero. -/
def sqrtPullbackProfile (phi : ℝ → ℝ) (rho : ℝ) : ℝ :=
  2 * invProfile phi 0 rho

lemma sqrtPullbackProfile_contDiff {phi : ℝ → ℝ} {R : ℝ}
    (hphi : ContDiff ℝ ∞ phi)
    (hphiSupp : tsupport phi ⊆ Ioo (0 : ℝ) R) :
    ContDiff ℝ ∞ (sqrtPullbackProfile phi) := by
  exact contDiff_const.mul (invProfile_contDiff (n := 0) hphi hphiSupp)

@[simp] lemma sqrtPullbackProfile_apply_sq {phi : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) :
    sqrtPullbackProfile phi (r ^ 2) = phi r := by
  simp [sqrtPullbackProfile, invProfile, sq_pos_of_pos hr,
    Real.sqrt_sq hr.le]
  ring

lemma sqrtPullbackProfile_eq_zero_of_sq_lt
    {phi : ℝ → ℝ} {R rho : ℝ} (hR : 0 ≤ R)
    (hphiSupp : tsupport phi ⊆ Ioo (0 : ℝ) R)
    (hrho : R ^ 2 < rho) :
    sqrtPullbackProfile phi rho = 0 := by
  rw [sqrtPullbackProfile,
    invProfile_eq_zero_of_sq_lt (n := 0) hR hphiSupp hrho]
  simp

/-- Differentiating `g(r^2) = phi r` for the square-root pullback gives the
first radial chain-rule identity. -/
lemma sqrtPullbackProfile_factor {phi : ℝ → ℝ} {R r : ℝ}
    (hphi : ContDiff ℝ ∞ phi)
    (hphiSupp : tsupport phi ⊆ Ioo (0 : ℝ) R) (hr : 0 < r) :
    2 * r * deriv (sqrtPullbackProfile phi) (r ^ 2) = deriv phi r := by
  have hg : ContDiff ℝ ∞ (sqrtPullbackProfile phi) :=
    sqrtPullbackProfile_contDiff hphi hphiSupp
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have hleft :=
    (hg.differentiable (by simp) (r ^ 2)).hasDerivAt.comp r hsq
  have hev :
      (fun s : ℝ => sqrtPullbackProfile phi (s ^ 2)) =ᶠ[nhds r] phi := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact sqrtPullbackProfile_apply_sq hs
  have hright :=
    ((hphi.differentiable (by simp) r).hasDerivAt).congr_of_eventuallyEq hev
  calc
    2 * r * deriv (sqrtPullbackProfile phi) (r ^ 2) =
        deriv (sqrtPullbackProfile phi) (r ^ 2) * (2 * r) := by ring
    _ = deriv phi r := hleft.unique hright

/-- For the square-root pullback, the squared-radius radial operator is the
derivative of the weighted test derivative. -/
lemma sqrtPullbackProfile_radialODE {phi : ℝ → ℝ} {R r : ℝ} {n : ℕ}
    (hn : 0 < n) (hphi : ContDiff ℝ ∞ phi)
    (hphiSupp : tsupport phi ⊆ Ioo (0 : ℝ) R) (hr : 0 < r) :
    r ^ (n - 1) *
        (4 * r ^ 2 * deriv (deriv (sqrtPullbackProfile phi)) (r ^ 2) +
          2 * n * deriv (sqrtPullbackProfile phi) (r ^ 2)) =
      deriv (fun s : ℝ => s ^ (n - 1) * deriv phi s) r := by
  let g : ℝ → ℝ := sqrtPullbackProfile phi
  let psi : ℝ → ℝ := fun s => s ^ (n - 1) * deriv phi s
  have hg : ContDiff ℝ ∞ g :=
    sqrtPullbackProfile_contDiff hphi hphiSupp
  have hphi' : ContDiff ℝ ∞ (deriv phi) :=
    (contDiff_infty_iff_deriv.mp hphi).2
  have hpsi : ContDiff ℝ ∞ psi := by
    exact (contDiff_id.pow (n - 1)).mul hphi'
  have hfactor : ∀ s : ℝ, 0 < s ->
      2 * s ^ n * deriv g (s ^ 2) = psi s := by
    intro s hs
    have hfirst := sqrtPullbackProfile_factor hphi hphiSupp hs
    have hpow : s ^ n = s ^ (n - 1) * s := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      exact pow_succ _ _
    simp only [g, psi]
    rw [hpow, ← hfirst]
    ring
  simpa only [g, psi] using
    radialODE_eq_deriv_of_factor hn hpsi hg hfactor r hr

/-- The sourced shell identity rewritten with an arbitrary smooth test
function compactly supported in `(0,R)`. -/
theorem integral_unitSphereRadialIntegral_mul_deriv_weightedDeriv_eq_source
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hn : 0 < n)
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {phi : ℝ → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hphiSupp : tsupport phi ⊆ Ioo (0 : ℝ) R) :
    ∫ r in Ioi (0 : ℝ), unitSphereRadialIntegral u r *
        deriv (fun s : ℝ => s ^ (n - 1) * deriv phi s) r =
      ∫ r in Ioi (0 : ℝ), r ^ (n - 1) *
        unitSphereRadialIntegral (Δ u) r * phi r := by
  let g : ℝ → ℝ := sqrtPullbackProfile phi
  have hg : ContDiff ℝ ∞ g :=
    sqrtPullbackProfile_contDiff hphi hphiSupp
  have hg' : ∀ rho : ℝ, 0 < rho -> HasDerivAt g (deriv g rho) rho := by
    intro rho _
    exact (hg.differentiable (by simp) rho).hasDerivAt
  have hgd : ContDiff ℝ ∞ (deriv g) :=
    (contDiff_infty_iff_deriv.mp hg).2
  have hg'' : ∀ rho : ℝ, 0 < rho ->
      HasDerivAt (deriv g) (deriv (deriv g) rho) rho := by
    intro rho _
    exact (hgd.differentiable (by simp) rho).hasDerivAt
  have hzero : ∀ rho : ℝ, R ^ 2 < rho -> g rho = 0 := by
    intro rho hrho
    exact sqrtPullbackProfile_eq_zero_of_sq_lt hR hphiSupp hrho
  have hsource := integral_radius_unitSphereRadialIntegral_radialODE_eq_source
    hU hu hR hball hg hg' hg'' hzero
  calc
    ∫ r in Ioi (0 : ℝ), unitSphereRadialIntegral u r *
        deriv (fun s : ℝ => s ^ (n - 1) * deriv phi s) r =
      ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * unitSphereRadialIntegral u r *
        (4 * r ^ 2 * deriv (deriv g) (r ^ 2) +
          2 * n * deriv g (r ^ 2)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume)
        (show MeasurableSet (Ioi (0 : ℝ)) from measurableSet_Ioi)] with r hr
      have hode := sqrtPullbackProfile_radialODE hn hphi hphiSupp hr
      calc
        unitSphereRadialIntegral u r *
            deriv (fun s : ℝ => s ^ (n - 1) * deriv phi s) r =
          unitSphereRadialIntegral u r *
            (r ^ (n - 1) *
              (4 * r ^ 2 * deriv (deriv g) (r ^ 2) +
                2 * n * deriv g (r ^ 2))) := by rw [hode]
        _ = r ^ (n - 1) * unitSphereRadialIntegral u r *
            (4 * r ^ 2 * deriv (deriv g) (r ^ 2) +
              2 * n * deriv g (r ^ 2)) := by ring
    _ = ∫ r in Ioi (0 : ℝ), r ^ (n - 1) *
        unitSphereRadialIntegral (Δ u) r * g (r ^ 2) := hsource
    _ = ∫ r in Ioi (0 : ℝ), r ^ (n - 1) *
        unitSphereRadialIntegral (Δ u) r * phi r := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume)
        (show MeasurableSet (Ioi (0 : ℝ)) from measurableSet_Ioi)] with r hr
      rw [show g (r ^ 2) = phi r by
        exact sqrtPullbackProfile_apply_sq hr]

/-- A smooth weak solution of the one-dimensional weighted radial equation is
a pointwise solution.  Compact support of the test function permits two
integrations by parts on the whole line; the fundamental lemma then gives an
almost-everywhere identity, which continuity upgrades to every point of
`(0, R)`. -/
theorem deriv_weightedDeriv_eq_of_integral_mul_deriv_weightedDeriv_eq
    {A B : ℝ → ℝ} {R : ℝ} {n : ℕ}
    (hA : ContDiff ℝ 2 A) (hB : Continuous B)
    (hweak : ∀ (phi : ℝ → ℝ), ContDiff ℝ ∞ phi →
      HasCompactSupport phi → tsupport phi ⊆ Ioo (0 : ℝ) R →
      ∫ r in Ioi (0 : ℝ), A r *
          deriv (fun s : ℝ => s ^ (n - 1) * deriv phi s) r =
        ∫ r in Ioi (0 : ℝ), B r * phi r) :
    ∀ r ∈ Ioo (0 : ℝ) R,
      deriv (fun s : ℝ => s ^ (n - 1) * deriv A s) r = B r := by
  let W : ℝ → ℝ := fun s => s ^ (n - 1) * deriv A s
  let F : ℝ → ℝ := fun s => deriv W s - B s
  have hA' : ContDiff ℝ 1 (deriv A) :=
    (contDiff_succ_iff_deriv.mp hA).2.2
  have hW : ContDiff ℝ 1 W := by
    exact (contDiff_id.pow (n - 1)).mul hA'
  have hW' : Continuous (deriv W) :=
    (contDiff_one_iff_deriv.mp hW).2
  have hF : Continuous F := hW'.sub hB
  have hFloc : LocallyIntegrableOn F (Ioo (0 : ℝ) R)
      (volume : Measure ℝ) :=
    hF.locallyIntegrable.locallyIntegrableOn _
  have hFae : ∀ᵐ s ∂(volume : Measure ℝ),
      s ∈ Ioo (0 : ℝ) R → F s = 0 := by
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      isOpen_Ioo hFloc
    intro phi hphi hphic hphiSupp
    let V : ℝ → ℝ := fun s => s ^ (n - 1) * deriv phi s
    have hphi' : ContDiff ℝ ∞ (deriv phi) :=
      (contDiff_infty_iff_deriv.mp hphi).2
    have hV : ContDiff ℝ ∞ V := by
      exact (contDiff_id.pow (n - 1)).mul hphi'
    have hV' : ContDiff ℝ ∞ (deriv V) :=
      (contDiff_infty_iff_deriv.mp hV).2
    have hVc : HasCompactSupport V := by
      change HasCompactSupport ((fun s : ℝ => s ^ (n - 1)) * deriv phi)
      exact hphic.deriv.mul_left
    have hVSupp : tsupport V ⊆ tsupport phi := by
      exact tsupport_mul_subset_right.trans tsupport_deriv_subset
    have hV'c : HasCompactSupport (deriv V) := hVc.deriv
    have hAderivV : Integrable (fun s => A s * deriv V s) :=
      (hA.continuous.mul hV'.continuous).integrable_of_hasCompactSupport
        hV'c.mul_left
    have hA'V : Integrable (fun s => deriv A s * V s) :=
      (hA'.continuous.mul hV.continuous).integrable_of_hasCompactSupport
        hVc.mul_left
    have hAV : Integrable (fun s => A s * V s) :=
      (hA.continuous.mul hV.continuous).integrable_of_hasCompactSupport
        hVc.mul_left
    have hibpA :
        ∫ s, A s * deriv V s = -∫ s, deriv A s * V s := by
      exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
        (fun s _ => (hA.differentiable (by simp) s).hasDerivAt)
        (fun s _ => (hV.differentiable (by simp) s).hasDerivAt)
        hAderivV hA'V hAV
    have hphiderivc : HasCompactSupport (deriv phi) := hphic.deriv
    have hWderivphi : Integrable (fun s => W s * deriv phi s) :=
      (hW.continuous.mul hphi'.continuous).integrable_of_hasCompactSupport
        hphiderivc.mul_left
    have hW'phi : Integrable (fun s => deriv W s * phi s) :=
      (hW'.mul hphi.continuous).integrable_of_hasCompactSupport
        hphic.mul_left
    have hWphi : Integrable (fun s => W s * phi s) :=
      (hW.continuous.mul hphi.continuous).integrable_of_hasCompactSupport
        hphic.mul_left
    have hibpW :
        ∫ s, W s * deriv phi s = -∫ s, deriv W s * phi s := by
      exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
        (fun s _ => (hW.differentiable (by simp) s).hasDerivAt)
        (fun s _ => (hphi.differentiable (by simp) s).hasDerivAt)
        hWderivphi hW'phi hWphi
    have hweakGlobal :
        ∫ s, A s * deriv V s = ∫ s, B s * phi s := by
      calc
        ∫ s, A s * deriv V s =
            ∫ s in Ioi (0 : ℝ), A s * deriv V s := by
          symm
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro s hs
          have hsV : s ∉ tsupport V := by
            intro hsV
            exact hs (hphiSupp (hVSupp hsV)).1
          rw [deriv_of_notMem_tsupport hsV, mul_zero]
        _ = ∫ s in Ioi (0 : ℝ), B s * phi s :=
          hweak phi hphi hphic hphiSupp
        _ = ∫ s, B s * phi s := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro s hs
          have hsphi : s ∉ tsupport phi := by
            intro hsphi
            exact hs (hphiSupp hsphi).1
          rw [image_eq_zero_of_notMem_tsupport hsphi, mul_zero]
    have hA'V_eq :
        ∫ s, deriv A s * V s = ∫ s, W s * deriv phi s := by
      apply integral_congr_ae
      filter_upwards [] with s
      simp only [V, W]
      ring
    have hbalance :
        ∫ s, deriv W s * phi s = ∫ s, B s * phi s := by
      calc
        ∫ s, deriv W s * phi s =
            -(∫ s, W s * deriv phi s) := by linarith [hibpW]
        _ = -(∫ s, deriv A s * V s) := by rw [hA'V_eq]
        _ = ∫ s, A s * deriv V s := hibpA.symm
        _ = ∫ s, B s * phi s := hweakGlobal
    have hBphi : Integrable (fun s => B s * phi s) :=
      (hB.mul hphi.continuous).integrable_of_hasCompactSupport
        hphic.mul_left
    calc
      ∫ s, phi s • F s =
          ∫ s, deriv W s * phi s - B s * phi s := by
        apply integral_congr_ae
        filter_upwards [] with s
        simp only [F, smul_eq_mul]
        ring
      _ = (∫ s, deriv W s * phi s) - ∫ s, B s * phi s := by
        rw [integral_sub hW'phi hBphi]
      _ = 0 := by rw [hbalance, sub_self]
  have hFae' : F =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) R)]
      (fun _ => 0) := by
    change ∀ᵐ s ∂(volume : Measure ℝ).restrict (Ioo (0 : ℝ) R), F s = 0
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hFae] with s hs
    intro hsI
    exact hs hsI
  have hFeq : Set.EqOn F (fun _ => 0) (Ioo (0 : ℝ) R) :=
    (volume : Measure ℝ).eqOn_Ioo_of_ae_eq hFae'
      hF.continuousOn continuousOn_const
  intro r hr
  have := hFeq hr
  simp only [F] at this
  linarith

end EvansLib
