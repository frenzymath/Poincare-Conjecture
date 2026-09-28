import EvansLib.Ch02.WaveCenterRadiusEPD
import EvansLib.Ch02.WaveSphericalMeans
import EvansLib.Ch02.LaplaceMeanValueTheorem
import EvansLib.Ch02.WaveMixedDerivatives

/-!
# Evans, Chapter 2: the odd-dimensional wave candidate

This file begins the data-to-solution direction of Evans's odd-dimensional
wave formula.  A normalized spherical data profile is passed through the
regular finite-sum radial extension.  Its derivative at the origin extracts
the data value with Evans's odd-product coefficient, which gives the initial
position of the candidate `γ⁻¹ (A_g' + A_h)`.
-/

open Filter MeasureTheory Metric Set
open scoped Real ContDiff Topology
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

/-! ## The first spherical moment -/

/-- Every continuous linear functional is harmonic. -/
theorem harmonicOnNhd_continuousLinearMap {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    HarmonicOnNhd (fun y => L y) univ := by
  intro y hy
  refine ⟨L.contDiff.contDiffAt, ?_⟩
  filter_upwards [] with z
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_two_apply]
  rw [show fderiv ℝ (fun v => L v) = fun _ => L by
    funext w
    exact L.hasFDerivAt.fderiv]
  simp

/-- The first moment of the unit-sphere measure vanishes.  This follows from
the spherical mean-value theorem applied to a linear harmonic function. -/
theorem integral_continuousLinearMap_toSphere_eq_zero
    {n : ℕ} [Nonempty (Fin n)]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        L (omega : EuclideanSpace ℝ (Fin n))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) = 0 := by
  have hmean := unitSphereRadialIntegralAt_eq_volume_mul_of_harmonicOnNhd
    (n := n) isOpen_univ (harmonicOnNhd_continuousLinearMap L)
    (x := (0 : EuclideanSpace ℝ (Fin n))) (R := 1) (r := 1)
    one_pos (by simp) (by simp)
  simpa [unitSphereRadialIntegralAt] using hmean

/-- The normalized spherical profile has zero radial derivative at its
center.  After differentiating under the compact sphere integral, this is the
vanishing first moment applied to the linear form `fderiv ℝ f x`. -/
theorem deriv_unitSphereRadialAverageAt_zero
    {n : ℕ} [Nonempty (Fin n)]
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin n)) :
    deriv (unitSphereRadialAverageAt f x) 0 = 0 := by
  let u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := fun p => f p.1
  have hu : ContDiff ℝ 1 u := hf.comp (by fun_prop)
  have hA : ContDiff ℝ 1 (waveSphericalAverage u x) :=
    waveSphericalAverage_contDiff_of_order hu x
  have hcurve : HasDerivAt (fun r : ℝ => (r, (0 : ℝ))) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
  have hcomp : HasDerivAt
      (fun r : ℝ => waveSphericalAverage u x (r, 0))
      (fderiv ℝ (waveSphericalAverage u x) (0, 0) (1, 0)) 0 :=
    (hA.differentiable (by norm_num) (0, 0)).hasFDerivAt.comp_hasDerivAt
      (f := fun r : ℝ => (r, (0 : ℝ))) 0 hcurve
  change deriv (fun r : ℝ => waveSphericalAverage u x (r, 0)) 0 = 0
  rw [hcomp.deriv]
  have hnorm := congrArg
    (fun T => T ![((1 : ℝ), (0 : ℝ))])
    (iteratedFDeriv_waveSphericalAverage_of_order hu x 1 le_rfl (0, 0))
  simp at hnorm
  rw [hnorm]
  have hmean := iteratedFDeriv_waveSphericalMean_apply_of_order
    hu x 1 le_rfl (0, 0) ![((1 : ℝ), (0 : ℝ))]
  simp at hmean
  rw [hmean]
  have hfiber : ∀ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      fderiv ℝ (waveSphereIntegrand u x
        (omega : EuclideanSpace ℝ (Fin n))) (0, 0) (1, 0) =
        fderiv ℝ f x (omega : EuclideanSpace ℝ (Fin n)) := by
    intro omega
    have hchain := iteratedFDeriv_waveSphereIntegrand_of_order hu x
      (omega : EuclideanSpace ℝ (Fin n)) 1 le_rfl (0, 0)
    have happ := congrArg
      (fun T => T ![((1 : ℝ), (0 : ℝ))]) hchain
    have hfst : HasFDerivAt
        (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.1)
        (ContinuousLinearMap.fst ℝ
          (EuclideanSpace ℝ (Fin n)) ℝ) (x, 0) :=
      hasFDerivAt_fst
    have hfu := ((hf.differentiable (by norm_num) x).hasFDerivAt.comp
      (x, (0 : ℝ)) hfst).fderiv
    have hfu_apply := congrArg
      (fun L : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] ℝ =>
        L ((omega : EuclideanSpace ℝ (Fin n)), 0)) hfu
    calc
      fderiv ℝ (waveSphereIntegrand u x
          (omega : EuclideanSpace ℝ (Fin n))) (0, 0) (1, 0) =
          fderiv ℝ u (x, 0) ((omega : EuclideanSpace ℝ (Fin n)), 0) := by
        simpa [iteratedFDeriv_one_apply, waveSphereParamLinear] using happ
      _ = fderiv ℝ f x (omega : EuclideanSpace ℝ (Fin n)) := by
        change fderiv ℝ (f ∘ fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.1)
            (x, 0) ((omega : EuclideanSpace ℝ (Fin n)), 0) = _
        exact hfu_apply
  simp_rw [hfiber]
  rw [integral_continuousLinearMap_toSphere_eq_zero (fderiv ℝ f x)]
  ring

/-- Evaluating an `m`-th derivative in the radius variable of a jointly
`C^(m+q)` function leaves a jointly `C^q` center-radius function. -/
private theorem contDiff_iteratedDeriv_centerRadius_of_order
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {m q : ℕ}
    (hf : ContDiff ℝ (m + q : ℕ) f) :
    ContDiff ℝ q (fun p : E × ℝ =>
      iteratedDeriv m (fun s => f (p.1, s)) p.2) := by
  let v : Fin m → E × ℝ := fun _ => (0, 1)
  have heq : (fun p : E × ℝ =>
      iteratedDeriv m (fun s => f (p.1, s)) p.2) =
      fun p => iteratedFDeriv ℝ m f p v := by
    funext p
    let a : E × ℝ := (p.1, 0)
    let L : ℝ →L[ℝ] E × ℝ := ContinuousLinearMap.inr ℝ E ℝ
    have hfun : (fun s => f (p.1, s)) =
        (fun z => f (a + z)) ∘ L := by
      funext s
      simp [a, L]
    have htrans : ContDiff ℝ (m + q : ℕ) (fun z => f (a + z)) :=
      hf.comp (contDiff_const.add contDiff_id)
    have hslice : iteratedFDeriv ℝ m (fun s => f (p.1, s)) p.2 =
        (iteratedFDeriv ℝ m f p).compContinuousLinearMap
          (fun _ => L) := by
      rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right L htrans p.2]
      · rw [iteratedFDeriv_comp_add_left]
        simp [a, L]
      · exact_mod_cast (show m ≤ m + q by omega)
    rw [iteratedDeriv_eq_iteratedFDeriv]
    have happ := congrArg (fun T => T (fun _ => (1 : ℝ))) hslice
    simpa [v, L] using happ
  rw [heq]
  have hf' : ContDiff ℝ (q + m : ℕ) f := by
    simpa [Nat.add_comm] using hf
  have hT : ContDiff ℝ q (iteratedFDeriv ℝ m f) :=
    hf'.iteratedFDeriv_right' (m := q)
  exact (ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin m => E × ℝ) F v).contDiff.comp hT

/-! ## The odd-dimensional candidate -/

/-- The regular odd-dimensional radial transform of the normalized spherical
average of spatial data around `x`. -/
def oddWaveDataTransform (k : ℕ)
    (f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) (r : ℝ) : ℝ :=
  waveRadialExtension k (unitSphereRadialAverageAt f x) r

/-- For smooth spatial data, the regular odd-wave transform is jointly
smooth in its center and radius variables. -/
theorem oddWaveDataTransform_joint_contDiff {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p :
      EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ =>
      oddWaveDataTransform k f p.1 p.2) := by
  let M : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ := fun p =>
    unitSphereRadialAverageAt f p.1 p.2
  have hM : ContDiff ℝ ∞ M := by
    rw [contDiff_infty]
    intro q
    exact unitSphereRadialAverageAt_joint_contDiff_of_order
      (hf.of_le (WithTop.coe_le_coe.mpr
        (show (q : ℕ∞) ≤ ⊤ from le_top)))
  unfold oddWaveDataTransform waveRadialExtension
  apply ContDiff.sum
  intro j hj
  have hiter : ContDiff ℝ ∞ (fun p :
      EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ =>
      iteratedDeriv j (unitSphereRadialAverageAt f p.1) p.2) := by
    simpa [M] using contDiff_iteratedDeriv_centerRadius hM j
  exact (contDiff_const.mul (contDiff_snd.pow (j + 1))).mul hiter

/-- The joint center-radius data transform retains every finite order `q`
available after its highest radial derivative. -/
theorem oddWaveDataTransform_joint_contDiff_of_order {k q : ℕ}
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ (k + q - 1 : ℕ) f) :
    ContDiff ℝ q (fun p :
      EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ =>
      oddWaveDataTransform k f p.1 p.2) := by
  let M : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ := fun p =>
    unitSphereRadialAverageAt f p.1 p.2
  have hM : ContDiff ℝ (k + q - 1 : ℕ) M :=
    unitSphereRadialAverageAt_joint_contDiff_of_order hf
  unfold oddWaveDataTransform waveRadialExtension
  apply ContDiff.sum
  intro j hj
  have hjlt : j < k := Finset.mem_range.mp hj
  have hiter : ContDiff ℝ q (fun p :
      EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ =>
      iteratedDeriv j (unitSphereRadialAverageAt f p.1) p.2) := by
    change ContDiff ℝ q (fun p :
      EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ =>
      iteratedDeriv j (fun s => M (p.1, s)) p.2)
    apply contDiff_iteratedDeriv_centerRadius_of_order
    simpa [M] using hM.of_le (by
      exact_mod_cast (show j + q ≤ k + q - 1 by omega))
  exact (contDiff_const.mul (contDiff_snd.pow (j + 1))).mul hiter

/-- Every odd-wave data transform vanishes at the origin. -/
@[simp] theorem oddWaveDataTransform_zero (k : ℕ)
    (f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    oddWaveDataTransform k f x 0 = 0 := by
  simp [oddWaveDataTransform]

/-- At positive radii, the regular data transform is Evans's iterated radial
operator applied to the normalized spherical average. -/
theorem oddWaveDataTransform_eq_radialIter {k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ k f)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) {r : ℝ} (hr : 0 < r) :
    oddWaveDataTransform k f x r =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        unitSphereRadialAverageAt f x s) r :=
  waveRadialExtension_eq_radialIter hk
    (unitSphereRadialAverageAt_contDiff_of_order hf x) hr

/-- The derivative of the regular data transform at the origin extracts the
center value with Evans's odd-product coefficient. -/
theorem deriv_oddWaveDataTransform_zero {k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ k f)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    deriv (oddWaveDataTransform k f x) 0 = evansOddProduct k * f x := by
  change deriv (waveRadialExtension k (unitSphereRadialAverageAt f x)) 0 =
    evansOddProduct k * f x
  rw [deriv_waveRadialExtension_zero hk
      (unitSphereRadialAverageAt_contDiff_of_order hf x),
    unitSphereRadialAverageAt_zero]

/-- The regular data transform has precisely the finite differentiability
remaining after its highest profile derivative. -/
theorem oddWaveDataTransform_contDiff_of_order {k q : ℕ}
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ (k + q - 1 : ℕ) f)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    ContDiff ℝ q (oddWaveDataTransform k f x) := by
  exact waveRadialExtension_contDiff_of_order
    (unitSphereRadialAverageAt_contDiff_of_order hf x)

/-- The second derivative of the position-data transform vanishes at the
origin.  The radial profile's first derivative vanishes by sphere symmetry. -/
theorem deriv_deriv_oddWaveDataTransform_zero {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ (k + 1 : ℕ) f)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    deriv (deriv (oddWaveDataTransform k f x)) 0 = 0 := by
  have hprofile : ContDiff ℝ (k + 1 : ℕ)
      (unitSphereRadialAverageAt f x) :=
    unitSphereRadialAverageAt_contDiff_of_order hf x
  have hprofile_zero :
      deriv (unitSphereRadialAverageAt f x) 0 = 0 :=
    deriv_unitSphereRadialAverageAt_zero (hf.of_le (by
      exact_mod_cast (show 1 ≤ k + 1 by omega))) x
  have hsecond := iteratedDeriv_two_waveRadialExtension_zero
    hprofile hprofile_zero
  change deriv (deriv
    (waveRadialExtension k (unitSphereRadialAverageAt f x))) 0 = 0
  simpa [iteratedDeriv_succ, iteratedDeriv_one] using hsecond

/-- At positive time, two time derivatives of the regular data transform are
the odd radial transform of the center Laplacian of the spherical profile. -/
theorem deriv_deriv_oddWaveDataTransform_eq_radialIter_laplacian
    {k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ (k + 1 : ℕ) f)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1)))
    (t : ℝ) (ht : 0 < t) :
    deriv (deriv (oddWaveDataTransform k f x)) t =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        Δ (fun y => unitSphereRadialAverageAt f y s) x) t := by
  let phi : ℝ → ℝ := unitSphereRadialAverageAt f x
  let psi : ℝ → ℝ := fun s =>
    Δ (fun y => unitSphereRadialAverageAt f y s) x
  let R : ℝ → ℝ := radialIter (k - 1)
    (fun s => s ^ (2 * k - 1) * phi s)
  have hfk : ContDiff ℝ k f :=
    hf.of_le (by exact_mod_cast Nat.le_succ k)
  have hphi : ContDiff ℝ (k + 1 : ℕ) phi :=
    unitSphereRadialAverageAt_contDiff_of_order hf x
  have heq : oddWaveDataTransform k f x =ᶠ[𝓝 t] R := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact oddWaveDataTransform_eq_radialIter hk hfk x hs
  have hsecondEq :
      deriv (deriv (oddWaveDataTransform k f x)) t =
        deriv (deriv R) t :=
    (heq.deriv).deriv_eq
  have hf2 : ContDiff ℝ 2 f :=
    hf.of_le (by exact_mod_cast (show 2 ≤ k + 1 by omega))
  have hEPD : ∀ s, 0 < s →
      radialOp (fun z => z ^ (2 * k) * deriv phi z) s =
        s ^ (2 * k - 1) * psi s := by
    intro s hs
    have hweighted :=
      deriv_weightedDeriv_unitSphereRadialAverageAt_eq_laplacian
        (n := 2 * k + 1) (by omega) hf2 x s hs
    have hweighted' :
        deriv (fun z : ℝ => z ^ (2 * k) * deriv phi z) s =
          s ^ (2 * k) * psi s := by
      simpa [phi, psi, show 2 * k + 1 - 1 = 2 * k by omega]
        using hweighted
    rw [radialOp, hweighted']
    change s ^ (2 * k) * psi s / s = s ^ (2 * k - 1) * psi s
    rw [show 2 * k = (2 * k - 1) + 1 by omega, pow_succ]
    field_simp
    rw [show 2 * k - 1 + 1 - 1 = 2 * k - 1 by omega]
    ring
  have hradial := waveRadial_transform_of_epd hk hphi hEPD ht
  calc
    deriv (deriv (oddWaveDataTransform k f x)) t =
        deriv (deriv R) t := hsecondEq
    _ = radialIter (k - 1) (fun s => s ^ (2 * k - 1) * psi s) t := by
      simpa [R] using hradial
    _ = _ := rfl

private theorem contDiff_laplacian_infty
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Δ f) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply ContDiff.sum
  intro i hi
  have heq : (fun x => iteratedFDeriv ℝ 2 f x
      ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]) =
      fun x => fderiv ℝ (fderiv ℝ f) x
        ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i) := by
    funext x
    simp [iteratedFDeriv_two_apply]
  rw [heq]
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) :=
    hf.fderiv_right (m := ∞) (by simp)
  have hfdd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    hfd.fderiv_right (m := ∞) (by simp)
  exact (hfdd.clm_apply contDiff_const).clm_apply contDiff_const

/-- Taking the Euclidean Laplacian consumes exactly two finite derivatives. -/
private theorem contDiff_laplacian_of_order
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f : E → ℝ} {q : ℕ} (hf : ContDiff ℝ (q + 2 : ℕ) f) :
    ContDiff ℝ q (Δ f) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply ContDiff.sum
  intro i hi
  have heq : (fun x => iteratedFDeriv ℝ 2 f x
      ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]) =
      fun x => fderiv ℝ (fderiv ℝ f) x
        ((stdOrthonormalBasis ℝ E) i) ((stdOrthonormalBasis ℝ E) i) := by
    funext x
    simp [iteratedFDeriv_two_apply]
  rw [heq]
  have hfd : ContDiff ℝ ((q : ℕ∞ω) + 1) (fderiv ℝ f) :=
    hf.fderiv_right (m := (q : ℕ∞ω) + 1) (by
      exact_mod_cast (show q + 1 + 1 ≤ q + 2 by omega))
  have hfdd : ContDiff ℝ q (fderiv ℝ (fderiv ℝ f)) :=
    hfd.fderiv_right (m := q) (by norm_num)
  exact (hfdd.clm_apply contDiff_const).clm_apply contDiff_const

/-- The center Laplacian of a smooth data transform is the radial transform
of the center Laplacian of the underlying spherical profile. -/
theorem laplacian_oddWaveDataTransform_eq_radialIter_laplacian_of_order
    {k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ (k + 1 : ℕ) f)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1)))
    (t : ℝ) (ht : 0 < t) :
    Δ (fun y => oddWaveDataTransform k f y t) x =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        Δ (fun y => unitSphereRadialAverageAt f y s) x) t := by
  let M : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ := fun p =>
    unitSphereRadialAverageAt f p.1 p.2
  let psi : ℝ → ℝ := fun s => Δ (fun y => M (y, s)) x
  let C : ℕ → ℝ := fun j => evansRadialCoeff k j * t ^ (j + 1)
  let H : ℕ → EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ := fun j y =>
    iteratedDeriv j (fun s => M (y, s)) t
  have hM : ContDiff ℝ (k + 1 : ℕ) M := by
    exact unitSphereRadialAverageAt_joint_contDiff_of_order hf
  have hH : ∀ j, j < k → ContDiff ℝ 2 (H j) := by
    intro j hj
    have hjq : j + 2 ≤ k + 1 := by omega
    have hMj : ContDiff ℝ (j + 2 : ℕ) M :=
      hM.of_le (by exact_mod_cast hjq)
    have hjoint := contDiff_iteratedDeriv_centerRadius_of_order
      (m := j) (q := 2) hMj
    change ContDiff ℝ 2 (fun y =>
      iteratedDeriv j (fun s => M (y, s)) t)
    convert hjoint.comp
      (contDiff_id.prodMk (contDiff_const :
        ContDiff ℝ 2 (fun _ : EuclideanSpace ℝ (Fin (2 * k + 1)) => t))) using 1 <;> rfl
  have hDf : ContDiff ℝ (k - 1 : ℕ) (Δ f) := by
    apply contDiff_laplacian_of_order
    simpa [show k - 1 + 2 = k + 1 by omega] using hf
  have hpsiEq : psi = unitSphereRadialAverageAt (Δ f) x := by
    funext s
    exact laplacian_unitSphereRadialAverageAt
      (hf.of_le (by exact_mod_cast (show 2 ≤ k + 1 by omega))) x s
  have hpsi : ContDiff ℝ (k - 1 : ℕ) psi := by
    rw [hpsiEq]
    exact unitSphereRadialAverageAt_contDiff_of_order hDf x
  have hfun : (fun y => oddWaveDataTransform k f y t) =
      fun y => ∑ j ∈ Finset.range k, C j • H j y := by
    funext y
    simp [oddWaveDataTransform, waveRadialExtension, C, H, M,
      smul_eq_mul, mul_assoc]
  rw [hfun]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  change (∑ i,
    (iteratedFDeriv ℝ 2
      (fun y => ∑ j ∈ Finset.range k, C j • H j y) x)
        ![(stdOrthonormalBasis ℝ
            (EuclideanSpace ℝ (Fin (2 * k + 1)))) i,
          (stdOrthonormalBasis ℝ
            (EuclideanSpace ℝ (Fin (2 * k + 1)))) i]) = _
  have hsum : iteratedFDeriv ℝ 2
      (fun y => ∑ j ∈ Finset.range k, C j • H j y) x =
      ∑ j ∈ Finset.range k,
        iteratedFDeriv ℝ 2 (fun y => C j • H j y) x := by
    exact iteratedFDeriv_fun_sum_apply fun j hj =>
      ((hH j (Finset.mem_range.mp hj)).const_smul (C j)).contDiffAt
  rw [hsum]
  simp_rw [ContinuousMultilinearMap.sum_apply]
  rw [Finset.sum_comm]
  change _ = radialIter (k - 1)
    (fun s => s ^ (2 * k - 1) * psi s) t
  rw [EvansLib.waveRadial_expansion_of_order hk hpsi ht]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < k := Finset.mem_range.mp hj
  rw [iteratedFDeriv_const_smul_apply'
    ((hH j (Finset.mem_range.mp hj)).contDiffAt)]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  have hlapH := congrFun
    (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (H j)) x
  rw [← hlapH]
  change C j * Δ (fun y =>
    iteratedDeriv j (fun s => M (y, s)) t) x = _
  rw [← iteratedDeriv_laplacian_center_slice_comm_of_order
    (m := j) (hM.of_le (by exact_mod_cast
      (show j + 2 ≤ k + 1 by omega))) x t]

theorem laplacian_oddWaveDataTransform_eq_radialIter_laplacian
    {k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1)))
    (t : ℝ) (ht : 0 < t) :
    Δ (fun y => oddWaveDataTransform k f y t) x =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        Δ (fun y => unitSphereRadialAverageAt f y s) x) t := by
  let M : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ := fun p =>
    unitSphereRadialAverageAt f p.1 p.2
  let psi : ℝ → ℝ := fun s => Δ (fun y => M (y, s)) x
  let C : ℕ → ℝ := fun j => evansRadialCoeff k j * t ^ (j + 1)
  let H : ℕ → EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ := fun j y =>
    iteratedDeriv j (fun s => M (y, s)) t
  have hM : ContDiff ℝ ∞ M := by
    rw [contDiff_infty]
    intro q
    exact unitSphereRadialAverageAt_joint_contDiff_of_order
      (hf.of_le (WithTop.coe_le_coe.mpr
        (show (q : ℕ∞) ≤ ⊤ from le_top)))
  have hH : ∀ j, ContDiff ℝ ∞ (H j) := fun j => by
    exact contDiff_iteratedDeriv_center_slice hM j t
  have hDf : ContDiff ℝ ∞ (Δ f) := contDiff_laplacian_infty hf
  have hpsiEq : psi = unitSphereRadialAverageAt (Δ f) x := by
    funext s
    exact laplacian_unitSphereRadialAverageAt
      (hf.of_le (WithTop.coe_le_coe.mpr
        (show (2 : ℕ∞) ≤ ⊤ from le_top))) x s
  have hpsi : ContDiff ℝ k psi := by
    rw [hpsiEq]
    exact unitSphereRadialAverageAt_contDiff_of_order
      (hDf.of_le (WithTop.coe_le_coe.mpr
        (show (k : ℕ∞) ≤ ⊤ from le_top))) x
  have hfun : (fun y => oddWaveDataTransform k f y t) =
      fun y => ∑ j ∈ Finset.range k, C j • H j y := by
    funext y
    simp [oddWaveDataTransform, waveRadialExtension, C, H, M,
      smul_eq_mul, mul_assoc]
  rw [hfun]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  change (∑ i,
    (iteratedFDeriv ℝ 2
      (fun y => ∑ j ∈ Finset.range k, C j • H j y) x)
        ![(stdOrthonormalBasis ℝ
            (EuclideanSpace ℝ (Fin (2 * k + 1)))) i,
          (stdOrthonormalBasis ℝ
            (EuclideanSpace ℝ (Fin (2 * k + 1)))) i]) = _
  have hsum : iteratedFDeriv ℝ 2
      (fun y => ∑ j ∈ Finset.range k, C j • H j y) x =
      ∑ j ∈ Finset.range k,
        iteratedFDeriv ℝ 2 (fun y => C j • H j y) x := by
    exact iteratedFDeriv_fun_sum_apply fun j hj =>
      ((hH j).const_smul (C j)).contDiffAt.of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [hsum]
  simp_rw [ContinuousMultilinearMap.sum_apply]
  rw [Finset.sum_comm]
  change _ = radialIter (k - 1)
    (fun s => s ^ (2 * k - 1) * psi s) t
  rw [waveRadial_expansion hk hpsi ht]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedFDeriv_const_smul_apply'
    ((hH j).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  have hlapH := congrFun
    (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (H j)) x
  rw [← hlapH]
  change C j * Δ (fun y =>
    iteratedDeriv j (fun s => M (y, s)) t) x = _
  rw [← iteratedDeriv_laplacian_center_slice_comm hM x t]

/-- Each smooth odd-wave data transform solves the wave equation at positive
time. -/
theorem oddWaveDataTransform_wave_equation_of_order
    {k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ (k + 1 : ℕ) f)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1)))
    (t : ℝ) (ht : 0 < t) :
    deriv (deriv (oddWaveDataTransform k f x)) t =
      Δ (fun y => oddWaveDataTransform k f y t) x := by
  have htime := deriv_deriv_oddWaveDataTransform_eq_radialIter_laplacian
    hk hf x t ht
  have hspace := laplacian_oddWaveDataTransform_eq_radialIter_laplacian_of_order
    hk hf x t ht
  exact htime.trans hspace.symm

theorem oddWaveDataTransform_wave_equation
    {k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1)))
    (t : ℝ) (ht : 0 < t) :
    deriv (deriv (oddWaveDataTransform k f x)) t =
      Δ (fun y => oddWaveDataTransform k f y t) x :=
  oddWaveDataTransform_wave_equation_of_order hk
    (hf.of_le (WithTop.coe_le_coe.mpr
      (show (k + 1 : ℕ∞) ≤ ⊤ from le_top))) x t ht

/-- Under finite regularity, the time derivative of the odd-wave transform
also solves the wave equation at positive time. -/
theorem deriv_oddWaveDataTransform_wave_equation_of_order
    {k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ (k + 2 : ℕ) f)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1)))
    (t : ℝ) (ht : 0 < t) :
    deriv (deriv (fun s => deriv (oddWaveDataTransform k f x) s)) t =
      Δ (fun y => deriv (oddWaveDataTransform k f y) t) x := by
  let A : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ := fun p =>
    oddWaveDataTransform k f p.1 p.2
  have hA : ContDiff ℝ 3 A := by
    simpa [A] using
      (oddWaveDataTransform_joint_contDiff_of_order (k := k) (q := 3) hf)
  have hlocal :
      (fun s => deriv (deriv (oddWaveDataTransform k f x)) s) =ᶠ[𝓝 t]
        fun s => Δ (fun y => oddWaveDataTransform k f y s) x := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact oddWaveDataTransform_wave_equation_of_order hk
      (hf.of_le (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))) x s hs
  have hderiv := hlocal.deriv_eq
  have hcomm := iteratedDeriv_laplacian_center_slice_comm_of_order
    (m := 1) hA x t
  rw [iteratedDeriv_one] at hcomm
  simpa [A] using hderiv.trans hcomm

/-- The smooth specialization of the finite time-derivative wave equation. -/
theorem deriv_oddWaveDataTransform_wave_equation
    {k : ℕ} (hk : 1 ≤ k)
    {f : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1)))
    (t : ℝ) (ht : 0 < t) :
    deriv (deriv (fun s => deriv (oddWaveDataTransform k f x) s)) t =
      Δ (fun y => deriv (oddWaveDataTransform k f y) t) x :=
  deriv_oddWaveDataTransform_wave_equation_of_order hk
    (hf.of_le (WithTop.coe_le_coe.mpr
      (show (k + 2 : ℕ∞) ≤ ⊤ from le_top))) x t ht

/-- Evans's odd-product normalization is positive in every odd dimension at
least three. -/
theorem evansOddProduct_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < evansOddProduct k := by
  have hidx : k - 1 + 1 = k := by omega
  rw [← hidx, evansOddProduct_eq_doubleFactorial]
  positivity

theorem evansOddProduct_ne_zero {k : ℕ} (hk : 1 ≤ k) :
    evansOddProduct k ≠ 0 :=
  (evansOddProduct_pos hk).ne'

/-- Evans's candidate solution in dimension `2k+1`, written using normalized
spherical averages:
`u(x,t) = γ⁻¹ (A_g'(x,t) + A_h(x,t))`. -/
def oddWaveSolution (k : ℕ)
    (g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ)
    (p : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ) : ℝ :=
  (evansOddProduct k)⁻¹ *
    (deriv (oddWaveDataTransform k g p.1) p.2 +
      oddWaveDataTransform k h p.1 p.2)

/-- The first time derivative of the odd-dimensional candidate, packaged as
a joint center-time field. -/
def oddWaveSolutionTimeDeriv (k : ℕ)
    (g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ)
    (p : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ) : ℝ :=
  deriv (fun t => oddWaveSolution k g h (p.1, t)) p.2

/-- Under Evans's finite data hypotheses, the odd-dimensional candidate is
globally `C²` in center and time.  Restricting this result to nonnegative time
gives the regularity assertion on the closed half-space. -/
theorem oddWaveSolution_contDiff_two {k : ℕ}
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hg : ContDiff ℝ (k + 2 : ℕ) g)
    (hh : ContDiff ℝ (k + 1 : ℕ) h) :
    ContDiff ℝ 2 (oddWaveSolution k g h) := by
  let Ag : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ := fun p =>
    oddWaveDataTransform k g p.1 p.2
  have hAg : ContDiff ℝ 3 Ag := by
    simpa [Ag] using
      (oddWaveDataTransform_joint_contDiff_of_order (k := k) (q := 3) hg)
  have hdAg : ContDiff ℝ 2 (fun p :
      EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ =>
      deriv (oddWaveDataTransform k g p.1) p.2) := by
    simpa [Ag, iteratedDeriv_one] using
      (contDiff_iteratedDeriv_centerRadius_of_order
        (m := 1) (q := 2) hAg)
  have hAh : ContDiff ℝ 2 (fun p :
      EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ =>
      oddWaveDataTransform k h p.1 p.2) := by
    simpa using
      (oddWaveDataTransform_joint_contDiff_of_order (k := k) (q := 2) hh)
  exact contDiff_const.mul (hdAg.add hAh)

/-- The finite-regularity candidate is `C²` on Evans's closed nonnegative-time
half-space. -/
theorem oddWaveSolution_contDiffOn_halfSpace {k : ℕ}
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hg : ContDiff ℝ (k + 2 : ℕ) g)
    (hh : ContDiff ℝ (k + 1 : ℕ) h) :
    ContDiffOn ℝ 2 (oddWaveSolution k g h)
      (waveSpaceTimeHalfSpace (2 * k + 1)) :=
  (oddWaveSolution_contDiff_two hg hh).contDiffOn

/-- Under Evans's sharp finite data hypotheses, the odd-dimensional candidate
solves the wave equation at every positive time. -/
theorem oddWaveSolution_wave_equation_of_order
    {k : ℕ} (hk : 1 ≤ k)
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hg : ContDiff ℝ (k + 2 : ℕ) g)
    (hh : ContDiff ℝ (k + 1 : ℕ) h)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1)))
    (t : ℝ) (ht : 0 < t) :
    deriv (deriv (fun s => oddWaveSolution k g h (x, s))) t =
      Δ (fun y => oddWaveSolution k g h (y, t)) x := by
  let c : ℝ := (evansOddProduct k)⁻¹
  let Bg : ℝ → ℝ := fun s => deriv (oddWaveDataTransform k g x) s
  let Bh : ℝ → ℝ := oddWaveDataTransform k h x
  have hAgJoint : ContDiff ℝ 3 (fun p :
      EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ =>
      oddWaveDataTransform k g p.1 p.2) := by
    exact oddWaveDataTransform_joint_contDiff_of_order (k := k) (q := 3) hg
  have hAhJoint : ContDiff ℝ 2 (fun p :
      EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ =>
      oddWaveDataTransform k h p.1 p.2) := by
    exact oddWaveDataTransform_joint_contDiff_of_order (k := k) (q := 2) hh
  have hAgTime : ContDiff ℝ 3 (oddWaveDataTransform k g x) :=
    hAgJoint.comp (contDiff_const.prodMk contDiff_id)
  have hAhTime : ContDiff ℝ 2 Bh := by
    change ContDiff ℝ 2 (fun s => oddWaveDataTransform k h x s)
    convert hAhJoint.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
  have hBgTime : ContDiff ℝ 2 Bg := by
    simpa [Bg] using (contDiff_succ_iff_deriv.mp hAgTime).2.2
  have hdBgTime : ContDiff ℝ 1 (deriv Bg) :=
    (contDiff_succ_iff_deriv.mp hBgTime).2.2
  have hdBhTime : ContDiff ℝ 1 (deriv Bh) :=
    (contDiff_succ_iff_deriv.mp hAhTime).2.2
  have hfirst : deriv (fun s => c * (Bg s + Bh s)) =
      fun s => c * (deriv Bg s + deriv Bh s) := by
    funext s
    rw [deriv_const_mul c ((hBgTime.add hAhTime).differentiable (by simp) s)]
    exact congrArg (fun z : ℝ => c * z) (by
      change deriv (Bg + Bh) s = deriv Bg s + deriv Bh s
      exact deriv_add (hBgTime.differentiable (by simp) s)
        (hAhTime.differentiable (by simp) s))
  have htime :
      deriv (deriv (fun s => c * (Bg s + Bh s))) t =
        c * (deriv (deriv Bg) t + deriv (deriv Bh) t) := by
    rw [hfirst]
    rw [deriv_const_mul c
      ((hdBgTime.add hdBhTime).differentiable (by simp) t)]
    exact congrArg (fun z : ℝ => c * z) (by
      change deriv (deriv Bg + deriv Bh) t =
        deriv (deriv Bg) t + deriv (deriv Bh) t
      exact deriv_add (hdBgTime.differentiable (by simp) t)
        (hdBhTime.differentiable (by simp) t))
  have hBgSpace : ContDiff ℝ 2 (fun y =>
      deriv (oddWaveDataTransform k g y) t) := by
    convert (contDiff_iteratedDeriv_centerRadius_of_order
      (m := 1) (q := 2) hAgJoint).comp
        (contDiff_id.prodMk (contDiff_const : ContDiff ℝ 2
          (fun _ : EuclideanSpace ℝ (Fin (2 * k + 1)) => t))) using 1
    · norm_num
    · funext y
      simp only [Function.comp_apply, iteratedDeriv_one]
      apply congrArg (fun F : ℝ → ℝ => deriv F t)
      funext s
      rfl
  have hBhSpace : ContDiff ℝ 2 (fun y =>
      oddWaveDataTransform k h y t) :=
    hAhJoint.comp (contDiff_id.prodMk contDiff_const)
  have hspace :
      Δ (fun y => c * (deriv (oddWaveDataTransform k g y) t +
        oddWaveDataTransform k h y t)) x =
      c * (Δ (fun y => deriv (oddWaveDataTransform k g y) t) x +
        Δ (fun y => oddWaveDataTransform k h y t) x) := by
    change Δ (c • (fun y => deriv (oddWaveDataTransform k g y) t +
      oddWaveDataTransform k h y t)) x = _
    rw [laplacian_smul c ((hBgSpace.add hBhSpace).contDiffAt)]
    change c * Δ (fun y => deriv (oddWaveDataTransform k g y) t +
      oddWaveDataTransform k h y t) x = _
    rw [show (fun y => deriv (oddWaveDataTransform k g y) t +
        oddWaveDataTransform k h y t) =
        (fun y => deriv (oddWaveDataTransform k g y) t) +
          fun y => oddWaveDataTransform k h y t by rfl]
    rw [hBgSpace.contDiffAt.laplacian_add hBhSpace.contDiffAt]
  have hgPDE := deriv_oddWaveDataTransform_wave_equation_of_order hk hg x t ht
  have hhPDE := oddWaveDataTransform_wave_equation_of_order hk hh x t ht
  change deriv (deriv (fun s => c * (Bg s + Bh s))) t =
    Δ (fun y => c * (deriv (oddWaveDataTransform k g y) t +
      oddWaveDataTransform k h y t)) x
  calc
    deriv (deriv (fun s => c * (Bg s + Bh s))) t =
        c * (deriv (deriv Bg) t + deriv (deriv Bh) t) := htime
    _ = c * (Δ (fun y => deriv (oddWaveDataTransform k g y) t) x +
        Δ (fun y => oddWaveDataTransform k h y t) x) := by
      rw [show deriv (deriv Bg) t =
          Δ (fun y => deriv (oddWaveDataTransform k g y) t) x by
        simpa [Bg] using hgPDE]
      rw [show deriv (deriv Bh) t =
          Δ (fun y => oddWaveDataTransform k h y t) x by
        simpa [Bh] using hhPDE]
    _ = Δ (fun y => c * (deriv (oddWaveDataTransform k g y) t +
        oddWaveDataTransform k h y t)) x := hspace.symm

/-- Smooth specialization of the finite odd-dimensional wave equation. -/
theorem oddWaveSolution_wave_equation
    {k : ℕ} (hk : 1 ≤ k)
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1)))
    (t : ℝ) (ht : 0 < t) :
    deriv (deriv (fun s => oddWaveSolution k g h (x, s))) t =
      Δ (fun y => oddWaveSolution k g h (y, t)) x :=
  oddWaveSolution_wave_equation_of_order hk
    (hg.of_le (WithTop.coe_le_coe.mpr
      (show (k + 2 : ℕ∞) ≤ ⊤ from le_top)))
    (hh.of_le (WithTop.coe_le_coe.mpr
      (show (k + 1 : ℕ∞) ≤ ⊤ from le_top))) x t ht

/-- The odd-dimensional candidate has the prescribed initial position. -/
theorem oddWaveSolution_initial_position {k : ℕ} (hk : 1 ≤ k)
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hg : ContDiff ℝ k g)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    oddWaveSolution k g h (x, 0) = g x := by
  rw [oddWaveSolution, deriv_oddWaveDataTransform_zero hk hg,
    oddWaveDataTransform_zero]
  field_simp [evansOddProduct_ne_zero hk]
  ring

/-- The odd-dimensional candidate has the prescribed initial velocity. -/
theorem oddWaveSolution_initial_velocity {k : ℕ} (hk : 1 ≤ k)
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hg : ContDiff ℝ (k + 1 : ℕ) g)
    (hh : ContDiff ℝ k h)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    deriv (fun t => oddWaveSolution k g h (x, t)) 0 = h x := by
  have hAg : ContDiff ℝ 2 (oddWaveDataTransform k g x) := by
    apply oddWaveDataTransform_contDiff_of_order
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hg
  have hAh : ContDiff ℝ 1 (oddWaveDataTransform k h x) := by
    apply oddWaveDataTransform_contDiff_of_order
    simpa using hh
  have hsum : HasDerivAt
      (fun t => deriv (oddWaveDataTransform k g x) t +
        oddWaveDataTransform k h x t)
      (deriv (deriv (oddWaveDataTransform k g x)) 0 +
        deriv (oddWaveDataTransform k h x) 0) 0 :=
    (hAg.differentiable_deriv_two 0).hasDerivAt.add
      (hAh.differentiable (by norm_num) 0).hasDerivAt
  change deriv (fun t => (evansOddProduct k)⁻¹ *
      (deriv (oddWaveDataTransform k g x) t +
        oddWaveDataTransform k h x t)) 0 = h x
  rw [(hsum.const_mul (evansOddProduct k)⁻¹).deriv,
    deriv_deriv_oddWaveDataTransform_zero hg x,
    deriv_oddWaveDataTransform_zero hk hh]
  field_simp [evansOddProduct_ne_zero hk]
  ring

/-- Under Evans's finite data hypotheses, the first time derivative of the
odd-dimensional candidate is jointly `C¹` in center and time. -/
theorem oddWaveSolution_timeDeriv_contDiff_one {k : ℕ}
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hg : ContDiff ℝ (k + 2 : ℕ) g)
    (hh : ContDiff ℝ (k + 1 : ℕ) h) :
    ContDiff ℝ 1 (oddWaveSolutionTimeDeriv k g h) := by
  have hu : ContDiff ℝ 2 (oddWaveSolution k g h) :=
    oddWaveSolution_contDiff_two hg hh
  unfold oddWaveSolutionTimeDeriv
  convert (contDiff_iteratedDeriv_centerRadius_of_order
    (m := 1) (q := 1) hu) using 1 <;> norm_num

/-- The finite-regularity candidate converges jointly to its prescribed
initial position as the center and positive time approach `(x, 0)`. -/
theorem oddWaveSolution_tendsto_initial_position {k : ℕ} (hk : 1 ≤ k)
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hg : ContDiff ℝ (k + 2 : ℕ) g)
    (hh : ContDiff ℝ (k + 1 : ℕ) h)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    Tendsto (oddWaveSolution k g h)
      (nhdsWithin (x, 0) (univ ×ˢ Ioi (0 : ℝ))) (nhds (g x)) := by
  have ht : Tendsto (oddWaveSolution k g h)
      (nhdsWithin (x, 0) (univ ×ˢ Ioi (0 : ℝ)))
      (nhds (oddWaveSolution k g h (x, 0))) :=
    (oddWaveSolution_contDiff_two hg hh).continuous.continuousAt.tendsto.mono_left
      inf_le_left
  have hinit : oddWaveSolution k g h (x, 0) = g x :=
    oddWaveSolution_initial_position (h := h) hk
      (hg.of_le (by exact_mod_cast (show k ≤ k + 2 by omega))) x
  rw [hinit] at ht
  exact ht

/-- The first time derivative converges jointly to the prescribed initial
velocity as the center and positive time approach `(x, 0)`. -/
theorem oddWaveSolution_tendsto_initial_velocity {k : ℕ} (hk : 1 ≤ k)
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hg : ContDiff ℝ (k + 2 : ℕ) g)
    (hh : ContDiff ℝ (k + 1 : ℕ) h)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    Tendsto (oddWaveSolutionTimeDeriv k g h)
      (nhdsWithin (x, 0) (univ ×ˢ Ioi (0 : ℝ))) (nhds (h x)) := by
  have ht : Tendsto (oddWaveSolutionTimeDeriv k g h)
      (nhdsWithin (x, 0) (univ ×ˢ Ioi (0 : ℝ)))
      (nhds (oddWaveSolutionTimeDeriv k g h (x, 0))) :=
    (oddWaveSolution_timeDeriv_contDiff_one hg hh).continuous.continuousAt.tendsto.mono_left
      inf_le_left
  have hinit : oddWaveSolutionTimeDeriv k g h (x, 0) = h x := by
    simpa [oddWaveSolutionTimeDeriv] using
      oddWaveSolution_initial_velocity (h := h) hk
        (hg.of_le (by exact_mod_cast (show k + 1 ≤ k + 2 by omega)))
        (hh.of_le (by exact_mod_cast (show k ≤ k + 1 by omega))) x
  rw [hinit] at ht
  exact ht

/-! The displayed spherical integrals in Evans's formula (31) are understood
as averages over the sphere (the surface measure divided by its total mass).
The definition `oddWaveSolution` uses exactly this normalized convention. -/

/-- **Evans's odd-dimensional wave Cauchy package.**  In dimension
`2 * k + 1`, the normalized spherical formula gives a `C²` solution on the
closed nonnegative-time half-space, satisfies the wave equation at positive
times, and has the prescribed position and velocity traces. -/
theorem oddWaveSolution_isSolutionOfIVP_of_order {k : ℕ} (hk : 1 ≤ k)
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hg : ContDiff ℝ (k + 2 : ℕ) g)
    (hh : ContDiff ℝ (k + 1 : ℕ) h) :
    ContDiffOn ℝ 2 (oddWaveSolution k g h)
        (waveSpaceTimeHalfSpace (2 * k + 1)) ∧
      (∀ x : EuclideanSpace ℝ (Fin (2 * k + 1)), ∀ t : ℝ, 0 < t →
        deriv (deriv (fun s => oddWaveSolution k g h (x, s))) t =
          Δ (fun y => oddWaveSolution k g h (y, t)) x) ∧
      (∀ x : EuclideanSpace ℝ (Fin (2 * k + 1)),
        Tendsto (oddWaveSolution k g h)
          (nhdsWithin (x, 0) (univ ×ˢ Ioi (0 : ℝ))) (nhds (g x))) ∧
      (∀ x : EuclideanSpace ℝ (Fin (2 * k + 1)),
        Tendsto (oddWaveSolutionTimeDeriv k g h)
          (nhdsWithin (x, 0) (univ ×ˢ Ioi (0 : ℝ))) (nhds (h x))) := by
  refine ⟨oddWaveSolution_contDiffOn_halfSpace hg hh, ?_, ?_, ?_⟩
  · intro x t ht
    exact oddWaveSolution_wave_equation_of_order hk hg hh x t ht
  · intro x
    exact oddWaveSolution_tendsto_initial_position hk hg hh x
  · intro x
    exact oddWaveSolution_tendsto_initial_velocity hk hg hh x

end EvansLib
