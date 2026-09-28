import EvansLib.Ch02.WaveSphericalMeanAnalytic
import EvansLib.Ch02.LaplaceRadialPointwise
import EvansLib.Ch02.WaveRadialTransform

/-!
# Euler--Poisson--Darboux equation for spherical means

A smooth solution of the wave equation has spherical means satisfying the
weighted radial equation

`(r^(n - 1) U_r)_r = r^(n - 1) U_tt`.

The proof translates the spatial slice to the origin, applies the sourced weak
radial identity, and then uses the one-dimensional weak-to-pointwise theorem.
Expanding the weighted derivative gives the usual Euler--Poisson--Darboux
equation at every positive radius.
-/

open Filter MeasureTheory Metric Set
open scoped Real ContDiff Topology
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- The Euclidean Laplacian commutes with translation of the argument. -/
lemma laplacian_comp_add_left
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Δ (fun z => f (x + z)) = fun z => Δ f (x + z) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  funext z
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_comp_add_left]

/-- For a wave solution, the spherical integral of the Laplacian of a
translated time slice is the second time derivative of its spherical mean. -/
lemma unitSphereRadialIntegral_laplacian_translate_eq_time_two
    [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (x : EuclideanSpace ℝ (Fin n)) (r t : ℝ) :
    unitSphereRadialIntegral
        (Δ (fun z => u (x + z, t))) r =
      iteratedFDeriv ℝ 2 (waveSphericalMean u x) (r, t)
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] := by
  have htime :=
    iteratedFDeriv_waveSphericalMean_time_two_of_order hu le_rfl x (r, t)
  have hlap : Δ (fun z => u (x + z, t)) =
      fun z => Δ (fun y => u (y, t)) (x + z) :=
    laplacian_comp_add_left (fun y => u (y, t)) x
  rw [hlap]
  rw [htime]
  apply integral_congr_ae
  filter_upwards [] with omega
  exact (hWave (x + r • (omega : EuclideanSpace ℝ (Fin n))) t).symm

/-- Spherical means inherit the initial position pointwise. -/
theorem waveSphericalMean_initial_position [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hInit : ∀ y, u (y, 0) = g y)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    waveSphericalMean u x (r, 0) =
      unitSphereRadialIntegralAt g x r := by
  rw [waveSphericalMean_eq_unitSphereRadialIntegralAt]
  apply integral_congr_ae
  filter_upwards [] with omega
  exact hInit _

/-- Normalized spherical averages inherit the initial position. -/
theorem waveSphericalAverage_initial_position [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hInit : ∀ y, u (y, 0) = g y)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    waveSphericalAverage u x (r, 0) =
      unitSphereRadialAverageAt g x r := by
  rw [waveSphericalAverage, unitSphereRadialAverageAt]
  apply MeasureTheory.average_congr
  filter_upwards [] with omega
  exact hInit _

/-- Spherical means inherit the initial time derivative pointwise. -/
theorem waveSphericalMean_initial_velocity [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u)
    (hInit : ∀ y,
      iteratedFDeriv ℝ 1 u (y, 0)
        ![((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))] = h y)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    iteratedFDeriv ℝ 1 (waveSphericalMean u x) (r, 0)
        ![((0 : ℝ), (1 : ℝ))] =
      unitSphereRadialIntegralAt h x r := by
  rw [iteratedFDeriv_waveSphericalMean_apply_of_order hu x 1 le_rfl (r, 0)
    ![((0 : ℝ), (1 : ℝ))]]
  rw [unitSphereRadialIntegralAt]
  apply integral_congr_ae
  filter_upwards [] with omega
  rw [iteratedFDeriv_waveSphereIntegrand_of_order hu x
    (omega : EuclideanSpace ℝ (Fin n)) 1 le_rfl (r, 0)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hv : (fun i : Fin 1 => waveSphereParamLinear
      (omega : EuclideanSpace ℝ (Fin n))
        (![((0 : ℝ), (1 : ℝ))] i)) =
      ![((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))] := by
    funext i
    fin_cases i
    simp [waveSphereParamLinear]
  rw [hv, hInit]

/-- Normalized spherical averages inherit the initial velocity under the
single derivative needed to differentiate in time. -/
theorem waveSphericalAverage_initial_velocity [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u)
    (hInit : ∀ y,
      iteratedFDeriv ℝ 1 u (y, 0)
        ![((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))] = h y)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    iteratedFDeriv ℝ 1 (waveSphericalAverage u x) (r, 0)
        ![((0 : ℝ), (1 : ℝ))] =
      unitSphereRadialAverageAt h x r := by
  have hscaleMap :=
    iteratedFDeriv_waveSphericalAverage_of_order hu x 1 le_rfl (r, 0)
  have hscale := congrArg
    (fun L : (ℝ × ℝ) [×1]→L[ℝ] ℝ => L ![((0 : ℝ), (1 : ℝ))]) hscaleMap
  rw [unitSphereRadialAverageAt_eq,
    ← waveSphericalMean_initial_velocity hu hInit x r]
  simpa only [ContinuousMultilinearMap.smul_apply, smul_eq_mul] using hscale

/-- Divergence form of the Euler--Poisson--Darboux equation for spherical
means, at an arbitrary center and positive radius. -/
theorem deriv_weightedDeriv_waveSphericalMean_eq_time_two
    [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hn : 0 < n) (hu : ContDiff ℝ 2 u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (x : EuclideanSpace ℝ (Fin n)) (r t : ℝ) (hr : 0 < r) :
    deriv (fun s : ℝ => s ^ (n - 1) *
        deriv (fun q : ℝ => waveSphericalMean u x (q, t)) s) r =
      r ^ (n - 1) *
        iteratedFDeriv ℝ 2 (waveSphericalMean u x) (r, t)
          ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] := by
  let A : ℝ → ℝ := fun s => waveSphericalMean u x (s, t)
  let T : ℝ → ℝ := fun s =>
    iteratedFDeriv ℝ 2 (waveSphericalMean u x) (s, t)
      ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]
  let B : ℝ → ℝ := fun s => s ^ (n - 1) * T s
  let v : EuclideanSpace ℝ (Fin n) → ℝ := fun z => u (x + z, t)
  let R : ℝ := r + 1
  have hA : ContDiff ℝ 2 A := by
    exact (waveSphericalMean_contDiff_of_order hu x).comp
      (contDiff_id.prodMk contDiff_const)
  have hT : Continuous T := by
    have hM := (waveSphericalMean_contDiff_of_order hu x).continuous_iteratedFDeriv
      (m := 2) (by norm_num)
    fun_prop
  have hB : Continuous B :=
    (continuous_id.pow (n - 1)).mul hT
  have hslice : ContDiff ℝ 2 (fun y => u (y, t)) :=
    hu.comp (contDiff_id.prodMk contDiff_const)
  have hv : ContDiff ℝ 2 v :=
    hslice.comp (contDiff_const.add contDiff_id)
  have hv2 : ContDiffOn ℝ 2 v Set.univ :=
    hv.contDiffOn
  have hweak : ∀ (phi : ℝ → ℝ), ContDiff ℝ ∞ phi →
      HasCompactSupport phi → tsupport phi ⊆ Ioo (0 : ℝ) R →
      ∫ s in Ioi (0 : ℝ), A s *
          deriv (fun q : ℝ => q ^ (n - 1) * deriv phi q) s =
        ∫ s in Ioi (0 : ℝ), B s * phi s := by
    intro phi hphi _hphic hphiSupp
    have hsourced :=
      integral_unitSphereRadialIntegral_mul_deriv_weightedDeriv_eq_source
        hn isOpen_univ hv2 (show 0 ≤ R by dsimp [R]; linarith)
        (subset_univ _) hphi hphiSupp
    calc
      ∫ s in Ioi (0 : ℝ), A s *
          deriv (fun q : ℝ => q ^ (n - 1) * deriv phi q) s =
        ∫ s in Ioi (0 : ℝ), unitSphereRadialIntegral v s *
          deriv (fun q : ℝ => q ^ (n - 1) * deriv phi q) s := by rfl
      _ = ∫ s in Ioi (0 : ℝ), s ^ (n - 1) *
          unitSphereRadialIntegral (Δ v) s * phi s := hsourced
      _ = ∫ s in Ioi (0 : ℝ), B s * phi s := by
        apply integral_congr_ae
        filter_upwards [] with s
        rw [unitSphereRadialIntegral_laplacian_translate_eq_time_two
          hu hWave x s t]
  have hpoint :=
    deriv_weightedDeriv_eq_of_integral_mul_deriv_weightedDeriv_eq
      hA hB hweak r (show r ∈ Ioo (0 : ℝ) R by
        constructor
        · exact hr
        · dsimp [R]
          linarith)
  exact hpoint

/-- The spherical mean of a smooth wave solution satisfies the
Euler--Poisson--Darboux equation
`U_tt = U_rr + (n - 1) / r * U_r` at every positive radius. -/
theorem waveSphericalMean_euler_poisson_darboux
    [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hn : 2 ≤ n) (hu : ContDiff ℝ 2 u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (x : EuclideanSpace ℝ (Fin n)) (r t : ℝ) (hr : 0 < r) :
    iteratedFDeriv ℝ 2 (waveSphericalMean u x) (r, t)
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] =
      deriv (deriv (fun q : ℝ => waveSphericalMean u x (q, t))) r +
        ((n : ℝ) - 1) / r *
          deriv (fun q : ℝ => waveSphericalMean u x (q, t)) r := by
  let A : ℝ → ℝ := fun s => waveSphericalMean u x (s, t)
  let T : ℝ :=
    iteratedFDeriv ℝ 2 (waveSphericalMean u x) (r, t)
      ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]
  have hA : ContDiff ℝ 2 A := by
    exact (waveSphericalMean_contDiff_of_order hu x).comp
      (contDiff_id.prodMk contDiff_const)
  have hweighted :
      deriv (fun s : ℝ => s ^ (n - 1) * deriv A s) r =
        r ^ (n - 1) * T :=
    deriv_weightedDeriv_waveSphericalMean_eq_time_two
      (lt_of_lt_of_le Nat.zero_lt_two hn) hu hWave x r t hr
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

/-- The normalized spherical average of a `C²` wave satisfies the same
Euler--Poisson--Darboux equation at every positive radius. -/
theorem waveSphericalAverage_euler_poisson_darboux
    [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (hn : 2 ≤ n) (hu : ContDiff ℝ 2 u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (x : EuclideanSpace ℝ (Fin n)) (r t : ℝ) (hr : 0 < r) :
    iteratedFDeriv ℝ 2 (waveSphericalAverage u x) (r, t)
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] =
      deriv (deriv (fun q : ℝ => waveSphericalAverage u x (q, t))) r +
        ((n : ℝ) - 1) / r *
          deriv (fun q : ℝ => waveSphericalAverage u x (q, t)) r := by
  let c : ℝ :=
    (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real univ)⁻¹
  let M : ℝ → ℝ := fun q => waveSphericalMean u x (q, t)
  let A : ℝ → ℝ := fun q => waveSphericalAverage u x (q, t)
  have hAeq : A = c • M := by
    funext q
    simp only [A, M, Pi.smul_apply, smul_eq_mul, c, waveSphericalAverage_eq]
  have htimeMap :=
    iteratedFDeriv_waveSphericalAverage_of_order hu x 2 le_rfl (r, t)
  have htime := congrArg
    (fun L : (ℝ × ℝ) [×2]→L[ℝ] ℝ =>
      L ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]) htimeMap
  have htime' :
      iteratedFDeriv ℝ 2 (waveSphericalAverage u x) (r, t)
          ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] =
        c * iteratedFDeriv ℝ 2 (waveSphericalMean u x) (r, t)
          ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))] := by
    simpa only [ContinuousMultilinearMap.smul_apply, smul_eq_mul, c] using htime
  have hfirst : deriv A r = c * deriv M r := by
    rw [hAeq]
    simpa [smul_eq_mul] using (deriv_const_smul_field (x := r) c M)
  have hderiv : deriv (c • M) = c • deriv M := by
    funext q
    exact deriv_const_smul_field (x := q) c M
  have hsecond : deriv (deriv A) r = c * deriv (deriv M) r := by
    rw [hAeq, hderiv]
    simpa [smul_eq_mul] using
      (deriv_const_smul_field (x := r) c (deriv M))
  have hmean := waveSphericalMean_euler_poisson_darboux
    hn hu hWave x r t hr
  change _ = deriv (deriv A) r + ((n : ℝ) - 1) / r * deriv A r
  rw [htime', hfirst, hsecond, hmean]
  ring

/-- Evans's odd-dimensional radial transform inherits the initial position
from the spherical mean, before any time/radius derivative commutation is used. -/
theorem waveSphericalMean_radial_transform_initial_position {n k : ℕ}
    [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hInit : ∀ y, u (y, 0) = g y)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
      waveSphericalMean u x (s, 0)) r =
    radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
      unitSphereRadialIntegralAt g x s) r := by
  congr 1
  funext s
  rw [waveSphericalMean_initial_position hInit x s]

/-- The radial part of Evans's odd-dimensional transform equation.  At each
positive radius, two radial derivatives of the transformed spherical mean are
the same transform applied to the second time derivative of the mean. -/
theorem waveSphericalMean_radial_transform_second_deriv {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ}
    (hk : 1 ≤ k) (hu : ContDiff ℝ ∞ u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) (r t : ℝ) (hr : 0 < r) :
    deriv (deriv (radialIter (k - 1)
      (fun s => s ^ (2 * k - 1) * waveSphericalMean u x (s, t)))) r =
    radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
      iteratedFDeriv ℝ 2 (waveSphericalMean u x) (s, t)
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]) r := by
  let phi : ℝ → ℝ := fun s => waveSphericalMean u x (s, t)
  let psi : ℝ → ℝ := fun s =>
    iteratedFDeriv ℝ 2 (waveSphericalMean u x) (s, t)
      ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]
  have hphi : ContDiff ℝ (k + 1 : ℕ) phi := by
    apply ((waveSphericalMean_contDiff hu x).comp
      (contDiff_id.prodMk contDiff_const)).of_le
    exact_mod_cast (show (k + 1 : ℕ∞) ≤ ⊤ from le_top)
  apply waveRadial_transform_of_epd hk hphi ?_ hr
  intro s hs
  have hweighted := deriv_weightedDeriv_waveSphericalMean_eq_time_two
    (n := 2 * k + 1) (by omega)
      (hu.of_le (WithTop.coe_le_coe.mpr
        (show (2 : ℕ∞) ≤ ⊤ from le_top))) hWave x s t hs
  have hweighted' :
      deriv (fun z : ℝ => z ^ (2 * k) * deriv phi z) s =
        s ^ (2 * k) * psi s := by
    simpa [phi, psi, show 2 * k + 1 - 1 = 2 * k by omega] using hweighted
  rw [radialOp, hweighted']
  change s ^ (2 * k) * psi s / s = s ^ (2 * k - 1) * psi s
  rw [show 2 * k = (2 * k - 1) + 1 by omega, pow_succ]
  field_simp
  rw [show 2 * k - 1 + 1 - 1 = 2 * k - 1 by omega]
  ring

/-- Evans's odd-dimensional transform of a spherical mean satisfies the
one-dimensional wave equation at every positive radius. -/
theorem waveSphericalMean_radial_transform_wave_eq {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ}
    (hk : 1 ≤ k) (hu : ContDiff ℝ ∞ u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) (r t : ℝ) (hr : 0 < r) :
    iteratedDeriv 2
        (fun tau => waveRadialTransform k (waveSphericalMean u x) (r, tau)) t =
      deriv (deriv
        (fun s => waveRadialTransform k (waveSphericalMean u x) (s, t))) r := by
  let U : ℝ × ℝ → ℝ := waveSphericalMean u x
  have hU : ContDiff ℝ ∞ U := waveSphericalMean_contDiff hu x
  have htime := iteratedDeriv_waveRadialTransform_time
    (F := U) (order := 2) (t := t) hk hU hr
  have htime' :
      iteratedDeriv 2 (fun tau => waveRadialTransform k U (r, tau)) t =
        radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
          iteratedFDeriv ℝ 2 U (s, t)
            ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]) r := by
    calc
      iteratedDeriv 2 (fun tau => waveRadialTransform k U (r, tau)) t =
          radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
            iteratedDeriv 2 (fun tau => U (s, tau)) t) r := htime
      _ = radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
            iteratedFDeriv ℝ 2 U (s, t)
              ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]) r := by
          congr 2
          funext s
          rw [iteratedDeriv_snd_two_eq_iteratedFDeriv hU]
  have hradial :=
    waveSphericalMean_radial_transform_second_deriv hk hu hWave x r t hr
  change iteratedDeriv 2 (fun tau => waveRadialTransform k U (r, tau)) t =
    deriv (deriv (fun s => waveRadialTransform k U (s, t))) r
  rw [htime']
  simpa [U, waveRadialTransform] using hradial.symm

/-- The initial velocity also passes through Evans's radial transform at every
positive radius. -/
theorem waveSphericalMean_radial_transform_initial_velocity {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ}
    {h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hk : 1 ≤ k) (hu : ContDiff ℝ ∞ u)
    (hInit : ∀ y,
      iteratedFDeriv ℝ 1 u (y, 0)
        ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] = h y)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) (r : ℝ) (hr : 0 < r) :
    iteratedDeriv 1
        (fun tau => waveRadialTransform k (waveSphericalMean u x) (r, tau)) 0 =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        unitSphereRadialIntegralAt h x s) r := by
  let U : ℝ × ℝ → ℝ := waveSphericalMean u x
  have hU : ContDiff ℝ ∞ U := waveSphericalMean_contDiff hu x
  calc
    iteratedDeriv 1 (fun tau => waveRadialTransform k U (r, tau)) 0 =
        radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
          iteratedDeriv 1 (fun tau => U (s, tau)) 0) r :=
      iteratedDeriv_waveRadialTransform_time (F := U) (order := 1) hk hU hr
    _ = radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
          unitSphereRadialIntegralAt h x s) r := by
      congr 2
      funext s
      rw [iteratedDeriv_snd_one_eq_iteratedFDeriv hU]
      exact congrArg (fun z => s ^ (2 * k - 1) * z)
        (waveSphericalMean_initial_velocity
          (hu.of_le (WithTop.coe_le_coe.mpr
            (show (1 : ℕ∞) ≤ ⊤ from le_top))) hInit x s)

/-- Complete spherical-mean form of Evans's transformed one-dimensional wave
problem: the PDE, both initial conditions, and the zero-radius boundary value. -/
theorem waveSphericalMean_transformed_wave_equation {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ}
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hk : 1 ≤ k) (hu : ContDiff ℝ ∞ u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (hPosition : ∀ y, u (y, 0) = g y)
    (hVelocity : ∀ y,
      iteratedFDeriv ℝ 1 u (y, 0)
        ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] = h y)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    (∀ r t, 0 < r →
      iteratedDeriv 2
          (fun tau => waveRadialTransform k (waveSphericalMean u x) (r, tau)) t =
        deriv (deriv
          (fun s => waveRadialTransform k (waveSphericalMean u x) (s, t))) r) ∧
    (∀ r, waveRadialTransform k (waveSphericalMean u x) (r, 0) =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        unitSphereRadialIntegralAt g x s) r) ∧
    (∀ r, 0 < r →
      iteratedDeriv 1
          (fun tau => waveRadialTransform k (waveSphericalMean u x) (r, tau)) 0 =
        radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
          unitSphereRadialIntegralAt h x s) r) ∧
    (∀ t, waveRadialTransform k (waveSphericalMean u x) (0, t) = 0 ∧
      Tendsto (fun r => waveRadialTransform k (waveSphericalMean u x) (r, t))
        (𝓝[>] (0 : ℝ)) (𝓝 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r t hr
    exact waveSphericalMean_radial_transform_wave_eq hk hu hWave x r t hr
  · intro r
    simpa [waveRadialTransform] using
      waveSphericalMean_radial_transform_initial_position
        (k := k) hPosition x r
  · intro r hr
    exact waveSphericalMean_radial_transform_initial_velocity
      hk hu hVelocity x r hr
  · intro t
    constructor
    · simpa [waveRadialTransform] using
        waveRadial_transform_zero hk (fun s => waveSphericalMean u x (s, t))
    · exact waveRadialTransform_tendsto_zero_right
        hk (waveSphericalMean_contDiff hu x) t

/-- Finite-regularity form of the radial part of Evans's transformed spherical
mean equation.  The `C^(k+1)` hypothesis is exactly what the two radial
derivatives and the highest transformed profile derivative consume. -/
theorem waveSphericalMean_radial_transform_second_deriv_of_order {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ}
    (hk : 1 ≤ k) (hu : ContDiff ℝ (k + 1 : ℕ) u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) (r t : ℝ) (hr : 0 < r) :
    deriv (deriv (radialIter (k - 1)
      (fun s => s ^ (2 * k - 1) * waveSphericalMean u x (s, t)))) r =
    radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
      iteratedFDeriv ℝ 2 (waveSphericalMean u x) (s, t)
        ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]) r := by
  let phi : ℝ → ℝ := fun s => waveSphericalMean u x (s, t)
  let psi : ℝ → ℝ := fun s =>
    iteratedFDeriv ℝ 2 (waveSphericalMean u x) (s, t)
      ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]
  have hphi : ContDiff ℝ (k + 1 : ℕ) phi :=
    (waveSphericalMean_contDiff_of_order hu x).comp
      (contDiff_id.prodMk contDiff_const)
  apply waveRadial_transform_of_epd hk hphi ?_ hr
  intro s hs
  have hweighted := deriv_weightedDeriv_waveSphericalMean_eq_time_two
    (n := 2 * k + 1) (by omega)
      (hu.of_le (by exact_mod_cast (show 2 ≤ k + 1 by omega)))
      hWave x s t hs
  have hweighted' :
      deriv (fun z : ℝ => z ^ (2 * k) * deriv phi z) s =
        s ^ (2 * k) * psi s := by
    simpa [phi, psi, show 2 * k + 1 - 1 = 2 * k by omega] using hweighted
  rw [radialOp, hweighted']
  change s ^ (2 * k) * psi s / s = s ^ (2 * k - 1) * psi s
  rw [show 2 * k = (2 * k - 1) + 1 by omega, pow_succ]
  field_simp
  rw [show 2 * k - 1 + 1 - 1 = 2 * k - 1 by omega]
  ring

/-- Under Evans's finite `C^(k+1)` regularity, the transformed spherical mean
satisfies the one-dimensional wave equation at every positive radius. -/
theorem waveSphericalMean_radial_transform_wave_eq_of_order {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ}
    (hk : 1 ≤ k) (hu : ContDiff ℝ (k + 1 : ℕ) u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) (r t : ℝ) (hr : 0 < r) :
    iteratedDeriv 2
        (fun tau => waveRadialTransform k (waveSphericalMean u x) (r, tau)) t =
      deriv (deriv
        (fun s => waveRadialTransform k (waveSphericalMean u x) (s, t))) r := by
  let U : ℝ × ℝ → ℝ := waveSphericalMean u x
  have hU : ContDiff ℝ (k + 1 : ℕ) U :=
    waveSphericalMean_contDiff_of_order hu x
  have htime := iteratedDeriv_waveRadialTransform_time_of_order
    (F := U) (order := 2) (t := t) hk
      (by simpa [show k - 1 + 2 = k + 1 by omega] using hU) hr
  have htime' :
      iteratedDeriv 2 (fun tau => waveRadialTransform k U (r, tau)) t =
        radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
          iteratedFDeriv ℝ 2 U (s, t)
            ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]) r := by
    calc
      iteratedDeriv 2 (fun tau => waveRadialTransform k U (r, tau)) t =
          radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
            iteratedDeriv 2 (fun tau => U (s, tau)) t) r := htime
      _ = radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
            iteratedFDeriv ℝ 2 U (s, t)
              ![((0 : ℝ), (1 : ℝ)), ((0 : ℝ), (1 : ℝ))]) r := by
          congr 2
          funext s
          rw [iteratedDeriv_snd_two_eq_iteratedFDeriv_of_order
            (hU.of_le (by exact_mod_cast (show 2 ≤ k + 1 by omega)))]
  have hradial :=
    waveSphericalMean_radial_transform_second_deriv_of_order
      hk hu hWave x r t hr
  change iteratedDeriv 2 (fun tau => waveRadialTransform k U (r, tau)) t =
    deriv (deriv (fun s => waveRadialTransform k U (s, t))) r
  rw [htime']
  simpa [U, waveRadialTransform] using hradial.symm

/-- The initial velocity passes through the radial transform with only Evans's
finite `C^(k+1)` regularity. -/
theorem waveSphericalMean_radial_transform_initial_velocity_of_order {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ}
    {h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hk : 1 ≤ k) (hu : ContDiff ℝ (k + 1 : ℕ) u)
    (hInit : ∀ y,
      iteratedFDeriv ℝ 1 u (y, 0)
        ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] = h y)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) (r : ℝ) (hr : 0 < r) :
    iteratedDeriv 1
        (fun tau => waveRadialTransform k (waveSphericalMean u x) (r, tau)) 0 =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        unitSphereRadialIntegralAt h x s) r := by
  let U : ℝ × ℝ → ℝ := waveSphericalMean u x
  have hU : ContDiff ℝ (k + 1 : ℕ) U :=
    waveSphericalMean_contDiff_of_order hu x
  calc
    iteratedDeriv 1 (fun tau => waveRadialTransform k U (r, tau)) 0 =
        radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
          iteratedDeriv 1 (fun tau => U (s, tau)) 0) r :=
      iteratedDeriv_waveRadialTransform_time_of_order (F := U) (order := 1)
        hk (hU.of_le (by exact_mod_cast
          (show k - 1 + 1 ≤ k + 1 by omega))) hr
    _ = radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
          unitSphereRadialIntegralAt h x s) r := by
      congr 2
      funext s
      rw [iteratedDeriv_snd_one_eq_iteratedFDeriv_of_order
        (hU.of_le (by exact_mod_cast (show 1 ≤ k + 1 by omega)))]
      exact congrArg (fun z => s ^ (2 * k - 1) * z)
        (waveSphericalMean_initial_velocity
          (hu.of_le (by exact_mod_cast (show 1 ≤ k + 1 by omega))) hInit x s)

/-- Complete finite-regularity spherical-mean form of Evans's transformed
one-dimensional wave problem. -/
theorem waveSphericalMean_transformed_wave_equation_of_order {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ}
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hk : 1 ≤ k) (hu : ContDiff ℝ (k + 1 : ℕ) u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (hPosition : ∀ y, u (y, 0) = g y)
    (hVelocity : ∀ y,
      iteratedFDeriv ℝ 1 u (y, 0)
        ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] = h y)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    (∀ r t, 0 < r →
      iteratedDeriv 2
          (fun tau => waveRadialTransform k (waveSphericalMean u x) (r, tau)) t =
        deriv (deriv
          (fun s => waveRadialTransform k (waveSphericalMean u x) (s, t))) r) ∧
    (∀ r, waveRadialTransform k (waveSphericalMean u x) (r, 0) =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        unitSphereRadialIntegralAt g x s) r) ∧
    (∀ r, 0 < r →
      iteratedDeriv 1
          (fun tau => waveRadialTransform k (waveSphericalMean u x) (r, tau)) 0 =
        radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
          unitSphereRadialIntegralAt h x s) r) ∧
    (∀ t, waveRadialTransform k (waveSphericalMean u x) (0, t) = 0 ∧
      Tendsto (fun r => waveRadialTransform k (waveSphericalMean u x) (r, t))
        (𝓝[>] (0 : ℝ)) (𝓝 0)) := by
  have hU : ContDiff ℝ (k + 1 : ℕ) (waveSphericalMean u x) :=
    waveSphericalMean_contDiff_of_order hu x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r t hr
    exact waveSphericalMean_radial_transform_wave_eq_of_order
      hk hu hWave x r t hr
  · intro r
    simpa [waveRadialTransform] using
      waveSphericalMean_radial_transform_initial_position
        (k := k) hPosition x r
  · intro r hr
    exact waveSphericalMean_radial_transform_initial_velocity_of_order
      hk hu hVelocity x r hr
  · intro t
    constructor
    · simpa [waveRadialTransform] using
        waveRadial_transform_zero hk (fun s => waveSphericalMean u x (s, t))
    · exact waveRadialTransform_tendsto_zero_right_of_order
        hk (hU.of_le (by exact_mod_cast (show k ≤ k + 1 by omega))) t

/-- Complete finite-regularity form of Evans's transformed wave problem for
the normalized spherical average. -/
theorem waveSphericalAverage_transformed_wave_equation_of_order {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (2 * k + 1)) × ℝ → ℝ}
    {g h : EuclideanSpace ℝ (Fin (2 * k + 1)) → ℝ}
    (hk : 1 ≤ k) (hu : ContDiff ℝ (k + 1 : ℕ) u)
    (hWave : ∀ y t,
      iteratedFDeriv ℝ 2 u (y, t)
          ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ)),
            ((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] =
        Δ (fun z => u (z, t)) y)
    (hPosition : ∀ y, u (y, 0) = g y)
    (hVelocity : ∀ y,
      iteratedFDeriv ℝ 1 u (y, 0)
        ![((0 : EuclideanSpace ℝ (Fin (2 * k + 1))), (1 : ℝ))] = h y)
    (x : EuclideanSpace ℝ (Fin (2 * k + 1))) :
    (∀ r t, 0 < r →
      iteratedDeriv 2
          (fun tau => waveRadialTransform k
            (waveSphericalAverage u x) (r, tau)) t =
        deriv (deriv (fun s => waveRadialTransform k
          (waveSphericalAverage u x) (s, t))) r) ∧
    (∀ r, waveRadialTransform k (waveSphericalAverage u x) (r, 0) =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        unitSphereRadialAverageAt g x s) r) ∧
    (∀ r, 0 < r →
      iteratedDeriv 1
          (fun tau => waveRadialTransform k
            (waveSphericalAverage u x) (r, tau)) 0 =
        radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
          unitSphereRadialAverageAt h x s) r) ∧
    (∀ t, waveRadialTransform k (waveSphericalAverage u x) (0, t) = 0 ∧
      Tendsto (fun r => waveRadialTransform k
        (waveSphericalAverage u x) (r, t))
        (𝓝[>] (0 : ℝ)) (𝓝 0)) := by
  let c : ℝ :=
    (((volume : Measure (EuclideanSpace ℝ (Fin (2 * k + 1)))).toSphere).real
      univ)⁻¹
  let U : ℝ × ℝ → ℝ := waveSphericalMean u x
  let A : ℝ × ℝ → ℝ := waveSphericalAverage u x
  have hA : A = c • U := by
    funext p
    simp only [A, U, Pi.smul_apply, smul_eq_mul, c, waveSphericalAverage_eq]
  have hT :
      waveRadialTransform k A = c • waveRadialTransform k U := by
    rw [hA]
    exact waveRadialTransform_const_smul k c U
  have hg :
      (fun s : ℝ => s ^ (2 * k - 1) *
        unitSphereRadialAverageAt g x s) =
      c • (fun s : ℝ => s ^ (2 * k - 1) *
        unitSphereRadialIntegralAt g x s) := by
    funext s
    rw [unitSphereRadialAverageAt_eq]
    simp only [Pi.smul_apply, smul_eq_mul, c]
    ring
  have hh :
      (fun s : ℝ => s ^ (2 * k - 1) *
        unitSphereRadialAverageAt h x s) =
      c • (fun s : ℝ => s ^ (2 * k - 1) *
        unitSphereRadialIntegralAt h x s) := by
    funext s
    rw [unitSphereRadialAverageAt_eq]
    simp only [Pi.smul_apply, smul_eq_mul, c]
    ring
  have hmean := waveSphericalMean_transformed_wave_equation_of_order
    hk hu hWave hPosition hVelocity x
  change
    (∀ r t, 0 < r →
      iteratedDeriv 2
          (fun tau => waveRadialTransform k A (r, tau)) t =
        deriv (deriv (fun s => waveRadialTransform k A (s, t))) r) ∧
    (∀ r, waveRadialTransform k A (r, 0) =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
        unitSphereRadialAverageAt g x s) r) ∧
    (∀ r, 0 < r →
      iteratedDeriv 1 (fun tau => waveRadialTransform k A (r, tau)) 0 =
        radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
          unitSphereRadialAverageAt h x s) r) ∧
    (∀ t, waveRadialTransform k A (0, t) = 0 ∧
      Tendsto (fun r => waveRadialTransform k A (r, t))
        (𝓝[>] (0 : ℝ)) (𝓝 0))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r t hr
    have hpde :
        iteratedDeriv 2 (fun tau =>
            waveRadialTransform k U (r, tau)) t =
          deriv (deriv (fun s => waveRadialTransform k U (s, t))) r := by
      simpa [U] using hmean.1 r t hr
    rw [hT]
    have ht :
        iteratedDeriv 2 (fun tau =>
            (c • waveRadialTransform k U) (r, tau)) t =
          c * iteratedDeriv 2 (fun tau =>
            waveRadialTransform k U (r, tau)) t := by
      simp only [Pi.smul_apply, smul_eq_mul, iteratedDeriv_const_mul_field]
    have hr1 :
        (fun s => (c • waveRadialTransform k U) (s, t)) =
          c • (fun s => waveRadialTransform k U (s, t)) := rfl
    have hr2 :
        deriv (fun s => (c • waveRadialTransform k U) (s, t)) =
          c • deriv (fun s => waveRadialTransform k U (s, t)) := by
      rw [hr1]
      funext s
      exact deriv_const_smul_field c
        (fun q => waveRadialTransform k U (q, t))
    have hr3 :
        deriv (deriv
            (fun s => (c • waveRadialTransform k U) (s, t))) r =
          c * deriv (deriv
            (fun s => waveRadialTransform k U (s, t))) r := by
      rw [hr2]
      simpa only [Pi.smul_apply, smul_eq_mul] using
        (deriv_const_smul_field (x := r) c
          (deriv (fun s => waveRadialTransform k U (s, t))))
    rw [ht, hr3, hpde]
  · intro r
    rw [hT, hg, radialIter_const_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    simpa [U] using congrArg (fun z => c * z) (hmean.2.1 r)
  · intro r hr
    have hvel :
        iteratedDeriv 1 (fun tau =>
            waveRadialTransform k U (r, tau)) 0 =
          radialIter (k - 1) (fun s => s ^ (2 * k - 1) *
            unitSphereRadialIntegralAt h x s) r := by
      simpa [U] using hmean.2.2.1 r hr
    rw [hT, hh, radialIter_const_smul]
    simp only [Pi.smul_apply, smul_eq_mul, iteratedDeriv_const_mul_field]
    rw [hvel]
  · intro t
    have hzero : waveRadialTransform k U (0, t) = 0 := by
      simpa [U] using (hmean.2.2.2 t).1
    have htrace :
        Tendsto (fun r => waveRadialTransform k U (r, t))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa [U] using (hmean.2.2.2 t).2
    constructor
    · rw [hT]
      simp [hzero]
    · rw [hT]
      simpa only [Pi.smul_apply, smul_eq_mul, mul_zero] using
        htrace.const_mul c

end EvansLib
