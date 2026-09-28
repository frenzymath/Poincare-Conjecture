import EvansLib.Ch02.Wave
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Evans, Ch. 2 §2.4 — wave energy and one-dimensional propagation

This file proves the pointwise energy-conservation law in arbitrary spatial
dimension and records a kernel-checked one-dimensional specialization of its
propagation consequences.  The characteristic (Riemann-invariant) calculation
is the one-dimensional analogue of the energy flux calculation:
`u_t + u_x` and `u_t - u_x` are constant on the two characteristic families.
It gives uniqueness for zero Cauchy data and finite propagation in a cone.

The hypotheses use the existing `waveSymbol`/`IsPDESolutionOn` interface.  The
cone theorem is stated for the open cone and closed initial interval; this avoids
any boundary-regularity convention hidden in the informal textbook notation.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace EvansLib

/-! ## Coordinates and characteristic fields -/

/-- A point `(x,t)` of one-dimensional space-time, with the same coordinate
convention as `Wave.lean` (`0` is time and `1` is space). -/
def wavePoint (x t : ℝ) : SpaceTime 1 :=
  t • timeDir 1 + x • spaceDir 1 0

@[simp] lemma wavePoint_apply_zero (x t : ℝ) : wavePoint x t 0 = t := by
  simp [wavePoint, timeDir, spaceDir, PiLp.add_apply, PiLp.smul_apply]

@[simp] lemma wavePoint_apply_one (x t : ℝ) : wavePoint x t 1 = x := by
  simp [wavePoint, timeDir, spaceDir, PiLp.add_apply, PiLp.smul_apply]

@[simp] lemma wavePoint_zero (x : ℝ) : wavePoint x 0 = x • spaceDir 1 0 := by
  simp [wavePoint]

lemma wavePoint_coordinates (p : SpaceTime 1) : wavePoint (p 1) (p 0) = p := by
  ext k
  fin_cases k <;>
    simp [wavePoint, timeDir, spaceDir, PiLp.add_apply, PiLp.smul_apply]

/-- The two characteristic directions in `(t,x)` coordinates. -/
def waveLeftDir : SpaceTime 1 := timeDir 1 - spaceDir 1 0
def waveRightDir : SpaceTime 1 := timeDir 1 + spaceDir 1 0

/-- The first derivatives used in the characteristic calculation. -/
def waveTimeDeriv (u : SpaceTime 1 → ℝ) (p : SpaceTime 1) : ℝ :=
  fderiv ℝ u p (timeDir 1)

def waveSpaceDeriv (u : SpaceTime 1 → ℝ) (p : SpaceTime 1) : ℝ :=
  fderiv ℝ u p (spaceDir 1 0)

def waveRiemannPlus (u : SpaceTime 1 → ℝ) : SpaceTime 1 → ℝ :=
  fun p => waveTimeDeriv u p + waveSpaceDeriv u p

def waveRiemannMinus (u : SpaceTime 1 → ℝ) : SpaceTime 1 → ℝ :=
  fun p => waveTimeDeriv u p - waveSpaceDeriv u p

/-! ## Second derivative bookkeeping -/

lemma wave_fderiv_fderiv_apply {u : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u) (p v w : SpaceTime 1) :
    fderiv ℝ (fun q => fderiv ℝ u q w) p v =
      iteratedFDeriv ℝ 2 u p ![v, w] := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h : fderiv ℝ (fun q => fderiv ℝ u q w) p v =
      fderiv ℝ (fderiv ℝ u) p v w := by
    rw [fderiv_clm_apply hfd (differentiableAt_const w)]
    simp
  simpa [iteratedFDeriv_two_apply] using h

lemma wave_pde_second_deriv {u : SpaceTime 1 → ℝ}
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol 1) u) (p : SpaceTime 1) :
    iteratedFDeriv ℝ 2 u p ![timeDir 1, timeDir 1] =
      iteratedFDeriv ℝ 2 u p ![spaceDir 1 0, spaceDir 1 0] := by
  have h := hsol p (Set.mem_univ p)
  rw [waveSymbol_eq] at h
  linarith

/-- The general `n`-dimensional wave equation identifies the pure second time
derivative with the sum of the pure second spatial derivatives. -/
lemma wave_pde_second_deriv_general {n : ℕ} {u : SpaceTime n → ℝ}
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol n) u) (p : SpaceTime n) :
    iteratedFDeriv ℝ 2 u p ![timeDir n, timeDir n] =
      ∑ i : Fin n, iteratedFDeriv ℝ 2 u p ![spaceDir n i, spaceDir n i] := by
  have h := hsol p (Set.mem_univ p)
  have hzero :
      (iteratedFDeriv ℝ 2 u p) ![timeDir n, timeDir n] -
          ∑ i : Fin n, (iteratedFDeriv ℝ 2 u p) ![spaceDir n i, spaceDir n i] = 0 := by
    simpa [waveSymbol, timeD2, spatialLaplace, jetD2, pdeJet] using h
  linarith

/-! ## The local energy conservation law in arbitrary dimension -/

/-- The time derivative entering the wave energy in arbitrary dimension. -/
def waveTimeDerivative {n : ℕ} (u : SpaceTime n → ℝ) (p : SpaceTime n) : ℝ :=
  fderiv ℝ u p (timeDir n)

/-- The `i`th spatial derivative entering the wave energy. -/
def waveSpatialDerivative {n : ℕ} (u : SpaceTime n → ℝ) (i : Fin n)
    (p : SpaceTime n) : ℝ :=
  fderiv ℝ u p (spaceDir n i)

/-- Twice the standard pointwise wave energy density.  Omitting the common
factor `1 / 2` keeps the local conservation identity algebraic. -/
def waveEnergyDensity {n : ℕ} (u : SpaceTime n → ℝ) (p : SpaceTime n) : ℝ :=
  waveTimeDerivative u p ^ 2 + ∑ i : Fin n, waveSpatialDerivative u i p ^ 2

/-- Twice the standard energy flux in the `i`th spatial direction. -/
def waveEnergyFlux {n : ℕ} (u : SpaceTime n → ℝ) (i : Fin n)
    (p : SpaceTime n) : ℝ :=
  2 * waveTimeDerivative u p * waveSpatialDerivative u i p

/-- The spatial energy flux contracted with a direction `ν`.  On the boundary
of a ball, `ν` is the outward unit normal and this is the boundary term produced
by the divergence theorem. -/
def waveNormalEnergyFlux {n : ℕ} (u : SpaceTime n → ℝ)
    (ν : EuclideanℝN n) (p : SpaceTime n) : ℝ :=
  ∑ i : Fin n, ν i * waveEnergyFlux u i p

lemma waveEnergyDensity_nonneg {n : ℕ} (u : SpaceTime n → ℝ) (p : SpaceTime n) :
    0 ≤ waveEnergyDensity u p := by
  unfold waveEnergyDensity
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Pointwise energy vanishes exactly when both the time derivative and every
spatial derivative vanish. -/
lemma waveEnergyDensity_eq_zero_iff {n : ℕ} (u : SpaceTime n → ℝ)
    (p : SpaceTime n) :
    waveEnergyDensity u p = 0 ↔
      waveTimeDerivative u p = 0 ∧ ∀ i : Fin n, waveSpatialDerivative u i p = 0 := by
  unfold waveEnergyDensity
  constructor
  · intro h
    have hsum_nonneg : 0 ≤ ∑ i : Fin n, waveSpatialDerivative u i p ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have ht_sq : waveTimeDerivative u p ^ 2 = 0 := by
      nlinarith [sq_nonneg (waveTimeDerivative u p)]
    have hx_sq : ∑ i : Fin n, waveSpatialDerivative u i p ^ 2 = 0 := by
      nlinarith [sq_nonneg (waveTimeDerivative u p)]
    refine ⟨sq_eq_zero_iff.mp ht_sq, fun i => sq_eq_zero_iff.mp ?_⟩
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hx_sq i
      (Finset.mem_univ i)
  · rintro ⟨ht, hx⟩
    simp [ht, hx]

/-- The normal component of the wave-energy flux is bounded by the energy
density for every spatial direction of norm at most one.  This is the sharp
pointwise estimate controlling the lateral boundary of a shrinking ball. -/
lemma abs_waveNormalEnergyFlux_le_waveEnergyDensity {n : ℕ}
    (u : SpaceTime n → ℝ) (ν : EuclideanℝN n) (p : SpaceTime n)
    (hν : ‖ν‖ ≤ 1) :
    |waveNormalEnergyFlux u ν p| ≤ waveEnergyDensity u p := by
  let a := waveTimeDerivative u p
  let b : Fin n → ℝ := fun i => waveSpatialDerivative u i p
  let s : ℝ := ∑ i : Fin n, ν i * b i
  let B : ℝ := ∑ i : Fin n, b i ^ 2
  have hνsq : (∑ i : Fin n, ν i ^ 2) ≤ 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq]
    nlinarith [norm_nonneg ν]
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : s ^ 2 ≤ (∑ i : Fin n, ν i ^ 2) * B := by
    simpa [s, B] using
      (Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ (fun i => ν i) b)
  have hs : s ^ 2 ≤ B := hcs.trans (by
    simpa using mul_le_mul_of_nonneg_right hνsq hB)
  have hflux : waveNormalEnergyFlux u ν p = 2 * a * s := by
    unfold waveNormalEnergyFlux waveEnergyFlux
    calc
      ∑ i : Fin n, ν i * (2 * waveTimeDerivative u p * waveSpatialDerivative u i p) =
          ∑ i : Fin n, (2 * a) * (ν i * b i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [a, b]
            ring
      _ = 2 * a * s := by rw [Finset.mul_sum]
  rw [hflux]
  have hamgm : |2 * a * s| ≤ a ^ 2 + s ^ 2 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (a + s)]
    · nlinarith [sq_nonneg (a - s)]
  calc
    |2 * a * s| ≤ a ^ 2 + s ^ 2 := hamgm
    _ ≤ a ^ 2 + B := by linarith
    _ = waveEnergyDensity u p := by rfl

/-- Pointwise sign of the complete lateral term in the energy identity for a
unit-speed shrinking ball: outward flux minus energy density is nonpositive. -/
lemma wave_moving_boundary_flux_nonpos {n : ℕ} (u : SpaceTime n → ℝ)
    (ν : EuclideanℝN n) (p : SpaceTime n) (hν : ‖ν‖ ≤ 1) :
    waveNormalEnergyFlux u ν p - waveEnergyDensity u p ≤ 0 := by
  rw [sub_nonpos]
  exact (le_abs_self _).trans (abs_waveNormalEnergyFlux_le_waveEnergyDensity u ν p hν)

lemma wave_fderiv_fderiv_apply_general {n : ℕ} {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (p v w : SpaceTime n) :
    fderiv ℝ (fun q => fderiv ℝ u q w) p v =
      iteratedFDeriv ℝ 2 u p ![v, w] := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h : fderiv ℝ (fun q => fderiv ℝ u q w) p v =
      fderiv ℝ (fderiv ℝ u) p v w := by
    rw [fderiv_clm_apply hfd (differentiableAt_const w)]
    simp
  simpa [iteratedFDeriv_two_apply] using h

lemma wave_mixed_symm_general {n : ℕ} {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u)
    (p v w : SpaceTime n) :
    iteratedFDeriv ℝ 2 u p ![v, w] = iteratedFDeriv ℝ 2 u p ![w, v] := by
  exact (hu.contDiffAt.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons

lemma waveTimeDerivative_fderiv {n : ℕ} {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (p v : SpaceTime n) :
    fderiv ℝ (waveTimeDerivative u) p v =
      iteratedFDeriv ℝ 2 u p ![v, timeDir n] := by
  exact wave_fderiv_fderiv_apply_general hu p v (timeDir n)

lemma waveSpatialDerivative_fderiv {n : ℕ} {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (i : Fin n) (p v : SpaceTime n) :
    fderiv ℝ (waveSpatialDerivative u i) p v =
      iteratedFDeriv ℝ 2 u p ![v, spaceDir n i] := by
  exact wave_fderiv_fderiv_apply_general hu p v (spaceDir n i)

/-- **Pointwise wave-energy conservation in `n` spatial dimensions.**  The
time derivative of twice the usual energy density is the spatial divergence
of twice the usual energy flux.  This is the local identity integrated over
shrinking balls in Evans's finite-propagation proof. -/
theorem wave_energy_conservation_pointwise {n : ℕ} {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol n) u) (p : SpaceTime n) :
    fderiv ℝ (waveEnergyDensity u) p (timeDir n) =
      ∑ i : Fin n, fderiv ℝ (waveEnergyFlux u i) p (spaceDir n i) := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have ht : DifferentiableAt ℝ (waveTimeDerivative u) p := by
    exact hfd.clm_apply (differentiableAt_const (timeDir n))
  have hx (i : Fin n) : DifferentiableAt ℝ (waveSpatialDerivative u i) p := by
    exact hfd.clm_apply (differentiableAt_const (spaceDir n i))
  have hleft :
      fderiv ℝ (waveEnergyDensity u) p (timeDir n) =
        2 * waveTimeDerivative u p *
            iteratedFDeriv ℝ 2 u p ![timeDir n, timeDir n] +
          ∑ i : Fin n, 2 * waveSpatialDerivative u i p *
            iteratedFDeriv ℝ 2 u p ![timeDir n, spaceDir n i] := by
    unfold waveEnergyDensity
    have hsum := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (hx i).hasFDerivAt.pow 2)
    have henergy := (ht.hasFDerivAt.pow 2).add hsum
    have henergy' : HasFDerivAt
        (fun q => waveTimeDerivative u q ^ 2 +
          ∑ i : Fin n, waveSpatialDerivative u i q ^ 2)
        ((2 • waveTimeDerivative u p ^ (2 - 1)) • fderiv ℝ (waveTimeDerivative u) p +
          ∑ i : Fin n, (2 • waveSpatialDerivative u i p ^ (2 - 1)) •
            fderiv ℝ (waveSpatialDerivative u i) p) p := by
      exact henergy
    rw [henergy'.fderiv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply, nsmul_eq_mul]
    rw [waveTimeDerivative_fderiv hu]
    norm_num [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [waveSpatialDerivative_fderiv hu]
  have hright (i : Fin n) :
      fderiv ℝ (waveEnergyFlux u i) p (spaceDir n i) =
        2 * (iteratedFDeriv ℝ 2 u p ![spaceDir n i, timeDir n] *
              waveSpatialDerivative u i p +
            waveTimeDerivative u p *
              iteratedFDeriv ℝ 2 u p ![spaceDir n i, spaceDir n i]) := by
    have h2t : DifferentiableAt ℝ (fun q => 2 * waveTimeDerivative u q) p :=
      ht.const_mul 2
    unfold waveEnergyFlux
    rw [fderiv_fun_mul h2t (hx i)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_fun_mul (differentiableAt_const (2 : ℝ)) ht]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rw [waveSpatialDerivative_fderiv hu, waveTimeDerivative_fderiv hu]
    simp
    ring
  rw [hleft]
  simp_rw [hright]
  have hpde := wave_pde_second_deriv_general hsol p
  rw [hpde, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [wave_mixed_symm_general hu p (timeDir n) (spaceDir n i)]
  ring

lemma wave_mixed_symm {u : SpaceTime 1 → ℝ} (hu : ContDiff ℝ 2 u)
    (p v w : SpaceTime 1) :
    iteratedFDeriv ℝ 2 u p ![v, w] = iteratedFDeriv ℝ 2 u p ![w, v] := by
  exact (hu.contDiffAt.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons

/-! ## Characteristic transport of the Riemann invariants -/

lemma waveRiemannPlus_differentiable {u : SpaceTime 1 → ℝ} (hu : ContDiff ℝ 2 u) :
    Differentiable ℝ (waveRiemannPlus u) := by
  have hfd : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact (hfd.clm_apply (differentiable_const (timeDir 1))).add
    (hfd.clm_apply (differentiable_const (spaceDir 1 0)))

lemma waveRiemannMinus_differentiable {u : SpaceTime 1 → ℝ} (hu : ContDiff ℝ 2 u) :
    Differentiable ℝ (waveRiemannMinus u) := by
  have hfd : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  exact (hfd.clm_apply (differentiable_const (timeDir 1))).sub
    (hfd.clm_apply (differentiable_const (spaceDir 1 0)))

lemma waveRiemannPlus_fderiv_left {u : SpaceTime 1 → ℝ} (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol 1) u) (p : SpaceTime 1) :
    fderiv ℝ (waveRiemannPlus u) p waveLeftDir = 0 := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym := wave_mixed_symm hu p (spaceDir 1 0) (timeDir 1)
  unfold waveRiemannPlus waveTimeDeriv waveSpaceDeriv
  change fderiv ℝ
    ((fun q => fderiv ℝ u q (timeDir 1)) +
      (fun q => fderiv ℝ u q (spaceDir 1 0))) p waveLeftDir = 0
  rw [fderiv_add
    (hfd.clm_apply (differentiableAt_const (timeDir 1)))
    (hfd.clm_apply (differentiableAt_const (spaceDir 1 0))),
    ContinuousLinearMap.add_apply, wave_fderiv_fderiv_apply hu,
    wave_fderiv_fderiv_apply hu]
  let B := iteratedFDeriv ℝ 2 u p
  have h1 : B ![timeDir 1 - spaceDir 1 0, timeDir 1] =
      B ![timeDir 1, timeDir 1] - B ![spaceDir 1 0, timeDir 1] := by
    convert B.map_update_sub ![timeDir 1, timeDir 1] (0 : Fin 2)
      (timeDir 1) (spaceDir 1 0) using 1 <;> congr 1
    all_goals
      ext j
      fin_cases j <;> rfl
  have h2 : B ![timeDir 1 - spaceDir 1 0, spaceDir 1 0] =
      B ![timeDir 1, spaceDir 1 0] - B ![spaceDir 1 0, spaceDir 1 0] := by
    convert B.map_update_sub ![timeDir 1, spaceDir 1 0] (0 : Fin 2)
      (timeDir 1) (spaceDir 1 0) using 1 <;> congr 1
    all_goals
      ext j
      fin_cases j <;> rfl
  change B ![timeDir 1 - spaceDir 1 0, timeDir 1] +
      B ![timeDir 1 - spaceDir 1 0, spaceDir 1 0] = 0
  rw [h1, h2, hsym]
  have hpde := wave_pde_second_deriv hsol p
  rw [← hpde]
  ring

lemma waveRiemannMinus_fderiv_right {u : SpaceTime 1 → ℝ} (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol 1) u) (p : SpaceTime 1) :
    fderiv ℝ (waveRiemannMinus u) p waveRightDir = 0 := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym := wave_mixed_symm hu p (spaceDir 1 0) (timeDir 1)
  unfold waveRiemannMinus waveTimeDeriv waveSpaceDeriv
  change fderiv ℝ
    ((fun q => fderiv ℝ u q (timeDir 1)) -
      (fun q => fderiv ℝ u q (spaceDir 1 0))) p waveRightDir = 0
  rw [fderiv_sub
    (hfd.clm_apply (differentiableAt_const (timeDir 1)))
    (hfd.clm_apply (differentiableAt_const (spaceDir 1 0))),
    ContinuousLinearMap.sub_apply, wave_fderiv_fderiv_apply hu,
    wave_fderiv_fderiv_apply hu]
  let B := iteratedFDeriv ℝ 2 u p
  have h1 : B ![timeDir 1 + spaceDir 1 0, timeDir 1] =
      B ![timeDir 1, timeDir 1] + B ![spaceDir 1 0, timeDir 1] := by
    convert B.map_update_add ![timeDir 1, timeDir 1] (0 : Fin 2)
      (timeDir 1) (spaceDir 1 0) using 1 <;> congr 1
    all_goals
      ext j
      fin_cases j <;> rfl
  have h2 : B ![timeDir 1 + spaceDir 1 0, spaceDir 1 0] =
      B ![timeDir 1, spaceDir 1 0] + B ![spaceDir 1 0, spaceDir 1 0] := by
    convert B.map_update_add ![timeDir 1, spaceDir 1 0] (0 : Fin 2)
      (timeDir 1) (spaceDir 1 0) using 1 <;> congr 1
    all_goals
      ext j
      fin_cases j <;> rfl
  change B ![timeDir 1 + spaceDir 1 0, timeDir 1] -
      B ![timeDir 1 + spaceDir 1 0, spaceDir 1 0] = 0
  rw [h1, h2, hsym]
  have hpde := wave_pde_second_deriv hsol p
  rw [← hpde]
  ring

lemma waveRiemannPlus_const_char {u : SpaceTime 1 → ℝ} (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol 1) u) (p : SpaceTime 1)
    (a b : ℝ) :
    waveRiemannPlus u (p + a • waveLeftDir) =
      waveRiemannPlus u (p + b • waveLeftDir) := by
  have hline : ∀ s : ℝ, HasDerivAt
      (fun s => waveRiemannPlus u (p + s • waveLeftDir)) 0 s := by
    intro s
    have hpath : HasDerivAt (fun s : ℝ => p + s • waveLeftDir)
        waveLeftDir s := by
      simpa using ((hasDerivAt_id s).smul_const waveLeftDir).const_add p
    have hc := (waveRiemannPlus_differentiable hu
      (p + s • waveLeftDir)).hasFDerivAt.comp_hasDerivAt s hpath
    rw [waveRiemannPlus_fderiv_left hu hsol] at hc
    exact hc
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hline s).differentiableAt) (fun s => (hline s).deriv) a b
  simpa using hconst

lemma waveRiemannMinus_const_char {u : SpaceTime 1 → ℝ} (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol 1) u) (p : SpaceTime 1)
    (a b : ℝ) :
    waveRiemannMinus u (p + a • waveRightDir) =
      waveRiemannMinus u (p + b • waveRightDir) := by
  have hline : ∀ s : ℝ, HasDerivAt
      (fun s => waveRiemannMinus u (p + s • waveRightDir)) 0 s := by
    intro s
    have hpath : HasDerivAt (fun s : ℝ => p + s • waveRightDir)
        waveRightDir s := by
      simpa using ((hasDerivAt_id s).smul_const waveRightDir).const_add p
    have hc := (waveRiemannMinus_differentiable hu
      (p + s • waveRightDir)).hasFDerivAt.comp_hasDerivAt s hpath
    rw [waveRiemannMinus_fderiv_right hu hsol] at hc
    exact hc
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hline s).differentiableAt) (fun s => (hline s).deriv) a b
  simpa using hconst

/-! ## Geometric foot identities -/

lemma wave_left_foot (p : SpaceTime 1) :
    p + (-(p 0)) • waveLeftDir = wavePoint (p 1 + p 0) 0 := by
  ext k
  fin_cases k <;>
    simp [waveLeftDir, wavePoint, timeDir, spaceDir, PiLp.add_apply, PiLp.smul_apply]

lemma wave_right_foot (p : SpaceTime 1) :
    p + (-(p 0)) • waveRightDir = wavePoint (p 1 - p 0) 0 := by
  ext k
  fin_cases k <;>
    simp [waveRightDir, wavePoint, timeDir, spaceDir, PiLp.add_apply, PiLp.smul_apply,
      sub_eq_add_neg]

lemma waveSpaceDeriv_wavePoint_hasDerivAt {u : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u) (x : ℝ) :
    HasDerivAt (fun y : ℝ => u (wavePoint y 0))
      (waveSpaceDeriv u (wavePoint x 0)) x := by
  have hp : HasDerivAt (fun y : ℝ => wavePoint y 0)
      (spaceDir 1 0) x := by
    simpa [wavePoint] using ((hasDerivAt_id x).smul_const (spaceDir 1 0))
  have hc := hu.contDiffAt.differentiableAt (by norm_num)
    |>.hasFDerivAt.comp_hasDerivAt x hp
  exact hc

lemma waveSpaceDeriv_initial_zero_of_zero {u : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u) (hinit : ∀ x : ℝ, u (wavePoint x 0) = 0) (x : ℝ) :
    waveSpaceDeriv u (wavePoint x 0) = 0 := by
  have hev : (fun y : ℝ => u (wavePoint y 0)) =ᶠ[nhds x] (fun _ => (0 : ℝ)) :=
    Filter.Eventually.of_forall hinit
  have hz := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  exact (waveSpaceDeriv_wavePoint_hasDerivAt hu x).unique hz

lemma waveSpaceDeriv_initial_zero_of_local_zero {u : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u) {x₀ t₀ : ℝ}
    (hinit : ∀ x : ℝ, |x - x₀| ≤ t₀ → u (wavePoint x 0) = 0)
    {x : ℝ} (hx : |x - x₀| < t₀) :
    waveSpaceDeriv u (wavePoint x 0) = 0 := by
  have hxball : x ∈ Metric.ball x₀ t₀ := by
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  have hmem : Metric.ball x₀ t₀ ∈ nhds x := Metric.isOpen_ball.mem_nhds hxball
  have hev : (fun y : ℝ => u (wavePoint y 0)) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmem] with y hy
    apply hinit y
    have hy' : |y - x₀| < t₀ := by
      simpa [Metric.mem_ball, Real.dist_eq] using hy
    exact hy'.le
  have hz := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  exact (waveSpaceDeriv_wavePoint_hasDerivAt hu x).unique hz

lemma waveTimeDeriv_zero_of_characteristic_values {u : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol 1) u) (p : SpaceTime 1)
    (hplus0 : waveRiemannPlus u (wavePoint (p 1 + p 0) 0) = 0)
    (hminus0 : waveRiemannMinus u (wavePoint (p 1 - p 0) 0) = 0) :
    waveTimeDeriv u p = 0 := by
  have hp := waveRiemannPlus_const_char hu hsol p 0 (-(p 0))
  have hm := waveRiemannMinus_const_char hu hsol p 0 (-(p 0))
  rw [zero_smul, add_zero, wave_left_foot] at hp
  rw [zero_smul, add_zero, wave_right_foot] at hm
  rw [hplus0] at hp
  rw [hminus0] at hm
  dsimp [waveRiemannPlus, waveRiemannMinus] at hp hm
  linarith

/-! ## Zero Cauchy data -/

theorem wave_zero_cauchy_unique {u : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol 1) u)
    (hinit : ∀ x : ℝ, u (wavePoint x 0) = 0)
    (hinit_t : ∀ x : ℝ, waveTimeDeriv u (wavePoint x 0) = 0) :
    ∀ p : SpaceTime 1, u p = 0 := by
  have hspace : ∀ x : ℝ, waveSpaceDeriv u (wavePoint x 0) = 0 :=
    fun x => waveSpaceDeriv_initial_zero_of_zero hu hinit x
  have hut : ∀ q : SpaceTime 1, waveTimeDeriv u q = 0 := by
    intro q
    apply waveTimeDeriv_zero_of_characteristic_values hu hsol q
    · dsimp [waveRiemannPlus]
      rw [hinit_t, hspace]
      ring
    · dsimp [waveRiemannMinus]
      rw [hinit_t, hspace]
      ring
  intro p
  have hline : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => u (wavePoint (p 1) s)) 0 s := by
    intro s
    have hp : HasDerivAt (fun r : ℝ => wavePoint (p 1) r)
        (timeDir 1) s := by
      simpa [wavePoint] using ((hasDerivAt_id s).smul_const (timeDir 1)).const_add
        ((p 1) • spaceDir 1 0)
    have hc := (hu.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
      |>.comp_hasDerivAt s hp
    have hc0 := hc.congr_deriv (hut (wavePoint (p 1) s))
    simpa [Function.comp_def, waveTimeDeriv] using hc0
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hline s).differentiableAt) (fun s => (hline s).deriv) 0 (p 0)
  rw [← wavePoint_coordinates p, ← hconst, hinit]

/-- Two `C²` one-dimensional waves on all of space with the same displacement
and velocity at `t = 0` coincide. -/
theorem wave_cauchy_unique_1d {u v : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hsolu : IsPDESolutionOn 2 Set.univ (waveSymbol 1) u)
    (hsolv : IsPDESolutionOn 2 Set.univ (waveSymbol 1) v)
    (hinit : ∀ x : ℝ, u (wavePoint x 0) = v (wavePoint x 0))
    (hinit_t : ∀ x : ℝ,
      waveTimeDeriv u (wavePoint x 0) = waveTimeDeriv v (wavePoint x 0)) :
    u = v := by
  have hw : ContDiff ℝ 2 (u - v) := hu.sub hv
  have hsolw : IsPDESolutionOn 2 Set.univ (waveSymbol 1) (u - v) := by
    intro p _
    rw [waveSymbol_eq, iteratedFDeriv_sub_apply hu.contDiffAt hv.contDiffAt]
    simp only [ContinuousMultilinearMap.sub_apply]
    have huwave := wave_pde_second_deriv hsolu p
    have hvwave := wave_pde_second_deriv hsolv p
    linarith
  have hwinit : ∀ x : ℝ, (u - v) (wavePoint x 0) = 0 := by
    intro x
    simp only [Pi.sub_apply]
    exact sub_eq_zero.mpr (hinit x)
  have hwinit_t : ∀ x : ℝ, waveTimeDeriv (u - v) (wavePoint x 0) = 0 := by
    intro x
    unfold waveTimeDeriv
    rw [fderiv_sub
      (hu.contDiffAt.differentiableAt (by norm_num))
      (hv.contDiffAt.differentiableAt (by norm_num)), ContinuousLinearMap.sub_apply]
    exact sub_eq_zero.mpr (hinit_t x)
  funext p
  exact sub_eq_zero.mp (wave_zero_cauchy_unique hw hsolw hwinit hwinit_t p)

/-- A one-dimensional wave vanishes inside the backward characteristic cone
from an interval of zero initial displacement and velocity. -/
theorem wave_finite_propagation_1d {u : SpaceTime 1 → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 Set.univ (waveSymbol 1) u)
    {x₀ t₀ : ℝ} (_ht₀ : 0 < t₀)
    (hinit : ∀ x : ℝ, |x - x₀| ≤ t₀ → u (wavePoint x 0) = 0)
    (hinit_t : ∀ x : ℝ, |x - x₀| ≤ t₀ → waveTimeDeriv u (wavePoint x 0) = 0) :
    ∀ p : SpaceTime 1, 0 ≤ p 0 → p 0 ≤ t₀ →
      |p 1 - x₀| < t₀ - p 0 → u p = 0 := by
  intro p hp0 hpt hcone
  have hpath : ∀ s ∈ Set.Icc (0 : ℝ) (p 0),
      HasDerivWithinAt (fun s : ℝ => u (wavePoint (p 1) s)) 0
        (Set.Icc (0 : ℝ) (p 0)) s := by
    intro s hs
    have hsq : 0 ≤ s := hs.1
    have hsq' : s ≤ p 0 := hs.2
    have hqcone : |p 1 - x₀| < t₀ - s := by linarith
    have hq : waveTimeDeriv u (wavePoint (p 1) s) = 0 := by
      -- The same characteristic argument applies at every point of the vertical path.
      have hp' : (wavePoint (p 1) s) 0 = s := by simp
      have hx' : (wavePoint (p 1) s) 1 = p 1 := by simp
      apply (show waveTimeDeriv u (wavePoint (p 1) s) = 0 from ?_)
      have hfp : |p 1 + s - x₀| < t₀ := by
        calc
          |p 1 + s - x₀| = |(p 1 - x₀) + s| := by ring_nf
          _ ≤ |p 1 - x₀| + |s| := abs_add_le _ _
          _ = |p 1 - x₀| + s := by rw [abs_of_nonneg hsq]
          _ < t₀ := by linarith
      have hfm : |p 1 - s - x₀| < t₀ := by
        calc
          |p 1 - s - x₀| = |(p 1 - x₀) + (-s)| := by ring_nf
          _ ≤ |p 1 - x₀| + |-s| := abs_add_le _ _
          _ = |p 1 - x₀| + s := by rw [abs_neg, abs_of_nonneg hsq]
          _ < t₀ := by linarith
      apply waveTimeDeriv_zero_of_characteristic_values hu hsol (wavePoint (p 1) s)
      · simpa using (show waveRiemannPlus u (wavePoint (p 1 + s) 0) = 0 by
          dsimp [waveRiemannPlus]
          rw [hinit_t (p 1 + s) hfp.le,
            waveSpaceDeriv_initial_zero_of_local_zero hu hinit hfp]
          ring)
      · simpa using (show waveRiemannMinus u (wavePoint (p 1 - s) 0) = 0 by
          dsimp [waveRiemannMinus]
          rw [hinit_t (p 1 - s) hfm.le,
            waveSpaceDeriv_initial_zero_of_local_zero hu hinit hfm]
          ring)
    have hline : HasDerivAt (fun r : ℝ => u (wavePoint (p 1) r))
        (waveTimeDeriv u (wavePoint (p 1) s)) s := by
      have hp : HasDerivAt (fun r : ℝ => wavePoint (p 1) r)
          (timeDir 1) s := by
        simpa [wavePoint] using ((hasDerivAt_id s).smul_const (timeDir 1)).const_add
          ((p 1) • spaceDir 1 0)
      exact (hu.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
        |>.comp_hasDerivAt s hp
    exact (hline.congr_deriv hq).hasDerivWithinAt
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.Icc (0 : ℝ) (p 0)) (f := fun s : ℝ => u (wavePoint (p 1) s))
    (f' := fun _ => (0 : ℝ)) (C := 0) (x := 0) (y := p 0)
    hpath (fun s hs => by simp) (convex_Icc 0 (p 0))
    ⟨le_rfl, hp0⟩ ⟨hp0, le_rfl⟩
  have heq : u (wavePoint (p 1) (p 0)) = u (wavePoint (p 1) 0) := by
    have hnorm : ‖u (wavePoint (p 1) (p 0)) - u (wavePoint (p 1) 0)‖ = 0 :=
      le_antisymm (by simpa using hbound) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  rw [← wavePoint_coordinates p, heq, hinit (p 1) (by linarith)]

end EvansLib
