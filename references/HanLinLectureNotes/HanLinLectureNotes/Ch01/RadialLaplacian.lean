import HanLinLectureNotes.Ch01.WeakGreen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Radial Laplacian identities for Han--Lin Chapter 1

This module reduces the Laplacian of a squared-radial function to its
one-dimensional profile. It is the coordinate calculation used by the native
harmonic mean-value proof.
-/

open scoped Real ContDiff
open MeasureTheory

noncomputable section

namespace HanLinLectureNotes.Ch01

/-- Norm expansion along a coordinate line. -/
lemma norm_add_smul_single_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (j : Fin n) (s : ℝ) :
    ‖x + s • EuclideanSpace.single j (1 : ℝ)‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * s * x j + s ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hco : ∀ i, (x + s • EuclideanSpace.single j (1 : ℝ)).ofLp i =
      x.ofLp i + s * (if i = j then 1 else 0) := by
    intro i
    simp [PiLp.single_apply]
  simp_rw [hco]
  have expand : ∀ i, (x.ofLp i + s * (if i = j then (1 : ℝ) else 0)) ^ 2 =
      (x.ofLp i) ^ 2 + 2 * s * (if i = j then x.ofLp i else 0) +
        s ^ 2 * (if i = j then 1 else 0) := by
    intro i
    by_cases h : i = j
    · subst h
      simp
      ring
    · simp [h]
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ j (fun i => x.ofLp i),
    Finset.sum_ite_eq' Finset.univ j (fun _ => (1 : ℝ))]
  simp

/-- If `f` is smooth on an open neighborhood of `x`, its pure second partial
at `x` is the second derivative of the corresponding coordinate line. -/
lemma partialDeriv_iterate_two_of_isOpen {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ∀ y ∈ U, ContDiffAt ℝ ∞ f y)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (j : Fin n) :
    (partialDeriv j)^[2] f x =
      iteratedDeriv 2
        (fun s : ℝ => f (x + s • EuclideanSpace.single j (1 : ℝ))) 0 := by
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (1 : ℝ) with he
  have hlineCont : Continuous (fun s : ℝ => x + s • e) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hlineDeriv : ∀ s : ℝ, HasDerivAt (fun t : ℝ => x + t • e) e s :=
    fun s => by
      simpa using ((hasDerivAt_id s).smul_const e).const_add x
  have hW : IsOpen ((fun s : ℝ => x + s • e) ⁻¹' U) := hU.preimage hlineCont
  have hmem0 : (0 : ℝ) ∈ (fun s : ℝ => x + s • e) ⁻¹' U := by
    simpa using hx
  have hderivEq : deriv (fun s : ℝ => f (x + s • e)) =ᶠ[nhds 0]
      fun s : ℝ => partialDeriv j f (x + s • e) := by
    filter_upwards [hW.mem_nhds hmem0] with s hs
    have hfat : ContDiffAt ℝ ∞ f (x + s • e) := hf _ hs
    have hd : HasDerivAt (fun t : ℝ => f (x + t • e))
        (fderiv ℝ f (x + s • e) e) s :=
      (hfat.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
        (hlineDeriv s)
    rw [hd.deriv, partialDeriv_apply]
  have hpjDiff : DifferentiableAt ℝ (partialDeriv j f) x := by
    have hfd : ContDiffAt ℝ ∞ (fderiv ℝ f) x :=
      (hf x hx).fderiv_right (by simp)
    exact (hfd.differentiableAt (by simp)).clm_apply (differentiableAt_const e)
  have hfin : HasDerivAt (fun s : ℝ => partialDeriv j f (x + s • e))
      (fderiv ℝ (partialDeriv j f) x e) 0 := by
    have hfd0 : HasFDerivAt (partialDeriv j f) (fderiv ℝ (partialDeriv j f) x)
        (x + (0 : ℝ) • e) := by
      rw [zero_smul, add_zero]
      exact hpjDiff.hasFDerivAt
    simpa only [Function.comp_def] using hfd0.comp_hasDerivAt 0 (hlineDeriv 0)
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderivEq.deriv_eq, hfin.deriv,
    Function.iterate_succ_apply', Function.iterate_one, partialDeriv_apply, he]

/-- The second derivative at zero of a profile composed with a quadratic. -/
lemma iteratedDeriv_two_comp_quadratic {g g' g'' : ℝ → ℝ} {A b : ℝ}
    (hA : 0 < A) (hg : ∀ rho, 0 < rho → HasDerivAt g (g' rho) rho)
    (hg' : ∀ rho, 0 < rho → HasDerivAt g' (g'' rho) rho) :
    iteratedDeriv 2 (fun s : ℝ => g (A + 2 * s * b + s ^ 2)) 0 =
      4 * b ^ 2 * g'' A + 2 * g' A := by
  set q : ℝ → ℝ := fun s => A + 2 * s * b + s ^ 2 with hq
  show iteratedDeriv 2 (fun s : ℝ => g (q s)) 0 =
    4 * b ^ 2 * g'' A + 2 * g' A
  have hqderiv : ∀ s : ℝ, HasDerivAt q (2 * b + 2 * s) s := by
    intro s
    have e1 : HasDerivAt (fun t : ℝ => 2 * t * b) (2 * b) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 : ℝ)).mul_const b
    have e2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    convert ((hasDerivAt_const s A).add e1).add e2 using 1
    · exact AddCommGroup.ext rfl
    · exact Module.ext rfl
    · rfl
    · ring
  have hq0 : q 0 = A := by simp [hq]
  have hqcont : Continuous q := by
    rw [hq]
    fun_prop
  have hWpos : IsOpen {s : ℝ | 0 < q s} := isOpen_lt continuous_const hqcont
  have hmem0 : (0 : ℝ) ∈ {s : ℝ | 0 < q s} := by
    rw [Set.mem_setOf_eq, hq0]
    exact hA
  have hderiv1 : deriv (fun s : ℝ => g (q s)) =ᶠ[nhds 0]
      fun s : ℝ => g' (q s) * (2 * b + 2 * s) := by
    filter_upwards [hWpos.mem_nhds hmem0] with s hs
    have hcomp : HasDerivAt (fun t : ℝ => g (q t))
        (g' (q s) * (2 * b + 2 * s)) s := by
      simpa only [Function.comp_def] using (hg (q s) hs).comp s (hqderiv s)
    rw [hcomp.deriv]
  have hcompo : HasDerivAt (fun s : ℝ => g' (q s))
      (g'' (q 0) * (2 * b + 2 * 0)) 0 := by
    simpa only [Function.comp_def] using
      (hg' (q 0) (by rw [hq0]; exact hA)).comp 0 (hqderiv 0)
  have hlin : HasDerivAt (fun s : ℝ => 2 * b + 2 * s) 2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).const_add (2 * b)
  have hprod : HasDerivAt
      (fun s : ℝ => g' (q s) * (2 * b + 2 * s))
      (g'' (q 0) * (2 * b + 2 * 0) * (2 * b + 2 * 0) + g' (q 0) * 2) 0 :=
    hcompo.mul hlin
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv1.deriv_eq, hprod.deriv, hq0]
  ring

/-- The Laplacian of `g (‖x‖^2)` away from the origin is
`4 ‖x‖^2 g'' (‖x‖^2) + 2 n g' (‖x‖^2)`. -/
lemma sum_partialDeriv_two_comp_normSq {n : ℕ} {g g' g'' : ℝ → ℝ}
    (hg : ∀ rho, 0 < rho → HasDerivAt g (g' rho) rho)
    (hg' : ∀ rho, 0 < rho → HasDerivAt g' (g'' rho) rho)
    (hgS : ∀ rho, 0 < rho → ContDiffAt ℝ ∞ g rho)
    {Phi : EuclideanSpace ℝ (Fin n) → ℝ}
    (hPhi : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → Phi z = g (‖z‖ ^ 2))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ∑ j, (partialDeriv j)^[2] Phi x =
      4 * ‖x‖ ^ 2 * g'' (‖x‖ ^ 2) + 2 * n * g' (‖x‖ ^ 2) := by
  have hUopen : IsOpen {z : EuclideanSpace ℝ (Fin n) | z ≠ 0} := isOpen_ne
  have hPhiSmooth : ∀ y ∈ {z : EuclideanSpace ℝ (Fin n) | z ≠ 0},
      ContDiffAt ℝ ∞ Phi y := by
    intro y hy
    have hnpos : (0 : ℝ) < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy) 2
    have hcomp : ContDiffAt ℝ ∞
        (fun z : EuclideanSpace ℝ (Fin n) => g (‖z‖ ^ 2)) y :=
      (hgS _ hnpos).comp y (contDiff_norm_sq ℝ).contDiffAt
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hUopen.mem_nhds hy] with z hz using hPhi z hz
  have hpart : ∀ j : Fin n, (partialDeriv j)^[2] Phi x =
      4 * (x j) ^ 2 * g'' (‖x‖ ^ 2) + 2 * g' (‖x‖ ^ 2) := by
    intro j
    rw [partialDeriv_iterate_two_of_isOpen hUopen hPhiSmooth hx j]
    have hline : (fun s : ℝ => Phi
        (x + s • EuclideanSpace.single j (1 : ℝ))) =ᶠ[nhds 0]
        fun s : ℝ => g (‖x‖ ^ 2 + 2 * s * (x j) + s ^ 2) := by
      have hcont : Continuous
          (fun s : ℝ => x + s • EuclideanSpace.single j (1 : ℝ)) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hmem : {s : ℝ |
          x + s • EuclideanSpace.single j (1 : ℝ) ≠ 0} ∈ nhds (0 : ℝ) := by
        apply (hUopen.preimage hcont).mem_nhds
        simpa using hx
      filter_upwards [hmem] with s hs
      rw [hPhi _ hs, norm_add_smul_single_sq]
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hline,
      iteratedDeriv_two_comp_quadratic
        (pow_pos (norm_pos_iff.mpr hx) 2) hg hg']
  have hnorm : ∑ j : Fin n, (x j) ^ 2 = ‖x‖ ^ 2 :=
    (EuclideanSpace.real_norm_sq_eq x).symm
  calc
    ∑ j, (partialDeriv j)^[2] Phi x =
        ∑ j : Fin n,
          (4 * (x j) ^ 2 * g'' (‖x‖ ^ 2) + 2 * g' (‖x‖ ^ 2)) :=
      Finset.sum_congr rfl (fun j _ => hpart j)
    _ = (∑ j : Fin n, 4 * (x j) ^ 2 * g'' (‖x‖ ^ 2)) +
        ∑ _j : Fin n, 2 * g' (‖x‖ ^ 2) := Finset.sum_add_distrib
    _ = 4 * g'' (‖x‖ ^ 2) * (∑ j : Fin n, (x j) ^ 2) +
        (n : ℝ) * (2 * g' (‖x‖ ^ 2)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = 4 * ‖x‖ ^ 2 * g'' (‖x‖ ^ 2) + 2 * n * g' (‖x‖ ^ 2) := by
      rw [hnorm]
      ring

end HanLinLectureNotes.Ch01
