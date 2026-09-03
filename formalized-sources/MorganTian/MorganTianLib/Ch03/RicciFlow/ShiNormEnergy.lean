import MorganTianLib.Ch03.RicciFlow.EvolvingFrameCurvature
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.ODE.Gronwall

/-!
# Morgan--Tian Ch. 3 -- a moving-frame curvature norm square

The Shi estimates are written in terms of squared norms of iterated curvature
derivatives.  This file supplies the finite-dimensional moving-frame part of
that construction.  The geometric curvature evolution is intentionally kept
in `EvolvingCurvatureData`; the results below only use the honest derivative
and frame equations supplied by `EvolvingFrameCurvature`.
-/

open scoped BigOperators
open Set

noncomputable section

namespace MorganTianLib

/-! ## Components and their two derivative contributions -/

/-- **Math.** The four-slot curvature component obtained by inserting an evolving frame. -/
def evolvingFrameCurvatureComponent
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    (slot : Fin 4 → ι) (t : ℝ) : ℝ :=
  C.curvature t (fun i => F.frame t (slot i))

/-- **Math.** The intrinsic time derivative of a curvature component, before the frame
motion terms are added. -/
def evolvingFrameCurvatureIntrinsicComponent
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    (slot : Fin 4 → ι) (t : ℝ) : ℝ :=
  C.curvatureDeriv t (fun i => F.frame t (slot i))

/-- **Math.** The sum of the four terms caused by differentiating the moving frame. -/
def evolvingFrameCurvatureFrameComponent
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    (slot : Fin 4 → ι) (t : ℝ) : ℝ :=
  ∑ i : Fin 4,
    (C.curvature t).toContinuousLinearMap
      (fun j => F.frame t (slot j)) i
      (F.dualRicci t (F.frame t (slot i)))

/-- **Math.** The derivative of a moving-frame component is the intrinsic derivative plus
the four frame-motion terms. -/
theorem evolvingFrameCurvatureComponent_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    (slot : Fin 4 → ι) (t : ℝ) :
    HasDerivAt (fun s => evolvingFrameCurvatureComponent F C slot s)
      (evolvingFrameCurvatureIntrinsicComponent F C slot t +
        evolvingFrameCurvatureFrameComponent F C slot t) t := by
  simpa [evolvingFrameCurvatureComponent,
    evolvingFrameCurvatureIntrinsicComponent,
    evolvingFrameCurvatureFrameComponent] using
    (evolvingFrame_curvatureComponent_hasDerivAt F C slot t)

/-! ## Squares and the finite energy -/

/-- **Math.** The squared norm surrogate of one four-slot curvature component. -/
def evolvingFrameCurvatureComponentSq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    (slot : Fin 4 → ι) (t : ℝ) : ℝ :=
  (evolvingFrameCurvatureComponent F C slot t) ^ 2

/-- **Math.** The finite moving-frame sum of squared four-slot curvature components. -/
def evolvingFrameCurvatureEnergy
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    (t : ℝ) : ℝ :=
  ∑ slot : (Fin 4 → ι), evolvingFrameCurvatureComponentSq F C slot t

/-- **Math.** The squared intrinsic derivative energy. -/
def evolvingFrameCurvatureIntrinsicEnergy
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    (t : ℝ) : ℝ :=
  ∑ slot : (Fin 4 → ι),
    (evolvingFrameCurvatureIntrinsicComponent F C slot t) ^ 2

/-- **Math.** The squared frame-motion correction energy. -/
def evolvingFrameCurvatureFrameEnergy
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    (t : ℝ) : ℝ :=
  ∑ slot : (Fin 4 → ι),
    (evolvingFrameCurvatureFrameComponent F C slot t) ^ 2

theorem evolvingFrameCurvatureComponentSq_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    (slot : Fin 4 → ι) (t : ℝ) :
    HasDerivAt (fun s => evolvingFrameCurvatureComponentSq F C slot s)
      (2 * evolvingFrameCurvatureComponent F C slot t *
        (evolvingFrameCurvatureIntrinsicComponent F C slot t +
          evolvingFrameCurvatureFrameComponent F C slot t)) t := by
  unfold evolvingFrameCurvatureComponentSq
  have h := evolvingFrameCurvatureComponent_hasDerivAt F C slot t
  have hsq := h.mul h
  have heq :
      (fun s => evolvingFrameCurvatureComponent F C slot s *
        evolvingFrameCurvatureComponent F C slot s) =
        (fun s => (evolvingFrameCurvatureComponent F C slot s) ^ 2) := by
    funext s
    ring
  have hd :
      (evolvingFrameCurvatureIntrinsicComponent F C slot t +
          evolvingFrameCurvatureFrameComponent F C slot t) *
        evolvingFrameCurvatureComponent F C slot t +
        evolvingFrameCurvatureComponent F C slot t *
          (evolvingFrameCurvatureIntrinsicComponent F C slot t +
            evolvingFrameCurvatureFrameComponent F C slot t) =
      2 * evolvingFrameCurvatureComponent F C slot t *
        (evolvingFrameCurvatureIntrinsicComponent F C slot t +
          evolvingFrameCurvatureFrameComponent F C slot t) := by
    ring
  rw [← heq, ← hd]
  exact hsq

theorem evolvingFrameCurvatureEnergy_nonneg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    (t : ℝ) : 0 ≤ evolvingFrameCurvatureEnergy F C t := by
  classical
  unfold evolvingFrameCurvatureEnergy
  exact Finset.sum_nonneg fun slot _ => sq_nonneg _

theorem evolvingFrameCurvatureEnergy_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    (t : ℝ) :
    HasDerivAt (fun s => evolvingFrameCurvatureEnergy F C s)
      (∑ slot : (Fin 4 → ι),
        2 * evolvingFrameCurvatureComponent F C slot t *
          (evolvingFrameCurvatureIntrinsicComponent F C slot t +
            evolvingFrameCurvatureFrameComponent F C slot t)) t := by
  classical
  have hsum := HasDerivAt.fun_sum
    (fun slot (_ : slot ∈ (Finset.univ : Finset (Fin 4 → ι))) =>
      evolvingFrameCurvatureComponentSq_hasDerivAt F C slot t)
  simpa [evolvingFrameCurvatureEnergy] using hsum

/-! ## A finite Cauchy/Young estimate -/

private theorem sq_add_le_two_sq_add_two_sq (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **Math.** Young's inequality controls the energy derivative by the component energy
and the two derivative energies.  The intrinsic and frame terms are kept
separate, so a geometric estimate for either one can be inserted later. -/
theorem evolvingFrameCurvatureEnergy_abs_deriv_le_young
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    {t ε : ℝ} (hε : 0 < ε) :
    |∑ slot : (Fin 4 → ι),
        2 * evolvingFrameCurvatureComponent F C slot t *
          (evolvingFrameCurvatureIntrinsicComponent F C slot t +
            evolvingFrameCurvatureFrameComponent F C slot t)| ≤
      ε * evolvingFrameCurvatureEnergy F C t +
        (2 * ε⁻¹) *
          (evolvingFrameCurvatureIntrinsicEnergy F C t +
            evolvingFrameCurvatureFrameEnergy F C t) := by
  classical
  let r : (Fin 4 → ι) → ℝ :=
    fun slot => evolvingFrameCurvatureComponent F C slot t
  let a : (Fin 4 → ι) → ℝ :=
    fun slot => evolvingFrameCurvatureIntrinsicComponent F C slot t
  let m : (Fin 4 → ι) → ℝ :=
    fun slot => evolvingFrameCurvatureFrameComponent F C slot t
  have hterm (slot : Fin 4 → ι) :
      |2 * r slot * (a slot + m slot)| ≤
        ε * (r slot) ^ 2 + ε⁻¹ * (a slot + m slot) ^ 2 := by
    have hY := two_mul_le_add_mul_sq (a := |r slot|)
      (b := |a slot + m slot|) hε
    have hsq := sq_add_le_two_sq_add_two_sq (a slot) (m slot)
    have hinv : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
    have hsq' := mul_le_mul_of_nonneg_left hsq hinv
    rw [abs_mul, abs_mul]
    simpa [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), pow_two,
      mul_assoc, mul_left_comm, mul_comm] using hY
  have hsum :
      |∑ slot : (Fin 4 → ι), 2 * r slot * (a slot + m slot)| ≤
        ∑ slot : (Fin 4 → ι),
          (ε * (r slot) ^ 2 + ε⁻¹ * (a slot + m slot) ^ 2) := by
    calc
      |∑ slot : (Fin 4 → ι), 2 * r slot * (a slot + m slot)| ≤
          ∑ slot : (Fin 4 → ι), |2 * r slot * (a slot + m slot)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ slot : (Fin 4 → ι),
          (ε * (r slot) ^ 2 + ε⁻¹ * (a slot + m slot) ^ 2) :=
        Finset.sum_le_sum fun slot _ => hterm slot
  have hsum_sq :
      (∑ slot : (Fin 4 → ι), (a slot + m slot) ^ 2) ≤
        2 * (∑ slot : (Fin 4 → ι), (a slot) ^ 2) +
          2 * (∑ slot : (Fin 4 → ι), (m slot) ^ 2) := by
    calc
      (∑ slot : (Fin 4 → ι), (a slot + m slot) ^ 2) ≤
          ∑ slot : (Fin 4 → ι), (2 * (a slot) ^ 2 + 2 * (m slot) ^ 2) :=
        Finset.sum_le_sum fun slot _ => sq_add_le_two_sq_add_two_sq (a slot) (m slot)
      _ = 2 * (∑ slot : (Fin 4 → ι), (a slot) ^ 2) +
          2 * (∑ slot : (Fin 4 → ι), (m slot) ^ 2) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.mul_sum]
  have hweighted :
      ε⁻¹ * (∑ slot : (Fin 4 → ι), (a slot + m slot) ^ 2) ≤
        ε⁻¹ *
          (2 * (∑ slot : (Fin 4 → ι), (a slot) ^ 2) +
            2 * (∑ slot : (Fin 4 → ι), (m slot) ^ 2)) :=
    mul_le_mul_of_nonneg_left hsum_sq (inv_nonneg.mpr hε.le)
  have hfinal :
      |∑ slot : (Fin 4 → ι), 2 * r slot * (a slot + m slot)| ≤
        ε * (∑ slot : (Fin 4 → ι), (r slot) ^ 2) +
          ε⁻¹ * (2 * (∑ slot : (Fin 4 → ι), (a slot) ^ 2) +
            2 * (∑ slot : (Fin 4 → ι), (m slot) ^ 2)) := by
    calc
      |∑ slot : (Fin 4 → ι), 2 * r slot * (a slot + m slot)| ≤
          ∑ slot : (Fin 4 → ι),
            (ε * (r slot) ^ 2 + ε⁻¹ * (a slot + m slot) ^ 2) := hsum
      _ = ε * (∑ slot : (Fin 4 → ι), (r slot) ^ 2) +
          ε⁻¹ * (∑ slot : (Fin 4 → ι), (a slot + m slot) ^ 2) := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.mul_sum]
      _ ≤ ε * (∑ slot : (Fin 4 → ι), (r slot) ^ 2) +
          ε⁻¹ * (2 * (∑ slot : (Fin 4 → ι), (a slot) ^ 2) +
            2 * (∑ slot : (Fin 4 → ι), (m slot) ^ 2)) := by
        exact add_le_add_right hweighted _
  simpa [r, a, m, evolvingFrameCurvatureEnergy,
    evolvingFrameCurvatureIntrinsicEnergy, evolvingFrameCurvatureFrameEnergy,
    evolvingFrameCurvatureComponentSq, mul_add, add_mul, mul_assoc,
    mul_left_comm, mul_comm] using hfinal

/-! ## A one-sided energy differential inequality -/

/-- **Math.** Intrinsic and frame energy bounds turn the finite moving-frame
energy identity into a one-sided differential inequality. -/
theorem evolvingFrameCurvatureEnergy_deriv_le_of_intrinsic_frame_bounds
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    {t ε A B : ℝ} (hε : 0 < ε)
    (hA : evolvingFrameCurvatureIntrinsicEnergy F C t ≤ A)
    (hB : evolvingFrameCurvatureFrameEnergy F C t ≤ B) :
    deriv (fun s => evolvingFrameCurvatureEnergy F C s) t ≤
      ε * evolvingFrameCurvatureEnergy F C t +
        (2 * ε⁻¹) * (A + B) := by
  have hderiv := (evolvingFrameCurvatureEnergy_hasDerivAt F C t).deriv
  have hyoung := evolvingFrameCurvatureEnergy_abs_deriv_le_young
    (t := t) F C hε
  have hnonneg : 0 ≤ 2 * ε⁻¹ := by
    positivity
  have hsum : evolvingFrameCurvatureIntrinsicEnergy F C t +
      evolvingFrameCurvatureFrameEnergy F C t ≤ A + B :=
    add_le_add hA hB
  have hmul := mul_le_mul_of_nonneg_left hsum hnonneg
  rw [hderiv]
  calc
    (∑ slot : (Fin 4 → ι),
        2 * evolvingFrameCurvatureComponent F C slot t *
          (evolvingFrameCurvatureIntrinsicComponent F C slot t +
            evolvingFrameCurvatureFrameComponent F C slot t)) ≤
        |∑ slot : (Fin 4 → ι),
          2 * evolvingFrameCurvatureComponent F C slot t *
            (evolvingFrameCurvatureIntrinsicComponent F C slot t +
              evolvingFrameCurvatureFrameComponent F C slot t)| :=
      le_abs_self _
    _ ≤ ε * evolvingFrameCurvatureEnergy F C t +
        (2 * ε⁻¹) *
          (evolvingFrameCurvatureIntrinsicEnergy F C t +
            evolvingFrameCurvatureFrameEnergy F C t) := hyoung
    _ ≤ ε * evolvingFrameCurvatureEnergy F C t +
        (2 * ε⁻¹) * (A + B) := by
      nlinarith

/-! The pointwise differential estimate becomes a finite-time bound once the
intrinsic and frame energies are controlled uniformly on the interval. -/

/-- **Math.** Uniform intrinsic and frame-energy bounds give an explicit
Grönwall bound for the moving-frame curvature energy.  The continuity and
uniform bounds are exposed as hypotheses so that this theorem can be consumed
by a geometric Shi evolution argument without hiding its analytic input. -/
theorem evolvingFrameCurvatureEnergy_le_gronwall_of_uniform_bounds
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    {a b ε A B E₀ : ℝ}
    (hcont : ContinuousOn (fun s => evolvingFrameCurvatureEnergy F C s)
      (Icc a b))
    (hinit : evolvingFrameCurvatureEnergy F C a ≤ E₀)
    (hA : ∀ s ∈ Ico a b,
      evolvingFrameCurvatureIntrinsicEnergy F C s ≤ A)
    (hB : ∀ s ∈ Ico a b,
      evolvingFrameCurvatureFrameEnergy F C s ≤ B)
    (hε : 0 < ε) :
    ∀ t ∈ Icc a b,
      evolvingFrameCurvatureEnergy F C t ≤
        gronwallBound E₀ ε (2 * ε⁻¹ * (A + B)) (t - a) := by
  have hderiv : ∀ s ∈ Ico a b,
      HasDerivWithinAt
        (fun u => evolvingFrameCurvatureEnergy F C u)
        (∑ slot : (Fin 4 → ι),
          2 * evolvingFrameCurvatureComponent F C slot s *
            (evolvingFrameCurvatureIntrinsicComponent F C slot s +
              evolvingFrameCurvatureFrameComponent F C slot s))
        (Ici s) s := by
    intro s hs
    simpa using (evolvingFrameCurvatureEnergy_hasDerivAt F C s).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico a b,
      ‖(∑ slot : (Fin 4 → ι),
          2 * evolvingFrameCurvatureComponent F C slot s *
            (evolvingFrameCurvatureIntrinsicComponent F C slot s +
              evolvingFrameCurvatureFrameComponent F C slot s))‖ ≤
        ε * ‖evolvingFrameCurvatureEnergy F C s‖ +
          (2 * ε⁻¹ * (A + B)) := by
    intro s hs
    have hy := evolvingFrameCurvatureEnergy_abs_deriv_le_young
      (t := s) F C hε
    have hsum :
        evolvingFrameCurvatureIntrinsicEnergy F C s +
            evolvingFrameCurvatureFrameEnergy F C s ≤ A + B :=
      add_le_add (hA s hs) (hB s hs)
    have hcoef : 0 ≤ 2 * ε⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsum hcoef
    have hfinal :
        |∑ slot : (Fin 4 → ι),
            2 * evolvingFrameCurvatureComponent F C slot s *
              (evolvingFrameCurvatureIntrinsicComponent F C slot s +
                evolvingFrameCurvatureFrameComponent F C slot s)| ≤
          ε * evolvingFrameCurvatureEnergy F C s +
            (2 * ε⁻¹ * (A + B)) := by
      calc
        |∑ slot : (Fin 4 → ι),
            2 * evolvingFrameCurvatureComponent F C slot s *
              (evolvingFrameCurvatureIntrinsicComponent F C slot s +
                evolvingFrameCurvatureFrameComponent F C slot s)| ≤
            ε * evolvingFrameCurvatureEnergy F C s +
              (2 * ε⁻¹) *
                (evolvingFrameCurvatureIntrinsicEnergy F C s +
                  evolvingFrameCurvatureFrameEnergy F C s) := hy
        _ ≤ ε * evolvingFrameCurvatureEnergy F C s +
              (2 * ε⁻¹) * (A + B) := by
          calc
            ε * evolvingFrameCurvatureEnergy F C s +
                (2 * ε⁻¹) *
                  (evolvingFrameCurvatureIntrinsicEnergy F C s +
                    evolvingFrameCurvatureFrameEnergy F C s) =
              (2 * ε⁻¹) *
                  (evolvingFrameCurvatureIntrinsicEnergy F C s +
                    evolvingFrameCurvatureFrameEnergy F C s) +
                ε * evolvingFrameCurvatureEnergy F C s := by ring
            _ ≤ (2 * ε⁻¹) * (A + B) +
                ε * evolvingFrameCurvatureEnergy F C s := by
              simpa [add_comm] using
                (add_le_add_left hmul
                  (ε * evolvingFrameCurvatureEnergy F C s))
            _ = ε * evolvingFrameCurvatureEnergy F C s +
                (2 * ε⁻¹) * (A + B) := by ring
        _ = ε * evolvingFrameCurvatureEnergy F C s +
              (2 * ε⁻¹ * (A + B)) := by ring
    have henergy_nonneg := evolvingFrameCurvatureEnergy_nonneg F C s
    simpa only [Real.norm_eq_abs, abs_of_nonneg henergy_nonneg] using hfinal
  intro t ht
  have henergy_nonneg := evolvingFrameCurvatureEnergy_nonneg F C a
  have hinitial_norm :
      ‖evolvingFrameCurvatureEnergy F C a‖ ≤ E₀ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg henergy_nonneg] using hinit
  have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun s => evolvingFrameCurvatureEnergy F C s)
    (f' := fun s =>
      ∑ slot : (Fin 4 → ι),
        2 * evolvingFrameCurvatureComponent F C slot s *
          (evolvingFrameCurvatureIntrinsicComponent F C slot s +
            evolvingFrameCurvatureFrameComponent F C slot s))
    (δ := E₀) (K := ε) (ε := 2 * ε⁻¹ * (A + B))
    hcont hderiv hinitial_norm hbound t ht
  calc
    evolvingFrameCurvatureEnergy F C t ≤
        ‖evolvingFrameCurvatureEnergy F C t‖ := by
      simpa only [Real.norm_eq_abs] using
        (le_abs_self (evolvingFrameCurvatureEnergy F C t))
    _ ≤ gronwallBound E₀ ε (2 * ε⁻¹ * (A + B)) (t - a) := hgronwall

end MorganTianLib

end
