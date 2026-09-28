import Topping.ParabolicPDE.SectionNemytskii

/-!
# Variable-coefficient section-space jet maps

On a compact base, continuous coefficient fields can be evaluated on bounded
continuous value and jet sections without adding a separate boundedness
certificate.  This is the compact-base variable-coefficient boundary needed
before a genuine chartwise DeTurck section map can be assembled.
-/

namespace Topping

open scoped BoundedContinuousFunction BigOperators

noncomputable section

variable {T ι V : Type*} [Fintype ι] [TopologicalSpace T]
  [CompactSpace T] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace VectorSecondOrderCoefficients

variable (A : VectorSecondOrderCoefficients T ι V)

/-! A continuous coefficient field becomes a bounded section on a compact base. -/

def boundedCoefficient
    (f : T → (V →L[ℝ] V)) (hf : Continuous f) :
    T →ᵇ (V →L[ℝ] V) :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := f
      continuous_toFun := hf }

@[simp] theorem boundedCoefficient_apply
    (f : T → (V →L[ℝ] V)) (hf : Continuous f) (t : T) :
    boundedCoefficient f hf t = f t := rfl

def aSection
    (ha : ∀ i k, Continuous (fun t => A.a t i k)) (i k : ι) :
    T →ᵇ (V →L[ℝ] V) :=
  boundedCoefficient (fun t => A.a t i k) (ha i k)

def bSection
    (hb : ∀ i, Continuous (fun t => A.b t i)) (i : ι) :
    T →ᵇ (V →L[ℝ] V) :=
  boundedCoefficient (fun t => A.b t i) (hb i)

def cSection
    (hc : Continuous (fun t => A.c t)) : T →ᵇ (V →L[ℝ] V) :=
  boundedCoefficient (fun t => A.c t) hc

@[simp] theorem aSection_apply
    (ha : ∀ i k, Continuous (fun t => A.a t i k)) (i k : ι) (t : T) :
    A.aSection ha i k t = A.a t i k := rfl

@[simp] theorem bSection_apply
    (hb : ∀ i, Continuous (fun t => A.b t i)) (i : ι) (t : T) :
    A.bSection hb i t = A.b t i := rfl

@[simp] theorem cSection_apply
    (hc : Continuous (fun t => A.c t)) (t : T) :
    A.cSection hc t = A.c t := rfl

/-! The coefficient fields are supplied as continuous maps on the compact
base.  No continuity in the fibre variable is needed beyond continuity of a
continuous linear map. -/

def variableSectionApplyJetArgs
    (ha : ∀ i k, Continuous (fun t => A.a t i k))
    (hb : ∀ i, Continuous (fun t => A.b t i))
    (hc : Continuous (fun t => A.c t))
    (value : T →ᵇ V) (first : ι → T →ᵇ V)
    (second : ι → ι → T →ᵇ V) : T →ᵇ V := by
  let f : C(T, V) :=
    { toFun := fun t =>
        (∑ i, ∑ k, A.a t i k (second i k t)) +
          (∑ i, A.b t i (first i t)) + A.c t (value t)
      continuous_toFun := by
        have hA : ∀ i k, Continuous (fun t => A.a t i k (second i k t)) := by
          intro i k
          exact (ha i k).clm_apply (BoundedContinuousFunction.continuous _)
        have hB : ∀ i, Continuous (fun t => A.b t i (first i t)) := by
          intro i
          exact (hb i).clm_apply (BoundedContinuousFunction.continuous _)
        have hAsum : Continuous (fun t => ∑ i, ∑ k,
            A.a t i k (second i k t)) := by
          apply continuous_finsetSum
          intro i hi
          apply continuous_finsetSum
          intro k hk
          exact hA i k
        have hBsum : Continuous (fun t => ∑ i,
            A.b t i (first i t)) := by
          apply continuous_finsetSum
          intro i hi
          exact hB i
        have hC : Continuous (fun t => A.c t (value t)) :=
          hc.clm_apply (BoundedContinuousFunction.continuous _)
        exact (hAsum.add hBsum).add hC }
  exact BoundedContinuousFunction.mkOfCompact f

@[simp] theorem variableSectionApplyJetArgs_apply
    (ha : ∀ i k, Continuous (fun t => A.a t i k))
    (hb : ∀ i, Continuous (fun t => A.b t i))
    (hc : Continuous (fun t => A.c t))
    (value : T →ᵇ V) (first : ι → T →ᵇ V)
    (second : ι → ι → T →ᵇ V) (t : T) :
    A.variableSectionApplyJetArgs ha hb hc value first second t =
      (∑ i, ∑ k, A.a t i k (second i k t)) +
        (∑ i, A.b t i (first i t)) + A.c t (value t) := by
  simp [variableSectionApplyJetArgs]

theorem variableSectionApplyJetArgs_eq_pointwise
    (ha : ∀ i k, Continuous (fun t => A.a t i k))
    (hb : ∀ i, Continuous (fun t => A.b t i))
    (hc : Continuous (fun t => A.c t))
    (value : T →ᵇ V) (first : ι → T →ᵇ V)
    (second : ι → ι → T →ᵇ V) (t : T) :
    A.variableSectionApplyJetArgs ha hb hc value first second t =
      A.applyJetArgs t (value t) (fun i => first i t)
        (fun i k => second i k t) := by
  rw [variableSectionApplyJetArgs_apply]
  rfl

/-! A coefficient-weighted pointwise estimate for the variable section map. -/
theorem variableSectionApplyJetArgs_apply_norm_le
    (ha : ∀ i k, Continuous (fun t => A.a t i k))
    (hb : ∀ i, Continuous (fun t => A.b t i))
    (hc : Continuous (fun t => A.c t))
    (value : T →ᵇ V) (first : ι → T →ᵇ V)
    (second : ι → ι → T →ᵇ V) (t : T) :
    ‖A.variableSectionApplyJetArgs ha hb hc value first second t‖ ≤
      (∑ i, ∑ k, ‖A.a t i k‖ * ‖second i k‖) +
        (∑ i, ‖A.b t i‖ * ‖first i‖) + ‖A.c t‖ * ‖value‖ := by
  have hA (i k : ι) :
      ‖A.a t i k (second i k t)‖ ≤ ‖A.a t i k‖ * ‖second i k‖ := by
    exact (A.a t i k).le_opNorm_of_le ((second i k).norm_coe_le_norm t)
  have hB (i : ι) :
      ‖A.b t i (first i t)‖ ≤ ‖A.b t i‖ * ‖first i‖ := by
    exact (A.b t i).le_opNorm_of_le ((first i).norm_coe_le_norm t)
  have hA_sum :
      ‖∑ i, ∑ k, A.a t i k (second i k t)‖ ≤
        ∑ i, ∑ k, ‖A.a t i k‖ * ‖second i k‖ := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => hA i k))
  have hB_sum :
      ‖∑ i, A.b t i (first i t)‖ ≤ ∑ i, ‖A.b t i‖ * ‖first i‖ := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum (fun i hi => hB i)
  have hC_point :
      ‖A.c t (value t)‖ ≤ ‖A.c t‖ * ‖value‖ := by
    exact (A.c t).le_opNorm_of_le (value.norm_coe_le_norm t)
  rw [variableSectionApplyJetArgs_apply]
  calc
    ‖(∑ i, ∑ k, A.a t i k (second i k t)) +
          (∑ i, A.b t i (first i t)) + A.c t (value t)‖
        ≤ ‖∑ i, ∑ k, A.a t i k (second i k t)‖ +
            ‖∑ i, A.b t i (first i t)‖ + ‖A.c t (value t)‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add_left (norm_add_le _ _) _)
    _ ≤ (∑ i, ∑ k, ‖A.a t i k‖ * ‖second i k‖) +
          (∑ i, ‖A.b t i‖ * ‖first i‖) + ‖A.c t (value t)‖ := by
          exact add_le_add (add_le_add hA_sum hB_sum) le_rfl
    _ ≤ (∑ i, ∑ k, ‖A.a t i k‖ * ‖second i k‖) +
          (∑ i, ‖A.b t i‖ * ‖first i‖) + ‖A.c t‖ * ‖value‖ := by
          exact add_le_add (add_le_add le_rfl le_rfl) hC_point

/-! The same pointwise estimate with two coefficient fields.  This is the
coefficient perturbation term used in the joint section-space bound below. -/
theorem variableSectionApplyJetArgs_coeff_sub_apply_norm_le
    (A B : VectorSecondOrderCoefficients T ι V)
    (haA : ∀ i k, Continuous (fun t => A.a t i k))
    (haB : ∀ i k, Continuous (fun t => B.a t i k))
    (hbA : ∀ i, Continuous (fun t => A.b t i))
    (hbB : ∀ i, Continuous (fun t => B.b t i))
    (hcA : Continuous (fun t => A.c t))
    (hcB : Continuous (fun t => B.c t))
    (value : T →ᵇ V) (first : ι → T →ᵇ V)
    (second : ι → ι → T →ᵇ V) (t : T) :
    ‖A.variableSectionApplyJetArgs haA hbA hcA value first second t -
        B.variableSectionApplyJetArgs haB hbB hcB value first second t‖ ≤
      (∑ i, ∑ k, ‖A.a t i k - B.a t i k‖ * ‖second i k‖) +
        (∑ i, ‖A.b t i - B.b t i‖ * ‖first i‖) +
          ‖A.c t - B.c t‖ * ‖value‖ := by
  have hA (i k : ι) :
      ‖A.a t i k (second i k t) - B.a t i k (second i k t)‖ ≤
        ‖A.a t i k - B.a t i k‖ * ‖second i k‖ := by
    change ‖(A.a t i k - B.a t i k) (second i k t)‖ ≤ _
    exact (A.a t i k - B.a t i k).le_opNorm_of_le
      ((second i k).norm_coe_le_norm t)
  have hB (i : ι) :
      ‖A.b t i (first i t) - B.b t i (first i t)‖ ≤
        ‖A.b t i - B.b t i‖ * ‖first i‖ := by
    change ‖(A.b t i - B.b t i) (first i t)‖ ≤ _
    exact (A.b t i - B.b t i).le_opNorm_of_le
      ((first i).norm_coe_le_norm t)
  have hC :
      ‖A.c t (value t) - B.c t (value t)‖ ≤
        ‖A.c t - B.c t‖ * ‖value‖ := by
    change ‖(A.c t - B.c t) (value t)‖ ≤ _
    exact (A.c t - B.c t).le_opNorm_of_le (value.norm_coe_le_norm t)
  have hA_sum :
      ‖(∑ i, ∑ k, A.a t i k (second i k t)) -
          (∑ i, ∑ k, B.a t i k (second i k t))‖ ≤
        ∑ i, ∑ k, ‖A.a t i k - B.a t i k‖ * ‖second i k‖ := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => hA i k))
  have hB_sum :
      ‖(∑ i, A.b t i (first i t)) -
          (∑ i, B.b t i (first i t))‖ ≤
        ∑ i, ‖A.b t i - B.b t i‖ * ‖first i‖ := by
    rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => hB i))
  rw [variableSectionApplyJetArgs_apply, variableSectionApplyJetArgs_apply]
  calc
    ‖((∑ i, ∑ k, A.a t i k (second i k t)) +
          (∑ i, A.b t i (first i t)) + A.c t (value t)) -
        ((∑ i, ∑ k, B.a t i k (second i k t)) +
          (∑ i, B.b t i (first i t)) + B.c t (value t))‖
        = ‖((∑ i, ∑ k, A.a t i k (second i k t)) -
            (∑ i, ∑ k, B.a t i k (second i k t))) +
          ((∑ i, A.b t i (first i t)) -
            (∑ i, B.b t i (first i t))) +
          (A.c t (value t) - B.c t (value t))‖ := by
          congr 1
          abel
    _ ≤ ‖(∑ i, ∑ k, A.a t i k (second i k t)) -
          (∑ i, ∑ k, B.a t i k (second i k t))‖ +
        ‖(∑ i, A.b t i (first i t)) -
          (∑ i, B.b t i (first i t))‖ +
        ‖A.c t (value t) - B.c t (value t)‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add_left (norm_add_le _ _) _)
    _ ≤ (∑ i, ∑ k, ‖A.a t i k - B.a t i k‖ * ‖second i k‖) +
        (∑ i, ‖A.b t i - B.b t i‖ * ‖first i‖) +
          ‖A.c t - B.c t‖ * ‖value‖ := by
          exact add_le_add (add_le_add hA_sum hB_sum) hC

/-! Compactness turns the pointwise estimate into a section-space estimate. -/
theorem variableSectionApplyJetArgs_norm_le
    (ha : ∀ i k, Continuous (fun t => A.a t i k))
    (hb : ∀ i, Continuous (fun t => A.b t i))
    (hc : Continuous (fun t => A.c t))
    (value : T →ᵇ V) (first : ι → T →ᵇ V)
    (second : ι → ι → T →ᵇ V) :
    ‖A.variableSectionApplyJetArgs ha hb hc value first second‖ ≤
      (∑ i, ∑ k, ‖A.aSection ha i k‖ * ‖second i k‖) +
        (∑ i, ‖A.bSection hb i‖ * ‖first i‖) +
          ‖A.cSection hc‖ * ‖value‖ := by
  let C : ℝ :=
    (∑ i, ∑ k, ‖A.aSection ha i k‖ * ‖second i k‖) +
      (∑ i, ‖A.bSection hb i‖ * ‖first i‖) +
        ‖A.cSection hc‖ * ‖value‖
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  change ‖A.variableSectionApplyJetArgs ha hb hc value first second‖ ≤ C
  apply (BoundedContinuousFunction.norm_le hC).2
  intro t
  have hpoint := A.variableSectionApplyJetArgs_apply_norm_le
    ha hb hc value first second t
  have hAcoeff (i k : ι) :
      ‖A.a t i k‖ ≤ ‖A.aSection ha i k‖ :=
    (A.aSection ha i k).norm_coe_le_norm t
  have hBcoeff (i : ι) :
      ‖A.b t i‖ ≤ ‖A.bSection hb i‖ :=
    (A.bSection hb i).norm_coe_le_norm t
  have hCcoeff : ‖A.c t‖ ≤ ‖A.cSection hc‖ :=
    (A.cSection hc).norm_coe_le_norm t
  calc
    ‖A.variableSectionApplyJetArgs ha hb hc value first second t‖ ≤
        (∑ i, ∑ k, ‖A.a t i k‖ * ‖second i k‖) +
          (∑ i, ‖A.b t i‖ * ‖first i‖) + ‖A.c t‖ * ‖value‖ := hpoint
    _ ≤ C := by
      dsimp [C]
      refine add_le_add (add_le_add ?_ ?_) ?_
      · refine Finset.sum_le_sum (fun i hi => ?_)
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact mul_le_mul_of_nonneg_right (hAcoeff i k) (norm_nonneg _)
      · refine Finset.sum_le_sum (fun i hi => ?_)
        exact mul_le_mul_of_nonneg_right (hBcoeff i) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_right hCcoeff (norm_nonneg _)

@[simp] theorem variableSectionApplyJetArgs_add
    (ha : ∀ i k, Continuous (fun t => A.a t i k))
    (hb : ∀ i, Continuous (fun t => A.b t i))
    (hc : Continuous (fun t => A.c t))
    (value₁ value₂ : T →ᵇ V) (first₁ first₂ : ι → T →ᵇ V)
    (second₁ second₂ : ι → ι → T →ᵇ V) :
    A.variableSectionApplyJetArgs ha hb hc (value₁ + value₂)
        (first₁ + first₂) (second₁ + second₂) =
      A.variableSectionApplyJetArgs ha hb hc value₁ first₁ second₁ +
        A.variableSectionApplyJetArgs ha hb hc value₂ first₂ second₂ := by
  ext t
  simp only [variableSectionApplyJetArgs_apply,
    BoundedContinuousFunction.add_apply, Pi.add_apply]
  change A.applyJetArgs t (value₁ t + value₂ t)
      ((fun i => first₁ i t) + fun i => first₂ i t)
      ((fun i k => second₁ i k t) + fun i k => second₂ i k t) =
    A.applyJetArgs t (value₁ t) (fun i => first₁ i t)
        (fun i k => second₁ i k t) +
      A.applyJetArgs t (value₂ t) (fun i => first₂ i t)
        (fun i k => second₂ i k t)
  exact A.applyJetArgs_add t (value₁ t) (value₂ t)
    (fun i => first₁ i t) (fun i => first₂ i t)
    (fun i k => second₁ i k t) (fun i k => second₂ i k t)

@[simp] theorem variableSectionApplyJetArgs_smul
    (ha : ∀ i k, Continuous (fun t => A.a t i k))
    (hb : ∀ i, Continuous (fun t => A.b t i))
    (hc : Continuous (fun t => A.c t))
    (r : ℝ) (value : T →ᵇ V) (first : ι → T →ᵇ V)
    (second : ι → ι → T →ᵇ V) :
    A.variableSectionApplyJetArgs ha hb hc (r • value) (r • first)
        (r • second) = r • A.variableSectionApplyJetArgs ha hb hc value first second := by
  ext t
  simp only [variableSectionApplyJetArgs_apply,
    BoundedContinuousFunction.smul_apply, Pi.smul_apply]
  change A.applyJetArgs t (r • value t)
      ((fun i => r • first i t))
      ((fun i k => r • second i k t)) =
    r • A.applyJetArgs t (value t) (fun i => first i t)
      (fun i k => second i k t)
  exact A.applyJetArgs_smul t r (value t)
    (fun i => first i t) (fun i k => second i k t)

/-! Bundle the variable-coefficient evaluator as a continuous linear map of
the value and jet sections.  The coefficient field is held fixed. -/

/-- Sum of the uniform coefficient norms controlling the operator norm on the
product of bounded section spaces. -/
def variableSectionApplyJetArgsBound
    (ha : ∀ i k, Continuous (fun t => A.a t i k))
    (hb : ∀ i, Continuous (fun t => A.b t i))
    (hc : Continuous (fun t => A.c t)) : ℝ :=
  (∑ i, ∑ k, ‖A.aSection ha i k‖) +
    (∑ i, ‖A.bSection hb i‖) + ‖A.cSection hc‖

/-- Uniform coefficient difference controlling the variable evaluator on a
compact base.  The coefficient fields are measured in the sup norm of their
bounded continuous sections. -/
def variableSectionApplyJetArgsCoefficientBound
    (A B : VectorSecondOrderCoefficients T ι V)
    (haA : ∀ i k, Continuous (fun t => A.a t i k))
    (haB : ∀ i k, Continuous (fun t => B.a t i k))
    (hbA : ∀ i, Continuous (fun t => A.b t i))
    (hbB : ∀ i, Continuous (fun t => B.b t i))
    (hcA : Continuous (fun t => A.c t))
    (hcB : Continuous (fun t => B.c t)) : ℝ :=
  (∑ i, ∑ k, ‖A.aSection haA i k - B.aSection haB i k‖) +
    (∑ i, ‖A.bSection hbA i - B.bSection hbB i‖) +
      ‖A.cSection hcA - B.cSection hcB‖

theorem variableSectionApplyJetArgsCoefficientBound_nonneg
    (A B : VectorSecondOrderCoefficients T ι V)
    (haA : ∀ i k, Continuous (fun t => A.a t i k))
    (haB : ∀ i k, Continuous (fun t => B.a t i k))
    (hbA : ∀ i, Continuous (fun t => A.b t i))
    (hbB : ∀ i, Continuous (fun t => B.b t i))
    (hcA : Continuous (fun t => A.c t))
    (hcB : Continuous (fun t => B.c t)) :
    0 ≤ A.variableSectionApplyJetArgsCoefficientBound
      B haA haB hbA hbB hcA hcB := by
  simp only [variableSectionApplyJetArgsCoefficientBound]
  positivity

theorem variableSectionApplyJetArgsBound_nonneg
    (ha : ∀ i k, Continuous (fun t => A.a t i k))
    (hb : ∀ i, Continuous (fun t => A.b t i))
    (hc : Continuous (fun t => A.c t)) :
    0 ≤ A.variableSectionApplyJetArgsBound ha hb hc := by
  simp only [variableSectionApplyJetArgsBound]
  positivity

/-- The coefficient sum controls the variable evaluator for the sup norm on
the product of value, first-jet, and second-jet sections. -/
theorem variableSectionApplyJetArgs_norm_le_bound_mul
    (ha : ∀ i k, Continuous (fun t => A.a t i k))
    (hb : ∀ i, Continuous (fun t => A.b t i))
    (hc : Continuous (fun t => A.c t))
    (z : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) :
    ‖A.variableSectionApplyJetArgs ha hb hc z.1 z.2.1 z.2.2‖ ≤
      A.variableSectionApplyJetArgsBound ha hb hc * ‖z‖ := by
  have hvalue : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have hfirst (i : ι) : ‖z.2.1 i‖ ≤ ‖z‖ :=
    (norm_le_pi_norm z.2.1 i).trans
      ((norm_fst_le z.2).trans (norm_snd_le z))
  have hsecond (i k : ι) : ‖z.2.2 i k‖ ≤ ‖z‖ :=
    (norm_le_pi_norm (z.2.2 i) k).trans
      ((norm_le_pi_norm z.2.2 i).trans
        ((norm_snd_le z.2).trans (norm_snd_le z)))
  calc
    ‖A.variableSectionApplyJetArgs ha hb hc z.1 z.2.1 z.2.2‖ ≤
        (∑ i, ∑ k, ‖A.aSection ha i k‖ * ‖z.2.2 i k‖) +
          (∑ i, ‖A.bSection hb i‖ * ‖z.2.1 i‖) +
            ‖A.cSection hc‖ * ‖z.1‖ :=
      A.variableSectionApplyJetArgs_norm_le ha hb hc z.1 z.2.1 z.2.2
    _ ≤ (∑ i, ∑ k, ‖A.aSection ha i k‖ * ‖z‖) +
          (∑ i, ‖A.bSection hb i‖ * ‖z‖) +
            ‖A.cSection hc‖ * ‖z‖ := by
      refine add_le_add (add_le_add ?_ ?_) ?_
      · refine Finset.sum_le_sum (fun i hi => ?_)
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact mul_le_mul_of_nonneg_left (hsecond i k)
          (norm_nonneg (A.aSection ha i k))
      · refine Finset.sum_le_sum (fun i hi => ?_)
        exact mul_le_mul_of_nonneg_left (hfirst i)
          (norm_nonneg (A.bSection hb i))
      · exact mul_le_mul_of_nonneg_left hvalue
          (norm_nonneg (A.cSection hc))
    _ = A.variableSectionApplyJetArgsBound ha hb hc * ‖z‖ := by
      simp only [variableSectionApplyJetArgsBound, add_mul, Finset.sum_mul]

/-- Uniform coefficient perturbation estimate in the sup norm.  The input
section is held fixed, while the coefficient fields may vary. -/
theorem norm_variableSectionApplyJetArgs_coeff_sub_le
    (A B : VectorSecondOrderCoefficients T ι V)
    (haA : ∀ i k, Continuous (fun t => A.a t i k))
    (haB : ∀ i k, Continuous (fun t => B.a t i k))
    (hbA : ∀ i, Continuous (fun t => A.b t i))
    (hbB : ∀ i, Continuous (fun t => B.b t i))
    (hcA : Continuous (fun t => A.c t))
    (hcB : Continuous (fun t => B.c t))
    (z : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) :
    ‖A.variableSectionApplyJetArgs haA hbA hcA z.1 z.2.1 z.2.2 -
        B.variableSectionApplyJetArgs haB hbB hcB z.1 z.2.1 z.2.2‖ ≤
      A.variableSectionApplyJetArgsCoefficientBound
          B haA haB hbA hbB hcA hcB * ‖z‖ := by
  let C : ℝ := A.variableSectionApplyJetArgsCoefficientBound
    B haA haB hbA hbB hcA hcB
  have hC : 0 ≤ C := by
    dsimp [C]
    exact A.variableSectionApplyJetArgsCoefficientBound_nonneg
      B haA haB hbA hbB hcA hcB
  change ‖A.variableSectionApplyJetArgs haA hbA hcA z.1 z.2.1 z.2.2 -
      B.variableSectionApplyJetArgs haB hbB hcB z.1 z.2.1 z.2.2‖ ≤ C * ‖z‖
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg hC (norm_nonneg z))).2
  intro t
  have hpoint := A.variableSectionApplyJetArgs_coeff_sub_apply_norm_le
    B haA haB hbA hbB hcA hcB z.1 z.2.1 z.2.2 t
  have hvalue : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have hfirst (i : ι) : ‖z.2.1 i‖ ≤ ‖z‖ :=
    (norm_le_pi_norm z.2.1 i).trans
      ((norm_fst_le z.2).trans (norm_snd_le z))
  have hsecond (i k : ι) : ‖z.2.2 i k‖ ≤ ‖z‖ :=
    (norm_le_pi_norm (z.2.2 i) k).trans
      ((norm_le_pi_norm z.2.2 i).trans
        ((norm_snd_le z.2).trans (norm_snd_le z)))
  have hAcoeff (i k : ι) :
      ‖A.a t i k - B.a t i k‖ ≤
        ‖A.aSection haA i k - B.aSection haB i k‖ := by
    simpa only [BoundedContinuousFunction.sub_apply, aSection_apply,
      sub_apply] using
      (A.aSection haA i k - B.aSection haB i k).norm_coe_le_norm t
  have hBcoeff (i : ι) :
      ‖A.b t i - B.b t i‖ ≤
        ‖A.bSection hbA i - B.bSection hbB i‖ := by
    simpa only [BoundedContinuousFunction.sub_apply, bSection_apply,
      sub_apply] using
      (A.bSection hbA i - B.bSection hbB i).norm_coe_le_norm t
  have hCcoeff : ‖A.c t - B.c t‖ ≤
      ‖A.cSection hcA - B.cSection hcB‖ := by
    simpa only [BoundedContinuousFunction.sub_apply, cSection_apply,
      sub_apply] using
      (A.cSection hcA - B.cSection hcB).norm_coe_le_norm t
  calc
    ‖A.variableSectionApplyJetArgs haA hbA hcA z.1 z.2.1 z.2.2 t -
        B.variableSectionApplyJetArgs haB hbB hcB z.1 z.2.1 z.2.2 t‖ ≤
        (∑ i, ∑ k, ‖A.a t i k - B.a t i k‖ * ‖z.2.2 i k‖) +
          (∑ i, ‖A.b t i - B.b t i‖ * ‖z.2.1 i‖) +
            ‖A.c t - B.c t‖ * ‖z.1‖ := hpoint
    _ ≤ (∑ i, ∑ k,
          ‖A.aSection haA i k - B.aSection haB i k‖ * ‖z‖) +
          (∑ i, ‖A.bSection hbA i - B.bSection hbB i‖ * ‖z‖) +
            ‖A.cSection hcA - B.cSection hcB‖ * ‖z‖ := by
      refine add_le_add (add_le_add ?_ ?_) ?_
      · refine Finset.sum_le_sum (fun i hi => ?_)
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact mul_le_mul (hAcoeff i k) (hsecond i k)
          (norm_nonneg (z.2.2 i k))
          (norm_nonneg (A.aSection haA i k - B.aSection haB i k))
      · refine Finset.sum_le_sum (fun i hi => ?_)
        exact mul_le_mul (hBcoeff i) (hfirst i)
          (norm_nonneg (z.2.1 i))
          (norm_nonneg (A.bSection hbA i - B.bSection hbB i))
      · exact mul_le_mul hCcoeff hvalue (norm_nonneg z.1)
          (norm_nonneg (A.cSection hcA - B.cSection hcB))
    _ = C * ‖z‖ := by
      simp only [C, variableSectionApplyJetArgsCoefficientBound,
        add_mul, Finset.sum_mul]

/-- The variable-coefficient section evaluator as a linear map in the value
and jet sections. -/
def variableSectionApplyJetArgsLinearMap
    (ha : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (hb : ∀ i, Continuous (fun t ↦ A.b t i))
    (hc : Continuous (fun t ↦ A.c t)) :
    ((T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) →ₗ[ℝ] (T →ᵇ V) where
  toFun z := A.variableSectionApplyJetArgs ha hb hc z.1 z.2.1 z.2.2
  map_add' z w := by simp
  map_smul' r z := by simp

/-- The variable-coefficient section evaluator as a continuous linear map in
the value and jet sections. -/
def variableSectionApplyJetArgsCLM
    (ha : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (hb : ∀ i, Continuous (fun t ↦ A.b t i))
    (hc : Continuous (fun t ↦ A.c t)) :
    ((T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) →L[ℝ] (T →ᵇ V) :=
  (A.variableSectionApplyJetArgsLinearMap ha hb hc).mkContinuous
    (A.variableSectionApplyJetArgsBound ha hb hc)
    (A.variableSectionApplyJetArgs_norm_le_bound_mul ha hb hc)

@[simp] theorem variableSectionApplyJetArgsCLM_apply
    (ha : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (hb : ∀ i, Continuous (fun t ↦ A.b t i))
    (hc : Continuous (fun t ↦ A.c t))
    (z : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) :
    A.variableSectionApplyJetArgsCLM ha hb hc z =
      A.variableSectionApplyJetArgs ha hb hc z.1 z.2.1 z.2.2 := rfl

/-- The variable-coefficient section evaluator is continuous in its section
variables, with the coefficient field held fixed. -/
theorem continuous_variableSectionApplyJetArgs
    (ha : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (hb : ∀ i, Continuous (fun t ↦ A.b t i))
    (hc : Continuous (fun t ↦ A.c t)) :
    Continuous (fun z :
      (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V) ↦
      A.variableSectionApplyJetArgs ha hb hc z.1 z.2.1 z.2.2) := by
  change Continuous (A.variableSectionApplyJetArgsCLM ha hb hc)
  exact (A.variableSectionApplyJetArgsCLM ha hb hc).continuous

theorem norm_variableSectionApplyJetArgsCLM_le
    (ha : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (hb : ∀ i, Continuous (fun t ↦ A.b t i))
    (hc : Continuous (fun t ↦ A.c t)) :
    ‖A.variableSectionApplyJetArgsCLM ha hb hc‖ ≤
      A.variableSectionApplyJetArgsBound ha hb hc := by
  exact LinearMap.mkContinuous_norm_le _
    (A.variableSectionApplyJetArgsBound_nonneg ha hb hc)
    (A.variableSectionApplyJetArgs_norm_le_bound_mul ha hb hc)

/-- Uniform Lipschitz estimate in the value and jet sections, with the
coefficient field held fixed. -/
theorem norm_variableSectionApplyJetArgs_sub_le
    (ha : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (hb : ∀ i, Continuous (fun t ↦ A.b t i))
    (hc : Continuous (fun t ↦ A.c t))
    (z w : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) :
    ‖A.variableSectionApplyJetArgs ha hb hc z.1 z.2.1 z.2.2 -
        A.variableSectionApplyJetArgs ha hb hc w.1 w.2.1 w.2.2‖ ≤
      A.variableSectionApplyJetArgsBound ha hb hc * ‖z - w‖ := by
  change ‖A.variableSectionApplyJetArgsCLM ha hb hc z -
      A.variableSectionApplyJetArgsCLM ha hb hc w‖ ≤
    A.variableSectionApplyJetArgsBound ha hb hc * ‖z - w‖
  rw [← map_sub]
  exact (A.variableSectionApplyJetArgsCLM ha hb hc).le_opNorm (z - w) |>.trans
    (mul_le_mul_of_nonneg_right
      (A.norm_variableSectionApplyJetArgsCLM_le ha hb hc) (norm_nonneg _))

/-- Joint perturbation estimate for the variable evaluator.  The first term
measures changes in the value and jet sections with `A` fixed; the second
measures changes in the coefficient field, weighted by the reference input
`w`. -/
theorem norm_variableSectionApplyJetArgs_joint_sub_le
    (A B : VectorSecondOrderCoefficients T ι V)
    (haA : ∀ i k, Continuous (fun t => A.a t i k))
    (haB : ∀ i k, Continuous (fun t => B.a t i k))
    (hbA : ∀ i, Continuous (fun t => A.b t i))
    (hbB : ∀ i, Continuous (fun t => B.b t i))
    (hcA : Continuous (fun t => A.c t))
    (hcB : Continuous (fun t => B.c t))
    (z w : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) :
    ‖A.variableSectionApplyJetArgs haA hbA hcA z.1 z.2.1 z.2.2 -
        B.variableSectionApplyJetArgs haB hbB hcB w.1 w.2.1 w.2.2‖ ≤
      A.variableSectionApplyJetArgsBound haA hbA hcA * ‖z - w‖ +
        A.variableSectionApplyJetArgsCoefficientBound
          B haA haB hbA hbB hcA hcB * ‖w‖ := by
  calc
    ‖A.variableSectionApplyJetArgs haA hbA hcA z.1 z.2.1 z.2.2 -
        B.variableSectionApplyJetArgs haB hbB hcB w.1 w.2.1 w.2.2‖ =
        ‖(A.variableSectionApplyJetArgs haA hbA hcA z.1 z.2.1 z.2.2 -
            A.variableSectionApplyJetArgs haA hbA hcA w.1 w.2.1 w.2.2) +
          (A.variableSectionApplyJetArgs haA hbA hcA w.1 w.2.1 w.2.2 -
            B.variableSectionApplyJetArgs haB hbB hcB w.1 w.2.1 w.2.2)‖ := by
          congr 1
          abel
    _ ≤ ‖A.variableSectionApplyJetArgs haA hbA hcA z.1 z.2.1 z.2.2 -
          A.variableSectionApplyJetArgs haA hbA hcA w.1 w.2.1 w.2.2‖ +
        ‖A.variableSectionApplyJetArgs haA hbA hcA w.1 w.2.1 w.2.2 -
          B.variableSectionApplyJetArgs haB hbB hcB w.1 w.2.1 w.2.2‖ := by
          exact norm_add_le _ _
    _ ≤ A.variableSectionApplyJetArgsBound haA hbA hcA * ‖z - w‖ +
        A.variableSectionApplyJetArgsCoefficientBound
          B haA haB hbA hbB hcA hcB * ‖w‖ := by
          exact add_le_add
            (A.norm_variableSectionApplyJetArgs_sub_le haA hbA hcA z w)
            (A.norm_variableSectionApplyJetArgs_coeff_sub_le
              B haA haB hbA hbB hcA hcB w)

/-- The genuine Frechet derivative with respect to the three section
variables.  This does not differentiate the coefficient field. -/
theorem hasFDerivAt_variableSectionApplyJetArgs
    (ha : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (hb : ∀ i, Continuous (fun t ↦ A.b t i))
    (hc : Continuous (fun t ↦ A.c t))
    (z : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) :
    HasFDerivAt
      (fun w ↦ A.variableSectionApplyJetArgs ha hb hc w.1 w.2.1 w.2.2)
      (A.variableSectionApplyJetArgsCLM ha hb hc) z :=
  (A.variableSectionApplyJetArgsCLM ha hb hc).hasFDerivAt

theorem fderiv_variableSectionApplyJetArgs
    (ha : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (hb : ∀ i, Continuous (fun t ↦ A.b t i))
    (hc : Continuous (fun t ↦ A.c t))
    (z : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) :
    fderiv ℝ
      (fun w ↦ A.variableSectionApplyJetArgs ha hb hc w.1 w.2.1 w.2.2) z =
      A.variableSectionApplyJetArgsCLM ha hb hc :=
  (A.variableSectionApplyJetArgsCLM ha hb hc).fderiv

/-! An affine coefficient line gives a genuine coefficient-direction derivative.
The coefficient package itself has no ambient normed-space structure, so this
line is the unconditional parameter bridge used by later chartwise maps. -/

/-- Affine interpolation of two coefficient packages. -/
def coefficientLine
    (A H : VectorSecondOrderCoefficients T ι V) (s : ℝ) :
    VectorSecondOrderCoefficients T ι V where
  a := fun t i k => A.a t i k + s • H.a t i k
  b := fun t i => A.b t i + s • H.b t i
  c := fun t => A.c t + s • H.c t

omit [TopologicalSpace T] [CompactSpace T] in
@[simp] theorem coefficientLine_a
    (A H : VectorSecondOrderCoefficients T ι V) (s : ℝ)
    (t : T) (i k : ι) :
    (coefficientLine A H s).a t i k = A.a t i k + s • H.a t i k := rfl

omit [TopologicalSpace T] [CompactSpace T] in
@[simp] theorem coefficientLine_b
    (A H : VectorSecondOrderCoefficients T ι V) (s : ℝ)
    (t : T) (i : ι) :
    (coefficientLine A H s).b t i = A.b t i + s • H.b t i := rfl

omit [TopologicalSpace T] [CompactSpace T] in
@[simp] theorem coefficientLine_c
    (A H : VectorSecondOrderCoefficients T ι V) (s : ℝ)
    (t : T) :
    (coefficientLine A H s).c t = A.c t + s • H.c t := rfl

theorem variableSectionApplyJetArgs_coefficientLine_eq
    (A H : VectorSecondOrderCoefficients T ι V)
    (haA : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (haH : ∀ i k, Continuous (fun t ↦ H.a t i k))
    (hbA : ∀ i, Continuous (fun t ↦ A.b t i))
    (hbH : ∀ i, Continuous (fun t ↦ H.b t i))
    (hcA : Continuous (fun t ↦ A.c t))
    (hcH : Continuous (fun t ↦ H.c t))
    (s : ℝ)
    (z : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) :
    (coefficientLine A H s).variableSectionApplyJetArgs
        (fun i k ↦ (haA i k).add ((haH i k).const_smul s))
        (fun i ↦ (hbA i).add ((hbH i).const_smul s))
        (hcA.add (hcH.const_smul s)) z.1 z.2.1 z.2.2 =
      A.variableSectionApplyJetArgs haA hbA hcA z.1 z.2.1 z.2.2 +
        s • H.variableSectionApplyJetArgs haH hbH hcH z.1 z.2.1 z.2.2 := by
  ext t
  simp only [variableSectionApplyJetArgs_apply, coefficientLine_a,
    coefficientLine_b, coefficientLine_c,
    BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply,
    add_apply, smul_apply, Finset.sum_add_distrib, Finset.smul_sum,
    smul_add]
  abel

/-- Frechet derivative of the section evaluator along an affine coefficient
line.  The derivative is the evaluator of the coefficient direction `H`. -/
theorem hasFDerivAt_variableSectionApplyJetArgs_coefficientLine
    (A H : VectorSecondOrderCoefficients T ι V)
    (haA : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (haH : ∀ i k, Continuous (fun t ↦ H.a t i k))
    (hbA : ∀ i, Continuous (fun t ↦ A.b t i))
    (hbH : ∀ i, Continuous (fun t ↦ H.b t i))
    (hcA : Continuous (fun t ↦ A.c t))
    (hcH : Continuous (fun t ↦ H.c t))
    (z : (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)) (s₀ : ℝ) :
    HasFDerivAt
      (fun s ↦ (coefficientLine A H s).variableSectionApplyJetArgs
        (fun i k ↦ (haA i k).add ((haH i k).const_smul s))
        (fun i ↦ (hbA i).add ((hbH i).const_smul s))
        (hcA.add (hcH.const_smul s)) z.1 z.2.1 z.2.2)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight
        (H.variableSectionApplyJetArgs haH hbH hcH z.1 z.2.1 z.2.2)) s₀ := by
  -- The bounded-function library exposes a generic `Module` instance in
  -- addition to its normed-space instance.  Give the calculus lemmas a
  -- normed-space structure whose underlying modules are those generic
  -- instances, so their `HasFDerivAt` propositions match the statement.
  letI : NormedSpace ℝ ℝ :=
    { toModule := Semiring.toModule
      norm_smul_le := fun a b => norm_mul_le a b }
  letI : NormedSpace ℝ (T →ᵇ V) :=
    { toModule := BoundedContinuousFunction.instModule
      norm_smul_le := by
        intro a g
        apply (BoundedContinuousFunction.norm_le
          (mul_nonneg (norm_nonneg a) (norm_nonneg g))).2
        intro t
        rw [BoundedContinuousFunction.smul_apply, norm_smul]
        exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm t) (norm_nonneg a) }
  rw [show (fun s ↦ (coefficientLine A H s).variableSectionApplyJetArgs
        (fun i k ↦ (haA i k).add ((haH i k).const_smul s))
        (fun i ↦ (hbA i).add ((hbH i).const_smul s))
        (hcA.add (hcH.const_smul s)) z.1 z.2.1 z.2.2) =
      (fun s ↦ A.variableSectionApplyJetArgs haA hbA hcA
          z.1 z.2.1 z.2.2 +
        s • H.variableSectionApplyJetArgs haH hbH hcH z.1 z.2.1 z.2.2) by
        funext s
        exact variableSectionApplyJetArgs_coefficientLine_eq
          A H haA haH hbA hbH hcA hcH s z]
  exact (hasFDerivAt_id (𝕜 := ℝ) s₀).smul_const
    (H.variableSectionApplyJetArgs haH hbH hcH z.1 z.2.1 z.2.2) |>.const_add
      (A.variableSectionApplyJetArgs haA hbA hcA z.1 z.2.1 z.2.2)

/-! A normed coefficient-section product gives a genuine bilinear bridge.
The raw coefficient structure above intentionally has no norm; this product
packages precisely the continuous coefficient fields used by the evaluator. -/

abbrev VariableCoefficientSections :=
  (ι → ι → T →ᵇ (V →L[ℝ] V)) ×
    (ι → T →ᵇ (V →L[ℝ] V)) ×
      (T →ᵇ (V →L[ℝ] V))

abbrev VariableJetSections :=
  (T →ᵇ V) × (ι → T →ᵇ V) × (ι → ι → T →ᵇ V)

/-- Forget the bounded-section packaging and recover a raw coefficient field. -/
def variableCoefficientSectionsToCoefficients
    (C : VariableCoefficientSections (T := T) (ι := ι) (V := V)) :
    VectorSecondOrderCoefficients T ι V where
  a := fun t i k => C.1 i k t
  b := fun t i => C.2.1 i t
  c := fun t => C.2.2 t

/-- Evaluate a normed coefficient-section package on bounded jet sections. -/
def variableCoefficientSectionsApplyJetArgs
    (C : VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (z : VariableJetSections (T := T) (ι := ι) (V := V)) : T →ᵇ V :=
  (variableCoefficientSectionsToCoefficients C).variableSectionApplyJetArgs
    (fun i k => (C.1 i k).continuous)
    (fun i => (C.2.1 i).continuous)
    C.2.2.continuous z.1 z.2.1 z.2.2

@[simp] theorem variableCoefficientSectionsApplyJetArgs_apply
    (C : VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (z : VariableJetSections (T := T) (ι := ι) (V := V)) (t : T) :
    variableCoefficientSectionsApplyJetArgs C z t =
      (∑ i, ∑ k, (C.1 i k t) (z.2.2 i k t)) +
        (∑ i, (C.2.1 i t) (z.2.1 i t)) + (C.2.2 t) (z.1 t) := by
  simp [variableCoefficientSectionsApplyJetArgs,
    variableCoefficientSectionsToCoefficients,
    variableSectionApplyJetArgs_apply]

/-- The coefficient-section package induced by a raw field and continuity
witnesses. -/
def variableCoefficientSectionsOf
    (A : VectorSecondOrderCoefficients T ι V)
    (ha : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (hb : ∀ i, Continuous (fun t ↦ A.b t i))
    (hc : Continuous (fun t ↦ A.c t)) :
    VariableCoefficientSections (T := T) (ι := ι) (V := V) :=
  (fun i k ↦ A.aSection ha i k, fun i ↦ A.bSection hb i, A.cSection hc)

@[simp] theorem variableCoefficientSectionsOf_applyJetArgs
    (A : VectorSecondOrderCoefficients T ι V)
    (ha : ∀ i k, Continuous (fun t ↦ A.a t i k))
    (hb : ∀ i, Continuous (fun t ↦ A.b t i))
    (hc : Continuous (fun t ↦ A.c t))
    (z : VariableJetSections (T := T) (ι := ι) (V := V)) :
    variableCoefficientSectionsApplyJetArgs
        (variableCoefficientSectionsOf A ha hb hc) z =
      A.variableSectionApplyJetArgs ha hb hc z.1 z.2.1 z.2.2 := by
  ext t
  simp [variableCoefficientSectionsApplyJetArgs,
    variableCoefficientSectionsToCoefficients,
    variableCoefficientSectionsOf, variableSectionApplyJetArgs_apply]

/-- The packaged evaluator is bounded bilinear in coefficient and jet
sections.  Consequently it can be used as a continuous linear map in either
direction and has a genuine product-space Frechet derivative. -/
theorem isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs :
    IsBoundedBilinearMap ℝ
      (fun p : VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
          VariableJetSections (T := T) (ι := ι) (V := V) ↦
        variableCoefficientSectionsApplyJetArgs p.1 p.2) := by
  let K : ℝ :=
    (Fintype.card ι : ℝ) * Fintype.card ι + Fintype.card ι + 1
  refine
    { add_left := by
        intro C D z
        ext t
        simp [variableCoefficientSectionsApplyJetArgs,
          variableCoefficientSectionsToCoefficients,
          variableSectionApplyJetArgs_apply, Finset.sum_add_distrib]
        abel
      smul_left := by
        intro r C z
        ext t
        simp [variableCoefficientSectionsApplyJetArgs,
          variableCoefficientSectionsToCoefficients,
          variableSectionApplyJetArgs_apply, Finset.smul_sum]
      add_right := by
        intro C z w
        ext t
        simp [variableCoefficientSectionsApplyJetArgs,
          variableCoefficientSectionsToCoefficients,
          variableSectionApplyJetArgs_apply]
      smul_right := by
        intro r C z
        ext t
        simp [variableCoefficientSectionsApplyJetArgs,
          variableCoefficientSectionsToCoefficients,
          variableSectionApplyJetArgs_apply]
      bound := ?_ }
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    positivity
  · intro C z
    apply (BoundedContinuousFunction.norm_le
      (by positivity : 0 ≤ K * ‖C‖ * ‖z‖)).2
    intro t
    have hCa (i k : ι) : ‖C.1 i k t‖ ≤ ‖C‖ := by
      exact (C.1 i k).norm_coe_le_norm t |>.trans
        ((norm_le_pi_norm (C.1 i) k).trans
          ((norm_le_pi_norm C.1 i).trans (norm_fst_le C)))
    have hCb (i : ι) : ‖C.2.1 i t‖ ≤ ‖C‖ := by
      exact (C.2.1 i).norm_coe_le_norm t |>.trans
        ((norm_le_pi_norm C.2.1 i).trans
          ((norm_fst_le C.2).trans (norm_snd_le C)))
    have hCc : ‖C.2.2 t‖ ≤ ‖C‖ := by
      exact C.2.2.norm_coe_le_norm t |>.trans
        ((norm_snd_le C.2).trans (norm_snd_le C))
    have hZv : ‖z.1 t‖ ≤ ‖z‖ :=
      z.1.norm_coe_le_norm t |>.trans (norm_fst_le z)
    have hZf (i : ι) : ‖z.2.1 i t‖ ≤ ‖z‖ := by
      exact (z.2.1 i).norm_coe_le_norm t |>.trans
        ((norm_le_pi_norm z.2.1 i).trans
          ((norm_fst_le z.2).trans (norm_snd_le z)))
    have hZs (i k : ι) : ‖z.2.2 i k t‖ ≤ ‖z‖ := by
      exact (z.2.2 i k).norm_coe_le_norm t |>.trans
        ((norm_le_pi_norm (z.2.2 i) k).trans
          ((norm_le_pi_norm z.2.2 i).trans
            ((norm_snd_le z.2).trans (norm_snd_le z))))
    have hA (i k : ι) :
        ‖(C.1 i k t) (z.2.2 i k t)‖ ≤ ‖C‖ * ‖z‖ := by
      exact ((C.1 i k t).le_opNorm (z.2.2 i k t)).trans
        (mul_le_mul (hCa i k) (hZs i k)
          (norm_nonneg (z.2.2 i k t)) (norm_nonneg C))
    have hB (i : ι) :
        ‖(C.2.1 i t) (z.2.1 i t)‖ ≤ ‖C‖ * ‖z‖ := by
      exact ((C.2.1 i t).le_opNorm (z.2.1 i t)).trans
        (mul_le_mul (hCb i) (hZf i)
          (norm_nonneg (z.2.1 i t)) (norm_nonneg C))
    have hC : ‖(C.2.2 t) (z.1 t)‖ ≤ ‖C‖ * ‖z‖ := by
      exact ((C.2.2 t).le_opNorm (z.1 t)).trans
        (mul_le_mul hCc hZv (norm_nonneg (z.1 t)) (norm_nonneg C))
    rw [variableCoefficientSectionsApplyJetArgs_apply]
    calc
      ‖(∑ i, ∑ k, (C.1 i k t) (z.2.2 i k t)) +
          (∑ i, (C.2.1 i t) (z.2.1 i t)) + (C.2.2 t) (z.1 t)‖ ≤
          ‖∑ i, ∑ k, (C.1 i k t) (z.2.2 i k t)‖ +
            ‖∑ i, (C.2.1 i t) (z.2.1 i t)‖ +
              ‖(C.2.2 t) (z.1 t)‖ := by
            exact (norm_add_le _ _).trans
              (add_le_add_left (norm_add_le _ _) _)
      _ ≤ (∑ i, ∑ k, ‖C‖ * ‖z‖) +
          (∑ i, ‖C‖ * ‖z‖) + ‖C‖ * ‖z‖ := by
            exact add_le_add (add_le_add
              ((norm_sum_le _ _).trans
                (Finset.sum_le_sum (fun i hi =>
                  (norm_sum_le _ _).trans
                    (Finset.sum_le_sum (fun k hk => hA i k)))))
              ((norm_sum_le _ _).trans
                (Finset.sum_le_sum (fun i hi => hB i)))) hC
      _ = K * ‖C‖ * ‖z‖ := by
            simp [K, Finset.sum_const, Finset.card_univ]
            ring

def variableCoefficientSectionsApplyJetArgsCLM :
    VariableCoefficientSections (T := T) (ι := ι) (V := V) →L[ℝ]
      VariableJetSections (T := T) (ι := ι) (V := V) →L[ℝ] (T →ᵇ V) :=
  (isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
    (T := T) (ι := ι) (V := V)).toContinuousLinearMap

@[simp] theorem variableCoefficientSectionsApplyJetArgsCLM_apply
    (C : VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (z : VariableJetSections (T := T) (ι := ι) (V := V)) :
    variableCoefficientSectionsApplyJetArgsCLM C z =
      variableCoefficientSectionsApplyJetArgs C z := by
  exact IsBoundedBilinearMap.toContinuousLinearMap_apply
    (isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
      (T := T) (ι := ι) (V := V)) C z

/-! The bounded bilinear package gives the genuine derivative on the product
of coefficient and jet section spaces. -/

/-! The bounded-function module instance is provided independently of the
normed-space instance.  Register the product module explicitly so the
calculus predicates use the same pointwise scalar action as the bilinear map. -/
instance variableCoefficientSectionsJetSectionsModule :
    Module ℝ (VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
      VariableJetSections (T := T) (ι := ι) (V := V)) :=
  Prod.instModule

theorem hasFDerivAt_variableCoefficientSectionsApplyJetArgs
    (C : VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (z : VariableJetSections (T := T) (ι := ι) (V := V)) :
    HasFDerivAt
      (fun p : VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
          VariableJetSections (T := T) (ι := ι) (V := V) ↦
        variableCoefficientSectionsApplyJetArgs p.1 p.2)
      ((isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
        (T := T) (ι := ι) (V := V)).deriv (C, z)) (C, z) := by
  exact (isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
    (T := T) (ι := ι) (V := V)).hasFDerivAt (C, z)

@[simp] theorem variableCoefficientSectionsApplyJetArgs_deriv_apply
    (p q : VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
      VariableJetSections (T := T) (ι := ι) (V := V)) :
    (isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
      (T := T) (ι := ι) (V := V)).deriv p q =
        variableCoefficientSectionsApplyJetArgs p.1 q.2 +
          variableCoefficientSectionsApplyJetArgs q.1 p.2 := by
  rfl

end VectorSecondOrderCoefficients

end
end Topping
