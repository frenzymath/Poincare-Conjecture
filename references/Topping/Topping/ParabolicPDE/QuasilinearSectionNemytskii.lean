import Topping.ParabolicPDE.VariableSectionNemytskii

/-!
# Quasilinear section-space Nemytskii composition

This module isolates the bounded composition step for a quasilinear operator.
The coefficient package may depend on bounded value and first-jet sections,
while the evaluator remains linear in the second-jet section.  The coefficient
producer is supplied explicitly, recording the still-missing chart/bundle
construction rather than hiding it in an axiom.
-/

namespace Topping
namespace ParabolicPDE

open scoped BoundedContinuousFunction BigOperators

noncomputable section

variable {T ι V : Type*} [Fintype ι] [TopologicalSpace T]
  [CompactSpace T] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Bounded continuous value and first-jet sections. -/
abbrev QuasilinearFirstJetSections :=
  (T →ᵇ V) × (ι → T →ᵇ V)

/-- The full bounded value/first/second-jet input. -/
abbrev QuasilinearSectionInput :=
  Topping.VectorSecondOrderCoefficients.VariableJetSections
    (T := T) (ι := ι) (V := V)

/- The aliases above are reducible products; expose their product calculus
instances locally so `HasFDerivAt` sees the intended scalar actions. -/
local instance quasilinearFirstJetModule :
    Module ℝ (QuasilinearFirstJetSections (T := T) (ι := ι) (V := V)) :=
  Prod.instModule

local instance quasilinearFirstJetNormedSpace :
    NormedSpace ℝ (QuasilinearFirstJetSections (T := T) (ι := ι) (V := V)) :=
  Prod.normedSpace

local instance quasilinearInputModule :
    Module ℝ (QuasilinearSectionInput (T := T) (ι := ι) (V := V)) :=
  Prod.instModule

local instance quasilinearInputNormedSpace :
    NormedSpace ℝ (QuasilinearSectionInput (T := T) (ι := ι) (V := V)) :=
  Prod.normedSpace

local instance quasilinearCoefficientModule :
    Module ℝ (Topping.VectorSecondOrderCoefficients.VariableCoefficientSections
      (T := T) (ι := ι) (V := V)) :=
  Prod.instModule

local instance quasilinearCoefficientNormedSpace :
    NormedSpace ℝ (Topping.VectorSecondOrderCoefficients.VariableCoefficientSections
      (T := T) (ι := ι) (V := V)) :=
  Prod.normedSpace

open Topping.VectorSecondOrderCoefficients

/-! ## The value/first-jet projection -/

/-- The continuous linear projection which forgets the second jet. -/
def quasilinearFirstJetProjection :
    QuasilinearSectionInput (T := T) (ι := ι) (V := V) →L[ℝ]
      QuasilinearFirstJetSections (T := T) (ι := ι) (V := V) :=
  (ContinuousLinearMap.fst ℝ (T →ᵇ V)
      ((ι → T →ᵇ V) × (ι → ι → T →ᵇ V))).prod
    ((ContinuousLinearMap.fst ℝ (ι → T →ᵇ V)
      (ι → ι → T →ᵇ V)).comp
      (ContinuousLinearMap.snd ℝ (T →ᵇ V)
        ((ι → T →ᵇ V) × (ι → ι → T →ᵇ V))))

omit [Fintype ι] [CompactSpace T] in
@[simp] theorem quasilinearFirstJetProjection_apply
    (z : QuasilinearSectionInput (T := T) (ι := ι) (V := V)) :
    quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z =
      (z.1, z.2.1) := rfl

/-! ## The bounded quasilinear composition -/

/-- Evaluate a coefficient package produced from the value and first jet on the
second jet of the same section. -/
def quasilinearSectionApplyJetArgs
    (coeff : QuasilinearFirstJetSections (T := T) (ι := ι) (V := V) →
      VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (z : QuasilinearSectionInput (T := T) (ι := ι) (V := V)) : T →ᵇ V :=
  variableCoefficientSectionsApplyJetArgs
    (coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z)) z

@[simp] theorem quasilinearSectionApplyJetArgs_apply
    (coeff : QuasilinearFirstJetSections (T := T) (ι := ι) (V := V) →
      VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (z : QuasilinearSectionInput (T := T) (ι := ι) (V := V)) (t : T) :
    quasilinearSectionApplyJetArgs coeff z t =
      (∑ i, ∑ k,
        (coeff (z.1, z.2.1)).1 i k t (z.2.2 i k t)) +
        (∑ i, (coeff (z.1, z.2.1)).2.1 i t (z.2.1 i t)) +
          (coeff (z.1, z.2.1)).2.2 t (z.1 t) := by
  simp [quasilinearSectionApplyJetArgs,
    quasilinearFirstJetProjection_apply,
    variableCoefficientSectionsApplyJetArgs_apply]

/-! On a pure second-jet input, the value and first-jet coefficient slots are
zero, so the quasilinear evaluator is exactly the fixed-coefficient one. -/
theorem quasilinearSectionApplyJetArgs_pureSecond
    (coeff : QuasilinearFirstJetSections (T := T) (ι := ι) (V := V) →
      VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (Q : ι → ι → T →ᵇ V) :
    quasilinearSectionApplyJetArgs coeff (0, (0, Q)) =
      variableCoefficientSectionsApplyJetArgs (coeff (0, 0)) (0, 0, Q) := by
  ext t
  simp [quasilinearSectionApplyJetArgs,
    quasilinearFirstJetProjection_apply,
    variableCoefficientSectionsApplyJetArgs_apply]

/-! The composition is continuous whenever the coefficient producer is. -/
theorem continuous_quasilinearSectionApplyJetArgs
    {coeff : QuasilinearFirstJetSections (T := T) (ι := ι) (V := V) →
      VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    (hcoeff : Continuous coeff) :
    Continuous (fun z : QuasilinearSectionInput (T := T) (ι := ι) (V := V) =>
      quasilinearSectionApplyJetArgs coeff z) := by
  let B := isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
    (T := T) (ι := ι) (V := V)
  have hfirst : Continuous
      (fun z : QuasilinearSectionInput (T := T) (ι := ι) (V := V) =>
        quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z) :=
    (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V)).continuous
  have hpair : Continuous
      (fun z : QuasilinearSectionInput (T := T) (ι := ι) (V := V) =>
        (coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z), z)) :=
    (hcoeff.comp hfirst).prodMk continuous_id
  have hcomp := B.continuous.comp hpair
  simpa [quasilinearSectionApplyJetArgs, B, Function.comp_def] using hcomp

/-- The composition is continuous for a coefficient package independent of the
value and first-jet sections. -/
theorem continuous_quasilinearSectionApplyJetArgs_const
    (C : VariableCoefficientSections (T := T) (ι := ι) (V := V)) :
    Continuous (fun z : QuasilinearSectionInput (T := T) (ι := ι) (V := V) =>
      quasilinearSectionApplyJetArgs (fun _ => C) z) := by
  exact continuous_quasilinearSectionApplyJetArgs (coeff := fun _ => C) continuous_const

/-! ## Quantitative local control -/

/-- A bounded and Lipschitz coefficient producer gives a quantitative joint
estimate for the quasilinear section evaluator.  The coefficient bound is
only required at the value/first-jet projections being compared; this is the
local estimate used on a Picard ball. -/
theorem exists_norm_quasilinearSectionApplyJetArgs_sub_le
    {coeff : QuasilinearFirstJetSections (T := T) (ι := ι) (V := V) →
      VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {C Kc : ℝ} (hKc : 0 ≤ Kc)
    (hcoeff_bound : ∀ z : QuasilinearSectionInput
      (T := T) (ι := ι) (V := V),
      ‖coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z)‖ ≤ C)
    (hcoeff_lipschitz : ∀ z w : QuasilinearSectionInput
      (T := T) (ι := ι) (V := V),
      ‖coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z) -
        coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w)‖ ≤
        Kc * ‖quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z -
          quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w‖) :
    ∃ Kbil : ℝ, 0 ≤ Kbil ∧
      ∀ z w : QuasilinearSectionInput (T := T) (ι := ι) (V := V),
        ‖quasilinearSectionApplyJetArgs coeff z -
            quasilinearSectionApplyJetArgs coeff w‖ ≤
          Kbil * C * ‖z - w‖ + Kbil * Kc * ‖w‖ * ‖z - w‖ := by
  let B := isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
    (T := T) (ι := ι) (V := V)
  obtain ⟨Kbil, hKbil, hB⟩ := B.bound
  refine ⟨Kbil, le_of_lt hKbil, ?_⟩
  intro z w
  let Cz := coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z)
  let Cw := coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w)
  let E := B.toContinuousLinearMap
  have hsplit :
      E Cz z - E Cw w = E Cz (z - w) + E (Cz - Cw) w := by
    calc
      E Cz z - E Cw w = (E Cz z - E Cz w) + (E Cz w - E Cw w) := by
        abel
      _ = E Cz (z - w) + E (Cz - Cw) w := by
        rw [← map_sub]
        congr 1
        have hEsub : E (Cz - Cw) = E Cz - E Cw := map_sub E Cz Cw
        rw [hEsub]
        rfl
  have hnorm :
      ‖E Cz z - E Cw w‖ ≤ ‖E Cz (z - w)‖ + ‖E (Cz - Cw) w‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  have hfirst : ‖E Cz (z - w)‖ ≤ Kbil * C * ‖z - w‖ := by
    have h := hB Cz (z - w)
    have hcz : ‖Cz‖ ≤ C := hcoeff_bound z
    calc
      ‖E Cz (z - w)‖ ≤ Kbil * ‖Cz‖ * ‖z - w‖ := by
        simpa [E] using h
      _ ≤ Kbil * C * ‖z - w‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcz (le_of_lt hKbil)) (norm_nonneg _)
  have hsecond : ‖E (Cz - Cw) w‖ ≤ Kbil * Kc * ‖w‖ * ‖z - w‖ := by
    have h := hB (Cz - Cw) w
    have hcw : ‖Cz - Cw‖ ≤ Kc * ‖
        quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z -
          quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w‖ := by
      exact hcoeff_lipschitz z w
    have hproj : ‖quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z -
        quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w‖ ≤ ‖z - w‖ := by
      rw [quasilinearFirstJetProjection_apply,
        quasilinearFirstJetProjection_apply]
      rw [Prod.norm_def]
      apply max_le
      · exact norm_fst_le (z - w)
      · exact (norm_fst_le (z.2 - w.2)).trans (norm_snd_le (z - w))
    calc
      ‖E (Cz - Cw) w‖ ≤ Kbil * ‖Cz - Cw‖ * ‖w‖ := by
        simpa [E] using h
      _ ≤ Kbil * (Kc * ‖
          quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z -
            quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w‖) * ‖w‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcw (le_of_lt hKbil)) (norm_nonneg w)
      _ ≤ Kbil * (Kc * ‖z - w‖) * ‖w‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hproj hKc)
            (le_of_lt hKbil)) (norm_nonneg w)
      _ = Kbil * Kc * ‖w‖ * ‖z - w‖ := by ring
  rw [show quasilinearSectionApplyJetArgs coeff z = E Cz z by
    simp [E, Cz, quasilinearSectionApplyJetArgs],
    show quasilinearSectionApplyJetArgs coeff w = E Cw w by
    simp [E, Cw, quasilinearSectionApplyJetArgs]]
  exact hnorm.trans (add_le_add hfirst hsecond)

/-! ## Frechet derivative consumer -/

/- The coefficient derivative, precomposed with the value/first-jet projection,
paired with the identity derivative on the full jet section. -/
def quasilinearCoefficientJetDerivative
    (coeff' : QuasilinearFirstJetSections (T := T) (ι := ι) (V := V) →L[ℝ]
      VariableCoefficientSections (T := T) (ι := ι) (V := V)) :
    QuasilinearSectionInput (T := T) (ι := ι) (V := V) →L[ℝ]
      (VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
        QuasilinearSectionInput (T := T) (ι := ι) (V := V)) :=
  (coeff'.comp
      (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V))).prod
    (ContinuousLinearMap.id ℝ
      (QuasilinearSectionInput (T := T) (ι := ι) (V := V)))

theorem hasFDerivAt_quasilinearSectionApplyJetArgs
    {coeff : QuasilinearFirstJetSections (T := T) (ι := ι) (V := V) →
      VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {coeff' : QuasilinearFirstJetSections (T := T) (ι := ι) (V := V) →L[ℝ]
      VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    (z : QuasilinearSectionInput (T := T) (ι := ι) (V := V))
    (hcoeff : HasFDerivAt coeff coeff'
      (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z)) :
    HasFDerivAt
      (fun w : QuasilinearSectionInput (T := T) (ι := ι) (V := V) =>
        quasilinearSectionApplyJetArgs coeff w)
      (((isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
        (T := T) (ι := ι) (V := V)).deriv
        (coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z), z)).comp
      (quasilinearCoefficientJetDerivative (T := T) (ι := ι) (V := V)
          coeff')) z := by
  have hproj : HasFDerivAt
      (fun w : QuasilinearSectionInput (T := T) (ι := ι) (V := V) =>
        quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w)
      (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V)) z :=
    (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V)).hasFDerivAt
  have hcoeff' : HasFDerivAt
      (fun w : QuasilinearSectionInput (T := T) (ι := ι) (V := V) =>
        coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w))
      (coeff'.comp
        (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V))) z := by
    simpa [Function.comp_def] using
      (HasFDerivAt.comp
        (f := fun w : QuasilinearSectionInput (T := T) (ι := ι) (V := V) =>
          quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w)
        (f' := quasilinearFirstJetProjection (T := T) (ι := ι) (V := V))
        (g := coeff) (g' := coeff') z hcoeff hproj)
  have hpair : HasFDerivAt
      (fun w : QuasilinearSectionInput (T := T) (ι := ι) (V := V) =>
        (coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w), w))
      (quasilinearCoefficientJetDerivative (T := T) (ι := ι) (V := V)
        coeff') z := by
    have hid : HasFDerivAt
        (fun w : QuasilinearSectionInput (T := T) (ι := ι) (V := V) => w)
        (ContinuousLinearMap.id ℝ
          (QuasilinearSectionInput (T := T) (ι := ι) (V := V))) z :=
      (ContinuousLinearMap.id ℝ
        (QuasilinearSectionInput (T := T) (ι := ι) (V := V))).hasFDerivAt
    simpa [quasilinearCoefficientJetDerivative] using
      (HasFDerivAt.prodMk (f₁ := fun w =>
        coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w))
        (f₁' := coeff'.comp
          (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V)))
        (f₂ := fun w : QuasilinearSectionInput (T := T) (ι := ι) (V := V) => w)
        (f₂' := ContinuousLinearMap.id ℝ
          (QuasilinearSectionInput (T := T) (ι := ι) (V := V)))
        hcoeff' hid)
  have hB := (isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
    (T := T) (ι := ι) (V := V)).hasFDerivAt
    (coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z), z)
  have hcomp := HasFDerivAt.comp (f := fun w : QuasilinearSectionInput
      (T := T) (ι := ι) (V := V) =>
        (coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w), w))
    (f' := quasilinearCoefficientJetDerivative (T := T) (ι := ι) (V := V)
      coeff')
    z hB hpair
  simpa [quasilinearSectionApplyJetArgs, Function.comp_def] using hcomp

end
end ParabolicPDE
end Topping
