import Topping.ParabolicPDE.Operators

/-!
# Quotient assembly of scalar principal symbols

The local atlas interface in `Operators.lean` records a one-way transition
law.  This file adds the missing global assembly layer: invertible cotangent
coordinate changes and their cocycle make chart/covector representatives a
setoid, and the local quadratic symbol descends to the quotient.  No manifold
or bundle is assumed here; those geometric data can instantiate the atlas.
-/

namespace Topping
namespace ParabolicPDE

noncomputable section

open scoped BigOperators

variable {X C ι : Type*} [Fintype ι]

/-- A scalar symbol atlas with invertible cotangent-coordinate transitions.

`transition c d x` sends a covector represented in chart `c` to its
representation in chart `d`.  The composition law is stated in the order in
which `LinearEquiv.trans` composes maps. -/
structure ScalarPrincipalSymbolCocycle (X C ι : Type*) [Fintype ι] where
  localSymbol : C → X → (ι → ℝ) → ℝ
  transition : C → C → X → (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)
  transition_self : ∀ c x, transition c c x = LinearEquiv.refl ℝ (ι → ℝ)
  transition_cocycle : ∀ c d e x,
    (transition c d x).trans (transition d e x) = transition c e x
  glue : ∀ c d x ξ,
    localSymbol d x (transition c d x ξ) = localSymbol c x ξ

namespace ScalarPrincipalSymbolCocycle

variable (A : ScalarPrincipalSymbolCocycle X C ι)

@[simp] theorem transition_self_apply (c : C) (x : X) (ξ : ι → ℝ) :
    A.transition c c x ξ = ξ := by
  rw [A.transition_self c x]
  exact LinearEquiv.refl_apply ξ

theorem transition_inverse_apply (c d : C) (x : X) (ξ : ι → ℝ) :
    A.transition d c x (A.transition c d x ξ) = ξ := by
  have h := congrArg (fun e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) => e ξ)
    (A.transition_cocycle c d c x)
  simpa [LinearEquiv.trans_apply, A.transition_self c x] using h

theorem transition_inverse_apply' (c d : C) (x : X) (ξ : ι → ℝ) :
    A.transition c d x (A.transition d c x ξ) = ξ := by
  have h := congrArg (fun e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) => e ξ)
    (A.transition_cocycle d c d x)
  simpa [LinearEquiv.trans_apply, A.transition_self d x] using h

theorem glue_inverse (c d : C) (x : X) (ξ : ι → ℝ) :
    A.localSymbol c x (A.transition d c x ξ) = A.localSymbol d x ξ := by
  rw [A.glue d c x ξ]

end ScalarPrincipalSymbolCocycle

/-! ## Chart/covector representatives and their quotient -/

/-- A representative of a cotangent vector, including its base point and
chart label. -/
structure ChartCovector (X C ι : Type*) where
  base : X
  chart : C
  covector : ι → ℝ

namespace ChartCovector

variable (A : ScalarPrincipalSymbolCocycle X C ι)

/-- Two representatives are equivalent when they have the same base point and
the second is the transition of the first. -/
def Equivalent (p q : ChartCovector X C ι) : Prop :=
  p.base = q.base ∧
    q.covector = A.transition p.chart q.chart p.base p.covector

theorem equivalent_refl (p : ChartCovector X C ι) :
    Equivalent A p p := by
  refine ⟨rfl, ?_⟩
  rw [A.transition_self p.chart p.base]
  exact (LinearEquiv.refl_apply p.covector).symm

theorem equivalent_symm {p q : ChartCovector X C ι}
    (hpq : Equivalent A p q) : Equivalent A q p := by
  rcases hpq with ⟨hbase, hcov⟩
  refine ⟨hbase.symm, ?_⟩
  rw [← hbase]
  rw [hcov]
  exact (A.transition_inverse_apply p.chart q.chart p.base p.covector).symm

theorem equivalent_trans {p q r : ChartCovector X C ι}
    (hpq : Equivalent A p q) (hqr : Equivalent A q r) :
    Equivalent A p r := by
  rcases hpq with ⟨hpq_base, hpq_cov⟩
  rcases hqr with ⟨hqr_base, hqr_cov⟩
  refine ⟨hpq_base.trans hqr_base, ?_⟩
  rw [← hpq_base] at hqr_cov
  rw [hqr_cov, hpq_cov, ← LinearEquiv.trans_apply]
  rw [A.transition_cocycle p.chart q.chart r.chart p.base]

end ChartCovector

/- The setoid is parameterized by the atlas rather than installed globally:
different atlases on the same coordinate type give different quotient spaces. -/
def chartCovectorSetoid
    (A : ScalarPrincipalSymbolCocycle X C ι) : Setoid (ChartCovector X C ι) where
  r := ChartCovector.Equivalent A
  iseqv := by
    constructor
    · exact ChartCovector.equivalent_refl A
    · intro p q hpq
      exact ChartCovector.equivalent_symm A hpq
    · intro p q r hpq hqr
      exact ChartCovector.equivalent_trans A hpq hqr

/-- The quotient of chart/covector representatives. -/
abbrev GlobalCovector (A : ScalarPrincipalSymbolCocycle X C ι) :=
  Quotient (chartCovectorSetoid A)

namespace ScalarPrincipalSymbolCocycle

variable (A : ScalarPrincipalSymbolCocycle X C ι)

/-- The local symbol descends to a well-defined function on the quotient. -/
def globalSymbol : GlobalCovector A → ℝ :=
  Quotient.lift
    (fun p : ChartCovector X C ι => A.localSymbol p.chart p.base p.covector)
    (by
      intro p q hpq
      rcases hpq with ⟨hbase, hcov⟩
      rw [← hbase]
      rw [hcov, A.glue])

@[simp] theorem globalSymbol_mk (p : ChartCovector X C ι) :
    A.globalSymbol ⟦p⟧ = A.localSymbol p.chart p.base p.covector := by
  rfl

theorem globalSymbol_eq_of_equivalent
    {p q : ChartCovector X C ι} (hpq : ChartCovector.Equivalent A p q) :
    A.localSymbol p.chart p.base p.covector =
      A.localSymbol q.chart q.base q.covector := by
  rcases hpq with ⟨hbase, hcov⟩
  rw [← hbase, hcov, A.glue]

theorem globalSymbol_positive_iff_of_equivalent
    {p q : ChartCovector X C ι} (hpq : ChartCovector.Equivalent A p q) :
    0 < A.localSymbol p.chart p.base p.covector ↔
      0 < A.localSymbol q.chart q.base q.covector := by
  rw [A.globalSymbol_eq_of_equivalent hpq]

end ScalarPrincipalSymbolCocycle

/-! ## The quotient is the promised global principal-symbol object. -/

/-- A global scalar principal symbol, assembled from an atlas quotient. -/
structure GlobalScalarPrincipalSymbol
    (A : ScalarPrincipalSymbolCocycle X C ι) where
  value : GlobalCovector A → ℝ
  value_is_local :
    ∀ (p : ChartCovector X C ι), value ⟦p⟧ =
      A.localSymbol p.chart p.base p.covector

namespace ScalarPrincipalSymbolCocycle

variable (A : ScalarPrincipalSymbolCocycle X C ι)

def globalPrincipalSymbol : GlobalScalarPrincipalSymbol A where
  value := A.globalSymbol
  value_is_local := fun p => A.globalSymbol_mk p

@[simp] theorem globalPrincipalSymbol_value_mk (p : ChartCovector X C ι) :
    (A.globalPrincipalSymbol).value ⟦p⟧ =
      A.localSymbol p.chart p.base p.covector :=
  A.globalPrincipalSymbol.value_is_local p

theorem globalPrincipalSymbol_positive_iff
    (p q : ChartCovector X C ι)
    (hpq : ChartCovector.Equivalent A p q) :
    0 < (A.globalPrincipalSymbol).value ⟦p⟧ ↔
      0 < (A.globalPrincipalSymbol).value ⟦q⟧ := by
  rw [A.globalPrincipalSymbol_value_mk, A.globalPrincipalSymbol_value_mk]
  exact A.globalSymbol_positive_iff_of_equivalent hpq

end ScalarPrincipalSymbolCocycle

/-! ## A concrete one-chart consumer -/

/-- The principal symbol of any scalar coefficient field as a one-chart
atlas.  This is useful for Euclidean model equations and also checks that the
quotient assembly has a genuine concrete consumer. -/
def singleChartPrincipalSymbolCocycle
    {X : Type*} {n : ℕ}
    (A : ScalarSecondOrderCoefficients X n) :
    ScalarPrincipalSymbolCocycle X Unit (Fin n) where
  localSymbol := fun _ x ξ => A.principalSymbol x ξ
  transition := fun _ _ _ => LinearEquiv.refl ℝ (Fin n → ℝ)
  transition_self := by
    intro c x
    rfl
  transition_cocycle := by
    intro c d e x
    rfl
  glue := by
    intro c d x ξ
    simp

@[simp] theorem singleChartPrincipalSymbolCocycle_globalSymbol_mk
    {X : Type*} {n : ℕ}
    (A : ScalarSecondOrderCoefficients X n)
    (p : ChartCovector X Unit (Fin n)) :
    (singleChartPrincipalSymbolCocycle A).globalSymbol ⟦p⟧ =
      A.principalSymbol p.base p.covector := by
  rw [ScalarPrincipalSymbolCocycle.globalSymbol_mk]
  rfl

theorem singleChart_heat_globalSymbol_pos
    {X : Type*} {n : ℕ} (p : ChartCovector X Unit (Fin n))
    (hp : p.covector ≠ 0) :
    0 < (singleChartPrincipalSymbolCocycle
      (heatCoefficients X n)).globalSymbol ⟦p⟧ := by
  rw [singleChartPrincipalSymbolCocycle_globalSymbol_mk,
    heatCoefficients_principalSymbol]
  exact euclideanNormSq_pos hp

end
end ParabolicPDE
end Topping
