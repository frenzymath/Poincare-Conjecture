import Topping.ParabolicPDE.GlobalSymbol

/-!
# Consumers for the global scalar symbol quotient

The cocycle interface has invertible cotangent transitions, while the atlas
interface is the one used by the parabolicity predicates.  This module bridges
the two and records the representative-independent nonzero/positivity facts
needed by later manifold constructions.
-/

namespace Topping
namespace ParabolicPDE

noncomputable section

variable {X C ι : Type*} [Fintype ι]

/-! ## Bridging the two symbol interfaces -/

/-- The invertible transition data of a cocycle give the injective transition
maps required by the atlas-level parabolicity interface. -/
def ScalarPrincipalSymbolCocycle.toAtlas
    (A : ScalarPrincipalSymbolCocycle X C ι) :
    ScalarPrincipalSymbolAtlas X C ι where
  localSymbol := A.localSymbol
  covectorTransition := fun c d x => A.transition c d x
  transition_zero := by
    intro c d x
    exact map_zero _
  transition_injective := by
    intro c d x
    exact (A.transition c d x).injective
  glue := A.glue

@[simp] theorem ScalarPrincipalSymbolCocycle.toAtlas_localSymbol
    (A : ScalarPrincipalSymbolCocycle X C ι) (c : C) (x : X) (ξ : ι → ℝ) :
    (A.toAtlas).localSymbol c x ξ = A.localSymbol c x ξ := rfl

/-! ## Nonzero quotient covectors -/

/-- A quotient covector is nonzero when (equivalently, any) chart
representative is nonzero.  The `Quotient.lift` proof below makes the
representative-independence explicit. -/
def ScalarPrincipalSymbolCocycle.globalCovectorNonzero
    (A : ScalarPrincipalSymbolCocycle X C ι) : GlobalCovector A → Prop :=
  Quotient.lift (fun p : ChartCovector X C ι => p.covector ≠ 0)
    (by
      intro p q hpq
      apply propext
      rcases hpq with ⟨hbase, hcov⟩
      constructor
      · intro hp hq
        apply hp
        have he : (A.transition p.chart q.chart p.base) p.covector = 0 := by
          rw [← hcov, hq]
        exact (A.transition p.chart q.chart p.base).map_eq_zero_iff.mp he
      · intro hq hp
        apply hq
        rw [hcov, hp]
        exact map_zero _)

@[simp] theorem ScalarPrincipalSymbolCocycle.globalCovectorNonzero_mk
    (A : ScalarPrincipalSymbolCocycle X C ι) (p : ChartCovector X C ι) :
    A.globalCovectorNonzero ⟦p⟧ ↔ p.covector ≠ 0 := by
  rfl

/-! ## Positivity consumers -/

/-- Local positivity of a cocycle descends to its global symbol on every
nonzero quotient covector. -/
theorem ScalarPrincipalSymbolCocycle.globalSymbol_pos_of_local_pos
    (A : ScalarPrincipalSymbolCocycle X C ι)
    (hpos : ∀ c x ξ, ξ ≠ 0 → 0 < A.localSymbol c x ξ)
    (ξ : GlobalCovector A) :
    A.globalCovectorNonzero ξ → 0 < A.globalSymbol ξ := by
  refine Quotient.inductionOn ξ ?_
  intro p hp
  rw [A.globalSymbol_mk]
  exact hpos p.chart p.base p.covector
    ((A.globalCovectorNonzero_mk p).mp hp)

/-- The same positivity consumer can be stated using the atlas view of the
cocycle, which is the form expected by fixed-coordinate parabolicity APIs. -/
theorem ScalarPrincipalSymbolCocycle.globalSymbol_pos_of_atlas_pos
    (A : ScalarPrincipalSymbolCocycle X C ι)
    (hpos : ∀ c x ξ, ξ ≠ 0 → 0 < (A.toAtlas).atlasSymbol c x ξ)
    (ξ : GlobalCovector A) :
    A.globalCovectorNonzero ξ → 0 < A.globalSymbol ξ := by
  apply A.globalSymbol_pos_of_local_pos
  intro c x ξ hξ
  exact hpos c x ξ hξ

end
end ParabolicPDE
end Topping
