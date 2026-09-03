import Topping.ParabolicPDE.Operators

/-!
# Quotient assembly of vector-valued principal symbols

The local vector symbol is an endomorphism of the fibre.  This file assembles
its evaluations on chart representatives into a quotient, using the frame
transition to transport the fibre vector.  The covector coordinate is kept in
the representative; the abstract `GlobalPrincipalSymbol` interface leaves
its transition law to a later geometric layer.
-/

namespace Topping
namespace ParabolicPDE

noncomputable section

variable {X C ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

structure ChartSymbolVector (X C ι V : Type*) where
  base : X
  chart : C
  covector : ι → ℝ
  vector : V

namespace ChartSymbolVector

variable (G : GlobalPrincipalSymbol X C ι V)

theorem frame_self_forward_apply (c : C) (v : V) :
    (G.frame c c).forward v = v := by
  have hidem : (G.frame c c).forward.comp (G.frame c c).forward =
      (G.frame c c).forward := by
    simpa using (G.cocycle_forward c c c).symm
  have happly := congrArg (fun f : V →L[ℝ] V => f v) hidem
  apply (G.frame c c).forward_injective
  simpa [ContinuousLinearMap.comp_apply] using happly

theorem frame_forward_inverse_apply (c d : C) (v : V) :
    (G.frame d c).forward ((G.frame c d).forward v) = v := by
  apply (G.frame c d).forward_injective
  have hc := G.cocycle_forward d c d
  have h := congrArg (fun f : V →L[ℝ] V => f ((G.frame c d).forward v)) hc
  simpa [ContinuousLinearMap.comp_apply,
    ChartSymbolVector.frame_self_forward_apply] using h.symm

def Equivalent (p q : ChartSymbolVector X C ι V) : Prop :=
  p.base = q.base ∧ p.covector = q.covector ∧
    q.vector = (G.frame p.chart q.chart).forward p.vector

theorem equivalent_refl (p : ChartSymbolVector X C ι V) :
    Equivalent G p p := by
  refine ⟨rfl, rfl, ?_⟩
  exact (ChartSymbolVector.frame_self_forward_apply G p.chart p.vector).symm

theorem equivalent_symm {p q : ChartSymbolVector X C ι V}
    (hpq : Equivalent G p q) : Equivalent G q p := by
  rcases hpq with ⟨hbase, hxi, hv⟩
  refine ⟨hbase.symm, hxi.symm, ?_⟩
  rw [hv]
  exact (ChartSymbolVector.frame_forward_inverse_apply G p.chart q.chart p.vector).symm

theorem equivalent_trans {p q r : ChartSymbolVector X C ι V}
    (hpq : Equivalent G p q) (hqr : Equivalent G q r) :
    Equivalent G p r := by
  rcases hpq with ⟨hpq_base, hpq_xi, hpq_v⟩
  rcases hqr with ⟨hqr_base, hqr_xi, hqr_v⟩
  refine ⟨hpq_base.trans hqr_base, hpq_xi.trans hqr_xi, ?_⟩
  rw [hqr_v, hpq_v]
  have hc := G.cocycle_forward p.chart q.chart r.chart
  change (G.frame q.chart r.chart).forward
      ((G.frame p.chart q.chart).forward p.vector) = _
  rw [← ContinuousLinearMap.comp_apply, ← hc]

end ChartSymbolVector

def chartSymbolVectorSetoid
    (G : GlobalPrincipalSymbol X C ι V) : Setoid (ChartSymbolVector X C ι V) where
  r := ChartSymbolVector.Equivalent G
  iseqv := by
    constructor
    · exact ChartSymbolVector.equivalent_refl G
    · intro p q hpq
      exact ChartSymbolVector.equivalent_symm G hpq
    · intro p q r hpq hqr
      exact ChartSymbolVector.equivalent_trans G hpq hqr

abbrev GlobalSymbolVector (G : GlobalPrincipalSymbol X C ι V) :=
  Quotient (chartSymbolVectorSetoid G)

structure ChartFiberVector (X C V : Type*) where
  base : X
  chart : C
  vector : V

namespace ChartFiberVector

variable (G : GlobalPrincipalSymbol X C ι V)

def Equivalent (p q : ChartFiberVector X C V) : Prop :=
  p.base = q.base ∧ q.vector = (G.frame p.chart q.chart).forward p.vector

theorem equivalent_refl (p : ChartFiberVector X C V) :
    Equivalent G p p := by
  refine ⟨rfl, ?_⟩
  exact (ChartSymbolVector.frame_self_forward_apply G p.chart p.vector).symm

theorem equivalent_symm {p q : ChartFiberVector X C V}
    (hpq : Equivalent G p q) : Equivalent G q p := by
  rcases hpq with ⟨hbase, hv⟩
  refine ⟨hbase.symm, ?_⟩
  rw [hv]
  exact (ChartSymbolVector.frame_forward_inverse_apply G p.chart q.chart p.vector).symm

theorem equivalent_trans {p q r : ChartFiberVector X C V}
    (hpq : Equivalent G p q) (hqr : Equivalent G q r) :
    Equivalent G p r := by
  rcases hpq with ⟨hpq_base, hpq_v⟩
  rcases hqr with ⟨hqr_base, hqr_v⟩
  refine ⟨hpq_base.trans hqr_base, ?_⟩
  rw [hqr_v, hpq_v]
  have hc := G.cocycle_forward p.chart q.chart r.chart
  change (G.frame q.chart r.chart).forward
      ((G.frame p.chart q.chart).forward p.vector) = _
  rw [← ContinuousLinearMap.comp_apply, ← hc]

end ChartFiberVector

def chartFiberVectorSetoid
    (G : GlobalPrincipalSymbol X C ι V) : Setoid (ChartFiberVector X C V) where
  r := ChartFiberVector.Equivalent G
  iseqv := by
    constructor
    · exact ChartFiberVector.equivalent_refl G
    · intro p q hpq
      exact ChartFiberVector.equivalent_symm G hpq
    · intro p q r hpq hqr
      exact ChartFiberVector.equivalent_trans G hpq hqr

abbrev GlobalFiberVector (G : GlobalPrincipalSymbol X C ι V) :=
  Quotient (chartFiberVectorSetoid G)

namespace GlobalPrincipalSymbol

variable (G : GlobalPrincipalSymbol X C ι V)

def globalSymbolVector : GlobalSymbolVector G → GlobalFiberVector G :=
  Quotient.lift
    (fun p : ChartSymbolVector X C ι V =>
      ⟦⟨p.base, p.chart, G.localSymbol p.chart p.base p.covector p.vector⟩⟧)
    (by
      intro p q hpq
      rcases hpq with ⟨hbase, hxi, hv⟩
      rw [← hbase, ← hxi, hv]
      apply Quotient.sound
      refine ⟨rfl, ?_⟩
      rw [G.gluing_apply p.chart q.chart p.base p.covector]
      simp [BundleFrameTransition.backward_forward_apply])

@[simp] theorem globalSymbolVector_mk (p : ChartSymbolVector X C ι V) :
    G.globalSymbolVector ⟦p⟧ =
      (⟦⟨p.base, p.chart, G.localSymbol p.chart p.base p.covector p.vector⟩⟧ :
        GlobalFiberVector G) := by
  rfl

theorem globalSymbolVector_eq_of_equivalent
    {p q : ChartSymbolVector X C ι V}
    (hpq : ChartSymbolVector.Equivalent G p q) :
    (⟦⟨p.base, p.chart, G.localSymbol p.chart p.base p.covector p.vector⟩⟧ :
      GlobalFiberVector G) =
      ⟦⟨q.base, q.chart, G.localSymbol q.chart q.base q.covector q.vector⟩⟧ := by
  rcases hpq with ⟨hbase, hxi, hv⟩
  rw [← hbase, ← hxi, hv]
  apply Quotient.sound
  refine ⟨rfl, ?_⟩
  rw [G.gluing_apply p.chart q.chart p.base p.covector]
  simp [BundleFrameTransition.backward_forward_apply]

structure GlobalVectorPrincipalSymbol where
  value : GlobalSymbolVector G → GlobalFiberVector G
  value_is_local :
    ∀ p : ChartSymbolVector X C ι V, value ⟦p⟧ =
        (⟦⟨p.base, p.chart, G.localSymbol p.chart p.base p.covector p.vector⟩⟧ :
          GlobalFiberVector G)

def globalVectorPrincipalSymbol : GlobalVectorPrincipalSymbol G where
  value := G.globalSymbolVector
  value_is_local := fun p => G.globalSymbolVector_mk p

@[simp] theorem globalVectorPrincipalSymbol_value_mk
    (p : ChartSymbolVector X C ι V) :
    (G.globalVectorPrincipalSymbol).value ⟦p⟧ =
      (⟦⟨p.base, p.chart, G.localSymbol p.chart p.base p.covector p.vector⟩⟧ :
        GlobalFiberVector G) :=
  G.globalVectorPrincipalSymbol.value_is_local p

end GlobalPrincipalSymbol

end
end ParabolicPDE
end Topping
