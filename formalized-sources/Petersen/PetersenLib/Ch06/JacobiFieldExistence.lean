import PetersenLib.Ch06.JacobiChartBridge
import PetersenLib.Riemannian.Jacobi.PairJacobiField

/-!
# Petersen Ch. 6, §6.1 — bounded Jacobi initial data in one chart

This module is the small initial-value layer between the coordinate pair ODE and
Petersen's chart-free Jacobi equation.  `PetersenLib.Jacobi.IsJacobiFieldOn` is
kept in its own namespace (it is the coordinate pair predicate), while the
root `PetersenLib.IsJacobiFieldAlongOn` remains the chart-free equation.

The statements here deliberately require one fixed chart on the compact time
interval.  They provide the reusable bounded piece needed by later comparison
arguments; they do not claim the chart-covering/gluing theorem for an arbitrary
long curve.  In particular, uniqueness below is uniqueness of two fixed-chart
certificates, not of bare equation predicates (whose definition does not carry
regularity data).
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

namespace Jacobi

/-! ### Fixed-chart certificates and their readback -/

/-- A fixed-chart certificate for a pair of tangent fields along `c`.

The pair fields are stored in the model space `E`; the first conjunct records
that the whole compact interval is in the chosen chart source.  This is kept
under `PetersenLib.Jacobi` so it cannot be confused with the root,
chart-free `PetersenLib.IsJacobiFieldAlongOn` predicate.
-/
def IsJacobiPairAlongOn (g : RiemannianMetric I M) (c : ℝ → M) (α : M)
    (J DJ : ℝ → E) (a b : ℝ) : Prop :=
  (∀ t ∈ Icc a b, c t ∈ (chartAt H α).source) ∧
    IsJacobiFieldOn (I := I) g α (fun t => extChartAt I α (c t)) J DJ a b

/-- Read a model-space field in the chosen chart back to the moving tangent
fiber. -/
def chartReadbackField (c : ℝ → M) (α : M) (J : ℝ → E) :
    ∀ t, TangentSpace I (c t) :=
  fun t => (tangentCoordChange I α (c t) (c t) (J t) : TangentSpace I (c t))

@[simp] theorem chartReadbackField_apply (c : ℝ → M) (α : M) (J : ℝ → E) (t : ℝ) :
    chartReadbackField (I := I) c α J t =
      (tangentCoordChange I α (c t) (c t) (J t) : TangentSpace I (c t)) := rfl

/-- Reading a readback field in its original chart recovers the model-space
field, whenever the foot lies in the chart source. -/
theorem chartFieldRep_chartReadbackField {c : ℝ → M} {α : M} {J : ℝ → E} {t : ℝ}
    (hsrc : c t ∈ (chartAt H α).source) :
    chartFieldRep (I := I) c α (chartReadbackField (I := I) c α J) t = J t := by
  rw [chartFieldRep_apply, chartReadbackField_apply]
  have hxα : c t ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact hsrc
  have hfoot : c t ∈ (extChartAt I (c t)).source :=
    mem_extChartAt_source (I := I) (c t)
  rw [tangentCoordChange_comp (I := I) ⟨⟨hxα, hfoot⟩, hxα⟩]
  exact tangentCoordChange_self (I := I) hxα

/-- The readback of a chart reading of an intrinsic field is the original
field. -/
theorem chartReadbackField_chartFieldRep {c : ℝ → M} {α : M}
    {V : ∀ t, TangentSpace I (c t)} {t : ℝ}
    (hsrc : c t ∈ (chartAt H α).source) :
    chartReadbackField (I := I) c α (chartFieldRep (I := I) c α V) t = V t := by
  rw [chartReadbackField_apply, chartFieldRep_apply]
  have hxα : c t ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact hsrc
  have hfoot : c t ∈ (extChartAt I (c t)).source :=
    mem_extChartAt_source (I := I) (c t)
  change tangentCoordChange I α (c t) (c t)
      (tangentCoordChange I (c t) α (c t) (V t : E)) = (V t : E)
  rw [tangentCoordChange_comp (I := I) ⟨⟨hfoot, hxα⟩, hfoot⟩]
  exact tangentCoordChange_self (I := I) hfoot

/-! ### Bridge to Petersen's chart-free predicate -/

/-- A fixed-chart pair certificate yields Petersen's chart-free Jacobi equation
on the open interior.  The field on the right is the explicit tangent-fiber
readback of the chart pair. -/
theorem IsJacobiPairAlongOn.isJacobiFieldAlongOn
    {g : RiemannianMetric I M} {c : ℝ → M} {α : M}
    {J DJ : ℝ → E} {a b : ℝ}
    (h : IsJacobiPairAlongOn (I := I) g c α J DJ a b)
    (hc : ∀ t ∈ Icc a b, ContinuousAt c t)
    (hu : ∀ t ∈ Icc a b,
      DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t) :
    PetersenLib.IsJacobiFieldAlongOn (I := I) g c
      (chartReadbackField (I := I) c α J) (Ioo a b) := by
  exact isJacobiFieldAlongOn_Ioo_of_isJacobiFieldOn (I := I) g α hc h.1 hu h.2

/-! ### Existence with prescribed initial position and covariant derivative -/

/-- **Bounded one-chart Jacobi initial value theorem.**  The coordinate pair
ODE supplies a solution with prescribed `(J a, DJ a)` on `[a,b]`; its readback
is a tangent-fiber field solving Petersen's Jacobi equation on `(a,b)`.

The chart/source and regularity hypotheses are explicit.  This is the local
piece only; no chart-covering continuation is asserted here. -/
theorem exists_isJacobiPairAlongOn_Icc_of_chart
    (g : RiemannianMetric I M) (α : M) {c : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hc : ∀ t ∈ Icc a b, ContinuousAt c t)
    (hsrc : ∀ t ∈ Icc a b, c t ∈ (chartAt H α).source)
    (hu : ∀ t ∈ Icc a b,
      DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hucont : ContinuousOn (fun τ => extChartAt I α (c τ)) (Icc a b))
    (hu'cont : ContinuousOn (deriv (fun τ => extChartAt I α (c τ))) (Icc a b))
    (hmem : ∀ t ∈ Icc a b,
      extChartAt I α (c t) ∈ interior (extChartAt I α).target)
    (J₀ DJ₀ : TangentSpace I (c a)) :
    ∃ J DJ : ℝ → E,
      IsJacobiPairAlongOn (I := I) g c α J DJ a b ∧
      chartReadbackField (I := I) c α J a = J₀ ∧
      chartReadbackField (I := I) c α DJ a = DJ₀ ∧
      PetersenLib.IsJacobiFieldAlongOn (I := I) g c
        (chartReadbackField (I := I) c α J) (Ioo a b) := by
  let J₀α : E := tangentCoordChange I (c a) α (c a) (J₀ : E)
  let DJ₀α : E := tangentCoordChange I (c a) α (c a) (DJ₀ : E)
  obtain ⟨J, DJ, hJa, hDJa, hpair⟩ :=
    exists_isJacobiFieldOn_Icc_of_curve (I := I) g α hab hucont hu'cont hmem J₀α DJ₀α
  have hcert : IsJacobiPairAlongOn (I := I) g c α J DJ a b := ⟨hsrc, hpair⟩
  have hJread : chartReadbackField (I := I) c α J a = J₀ := by
    rw [chartReadbackField_apply, hJa]
    have hsrca := hsrc a (left_mem_Icc.2 hab)
    have hxα : c a ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact hsrca
    have hfoot : c a ∈ (extChartAt I (c a)).source :=
      mem_extChartAt_source (I := I) (c a)
    rw [show J₀α = tangentCoordChange I (c a) α (c a) (J₀ : E) from rfl]
    change tangentCoordChange I α (c a) (c a)
        (tangentCoordChange I (c a) α (c a) (J₀ : E)) = (J₀ : E)
    rw [tangentCoordChange_comp (I := I) ⟨⟨hfoot, hxα⟩, hfoot⟩]
    exact tangentCoordChange_self (I := I) hfoot
  have hDJread : chartReadbackField (I := I) c α DJ a = DJ₀ := by
    rw [chartReadbackField_apply, hDJa]
    have hsrca := hsrc a (left_mem_Icc.2 hab)
    have hxα : c a ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact hsrca
    have hfoot : c a ∈ (extChartAt I (c a)).source :=
      mem_extChartAt_source (I := I) (c a)
    rw [show DJ₀α = tangentCoordChange I (c a) α (c a) (DJ₀ : E) from rfl]
    change tangentCoordChange I α (c a) (c a)
        (tangentCoordChange I (c a) α (c a) (DJ₀ : E)) = (DJ₀ : E)
    rw [tangentCoordChange_comp (I := I) ⟨⟨hfoot, hxα⟩, hfoot⟩]
    exact tangentCoordChange_self (I := I) hfoot
  exact ⟨J, DJ, hcert, hJread, hDJread,
    hcert.isJacobiFieldAlongOn hc hu⟩

/-- The same bounded one-chart existence result with the tangent-fiber readback
returned directly.  The companion field `DJ` records the second coordinate of
the chart pair and exposes its prescribed initial value; this wrapper does not
assert that its readback is definitionally `derivAlongCurve g c J`.  That
additional derivative-readback identity belongs to the chart-transfer layer. -/
theorem exists_isJacobiFieldAlongOn_Ioo_of_chart_pair_initial
    (g : RiemannianMetric I M) (α : M) {c : ℝ → M} {a b : ℝ}
    (hab : a ≤ b)
    (hc : ∀ t ∈ Icc a b, ContinuousAt c t)
    (hsrc : ∀ t ∈ Icc a b, c t ∈ (chartAt H α).source)
    (hu : ∀ t ∈ Icc a b,
      DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hucont : ContinuousOn (fun τ => extChartAt I α (c τ)) (Icc a b))
    (hu'cont : ContinuousOn (deriv (fun τ => extChartAt I α (c τ))) (Icc a b))
    (hmem : ∀ t ∈ Icc a b,
      extChartAt I α (c t) ∈ interior (extChartAt I α).target)
    (J₀ DJ₀ : TangentSpace I (c a)) :
    ∃ J DJ : ∀ t, TangentSpace I (c t),
      PetersenLib.IsJacobiFieldAlongOn (I := I) g c J (Ioo a b) ∧
      J a = J₀ ∧ DJ a = DJ₀ := by
  obtain ⟨Jα, DJα, _hpair, hJ, hDJ, hroot⟩ :=
    exists_isJacobiPairAlongOn_Icc_of_chart (I := I) g α hab hc hsrc hu
      hucont hu'cont hmem J₀ DJ₀
  exact ⟨chartReadbackField (I := I) c α Jα,
    chartReadbackField (I := I) c α DJα, hroot, hJ, hDJ⟩

/-! ### Fixed-chart uniqueness -/

/-- Uniqueness of the coordinate pair solution with prescribed initial data. -/
theorem IsJacobiPairAlongOn.eqOn_of_initial
    {g : RiemannianMetric I M} {c : ℝ → M} {α : M}
    {J₁ DJ₁ J₂ DJ₂ : ℝ → E} {a b : ℝ} {K : NNReal}
    (hK : ∀ t ∈ Icc a b,
      ‖jacobiPairCoeffCoord (I := I) g α (fun τ => extChartAt I α (c τ)) t‖₊ ≤ K)
    (h₁ : IsJacobiPairAlongOn (I := I) g c α J₁ DJ₁ a b)
    (h₂ : IsJacobiPairAlongOn (I := I) g c α J₂ DJ₂ a b)
    (hJ : J₁ a = J₂ a) (hDJ : DJ₁ a = DJ₂ a) :
    EqOn J₁ J₂ (Icc a b) ∧ EqOn DJ₁ DJ₂ (Icc a b) :=
  IsJacobiFieldOn.eqOn_of_left hK h₁.2 h₂.2 hJ hDJ

/-- The tangent-fiber readbacks of two fixed-chart certificates agree when the
coordinate initial data agree. -/
theorem IsJacobiPairAlongOn.readback_eqOn_of_initial
    {g : RiemannianMetric I M} {c : ℝ → M} {α : M}
    {J₁ DJ₁ J₂ DJ₂ : ℝ → E} {a b : ℝ} {K : NNReal}
    (hK : ∀ t ∈ Icc a b,
      ‖jacobiPairCoeffCoord (I := I) g α (fun τ => extChartAt I α (c τ)) t‖₊ ≤ K)
    (h₁ : IsJacobiPairAlongOn (I := I) g c α J₁ DJ₁ a b)
    (h₂ : IsJacobiPairAlongOn (I := I) g c α J₂ DJ₂ a b)
    (hJ : J₁ a = J₂ a) (hDJ : DJ₁ a = DJ₂ a) :
    EqOn (chartReadbackField (I := I) c α J₁)
      (chartReadbackField (I := I) c α J₂) (Icc a b) ∧
    EqOn (chartReadbackField (I := I) c α DJ₁)
      (chartReadbackField (I := I) c α DJ₂) (Icc a b) := by
  obtain ⟨hJeq, hDJeq⟩ := h₁.eqOn_of_initial hK h₂ hJ hDJ
  constructor
  · intro t ht
    rw [chartReadbackField_apply, chartReadbackField_apply, hJeq ht]
  · intro t ht
    rw [chartReadbackField_apply, chartReadbackField_apply, hDJeq ht]

/-- Uniqueness with initial data stated directly in the tangent fibers.  The
coordinate equalities needed by the pair ODE are recovered by reading both
initial readbacks back into the fixed chart. -/
theorem IsJacobiPairAlongOn.readback_eqOn_of_readback_initial
    {g : RiemannianMetric I M} {c : ℝ → M} {α : M}
    {J₁ DJ₁ J₂ DJ₂ : ℝ → E} {a b : ℝ} (hab : a ≤ b) {K : NNReal}
    (hK : ∀ t ∈ Icc a b,
      ‖jacobiPairCoeffCoord (I := I) g α (fun τ => extChartAt I α (c τ)) t‖₊ ≤ K)
    (h₁ : IsJacobiPairAlongOn (I := I) g c α J₁ DJ₁ a b)
    (h₂ : IsJacobiPairAlongOn (I := I) g c α J₂ DJ₂ a b)
    (hJ : chartReadbackField (I := I) c α J₁ a =
      chartReadbackField (I := I) c α J₂ a)
    (hDJ : chartReadbackField (I := I) c α DJ₁ a =
      chartReadbackField (I := I) c α DJ₂ a) :
    EqOn (chartReadbackField (I := I) c α J₁)
      (chartReadbackField (I := I) c α J₂) (Icc a b) ∧
    EqOn (chartReadbackField (I := I) c α DJ₁)
      (chartReadbackField (I := I) c α DJ₂) (Icc a b) := by
  have hsrc₁a := h₁.1 a (left_mem_Icc.2 hab)
  have hsrc₂a := h₂.1 a (left_mem_Icc.2 hab)
  have hJcoord : J₁ a = J₂ a := by
    calc
      J₁ a = chartFieldRep (I := I) c α
          (chartReadbackField (I := I) c α J₁) a :=
        (chartFieldRep_chartReadbackField (I := I) hsrc₁a).symm
      _ = chartFieldRep (I := I) c α
          (chartReadbackField (I := I) c α J₂) a := by
        change tangentCoordChange I (c a) α (c a)
            (chartReadbackField (I := I) c α J₁ a : E) =
          tangentCoordChange I (c a) α (c a)
            (chartReadbackField (I := I) c α J₂ a : E)
        exact congrArg (fun V : TangentSpace I (c a) =>
          tangentCoordChange I (c a) α (c a) (V : E)) hJ
      _ = J₂ a := chartFieldRep_chartReadbackField (I := I) hsrc₂a
  have hDJcoord : DJ₁ a = DJ₂ a := by
    calc
      DJ₁ a = chartFieldRep (I := I) c α
          (chartReadbackField (I := I) c α DJ₁) a :=
        (chartFieldRep_chartReadbackField (I := I) hsrc₁a).symm
      _ = chartFieldRep (I := I) c α
          (chartReadbackField (I := I) c α DJ₂) a := by
        change tangentCoordChange I (c a) α (c a)
            (chartReadbackField (I := I) c α DJ₁ a : E) =
          tangentCoordChange I (c a) α (c a)
            (chartReadbackField (I := I) c α DJ₂ a : E)
        exact congrArg (fun V : TangentSpace I (c a) =>
          tangentCoordChange I (c a) α (c a) (V : E)) hDJ
      _ = DJ₂ a := chartFieldRep_chartReadbackField (I := I) hsrc₂a
  exact IsJacobiPairAlongOn.readback_eqOn_of_initial hK h₁ h₂ hJcoord hDJcoord

end Jacobi

end PetersenLib

end
