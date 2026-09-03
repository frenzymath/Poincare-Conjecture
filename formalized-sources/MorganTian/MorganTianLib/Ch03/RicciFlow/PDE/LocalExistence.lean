import MorganTianLib.Ch03.RicciFlow.LocalExistence
import MorganTianLib.Ch03.RicciFlow.RicciDeTurckSymbol
import MorganTianLib.Ch03.RicciFlow.FlowRestriction

/-!
# Morgan--Tian Ch. 3 -- the PDE local-existence interface

The fixed-frame calculation in `RicciDeTurckSymbol` is the algebraic part of
Hamilton's gauge-breaking argument.  The analytic theorem used in the book is
an external short-time theorem for strictly parabolic systems.  This module
keeps that boundary explicit: a solver supplies a *classical PDE output*,
while the conversion of that output to the geometric DeTurck certificate is
proved here.  In particular, this file does not introduce a proposition whose
type is merely "there exists a Ricci flow".
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## The strict-parabolic certificate

The certificate is a finite-dimensional coercivity statement, rather than a
name for the Ricci-flow conclusion.  Its canonical instance is discharged by
the symbol computation already checked in `RicciDeTurckSymbol.lean`.
-/

/-- **Math.** Coercivity of the fixed-frame Ricci--DeTurck principal symbol in dimension
`n`.  This is the finite-dimensional strict-parabolic input to a classical
system solver. -/
structure RicciDeTurckStrictParabolic (n : ℕ) : Prop where
  coercive :
    ∀ {xi : RicciCovector n} {h : Matrix (Fin n) (Fin n) ℝ},
      xi ≠ 0 → h ≠ 0 →
        0 < ricciMatrixPairing h (deTurckLinearisationSymbol xi h)

/-- **Math.** The symbol algebra supplies the strict-parabolic certificate in every
finite dimension. -/
theorem canonicalRicciDeTurckStrictParabolic (n : ℕ) :
    RicciDeTurckStrictParabolic n where
  coercive := by
    intro xi h hxi hh
    exact deTurckLinearisationSymbol_coercive hxi hh

theorem canonicalRicciDeTurckStrictParabolic_coercive (n : ℕ)
    {xi : RicciCovector n} {h : Matrix (Fin n) (Fin n) ℝ}
    (hxi : xi ≠ 0) (hh : h ≠ 0) :
    0 < ricciMatrixPairing h (deTurckLinearisationSymbol xi h) := by
  exact (canonicalRicciDeTurckStrictParabolic n).coercive hxi hh

/-! ## Classical PDE output

The fields below are the output of the standard strictly-parabolic PDE
theorem.  They are deliberately coefficient-level fields: no `Has*`/`Is*`
predicate is introduced as a target-shaped existence assumption.  The adapter
below is the only place where this output enters the geometric Ricci-flow API.
-/

/-- **Math.** A classical solution output for the Ricci--DeTurck equation with initial
metric `g₀`.  The section field is the joint space-time regularity delivered by
the PDE theorem; the other two fields are its coefficient equation and initial
trace. -/
structure RicciDeTurckClassicalOutput (g₀ : RiemannianMetric I M) where
  lifespan : ℝ
  lifespan_pos : 0 < lifespan
  metric : ℝ → RiemannianMetric I M
  deturckField : ℝ → SmoothVectorField I M
  section_smooth :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (horizontalMetricSection metric)
      ((Set.univ : Set M) ×ˢ Ico 0 lifespan)
  coefficient_equation :
    ∀ t ∈ (Ico 0 lifespan : Set ℝ), ∀ (p : M)
      (v w : TangentSpace I p),
      HasDerivWithinAt (fun s => (metric s).metricInner p v w)
        (ricciDeTurckVariation (metric t) (deturckField t) p v w)
        (Ico 0 lifespan) t
  initial_coefficients :
    ∀ (p : M) (v w : TangentSpace I p),
      (metric 0).metricInner p v w = g₀.metricInner p v w

/-- **Math.** Convert a classical PDE output into the geometric DeTurck solution
certificate. -/
def RicciDeTurckClassicalOutput.toLocalSolution
    {g₀ : RiemannianMetric I M}
    (P : RicciDeTurckClassicalOutput g₀) :
    RicciDeTurckLocalSolution g₀ :=
  { T := P.lifespan
    hT := P.lifespan_pos
    gBar := P.metric
    V := P.deturckField
    smooth_raw := P.section_smooth
    equation_raw := P.coefficient_equation
    initial_raw := P.initial_coefficients }

@[simp] theorem RicciDeTurckClassicalOutput.toLocalSolution_T
    {g₀ : RiemannianMetric I M}
    (P : RicciDeTurckClassicalOutput g₀) :
    P.toLocalSolution.T = P.lifespan := rfl

theorem RicciDeTurckClassicalOutput.toLocalSolution_initial
    {g₀ : RiemannianMetric I M}
    (P : RicciDeTurckClassicalOutput g₀) :
    P.toLocalSolution.gBar 0 = g₀ := by
  exact P.toLocalSolution.initial

theorem RicciDeTurckClassicalOutput.toLocalSolution_equation
    {g₀ : RiemannianMetric I M}
    (P : RicciDeTurckClassicalOutput g₀) :
    IsRicciDeTurckEquationOn P.toLocalSolution.gBar P.toLocalSolution.V
      (Ico 0 P.toLocalSolution.T) := by
  exact P.toLocalSolution.deTurckEquation

/-! ## A supplied strictly-parabolic solver

The solver record is the precise analytic boundary of this development.  Its
`solve` field is what standard PDE theory provides; all geometric packaging
after that field is constructive and kernel checked.
-/

/-- **Math.** A supplied closed-manifold Ricci--DeTurck solver.  The symbol certificate
is recorded alongside the solver so downstream uses cannot silently forget the
strict-parabolic hypothesis. -/
structure RicciDeTurckPDESolver where
  symbol : RicciDeTurckStrictParabolic (Module.finrank ℝ E)
  solve : ∀ g₀ : RiemannianMetric I M, RicciDeTurckClassicalOutput g₀

/-- **Math.** The canonical symbol certificate is available without any analytic
assumption on the initial metric. -/
def canonicalRicciDeTurckPDESolverData
    (solve : ∀ g₀ : RiemannianMetric I M, RicciDeTurckClassicalOutput g₀) :
    RicciDeTurckPDESolver (E := E) (I := I) (M := M) where
  symbol := canonicalRicciDeTurckStrictParabolic (Module.finrank ℝ E)
  solve := solve

/-- **Math.** Apply a supplied solver and expose its result in the geometric certificate
API. -/
def RicciDeTurckPDESolver.localSolution
    (S : RicciDeTurckPDESolver (E := E) (I := I) (M := M))
    (g₀ : RiemannianMetric I M) : RicciDeTurckLocalSolution g₀ :=
  (S.solve g₀).toLocalSolution

/-- **Math.** A supplied classical strictly-parabolic solver yields a local Ricci--DeTurck
solution for every initial metric. -/
theorem exists_ricciDeTurckLocalSolution_of_solver
    (S : RicciDeTurckPDESolver (E := E) (I := I) (M := M))
    (g₀ : RiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ S₀ : RicciDeTurckLocalSolution g₀,
      S₀.T = T := by
  let P := S.solve g₀
  refine ⟨P.lifespan, P.lifespan_pos, P.toLocalSolution, ?_⟩
  rfl

/-- **Math.** The solver's output has the exact initial metric and DeTurck equation
needed by the Hamilton gauge transfer. -/
theorem ricciDeTurckLocalSolution_of_solver_has_initial_and_equation
    (S : RicciDeTurckPDESolver (E := E) (I := I) (M := M))
    (g₀ : RiemannianMetric I M) :
    (S.localSolution g₀).gBar 0 = g₀ ∧
      IsRicciDeTurckEquationOn (S.localSolution g₀).gBar
        (S.localSolution g₀).V (Ico 0 (S.localSolution g₀).T) := by
  constructor
  · exact (S.solve g₀).toLocalSolution_initial
  · exact (S.solve g₀).toLocalSolution_equation

/-! ## Direct solver-to-gauge assembly -/

/-- **Math.** A supplied DeTurck solver and an explicit Hamilton-gauge
transport assemble into a short-time Ricci flow.  The theorem keeps both
analytic boundaries visible: `S` supplies the PDE output, while `G` supplies
the time-dependent diffeomorphism, transport derivative, and Ricci
naturality data. -/
theorem exists_localRicciFlow_of_solver_and_hamiltonGauge
    (S : RicciDeTurckPDESolver (E := E) (I := I) (M := M))
    (g₀ : RiemannianMetric I M)
    (G : HamiltonGaugeTransport (S.localSolution g₀)) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric I M,
      IsRicciFlowOn g (Ico 0 T) ∧ g 0 = g₀ := by
  exact exists_localRicciFlow_of_splitHamiltonGauge G

/-- **Math.** Exact-time projection of the solver-to-gauge assembly. -/
theorem solver_hamiltonGauge_isRicciFlowOn_initial
    (S : RicciDeTurckPDESolver (E := E) (I := I) (M := M))
    (g₀ : RiemannianMetric I M)
    (G : HamiltonGaugeTransport (S.localSolution g₀)) :
    IsRicciFlowOn G.g (Ico 0 (S.localSolution g₀).T) ∧ G.g 0 = g₀ := by
  exact ⟨G.isRicciFlowOn, G.initial⟩

/-! ## Coefficient-level uniqueness on an overlap

This is the part of uniqueness that is independent of the analytic PDE
uniqueness theorem: once two solver outputs have the same coefficients, bundled
metric extensionality gives equality of the metric families. -/

theorem RicciDeTurckClassicalOutput.metric_eq_on_overlap
    {g₀ : RiemannianMetric I M}
    (P Q : RicciDeTurckClassicalOutput g₀)
    (hcoeff : ∀ t ∈ (Ico 0 (min P.lifespan Q.lifespan) : Set ℝ),
      ∀ (p : M) (v w : TangentSpace I p),
        (P.metric t).metricInner p v w = (Q.metric t).metricInner p v w) :
    ∀ t ∈ (Ico 0 (min P.lifespan Q.lifespan) : Set ℝ),
      P.metric t = Q.metric t := by
  intro t ht
  apply riemannianMetric_eq_of_metricInner_eq
  intro p v w
  exact hcoeff t ht p v w

/-! The next result discharges the one-dimensional part of PDE uniqueness.  An
analytic uniqueness theorem still has to identify the two nonlinear variation
fields; once that field is shared, the metric-family ODE and the common initial
trace force equality on the common interval. -/

/-- **Math.** Classical DeTurck outputs with a shared coefficient variation
and the same initial metric agree on the common lifespan.  The hypothesis is
the nonlinear PDE uniqueness boundary, while the interval propagation and
bundled-metric extensionality are proved here. -/
theorem RicciDeTurckClassicalOutput.metric_eq_on_overlap_of_sharedVariation
    {g₀ : RiemannianMetric I M}
    (P Q : RicciDeTurckClassicalOutput g₀)
    (hvariation : ∀ t ∈ (Ico 0 (min P.lifespan Q.lifespan) : Set ℝ),
      ∀ (p : M) (v w : TangentSpace I p),
        ricciDeTurckVariation (P.metric t) (P.deturckField t) p v w =
          ricciDeTurckVariation (Q.metric t) (Q.deturckField t) p v w) :
    ∀ t ∈ (Ico 0 (min P.lifespan Q.lifespan) : Set ℝ),
      P.metric t = Q.metric t := by
  let J : Set ℝ := Ico 0 (min P.lifespan Q.lifespan)
  let h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ :=
    fun t p v w => ricciDeTurckVariation (P.metric t) (P.deturckField t) p v w
  have hP : IsMetricVariationOn P.metric h J := by
    intro t ht p v w
    exact (P.coefficient_equation t
      ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩ p v w).mono
      (by
        intro s hs
        exact ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩)
  have hQ : IsMetricVariationOn Q.metric h J := by
    intro t ht p v w
    have hq := (Q.coefficient_equation t
      ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩ p v w).mono
      (show J ⊆ Ico 0 Q.lifespan from by
        intro s hs
        change s ∈ Ico 0 (min P.lifespan Q.lifespan) at hs
        exact ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩)
    rw [← hvariation t ht p v w] at hq
    exact hq
  have hzero : (0 : ℝ) ∈ J := by
    exact ⟨le_rfl, lt_min P.lifespan_pos Q.lifespan_pos⟩
  have hinit : P.metric 0 = Q.metric 0 := by
    exact (P.toLocalSolution_initial).trans Q.toLocalSolution_initial.symm
  have hagree : MetricFamilyAgreementOn P.metric Q.metric J :=
    metricFamilyAgreementOn_of_sharedMetricVariation ordConnected_Ico hP hQ
      hzero hinit
  intro t ht
  exact riemannianMetric_eq_of_metricInner_eq (hagree t ht)

#print axioms canonicalRicciDeTurckStrictParabolic
#print axioms RicciDeTurckClassicalOutput.toLocalSolution
#print axioms exists_ricciDeTurckLocalSolution_of_solver
#print axioms ricciDeTurckLocalSolution_of_solver_has_initial_and_equation
#print axioms RicciDeTurckClassicalOutput.metric_eq_on_overlap
#print axioms RicciDeTurckClassicalOutput.metric_eq_on_overlap_of_sharedVariation

end MorganTianLib

end
