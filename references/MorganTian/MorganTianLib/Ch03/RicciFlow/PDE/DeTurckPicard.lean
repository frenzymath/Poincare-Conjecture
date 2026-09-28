import MorganTianLib.Ch03.RicciFlow.PDE.Contraction
import MorganTianLib.Ch03.RicciFlow.PDE.LocalExistence

/-!
# A Ricci--DeTurck Picard reconstruction bridge

The classical PDE theorem is naturally used through a Picard iteration on a
complete coefficient space.  This file records that boundary without making
the desired solution a hypothesis: a model supplies an invariant contraction
and reconstruction maps.  The fixed-point reconstruction is expressed by an
actual time-integral equation with a continuous source; the coefficient
equation and initial trace are then proved from the fundamental theorem of
calculus.  Banach's theorem supplies the fixed-point witness and hence an
actual `RicciDeTurckClassicalOutput`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace NNReal
open Set Filter Function Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## One initial metric -/

/-! ### Integral reconstruction -/

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A continuous coefficient source and its interval-integral
reconstruction give the corresponding metric variation on every time set. -/
theorem isMetricVariationOn_of_intervalIntegral
    {g₀ : RiemannianMetric I M}
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    (hcont : ∀ (p : M) (v w : TangentSpace I p),
      Continuous (fun s => h s p v w))
    (hint : ∀ (t : ℝ) (p : M) (v w : TangentSpace I p),
      (g t).metricInner p v w =
        g₀.metricInner p v w + ∫ s in (0 : ℝ)..t, h s p v w)
    (J : Set ℝ) : IsMetricVariationOn g h J := by
  intro t ht p v w
  have hp :=
    (hcont p v w).integral_hasStrictDerivAt (0 : ℝ) t |>.hasDerivAt.const_add
      (g₀.metricInner p v w)
  have hfun :
      (fun s => (g s).metricInner p v w) =
        (fun s => g₀.metricInner p v w + ∫ u in (0 : ℝ)..s, h u p v w) := by
    funext s
    exact hint s p v w
  rw [hfun]
  exact hp.hasDerivWithinAt

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Evaluating the interval reconstruction at time zero recovers
the prescribed initial metric coefficient. -/
theorem initial_metricInner_of_intervalIntegral
    {g₀ : RiemannianMetric I M}
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    (hint : ∀ (t : ℝ) (p : M) (v w : TangentSpace I p),
      (g t).metricInner p v w =
        g₀.metricInner p v w + ∫ s in (0 : ℝ)..t, h s p v w)
    (p : M) (v w : TangentSpace I p) :
    (g 0).metricInner p v w = g₀.metricInner p v w := by
  rw [hint]
  simp

/-- **Math.** A Picard model for one initial metric.  Its reconstruction
obligations are joint section regularity, continuity of the nonlinear source,
and the integral fixed-point equation.  Neither the differential equation nor
the initial trace is assumed as a separate field. -/
structure RicciDeTurckPicardModel
    (g₀ : RiemannianMetric I M) (X : Type*) [MetricSpace X] where
  contraction : ParabolicPDE.CompleteInvariantContraction X
  seed : X
  seed_mem : seed ∈ contraction.carrier
  lifespan : ℝ
  lifespan_pos : 0 < lifespan
  metric : X → ℝ → RiemannianMetric I M
  deturckField : X → ℝ → SmoothVectorField I M
  section_smooth_of_map :
    ∀ {x : X}, x ∈ contraction.carrier →
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (MorganTianLib.horizontalMetricSection (metric (contraction.map x)))
        ((Set.univ : Set M) ×ˢ Ico 0 lifespan)
  source_continuous_of_map :
    ∀ {x : X}, x ∈ contraction.carrier →
      ∀ (p : M) (v w : TangentSpace I p),
        Continuous (fun s =>
          MorganTianLib.ricciDeTurckVariation
            (metric x s) (deturckField x s) p v w)
  integral_equation_of_map :
    ∀ {x : X}, x ∈ contraction.carrier →
      ∀ (t : ℝ) (p : M) (v w : TangentSpace I p),
        (metric (contraction.map x) t).metricInner p v w =
          g₀.metricInner p v w +
            ∫ s in (0 : ℝ)..t,
              MorganTianLib.ricciDeTurckVariation
                (metric x s) (deturckField x s) p v w

namespace RicciDeTurckPicardModel

variable {g₀ : RiemannianMetric I M} {X : Type*} [MetricSpace X]
  (P : RicciDeTurckPicardModel g₀ X)

/-- **Math.** The coefficient point selected by Banach's theorem. -/
noncomputable def fixedPoint : X :=
  P.contraction.fixedPoint P.seed P.seed_mem

theorem fixedPoint_mem : P.fixedPoint ∈ P.contraction.carrier := by
  exact P.contraction.fixedPoint_mem P.seed P.seed_mem

theorem fixedPoint_isFixedPt :
    IsFixedPt P.contraction.map P.fixedPoint := by
  exact P.contraction.fixedPoint_isFixedPt P.seed P.seed_mem

/-- **Math.** Every invariant-set fixed point is the coefficient point selected
by Banach's theorem. -/
theorem fixedPoint_unique_of_fixed
    {x : X} (hx : x ∈ P.contraction.carrier)
    (hfix : IsFixedPt P.contraction.map x) :
    x = P.fixedPoint := by
  exact P.contraction.fixedPoint_unique hx P.fixedPoint_mem hfix
    P.fixedPoint_isFixedPt

/-! These projections are deliberately explicit: downstream proofs can use
the fixed-point witness without unfolding the output constructor. -/

theorem fixedPoint_section_smooth :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (MorganTianLib.horizontalMetricSection (P.metric P.fixedPoint))
      ((Set.univ : Set M) ×ˢ Ico 0 P.lifespan) := by
  have h := P.section_smooth_of_map P.fixedPoint_mem
  rw [P.fixedPoint_isFixedPt] at h
  exact h

theorem fixedPoint_coefficient_equation :
    ∀ t ∈ (Ico 0 P.lifespan : Set ℝ), ∀ (p : M)
      (v w : TangentSpace I p),
      HasDerivWithinAt
        (fun s => (P.metric P.fixedPoint s).metricInner p v w)
        (MorganTianLib.ricciDeTurckVariation
          (P.metric P.fixedPoint t) (P.deturckField P.fixedPoint t) p v w)
        (Ico 0 P.lifespan) t := by
  intro t ht p v w
  have hvariation :
      IsMetricVariationOn
        (P.metric P.fixedPoint)
        (fun t p v w =>
          MorganTianLib.ricciDeTurckVariation
            (P.metric P.fixedPoint t) (P.deturckField P.fixedPoint t) p v w)
        (Ico 0 P.lifespan) :=
    isMetricVariationOn_of_intervalIntegral
      (hcont := fun p v w =>
        by
          exact P.source_continuous_of_map P.fixedPoint_mem p v w)
      (hint := fun t p v w =>
        by
          have h := P.integral_equation_of_map P.fixedPoint_mem t p v w
          rw [P.fixedPoint_isFixedPt] at h
          exact h)
      (Ico 0 P.lifespan)
  exact hvariation t ht p v w

theorem fixedPoint_initial_coefficients :
    ∀ (p : M) (v w : TangentSpace I p),
      (P.metric P.fixedPoint 0).metricInner p v w = g₀.metricInner p v w := by
  intro p v w
  exact initial_metricInner_of_intervalIntegral
    (hint := fun t p v w =>
      by
        have h := P.integral_equation_of_map P.fixedPoint_mem t p v w
        rw [P.fixedPoint_isFixedPt] at h
        exact h) p v w

/-- **Math.** Banach's fixed point, reconstructed as the classical DeTurck output used
by the geometric transfer API. -/
noncomputable def classicalOutput :
    MorganTianLib.RicciDeTurckClassicalOutput g₀ :=
  { lifespan := P.lifespan
    lifespan_pos := P.lifespan_pos
    metric := P.metric P.fixedPoint
    deturckField := P.deturckField P.fixedPoint
    section_smooth := P.fixedPoint_section_smooth
    coefficient_equation := P.fixedPoint_coefficient_equation
    initial_coefficients := P.fixedPoint_initial_coefficients }

/-! The direct Morgan-facing view of the same fixed point. -/

/-- **Math.** Decode the Picard fixed point directly as a Morgan--Tian local
Ricci--DeTurck solution. -/
noncomputable def localSolution :
    MorganTianLib.RicciDeTurckLocalSolution g₀ :=
  P.classicalOutput.toLocalSolution

@[simp] theorem localSolution_T :
    P.localSolution.T = P.lifespan := rfl

theorem localSolution_initial : P.localSolution.gBar 0 = g₀ := by
  exact P.classicalOutput.toLocalSolution_initial

theorem localSolution_equation :
    IsRicciDeTurckEquationOn P.localSolution.gBar P.localSolution.V
      (Ico 0 P.localSolution.T) := by
  exact P.classicalOutput.toLocalSolution_equation

/-- **Math.** Banach's theorem yields a Morgan--Tian local solution with the
Picard model's positive lifespan. -/
theorem exists_ricciDeTurckLocalSolution_of_picard
    (P : RicciDeTurckPicardModel g₀ X) :
    ∃ T : ℝ, 0 < T ∧ ∃ S₀ : MorganTianLib.RicciDeTurckLocalSolution g₀,
      S₀.T = T := by
  exact ⟨P.lifespan, P.lifespan_pos, P.localSolution, rfl⟩

@[simp] theorem classicalOutput_lifespan :
    P.classicalOutput.lifespan = P.lifespan := rfl

theorem classicalOutput_toLocalSolution :
    P.classicalOutput.toLocalSolution =
      (P.classicalOutput : MorganTianLib.RicciDeTurckClassicalOutput g₀).toLocalSolution :=
  rfl

theorem exists_classicalOutput :
    ∃ Q : MorganTianLib.RicciDeTurckClassicalOutput g₀,
      Q = P.classicalOutput := by
  exact ⟨P.classicalOutput, rfl⟩

end RicciDeTurckPicardModel

/-! ## From Picard models to the solver interface -/

/-- **Math.** A family of invariant Picard models, one for each initial metric,
supplies the classical strictly-parabolic solver record.  The principal-symbol
certificate is the canonical algebraic one; Banach's theorem and the integral
reconstruction are discharged by each model's `classicalOutput`. -/
noncomputable def RicciDeTurckPDESolver.of_picard_models
    {X : Type*} [MetricSpace X]
    (models : ∀ g₀ : RiemannianMetric I M,
      RicciDeTurckPicardModel (I := I) (M := M) g₀ X) :
    RicciDeTurckPDESolver (E := E) (I := I) (M := M) where
  symbol := canonicalRicciDeTurckStrictParabolic (Module.finrank ℝ E)
  solve := fun g₀ => (models g₀).classicalOutput

/-- **Math.** The Picard-model family therefore yields a DeTurck local solution
for every prescribed initial metric, with the model's positive lifespan. -/
theorem exists_ricciDeTurckLocalSolution_of_picard_models
    {X : Type*} [MetricSpace X]
    (models : ∀ g₀ : RiemannianMetric I M,
      RicciDeTurckPicardModel (I := I) (M := M) g₀ X)
    (g₀ : RiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ S₀ : RicciDeTurckLocalSolution g₀,
      S₀.T = T := by
  exact exists_ricciDeTurckLocalSolution_of_solver
    (RicciDeTurckPDESolver.of_picard_models models) g₀

/-! ## Parameterised families -/

/-- **Math.** A family of Picard models with a common coefficient space.  The
reconstruction maps may depend on the parameter; the contraction theorem is
what controls the selected coefficient points as the parameter varies. -/
structure RicciDeTurckPicardFamily
    (A X : Type*) [MetricSpace A] [MetricSpace X]
    [Nonempty X] [CompleteSpace X] where
  initialMetric : A → RiemannianMetric I M
  contraction : ParabolicPDE.UniformContractionFamily A X
  lifespan : A → ℝ
  lifespan_pos : ∀ a, 0 < lifespan a
  metric : A → X → ℝ → RiemannianMetric I M
  deturckField : A → X → ℝ → SmoothVectorField I M
  section_smooth_of_map :
    ∀ (a : A) (x : X),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (MorganTianLib.horizontalMetricSection (metric a (contraction.map a x)))
        ((Set.univ : Set M) ×ˢ Ico 0 (lifespan a))
  source_continuous_of_map :
    ∀ (a : A) (x : X),
      ∀ (p : M) (v w : TangentSpace I p),
        Continuous (fun s =>
          MorganTianLib.ricciDeTurckVariation
            (metric a x s) (deturckField a x s) p v w)
  integral_equation_of_map :
    ∀ (a : A) (x : X),
      ∀ (t : ℝ) (p : M) (v w : TangentSpace I p),
        (metric a (contraction.map a x) t).metricInner p v w =
          (initialMetric a).metricInner p v w +
            ∫ s in (0 : ℝ)..t,
              MorganTianLib.ricciDeTurckVariation
                (metric a x s) (deturckField a x s) p v w

namespace RicciDeTurckPicardFamily

variable {A X : Type*} [MetricSpace A] [MetricSpace X]
  [Nonempty X] [CompleteSpace X]
  (F : RicciDeTurckPicardFamily (I := I) (M := M) A X)

noncomputable def fixedPoint (a : A) : X :=
  F.contraction.fixedPointAt a

theorem fixedPoint_isFixedPt (a : A) :
    IsFixedPt (F.contraction.map a) (F.fixedPoint a) := by
  exact F.contraction.fixedPointAt_isFixedPt a

theorem fixedPoint_section_smooth (a : A) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (MorganTianLib.horizontalMetricSection (F.metric a (F.fixedPoint a)))
      ((Set.univ : Set M) ×ˢ Ico 0 (F.lifespan a)) := by
  have h := F.section_smooth_of_map a (F.fixedPoint a)
  rw [F.fixedPoint_isFixedPt a] at h
  exact h

theorem fixedPoint_coefficient_equation (a : A) :
    ∀ t ∈ (Ico 0 (F.lifespan a) : Set ℝ), ∀ (p : M)
      (v w : TangentSpace I p),
      HasDerivWithinAt
        (fun s => (F.metric a (F.fixedPoint a) s).metricInner p v w)
        (MorganTianLib.ricciDeTurckVariation
          (F.metric a (F.fixedPoint a) t)
          (F.deturckField a (F.fixedPoint a) t) p v w)
        (Ico 0 (F.lifespan a)) t := by
  intro t ht p v w
  have hvariation :
      IsMetricVariationOn
        (F.metric a (F.fixedPoint a))
        (fun t p v w =>
          MorganTianLib.ricciDeTurckVariation
            (F.metric a (F.fixedPoint a) t)
            (F.deturckField a (F.fixedPoint a) t) p v w)
        (Ico 0 (F.lifespan a)) :=
    isMetricVariationOn_of_intervalIntegral
      (hcont := fun p v w =>
        by
          exact F.source_continuous_of_map a (F.fixedPoint a) p v w)
      (hint := fun t p v w =>
        by
          have h := F.integral_equation_of_map a (F.fixedPoint a) t p v w
          rw [F.fixedPoint_isFixedPt a] at h
          exact h)
      (Ico 0 (F.lifespan a))
  exact hvariation t ht p v w

theorem fixedPoint_initial_coefficients (a : A) :
    ∀ (p : M) (v w : TangentSpace I p),
      (F.metric a (F.fixedPoint a) 0).metricInner p v w =
        (F.initialMetric a).metricInner p v w := by
  intro p v w
  exact initial_metricInner_of_intervalIntegral
    (hint := fun t p v w =>
      by
        have h := F.integral_equation_of_map a (F.fixedPoint a) t p v w
        rw [F.fixedPoint_isFixedPt a] at h
        exact h) p v w

noncomputable def classicalOutput (a : A) :
    MorganTianLib.RicciDeTurckClassicalOutput (F.initialMetric a) :=
  { lifespan := F.lifespan a
    lifespan_pos := F.lifespan_pos a
    metric := F.metric a (F.fixedPoint a)
    deturckField := F.deturckField a (F.fixedPoint a)
    section_smooth := F.fixedPoint_section_smooth a
    coefficient_equation := F.fixedPoint_coefficient_equation a
    initial_coefficients := F.fixedPoint_initial_coefficients a }

/-! The parameter estimate is stated at the coefficient-space level.  It is
the quantitative smooth/continuous-dependence input passed to a later
reconstruction theorem. -/

theorem fixedPoint_parameter_stability
    {L : ℝ≥0}
    (hmap : ∀ (a b : A) (z : X),
      dist (F.contraction.map a z) (F.contraction.map b z) ≤
        (L : ℝ) * dist a b) (a b : A) :
    dist (F.fixedPoint a) (F.fixedPoint b) ≤
      (L : ℝ) * dist a b /
        (1 - (F.contraction.K : ℝ)) := by
  exact F.contraction.dist_fixedPointAt_le hmap a b

theorem fixedPoint_parameter_continuous
    {L : ℝ≥0}
    (hmap : ∀ (a b : A) (z : X),
      dist (F.contraction.map a z) (F.contraction.map b z) ≤
        (L : ℝ) * dist a b) :
    Continuous F.fixedPoint := by
  rw [Metric.continuous_iff]
  intro a ε hε
  have hK : 0 < 1 - (F.contraction.K : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast (F.contraction.contract a).1)
  by_cases hL : (L : ℝ) = 0
  · refine ⟨1, one_pos, ?_⟩
    intro b hb
    have hzero : dist (F.fixedPoint b) (F.fixedPoint a) = 0 := by
      apply le_antisymm
      · simpa [hL] using F.fixedPoint_parameter_stability hmap b a
      · exact dist_nonneg
    rw [dist_eq_zero] at hzero
    simpa [hzero]
  · have hLpos : 0 < (L : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (NNReal.coe_ne_zero.mp hL))
    refine ⟨ε * (1 - (F.contraction.K : ℝ)) / (L : ℝ), ?_, ?_⟩
    · positivity
    · intro b hb
      have hsmall : dist b a <
          ε * (1 - (F.contraction.K : ℝ)) / (L : ℝ) := by
        simpa [dist_comm] using hb
      have hmul : (L : ℝ) * dist b a <
          ε * (1 - (F.contraction.K : ℝ)) := by
        simpa [mul_comm] using (lt_div_iff₀ hLpos).mp hsmall
      have hquot : (L : ℝ) * dist b a /
          (1 - (F.contraction.K : ℝ)) < ε :=
        (div_lt_iff₀ hK).mpr hmul
      exact lt_of_le_of_lt (F.fixedPoint_parameter_stability hmap b a) hquot

end RicciDeTurckPicardFamily

end MorganTianLib

end
