import Topping.ParabolicPDE.Contraction
import MorganTianLib.Ch03.RicciFlow.PDE.LocalExistence

/-!
# A Ricci--DeTurck Picard reconstruction bridge

The classical PDE theorem is naturally used through a Picard iteration on a
complete coefficient space.  This file records that boundary without making
the desired solution a hypothesis: a model supplies an invariant contraction
and reconstruction maps, while the section regularity, coefficient equation,
and initial trace are required only as consequences of a fixed-point witness.
Banach's theorem supplies that witness and hence an actual
`RicciDeTurckClassicalOutput`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace NNReal
open Set Filter Function Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## One initial metric -/

/-! ### Integral reconstruction

The interval-integral identity is the concrete temporal part of a Picard
construction.  The two lemmas below turn that identity, together with source
continuity, into the within-derivative and initial-trace statements consumed
by the geometric Ricci--DeTurck API.  In particular, callers no longer have to
provide those statements as independent certificates. -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
theorem isMetricVariationOn_of_intervalIntegral
    {g₀ : RiemannianMetric I M}
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    (hcont : ∀ (p : M) (v w : TangentSpace I p),
      Continuous (fun s => h s p v w))
    (hint : ∀ (t : ℝ) (p : M) (v w : TangentSpace I p),
      (g t).metricInner p v w =
        g₀.metricInner p v w + ∫ s in (0 : ℝ)..t, h s p v w)
    (J : Set ℝ) : MorganTianLib.IsMetricVariationOn g h J := by
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

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
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

/-- **Math.** A Picard model for one initial metric.  The three final fields are
 the integral identity and source regularity are the concrete reconstruction
 obligations; the coefficient equation and initial trace are derived below. -/
structure RicciDeTurckPicardModel
    (g₀ : RiemannianMetric I M) (X : Type*) [MetricSpace X] where
  contraction : ParabolicPDE.CompleteInvariantContraction X
  seed : X
  seed_mem : seed ∈ contraction.carrier
  lifespan : ℝ
  lifespan_pos : 0 < lifespan
  metric : X → ℝ → RiemannianMetric I M
  deturckField : X → ℝ → SmoothVectorField I M
  section_smooth_of_fixed :
    ∀ {x : X}, x ∈ contraction.carrier →
      IsFixedPt contraction.map x →
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (MorganTianLib.horizontalMetricSection (metric x))
        ((Set.univ : Set M) ×ˢ Ico 0 lifespan)
  source_continuous_of_fixed :
    ∀ {x : X}, x ∈ contraction.carrier →
      IsFixedPt contraction.map x →
      ∀ (p : M) (v w : TangentSpace I p),
        Continuous (fun s =>
          MorganTianLib.ricciDeTurckVariation
            (metric x s) (deturckField x s) p v w)
  integral_equation_of_fixed :
    ∀ {x : X}, x ∈ contraction.carrier →
      IsFixedPt contraction.map x →
      ∀ (t : ℝ) (p : M) (v w : TangentSpace I p),
        (metric x t).metricInner p v w =
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

/-- **Math.** Any invariant-set fixed point of the Picard map is the selected
fixed point.  This is the coefficient-level forward uniqueness statement
used when two reconstructions are compared. -/
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
  exact P.section_smooth_of_fixed P.fixedPoint_mem P.fixedPoint_isFixedPt

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
      MorganTianLib.IsMetricVariationOn
        (P.metric P.fixedPoint)
        (fun t p v w =>
          MorganTianLib.ricciDeTurckVariation
            (P.metric P.fixedPoint t) (P.deturckField P.fixedPoint t) p v w)
        (Ico 0 P.lifespan) :=
    isMetricVariationOn_of_intervalIntegral
      (hcont := fun p v w =>
        P.source_continuous_of_fixed P.fixedPoint_mem
          P.fixedPoint_isFixedPt p v w)
      (hint := fun t p v w =>
        P.integral_equation_of_fixed P.fixedPoint_mem
          P.fixedPoint_isFixedPt t p v w)
      (Ico 0 P.lifespan)
  exact hvariation t ht p v w

theorem fixedPoint_initial_coefficients :
    ∀ (p : M) (v w : TangentSpace I p),
      (P.metric P.fixedPoint 0).metricInner p v w = g₀.metricInner p v w := by
  intro p v w
  exact initial_metricInner_of_intervalIntegral
    (hint := fun t p v w =>
      P.integral_equation_of_fixed P.fixedPoint_mem
        P.fixedPoint_isFixedPt t p v w) p v w

/-- **Math.** The reconstructed Picard metric has the prescribed initial
metric as an equality of bundled Riemannian metrics. -/
theorem fixedPoint_initial_metric :
    P.metric P.fixedPoint 0 = g₀ := by
  apply MorganTianLib.riemannianMetric_eq_of_metricInner_eq
  exact P.fixedPoint_initial_coefficients

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
  section_smooth_of_fixed :
    ∀ (a : A) {x : X},
      IsFixedPt (contraction.map a) x →
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (MorganTianLib.horizontalMetricSection (metric a x))
        ((Set.univ : Set M) ×ˢ Ico 0 (lifespan a))
  source_continuous_of_fixed :
    ∀ (a : A) {x : X}, IsFixedPt (contraction.map a) x →
      ∀ (p : M) (v w : TangentSpace I p),
        Continuous (fun s =>
          MorganTianLib.ricciDeTurckVariation
            (metric a x s) (deturckField a x s) p v w)
  integral_equation_of_fixed :
    ∀ (a : A) {x : X}, IsFixedPt (contraction.map a) x →
      ∀ (t : ℝ) (p : M) (v w : TangentSpace I p),
        (metric a x t).metricInner p v w =
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
  exact F.section_smooth_of_fixed a (F.fixedPoint_isFixedPt a)

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
      MorganTianLib.IsMetricVariationOn
        (F.metric a (F.fixedPoint a))
        (fun t p v w =>
          MorganTianLib.ricciDeTurckVariation
            (F.metric a (F.fixedPoint a) t)
            (F.deturckField a (F.fixedPoint a) t) p v w)
        (Ico 0 (F.lifespan a)) :=
    isMetricVariationOn_of_intervalIntegral
      (hcont := fun p v w =>
        F.source_continuous_of_fixed a (F.fixedPoint_isFixedPt a) p v w)
      (hint := fun t p v w =>
        F.integral_equation_of_fixed a (F.fixedPoint_isFixedPt a) t p v w)
      (Ico 0 (F.lifespan a))
  exact hvariation t ht p v w

theorem fixedPoint_initial_coefficients (a : A) :
    ∀ (p : M) (v w : TangentSpace I p),
      (F.metric a (F.fixedPoint a) 0).metricInner p v w =
        (F.initialMetric a).metricInner p v w := by
  intro p v w
  exact initial_metricInner_of_intervalIntegral
    (hint := fun t p v w =>
      F.integral_equation_of_fixed a (F.fixedPoint_isFixedPt a) t p v w) p v w

/-- **Math.** Every member of the parameterized Picard family attains its
prescribed initial metric as a bundled metric equality. -/
theorem fixedPoint_initial_metric (a : A) :
    F.metric a (F.fixedPoint a) 0 = F.initialMetric a := by
  apply MorganTianLib.riemannianMetric_eq_of_metricInner_eq
  exact F.fixedPoint_initial_coefficients a

noncomputable def classicalOutput (a : A) :
    MorganTianLib.RicciDeTurckClassicalOutput (F.initialMetric a) :=
  { lifespan := F.lifespan a
    lifespan_pos := F.lifespan_pos a
    metric := F.metric a (F.fixedPoint a)
    deturckField := F.deturckField a (F.fixedPoint a)
    section_smooth := F.fixedPoint_section_smooth a
    coefficient_equation := F.fixedPoint_coefficient_equation a
    initial_coefficients := F.fixedPoint_initial_coefficients a }

@[simp] theorem classicalOutput_lifespan (a : A) :
    (F.classicalOutput a).lifespan = F.lifespan a := rfl

theorem classicalOutput_metric (a : A) :
    (F.classicalOutput a).metric = F.metric a (F.fixedPoint a) := rfl

theorem classicalOutput_deturckField (a : A) :
    (F.classicalOutput a).deturckField =
      F.deturckField a (F.fixedPoint a) := rfl

/-- **Math.** The reconstructed family output retains the prescribed initial metric.

This projection theorem is the metric-level bridge used by consumers of
`RicciDeTurckClassicalOutput`; callers need not unfold the record constructor
to recover the fixed-point initial trace. -/
theorem classicalOutput_initial_metric (a : A) :
    (F.classicalOutput a).metric 0 = F.initialMetric a := by
  rw [F.classicalOutput_metric]
  exact F.fixedPoint_initial_metric a

theorem classicalOutput_initial_coefficients (a : A) :
    ∀ (p : M) (v w : TangentSpace I p),
      ((F.classicalOutput a).metric 0).metricInner p v w =
        (F.initialMetric a).metricInner p v w := by
  intro p v w
  rw [F.classicalOutput_metric]
  exact F.fixedPoint_initial_coefficients a p v w

theorem classicalOutput_coefficient_equation (a : A) :
    ∀ t ∈ (Ico 0 (F.lifespan a) : Set ℝ), ∀ (p : M)
      (v w : TangentSpace I p),
      HasDerivWithinAt
        (fun s => ((F.classicalOutput a).metric s).metricInner p v w)
        (MorganTianLib.ricciDeTurckVariation
          ((F.classicalOutput a).metric t)
          ((F.classicalOutput a).deturckField t) p v w)
        (Ico 0 (F.lifespan a)) t := by
  intro t ht p v w
  rw [F.classicalOutput_metric, F.classicalOutput_deturckField]
  exact F.fixedPoint_coefficient_equation a t ht p v w

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

/-- **Math.** Pointwise continuity of the parameterized Picard map already gives
continuity of the selected coefficient fixed point.  This weaker hypothesis
is useful when a chartwise DeTurck map has continuity but no uniform parameter
Lipschitz estimate yet. -/
theorem fixedPoint_continuous_of_pointwise_continuous
    (hmap : ∀ (z : X), Continuous (fun a : A => F.contraction.map a z)) :
    Continuous F.fixedPoint := by
  exact F.contraction.continuous_fixedPointAt_of_continuous hmap

end RicciDeTurckPicardFamily

end Topping

end
