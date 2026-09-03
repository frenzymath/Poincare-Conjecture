import MorganTianLib.Ch03.RicciFlow.PDE.VolterraPicard

/-!
# Stability and uniqueness for the Banach-valued Volterra producer

The Picard construction in `VolterraPicard` gives one trajectory.  This file
records the complementary comparison estimate for any two classical
trajectories which stay in the same a-priori ball.  It is an unconditional
application of Mathlib's Gronwall theorem and is the temporal uniqueness
consumer needed when a spatial DeTurck source is supplied later.
-/

namespace MorganTianLib
namespace ParabolicPDE

open Filter Function MeasureTheory Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace BanachVolterraProblem

variable (P : BanachVolterraProblem E)

/-- Two ball-valued classical trajectories for the same Volterra source obey
the usual exponential Gronwall estimate.  The derivative hypotheses are stated
on the closed interval, as produced by the Picard module; they are converted
to right derivatives at points below the endpoint by the order-topology
neighbourhood lemma. -/
theorem dist_le_of_classical_solutions
    {u v : ℝ → E}
    (hu_cont : ContinuousOn u (Icc (0 : ℝ) P.T))
    (hu_deriv : ∀ t ∈ Icc (0 : ℝ) P.T,
      HasDerivWithinAt u (P.source t (u t)) (Icc (0 : ℝ) P.T) t)
    (hu_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hv_cont : ContinuousOn v (Icc (0 : ℝ) P.T))
    (hv_deriv : ∀ t ∈ Icc (0 : ℝ) P.T,
      HasDerivWithinAt v (P.source t (v t)) (Icc (0 : ℝ) P.T) t)
    (hv_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    {δ : ℝ} (h0 : dist (u 0) (v 0) ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) P.T,
      dist (u t) (v t) ≤
        δ * Real.exp ((P.sourceLipschitz : ℝ) * t) := by
  intro t ht
  simpa only [sub_zero] using
    dist_le_of_trajectories_ODE_of_mem
      (v := P.source)
      (s := fun _ : ℝ => Metric.closedBall P.initial (P.radius : ℝ))
      (K := (P.sourceLipschitz : ℝ≥0))
      (f := u) (g := v) (a := (0 : ℝ)) (b := P.T)
      (fun τ hτ => P.source_lipschitzOn τ ⟨hτ.1, hτ.2.le⟩)
      hu_cont
      (fun τ hτ =>
        (hu_deriv τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem hτ))
      (fun τ hτ => hu_mem τ ⟨hτ.1, hτ.2.le⟩)
      hv_cont
      (fun τ hτ =>
        (hv_deriv τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem hτ))
      (fun τ hτ => hv_mem τ ⟨hτ.1, hτ.2.le⟩)
      h0 t ht

/-! The same comparison remains available when the trajectories only satisfy
the equation up to a uniformly bounded residual.  This is the form used when
the source map is perturbed by parameters or by a spatial approximation. -/

/-- Two ball-valued approximate trajectories are controlled by the explicit
Gronwall bound for the common Volterra source.  The residuals are measured
against the source along each trajectory, so this theorem also applies when
the two trajectories come from nearby source constructions. -/
theorem dist_le_of_approximate_classical_solutions
    {u v u' v' : ℝ → E} {εu εv δ : ℝ}
    (hu_cont : ContinuousOn u (Icc (0 : ℝ) P.T))
    (hu_deriv : ∀ t ∈ Icc (0 : ℝ) P.T,
      HasDerivWithinAt u (u' t) (Icc (0 : ℝ) P.T) t)
    (hu_residual : ∀ t ∈ Icc (0 : ℝ) P.T,
      dist (u' t) (P.source t (u t)) ≤ εu)
    (hu_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hv_cont : ContinuousOn v (Icc (0 : ℝ) P.T))
    (hv_deriv : ∀ t ∈ Icc (0 : ℝ) P.T,
      HasDerivWithinAt v (v' t) (Icc (0 : ℝ) P.T) t)
    (hv_residual : ∀ t ∈ Icc (0 : ℝ) P.T,
      dist (v' t) (P.source t (v t)) ≤ εv)
    (hv_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (h0 : dist (u 0) (v 0) ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) P.T,
      dist (u t) (v t) ≤
        gronwallBound δ (P.sourceLipschitz : ℝ) (εu + εv) t := by
  intro t ht
  simpa only [sub_zero] using
    dist_le_of_approx_trajectories_ODE_of_mem
      (v := P.source)
      (s := fun _ : ℝ => Metric.closedBall P.initial (P.radius : ℝ))
      (K := (P.sourceLipschitz : ℝ≥0))
      (f := u) (g := v) (f' := u') (g' := v')
      (a := (0 : ℝ)) (b := P.T) (εf := εu) (εg := εv)
      (δ := δ)
      (fun τ hτ => P.source_lipschitzOn τ ⟨hτ.1, hτ.2.le⟩)
      hu_cont
      (fun τ hτ =>
        (hu_deriv τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem hτ))
      (fun τ hτ => hu_residual τ ⟨hτ.1, hτ.2.le⟩)
      (fun τ hτ => hu_mem τ ⟨hτ.1, hτ.2.le⟩)
      hv_cont
      (fun τ hτ =>
        (hv_deriv τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem hτ))
      (fun τ hτ => hv_residual τ ⟨hτ.1, hτ.2.le⟩)
      (fun τ hτ => hv_mem τ ⟨hτ.1, hτ.2.le⟩)
      h0 t ht

/-! The reference-source version below is convenient for the selected Picard
trajectory.  Parameterized constructions also need the same conversion for a
second source, so expose the source-continuity hypotheses explicitly. -/

/-- A continuous trajectory satisfying a Duhamel equation for an arbitrary
source has the corresponding derivative on the closed construction interval.
The source only needs to be continuous on the product of that interval with
the prescribed invariant ball. -/
theorem hasDerivWithinAt_of_integral_equation_of_continuous
    {source : ℝ → E → E} {initial : E} {u : ℝ → E}
    (hsource_cont : ContinuousOn (Function.uncurry source)
      (Icc (0 : ℝ) P.T ×ˢ Metric.closedBall P.initial (P.radius : ℝ)))
    (hu_cont : ContinuousOn u (Icc (0 : ℝ) P.T))
    (hu_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hintegral : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t = initial + ∫ s in (0 : ℝ)..t, source s (u s))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) P.T) :
    HasDerivWithinAt u (source t (u t)) (Icc (0 : ℝ) P.T) t := by
  have hpicard := ODE.hasDerivWithinAt_picard_Icc
    (show (0 : ℝ) ∈ Icc (0 : ℝ) P.T from ⟨le_rfl, P.T_nonneg⟩)
    hsource_cont hu_cont hu_mem initial ht
  apply hpicard.congr_of_mem _ ht
  intro s hs
  simpa only [ODE.picard_apply] using hintegral s hs

/-! A useful specialization compares an exact trajectory for `P.source` with a
trajectory driven by a second source.  The latter is only required to stay in
the same a-priori ball and to be uniformly close to the reference source
there; its regularity is exposed through the explicit trajectory hypotheses. -/

/-- A classical trajectory for a uniformly perturbed source stays within the
explicit Grönwall distance of a classical trajectory for the reference source.

The source discrepancy is required only on the common invariant ball.  This is
the form needed for parameter or spatial-approximation stability, where the
second source need not itself be packaged as a `BanachVolterraProblem`. -/
theorem dist_le_of_source_perturbation
    {u v : ℝ → E} {source₂ : ℝ → E → E} {ε δ : ℝ}
    (hu_cont : ContinuousOn u (Icc (0 : ℝ) P.T))
    (hu_deriv : ∀ t ∈ Icc (0 : ℝ) P.T,
      HasDerivWithinAt u (P.source t (u t)) (Icc (0 : ℝ) P.T) t)
    (hu_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hv_cont : ContinuousOn v (Icc (0 : ℝ) P.T))
    (hv_deriv : ∀ t ∈ Icc (0 : ℝ) P.T,
      HasDerivWithinAt v (source₂ t (v t)) (Icc (0 : ℝ) P.T) t)
    (hv_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hsource_diff : ∀ t ∈ Icc (0 : ℝ) P.T,
      ∀ x ∈ Metric.closedBall P.initial (P.radius : ℝ),
        dist (source₂ t x) (P.source t x) ≤ ε)
    (h0 : dist (u 0) (v 0) ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) P.T,
      dist (u t) (v t) ≤
        gronwallBound δ (P.sourceLipschitz : ℝ) ε t := by
  intro t ht
  simpa only [zero_add] using
    (P.dist_le_of_approximate_classical_solutions
      (u := u) (v := v)
      (u' := fun s => P.source s (u s))
      (v' := fun s => source₂ s (v s))
      (εu := (0 : ℝ)) (εv := ε) (δ := δ)
      hu_cont hu_deriv
      (fun s hs => by simp)
      hu_mem
      hv_cont hv_deriv
      (fun s hs =>
        hsource_diff s ⟨hs.1, hs.2⟩ (v s)
          (hv_mem s ⟨hs.1, hs.2⟩))
      hv_mem h0 t ht)

/-- Two continuous Duhamel trajectories, one for the reference source and one
for a uniformly perturbed source, satisfy the explicit Gronwall comparison.
Unlike the derivative-level theorem above, this adapter asks only for the two
integral equations and continuity of the perturbed source on the common
invariant ball.  The second trajectory may start from a different initial
value, provided it remains in that ball. -/
theorem dist_le_of_integral_equations_source_perturbation
    {u v : ℝ → E} {source₂ : ℝ → E → E} {initial₂ : E}
    {ε δ : ℝ}
    (hsource₂_cont : ContinuousOn (Function.uncurry source₂)
      (Icc (0 : ℝ) P.T ×ˢ Metric.closedBall P.initial (P.radius : ℝ)))
    (hu_cont : ContinuousOn u (Icc (0 : ℝ) P.T))
    (hu_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hu_integral : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t = P.initial + ∫ s in (0 : ℝ)..t, P.source s (u s))
    (hv_cont : ContinuousOn v (Icc (0 : ℝ) P.T))
    (hv_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hv_integral : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t = initial₂ + ∫ s in (0 : ℝ)..t, source₂ s (v s))
    (hsource_diff : ∀ t ∈ Icc (0 : ℝ) P.T,
      ∀ x ∈ Metric.closedBall P.initial (P.radius : ℝ),
        dist (source₂ t x) (P.source t x) ≤ ε)
    (h0 : dist (u 0) (v 0) ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) P.T,
      dist (u t) (v t) ≤
        gronwallBound δ (P.sourceLipschitz : ℝ) ε t := by
  intro t ht
  exact P.dist_le_of_source_perturbation
    (u := u) (v := v) (source₂ := source₂) (ε := ε) (δ := δ)
    hu_cont
    (fun s hs => P.hasDerivWithinAt_of_integral_equation_of_continuous
      (source := P.source) (initial := P.initial) (u := u)
      P.toPicardLindelof.continuousOn_uncurry hu_cont hu_mem hu_integral hs)
    hu_mem
    hv_cont
    (fun s hs => P.hasDerivWithinAt_of_integral_equation_of_continuous
      (source := source₂) (initial := initial₂) (u := v)
      hsource₂_cont hv_cont hv_mem hv_integral hs)
    hv_mem hsource_diff h0 t ht

/-- The selected Picard trajectory admits the same integral-equation comparison
with a perturbed source.  This is the compact consumer form: only continuity,
ball membership, and the Duhamel identity of the competing trajectory remain
as inputs. -/
theorem solution_dist_le_of_integral_equation_source_perturbation
    {v : ℝ → E} {source₂ : ℝ → E → E} {initial₂ : E}
    {ε δ : ℝ}
    (hsource₂_cont : ContinuousOn (Function.uncurry source₂)
      (Icc (0 : ℝ) P.T ×ˢ Metric.closedBall P.initial (P.radius : ℝ)))
    (hv_cont : ContinuousOn v (Icc (0 : ℝ) P.T))
    (hv_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hv_integral : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t = initial₂ + ∫ s in (0 : ℝ)..t, source₂ s (v s))
    (hsource_diff : ∀ t ∈ Icc (0 : ℝ) P.T,
      ∀ x ∈ Metric.closedBall P.initial (P.radius : ℝ),
        dist (source₂ t x) (P.source t x) ≤ ε)
    (h0 : dist P.initial (v 0) ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) P.T,
      dist (P.solution t) (v t) ≤
        gronwallBound δ (P.sourceLipschitz : ℝ) ε t := by
  have h0' : dist (P.solution 0) (v 0) ≤ δ := by
    simpa only [P.solution_initial_trace] using h0
  exact P.dist_le_of_integral_equations_source_perturbation
    (u := P.solution) (v := v) (source₂ := source₂)
    (initial₂ := initial₂) (ε := ε) (δ := δ)
    hsource₂_cont
    P.continuous_solution.continuousOn
    (fun t ht => by
      rw [P.solution_eq_fixedPoint ⟨t, ht⟩]
      exact P.fixedPoint_mem_closedBall ⟨t, ht⟩)
    (fun t ht => P.solution_integral_equation ht)
    hv_cont hv_mem hv_integral hsource_diff h0'

/-! The zero-source-discrepancy specialization is the restart estimate for
the same evolution law with a perturbed initial value. -/

/-- A continuous ball-valued Duhamel trajectory for the reference source is
controlled by its initial discrepancy alone.  This is the temporal stability
bound used when a local construction is restarted at a nearby endpoint. -/
theorem solution_dist_le_of_initial_perturbation
    {v : ℝ → E} {initial₂ : E} {δ : ℝ}
    (hv_cont : ContinuousOn v (Icc (0 : ℝ) P.T))
    (hv_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hv_integral : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t = initial₂ + ∫ s in (0 : ℝ)..t, P.source s (v s))
    (h0 : dist P.initial (v 0) ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) P.T,
      dist (P.solution t) (v t) ≤
        gronwallBound δ (P.sourceLipschitz : ℝ) 0 t := by
  exact P.solution_dist_le_of_integral_equation_source_perturbation
    (source₂ := P.source) (initial₂ := initial₂) (ε := 0) (δ := δ)
    P.toPicardLindelof.continuousOn_uncurry hv_cont hv_mem hv_integral
    (fun _ _ _ _ => by simp) h0

/-! The comparison estimate is also useful before selecting the Picard fixed
point: two independently constructed Duhamel trajectories can be compared
directly. -/

/-- Two continuous ball-valued Duhamel trajectories for the same source obey
the explicit Grönwall estimate, without either trajectory being the selected
Picard solution. -/
theorem dist_le_of_integral_equations
    {u v : ℝ → E} {δ : ℝ}
    (hu_cont : ContinuousOn u (Icc (0 : ℝ) P.T))
    (hu_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hu_integral : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t = P.initial +
        ∫ s in (0 : ℝ)..t, P.source s (u s))
    (hv_cont : ContinuousOn v (Icc (0 : ℝ) P.T))
    (hv_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hv_integral : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t = P.initial +
        ∫ s in (0 : ℝ)..t, P.source s (v s))
    (h0 : dist (u 0) (v 0) ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) P.T,
      dist (u t) (v t) ≤
        gronwallBound δ (P.sourceLipschitz : ℝ) 0 t := by
  intro t ht
  have hdist := P.dist_le_of_classical_solutions
    hu_cont
    (fun s hs => P.hasDerivWithinAt_of_integral_equation_of_continuous
      (source := P.source) (initial := P.initial) (u := u)
      P.toPicardLindelof.continuousOn_uncurry hu_cont hu_mem hu_integral hs)
    hu_mem
    hv_cont
    (fun s hs => P.hasDerivWithinAt_of_integral_equation_of_continuous
      (source := P.source) (initial := P.initial) (u := v)
      P.toPicardLindelof.continuousOn_uncurry hv_cont hv_mem hv_integral hs)
    hv_mem h0 t ht
  by_cases hL : (P.sourceLipschitz : ℝ) = 0
  · simpa [gronwallBound, hL] using hdist
  · simpa [gronwallBound, hL] using hdist

/-- The selected Picard trajectory obeys the source-perturbation estimate
without requiring callers to repeat its continuity, derivative, ball, or
initial-trace facts. -/
theorem solution_dist_le_of_source_perturbation
    {v : ℝ → E} {source₂ : ℝ → E → E} {ε δ : ℝ}
    (hv_cont : ContinuousOn v (Icc (0 : ℝ) P.T))
    (hv_deriv : ∀ t ∈ Icc (0 : ℝ) P.T,
      HasDerivWithinAt v (source₂ t (v t)) (Icc (0 : ℝ) P.T) t)
    (hv_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      v t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hsource_diff : ∀ t ∈ Icc (0 : ℝ) P.T,
      ∀ x ∈ Metric.closedBall P.initial (P.radius : ℝ),
        dist (source₂ t x) (P.source t x) ≤ ε)
    (h0 : dist P.initial (v 0) ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) P.T,
      dist (P.solution t) (v t) ≤
        gronwallBound δ (P.sourceLipschitz : ℝ) ε t := by
  have h0' : dist (P.solution 0) (v 0) ≤ δ := by
    simpa only [P.solution_initial_trace] using h0
  exact P.dist_le_of_source_perturbation
    (u := P.solution) (v := v) (source₂ := source₂)
    P.continuous_solution.continuousOn
    (fun t ht => P.solution_hasDerivWithinAt ht)
    (fun t ht => by
      rw [P.solution_eq_fixedPoint ⟨t, ht⟩]
      exact P.fixedPoint_mem_closedBall ⟨t, ht⟩)
    hv_cont hv_deriv hv_mem hsource_diff h0'

/-- A continuous ball-valued solution of the Duhamel equation is automatically
a classical solution on the closed interval. -/
theorem hasDerivWithinAt_of_integral_equation
    {u : ℝ → E}
    (hu_cont : ContinuousOn u (Icc (0 : ℝ) P.T))
    (hu_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hintegral : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t = P.initial +
        ∫ s in (0 : ℝ)..t, P.source s (u s))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) P.T) :
    HasDerivWithinAt u (P.source t (u t)) (Icc (0 : ℝ) P.T) t := by
  have hpicard := ODE.hasDerivWithinAt_picard_Icc
    (show (0 : ℝ) ∈ Icc (0 : ℝ) P.T from ⟨le_rfl, P.T_nonneg⟩)
    P.toPicardLindelof.continuousOn_uncurry hu_cont hu_mem P.initial ht
  apply hpicard.congr_of_mem _ ht
  intro s hs
  simpa only [ODE.picard_apply] using hintegral s hs

/-! The integral-equation form is often the one available at a nonlinear
construction boundary.  Expose the corresponding quantitative estimate
directly, rather than requiring each consumer to first package the trajectory
as a classical solution. -/

/-- A continuous ball-valued Duhamel trajectory for the reference source is
within the explicit Gronwall distance of the selected Picard trajectory. -/
theorem solution_dist_le_of_integral_equation
    {u : ℝ → E} {δ : ℝ}
    (hu_cont : ContinuousOn u (Icc (0 : ℝ) P.T))
    (hu_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hintegral : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t = P.initial +
        ∫ s in (0 : ℝ)..t, P.source s (u s))
    (h0 : dist P.initial (u 0) ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) P.T,
      dist (P.solution t) (u t) ≤
        gronwallBound δ (P.sourceLipschitz : ℝ) 0 t := by
  exact P.solution_dist_le_of_source_perturbation
    (source₂ := P.source) (ε := 0) (δ := δ)
    hu_cont
    (fun t ht => P.hasDerivWithinAt_of_integral_equation
      hu_cont hu_mem hintegral ht)
    hu_mem
    (fun t ht x hx => by simp)
    h0

/-- The Picard trajectory is the unique ball-valued classical trajectory with
the prescribed initial value. -/
theorem classical_solution_unique
    {u : ℝ → E}
    (hu_cont : ContinuousOn u (Icc (0 : ℝ) P.T))
    (hu_deriv : ∀ t ∈ Icc (0 : ℝ) P.T,
      HasDerivWithinAt u (P.source t (u t)) (Icc (0 : ℝ) P.T) t)
    (hu_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hu_initial : u 0 = P.initial) :
    EqOn u P.solution (Icc (0 : ℝ) P.T) := by
  intro t ht
  have hsolution_cont : ContinuousOn P.solution (Icc (0 : ℝ) P.T) :=
    P.continuous_solution.continuousOn
  have hsolution_deriv : ∀ τ ∈ Icc (0 : ℝ) P.T,
      HasDerivWithinAt P.solution
        (P.source τ (P.solution τ)) (Icc (0 : ℝ) P.T) τ := by
    intro τ hτ
    exact P.solution_hasDerivWithinAt hτ
  have hsolution_mem : ∀ τ ∈ Icc (0 : ℝ) P.T,
      P.solution τ ∈ Metric.closedBall P.initial (P.radius : ℝ) := by
    intro τ hτ
    rw [P.solution_eq_fixedPoint ⟨τ, hτ⟩]
    exact P.fixedPoint_mem_closedBall ⟨τ, hτ⟩
  have hdist := P.dist_le_of_classical_solutions
    hu_cont hu_deriv hu_mem
    hsolution_cont hsolution_deriv hsolution_mem
    (δ := 0) (by simp [hu_initial, P.solution_initial_trace])
    t ht
  have hz : (0 : ℝ) * Real.exp ((P.sourceLipschitz : ℝ) * t) = 0 := by
    simp
  have : dist (u t) (P.solution t) ≤ 0 := by simpa [hz] using hdist
  exact dist_le_zero.mp this

/-- The Duhamel equation itself has at most one continuous solution that stays
in the a-priori ball, and that solution is the Picard trajectory. -/
theorem integral_solution_unique
    {u : ℝ → E}
    (hu_cont : ContinuousOn u (Icc (0 : ℝ) P.T))
    (hu_mem : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t ∈ Metric.closedBall P.initial (P.radius : ℝ))
    (hintegral : ∀ t ∈ Icc (0 : ℝ) P.T,
      u t = P.initial +
        ∫ s in (0 : ℝ)..t, P.source s (u s)) :
    EqOn u P.solution (Icc (0 : ℝ) P.T) := by
  apply P.classical_solution_unique hu_cont
    (fun t ht => P.hasDerivWithinAt_of_integral_equation
      hu_cont hu_mem hintegral ht)
    hu_mem
  simpa using hintegral 0 ⟨le_rfl, P.T_nonneg⟩

end BanachVolterraProblem

end
end ParabolicPDE
end MorganTianLib

