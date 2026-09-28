import PetersenLib.Ch05.ExponentialMap

/-!
# Petersen Ch. 5, §5.5 — the radial distance function

Blueprint node `def:pet-ch5-radial-distance-function`.  On the normal
neighbourhood `U = exp_p(B(0,ε)) ⊆ M`, the **radial distance function**
`r(x) = |exp_p⁻¹(x)|` records the Euclidean length in `T_pM` of the unique small
tangent vector `w` (with `‖w‖ < ρ`) whose exponential image is `x`.

Here `ρ > 0` is the injectivity radius witness furnished by
`expMap_localDiffeomorphism`: `exp_p` is a diffeomorphism of `B(0, ρ) ⊆ T_pM`
onto its image, so `exp_p⁻¹` is well defined on the normal ball and `r` is the
composition `x ↦ ‖exp_p⁻¹ x‖`.  We realise `exp_p⁻¹` with `Function.invFunOn`
over `B(0, ρ)`; on the normal ball this genuinely inverts `exp_p` (the
characterising lemma `radialDistanceFunction_expMap`), so `r` is not vacuous.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** The radius `ρ > 0` of the normal ball around `p`, extracted from
`expMap_localDiffeomorphism` (Petersen Prop. 5.5.1): on `B(0, ρ) ⊆ T_pM` the map
`exp_p` is injective, lands in the exponential domain, and is a local
diffeomorphism. -/
def normalRadius (g : RiemannianMetric I M) (p : M) : ℝ :=
  Classical.choose (expMap_localDiffeomorphism (I := I) g p)

theorem normalRadius_pos (g : RiemannianMetric I M) (p : M) :
    0 < normalRadius (I := I) g p :=
  (Classical.choose_spec (expMap_localDiffeomorphism (I := I) g p)).1

/-- `exp_p` is injective on the normal ball `B(0, normalRadius g p)`. -/
theorem injOn_expMap_normalBall (g : RiemannianMetric I M) (p : M) :
    Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
      (Metric.ball (0 : E) (normalRadius (I := I) g p)) :=
  (Classical.choose_spec (expMap_localDiffeomorphism (I := I) g p)).2.2.1

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-radial-distance-function`, §5.5): the
**radial distance function** `r(x) = |exp_p⁻¹(x)|` on the normal neighbourhood
`U = exp_p(B(0, ρ))`.  For `x = exp_p(w)` with `‖w‖ < ρ` it returns the Euclidean
length `‖w‖` of the (unique) preimage `w ∈ T_pM`; here `exp_p⁻¹` is realised as
`Function.invFunOn` of `exp_p` over the normal ball `B(0, ρ)`, on which `exp_p`
is injective (`injOn_expMap_normalBall`).  See `radialDistanceFunction_expMap`
for the defining identity `r(exp_p w) = ‖w‖`. -/
def radialDistanceFunction (g : RiemannianMetric I M) (p : M) : M → ℝ :=
  fun x => ‖Function.invFunOn
    (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
    (Metric.ball (0 : E) (normalRadius (I := I) g p)) x‖

/-- **Math.** Faithfulness of `radialDistanceFunction` (Petersen §5.5): on the
normal ball, `r ∘ exp_p` is the Euclidean length, i.e.
`r(exp_p w) = ‖w‖` whenever `‖w‖ < ρ`.  This exhibits `r` as `‖exp_p⁻¹(·)‖` on
`U = exp_p(B(0, ρ))`, so the definition is not vacuous. -/
theorem radialDistanceFunction_expMap (g : RiemannianMetric I M) (p : M)
    (w : E) (hw : ‖w‖ < normalRadius (I := I) g p) :
    radialDistanceFunction (I := I) g p
      (expMap (I := I) g p (w : TangentSpace I p)) = ‖w‖ := by
  have hmem : w ∈ Metric.ball (0 : E) (normalRadius (I := I) g p) :=
    mem_ball_zero_iff.mpr hw
  have hinv := (injOn_expMap_normalBall (I := I) g p).leftInvOn_invFunOn hmem
  simp only [radialDistanceFunction]
  rw [hinv]

end PetersenLib

end
