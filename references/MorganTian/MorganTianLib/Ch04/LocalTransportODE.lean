import MorganTianLib.Ch04.ParallelTransportReparam

/-!
# Coordinate ODE identification of local parallel transport

An operator solution of the chart parallel equation, evaluated after the
canonical smooth change of parameter, agrees with the declared local
Levi-Civita tangent transport.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

private theorem localTransportTangentBetween_apply_model
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) {p q : M}
    (hp : c a = p) (hq : c b = q) (v : E) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (parallelTransportTangentBetween g hab hc hp hq v : E) =
      parallelTransportTangentEquiv g hab hc v := by
  subst p q
  rfl

/-- **Math.** The chart reading of the canonical local endpoint transport is
the endpoint value of any operator solution of its parallel equation. -/
theorem localLeviCivitaTangentTransport_chart_eq_of_ode
    (g : RiemannianMetric I M) (p : M) {U : Set M}
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x)
    (x : U) {τ : ℝ} (hτ : 0 < τ) (d : E) (P : ℝ → E →L[ℝ] E)
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hsrc : ∀ t : ℝ, localTransportCurve (I := I) p x t ∈ (chartAt H p).source)
    (hcoord : ∀ t : ℝ, extChartAt I p (localTransportCurve (I := I) p x t) =
      extChartAt I p p + (τ * Real.smoothTransition t) • d)
    (hP : ∀ s ∈ Icc (0 : ℝ) τ,
      HasDerivWithinAt P
        (-((Jacobi.chartChristoffelBilin (I := I) g p
          (extChartAt I p p + s • d) d).comp (P s))) (Icc (0 : ℝ) τ) s) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ v : E, tangentCoordChange I (x : M) p (x : M)
      (localLeviCivitaTangentTransport g p hC x v) = P τ v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro v
  let c : ℝ → M := localTransportCurve (I := I) p x
  let r : ℝ → ℝ := fun t => τ * Real.smoothTransition t
  let r' : ℝ → ℝ := fun t => τ * deriv Real.smoothTransition t
  let w : ℝ → E := fun t => P (r t) v
  let V : ∀ t, TangentSpace I (c t) := fun t =>
    tangentCoordChange I p (c t) (c t) (w t)
  have hrep (t : ℝ) : chartFieldRep (I := I) c p V t = w t :=
    Jacobi.tangentCoordChange_realize_self (I := I) (hsrc t) (w t)
  have hrange : MapsTo r (Icc (0 : ℝ) 1) (Icc (0 : ℝ) τ) := by
    intro t _
    exact ⟨mul_nonneg hτ.le (Real.smoothTransition.nonneg t),
      (mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one t) hτ.le).trans
        (by simp)⟩
  have hr (t : ℝ) : HasDerivWithinAt r (r' t) (Icc (0 : ℝ) 1) t := by
    exact (((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) t).hasDerivAt.const_mul
      τ).hasDerivWithinAt
  have hV : IsParallelWithinSolOn (I := I) g p c V 0 1 := by
    intro t ht
    refine ⟨r' t • d, ?_, ?_⟩
    · have hc := (hasDerivWithinAt_const t (Icc (0 : ℝ) 1) (extChartAt I p p)).add
        ((hr t).smul_const d)
      simpa only [zero_add] using hc.congr (fun s _ => hcoord s) (hcoord t)
    · have hoperator := (hP (r t) (hrange ht)).scomp t (hr t) hrange
      have hfield := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivWithinAt
        t hoperator
      have hw : HasDerivWithinAt w
          (-Geodesic.chartChristoffelContraction (I := I) g p
            (r' t • d) (w t) (extChartAt I p p + r t • d))
          (Icc (0 : ℝ) 1) t := by
        simpa only [w, Function.comp_def,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
          smul_apply, neg_apply,
          ← Jacobi.chartChristoffelBilin_apply, map_smul, smul_neg] using hfield
      rw [hrep t, hcoord t]
      exact hw.congr (fun s _ => hrep s) (hrep t)
  have hV0 : (V 0 : E) = v := by
    change tangentCoordChange I p (c 0) (c 0) (w 0) = v
    rw [show c 0 = p from (hC x x.property).2.1]
    have hw0 : w 0 = v := by simp [w, r, hP0]
    rw [hw0]
    exact tangentCoordChange_self (mem_extChartAt_source p)
  have hend := parallelTransportTangentEquiv_apply_eq_of_isParallelAlongWithinOn
    g (by norm_num : (0 : ℝ) < 1) (hC x x.property).1
      (isParallelAlongWithinOn_of_single_chart (by norm_num : (0 : ℝ) < 1)
        (fun t _ => hsrc t) hV)
  rw [hV0] at hend
  have hmodel : (localLeviCivitaTangentTransport g p hC x v : E) =
      parallelTransportTangentEquiv g (by norm_num : (0 : ℝ) < 1)
        (hC x x.property).1 v := by
    exact localTransportTangentBetween_apply_model g
      (by norm_num : (0 : ℝ) < 1) (hC x x.property).1
      (hC x x.property).2.1 (hC x x.property).2.2 v
  rw [hmodel, hend]
  have hread := hrep 1
  simpa [chartFieldRep, c, (hC x x.property).2.2, w, r] using hread

end MorganTianLib
