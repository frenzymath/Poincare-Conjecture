import PetersenLib.Ch06.JacobiFields

/-!
# Petersen Ch. 6, Exercise 6.7.3 — Fermi–Walker transport

`rem:pet-ch6-ex-6-7-3` (`PetersenLib.exercise_6_7_3`).  Let `c` have nonvanishing
speed and `T = ċ/|ċ|`.  A field `V` along `c` is a **Fermi–Walker field** when
$$
  \dot V = g(V,T)\,\dot T - g(V,\dot T)\,T = (T \wedge \dot T)(V) .
$$
Petersen asks for four facts: (1) existence and uniqueness given `V(t₀)`; (2) `T`
is a Fermi–Walker field; (3) `g(V,W)` is constant for Fermi–Walker `V, W`; (4) if
`c` is a geodesic (so `T` is parallel), Fermi–Walker fields are parallel.

## Scope of this file

The definition and parts (2), (3), (4) are here — all chart-free, resting on the
metric product rule `hasDerivAt_inner_along`.  Part (3) is landed in its sharp
infinitesimal form `d/dt g(V,W) = 0` (constancy on an interval then follows from
`is_const_of_deriv_eq_zero`), mirroring the sibling
`hasDerivAt_inner_eq_zero_of_isParallelAlong`.  Part (1) (existence/uniqueness) is
a linear-ODE statement for the inhomogeneous field `X ↦ g(X,T)Ṫ − g(X,Ṫ)T`; its
engine exists (`LinearODE`) but the plumbing is separate infrastructure, so it is
deferred and this node is **not** `\leanok` yet.  `T` is carried as an explicit
unit field (the intended `T = ċ/|ċ|`); its unit and parallel properties enter as
hypotheses.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** Petersen Ex. 6.7.3: `V` is a **Fermi–Walker field** along `c` with
respect to the unit tangent `T` (`T = ċ/|ċ|`) when
`V̇ = g(V,T)·Ṫ − g(V,Ṫ)·T`, where `Ṫ = derivAlongCurve g c T`.  Chart-free: `V̇`,
`Ṫ` are `derivAlongCurve` and `g(·,·)` is `metricInner`.  `T` is an explicit
field; its unit / parallel properties enter parts (2), (4) as hypotheses. -/
def IsFermiWalkerField (g : RiemannianMetric I M) (c : ℝ → M)
    (T V : ∀ t, TangentSpace I (c t)) : Prop :=
  ∀ t, derivAlongCurve (I := I) g c V t
      = g.metricInner (c t) (V t) (T t) • derivAlongCurve (I := I) g c T t
        - g.metricInner (c t) (V t) (derivAlongCurve (I := I) g c T t) • T t

/-! ### Part (2): the unit tangent `T` is itself a Fermi–Walker field -/

/-- **Math.** Differentiating `g(T,T) ≡ 1` gives `g(T,Ṫ) = 0` (product rule + a
constant has zero derivative). -/
theorem metricInner_tangent_deriv_eq_zero (g : RiemannianMetric I M) {c : ℝ → M}
    (T : ∀ t, TangentSpace I (c t)) (α : M) {t : ℝ}
    (hc : ContinuousAt c t) (hsrc : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hT : DifferentiableAt ℝ (chartFieldRep (I := I) c α T) t)
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (extChartAt I α (c t)))
    (hunit : ∀ s, g.metricInner (c s) (T s) (T s) = 1) :
    g.metricInner (c t) (T t) (derivAlongCurve (I := I) g c T t) = 0 := by
  have hprod := hasDerivAt_inner_along (I := I) g (V := T) (W := T) α hc hsrc hu hT hT hG
  have hconst : HasDerivAt (fun τ => g.inner (c τ) (T τ) (T τ)) 0 t := by
    have hfun : (fun τ => g.inner (c τ) (T τ) (T τ)) = fun _ => (1 : ℝ) := by
      funext τ; exact hunit τ
    rw [hfun]; exact hasDerivAt_const t 1
  have hsum := hprod.unique hconst
  have hcomm : g.inner (c t) (derivAlongCurve (I := I) g c T t) (T t)
             = g.inner (c t) (T t) (derivAlongCurve (I := I) g c T t) :=
    g.metricInner_comm (c t) _ _
  rw [hcomm] at hsum
  have h2 : (2 : ℝ) * g.metricInner (c t) (T t) (derivAlongCurve (I := I) g c T t) = 0 := by
    have := hsum
    simp only [RiemannianMetric.metricInner_apply] at this ⊢
    linarith [this]
  linarith [h2]

/-- **Part (2).** `T` itself is a Fermi–Walker field. -/
theorem isFermiWalkerField_tangent (g : RiemannianMetric I M) {c : ℝ → M}
    (T : ∀ t, TangentSpace I (c t)) (α : M)
    (hc : ∀ t, ContinuousAt c t) (hsrc : ∀ t, c t ∈ (chartAt H α).source)
    (hu : ∀ t, DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hT : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c α T) t)
    (hG : ∀ t, ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (extChartAt I α (c t)))
    (hunit : ∀ t, g.metricInner (c t) (T t) (T t) = 1) :
    IsFermiWalkerField (I := I) g c T T := by
  intro t
  have hperp := metricInner_tangent_deriv_eq_zero (I := I) g T α (hc t) (hsrc t) (hu t)
    (hT t) (hG t) hunit
  rw [hunit t, one_smul, hperp, zero_smul, sub_zero]

/-! ### Part (3): `g(V,W)` is (infinitesimally) constant for Fermi–Walker fields -/

/-- **Part (3).** For Fermi–Walker fields `V, W`, `d/dt g(V,W) = 0` — the four
cross terms cancel by the `g`-skewness of `X ↦ g(X,T)Ṫ − g(X,Ṫ)T`.  Constancy on
an interval follows by `is_const_of_deriv_eq_zero`. -/
theorem hasDerivAt_metricInner_fermiWalker_zero (g : RiemannianMetric I M) {c : ℝ → M}
    (T V W : ∀ t, TangentSpace I (c t)) (α : M) {t : ℝ}
    (hc : ContinuousAt c t) (hsrc : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c α W) t)
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (extChartAt I α (c t)))
    (hVfw : IsFermiWalkerField (I := I) g c T V)
    (hWfw : IsFermiWalkerField (I := I) g c T W) :
    HasDerivAt (fun τ => g.metricInner (c τ) (V τ) (W τ)) 0 t := by
  have hprod := hasDerivAt_inner_along (I := I) g (V := V) (W := W) α hc hsrc hu hV hW hG
  have key : g.inner (c t) (derivAlongCurve (I := I) g c V t) (W t)
           + g.inner (c t) (V t) (derivAlongCurve (I := I) g c W t) = 0 := by
    rw [hVfw t, hWfw t]
    simp only [← RiemannianMetric.metricInner_apply,
      g.metricInner_sub_left, g.metricInner_sub_right,
      g.metricInner_smul_left, g.metricInner_smul_right]
    rw [g.metricInner_comm (c t) (derivAlongCurve (I := I) g c T t) (W t),
        g.metricInner_comm (c t) (T t) (W t),
        g.metricInner_comm (c t) (V t) (T t),
        g.metricInner_comm (c t) (V t) (derivAlongCurve (I := I) g c T t)]
    ring
  rw [key] at hprod
  simpa only [RiemannianMetric.metricInner_apply] using hprod

/-! ### Part (4): if the tangent is parallel (e.g. `c` a geodesic), FW fields are parallel -/

/-- **Part (4), core.** If `Ṫ = 0` (`T` parallel — which for `T = ċ/|ċ|` holds
along a geodesic), every Fermi–Walker field is parallel. -/
theorem isParallelAlong_of_isFermiWalkerField (g : RiemannianMetric I M) {c : ℝ → M}
    {T V : ∀ t, TangentSpace I (c t)}
    (hTpar : IsParallelAlong (I := I) g c T)
    (hVfw : IsFermiWalkerField (I := I) g c T V) :
    IsParallelAlong (I := I) g c V := by
  intro t
  rw [hVfw t, hTpar t, smul_zero, g.metricInner_zero_right, zero_smul, sub_zero]

/-! ### Bundled statement (parts 2, 3, 4) -/

/-- **Ex. 6.7.3**, parts (2), (3), (4).  (2) `T` is a Fermi–Walker field; (3)
`g(V,W)` has zero derivative for Fermi–Walker `V, W`; (4) Fermi–Walker fields are
parallel when `T` is.  Part (1) (existence and uniqueness given `V(t₀)`) is a
separate linear-ODE statement, deferred (see the module docstring). -/
theorem exercise_6_7_3 (g : RiemannianMetric I M) {c : ℝ → M}
    (T : ∀ t, TangentSpace I (c t)) (α : M)
    (hc : ∀ t, ContinuousAt c t) (hsrc : ∀ t, c t ∈ (chartAt H α).source)
    (hu : ∀ t, DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hT : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c α T) t)
    (hG : ∀ t, ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (extChartAt I α (c t)))
    (hunit : ∀ t, g.metricInner (c t) (T t) (T t) = 1) :
    IsFermiWalkerField (I := I) g c T T ∧
    (∀ (V W : ∀ t, TangentSpace I (c t)),
      (∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t) →
      (∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) c α W) t) →
      IsFermiWalkerField (I := I) g c T V → IsFermiWalkerField (I := I) g c T W →
      ∀ t, HasDerivAt (fun τ => g.metricInner (c τ) (V τ) (W τ)) 0 t) ∧
    (∀ (V : ∀ t, TangentSpace I (c t)),
      IsParallelAlong (I := I) g c T → IsFermiWalkerField (I := I) g c T V →
      IsParallelAlong (I := I) g c V) :=
  ⟨isFermiWalkerField_tangent (I := I) g T α hc hsrc hu hT hG hunit,
   fun V W hVd hWd hVfw hWfw t =>
     hasDerivAt_metricInner_fermiWalker_zero (I := I) g T V W α
       (hc t) (hsrc t) (hu t) (hVd t) (hWd t) (hG t) hVfw hWfw,
   fun V hTpar hVfw => isParallelAlong_of_isFermiWalkerField (I := I) g hTpar hVfw⟩

end PetersenLib

end
