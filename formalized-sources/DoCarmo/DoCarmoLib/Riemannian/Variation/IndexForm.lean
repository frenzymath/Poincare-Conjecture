import DoCarmoLib.Riemannian.Variation.CovariantField
import DoCarmoLib.Riemannian.Connection.CurvaturePointwise
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2

/-!
# The index form `I_a(V, V)` (do Carmo Ch. 9, §2, Remark 2.10)

do Carmo, *Riemannian Geometry*, Ch. 9, §2, Remark 2.10 introduces, for a geodesic
`γ : [0, a] → M` and a field `V` along it, the **index form**
$$I_a(V, V) = \int_0^a \Big\{\langle V', V'\rangle - \langle R(\gamma', V)\gamma', V\rangle\Big\}\,dt,$$
"for reasons which will be clear later" — it is the quadratic form that Ch. 10 and
Ch. 11 study in its own right, and by formula (6) of that remark it computes
`E''(0)/2` for a proper variation.

The same remark opens with the differentiation identity
$$\frac{d}{dt}\Big\langle V, \frac{DV}{dt}\Big\rangle
  = \Big\langle V, \frac{D^2V}{dt^2}\Big\rangle + \Big\langle\frac{DV}{dt}, \frac{DV}{dt}\Big\rangle,$$
which is what turns formula (5) (`rem:dc-ch9-2-9`) into formula (6).  That identity
is `hasDerivAt_metricInner_covariantDeriv` below: it is the manifold Leibniz rule
`IsCovariantDerivFieldAlongOn.hasDerivAt_metricInner` (do Carmo Ch. 2, Prop. 3.2)
applied to the pairs `(V, DV)` and `(DV, D²V)`.

## The `D/dt`-as-a-second-field discipline

`V'` is `DV`, carried as a **second field** constrained by
`IsCovariantDerivFieldAlongOn` (see `Variation/CovariantField.lean`): DoCarmoLib has
no intrinsic manifold-level `D/dt` operator to apply, so the index form takes the
pair `(V, DV)` rather than `V` alone.  `D²V/dt²` is a third field `D2V`, related to
`DV` by the same predicate.

## Curvature sign

`AffineConnection.curvatureFormAt g p x y z t = ⟨R(x, y)z, t⟩_g` with
`R(X, Y)Z = ∇_Y∇_X Z − ∇_X∇_Y Z + ∇_{[X,Y]}Z` (`DoCarmoCh4.lean`), which is do
Carmo's Ch. 4 Def. 2.1 convention on the nose.  So do Carmo's
`⟨R(γ', V)γ', V⟩` is `curvatureFormAt g (γ t) (γ' t) (V t) (γ' t) (V t)`, used
verbatim below.  (Beware: the `christoffelCurvature`/`chartCurvature` layer used by
the Jacobi files is the *Morgan–Tian* convention, `= −R_doCarmo`; it is not used
here.)

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, §2, Remark 2.10.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### The differentiation identity of do Carmo Remark 2.10 -/

/-- **Math.** do Carmo Ch. 9, §2, Remark 2.10, the opening identity: on an interval
where `V` is differentiable,
$$\frac{d}{dt}\Big\langle V, \frac{DV}{dt}\Big\rangle
  = \Big\langle\frac{DV}{dt}, \frac{DV}{dt}\Big\rangle
    + \Big\langle V, \frac{D^2V}{dt^2}\Big\rangle.$$

This is exactly the metric-compatibility Leibniz rule (do Carmo Ch. 2, Prop. 3.2)
`IsCovariantDerivFieldAlongOn.hasDerivAt_metricInner` applied to the pair `(V, DV)`
against the pair `(DV, D²V)` — the step that converts formula (5)
(`rem:dc-ch9-2-9`) into formula (6) via the index form. -/
theorem hasDerivAt_metricInner_covariantDeriv
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV D2V : ℝ → E} {a b : ℝ}
    (hV : IsCovariantDerivFieldAlongOn (I := I) g γ V DV a b)
    (hDV : IsCovariantDerivFieldAlongOn (I := I) g γ DV D2V a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => g.metricInner (γ s) (V s : TangentSpace I (γ s)) (DV s))
      (g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (DV t)
        + g.metricInner (γ t) (V t : TangentSpace I (γ t)) (D2V t)) t :=
  hV.hasDerivAt_metricInner hDV hdiff hγc ht

/-! ### The index form -/

/-- **Math.** do Carmo Ch. 9, §2, Remark 2.10.  **The index form**
$$I_a(V, V) = \int_0^a\Big\{\langle V', V'\rangle - \langle R(\gamma', V)\gamma', V\rangle\Big\}\,dt$$
of a field `V` along `γ`, whose covariant derivative `V' = DV/dt` is carried as the
second field `DV` (do Carmo's `V'`).

`⟨R(γ', V)γ', V⟩` is `curvatureFormAt g (γ t) (γ' t) (V t) (γ' t) (V t)`, in do
Carmo's Ch. 4 Def. 2.1 curvature convention, and `γ'` is the velocity `DCVelocity`
of do Carmo Ch. 1 Def. 2.9.

This is only a *definition*: the identity `I_a(V, V) = E''(0)/2` for a proper
variation is formula (6) of the same remark, which rests on the second variation
formula `prop:dc-ch9-2-8`. -/
def indexForm (g : RiemannianMetric I M) (γ : ℝ → M) (V DV : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (DV t)
    - g.leviCivitaConnection.curvatureFormAt g (γ t)
        (DCVelocity (I := I) γ t) (V t : TangentSpace I (γ t))
        (DCVelocity (I := I) γ t) (V t))

/-- **Math.** The index form, unfolded to its defining integral. -/
theorem indexForm_def (g : RiemannianMetric I M) (γ : ℝ → M) (V DV : ℝ → E)
    (a b : ℝ) :
    indexForm (I := I) g γ V DV a b
      = ∫ t in a..b, (g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (DV t)
          - g.leviCivitaConnection.curvatureFormAt g (γ t)
              (DCVelocity (I := I) γ t) (V t : TangentSpace I (γ t))
              (DCVelocity (I := I) γ t) (V t)) := rfl

/-- **Math.** The index form of the zero field vanishes: both integrands are
multilinear in `V`, resp. `DV`. -/
@[simp] theorem indexForm_zero (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    indexForm (I := I) g γ 0 0 a b = 0 := by
  rw [indexForm_def]
  have h : ∀ t : ℝ, (g.metricInner (γ t) ((0 : ℝ → E) t : TangentSpace I (γ t))
        ((0 : ℝ → E) t)
      - g.leviCivitaConnection.curvatureFormAt g (γ t)
          (DCVelocity (I := I) γ t) ((0 : ℝ → E) t : TangentSpace I (γ t))
          (DCVelocity (I := I) γ t) ((0 : ℝ → E) t)) = 0 := by
    intro t
    show g.metricInner (γ t) (0 : TangentSpace I (γ t)) 0
      - g.leviCivitaConnection.curvatureFormAt g (γ t)
          (DCVelocity (I := I) γ t) (0 : TangentSpace I (γ t))
          (DCVelocity (I := I) γ t) 0 = 0
    rw [AffineConnection.curvatureFormAt]
    simp [RiemannianMetric.metricInner]
  simp only [h]
  simp

end Riemannian.Variation
