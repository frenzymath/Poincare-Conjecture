import PetersenLib.Ch06.BonnetSynge
import PetersenLib.Ch06.SecondVariationGlobal
import PetersenLib.Ch06.SecBounds

/-!
# Petersen Ch. 6, §6.3 — Bonnet–Synge: the sin-field second variation is negative

`Ch06/BonnetSynge.lean` proved the scalar core `bonnetSynge_index_core`.  This file supplies
the **geometric half** of Lemma 6.3.1 (`lem:pet-ch6-bonnet-synge-diameter`): the second
variation of energy of the exponential variation with field `V(t) = sin(π t/l) E(t)` — for
`E` a *unit parallel* field *perpendicular* to a unit-speed geodesic — is strictly negative
once `l > π/√k` under `sec ≥ k > 0`, so `c` is not locally minimizing.

The heart is `bonnetSynge_variation_integrand`: the Synge integrand of Thm. 6.1.4
(`secondVariationEnergy_properVariation`) for this field equals, pointwise,

$$g(\dot V,\dot V) - g(R(V,\dot c)\dot c, V)
  = \Big(\frac\pi l\Big)^2\cos^2\Big(\frac\pi l t\Big) - \sin^2\Big(\frac\pi l t\Big)\sec(E,\dot c).$$

The `V̇ = (π/l)\cos(πt/l)E` step is the covariant Leibniz rule `derivAlongCurve_smul_fun`
(the `E`-term dies because `E` is parallel); the curvature step is `curvatureTensorAt`
linearity, the pointwise `IsAlgCurvatureForm` pair-swap, and the `sec` bridge with
`|E∧ċ|² = 1` from `E` unit ⟂ unit-speed `ċ`.

Then `bonnetSynge_longGeodesicsNotMinimizing` integrates that identity and feeds
`bonnetSynge_index_core`.

## Honest scope

The variation `f` and its joint slab smoothness (`hf`) enter as hypotheses, not conclusions:
producing a smooth `f` with `variationField f = sin(π·/l)E` is the exponential-variation
slab-smoothness fact of `Ch06/ExpVariation.lean`, which is a separate (and much harder)
analytic problem — see that file's docstring.  What is proven here is exactly Petersen's
computation: *given such a variation*, its second variation is negative.  The integrability of
the sectional-curvature weight (`hint`) is likewise assumed; it holds because the fields are
smooth.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval Real

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** `d/dt sin(π t/l) = (π/l)cos(π t/l)` — the derivative of the sin window. -/
theorem hasDerivAt_sin_window {l : ℝ} (t : ℝ) :
    HasDerivAt (fun s => Real.sin (π / l * s)) (Real.cos (π / l * t) * (π / l)) t := by
  have h1 : HasDerivAt (fun s : ℝ => π / l * s) (π / l) t := by
    simpa using (hasDerivAt_id t).const_mul (π / l)
  simpa using h1.sin

/-- **Math.** The pointwise Synge integrand for the Bonnet–Synge field `V = sin(π·/l) E`. -/
theorem bonnetSynge_variation_integrand
    (g : RiemannianMetric I M) {l : ℝ}
    {f : ℝ → ℝ → M} {Efield : ∀ t, TangentSpace I (f 0 t)}
    (hEpar : IsParallelAlong (I := I) g (f 0) Efield)
    (hEdiff : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) (f 0) (f 0 t) Efield) t)
    (hEunit : ∀ t, g.metricInner (f 0 t) (Efield t) (Efield t) = 1)
    (hEperp : ∀ t, g.metricInner (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t) = 0)
    (hspeed : ∀ t, g.metricInner (f 0 t) (curveVelocity (I := I) (f 0) t)
      (curveVelocity (I := I) (f 0) t) = 1)
    (hVfield : variationField (I := I) f = fun t => Real.sin (π / l * t) • Efield t)
    (t : ℝ) :
    g.inner (f 0 t) (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
        (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
      - g.inner (f 0 t)
          (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
            (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
            (curveVelocity (I := I) (f 0) t))
          (variationField (I := I) f t)
      = (π / l) ^ 2 * Real.cos (π / l * t) ^ 2
        - Real.sin (π / l * t) ^ 2
            * sectionalCurvature (g.leviCivita) (f 0 t) (Efield t)
                (curveVelocity (I := I) (f 0) t) := by
  set ċ := curveVelocity (I := I) (f 0) t with hcdef
  -- convert `g.inner` to `g.metricInner` and expand the variation field
  simp only [hVfield, ← RiemannianMetric.metricInner_apply]
  -- (1) the covariant derivative of the sin-field: `V̇ = (π/l)cos(π/l t) • E t`
  have hVdot : derivAlongCurve (I := I) g (f 0) (fun s => Real.sin (π / l * s) • Efield s) t
      = (Real.cos (π / l * t) * (π / l)) • Efield t := by
    rw [derivAlongCurve_smul_fun (I := I) g (f 0) (fun s => Real.sin (π / l * s)) Efield
      (hasDerivAt_sin_window t).differentiableAt (hEdiff t),
      (hasDerivAt_sin_window t).deriv, hEpar t, smul_zero, add_zero]
  -- (2) the bivector `|E ∧ ċ|² = 1`
  have hbiv : bivectorInnerProduct g (f 0 t) (Efield t) ċ (Efield t) ċ = 1 := by
    rw [bivectorInnerProduct, hEunit t, hspeed t, hEperp t]; ring
  -- (3) the curvature 4-tensor at `(E, ċ, ċ, E)` is `sec(E, ċ)`
  have hcurv4 : curvatureTensorFourAt (g.leviCivita) (f 0 t) (Efield t) ċ ċ (Efield t)
      = sectionalCurvature (g.leviCivita) (f 0 t) (Efield t) ċ := by
    rw [(isAlgCurvatureForm_curvatureTensorFourAt (g.leviCivita) (f 0 t)).pairSwap
      (Efield t) ċ ċ (Efield t), sectionalCurvature_eq_curvatureTensorFourAt, hbiv, div_one]
  -- kinetic term
  have hT1 : g.metricInner (f 0 t)
      (derivAlongCurve (I := I) g (f 0) (fun s => Real.sin (π / l * s) • Efield s) t)
      (derivAlongCurve (I := I) g (f 0) (fun s => Real.sin (π / l * s) • Efield s) t)
      = (π / l) ^ 2 * Real.cos (π / l * t) ^ 2 := by
    rw [hVdot, g.metricInner_smul_left, g.metricInner_smul_right, hEunit t]; ring
  -- curvature term
  have hT2 : g.metricInner (f 0 t)
      (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
        (Real.sin (π / l * t) • Efield t) ċ ċ) (Real.sin (π / l * t) • Efield t)
      = Real.sin (π / l * t) ^ 2 * sectionalCurvature (g.leviCivita) (f 0 t) (Efield t) ċ := by
    rw [curvatureTensorAt_smul_first, g.metricInner_smul_left, g.metricInner_smul_right,
      show g.metricInner (f 0 t)
          (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t) (Efield t) ċ ċ) (Efield t)
        = curvatureTensorFourAt (g.leviCivita) (f 0 t) (Efield t) ċ ċ (Efield t) from rfl,
      hcurv4]
    ring
  rw [hT1, hT2]

/-- **Math.** Petersen §6.3, Lemma 6.3.1 (Bonnet 1855 / Synge 1926): the second variation of
energy of the sin-weighted parallel field along a unit-speed geodesic is **strictly negative**
when `sec ≥ k > 0` and the length `l > π/√k`.  Hence the geodesic is not locally minimizing.

The variation `f`, its smoothness `hf`, that it is proper and geodesic-based, that its
variation field is `sin(π·/l) E` for `E` a unit parallel field ⟂ `ċ`, unit speed, and the
integrability `hint` of the curvature weight are all hypotheses — see the module docstring on
scope.  Given them, this is exactly Petersen's computation feeding `bonnetSynge_index_core`. -/
theorem bonnetSynge_longGeodesicsNotMinimizing
    (g : RiemannianMetric I M) {l k : ℝ} (hk : 0 < k) (hlk : π / Real.sqrt k < l)
    {f : ℝ → ℝ → M} {δ a b : ℝ} (hδ : 0 < δ)
    (hsub : Set.Icc (0 : ℝ) l ⊆ Set.Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b))
    (hgeo : ∀ t ∈ Set.Icc (0 : ℝ) l, curveAcceleration (I := I) g (f 0) t = 0)
    (hfix₀ : ∀ s, f s 0 = f 0 0) (hfixl : ∀ s, f s l = f 0 l)
    {Efield : ∀ t, TangentSpace I (f 0 t)}
    (hEpar : IsParallelAlong (I := I) g (f 0) Efield)
    (hEdiff : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) (f 0) (f 0 t) Efield) t)
    (hEunit : ∀ t, g.metricInner (f 0 t) (Efield t) (Efield t) = 1)
    (hEperp : ∀ t, g.metricInner (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t) = 0)
    (hspeed : ∀ t, g.metricInner (f 0 t) (curveVelocity (I := I) (f 0) t)
      (curveVelocity (I := I) (f 0) t) = 1)
    (hVfield : variationField (I := I) f = fun t => Real.sin (π / l * t) • Efield t)
    (hsec : ∀ t, HasSecBoundedBelowAt (g.leviCivita) (f 0 t) k)
    (hint : IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 *
        sectionalCurvature (g.leviCivita) (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t))
        volume 0 l) :
    deriv (deriv (fun s : ℝ => energyFunctional (I := I) g (f s) 0 l)) 0 < 0 := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hl : 0 < l := lt_trans (div_pos Real.pi_pos hsk) hlk
  have hHD := secondVariationEnergy_properVariation (I := I) g hδ hl hsub hf hgeo hfix₀ hfixl
  rw [hHD.deriv]
  -- rewrite the Synge integrand pointwise to `(π/l)²cos² − sin²·sec`
  rw [intervalIntegral.integral_congr
      (fun t _ => bonnetSynge_variation_integrand g hEpar hEdiff hEunit hEperp hspeed hVfield t)]
  -- split the integral and normalise the constant factor
  have hcos_int : IntervalIntegrable
      (fun t => (π / l) ^ 2 * Real.cos (π / l * t) ^ 2) volume 0 l :=
    (by fun_prop : Continuous fun t => (π / l) ^ 2 * Real.cos (π / l * t) ^ 2).intervalIntegrable 0 l
  rw [intervalIntegral.integral_sub hcos_int hint, intervalIntegral.integral_const_mul]
  -- the scalar core, with the sectional-curvature weight bounded below by `k`
  refine bonnetSynge_index_core hl hk hlk hint (fun t _ => ?_)
  have hli : LinearIndependent ℝ ![Efield t, curveVelocity (I := I) (f 0) t] := by
    by_contra h
    have hz := bivectorInnerProduct_self_eq_zero_of_not_linearIndependent g (f 0 t) h
    rw [show bivectorInnerProduct g (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t)
          (Efield t) (curveVelocity (I := I) (f 0) t) = 1 from by
        rw [bivectorInnerProduct, hEunit t, hspeed t, hEperp t]; ring] at hz
    exact one_ne_zero hz
  exact hsec t (Efield t) (curveVelocity (I := I) (f 0) t) hli

end PetersenLib
