import DoCarmoLib.Riemannian.Variation.EnergySecondDeriv
import DoCarmoLib.Riemannian.Variation.FirstVariation
import DoCarmoLib.Riemannian.Variation.IndexForm

/-!
# do Carmo's formula (3): the second variation of energy, assembled

do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.8 (`prop:dc-ch9-2-8`), the central
theorem of the chapter, **on a segment carrying no breakpoint** (do Carmo's `k = 0` case),
for a **proper** variation of a **geodesic**:
$$\frac{1}{2}E''(0)
  = -\int_a^b \Big\langle V,\ \frac{D^2V}{dt^2} + R(\gamma', V)\gamma'\Big\rangle\,dt .$$

This file **composes** the two halves of do Carmo's proof, which until now had never met:

1. *the analytic half* — `hasDerivAt_deriv_dcEnergy_second_variation`
   (`Variation/EnergySecondDeriv.lean`): differentiating the first variation
   `E'(s) = 2∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩ dt` once more in `s` gives
   $$\tfrac12 E''(s_0) = \int_a^b\Big\{\Big\langle\tfrac{D}{\partial s}\tfrac{D}{\partial s}\tfrac{\partial f}{\partial t},
     \tfrac{\partial f}{\partial t}\Big\rangle + \Big\langle\tfrac{D}{\partial s}\tfrac{\partial f}{\partial t},
     \tfrac{D}{\partial s}\tfrac{\partial f}{\partial t}\Big\rangle\Big\}\,dt ;$$
2. *the geometric substitution* — the symmetry of the connection
   (`lem:dc-ch9-2-4-symmetry-manifold`) and the Ricci identity
   (`lem:dc-ch9-2-8-curvature-substitution-manifold`), which at `s = 0` for a geodesic turn
   that integrand into do Carmo's `-⟨V, D²V/dt² + R(γ', V)γ'⟩`, plus two integrations by
   parts (`FirstVariation.lean`) that discharge the boundary terms of the proper variation.

## The two pointwise inputs, carried as hypotheses

Exactly as `FirstVariationFormula.lean` carries the symmetry of the connection as the
hypothesis `hsymm` (it is discharged at the call site from
`covariantDerivS_velT_eq_covariantDerivT_velS`), this file carries **two** pointwise
geometric identities as hypotheses, both required only at **interior** times `t ∈ (a, b)`:

* `hsymm` — the symmetry of the connection at `s₀`, `D/∂s ∂f/∂t = D/∂t ∂f/∂s = V'`, which
  rewrites the second integrand `⟨D/∂s ∂f/∂t, D/∂s ∂f/∂t⟩` as `⟨V', V'⟩`
  (`lem:dc-ch9-2-4-symmetry-manifold`);
* `hric` — the Ricci-identity substitution at `s₀`, in the metric-paired form
  $$\Big\langle\tfrac{D}{\partial s}\tfrac{D}{\partial s}\tfrac{\partial f}{\partial t},\ \tfrac{\partial f}{\partial t}\Big\rangle
    = \Big\langle\tfrac{D}{\partial t}\tfrac{D}{\partial s}\tfrac{\partial f}{\partial s},\ \tfrac{\partial f}{\partial t}\Big\rangle
      - R\Big(\tfrac{\partial f}{\partial s}, \tfrac{\partial f}{\partial t}, \tfrac{\partial f}{\partial s}, \tfrac{\partial f}{\partial t}\Big) ,$$
  the result of applying the symmetry of the connection to the inner pair
  `D/∂s ∂f/∂t = D/∂t ∂f/∂s` and then the Ricci identity
  (`metricInner_covariantDerivT_covariantDerivS_commutator_eq_curvatureFormAt`) to the field
  `∂f/∂s`.  It is discharged at the call site from those two chart-free nodes.

The **assembly** — the two integrations by parts, the geodesic and properness vanishing, and
the curvature-symmetry rewrite `R(∂f/∂s, ∂f/∂t, ∂f/∂s, ∂f/∂t) = R(γ', V, γ', V)` — is
performed here.

## Scope — what is and is not claimed

The conclusion is do Carmo's formula (3) **on a single segment carrying no breakpoint**, for
a **proper** variation of a geodesic: his jump sum `∑_i ⟨V(t_i), Δ(DV/dt)(t_i)⟩` arises by
summing over the segments of a subdivision, which is not performed here — this is do Carmo's
`k = 0` case, exactly as `FirstVariationFormula.lean` is for the first variation.  Because the
variation is proper (`V(a) = V(b) = 0` and `D/∂s ∂f/∂s = 0` at the endpoints), every boundary
term drops and the formula is the clean `-∫⟨V, D²V/dt² + R(γ', V)γ'⟩`.

## Fields

At the base parameter `s₀`, along the base curve `γ = f(s₀, ·)` (a geodesic):
`T = ∂f/∂t = γ'`; `S = ∂f/∂s`, whose value `V = S(s₀, ·)` is the variational field;
`DtS = D/∂t V = V'`, `DtDtS = D²V/dt²`; `DsT = D/∂s ∂f/∂t`,
`DsDsT = D/∂s D/∂s ∂f/∂t` (the analytic side); and `W2 = D/∂s ∂f/∂s`,
`DtW2 = D/∂t D/∂s ∂f/∂s` (the field the Ricci identity integrates by parts against `γ'`).

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.8 (formula (3)); the symmetry
of the connection is Ch. 3, Lemma 3.4, the Ricci identity Ch. 4, Lemma 4.1, and metric
compatibility Ch. 2, Prop. 3.2.
-/

open Set Riemannian Filter MeasureTheory
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

/-- **Math.** The pointwise curvature-form symmetry `R(x, y, x, y) = R(y, x, y, x)` for the
Levi-Civita curvature `(0,4)` form, i.e.
`curvatureFormAt g p x y x y = curvatureFormAt g p y x y x`.  Antisymmetry in the first pair
(`IsAlgCurvatureForm.antisymm₁₂`) and in the second pair (`.antisymm₃₄`) each contribute a
sign, and the two cancel.  This is what turns the `R(∂f/∂s, ∂f/∂t, ∂f/∂s, ∂f/∂t)` produced by
the Ricci identity into do Carmo's `R(γ', V, γ', V) = ⟨R(γ', V)γ', V⟩`. -/
theorem curvatureFormAt_swap_pairs (g : RiemannianMetric I M) (p : M)
    (x y : TangentSpace I p) :
    g.leviCivitaConnection.curvatureFormAt g p x y x y
      = g.leviCivitaConnection.curvatureFormAt g p y x y x := by
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  obtain ⟨_hsym, hcompat⟩ := hLC
  -- read both sides as the field-level curvature 4-tensor of the extended fields, where
  -- antisymmetry in each pair (instance-free, no `RiemannianBundle` on `TangentSpace`) applies
  rw [g.leviCivitaConnection.curvatureFormAt_eq g p (AffineConnection.extendField_apply p x)
        (AffineConnection.extendField_apply p y) (AffineConnection.extendField_apply p x)
        (AffineConnection.extendField_apply p y),
      g.leviCivitaConnection.curvatureFormAt_eq g p (AffineConnection.extendField_apply p y)
        (AffineConnection.extendField_apply p x) (AffineConnection.extendField_apply p y)
        (AffineConnection.extendField_apply p x),
      g.leviCivitaConnection.curvatureForm_antisymm_left g (AffineConnection.extendField p x)
        (AffineConnection.extendField p y) (AffineConnection.extendField p x)
        (AffineConnection.extendField p y) p,
      g.leviCivitaConnection.curvatureForm_antisymm_right g hcompat
        (AffineConnection.extendField p y) (AffineConnection.extendField p x)
        (AffineConnection.extendField p y) (AffineConnection.extendField p x) p]

/-- **Math.** do Carmo Ch. 9, §2, `prop:dc-ch9-2-8`, **the integral identity behind formula
(3)** (the `k = 0`, proper case), stated without reference to `E`.  Given the analytic
integrand `⟨D/∂s D/∂s ∂f/∂t, ∂f/∂t⟩ + ⟨D/∂s ∂f/∂t, D/∂s ∂f/∂t⟩` of the second variation, the
symmetry of the connection (`hsymm`) and the Ricci-identity substitution (`hric`) reorganize
it, and two integrations by parts (using the geodesic hypothesis `hgeo` and properness `hSa`,
`hSb`, `hW2a`, `hW2b`) collapse it to
$$\int_a^b\Big\{\ldots\Big\}\,dt
  = -\int_a^b\Big\langle V,\ \frac{D^2V}{dt^2} + R(\gamma', V)\gamma'\Big\rangle\,dt .$$ -/
theorem integral_second_variation_integrand_eq
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M}
    {T S DsT DsDsT DtS DtDtS W2 DtW2 : ℝ × ℝ → E} {s₀ a b : ℝ}
    (hab : a ≤ b)
    -- the base curve `γ = f(s₀, ·)` is a geodesic: its velocity pair is `(T, 0)`
    (hgeo : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => T (s₀, t)) (fun _ => 0) a b)
    -- the variational field `V = S(s₀,·)` and its two covariant derivatives `V'`, `V''`
    (hV : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => S (s₀, t)) (fun t => DtS (s₀, t)) a b)
    (hV' : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => DtS (s₀, t)) (fun t => DtDtS (s₀, t)) a b)
    -- the field `W2 = D/∂s ∂f/∂s` and its covariant `t`-derivative
    (hW2 : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => W2 (s₀, t)) (fun t => DtW2 (s₀, t)) a b)
    (hdiff : IsChartDifferentiableOn (I := I) (fun t => f (s₀, t)) a b)
    (hcont : ∀ t ∈ Icc a b, ContinuousAt (fun t => f (s₀, t)) t)
    -- the two pointwise geometric identities, at interior times
    (hsymm : ∀ t ∈ Ioo a b, DsT (s₀, t) = DtS (s₀, t))
    (hric : ∀ t ∈ Ioo a b,
      g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        = g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
          - g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
              (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)))
    -- properness: `V` and `D/∂s ∂f/∂s` vanish at the endpoints
    (hSa : S (s₀, a) = 0) (hSb : S (s₀, b) = 0)
    (hW2a : W2 (s₀, a) = 0) (hW2b : W2 (s₀, b) = 0)
    -- integrability of each piece
    (hi_DsDsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_DsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      volume a b)
    (hi_DtW2 : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_R : IntervalIntegrable
      (fun t => g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
        (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t))) volume a b)
    (hi_DtS : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (DtS (s₀, t)))
      volume a b)
    (hi_S_DtDtS : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtDtS (s₀, t)))
      volume a b) :
    ∫ t in a..b, (g.metricInner (f (s₀, t))
          (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        + g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      = -∫ t in a..b, (g.metricInner (f (s₀, t))
            (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtDtS (s₀, t))
          + g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
              (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) (S (s₀, t))) := by
  -- split the analytic integrand into its two terms
  rw [intervalIntegral.integral_add hi_DsDsT hi_DsT]
  -- ## term A : `∫⟨D/∂s D/∂s ∂f/∂t, ∂f/∂t⟩ = -∫ R(∂f/∂s, ∂f/∂t, ∂f/∂s, ∂f/∂t)`
  have hA : (∫ t in a..b, g.metricInner (f (s₀, t))
        (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      = -∫ t in a..b, g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
          (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) := by
    -- rewrite the integrand by the Ricci identity, valid a.e. on `[a, b]`
    have hcongr : (∫ t in a..b, g.metricInner (f (s₀, t))
          (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
        = ∫ t in a..b, (g.metricInner (f (s₀, t))
              (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
            - g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
                (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t))) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le hab]
      filter_upwards [Ioo_ae_eq_Ioc (a := a) (b := b)] with t ht htm
      exact hric t (ht.mpr htm)
    rw [hcongr, intervalIntegral.integral_sub hi_DtW2 hi_R]
    -- `∫⟨D/∂t (D/∂s ∂f/∂s), γ'⟩ = 0` : geodesic + proper (the `D/∂s ∂f/∂s` field vanishes at
    -- the endpoints)
    have hzero := hW2.integral_metricInner_covariantDeriv_eq_zero_of_geodesic hgeo hdiff hcont
      hab hi_DtW2 hW2a hW2b
    rw [hzero, zero_sub]
  -- ## term B : `∫⟨D/∂s ∂f/∂t, D/∂s ∂f/∂t⟩ = ∫⟨V', V'⟩ = -∫⟨V, V''⟩`
  have hB : (∫ t in a..b, g.metricInner (f (s₀, t))
        (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      = -∫ t in a..b, g.metricInner (f (s₀, t))
          (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtDtS (s₀, t)) := by
    -- symmetry of the connection : `D/∂s ∂f/∂t = V'`, valid a.e. on `[a, b]`
    have hcongr : (∫ t in a..b, g.metricInner (f (s₀, t))
          (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
        = ∫ t in a..b, g.metricInner (f (s₀, t))
            (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (DtS (s₀, t)) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le hab]
      filter_upwards [Ioo_ae_eq_Ioc (a := a) (b := b)] with t ht htm
      rw [hsymm t (ht.mpr htm)]
    rw [hcongr]
    exact hV.integral_metricInner_eq_neg_integral_of_proper hV' hdiff hcont hab hi_DtS
      hi_S_DtDtS hSa hSb
  rw [hA, hB]
  -- reorganize `-∫R(S,T,S,T) + -∫⟨S, V''⟩` into `-∫(⟨S, V''⟩ + R(T,S,T,S))`
  rw [intervalIntegral.integral_add hi_S_DtDtS
    (by
      -- `R(T,S,T,S)` is integrable because it equals `R(S,T,S,T)` pointwise
      have hfun : (fun t => g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
            (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) (S (s₀, t)))
          = fun t => g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
            (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) := by
        funext t
        exact (curvatureFormAt_swap_pairs g (f (s₀, t)) (T (s₀, t)) (S (s₀, t)))
      rw [hfun]; exact hi_R)]
  -- the curvature-symmetry rewrite `R(S,T,S,T) = R(T,S,T,S)`
  have hswap : (∫ t in a..b, g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
        (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)))
      = ∫ t in a..b, g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
          (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    exact curvatureFormAt_swap_pairs g (f (s₀, t)) (S (s₀, t)) (T (s₀, t))
  rw [hswap]
  ring

/-- **Math.** do Carmo Ch. 9, §2, `prop:dc-ch9-2-8`, **formula (3)** on a segment carrying no
breakpoint, for a **proper** variation of a geodesic `γ = f(s₀, ·)`:
$$\frac{1}{2}E''(0)
  = -\int_a^b\Big\langle V,\ \frac{D^2V}{dt^2} + R(\gamma', V)\gamma'\Big\rangle\,dt,$$
i.e. `deriv (deriv E) s₀ = -2∫{⟨V, V''⟩ + ⟨R(γ', V)γ', V⟩}`.

This composes the two named halves of the proof: the analytic second variation
`hasDerivAt_deriv_dcEnergy_second_variation` (`lem:dc-ch9-2-8-energy-snd-deriv`), supplied as
`hE2`, and the geometric reorganization `integral_second_variation_integrand_eq` — the Ricci
identity, the symmetry of the connection, and two integrations by parts.  As in
`FirstVariationFormula.lean`, the two pointwise geometric identities `hsymm`
(`lem:dc-ch9-2-4-symmetry-manifold`) and `hric`
(`lem:dc-ch9-2-8-curvature-substitution-manifold`) are carried as hypotheses, discharged at
the call site from those chart-free nodes.  `⟨R(γ', V)γ', V⟩` is
`curvatureFormAt g (γ t) (γ' t) (V t) (γ' t) (V t)`, do Carmo's Ch. 4 Def. 2.1 sign, matching
`indexForm`. -/
theorem deriv_deriv_dcEnergy_eq_second_variation
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M}
    {T S DsT DsDsT DtS DtDtS W2 DtW2 : ℝ × ℝ → E} {s₀ a b : ℝ}
    (hab : a ≤ b)
    (hE2 : HasDerivAt (deriv (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b))
      (2 * ∫ t in a..b, (g.metricInner (f (s₀, t))
            (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
          + g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))) s₀)
    (hgeo : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => T (s₀, t)) (fun _ => 0) a b)
    (hV : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => S (s₀, t)) (fun t => DtS (s₀, t)) a b)
    (hV' : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => DtS (s₀, t)) (fun t => DtDtS (s₀, t)) a b)
    (hW2 : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => W2 (s₀, t)) (fun t => DtW2 (s₀, t)) a b)
    (hdiff : IsChartDifferentiableOn (I := I) (fun t => f (s₀, t)) a b)
    (hcont : ∀ t ∈ Icc a b, ContinuousAt (fun t => f (s₀, t)) t)
    (hsymm : ∀ t ∈ Ioo a b, DsT (s₀, t) = DtS (s₀, t))
    (hric : ∀ t ∈ Ioo a b,
      g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        = g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
          - g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
              (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)))
    (hSa : S (s₀, a) = 0) (hSb : S (s₀, b) = 0)
    (hW2a : W2 (s₀, a) = 0) (hW2b : W2 (s₀, b) = 0)
    (hi_DsDsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_DsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      volume a b)
    (hi_DtW2 : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_R : IntervalIntegrable
      (fun t => g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
        (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t))) volume a b)
    (hi_DtS : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (DtS (s₀, t)))
      volume a b)
    (hi_S_DtDtS : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtDtS (s₀, t)))
      volume a b) :
    deriv (deriv (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b)) s₀
      = -2 * ∫ t in a..b, (g.metricInner (f (s₀, t))
            (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtDtS (s₀, t))
          + g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
              (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) (S (s₀, t))) := by
  rw [hE2.deriv, integral_second_variation_integrand_eq hab hgeo hV hV' hW2 hdiff hcont hsymm
    hric hSa hSb hW2a hW2b hi_DsDsT hi_DsT hi_DtW2 hi_R hi_DtS hi_S_DtDtS]
  ring

/-! ### The index form of the second variation (formula (6), the proper case) -/

/-- **Math.** do Carmo Ch. 9, §2, Remark 2.10, **formula (6) for a proper variation**
(`rem:dc-ch9-2-10`): the analytic second-variation integrand equals the index form
`I_a(V, V)` of \cref{def:dc-ch9-2-10-index-form}.  This is
`integral_second_variation_integrand_eq` read one integration-by-parts earlier — instead of
pushing `⟨V', V'⟩` back to `-⟨V, V''⟩`, it keeps it, landing on
`∫\{⟨V', V'⟩ - ⟨R(γ', V)γ', V⟩\}\,dt = I_a(V, V)`.

`hvel` pins `T = ∂f/∂t` to the velocity `γ'` of `γ = f(s₀, ·)`, matching the `DCVelocity`
that `indexForm` reads for `R(γ', V)γ'`.  Only the geodesic hypothesis (`hgeo`) and the
properness of `D/∂s ∂f/∂s` (`hW2a`, `hW2b`) enter — the properness of `V` itself is not
needed here, because the `V'`-to-`V''` integration by parts is skipped. -/
theorem integral_second_variation_eq_indexForm
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M}
    {T S DsT DsDsT DtS W2 DtW2 : ℝ × ℝ → E} {s₀ a b : ℝ}
    (hab : a ≤ b)
    (hvel : ∀ t, T (s₀, t) = DCVelocity (I := I) (fun τ => f (s₀, τ)) t)
    (hgeo : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => T (s₀, t)) (fun _ => 0) a b)
    (hW2 : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => W2 (s₀, t)) (fun t => DtW2 (s₀, t)) a b)
    (hdiff : IsChartDifferentiableOn (I := I) (fun t => f (s₀, t)) a b)
    (hcont : ∀ t ∈ Icc a b, ContinuousAt (fun t => f (s₀, t)) t)
    (hsymm : ∀ t ∈ Ioo a b, DsT (s₀, t) = DtS (s₀, t))
    (hric : ∀ t ∈ Ioo a b,
      g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        = g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
          - g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
              (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)))
    (hW2a : W2 (s₀, a) = 0) (hW2b : W2 (s₀, b) = 0)
    (hi_DsDsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_DsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      volume a b)
    (hi_DtW2 : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_R : IntervalIntegrable
      (fun t => g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
        (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t))) volume a b)
    (hi_DtS : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (DtS (s₀, t)))
      volume a b) :
    ∫ t in a..b, (g.metricInner (f (s₀, t))
          (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        + g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      = indexForm (I := I) g (fun t => f (s₀, t)) (fun t => S (s₀, t)) (fun t => DtS (s₀, t)) a b := by
  rw [intervalIntegral.integral_add hi_DsDsT hi_DsT]
  -- term A : `∫⟨D/∂s D/∂s ∂f/∂t, ∂f/∂t⟩ = -∫ R(∂f/∂s, ∂f/∂t, ∂f/∂s, ∂f/∂t)` (as in formula (3))
  have hA : (∫ t in a..b, g.metricInner (f (s₀, t))
        (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      = -∫ t in a..b, g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
          (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) := by
    have hcongr : (∫ t in a..b, g.metricInner (f (s₀, t))
          (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
        = ∫ t in a..b, (g.metricInner (f (s₀, t))
              (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
            - g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
                (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t))) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le hab]
      filter_upwards [Ioo_ae_eq_Ioc (a := a) (b := b)] with t ht htm
      exact hric t (ht.mpr htm)
    rw [hcongr, intervalIntegral.integral_sub hi_DtW2 hi_R]
    have hzero := hW2.integral_metricInner_covariantDeriv_eq_zero_of_geodesic hgeo hdiff hcont
      hab hi_DtW2 hW2a hW2b
    rw [hzero, zero_sub]
  -- term B : `∫⟨D/∂s ∂f/∂t, D/∂s ∂f/∂t⟩ = ∫⟨V', V'⟩` (symmetry, no integration by parts)
  have hB : (∫ t in a..b, g.metricInner (f (s₀, t))
        (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      = ∫ t in a..b, g.metricInner (f (s₀, t))
          (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (DtS (s₀, t)) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hab]
    filter_upwards [Ioo_ae_eq_Ioc (a := a) (b := b)] with t ht htm
    rw [hsymm t (ht.mpr htm)]
  rw [hA, hB, indexForm_def]
  -- match the index-form curvature slot `R(γ', V, γ', V)` to `R(∂f/∂s, ∂f/∂t, ∂f/∂s, ∂f/∂t)`
  have hidx : (∫ t in a..b, (g.metricInner (f (s₀, t))
          (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (DtS (s₀, t))
        - g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
            (DCVelocity (I := I) (fun t => f (s₀, t)) t) (S (s₀, t))
            (DCVelocity (I := I) (fun t => f (s₀, t)) t) (S (s₀, t))))
      = ∫ t in a..b, (g.metricInner (f (s₀, t))
          (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (DtS (s₀, t))
        - g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
            (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t))) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [← hvel t, curvatureFormAt_swap_pairs g (f (s₀, t)) (T (s₀, t)) (S (s₀, t))]
  rw [hidx, intervalIntegral.integral_sub hi_DtS hi_R]
  ring

/-- **Math.** do Carmo Ch. 9, §2, Remark 2.10, **formula (6) for a proper variation**
(`rem:dc-ch9-2-10`): for a proper variation of a geodesic `γ = f(s₀, ·)`,
$$\tfrac12 E''(0) = I_a(V, V),$$
i.e. `deriv (deriv E) s₀ = 2 · indexForm g γ V V'`.  This composes the analytic second
variation `hE2` (`lem:dc-ch9-2-8-energy-snd-deriv`) with `integral_second_variation_eq_indexForm`. -/
theorem deriv_deriv_dcEnergy_eq_indexForm
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M}
    {T S DsT DsDsT DtS W2 DtW2 : ℝ × ℝ → E} {s₀ a b : ℝ}
    (hab : a ≤ b)
    (hE2 : HasDerivAt (deriv (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b))
      (2 * ∫ t in a..b, (g.metricInner (f (s₀, t))
            (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
          + g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))) s₀)
    (hvel : ∀ t, T (s₀, t) = DCVelocity (I := I) (fun τ => f (s₀, τ)) t)
    (hgeo : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => T (s₀, t)) (fun _ => 0) a b)
    (hW2 : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => W2 (s₀, t)) (fun t => DtW2 (s₀, t)) a b)
    (hdiff : IsChartDifferentiableOn (I := I) (fun t => f (s₀, t)) a b)
    (hcont : ∀ t ∈ Icc a b, ContinuousAt (fun t => f (s₀, t)) t)
    (hsymm : ∀ t ∈ Ioo a b, DsT (s₀, t) = DtS (s₀, t))
    (hric : ∀ t ∈ Ioo a b,
      g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        = g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
          - g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
              (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)))
    (hW2a : W2 (s₀, a) = 0) (hW2b : W2 (s₀, b) = 0)
    (hi_DsDsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_DsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      volume a b)
    (hi_DtW2 : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_R : IntervalIntegrable
      (fun t => g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
        (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t))) volume a b)
    (hi_DtS : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (DtS (s₀, t)))
      volume a b) :
    deriv (deriv (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b)) s₀
      = 2 * indexForm (I := I) g (fun t => f (s₀, t)) (fun t => S (s₀, t)) (fun t => DtS (s₀, t)) a b := by
  rw [hE2.deriv, integral_second_variation_eq_indexForm hab hvel hgeo hW2 hdiff hcont hsymm hric
    hW2a hW2b hi_DsDsT hi_DsT hi_DtW2 hi_R hi_DtS]

/-! ### Formula (5): the second variation of a non-proper variation -/

/-- **Math.** do Carmo Ch. 9, §2, Remark 2.9, **formula (5)** on a segment carrying no
breakpoint (`rem:dc-ch9-2-9`): for a variation of a geodesic `γ = f(s₀, ·)` that need **not**
be proper,
$$\tfrac12 E''(s_0)
  = -\int_a^b\Big\langle V,\frac{D^2V}{dt^2}+R(\gamma',V)\gamma'\Big\rangle dt
    + \Big\langle\tfrac{D}{\partial s}\tfrac{\partial f}{\partial s},\gamma'\Big\rangle\Big|_a^b
    + \big\langle V, V'\big\rangle\Big|_a^b .$$

This is `integral_second_variation_integrand_eq` with the properness hypotheses dropped: the
two integrations by parts keep their boundary terms
(`IsCovariantDerivFieldAlongOn.integral_metricInner_covariantDeriv_left`) instead of dropping
them.  These are exactly the extra terms of do Carmo's formula (5) at `i = 0` and `i = k+1`;
they feed the proof of `thm:dc-ch9-3-7` (Synge–Weinstein), whose variation is not proper. -/
theorem integral_second_variation_integrand_eq_nonproper
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M}
    {T S DsT DsDsT DtS DtDtS W2 DtW2 : ℝ × ℝ → E} {s₀ a b : ℝ}
    (hab : a ≤ b)
    (hgeo : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => T (s₀, t)) (fun _ => 0) a b)
    (hV : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => S (s₀, t)) (fun t => DtS (s₀, t)) a b)
    (hV' : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => DtS (s₀, t)) (fun t => DtDtS (s₀, t)) a b)
    (hW2 : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => W2 (s₀, t)) (fun t => DtW2 (s₀, t)) a b)
    (hdiff : IsChartDifferentiableOn (I := I) (fun t => f (s₀, t)) a b)
    (hcont : ∀ t ∈ Icc a b, ContinuousAt (fun t => f (s₀, t)) t)
    (hsymm : ∀ t ∈ Ioo a b, DsT (s₀, t) = DtS (s₀, t))
    (hric : ∀ t ∈ Ioo a b,
      g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        = g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
          - g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
              (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)))
    (hi_DsDsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_DsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      volume a b)
    (hi_DtW2 : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_R : IntervalIntegrable
      (fun t => g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
        (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t))) volume a b)
    (hi_DtS : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (DtS (s₀, t)))
      volume a b)
    (hi_S_DtDtS : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtDtS (s₀, t)))
      volume a b) :
    ∫ t in a..b, (g.metricInner (f (s₀, t))
          (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        + g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      = -(∫ t in a..b, (g.metricInner (f (s₀, t))
            (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtDtS (s₀, t))
          + g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
              (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) (S (s₀, t))))
        + (g.metricInner (f (s₀, b)) (W2 (s₀, b) : TangentSpace I (f (s₀, b))) (T (s₀, b))
            - g.metricInner (f (s₀, a)) (W2 (s₀, a) : TangentSpace I (f (s₀, a))) (T (s₀, a)))
        + (g.metricInner (f (s₀, b)) (S (s₀, b) : TangentSpace I (f (s₀, b))) (DtS (s₀, b))
            - g.metricInner (f (s₀, a)) (S (s₀, a) : TangentSpace I (f (s₀, a))) (DtS (s₀, a))) := by
  rw [intervalIntegral.integral_add hi_DsDsT hi_DsT]
  -- term A : `∫⟨D/∂s D/∂s ∂f/∂t, ∂f/∂t⟩ = ⟨D/∂s ∂f/∂s, γ'⟩|_a^b - ∫ R(∂f/∂s, ∂f/∂t, ∂f/∂s, ∂f/∂t)`
  have hzeroInt : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (W2 (s₀, t) : TangentSpace I (f (s₀, t)))
        ((fun _ => (0 : E)) t)) volume a b := by
    simp only [g.metricInner_zero_right]; exact intervalIntegrable_const
  have hA : (∫ t in a..b, g.metricInner (f (s₀, t))
        (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      = (g.metricInner (f (s₀, b)) (W2 (s₀, b) : TangentSpace I (f (s₀, b))) (T (s₀, b))
          - g.metricInner (f (s₀, a)) (W2 (s₀, a) : TangentSpace I (f (s₀, a))) (T (s₀, a)))
        - ∫ t in a..b, g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
            (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) := by
    have hcongr : (∫ t in a..b, g.metricInner (f (s₀, t))
          (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
        = ∫ t in a..b, (g.metricInner (f (s₀, t))
              (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
            - g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
                (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t))) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le hab]
      filter_upwards [Ioo_ae_eq_Ioc (a := a) (b := b)] with t ht htm
      exact hric t (ht.mpr htm)
    rw [hcongr, intervalIntegral.integral_sub hi_DtW2 hi_R]
    -- integration by parts against the geodesic `γ'` (velocity pair `(T, 0)`), boundary kept
    have hbdry := hW2.integral_metricInner_covariantDeriv_left hgeo hdiff hcont hab hi_DtW2 hzeroInt
    rw [hbdry]
    simp only [g.metricInner_zero_right, intervalIntegral.integral_zero, sub_zero]
  -- term B : `∫⟨D/∂s ∂f/∂t, D/∂s ∂f/∂t⟩ = ⟨V, V'⟩|_a^b - ∫⟨V, V''⟩`
  have hB : (∫ t in a..b, g.metricInner (f (s₀, t))
        (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      = (g.metricInner (f (s₀, b)) (S (s₀, b) : TangentSpace I (f (s₀, b))) (DtS (s₀, b))
          - g.metricInner (f (s₀, a)) (S (s₀, a) : TangentSpace I (f (s₀, a))) (DtS (s₀, a)))
        - ∫ t in a..b, g.metricInner (f (s₀, t))
            (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtDtS (s₀, t)) := by
    have hcongr : (∫ t in a..b, g.metricInner (f (s₀, t))
          (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
        = ∫ t in a..b, g.metricInner (f (s₀, t))
            (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (DtS (s₀, t)) := by
      refine intervalIntegral.integral_congr_ae ?_
      rw [uIoc_of_le hab]
      filter_upwards [Ioo_ae_eq_Ioc (a := a) (b := b)] with t ht htm
      rw [hsymm t (ht.mpr htm)]
    rw [hcongr]
    exact hV.integral_metricInner_covariantDeriv_left hV' hdiff hcont hab hi_DtS hi_S_DtDtS
  rw [hA, hB]
  -- reorganize `-∫R(S,T,S,T) - ∫⟨S,V''⟩` into `-∫(⟨S,V''⟩ + R(T,S,T,S))`, boundary terms carried
  rw [intervalIntegral.integral_add hi_S_DtDtS
    (by
      have hfun : (fun t => g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
            (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) (S (s₀, t)))
          = fun t => g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
            (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) := by
        funext t
        exact (curvatureFormAt_swap_pairs g (f (s₀, t)) (T (s₀, t)) (S (s₀, t)))
      rw [hfun]; exact hi_R)]
  have hswap : (∫ t in a..b, g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
        (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)))
      = ∫ t in a..b, g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
          (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    exact curvatureFormAt_swap_pairs g (f (s₀, t)) (S (s₀, t)) (T (s₀, t))
  rw [hswap]
  ring

/-- **Math.** do Carmo Ch. 9, §2, Remark 2.9, **formula (5)** at the level of `E''`
(`rem:dc-ch9-2-9`), on a segment carrying no breakpoint, for a variation of a geodesic that
need not be proper:
$$\tfrac12 E''(s_0)
  = -\int_a^b\Big\langle V,\frac{D^2V}{dt^2}+R(\gamma',V)\gamma'\Big\rangle dt
    + \Big\langle\tfrac{D}{\partial s}\tfrac{\partial f}{\partial s},\gamma'\Big\rangle\Big|_a^b
    + \big\langle V, V'\big\rangle\Big|_a^b .$$

Composes the analytic second variation `hE2` (`lem:dc-ch9-2-8-energy-snd-deriv`) with
`integral_second_variation_integrand_eq_nonproper`.  This is the form
`thm:dc-ch9-3-7` (Synge–Weinstein) applies, where the variation `h(s,t)=exp_{γ(t)}(s e_1(t))`
is not proper. -/
theorem deriv_deriv_dcEnergy_eq_second_variation_nonproper
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M}
    {T S DsT DsDsT DtS DtDtS W2 DtW2 : ℝ × ℝ → E} {s₀ a b : ℝ}
    (hab : a ≤ b)
    (hE2 : HasDerivAt (deriv (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b))
      (2 * ∫ t in a..b, (g.metricInner (f (s₀, t))
            (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
          + g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))) s₀)
    (hgeo : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => T (s₀, t)) (fun _ => 0) a b)
    (hV : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => S (s₀, t)) (fun t => DtS (s₀, t)) a b)
    (hV' : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => DtS (s₀, t)) (fun t => DtDtS (s₀, t)) a b)
    (hW2 : IsCovariantDerivFieldAlongOn (I := I) g (fun t => f (s₀, t))
      (fun t => W2 (s₀, t)) (fun t => DtW2 (s₀, t)) a b)
    (hdiff : IsChartDifferentiableOn (I := I) (fun t => f (s₀, t)) a b)
    (hcont : ∀ t ∈ Icc a b, ContinuousAt (fun t => f (s₀, t)) t)
    (hsymm : ∀ t ∈ Ioo a b, DsT (s₀, t) = DtS (s₀, t))
    (hric : ∀ t ∈ Ioo a b,
      g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
        = g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))
          - g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
              (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t)))
    (hi_DsDsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsDsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_DsT : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (DsT (s₀, t)))
      volume a b)
    (hi_DtW2 : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtW2 (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hi_R : IntervalIntegrable
      (fun t => g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
        (S (s₀, t)) (T (s₀, t)) (S (s₀, t)) (T (s₀, t))) volume a b)
    (hi_DtS : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (DtS (s₀, t) : TangentSpace I (f (s₀, t))) (DtS (s₀, t)))
      volume a b)
    (hi_S_DtDtS : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtDtS (s₀, t)))
      volume a b) :
    deriv (deriv (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b)) s₀
      = 2 * (-(∫ t in a..b, (g.metricInner (f (s₀, t))
            (S (s₀, t) : TangentSpace I (f (s₀, t))) (DtDtS (s₀, t))
          + g.leviCivitaConnection.curvatureFormAt g (f (s₀, t))
              (T (s₀, t)) (S (s₀, t)) (T (s₀, t)) (S (s₀, t))))
        + (g.metricInner (f (s₀, b)) (W2 (s₀, b) : TangentSpace I (f (s₀, b))) (T (s₀, b))
            - g.metricInner (f (s₀, a)) (W2 (s₀, a) : TangentSpace I (f (s₀, a))) (T (s₀, a)))
        + (g.metricInner (f (s₀, b)) (S (s₀, b) : TangentSpace I (f (s₀, b))) (DtS (s₀, b))
            - g.metricInner (f (s₀, a)) (S (s₀, a) : TangentSpace I (f (s₀, a))) (DtS (s₀, a)))) := by
  rw [hE2.deriv, integral_second_variation_integrand_eq_nonproper hab hgeo hV hV' hW2 hdiff hcont
    hsymm hric hi_DsDsT hi_DsT hi_DtW2 hi_R hi_DtS hi_S_DtDtS]

end Riemannian.Variation
