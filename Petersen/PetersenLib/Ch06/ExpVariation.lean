import PetersenLib.Ch06.SecondVariationGlobal
import PetersenLib.Ch05.ExponentialMap

/-!
# Petersen Ch. 6 — the exponential variation of a field along a curve

Thm. 6.1.4 (`Ch06/SecondVariationGlobal.lean`) computes `d²E/ds²|₀` for a *variation*
`f : ℝ → ℝ → M`.  Every application in §6.2–§6.3 instead starts from a **field** `V` along a
geodesic `c` — Bonnet–Synge (Lem. 6.3.1) takes `V(t) = \sin(\pi t/l)E(t)` for a parallel `E`,
Synge's theorem takes a parallel `V`, and so on — and needs a variation realizing it.

The canonical realization is the **exponential variation**

$$\bar c(s,t) = \exp_{c(t)}\big(s\,V(t)\big),$$

whose base curve is `c` (at `s = 0` the exponential is evaluated at the zero vector) and whose
variation field is `V` (differentiating in `s` at `0`, the exponential's derivative at the
origin is the identity — Gauss's observation, here
`Exponential.exists_hasStrictFDerivAt_extChartAt_expMap`).

This file proves those two facts.  They are the *pointwise* half of the bridge, and they need
no compactness, no chart cover, and no smoothness of the exponential in its **basepoint** —
each is a statement at one fixed time `t`, where the basepoint `c t` is a constant.

* `expVariation` — the variation `\bar c(s,t) = \exp_{c(t)}(sV(t))`.
* `expVariation_zero` — its base curve is `c`.
* `variationField_expVariation` — its variation field is `V`.

**What is still missing for §6.3** (deliberately not attempted here): the *global* half — that
`(s,t) ↦ \exp_{c(t)}(sV(t))` is jointly `ContMDiffOn` on a slab `Ioo (-δ) δ ×ˢ Ioo a b`, which
is what Thm. 6.1.4's `hf` hypothesis wants.

**Correction (run 0184, s0010).**  An earlier version of this docstring said the gap was "a
uniform normal radius along `c` — another chart cover, of the same shape as Thm. 6.1.4's".  That
misnames the obstruction on two counts, and cost at least one session:

1. The real blocker is that **`expMap` is the wrong exponential for a slab**.  It is anchored to
   `chartAt H (c t)` — an arbitrary per-point choice with no uniform size — so its chart-escape
   radius has *no locally uniform lower bound* in the basepoint, and a single `δ` serving every
   `c t` is unobtainable in principle, not merely unproved.  (`Ch05/ExpChartConfinement.lean` and
   `compactSet_uniformCInftyDiffeo`'s docstring both say so.)  The slab statement must be made
   about the **intrinsic** exponential `geodesicMaximalCurve g q v 1`; the two agree near the
   origin by `expMap_eq_geodesicMaximalCurve_of_small` (`Ch06/ExpIntrinsicBridge.lean`), which is
   how the two pointwise theorems below carry across.
2. Once restated intrinsically, **no Lebesgue-number machinery is needed**.  `ContMDiffOn` on an
   *open* slab is a pointwise condition, so a purely local statement plus a `min` over a finite
   subcover of the compact time interval suffices.  `isGeodesicWithInitialOn_flow_window`
   (`Ch05/UniformInjectivityRadius.lean`) already leaves the foot `q` free over a whole chart;
   `exists_local_uniformCInftyDiffeo` merely *chose* to slice it at a fixed basepoint.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle Interval

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  -- the exponential-map layer (`Ch05/ExponentialMap.lean`) runs on this instance
  [T2Space (TangentBundle I M)]

/-- **Math.** Petersen §6.1: the **exponential variation** of a field `V` along a curve `c`,
`\bar c(s,t) = \exp_{c(t)}(sV(t))`.  This is the standard way to turn a field along `c` into a
variation of `c` — the one every application of the second variation formula uses. -/
def expVariation (g : RiemannianMetric I M) (c : ℝ → M) (V : ∀ t, TangentSpace I (c t)) :
    ℝ → ℝ → M :=
  fun s t => expMap (I := I) g (c t) ((s • V t : TangentSpace I (c t)))

/-- **Math.** The exponential variation is a variation **of `c`**: at `s = 0` the exponential is
evaluated at the zero vector, and `exp_p 0 = p`. -/
@[simp] theorem expVariation_zero (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) : expVariation (I := I) g c V 0 = c := by
  funext t
  show expMap (I := I) g (c t) (((0 : ℝ) • V t : TangentSpace I (c t))) = c t
  rw [zero_smul, expMap_zero]

/-- **Math.** Petersen §6.1: the **variation field of the exponential variation is `V`**,

$$\frac{\partial}{\partial s}\Big|_{s=0}\exp_{c(t)}\big(sV(t)\big) = V(t).$$

This is what makes `expVariation` the right realization: feeding it to Thm. 6.1.4
(`secondVariationEnergy`) produces the second variation *in the direction `V`*.

**Proof.**  Fix `t`; the basepoint `c t` is then a constant, so no basepoint-dependence of the
exponential is involved.  `variationField` is by definition the `s`-velocity of the transversal
curve read in the chart at `\bar c(0,t) = c t`, i.e.
`deriv (fun s => φ_{c t}(\exp_{c t}(sV(t)))) 0`.  That map is the composite of the linear
`s ↦ sV(t)` with `w ↦ φ_{c t}(\exp_{c t}(w))`, whose strict Fréchet derivative at the origin is
the **identity** (`Exponential.exists_hasStrictFDerivAt_extChartAt_expMap`).  The chain rule
therefore returns `id (V t) = V t`. -/
theorem variationField_expVariation (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    variationField (I := I) (expVariation (I := I) g c V) t = V t := by
  classical
  -- the base point of the transversal curve at time `t`
  have hbase : expVariation (I := I) g c V 0 t = c t := by
    rw [expVariation_zero]
  -- the exponential's chart reading has the identity as derivative at the origin
  obtain ⟨ρ, -, -, -, hstrict⟩ :=
    Exponential.exists_hasStrictFDerivAt_extChartAt_expMap (I := I) g (c t)
  -- the inner, linear factor `s ↦ s • V t`.  `(F := E)` is load-bearing: without it
  -- `smul_const` unifies `F` with `TangentSpace I (c t)`, which carries no norm instance.
  have hlin : HasDerivAt (fun s : ℝ => s • V t) (V t) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (F := E) (V t)
  -- the outer factor, rebased at `0 • V t = 0` so the chain rule composes.  The `•` is spelled
  -- with explicit types for the same reason as `(F := E)` above.
  have hF : HasFDerivAt
      (fun w : E => extChartAt I (c t) (Exponential.expMap (I := I) g (c t) w))
      (ContinuousLinearMap.id ℝ E) (@HSMul.hSMul ℝ E E _ (0 : ℝ) (V t)) := by
    rw [zero_smul]
    exact hstrict.hasFDerivAt
  have hcomp := hF.comp_hasDerivAt (F := E) (0 : ℝ) hlin
  -- `variationField` is exactly that derivative, read at the base point
  rw [variationField_eq, hbase]
  simp only [expVariation, expMap_eq]
  simpa [Function.comp] using hcomp.deriv

end PetersenLib

end
