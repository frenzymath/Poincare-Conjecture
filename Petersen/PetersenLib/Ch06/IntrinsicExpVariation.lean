import PetersenLib.Ch06.ExpIntrinsicBridge
import PetersenLib.Ch01.ArcLength
import PetersenLib.Ch05.UniformInjectivityRadius
-- `geodesicMaximalCurve_zero` is filed here, not in `Ch05/GeodesicCompleteness.lean`
import PetersenLib.Ch05.IsometryUniqueness

/-!
# The intrinsic exponential variation, and the chart reading of a field along a curve

Two pieces of infrastructure for §6.2–§6.3, both feeding the joint-smoothness gap that separates
this project from Bonnet–Synge (Lem. 6.3.1).

* `intrinsicExpVariation` — the exponential variation `\bar c(s,t) = \exp_{c(t)}(sV(t))` built on
  the **intrinsic** exponential `geodesicMaximalCurve g q v 1` rather than on the chart-anchored
  `PetersenLib.expMap`.  `Ch06/ExpIntrinsicBridge.lean` explains at length why the distinction is
  forced: `expMap`'s domain is anchored to `chartAt H q`, an arbitrary per-point choice, so its
  chart-escape radius has no locally uniform lower bound in `q` and a single `δ` serving every
  basepoint `c t` is unobtainable *in principle*.  The slab hypothesis `hf` of
  `secondVariationEnergy` (Thm. 6.1.4) must therefore be discharged intrinsically; the two agree
  near the origin by `expMap_eq_geodesicMaximalCurve_of_small`, which is how
  `Ch06/ExpVariation.lean`'s two pointwise results carry across.

* `IsVectorFieldAlong.contMDiffOn_chartFiberCoord` — the chart reading `t ↦ \hat V(t)` of a field
  along a curve is smooth.  This **activates `IsVectorFieldAlong`** (`Ch01/ArcLength.lean`), which
  until now was dead code: it had no uses anywhere in the tree outside its own file, and nothing
  derived the chart reading from it, which is the only thing one ever wants it for.

## Why the second lemma is three lines

`Exponential.chartFiberCoord_contMDiffOn` (`Riemannian/Geodesic/Equation.lean`) already says
the fibre coordinate `p ↦ (\text{triv}_x p).2` is `C^∞` on `geodesicChartDomain x`, and
`IsVectorFieldAlong c V J` is by definition smoothness of the section `t ↦ ⟨c t, V t⟩`.  So the
chart reading is a composition, and the only side condition is that the section lands in the
chart domain — which `mem_geodesicChartDomain_of_proj` reduces to `c t ∈ (chartAt H x).source`,
since `geodesicChartDomain x` is *by definition* the preimage of the chart source under the
projection (`trivializationAt_source_eq`).  The models match on the nose: `I.tangent` is
`I.prod 𝓘(ℝ, E)`, which is the target model `IsVectorFieldAlong` is stated with.
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Geodesic PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]

/-- **Math.** Petersen §6.1: the **intrinsic exponential variation** of a field `V` along a curve
`c`,

$$\bar c(s,t) = \exp_{c(t)}\big(sV(t)\big),$$

with `exp` the intrinsic (moving-foot) exponential `geodesicMaximalCurve g q v 1`.

This is `Ch06/ExpVariation.lean`'s `expVariation` with the chart-anchored `PetersenLib.expMap`
replaced by the intrinsic exponential.  The replacement is not cosmetic — see the module
docstring and `Ch06/ExpIntrinsicBridge.lean`: only the intrinsic form can carry a slab statement,
because `expMap`'s domain has no locally uniform radius in the basepoint. -/
def intrinsicExpVariation (g : RiemannianMetric I M) (c : ℝ → M) (V : ∀ t, TangentSpace I (c t)) :
    ℝ → ℝ → M :=
  fun s t => geodesicMaximalCurve (I := I) g (c t) ((s • V t : TangentSpace I (c t))) 1

/-- **Math.** The intrinsic exponential variation is a variation **of `c`**: at `s = 0` the
exponential is evaluated at the zero vector, and the maximal geodesic with zero initial velocity
is constant, so `\bar c(0, t) = c(t)`. -/
@[simp] theorem intrinsicExpVariation_zero (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) : intrinsicExpVariation (I := I) g c V 0 = c := by
  funext t
  show geodesicMaximalCurve (I := I) g (c t) (((0 : ℝ) • V t : TangentSpace I (c t))) 1 = c t
  rw [zero_smul]
  exact geodesicMaximalCurve_zero (I := I) g (c t) 1

/-- **Math.** **The chart reading of a smooth field along a curve is smooth.**  If `V` is a vector
field along `c` on `J` (`IsVectorFieldAlong`, i.e. the section `t ↦ ⟨c t, V t⟩` is `C^∞` on `J`)
and `c` maps `J` into the chart at `x`, then the chart-`x` fibre coordinate
`t ↦ \hat V(t) = (\text{triv}_x⟨c t, V t⟩)_2` is `C^∞` on `J`.

This is the lemma that makes `IsVectorFieldAlong` usable: reading a field along a curve in a
chart is the only thing one ever does with it, and nothing in the tree did it before — the
predicate had no uses outside its own defining file.

**Proof.**  `chartFiberCoord_contMDiffOn` gives smoothness of the fibre coordinate on
`geodesicChartDomain x`; compose with the section, whose `MapsTo` side condition is
`mem_geodesicChartDomain_of_proj` applied to `hsrc` (the chart domain of the bundle *is* the
preimage of the chart source under the projection). -/
theorem IsVectorFieldAlong.contMDiffOn_chartFiberCoord {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {J : Set ℝ}
    (hV : IsVectorFieldAlong (I := I) c V J) (x : M)
    (hsrc : ∀ t ∈ J, c t ∈ (chartAt H x).source) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (fun t => chartFiberCoord (I := I) x (⟨c t, V t⟩ : TangentBundle I M)) J :=
  (chartFiberCoord_contMDiffOn (I := I) x).comp hV fun t ht =>
    mem_geodesicChartDomain_of_proj (I := I) (hsrc t ht)

/-- **Math.** **The chart fibre coordinate is linear in the fibre**, in the `•` instance:
`\widehat{sv} = s\hat v`.  The trivialization is fibrewise a continuous *linear* map, so this is
`ContinuousLinearMap.map_smul` once the raw second component is rewritten into that linear map
(`Bundle.Trivialization.continuousLinearMapAt_apply_of_mem`, which needs the foot in the
trivialization's base set).

This is what turns the `s`-dependence of `intrinsicExpVariation` — where `s` sits *inside* the
fibre, as `s • V t` — into an `s` sitting outside, in the chart coordinate `s • \hat V(t)`.  That
is the form in which the pair map's joint `C^∞`-ness can consume it, so this lemma is exactly the
hinge of the slab argument. -/
theorem chartFiberCoord_smul (x q : M) (hq : q ∈ (chartAt H x).source) (s : ℝ)
    (v : TangentSpace I q) :
    chartFiberCoord (I := I) x (⟨q, (s • v : TangentSpace I q)⟩ : TangentBundle I M)
      = s • chartFiberCoord (I := I) x (⟨q, v⟩ : TangentBundle I M) := by
  set e := trivializationAt E (TangentSpace I) x with hedef
  -- the trivialization's base set *is* the chart source, so `hq` is the membership wanted
  have hq' : q ∈ e.baseSet := by
    rw [hedef, TangentBundle.trivializationAt_baseSet]; exact hq
  show (e ⟨q, (s • v : TangentSpace I q)⟩).2 = s • (e ⟨q, v⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hq',
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hq']
  exact ContinuousLinearMap.map_smul _ _ _

end PetersenLib

end
