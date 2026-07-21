import PetersenLib.Ch05.ShortSegmentUniquePiecewise

/-!
# Petersen Ch. 5 — the chart-anchoring of `expMap`

This file records, as a Lean theorem, the structural fact that the vendored
`expMap` / `expDomain` of this development are **chart-anchored by definition**:
the chart-`p`-fixed geodesic vector field `geodesicVectorFieldChart g p`
*vanishes identically* off `(chartAt H p).source`.

## Why this matters

`expDomain g p` unfolds to `{v | (1:ℝ) ∈ maximalGeodesicInterval g p v}`
(`Riemannian/Exponential/Defs.lean`), and `maximalGeodesicInterval` is cut
out by `IsGeodesicOnWithInitial`, which asks for an integral curve of
`geodesicVectorFieldChart g p` — the geodesic spray written in the **single
chart at the basepoint `p`** (`Riemannian/Geodesic/MaximalInterval.lean`).
That field is built by `Trivialization.symm`
(`Riemannian/Geodesic/Equation.lean`), and `Trivialization.symm` returns `0`
off the trivialization's `baseSet`, which `geodesicChartDomain_eq_trivBaseSet`
identifies with `proj ⁻¹' (chartAt H p).source`.  Hence the theorem below.

The consequence — *not proved here*, see below — is that a hypothesis
`B(0,ε) ⊆ expDomain g p` already **forces** `exp_p(B(0,ε)) ⊆ (chartAt H p).source`,
because an integral curve of a field that vanishes off the chart cannot leave the
chart while moving at conserved nonzero speed.  This is what refutes the
recorded objection to proving Petersen Thm. 5.5.4 at a *hypothesised*
diffeomorphism radius, namely that "on the round `S²` with `p` a pole and
`ε` slightly under `π`, `exp_p` is a diffeomorphism on `B(0,ε)` yet
`exp_p(B(0,ε)) = S² ∖ {−p}` lies in no chart, so the vendored Gauss engine
cannot fire at `ε`".  That objection reasons about the *mathematical* `exp_p`;
the *on-disk* `expMap` is chart-anchored, so on such an `S²` the Lean hypothesis
`B(0,ε) ⊆ expDomain g p` is simply **false** for `ε` near `π` and the
counterexample never arises.

## What this file does NOT provide

* It does **not** prove the confinement lemma
  `∀ t ∈ [0,1], exp_p(t·v) ∈ (chartAt H p).source` from `v ∈ expDomain g p`.
  That needs the first-exit-time argument (at a first exit time `t₀` the field
  vanishes, so the velocity is `0` there, contradicting — via the mean value
  theorem in a chart at `γ t₀` — the conserved nonzero speed on `[0, t₀)`).
* It therefore does **not**, on its own, deliver Thm. 5.5.4 at a hypothesised
  radius.  See `GaussLemmaAtRadius.lean` for the other compiled half.

## An honesty note for downstream users

The chart-anchoring recorded here is a **fidelity gap** between the Lean
`expDomain` and the blueprint's `def:pet-ch5-exponential-map`, which defines the
domain `𝒪_p` mathematically as `{v | 1 < L_v}` with `L_v` the maximal interval
of the *genuine* geodesic.  The Lean `expDomain` is strictly smaller: it stops
when the geodesic leaves the chart at `p`.  (The sibling development records the
same gap in `DoCarmoLib/Riemannian/Exponential/GlobalExp.lean`, citing issue
I-0199.)  Any future theorem that hypothesises `B(0,ε) ⊆ expDomain g p` and
claims to formalize Petersen's "let `ε` be a radius on which `exp_p` is a
diffeomorphism" leans on the chapter's convention that `expMap`/`expDomain`
formalize `exp_p`/`𝒪_p`, and is, read strictly, restricted to `ε` below the
chart-escape radius.  Do not let that convention become load-bearing silently.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The chart-`p`-fixed geodesic vector field `geodesicVectorFieldChart g p`
**vanishes identically off the chart at `p`**: if the foot `z.proj` of a point
`z : TM` is outside `(chartAt H p).source`, then the field is `0` at `z`.

This is immediate from the construction: the field is defined by applying
`Trivialization.symm` of the trivialization of `T(TM)` at `⟨p, 0⟩`, and
`Trivialization.symm` is `0` outside the `baseSet`, which
`geodesicChartDomain_eq_trivBaseSet` identifies with the set of `z` whose foot
lies in `(chartAt H p).source`.

Structurally this is the reason `expDomain g p` is *chart-anchored*: it is cut
out by the existence of an integral curve of this field, and such a curve cannot
leave the chart at `p` while moving.  See the module docstring — in particular
the honesty note on the resulting fidelity gap with
`def:pet-ch5-exponential-map`. -/
theorem geodesicVectorFieldChart_eq_zero_of_notMem (g : RiemannianMetric I M) (p : M)
    (z : TangentBundle I M) (hz : z.proj ∉ (chartAt H p).source) :
    geodesicVectorFieldChart (I := I) g p z = 0 := by
  have hz' : z ∉ geodesicChartDomain (I := I) (M := M) p := hz
  rw [geodesicChartDomain_eq_trivBaseSet (I := I) (M := M) p] at hz'
  exact Trivialization.symm_apply_of_notMem _ hz' _

end Geodesic

end PetersenLib

end
