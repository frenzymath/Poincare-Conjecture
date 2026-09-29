# Terminal strong-neck stability

## Informal proof

Use the full terminal embedding witness. Restrict each embedding to time zero,
and compose its spatial map with the limit neck map on the smaller cylinder.
The spatial maps are smooth with smooth inverses, preserve the basepoint, and
are independent of time. Compactness places the closed smaller cylinder inside
one exhaustion stage. Terminal halfspace jets give ordinary spatial jets
uniformly on the closed backward slab. Subtracting the limit metric at an
arbitrary moving time gives vanishing spatial errors, to which bounded spatial
coordinate changes apply. Uniform evolving-cylinder covariant-jet estimates
then absorb the error into the strict delta-to-epsilon margin. The source
basepoint scalar normalization makes the neck scale and duration exactly one.

## Proposed formal statements

```lean
namespace PoincareMT

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalStabilityCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

theorem M23TerminalExtension.eventually_strongEvolvingNeck
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (hterminal : M23TerminalExtension G)
    {δ ε : ℝ} (N : StrongEvolvingNeck G.limit.flow 0 δ)
    (hcenter : N.center = G.limit.base) (hδε : δ < ε) (hε : ε < 1 / 4) :
    ∀ᶠ k in Filter.atTop,
      ∃ Nk : StrongEvolvingNeck (S.term (G.subsequence k)).flow 0 ε,
        Nk.center = (S.term (G.subsequence k)).base ∧
        Nk.duration = 1 ∧ Nk.terminal_neck.scale = 1 := by
  sorry

end PoincareMT
```

## Informal translation

Let a normalized sequence of connected three-dimensional ancient kappa-solutions
converge along its selected subsequence to a normalized pointed ancient
kappa-solution. Suppose the interior embeddings have the full M23 terminal
extension: they agree on their interior domains, preserve the time-zero basepoints,
have time-independent spatial maps, and give smooth convergence through zero
from the past. The terminal limit is complete, bounded-curvature and
noncollapsed. If its basepoint is the center of a strong evolving delta-neck,
then for every delta < epsilon < 1/4, all sufficiently late selected source
basepoints are centers of strong evolving epsilon-necks with duration and
terminal scale equal to one. Their comparison uses the full slab (-1,0].

## Alignment review

The independent translator and reviewer accepted the statement: the sequence
is the selected convergent subsequence, normalization gives scale and duration
one, and the full terminal witness includes base preservation and spatial
time-independence. The displayed candidate fixes the exact theorem target;
the proof in `Stability.lean` replaces its candidate admission.

## Verification

With Lean 4.33.1, the managed
`PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Stability`
build passes. The adjacent `Check` target prints exactly `propext`,
`Classical.choice`, and `Quot.sound` for the final theorem; there is no
`sorryAx` in its dependency closure. The check helper used its local-cache
fallback while build coordination was unavailable. `make check` passes the
full library build and all 12 frozen contract hashes. The full M23 terminal
witness is an explicit theorem hypothesis, with its construction tracked by
the existing M23 graph dependency.

## References

Morgan and Tian, *Ricci Flow and the Poincare Conjecture* (2007),
Proposition 9.79(4); application in Proposition 9.85, pp. 237--239.
