import PetersenLib.Ch01.CoveringMetrics
import Mathlib.Topology.Covering.Basic

/-!
# Petersen Ch. 6, §6.2 — deck transformations (GTM 171, 3rd ed.)

Petersen's §6.2 (p. 264), `def:pet-ch6-deck-transformation`: for the universal cover
`π : M̃ → M`, a **deck transformation** is a map `F : M̃ → M̃` with `π ∘ F = π`. Petersen's
accompanying remarks: `F` is determined by the single value `F(p) ∈ π⁻¹(q)` for a chosen
`p ∈ π⁻¹(q)`; the fundamental group `π₁(M, q)` acts by deck transformations (a loop `[α]`
lifts to `α̃` with `α̃(0) = p` and yields the deck transformation with `F(p) = α̃(1)`); and
**in the Riemannian setting deck transformations are isometries of `M̃`, since `π` is a
local isometry**.

That last sentence is what this chapter actually consumes — via
`lem:pet-ch6-deck-transformation-dilation` (Lemma 6.2.8), which needs `δ_F` to be an
honest displacement function of an *isometry* before Lemma 6.2.7 can produce an axis — and
it is what `DeckTransformation.isRiemannianIsometry` below delivers.

## Reuse: the Riemannian content is already in Ch. 1

`Ch01/CoveringMetrics.lean` already builds the covering-induced metric
`coveringInducedMetric gN π hπ` (pull back the base metric along the local diffeomorphism
`π`, §1.3.3) and already proves that any diffeomorphism commuting with `π` is an isometry of
it (`coveringInducedMetric_deck_isRiemannianIsometry`). So Petersen's "deck transformations
are isometries" needs no new analysis here: the theorem below is a one-liner projecting the
`π ∘ F = π` component of the definition into that Ch. 1 lemma. Before writing anything new
in this area, look in Ch. 1 first — that is where the covering/isometry infrastructure
lives.

## Design notes

* **`F` is a `Diffeomorph`, not a bare map.** The blueprint says "a map `F : M̃ → M̃` with
  `π ∘ F = π`", which in the *topological* setting is enough (continuity plus the lifting
  property already force a homeomorphism). But the blueprint's own concluding claim — deck
  transformations are isometries of `M̃` — is a *smooth/Riemannian* statement and is false to
  even state for a non-smooth `F`. For a smooth covering, deck transformations are
  automatically diffeomorphisms, so requiring it costs nothing mathematically while making
  the isometry conclusion expressible. Deriving smoothness from continuity (via smooth
  lifting) is a genuine theorem this project does not have; requiring it here is the honest
  trade, and it is the same convention Ch. 1 already uses.
* **Smoothness index `∞`, never `⊤`.** `Diffeomorph I I M M ∞` is the smooth category. In
  `WithTop ℕ∞`, `⊤ = ω` is the *analytic* category, which is strictly stronger and not what
  Petersen means. Ch. 1's covering API is stated at `∞`, so `⊤` would also simply fail to
  connect to `coveringInducedMetric_deck_isRiemannianIsometry`.
* **`IsCoveringMap π` is bundled into the definition** rather than left as ambient context,
  so that "`F` is a deck transformation" is self-contained — it carries the covering it is a
  deck transformation *of*. Universal-ness (simple connectivity of `M̃`) is *not* required:
  none of the statements above need it, and Lemma 6.2.8 will supply it as a hypothesis where
  it is genuinely used (in the free-homotopy argument).

## Scope

The definition and the isometry property are here. Not here: the `π₁(M, q)`-action and the
"determined by `F(p)`" rigidity, both of which need the lifting/monodromy machinery for
covering spaces rather than Riemannian geometry; and Lemma 6.2.8 itself.
-/

open Set
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** Petersen §6.2 (p. 264), `def:pet-ch6-deck-transformation`: `F` is a **deck
transformation** of the covering `π : M → M'` when `π ∘ F = π`, i.e. `F` permutes each fibre
`π⁻¹(x)`.

Here `M` is the covering space (Petersen's `M̃`) and `M'` the base. `F` is taken to be a
diffeomorphism of `M`: this is automatic for deck transformations of a smooth covering, and
it is what makes the definition's whole purpose — "deck transformations are isometries of
`M̃`", `DeckTransformation.isRiemannianIsometry` — a statement one can even write down. Use
`∞` (smooth), never `⊤` (`= ω`, analytic). See the module docstring. -/
def DeckTransformation (π : M → M') (F : Diffeomorph I I M M ∞) : Prop :=
  IsCoveringMap π ∧ π ∘ (F : M → M) = π

/-- **Math.** Petersen §6.2 (p. 264), the operative claim of `def:pet-ch6-deck-transformation`:
**deck transformations are isometries of the covering-induced metric on `M̃`**, because `π`
is a local isometry for that metric and `F` commutes with `π`.

This is the hinge the rest of §6.2 turns on: `lem:pet-ch6-deck-transformation-dilation`
(Lemma 6.2.8) studies the displacement function `δ_F` and hands the result to
`lem:pet-ch6-axis-existence` (Lemma 6.2.7), which is a statement about isometries.

The proof is entirely Ch. 1's: `coveringInducedMetric` pulls the base metric `gN` back along
the immersion `π` (§1.3.3), and `coveringInducedMetric_deck_isRiemannianIsometry` already
shows any `π`-commuting diffeomorphism preserves it. Only the `π ∘ F = π` component of
`DeckTransformation` is used — the `IsCoveringMap` component is not needed for the isometry
property, which holds for any local-diffeomorphic `π`. -/
theorem DeckTransformation.isRiemannianIsometry
    {gN : RiemannianMetric I' M'} {π : M → M'} (hπ : IsSmoothImmersion (I := I) (I' := I') π)
    {F : Diffeomorph I I M M ∞} (hF : DeckTransformation (I := I) π F) :
    IsRiemannianIsometry (coveringInducedMetric gN π hπ) (coveringInducedMetric gN π hπ)
      (F : M → M) :=
  coveringInducedMetric_deck_isRiemannianIsometry gN π hπ F hF.2

end PetersenLib
