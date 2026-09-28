# Conditional Terminal Composition

## Informal description

Let a smooth sphere be a leaf of a sphere Morse reduction. Assume that, for
every first-paired normalized terminal saddle band with the constructed direct
rounded union or removal and its actual annular ends, there are two ambient
diffeomorphisms and a horizontal cut such that the second diffeomorphism maps
both parts of the first diffeomorphism's sphere into the terminal leaf. Then
the original leaf bounds an ambient image of the unit ball.

The single remaining hypothesis is `join_terminal_direct_pair`. It requires
one common correction for the lower and upper parts. Separate existence of
lower and upper corrections does not satisfy it.

## Informal proof

The terminal reduction either constructs an ambient filling immediately or
produces a normalized first-paired terminal band and an ambient map carrying
its leaf back to the original leaf. The direct wall construction supplies its
rounded union or removal, including the actual ends. Apply the assumed
compatible joining and compose with the ambient map back to the original
leaf. The two parts partition the sphere, giving containment in the embedded
leaf. Invariance of domain and compactness give equality.

## Proposed formal statements

```lean
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Terminal
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.TerminalSurface.TerminalPairing.Direct

noncomputable section
set_option autoImplicit false
open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereMorseReduction

open Saddle.Wall.Attachment.TerminalSurface.TerminalPairing
open PlaneArcs.Terminal.Reflection

theorem terminal_wall_certificate_of_direct_pair_joining
    {f : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → EuclideanSpace Real (Fin 3)}
    (M : SphereMorseReduction f)
    {g : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → EuclideanSpace Real (Fin 3)}
    (hg : g ∈ M.tree.leaves)
    (join_terminal_direct_pair :
      ∀ {f' : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → EuclideanSpace Real (Fin 3)}
        {p : sphere (0 : EuclideanSpace Real (Fin 3)) 1}
        (s : TerminalInputData f' p)
        (B : NormalizedBand (s.reduction.v : EuclideanSpace Real (Fin 3))
          s.leaf p s.path.core),
        B.FirstPairing → DirectPairConclusion s B →
        ∃ (F E : Diffeomorph (𝓡 3) (𝓡 3)
            (EuclideanSpace Real (Fin 3)) (EuclideanSpace Real (Fin 3)) ∞)
          (c : Real),
          E '' (F '' sphere (0 : EuclideanSpace Real (Fin 3)) 1 ∩ {q | q 2 ≤ c}) ⊆
            range s.leaf ∧
          E '' (F '' sphere (0 : EuclideanSpace Real (Fin 3)) 1 ∩ {q | c < q 2}) ⊆
            range s.leaf) :
    TerminalWallCertificate g := by
  rcases exists_filling_or_terminal_direct_pair M hg with hfill |
    ⟨f', p, s, T, hT, B, hfirst, hpair⟩
  · obtain ⟨F, hF⟩ := hfill
    refine ⟨F, Diffeomorph.refl (𝓡 3) (EuclideanSpace Real (Fin 3)) ∞, 0, ?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact hF.subset hq.1
    · rintro _ ⟨q, hq, rfl⟩
      exact hF.subset hq.1
  · obtain ⟨F, E, c, hlower, hupper⟩ := join_terminal_direct_pair s B hfirst hpair
    refine ⟨F, E.trans T, c, ?_, ?_⟩
    · rw [Diffeomorph.coe_trans, image_comp]
      exact (image_mono hlower).trans hT.subset
    · rw [Diffeomorph.coe_trans, image_comp]
      exact (image_mono hupper).trans hT.subset

end Poincare.Manifold.Schoenflies.SphereMorseReduction
```

## Informal Translation

Let a map from the unit sphere to Euclidean three-space have a sphere Morse
reduction, and let another map be a leaf of its tree. Suppose universally that
every terminal input and normalized band satisfying first pairing and the
direct-pair conclusion admits smooth ambient diffeomorphisms F and E and a
real cut c, with E mapping both the portion of F's sphere below or at c and
the portion strictly above c into that terminal input's leaf. Then the original
leaf has a terminal wall certificate.

## Alignment Review

An independent formal-only translator and a separate prose-only reviewer
accepted this conditional statement on 2026-09-24. The reviewer noted that the
ball conclusion uses the embedding of each leaf; this is supplied by
`M.tree.embedding_of_mem_leaves hg`. The existing definitions of normalized
terminal input and `DirectPairConclusion` retain the selected bands, actual
annular ends, and constructed rounded union or removal.

## Scope

This is the conditional composition requested by mission revision 4. It is
not a proof of compatible joining or of the unconditional terminal filling.
The frozen `TerminalFlattenedBandData` and `TerminalWallCertificate` definitions
are unchanged. The composition reconstructs the stronger normalized band from
the terminal reduction instead of inferring that stronger data from flattened
level identities alone.

## Remaining Joining Obligation

The existing direct-union and direct-removal upper replacement theorems give
a correction fixing the joining plane and a lower halfspace. The lower
transport theorems give a different height-preserving correction mapping the
rounded sphere below the cut to the actual terminal surface. Their conclusions
do not identify the corrections on the intervening collar.

In particular, `exists_prescribed_cap_transport_to_actual_upper_end_with_collar`
in `Attachment/TerminalSurface/UpperReplacement/PhysicalTransport/Prescribed.lean`
maps the closed model cap and its latitude collar, whereas
`exists_direct_union_actual_lower_transport` and
`exists_direct_removal_actual_lower_transport` in `Middle/ActualUnion.lean` and
`Middle/ActualRemoval.lean` map the retimed lower boundary. To compose them one
must show that the points of the lower boundary in the support collar of the
upper correction still map into the actual sphere. Equatorial trace inclusion
alone does not provide this neighborhood statement.

The cap theorem on main,
`Saddle.Caps.Closing.exists_relative_upper_end_replacement_of_surface_germ`,
requires equality of the two surface ranges on an open neighborhood of the
rim, together with the isolated maximum disk and annular chart data. The
current direct-pair interface has not produced that equality for one common
corrected rounded sphere. The recovered cylindrical frontier lemmas establish
model collar identities, not this physical surface-germ equality.

Thus direct substitution of the existing producers leaves this geometric
premise unproved. Under the mission's stop rule, the conditional composition
is the stopping artifact; no unconditional filling or objective completion is
claimed, and no further smoothing or attachment theory is introduced.
