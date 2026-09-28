# Height orientation of the terminal saddle target

## Checked obstruction

`Obstruction.lean:exists_input_without_terminal_matching` proves the following.
Given any complete tuple of the original hypotheses of
`SaddleLevel.saddle_planar_family_leaf`, there is another complete tuple at
the same critical point, whose initial embedding is either the original
embedding or its height reflection conjugated by the initial ambient
perturbation, for which no terminal data and no height-indexed planar
diffeomorphisms match all slices. The excluded family need not be continuous
in height, compactly supported, or part of an isotopy.

`TerminalInputs.lean:TerminalInputData` contains exactly the original input
fields, including the chart-target inclusion. It contains no terminal
geometry, matching map, isotopy, or end-count assumption. Its
`exists_reflected` theorem constructs every reflected field, including the
Morse reduction, surgery path, protected values, preserved caps, unique
critical point, and chart. The source core and chart target are unchanged.

This is a conditional counterexample construction. It requires an original
input tuple and does not prove that such a tuple exists. In particular, it
must not be cited as a closed refutation of the universally quantified leaf.
It does prove that the universal planar matching assertion would force the
entire original terminal saddle input class to be empty.

## Argument

The actual saddle cut resolution constructs three annular ends, with one
end on one side and two on the other. If the lower side has one end, use
the original input. Otherwise, reflect the physical height and exchange
the two Morse coordinates. Reflection exchanges the annular ends while
preserving every original input hypothesis.

The resulting input has a connected lower level near its saddle. Regular
height transport makes this property independent of the chosen terminal
cut. Both permitted models have two lower level components near their
saddle. A planar diffeomorphism cannot identify a connected set with that
disconnected set. This excludes every existential choice of terminal data,
not merely a particular flattened model.

## Contract Review Required

Root cause: `TerminalSaddleGeometry.model_kind` permits only `Saddle.shear`
and `Saddle.Nested.shear (3/10)`. Together with `scale_pos` and
`transport_height`, this fixes the two-lower-end orientation, whereas the
original input class is closed under height reflection.

Proposed remedy: permit the height-reflected versions of both models and
derive the choice from the actual annular ends. Transport the model band,
caps, local chart, and height convention consistently. Adding an end-count
or matching hypothesis to the leaf would not meet the mission's acceptance
criterion.

Owner: `global-saddle-ambient-matching`, which owns `Global/TerminalData.lean`
and `Global/Leaves.lean`, with the operator and roadmap maintainer reviewing
the revised contract. The Arcs worker has not changed those files.

Unlock condition: a reviewed terminal-data contract supporting both height
orientations is published, with the exact amended leaf statement. The
checked `SelectedData.lean` producer already constructs the complete labeled
family in the two-lower-end case; the reflection constructors here supply
the original-input symmetry needed for the opposite case.

## Verification

The named `Reflection.Obstruction` build and `Arcs.Checks` build passed.
The obstruction and its recursive dependencies use only `propext`,
`Classical.choice`, and `Quot.sound`; they do not use the admitted leaf.
Formal-only translation, prose-only alignment, and an independent proof
review accepted the precise conditional statement above.

## Reference

Hatcher, *Notes on Basic 3-Manifold Topology* (2014), Theorem 1.1,
proof pp. 2-5. The reflection compatibility and obstruction above are
auxiliary results for this formalization, not separately numbered results
in that source.
