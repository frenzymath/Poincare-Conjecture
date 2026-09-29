# Common closing disk alignment

The closing interface distinguishes a boundary disk from the filled
three-ball. For a complementary disk
`E = B '' sphere 0 1 \\ g '' ball 0 1`, and an enlarged disk whose image lies
on `B '' sphere 0 1`, the set identity proved by
`boundary_union_closing_disk` is

```lean
E ∪ g '' closedBall 0 1 = B '' sphere 0 1.
```

The analogous identity holds for the transformed model disk. The former
filled-ball equality is ruled out by `not_boundary_union_eq_filled_ball`:
the left side is contained in the boundary sphere, while the filled ball
contains the image of the centre. The common-disk construction therefore
has to supply a genuine shared boundary disk and its widened exterior collar
before the relative replacement can be applied.

## Checked interface

`exists_common_closing_disk_replacement` takes the common smooth planar map,
the two complementary boundary-disk equations, the enlarged shared-exterior
data, and the protected-set conditions. It returns the common compact disk,
its terminal height and circle, both boundary-sphere decompositions, and the
compactly supported ambient diffeomorphism fixed near the protected set.
The lower and upper wrappers use this same interface. The upper geometry
module proves that `upperCap` has terminal rim
`upperCap '' sphere 0 (sqrt (3 / 4))` at height `1 / 2`, while its open
interior has strictly larger height; consequently the upper rounded cap is
not itself a flat terminal disk. A future consumer must provide the rounded
collar-to-disk attachment that identifies its common closing disk.

## Rounded transport bridge

`Closing/Rounded.lean` records the attachment as an explicit closed-disk
transport bridge: a smooth planar diffeomorphism `F` agrees with the curved
complementary parametrization pointwise on the closed unit disk, and its
boundary image is the common planar circle. The checked producer
`exists_flat_closing_disk_of_rounded_transport` constructs the compact
terminal-plane disk, proves its height and circle identities, and identifies
the transported closed disk with the actual image. The consumer
`exists_common_closing_disk_replacement_of_rounded_transport` feeds those
data into the published shared-exterior replacement and returns both
boundary-union equalities and the ambient map. The bridge remains a genuine
geometric input to be supplied by the widened collar construction; no raw
flat disk is silently substituted for the rounded rim.

## Terminal disk constructions

`Terminal.lean` constructs independent actual and model ball fillings from
the original `TerminalSaddleData` disk charts. Each cap is the complement
of an open curved disk on its filling sphere. The filling interior avoids
the original sphere, and its intersection with the closed terminal band is
contained in the closed complementary disk. The actual construction accepts
the prescribed ambient lift and an arbitrary open neighborhood of the cap.
The same module derives exact band transport and labeled attaching-circle
reparametrization from the original `hplanar` and `hlabels` inputs.

`TerminalAnnuli.lean` derives enlarged outer annuli contained in the bands,
using compact separation from the other two caps and the original sphere
decompositions. `TerminalCollars.lean` transports the actual annulus and
constructs an open neighborhood of the labeled attaching circle in which
both annuli cover the model band. This is a common one-sided surface collar;
the actual and model complementary disks are still independent.

`Isotopy/GraphTransport.lean` supplies localized ambient transport of smooth
graphs over a compact parameter set. Its support lies in any open set
containing their straight vertical sweep, and every fiber with zero graph
displacement is fixed pointwise. `Collar/TerminalProjection.lean` constructs
the compatible smooth projected chart from the actual disk: agreement with
the model sphere on the outer annulus makes radial projection nonsingular
at the rim. Compact injectivity gives one chart around the entire circle.
`Collar/TerminalGraph.lean` derives its radial height and proves that the
height vanishes over the model band on a smaller open parameter domain.

`Collar/TerminalTransport.lean` now constructs a compactly supported ambient
matching of the actual and model collars from the original disk charts and
labels. It matches a closed neighborhood of the entire attaching circle
and fixes the whole model band pointwise. The curved sphere chart is retained
through the radial ambient coordinates; no flat closing disk is substituted.
This local collar matching does not yet identify the independent complementary
disks or replace the whole cap. Simultaneous cap replacement remains open.
In particular, pairwise disjointness within
each cap family does not assert disjointness between an actual cap and a
different model cap; a successive construction must track the moving family.

The `_within` producer localizes support in any prescribed open neighborhood
of the rim. `Collar/SeparatedTransport.lean` chooses that neighborhood to avoid
every other actual and model cap. `Collar/SurfaceGerm.lean` identifies the full
surface images near the rim; `Collar/CapGerm.lean` uses the band decompositions
and separation from the other caps to identify the cap images there as well.
Neither identification asserts equality of the complete caps.
`Collar/Composition.lean` composes the separated moves into one compactly
supported diffeomorphism matching all three cap germs while fixing the band.
The induction transports the earlier neighborhoods through later moves;
fixation of each earlier model cap preserves the corresponding germ equality.

`Isotopy/Relative/Localization.lean` localizes a smooth family along a compact
trace while retaining its stationary set. `HalfSpace.lean` applies this to
translation conjugates: any ambient map fixing a closed halfspace can be
reproduced on a prescribed compact set by a compactly supported map fixing
that same halfspace.

`Ends/TerminalNormalization.lean` and its upper counterpart normalize the
complete actual end, including the terminal cut. They retain physical annular
coordinates across the cut and fix the halfspace on the band side of the
inner normalization height. `SupportedNormalization.lean` gives these whole-end
identities with compact support. Their targets are a canonical curved tip
and the original annulus, not the requested model cap.

`Ends/ModelCritical.lean` finds a critical point strictly outside the terminal
band in each compact model disk. `ModelCenter.lean` derives the central
quadratic height germ directly from the recorded level sets and matching,
without an additional Morse-chart hypothesis. `ModelCriticalCount.lean`
combines this interior-band critical point, the disjoint cap domains, and the
four-point bound for either model to prove exactly one critical point per cap.
Constructing compatible whole-cap normalizers and their simultaneous relative
replacement remains open.

`Ends/Model/Coordinates.lean` constructs definite physical Morse charts at
the model cap extrema. `TerminalAnnulus.lean` extends their level annuli
through the terminal cut. `Model/TerminalNormalization.lean` combines these
with a compact preparation near the cut and canonical profile transport to
normalize each complete original model cap. `Actual/TerminalNormalization.lean`
does the same for the actual caps, including after a height-preserving ambient
map that fixes the original inserted caps. Each final normalizer agrees with
its own preparation on the band-side halfspace. These independent preparations
are not asserted equal. `Ends/RelativeAlignment.lean` cancels normalizers when
their ambient halfspace agreement has been proved.

`Collar/HorizontalChart.lean` constructs curved model coordinates whose fibers
preserve physical height. `HorizontalProjection.lean` expresses the actual
collar as a graph in these coordinates, deriving zero graph height on the
protected band from the original labels. `HorizontalTransport.lean` flattens
this graph with compact support in any prescribed physical rim neighborhood,
preserves physical height globally, and fixes the model band. This strengthens
the radial collar construction without replacing the curved complement by a
planar disk.

`Collar/TerminalLiftPreparation.lean` corrects the prescribed lift on the
entire terminal sphere by a compact map fixed on the middle slab. Its prepared
lift retains an explicit smooth time parameter, preserves physical height,
and fixes every original inserted cap parametrization. The `Ends/Family/`
modules derive a common physical regular slab for each end family and
straighten all its labeled annuli together, retaining one common planar
diffeomorphism at each end. This regular-slab result does not yet transport
the whole family through its distinct cap extrema.

`EndBall/TerminalHeight.lean` derives physical height on both sides of an
actual terminal cut from the recorded height germ. `TerminalSlices.lean`
extends the projected circles to a smooth disjoint family, and
`TerminalCylinder.lean` constructs simultaneous ambient straightening of
these circles. Its compact support lies in any prescribed positive height
slab, it preserves height, and it fixes the whole central plane. These
endpoint constructions use the original end family without extending its
connected-component or retained-region fields.
`TerminalAnnulus.lean` extends the original physical annulus across both its
cap rim and its terminal cut, including a cut at the endpoint of the recorded
retained interval. It retains the original chart and smooth inverse.

All declarations in `Closing/Checks.lean` are audited for only
`propext`, `Classical.choice`, and `Quot.sound`. This module records the
checked interface and the obstruction to the retired filled-ball premises;
it does not claim the still-open global common-disk construction.
