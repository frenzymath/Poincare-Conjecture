# Direct wall route

The checked wall artifacts are:

- `Preparation/Chart.lean` and `Band.lean`: normalize an actual terminal
  chart over its whole restricted source before choosing fresh exterior
  strips, with the larger source square needed by side rounding;
- `Preparation/EndSelection.lean` and `Side.lean`: choose the actual lower
  annular end from a connected negative anchor and construct the exact
  joining collar from first-paired terminal strips, then fill an ambient side
  ball retaining the actual lower cap and the rounded band through a positive
  height;
- `Preparation/Filling.lean` and `UpperFilling.lean`: fill either actual
  joining collar, with a continued circle family and explicit auxiliary
  closing cap; the upper construction reverses physical height;
- `Preparation/Surface.lean` and `HeightCuts.lean`: decompose the entire
  actual terminal sphere into the central band and capped ends, and identify
  their unions exactly with the physical sublevel and superlevel surfaces;
- `Smoothing/Exterior/Construction/Pair.lean`: construct both actual side
  families with a common smoothing profile and height interval;
- `Arc/Separation/Orientation/`: actual positive anchors, chart and height
  reversal, selection of the actual upper annular end, and both lower anchors
  with fixed strip labels chosen from one recut;
- `Arc/Separation/Nested/Vertical.lean`: a compact separator through the
  nested annulus, made exactly vertical in a smaller square by a supported
  ambient correction;
- `Smoothing/Exterior/Caps/Split/Marked/ShearPair.lean`: two explicit smooth
  balls with a common smooth wall disk, retaining the physical height;
- `Attachment/ProfileCap.lean`: construct the spherical markings and
  rounded attachment for compatible caps carrying the same smoothing profile
  as the actual saddle sides;
- `Attachment/PlanarPair.lean`: simultaneously match two planar disks that
  meet on protected boundary arcs, fixing a neighborhood of both arcs;
- `Attachment/ProfilePair.lean` and `ProfileSymmetry.lean`: construct the
  common markings from actual profile arcs and use one isotopy to match the
  touching disks to opposite profile caps; the half-turn and transverse
  reflection give exactly the same cap disk;
- `Attachment/MarkedComplement.lean`, `TouchingBalls.lean`, and
  `LocalAttachment.lean`: construct the connected complement of a marked
  boundary disk and derive exact filled intersection from one local contact;
  rounded attachment then needs no global halfspace bounds on the balls;
- `Attachment/SliceBounds.lean` and `SlabAttachment.lean`: propagate boundary
  bounds through compact horizontal sections and construct the rounded
  attachment from opposite boundary signs in just one open height slab;
- `Attachment/WallDisk/`: construct a globally injective smooth marking with
  full derivative rank for the entire contact region joining the actual
  continuation width to the cylindrical profile cap, including both poles;
- `Preparation/PrescribedCap.lean`: fill an actual lower side using a
  prescribed endpoint disk and its canonical closing cap;
- `Preparation/ProfileSide.lean`: close that actual lower side with a
  prescribed height-preserving profile cap having a cylindrical base collar,
  using whole-cap replacement that fixes the actual lower end and side band;
- `Arc/Separation/Orientation/Touching.lean`: derive the exact common segment
  of two filled positive slices from the signed local and exterior formulas;
- `Smoothing/Exterior/Caps/Matching/`: derive a full ambient wall germ from a
  flat parameter arc of an embedded circle, apply it to the actual rounded
  profile, and recover the local filled side from the boundary sign;
- `Arc/Certificate.lean`: the central vertical wall and explicit exterior
  planar disk certificates, plus the smooth embedded-sphere frontier lemma and
  the rounded-union frontier bridge;
- `Arc/Separation/Disjoint.lean`: a constructed smooth proper separating line
  and clear strip for two disjoint filled planar disks. Agreement with the
  prescribed Morse-square wall is not yet established;
- `Arc/Separation/CirclePair.lean` retains both nesting alternatives for actual
  smooth circles; `RelativeGraph.lean` constructs a compact correction matching
  the central vertical segment from an explicit clear graph collar;
- `Arc/Separation/Ribbon.lean` constructs the relative vertical wall from the
  disjoint cut disks and actual ribbon, discharging the graph-collar input.
  Clearance from all nearby level curves remains to be established;
- `Arc/Separation/Nested.lean`: a proper wall through the central negative
  ribbon of a nested cut must cross the outer cut circle. If the wall is
  vertical inside the Morse square, the crossing lies on the exterior strip;
- `Surface.lean`: frontier reduction allowing the internal wall face on each
  side frontier and cancelling it using interior membership in the union;
- `Side/Family.lean`: disk transport for an already smooth circle family;
  wall-contact marks are independent of this construction;
- `Side/Critical.lean`: at height zero the left saddle level meets the wall
  only at the saddle point; `Side/CriticalFamily.lean` proves that both distinct
  smooth-family wall marks cannot belong to this critical slice;
- `Corner/Coordinates.lean` and `Corner/Frontier.lean`: a polynomial ambient
  chart for the two corner bodies, their exact frontiers, and cancellation
  of the internal wall face when the bodies are glued;
- `Corner/Local.lean`: frontier identification inside ambient corner charts
  and the exact frontier agreement implied by rounding, outside the closure
  of the prescribed edge neighborhood;
- `Smoothing/Profile.lean`, `Region.lean`, and `Localization.lean`: a smooth
  monotone corner profile and an explicit height-preserving ambient shear.
  Every positive smoothing scale produces a smooth side contained in the
  raw polynomial saddle side, agreeing with it outside an explicit open
  edge neighborhood;
- `Smoothing/Contact.lean` and `AttachmentGeometry.lean`: construction of
  both rounded sides from the smoothing scale alone. Their intersection is
  exactly a trimmed wall, with a positive first-contact height, and their
  germs above that height are opposite closed halfspaces;
- `Smoothing/Slices.lean`: jointly smooth parametrizations of every height
  slice of the rounded local boundary, each a smooth embedded line;
- `Smoothing/Exterior/Collars.lean`: the actual central exterior-strip
  decomposition supplies fixed endpoint rectangles inside the Morse patch
  throughout a smaller height interval;
- `Smoothing/Exterior/TailSplice.lean`: actual embedded saddle-chart data
  produces a smooth rounded patch agreeing exactly with the original
  parametrization on its negative tail;
- `Smoothing/Exterior/Anchor.lean`, `TailTransport.lean`, and `Parameters.lean`:
  actual negative-level anchor circles and smooth exterior-strip parameter
  families preserving the Morse transverse coordinate on the overlap;
- `Smoothing/Correction/DiagonalProfile.lean` and `DiagonalChart.lean`:
  a shared transverse graph coordinate for the rounded side and saddle body,
  with exact agreement on the negative tail;
- `Smoothing/Correction/Cutoff.lean`, `Supported.lean`, and `Frontier.lean`:
  a compactly supported correction of the constructed local side, with exact
  saddle-body and frontier agreement on a neighborhood of the critical point;
- `Side/Ball.lean`: a checked ambient side-ball model, including the
  height-preserving transport formula from the planar family (published at
  `125247a3e`);
- `Attachment.lean`: the historical rounded-attachment consumer. Its
  universal `rounded_frontier` requirement is inconsistent, as proved in
  `Attachment/Obstruction.lean`; this interface cannot have a geometric producer;
- `Attachment/Collar/Transverse.lean` and `Prescribed.lean`: construct an exact
  straight transverse collar on a compact patch of a known ball boundary.
  An outward field on the patch is extended to the whole boundary, and the
  ball is reparametrized without changing its image. `Marked.lean` retains
  this exact collar while normalizing the marked disk by radial extension.
  Applying this to the actual side balls and marked sweep remains a separate step;
- `Attachment/Collar/Common/`: align the orthogonal marked-disk frames and
  construct common parametrizations on an open collar of an enlarged shared
  boundary disk. Combining them with the checked common-compression theorem
  constructs a compactly supported matching of known balls, fixing a protected
  closed region. Local agreement of the sphere parametrizations and their
  filled inward sides supplies the positive normal derivative. The actual
  wall-plus-upper-cap common disk remains an application obligation;
- `Attachment/Collar/Common/BodyGerms.lean` removes the prescribed-field
  inputs: local inclusion of the actual open filled bodies determines the
  common outward field and hence the common collar. `Matching.lean` constructs
  the protected-region matching directly from those geometric germs;
- `Attachment/WallDisk/EnergyCollar.lean` and `WeightedEnergy.lean` construct
  exact matching of wall defining functions near the entire boundary circle,
  preserving the disk. This avoids rescaling the flat saddle profile itself.
  `RadiusFactor.lean` retains its positive factor on an open neighborhood of
  the full height interval, including both endpoints;
- `Attachment/Slab.lean` and `Edge.lean`: construct a selected rounding with
  its exact cutoff graph and an open neighborhood of the common edge on which
  it fixes both the original ball and its boundary;
- `Attachment/Frontier.lean` and `Boundary.lean`: prove the complete boundary
  formula for that constructed rounding and produce the ambient ball with this
  explicit boundary from the marked-ball attachment hypotheses;
- `Attachment/Disk.lean` and `Removal/Disk.lean`: construct the spherical
  markings from the physical common disk. Opposite boundary-side bounds give
  the filled intersection for attachment; non-strict boundary containment
  gives filled containment for removal;
- `Attachment/GraphCorrection.lean`: correct the entire selected surface using
  its local graph, the target graph, and their agreement outside the correction
  region. No filled-side description of the target surface is required;
- `Attachment/SurfaceChart.lean`: construct an exact ambient graph neighborhood
  of the actual saddle surface from its smooth embedding and Morse chart,
  excluding remote sheets through the embedding topology;
- `Attachment/ActualCorner.lean`: transport the polynomial rounded-side
  correction into the actual saddle chart, with exact equality to the entire
  sphere near the saddle and compact support inside any prescribed graph
  neighborhood. `Corner/Dilation.lean` constructs contractions preserving
  both corner sides and the saddle frontier to localize that support;
- `Flattening/Normalization.lean`: normalize a smaller saddle patch after
  strip flattening, retaining exact vertical-strip formulas for the composed
  map and its transformed central traces;
- `Arc/Separation/Square/Signed.lean` and `Square/Rounded.lean`: construct the
  full-square wall with strict and weak coordinate signs, then place every
  rounded local saddle slice in the signed near-critical region;
- `Smoothing/Exterior/Negative/Annular.lean`: recover an entire actual
  negative annular level from the pasted circle by the immersed-circle
  surjectivity theorem, including its moving endpoints;
- `Smoothing/Exterior/Caps/Split/Body.lean`: identify the canonical cap side
  bodies and their shared wall as a radial closed half-disk;
- `Smoothing/Exterior/Caps/Filling/`: fill each actual lower or upper annular
  end with a transported canonical closing cap;
- `Smoothing/Exterior/Caps/Replacement/`: replace a normalized cap by its
  actual terminal end while fixing the complementary halfspace, including
  its filled-body intersection and all marked points;
- `Smoothing/Exterior/Caps/Continuation/`: construct an actual annular
  continuation agreeing pointwise with the pasted family on its negative collar;
- `Attachment/Removal/Slab.lean` and `Removal/Boundary.lean`: give the
  analogous selected supergraph and complete boundary formula for the nested
  removal alternative;
- `Side/Filled.lean`: propagate coordinate side inequalities from a circle
  boundary through its compact Schoenflies disk and prove the exact intersection
  of two filled disks from opposite wall-side bounds;
- `Attachment/Obstruction.lean`: construct an arbitrarily localized boundary
  perturbation, preserving the body outside its neighborhood, and prove that
  the universal-frontier `AttachmentData` has no inhabitants;
- `Terminal.lean`: the saddle reduction facade, which invokes the exact
  flattened-band extraction in `Flattening.lean`, retaining the critical-plane
  fixed points, smooth strip sources, and exact strip flattening, packages it as
  `TerminalFlattenedBandData`, and passes that data into the wall producer.

The actual terminal producer remains unproved. Two distinct wall marks on the
raw critical slice would collapse to the single saddle point, while the
constructed smoothing first reaches the wall at a positive height. The disk
and ball consumers therefore require no wall marks. Each raw side is a body
with corners, whereas `AttachmentData` asks for smooth ambient ball images.
These are distinct geometric stages. The polynomial local corner smoothing is
now constructed in `Smoothing/`, including its splice with the actual exterior
strips. Actual sides can be filled with auxiliary closing caps. The shared
profile-cap construction now supplies compatible closures from a common
planar normalization and the exact planar contact equations.

`Attachment/ClosedSides.lean` now constructs the full common smooth disk and
filled intersection from the piecewise boundaries of profile-closed sides.
`WallDisk/CapJoin.lean` identifies the reflected upper-cap intersection and
joins it to the continued band. `Preparation/MovingProfileSide.lean` closes an
actual lower end and band using a height-varying cap collar, with no separate
planar filling assumption. `Preparation/ConjugatedContinuation.lean` performs
the continuation in flattened coordinates before returning to the original
ambient coordinates. `Preparation/NormalizedPair.lean` constructs both actual
lower-end balls in one normalized frame, proves the joining-circle identities,
and constructs their common disk and exact filled intersection.
`Preparation/PlanarNormalization.lean` lifts the common planar map through the
physical flattening and proves that fixing the terminal wall interval preserves
every earlier contact slice. `Preparation/SelectedPair.lean` constructs that
common correction and both actual side balls from the selected planar matching.
`RelativeSelectedPair.lean` synchronizes the two actual relative-height collars
and supplies all absolute-height filling parameters. `Attachment/LocalNesting.lean`
propagates nesting from one interior boundary point to the entire filled ball.
`Attachment/CapAgreement/` derives the actual filled upper region from the
piecewise boundary alone, using the connected sides of the explicit cap.
`Preparation/SelectedNestedPair.lean` now constructs the nested actual pair,
retaining the shared cap correction and proving full filled containment from
the explicit northern cap witness. `NormalizedNestedPair.lean` constructs the
same filling directly from compatible affine-height cap data, and
`Attachment/NestedClosedSides.lean` constructs its complete smooth wall disk.
`Preparation/TerminalSelection/Construction/Pair.lean` now instantiates both
planar alternatives from the same terminal selection, retaining the original
pasted bands, labels, common coordinate maps, actual balls and common disk.
`Construction/Rounding.lean` constructs a selected rounded ball in either
case, with its full boundary graph and exact filled union or removal outside
any prescribed open neighborhood of the wall edge.
`Attachment/CapAgreement/Band.lean` and `Family.lean` identify the actual filled
sections from the boundary circles, preserving any prescribed smooth family
of planar disk charts. `Continued.lean` applies this to the complete middle
band of the constructed side balls, including the common upper time change.
`Smoothing/Correction/PrescribedFrontier.lean` corrects the profile already
selected by the terminal construction and identifies both its body and
frontier near the saddle. The remaining terminal integration must compare the
selected rounded boundary with the original whole sphere, including its actual
upper end; the local profile correction alone does not prove that comparison.
`Attachment/ExposedBoundary.lean` identifies the exposed frontier for both
union and nested removal away from contact. `ExposedSphere.lean` transfers
that identity to a selected rounded ball, and `CapAgreement/Lower.lean`
proves that the two actual lower boundary pieces survive either operation
below the band. `Smoothing/UnionFrontier.lean` identifies the complete exposed
profile frontier and its wall-edge parabola, excluding the interior wall face.
`CapAgreement/TerminalLower.lean` uses the actual annular-end decomposition
to identify that lower boundary with the original terminal sphere in the
common ambient coordinates, in both branches.

`Attachment/Collar/Common/` constructs common collar coordinates from the
actual filled germs of two known balls, and then a relative ambient matching.
`Attachment/WallDisk/EnergyCollar.lean` constructs a plane diffeomorphism
matching two smooth defining energies near the entire disk boundary. Its
retained formula proves that the matching fixes every germ on which the
energies agree. `PlaneCoordinates.lean` and `EnergyTransport.lean` apply this
to the physical width energies of two wall disks, including both tips.
`PlaneLift.lean` gives one ambient lift acting simultaneously on both opposite
profile inequalities. The profile function itself is retained exactly.
`ProfileTransport.lean` extends this comparison across the entire filled wall
using vanishing of the profile on nonnegative energies. `BodyTransport.lean`
then compares the actual filled side germs under that one lift.
`ProtectedCollar.lean` and `ProtectedEnergy.lean` preserve any prescribed
compact region while correcting the remaining circle collar, assuming only
identity or energy agreement germs where that region meets the circle.

`Attachment/RelativePair/` constructs a common map for both disjoint and
nested pairs from immersed wall marks and actual filled-body germs. Each map
fixes an open neighborhood of the whole common wall. The protected disjoint
variant permits different enlarged marks and fixes a specified closed
rounding region meeting each ball only in its own mark. This stronger
retention matters: an unspecified wall neighborhood need not contain an
already chosen rounding patch. The quantitative whole-surface comparison
remains an integration obligation.

`Transport/NeckMark.lean` constructs explicit enlarged profile marks covering
the complete contact of the inserted neck with either model ball. Their
radii are chosen from the finite neck bound. `Transport/Inserted.lean` shows
that fixing the added material suffices to transport its filled union and
entire frontier. `WallDisk/PhysicalProtected.lean` retains a prescribed
compact transition patch during the physical energy comparison; the
`TerminalComparison/Height/` and `Plane/Joined.lean` producers calibrate and
retain the actual lower quadratic patch. `RelativePair/Protected/InteriorBall.lean`
constructs a correction fixing a known boundary-attached auxiliary ball
while preserving its outer ball. Applying it to the nested removal requires
an auxiliary-ball construction; the removed annular region is not assumed
to be a ball.

`Attachment/Transport/Gap/` constructs compactly supported increasing energy
clocks, their jointly smooth isotopies, and a compactness bound placing small
profile gaps in any prescribed neighborhood of the wall edge. Both the entire
added neck and the entire removed neck have energy at most `a + δ^2`.
Conjugating a pair matching by a common body-preserving compression then fixes
this whole finite gap. `TerminalComparison/Compression/` constructs the profile
ratio, localizes it in the invariant transverse coordinate, and supplies the
supported fiber compression. `Gap/ThinSupport.lean` allows any transverse
enlargement factor greater than one, and `Clearance.lean` chooses its support
from the existing strict strip margins. `ModelCompression.lean` constructs an
ambient compression preserving all three complete model balls. The actual
joined-wall ambient compression is also constructed. Their common application
is now proved in `Gap/FiniteMatching.lean`: finite agreement of the pulled-back
actual bodies with the model produces a pair matching retaining the entire
gap, regardless of the original fixed-neighborhood width.
`Gap/RoundedTransport.lean` then constructs the filled target and its entire
frontier in both alternatives, using the prescribed coordinate map for all
added or removed material. Applying these results still needs the actual
finite upper-cap comparison, retention of the lower quadratic patch, and
identification of that modified body's frontier with the terminal sphere.
`Gap/InitialPair.lean` and `NestedPair.lean` construct the initial global
matching from the actual closed-body wall germs. `Gap/Filling.lean` combines
this with finite compression and the selected model rounding, eliminating
both the supplied global matching and the rounding callback. `PlaneBounds.lean`
keeps finite energies inside the actual strip and cap chart; `ActualJoin.lean`
extends the selected filled-body comparison through the whole shallow front
of the cap joining plane. These comparisons remain inputs to the final
assembly until the protected planar selection and complete terminal-surface
identification are integrated.
`Gap/Neighborhood.lean` provides uniform transverse and energy clearance
inside any open neighborhood of the complete finite gap.
`SupportedCompression.lean` places the model compression in that neighborhood
while preserving all three complete model balls. `NeighborhoodMatching.lean`
and `NeighborhoodFilling.lean` therefore require actual body comparisons only
near the finite gap. Their constructed fillings retain the exact inserted or
removed material and its whole frontier. This removes the stronger rectangular
comparison premise from the application; the actual neighborhood comparisons
and terminal-surface identification are still separate obligations.

The checked pasted-circle family is deliberately recorded as a surrogate
family. Its negative anchor slice is the actual terminal circle and its
exterior strip pieces are actual, but the central rounded profile leaves the
original surface away from the negative tail. Its range therefore cannot yet
be identified with the terminal level set. The remaining comparison must
compose the local supported frontier correction with the global attachment, or
construct the moving endpoint reparametrization and then make the same
correction. This is why the terminal producer still does not claim the
original range `range g`.

Moreover, `exists_rounded_attachment` identifies bodies only outside the
chosen edge neighborhood. The `rounded_frontier` field is not merely unproved:
its quantification over every such rounding is contradictory, because a
compact perturbation inside that neighborhood changes the frontier while
preserving all exterior conditions. The selected rounding must instead be
compared explicitly with the actual terminal sphere. The exact graph and
protected edge germ of that selected rounding are now constructed.
The nested cut-circle configuration is an additional obstruction to the
proposed exterior-avoiding proper wall in the original planar chart: the
checked crossing theorem forces an intersection with an exterior strip.
These whole cut-circle disks cannot be treated as disjoint exterior disks.
The nested branch requires a different wall configuration or a removal step.
The current `Terminal.lean` theorem retains an external producer callback;
it is a conditional consumer, not acceptance of the terminal filling mission.
