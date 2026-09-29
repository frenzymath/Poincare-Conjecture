# PoincareLib

`PoincareLib` is organized by mathematics rather than by milestones or source
chapters. A milestone should be proved by importing the semantic modules that
implement its prerequisites; its coordination number must not become a library
namespace or directory.

Use focused files with narrow imports. Prefer established mathlib concepts and
naming. New subject areas should receive their own nested directory, while
cross-cutting utilities should be placed at the lowest mathematically natural
level. Move and rename modules when that improves the dependency structure.

The reviewed M05-M07 interfaces are preserved outside the build in
`../../archive/PoincareConjecture/contracts/`. Those snapshots constrain theorem statements, not the internal
organization of this library.
