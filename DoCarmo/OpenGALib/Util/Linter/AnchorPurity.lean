import Lean

/-!
# Anchor-purity linter

Enforces the OpenGALib "anchor files expose only `**Math.**`-tagged
declarations" rule: any top-level declaration whose docstring begins
with `**Eng.**` or `**Mixed.**` is forbidden unless the file lives
inside a `Util/` directory.

The rule applies to the anchor's **exposed math API**, not to file-internal
or framework-required plumbing. Two principled exemptions:

* **Typeclass `instance` declarations** — Lean's typeclass synthesis
  requires the instance to be visible wherever it is consumed; co-location
  with the type (rather than via a separate `Util/` import) is a real
  language constraint, not aesthetic choice. Same Mathlib convention.
* **`private` declarations** — invisible outside the file, so they do not
  participate in the anchor's exposed API. Their Eng/Mixed tag is internal
  documentation, not API drift.

Declarations without docstrings and `**Math.**`-tagged ones pass silently.

See CLAUDE.md "Code quality / Engineering tax encapsulation".
-/

open Lean Elab Linter

namespace OpenGALib.Linter.AnchorPurity

/--
The OpenGALib anchor-purity linter.

Anchor files (everything outside `Util/`) should expose only `**Math.**`
declarations. Eng/Mixed declarations belong in the layer's `Util/`
sub-module. Exempts typeclass `instance` (synthesis co-location
required by Lean) and `private` declarations (not in the anchor's
exposed API).
-/
register_option linter.openGA.anchorPurity : Bool := {
  defValue := true
  descr := "Forbid **Eng.**/**Mixed.** docstring tags outside `Util/` folders."
}

private def forbiddenInAnchor : List String := ["**Eng.**", "**Mixed.**"]

private def startsWithForbidden (s : String) : Option String :=
  let t := s.trimAsciiStart.toString
  forbiddenInAnchor.find? fun tag => t.startsWith tag

/-- True when `path` lies inside a `Util/` directory (top-level
`OpenGALib/Util/` or per-layer `OpenGALib/<Layer>/Util/`). Checked by
segmenting on `/` so accidental substrings like `Utilities` would not match. -/
private def isUtilPath (path : String) : Bool :=
  (path.splitOn "/").contains "Util"

/-- Inner declaration kinds the linter deliberately skips —
typeclass instances co-locate with their type by Lean synthesis
requirement. -/
private def exemptKinds : List Name :=
  [``Lean.Parser.Command.instance]

/-- Detect a `private` modifier inside `declModifiers` at
`declaration[0]`. The `private` token, when present, lives somewhere
in the modifiers' subtree as an atom literal `"private"`. -/
private partial def hasPrivateModifier (stx : Syntax) : Bool :=
  if stx.isAtom && stx.getAtomVal == "private" then true
  else stx.getArgs.any hasPrivateModifier

@[inherit_doc linter.openGA.anchorPurity]
def anchorPurityLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.openGA.anchorPurity (← getLinterOptions) do return
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  if exemptKinds.contains stx[1].getKind then return
  if hasPrivateModifier stx[0] then return
  if isUtilPath (← getFileName) then return
  let docStx := stx[0][0][0]
  if docStx.isMissing then return
  let docString ← try getDocStringText ⟨docStx⟩ catch _ => return
  if let some bad := startsWithForbidden docString then
    Linter.logLint linter.openGA.anchorPurity docStx
      m!"`{bad}` declaration in an anchor file — move it to the layer's \
         `Util/` sub-module, or re-tag as `**Math.**` if it actually \
         describes a textbook concept."

initialize addLinter anchorPurityLinter

end OpenGALib.Linter.AnchorPurity
