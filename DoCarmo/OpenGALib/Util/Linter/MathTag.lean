import Lean

/-!
# `Math/Eng/Mixed` docstring-tag linter

Enforces the OpenGALib documentation convention: any declaration
whose docstring is present must begin with one of the tags
`**Math.**`, `**Eng.**`, or `**Mixed.**`.

Declarations without docstrings are silently skipped — the linter
mandates a tag *if* a docstring exists, not the docstring itself.

Activated by default. Silence locally with
`set_option linter.openGA.mathTag false in <decl>`, or fix the tag.

See CLAUDE.md "Code quality / Math-Eng-Mixed tagging".
-/

open Lean Elab Linter

namespace OpenGALib.Linter.MathTag

/--
The OpenGALib Math/Eng/Mixed docstring-tag linter.

Every declaration with a docstring must begin its docstring with one of
`**Math.**`, `**Eng.**`, or `**Mixed.**`. The tag is the primary signal
when reading a file — Math reads as the textbook content, Eng is
engineering scaffolding, Mixed is a Math signature with engineering
proof body.
-/
register_option linter.openGA.mathTag : Bool := {
  defValue := true
  descr := "Enforce **Math.**/**Eng.**/**Mixed.** docstring tag on declarations."
}

private def acceptedTags : List String := ["**Math.**", "**Eng.**", "**Mixed.**"]

private def hasAcceptedTag (s : String) : Bool :=
  let t := s.trimAsciiStart.toString
  acceptedTags.any fun tag => t.startsWith tag

@[inherit_doc linter.openGA.mathTag]
def mathTagLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.openGA.mathTag (← getLinterOptions) do return
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  let docStx := stx[0][0][0]
  if docStx.isMissing then return
  let docString ← try getDocStringText ⟨docStx⟩ catch _ => return
  unless hasAcceptedTag docString do
    let preview := (docString.trimAscii.toString.take 40).replace "\n" " "
    Linter.logLint linter.openGA.mathTag docStx
      m!"docstring should start with **Math.**, **Eng.**, or **Mixed.** \
         (got: \"{preview}…\")"

initialize addLinter mathTagLinter

end OpenGALib.Linter.MathTag
