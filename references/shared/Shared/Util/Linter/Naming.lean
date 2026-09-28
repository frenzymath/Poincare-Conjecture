import Lean

/-!
# Naming-convention linter — forbidden initialisms

Forbids bare initialisms in declaration names. Specifically rejects the
substrings `CLM`, `NACG`, and `IPS` — they lose semantics and may collide
with unrelated names. Full Mathlib-style names are mandatory:

* `CLM`  → `ContinuousLinearMap`
* `NACG` → `NormedAddCommGroup`
* `IPS`  → `InnerProductSpace`

See CLAUDE.md "Code quality / Natural-language reading test".
-/

open Lean Elab Linter

namespace Shared.Linter.Naming

/--
The Shared naming-convention linter.

Top-level declaration identifiers may not contain `CLM`, `NACG`, or
`IPS` — initialisms hide semantics and risk collision. Use the full
Mathlib-style names (`ContinuousLinearMap`, `NormedAddCommGroup`,
`InnerProductSpace`).
-/
register_option linter.shared.naming : Bool := {
  defValue := true
  descr := "Forbid bare initialisms (CLM, NACG, IPS) in declaration names."
}

private def forbiddenInitialisms : List String := ["CLM", "NACG", "IPS"]

private def expandSuggestion : String → String
  | "CLM"  => "ContinuousLinearMap"
  | "NACG" => "NormedAddCommGroup"
  | "IPS"  => "InnerProductSpace"
  | _      => "(no suggestion)"

private def stringContains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def findBadInitialism (name : String) : Option String :=
  forbiddenInitialisms.find? (stringContains name ·)

/-- Locate the first `Lean.Parser.Command.declId` node inside `stx`
(depth-first). Returns `none` if the declaration is anonymous
(e.g., `instance : Foo` without a name). -/
private partial def findDeclId? (stx : Syntax) : Option Syntax :=
  if stx.isOfKind ``Lean.Parser.Command.declId then some stx
  else stx.getArgs.findSome? findDeclId?

@[inherit_doc linter.shared.naming]
def namingLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.shared.naming (← getLinterOptions) do return
  unless stx.isOfKind ``Lean.Parser.Command.declaration do return
  let some declId := findDeclId? stx[1] | return
  let nameStx := declId[0]
  unless nameStx.isIdent do return
  let name := nameStx.getId.toString
  if let some bad := findBadInitialism name then
    Linter.logLint linter.shared.naming nameStx
      m!"declaration name `{name}` contains the forbidden initialism `{bad}` — \
         expand to `{expandSuggestion bad}` (initialisms drop semantics and \
         risk colliding with unrelated names; see CLAUDE.md naming test)."

initialize addLinter namingLinter

end Shared.Linter.Naming
