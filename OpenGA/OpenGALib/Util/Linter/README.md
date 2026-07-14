# `OpenGALib/Util/Linter/` — fitness-function linters

Lean-native linters that enforce OpenGALib's architectural rules at
elaboration time. Each linter:

- runs on every `lake build` and shows inline in the editor via LSP;
- gates every push / PR in `.github/workflows/ci.yml` via baseline grep;
- has a unit test under `OpenGALib/Tests/Linter/` driven by `#guard_msgs`.

Background: Neal Ford et al., *Building Evolutionary Architectures*
(2017) — "fitness functions" name for executable architectural tests.
Mathlib's `Mathlib/Tactic/Linter/` is the reference Lean-side
implementation we follow.

## Linters

| File | Option | Rule |
|---|---|---|
| `MathTag.lean`      | `linter.openGA.mathTag`      | every doc must begin with `**Math.**`, `**Eng.**`, or `**Mixed.**` |
| `AnchorPurity.lean` | `linter.openGA.anchorPurity` | `**Eng.**` / `**Mixed.**` forbidden outside `Util/` (instance + private exempt) |
| `Naming.lean`       | `linter.openGA.naming`       | bare initialisms `CLM`, `NACG`, `IPS` forbidden in declaration names |

All three are bundled in the linter set `linter.openGA` defined in
`OpenGALib/Util/Linter.lean`. To silence the entire set for one file:

```lean
set_option linter.openGA false
```

To silence a single linter for one declaration:

```lean
set_option linter.openGA.mathTag false in
/-- intentionally untagged -/
def example_ : Nat := 0
```

## Adding a new linter

1. Drop `OpenGALib/Util/Linter/<Name>.lean` following the
   `MathTag.lean` template:
   - `register_option linter.openGA.<name>` with documenting `descr`
   - `@[inherit_doc linter.openGA.<name>]` on the linter function
   - `Linter where run := withSetOptionIn fun stx ↦ do`
   - body uses `getLinterValue ... (← getLinterOptions)` and
     `Linter.logLint` for warnings
   - `initialize addLinter ...`
2. Add the option to `OpenGALib/Util/Linter.lean`'s `register_linter_set`.
3. Add `OpenGALib/Tests/Linter/<Name>.lean` with `#guard_msgs (warning) in`
   blocks for each trigger pattern.
4. Add a baseline check to `.github/workflows/ci.yml` (`Enforce linter
   baselines` step) — grep for the linter's distinct warning prefix,
   assert count ≤ baseline.

CLAUDE.md "Fitness functions" tracks the public-facing summary.
