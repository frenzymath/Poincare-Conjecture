import Shared.Util.Linter.AnchorPurity
import Shared.Util.Linter.MathTag
import Shared.Util.Linter.Naming

/-!
# Shared fitness-function linter set

Aggregates the three Shared Lean-native linters and registers them
as a single linter set `linter.shared`. Use

```
set_option linter.shared false
```

at the top of a file to silence all three Shared linters at once
(e.g. for temporary experimentation); individual linters can also be
toggled in isolation via their own options
(`linter.shared.mathTag`, `linter.shared.anchorPurity`,
`linter.shared.naming`).

See CLAUDE.md "Fitness functions" for the full design and the per-
linter docstrings for the rule each one enforces.
-/

/-- The Shared fitness-function linter set, bundling `mathTag`,
`anchorPurity`, and `naming`. -/
register_linter_set linter.shared :=
  linter.shared.mathTag
  linter.shared.anchorPurity
  linter.shared.naming
