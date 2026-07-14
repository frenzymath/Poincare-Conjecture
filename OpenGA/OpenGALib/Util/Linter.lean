import OpenGALib.Util.Linter.AnchorPurity
import OpenGALib.Util.Linter.MathTag
import OpenGALib.Util.Linter.Naming

/-!
# OpenGALib fitness-function linter set

Aggregates the three OpenGALib Lean-native linters and registers them
as a single linter set `linter.openGA`. Use

```
set_option linter.openGA false
```

at the top of a file to silence all three OpenGALib linters at once
(e.g. for temporary experimentation); individual linters can also be
toggled in isolation via their own options
(`linter.openGA.mathTag`, `linter.openGA.anchorPurity`,
`linter.openGA.naming`).

See CLAUDE.md "Fitness functions" for the full design and the per-
linter docstrings for the rule each one enforces.
-/

/-- The OpenGALib fitness-function linter set, bundling `mathTag`,
`anchorPurity`, and `naming`. -/
register_linter_set linter.openGA :=
  linter.openGA.mathTag
  linter.openGA.anchorPurity
  linter.openGA.naming
