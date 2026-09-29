# Source modifications and attribution

This file records source-level reuse where a Lean file is adapted from an
external development. It complements each file's local notice. A source
reference is evidence for review, not an automatic copyright decision: before
adding an attribution, verify the cited revision, license, authorship, and the
substantive changes.

## DeGiorgi Sobolev approximation

- **Local file:** `PoincareLib/Analysis/Elliptic/Regularity/Sobolev/Weak/Approximation.lean`
- **Source:** `DifferentialGeometry/External/DeGiorgi/SobolevSpace/Approximation.lean`
- **Repository/revision:** `qinz1yang/differential-geometry`, v0.1.2,
  commit `1b535dd102b94cc42b107cca27059687888f08b3`
- **Upstream provenance:** the file derives from Julia Kempe and Scott
  Armstrong's DeGiorgi project. Preserve the upstream notice:
  `Copyright 2026 Scott Armstrong and Julia Kempe`.
- **Changes here:** import paths were moved into `PoincareLib`, the namespace
  was moved from `DeGiorgi` to `Poincare.Analysis.Sobolev.Weak`, and the local
  style-warning cleanup was retained. The theorem bodies otherwise match the
  cited source at the token level.
- **License:** Apache-2.0, subject to the source project's license and notice.

## Detection workflow

Run the detector against a checkout of the source repository. It follows
`DifferentialGeometry/.../*.lean` references in local comments, reads the
requested Git revision when a source file is not checked out, strips Lean
comments and whitespace, and reports token-stream similarity. The output is a
review queue. It does not add copyright notices or assert that similar code is
copyrightable.

```sh
python3 scripts/detect_provenance.py \
  PoincareConjecture/PoincareLib \
  /path/to/differential-geometry \
  --source-revision 1b535dd102b94cc42b107cca27059687888f08b3 \
  --threshold 0.98 \
  --json /tmp/poincare-provenance-candidates.json
```

For each `needs-review` result, compare the source and local file, inspect the
license and notices, and then add a concise local header plus an entry here.
Do not infer authorship from token similarity alone; mathematical statements,
common Mathlib idioms, and generated or mechanically renamed code need separate
review.
