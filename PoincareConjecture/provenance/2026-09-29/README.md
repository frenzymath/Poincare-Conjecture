# External source similarity audit

Target: `c99c35c5d3a5a67d4c647fa9cd20f83abfcee74d`, before these notice edits.
All 23,564 tracked active Lean files were scanned, including files without source
citations. Archived evidence under `PoincareConjecture/references` and frozen
`PoincareConjecture/contracts` were excluded. Dependency checkouts are compared
as upstream sources, not counted as local project code.

| Source | Lean files | Comparison revision |
| --- | ---: | --- |
| TauCeti | 5,329 | `d7ac608e0c97f71e9e0dc210d26a470d974368d7` |
| DifferentialGeometry | 3,932 | `1b535dd102b94cc42b107cca27059687888f08b3` (v0.1.2) |
| ClassificationOfSurfaces | 681 | `e3c7230fe78d7b056a415d9ecae6f77887046b32` |
| DeGiorgi | 94 | `4c1b3077d3782b24065184df4ba59501b2e56fc7` |
| Mathlib | 8,852 | `0df444a360eaa60ab8c11dca51a86af692955474` |

Repositories were identified from Horizon's local consulted-library catalog and
the retained [donor review](../../references/ricci-flow/mapher/complete-import/source-notices/references/2026-09-20-horizon-reuse-verification.md).
DeGiorgi was added to trace material vendored by DifferentialGeometry. Own and
colleague sources (AxelWorkspace, Mapher/Leheng, EarlierAlgebraicGeometry and the
Poincare blueprint) were excluded from the external corpus. This is an audit
against the identified corpus, not a claim that every historical consultation
was recoverable or that absence of a match proves original authorship.

## Results and review

The scanner compared 595 candidate pairs after indexing and reported 455 pairs
across 109 local files. These include repeated helpers and duplicate source trees.
All reported pairs have a disposition in [reviewed-files.json](reviewed-files.json).
The ledger also includes one explicitly acknowledged adaptation below the scan
threshold, giving 110 reviewed files. Missing notices were added to 36 files.

Source headers, root notices and licenses were inspected to determine attribution.
For example, the original DeGiorgi LICENSE and the vendored copy both name Scott
Armstrong and Julia Kempe. DifferentialGeometry's root NOTICE names its
contributors collectively. Individual TauCeti headers distinguish Lean FRO, LLC
and Tau Ceti contributors; a repository owner name was not substituted for them.
Partial Mathlib adaptations preserve the notices of Yizheng Zhu and Sebastien
Gouezel. Existing individual headers retain the exact spelling of their names.

Nine files contain substantial DeGiorgi material. A tenth candidate,
`Sobolev/Iterated/Basic.lean`, contains only scattered common proof idioms and was
not assigned additional DeGiorgi authorship. The partial adaptations in curve
traces, volume normalization, tangent-section negation, heat-kernel moments, and
spectral summability have scoped modification descriptions in the ledger and
local headers. Notice changes do not claim upstream authorship of entire files
when only a fragment is adapted.

- [summary.json](summary.json): counts, parameters, and exclusions.
- [candidates.jsonl.gz](candidates.jsonl.gz): full evidence, with original line
  ranges, coverage scores, source hashes, and stable candidate IDs.
- [reviewed-files.json](reviewed-files.json): source and modification decisions.
- [licenses.json](licenses.json): source hashes and paths of verbatim license copies.
- [licenses/](licenses/): upstream licenses and DifferentialGeometry NOTICE.

Line numbers in candidate evidence refer to the scanned commit, before notices
were prepended. The ledger's target hashes likewise identify the pre-edit files.

## Validation

All 27 Python tooling tests pass, including uncited-copy detection, fragment
matching, pinned Git reads, nested comments and literals, complete candidate
dispositions, and license checksums. Every reviewed target and source hash was
checked against the pinned Git blobs; all retained licenses match their source
bytes. Comparing comment-stripped token streams (without removing imports or
namespace commands) confirms that all 110 edited Lean files preserve their code.
No Lean build or comparator was rerun for these comment-only edits. Earlier
verification remains evidence for the exact commits named in its report.

## Method and limits

The scanner tokenizes Lean with hgraph's nested-comment-aware lexer. It removes
comments, whitespace, imports and namespace boundary commands for matching,
while retaining identifiers and literals. A sampled index of 12-token shingles
generates candidates; every reported overlap is checked against actual tokens.
Candidates require at least 80 covered tokens on both sides and either 80%
whole-file coverage or 80% coverage in a 200-token window on either side.
The sampled prefilter is documented in `summary.json`.

Coverage measures tokens participating in exact shared shingles, not edit-distance
similarity. Windows may combine separate matches; review must distinguish common
idioms from substantive reused proofs. Sampling and minimum lengths can miss
short, renamed, reorganized or heavily rewritten adaptations. This does not
establish semantic equivalence or determine copyrightability automatically.

## Reproduce

Install the pinned Python dependency from the repository root:

```sh
python3 -m venv .venv-provenance
.venv-provenance/bin/pip install -r requirements-site.txt
```

Prepare Git checkouts or bare repositories containing the five pinned commits.
Copy `manifest.example.json` to a local manifest and replace each source `path`
with its checkout path. The target path is the repository root; its pinned
revision must exist locally. The scanner reads Git blobs, ignoring dirty files.

Use disk-backed scratch with sufficient space, then run from the repository root:

```sh
mkdir -p "$HOME/.horizon/development-tmp/provenance-audit"
export TMPDIR="$HOME/.horizon/development-tmp/provenance-audit"
.venv-provenance/bin/python scripts/scan_external_reuse.py \
  --manifest /path/to/local-manifest.json \
  --output "$TMPDIR/report" --threshold 0.8
.venv-provenance/bin/python -m unittest discover -s scripts/tests
```

The output SQLite database is disposable indexing scratch. Keep the JSON evidence
and review decisions; no automatic notice writer is part of the detector.
