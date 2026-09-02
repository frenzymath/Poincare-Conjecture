# Review verdicts

Review verdicts are small YAML attachments kept with the hgraph node they
describe. Hgraph supplies the node identity and attachment location; this
layer records only the current human review marks.

There is no importer, issue-history database, or verdict-specific CI job. Issue
prose, issue tables, merged pull requests, and CI results do not create marks.
Only a reviewer's clear, direct add-mark instruction creates a new satisfactory
mark. The examples below are manual transcriptions of existing hgraph review
records, with their GitHub logins, timestamps, and source issues preserved.

## Record format

An attachment contains one current entry per reviewer:

```yaml
verdicts:
  - reviewer: diudiu1728
    verdict: satisfactory
    date: '2026-07-31T12:01:13Z'
    source: https://github.com/frenzymath/Poincare-Conjecture/issues/10
```

The allowed values are `satisfactory`, `unsatisfactory`, and
`satisfactory (outdated)`. `unsatisfactory` is optional guidance that tells
other reviewers that a node needs attention; it never prevents another review.
The `date` is the UTC time of the recorded review instruction or report, and
`source` points to the issue or comment that explains the mark. Keeping both
makes it clear which entry a later mark should replace.

Multiple reviewers are represented by multiple list items. A later mark from
the same reviewer replaces that reviewer's item rather than creating a review
history. Several different reviewers may therefore have `satisfactory` items
for the same node. A mark from another reviewer is left untouched.

## Issuing and replacing a mark

A reviewer makes the action explicit in an issue body or comment, for example:

```text
/add-mark satisfactory decl:Riemannian.Geodesic.HasGeodesicEquationAt
/add-mark unsatisfactory label:thm:bishop-gromov
```

The YAML is then edited by hand with the reviewer's GitHub login, the UTC date,
and the source URL. There is no process that infers a satisfactory mark from a
sentence such as "verified" or from an accepted PR.

When the blueprint statement or Lean declaration is directly revised, append
` (outdated)` to each existing satisfactory value while retaining its date and
source:

```yaml
verdicts:
  - reviewer: diudiu1728
    verdict: satisfactory (outdated)
    date: '2026-07-31T12:01:13Z'
    source: https://github.com/frenzymath/Poincare-Conjecture/issues/10
```

After re-review, that same reviewer replaces the item with a fresh
`satisfactory` value and a new date/source. An unsatisfactory item is not
automatically cleared by a revision. Whether any existing satisfactory mark is
enough to reduce a new reviewer's work remains a per-case decision.

## Real records

These attachments correspond to current human review records already present in
the graph:

### Lean declaration

`formalized-sources/DoCarmo/hgraph/nodes/45d735d70a2e/verdicts.yaml` is attached
to `Riemannian.Geodesic.HasGeodesicEquationAt`. It records `diudiu1728`'s
satisfactory review from issue #10 on 2026-07-31.

### Blueprint node with multiple reviewers

`formalized-sources/DoCarmo/hgraph/nodes/72dfd827f733/verdicts.yaml` is attached
to blueprint node `thm:dc-ch7-2-8` (Hopf--Rinow). It records `diudiu1728`'s
satisfactory review from issue #10 on 2026-07-31 and the latest
`JxChen24` unsatisfactory review from issue #11 on 2026-08-09. JxChen24 also
reviewed this node in issues #5 and #6; those older entries are deliberately
collapsed to the one current mark for that reviewer.

`formalized-sources/MorganTian/hgraph/nodes/216694762274/verdicts.yaml` is
attached to blueprint node `thm:bishop-gromov` (node 1.117). It records the
unsatisfactory statement-correspondence findings from `Lightmarey` (issue #16,
2026-08-23) and `wanxuy4-lab` (issue #18, 2026-08-30). Both entries are kept
because they are different reviewers of the same node.

The merged repair PR #17 does not add a verdict by itself. If a reviewer wants
to certify the repaired node, they must issue a new direct satisfactory mark;
the old unsatisfactory guidance remains until that happens or a human removes
it.
