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

The reviewer may edit the YAML directly, or ask a maintainer or AI agent to do
it. The updater reads the explicit instruction, resolves the named hgraph node,
and edits that reviewer's current item with the GitHub login, UTC date, and
source URL. This is a small reviewed repository change, not an automated
importer. In particular, no process infers a satisfactory mark from a sentence
such as "verified" or from an accepted PR.

When the reviewed content of a blueprint statement or Lean declaration is
directly revised, append ` (outdated)` to each existing satisfactory value while
retaining its date and source:

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

## Renaming a node or Lean declaration

The verdict attachment belongs to the reviewed node, not permanently to its
opaque hgraph hash. Renaming a Lean declaration or blueprint label can create a
new node directory, so the attachment must be moved to the new directory. It
must not be left on the stale node or replaced with a fresh, empty file.

For a rename:

1. Record the old node path, perform the rename, update any blueprint
   `\lean{...}` attachment, and run hgraph sync.
2. Confirm that the old and new nodes are the same mathematical or Lean object,
   rather than a split, merge, or replacement with different content.
3. Move `verdicts.yaml` from the old hash directory to the new hash directory
   with `git mv`. Keep every reviewer, verdict, date, and source unchanged.
4. Check that the old directory no longer has a verdict attachment and the new
   node has exactly one. Record the old and new declaration names or labels in
   the commit message so `git log --follow` provides the rename history.

A name-only rename does not invalidate satisfactory marks because the reviewed
content did not change. If the statement, type, definition, or proof changes at
the same time, first move the attachment and then mark its satisfactory entries
`satisfactory (outdated)` under the direct-revision rule above. If the identity
is ambiguous, especially after a declaration is split or several declarations
are merged, do not copy satisfactory marks to the new nodes without a reviewer
or maintainer deciding where they belong.

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
