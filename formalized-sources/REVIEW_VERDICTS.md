# Review verdicts

Review verdicts are small YAML attachments kept with the hgraph node they
describe. Hgraph still supplies the node identity and attachment location, but
its default `maths`/`lean` review fields are not involved.

There is no importer, issue-history database, or CI job for verdicts. A verdict
is a reviewer's deliberate mark, recorded by editing the YAML attachment after
the reviewer has issued a clear add-mark instruction in an issue. Issue prose,
issue tables, merged pull requests, and CI results never create marks on their
own.

## Issuing a mark

A reviewer makes the action explicit in an issue body or comment, for example:

```text
/add-mark satisfactory label:lem:geodesic-no-trivial-embedded-loop
/add-mark unsatisfactory decl:MorganTianLib.fderiv_neg_fieldChartRep_gradientField_of_bochner
```

The reviewer then records the corresponding value in that node's
`verdicts.yaml`. This is a human instruction and a small convention, not an
automated importer.

## Minimal format

Each node has at most one `verdicts.yaml` attachment. The keys are reviewer
logins and the values are the reviewer's current state for that node:

```yaml
verdicts:
  alice: satisfactory
  bob: unsatisfactory
```

The only useful positive state is `satisfactory`. `unsatisfactory` is optional
guidance for other reviewers; it means that the node needs attention, but does
not prevent another reviewer from checking it. A reviewer can be absent from
the map, which means no verdict has been recorded for that reviewer.

Multiple reviewers are represented by multiple keys. There is only one current
value per reviewer; the YAML is not a history of that reviewer's past actions.
A later satisfactory mark replaces that reviewer's unsatisfactory value.

## Direct revisions

When the node's blueprint statement or Lean declaration is directly revised,
append ` (outdated)` to every existing satisfactory value:

```yaml
verdicts:
  alice: satisfactory (outdated)
  bob: unsatisfactory
  carol: satisfactory
```

The outdated sign is deliberately visible in the attachment. It does not erase
the reviewer name or the fact that the earlier version was marked satisfactory.
An unsatisfactory value is not automatically cleared by a revision, and a mark
from another reviewer does not clear it. Only that same reviewer can replace it
with a new satisfactory value after re-review.

Whether an existing satisfactory mark is enough to reduce a new reviewer's
work remains a per-case decision. No automatic re-review skipping rule is
encoded here.

## Blueprint example

For a blueprint node such as `label:lem:geodesic-no-trivial-embedded-loop`, the
attachment lives beside the generated node file:

```text
formalized-sources/MorganTian/hgraph/nodes/e87da812fc4a/verdicts.yaml
```

Its contents could be:

```yaml
verdicts:
  reviewer-a: satisfactory
  reviewer-b: satisfactory (outdated)
```

The node path supplies the target, so the YAML needs no repeated label, title,
issue text, source URL, date, or review explanation.

## Lean declaration example

The same format applies to a Lean node such as
`decl:MorganTianLib.fderiv_neg_fieldChartRep_gradientField_of_bochner`:

```text
formalized-sources/MorganTian/hgraph/nodes/9f680e664d06/verdicts.yaml
```

```yaml
verdicts:
  reviewer-a: satisfactory
  reviewer-c: unsatisfactory
```

These examples illustrate the attachment shape; they are not inferred from the
old issue reviews. Existing issue discussions remain discussion until a
reviewer explicitly adds a mark.
