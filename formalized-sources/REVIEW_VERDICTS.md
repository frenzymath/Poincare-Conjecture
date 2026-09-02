# Explicit review verdicts

This repository keeps a minimal verdict layer on top of hgraph. Hgraph supplies
stable blueprint-node and Lean-declaration identity plus attachment storage; its
default `maths`/`lean` review vocabulary does not constrain this layer.

The layer records only a reviewer's current verdict on a target. It is not an
issue importer, a review transcript, or a per-node change history.

## Issuing a verdict

A verdict is created only by a reviewer writing a complete instruction line in
a GitHub issue body or comment:

```text
/add-mark satisfactory label:thm:example
/add-mark unsatisfactory decl:Project.example
```

`label:` selects a blueprint (`type: tex`) node. `decl:` selects a Lean
declaration (`type: lean`) node. The selector must resolve uniquely in the
project's generated `hgraph/nodes/*.md` files.

Ordinary issue prose, issue tables, comments without this instruction, merged
pull requests, and CI results never create verdicts. In particular, the
reviews previously discussed in issues #5--#18 are not seeded as verdicts:
they contain findings and table marks, not explicit `/add-mark` instructions.

## Semantics

- A target may have marks from any number of reviewers.
- Each reviewer has one current verdict per target, stored in
  `nodes/<node-id>/verdict-<github-login>.md`.
- A later explicit instruction from the same reviewer replaces that reviewer's
  current verdict. Other reviewers' verdicts are unaffected.
- Absence of a mark means no verdict from that reviewer.
- `unsatisfactory` exposes a target that still needs attention. It remains
  unsatisfactory until that reviewer explicitly marks the target satisfactory.
- `satisfactory` records positive review evidence; it is not a rule to skip
  re-review. Each future reviewer decides how much existing evidence is enough.

Verdict files contain only structured metadata: reviewer, verdict, target,
node id, review date, semantic digest, and the issue or comment URL. They never
copy issue text or review notes.

## Revisions and outdated marks

At marking time, the script records a SHA-256 digest of the target's semantic
content. The digest covers the statement/declaration body and stable fields
such as its label or declaration name, title, content type, and docstring. It
deliberately excludes sync metadata such as `created`, `updated`, `file`,
`order`, and `lean_status`.

After a direct semantic revision:

- a previous satisfactory mark displays as `satisfactory (outdated)`;
- an unsatisfactory mark remains `unsatisfactory`, with `target_changed: true`
  in status output, until that reviewer explicitly issues a satisfactory mark;
- the mark is retained rather than deleted, so its provenance remains visible.

## Commands

Run `hgraph sync` for the project before importing or checking marks. Fetch an
issue together with its comments, then apply only its explicit instructions:

```bash
gh issue view 20 --repo frenzymath/Poincare-Conjecture \
  --json number,url,author,createdAt,body,comments > /tmp/issue-20.json

python scripts/hgraph-verdicts.py import-issue \
  --issue-json /tmp/issue-20.json \
  --hgraph formalized-sources/MorganTian/hgraph \
  --repo frenzymath/Poincare-Conjecture
```

All instructions and target selectors are validated before any file is
written. Use `--dry-run` to inspect planned paths or `--source` to override the
recorded issue/comment URL.

Show every mark and its revision state:

```bash
python scripts/hgraph-verdicts.py status \
  --hgraph formalized-sources/MorganTian/hgraph

python scripts/hgraph-verdicts.py status \
  --hgraph formalized-sources/MorganTian/hgraph \
  --target decl:Project.example \
  --json
```

The custom command is necessary because the pinned hgraph dashboard does not
yet interpret `verdict-*.md`. The verdict files nonetheless remain attached to
the same hgraph nodes and can be consumed by later dashboard integration.
