# Human review import history

Imported from `frenzymath/Poincare-Conjecture` GitHub issues into hgraph
attachments (`nodes/<id>/review-*.md` and `comment-*.md`).

Each attachment records at least: `author` (GitHub login), `role:
human-reviewer`, `date`, `scope`, `mark`, and the stable blueprint `label` and/or
`blueprint_number` when available. Maths/Lean verdicts are present on reviews.
`source` is an **optional** single issue/PR URL (omitted for offline reviews).

## Coverage

| Issue | Author | Project | What was imported |
| --- | --- | --- | --- |
| [#5](https://github.com/frenzymath/Poincare-Conjecture/issues/5) | JxChen24 | DoCarmo | Problem reviews on all cited blueprint labels (Hopf–Rinow review I) |
| [#6](https://github.com/frenzymath/Poincare-Conjecture/issues/6) | JxChen24 | DoCarmo | Problem reviews on all cited blueprint labels (Hopf–Rinow review II) |
| [#7](https://github.com/frenzymath/Poincare-Conjecture/issues/7) | wanxuy4-lab | DoCarmo | Partial reviews: Ch.1–2 `\leanok` scope mismatches (table) |
| [#9](https://github.com/frenzymath/Poincare-Conjecture/issues/9) | Ezreal88 | DoCarmo | Per-node M/L marks for Ch3 §3 issues |
| [#10](https://github.com/frenzymath/Poincare-Conjecture/issues/10) | diudiu1728 | DoCarmo | Satisfactory M/L on `IsGeodesicallyComplete` chain (labels + Lean decls) |
| [#11](https://github.com/frenzymath/Poincare-Conjecture/issues/11) | JxChen24 | DoCarmo | Problem/partial reviews on CDV↔Levi-Civita cited labels |
| [#16](https://github.com/frenzymath/Poincare-Conjecture/issues/16) | Lightmarey | MorganTian | Explicit findings only (1.115, 1.117, 1.96, 1.101, 1.97, 1.71, 1.76, 1.20) |
| [#18](https://github.com/frenzymath/Poincare-Conjecture/issues/18) | wanxuy4-lab | MorganTian | Full node-by-node table (✓/△/✗/—) for sections 1.3, 1.4, 1.6 |

## Intentionally not imported as statement reviews

| Item | Why |
| --- | --- |
| #2, #3, #4 | Milestone trackers only — no per-node verdicts |
| #12 | Code-quality / mathlib style for Exponential modules, not statement correspondence |
| PRs #13–15, #17 | Fix landings; do **not** auto-mark satisfactory. Re-review after fix if needed |
| CI PR #1, sync PR #8 | Infrastructure, not human math/Lean statement review |

## Convention

- **satisfactory** (`maths`+`lean` good): skip re-review unless content changes
- **partial** / **problem**: findings to address; not a green mark
- **unformalized** (`comment`): no Lean yet at review time
- Agents must not use `role: human-reviewer`
- Multiple reviews on one node accumulate (history); latest human mark is current intent

The importer preserves the overall table mark. Its two verdict fields are a
statement-correspondence convention (`✓` = good/good, `△` = good/bad, `✗` =
bad/bad), not an automated proof or mathematical correctness claim.

## Regenerating

```bash
# Issue 18-style tables:
gh issue view 18 --json number,title,author,createdAt,body > /tmp/issue.json
python3 scripts/import-hgraph-human-reviews.py \
  --issue-json /tmp/issue.json \
  --hgraph formalized-sources/MorganTian/hgraph \
  --number-map path/to/number-map.json

# If no checked-in number map is available, run `hgraph sync` first and use the
# conservative title/order fallback. Ambiguous rows fail instead of guessing.
python3 scripts/import-hgraph-human-reviews.py \
  --issue-json /tmp/issue.json \
  --hgraph formalized-sources/MorganTian/hgraph \
  --labels-from-hgraph

# Full history re-import is done from the corpus under /tmp/pc_review_corpus
# (see commit message / OpenGA scripts). Re-imports are idempotent by
# author+role+source plus the node's label or blueprint number; distinct issue
# sources on the same node remain separate history entries.
```

Reviews attached to generated Lean declarations are retained in hgraph and are
available through `hgraph get`/the JSON API. The current blueprint website only
renders attachments on `generated: blueprint` nodes; this is a limitation of
the pinned hgraph frontend, not a reason to move a Lean review onto a different
mathematical statement.
