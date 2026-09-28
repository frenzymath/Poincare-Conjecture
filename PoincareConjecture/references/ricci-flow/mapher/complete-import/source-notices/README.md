---
document_status: ACTIVE
updated: 2026-09-20
---

# Morgan-Tian Poincare Formalization

An independent Lean 4 formalization project for the Poincare theorem,
following Morgan and Tian's *Ricci Flow and the Poincare Conjecture* with
applicable corrections.

**All 84 active skeleton contract gates are published: M01-M83 and M90.**
The 90-row register explicitly retires M84-M89. The original 40-node baseline
and subsequent corrections remain in the review history. The current
[goal](GOAL-90-MILESTONE-REDESIGN.md) requires both independent review rounds,
source/errata alignment, numbered ownership, commit/push and cumulative reports.

Both endpoint theorems have the original Mathlib-only propositions with no
service argument. They remain proofs relative to admitted milestones: the
current inventory has 40 direct admissions and the smooth/topological endpoints
reach 38/39 of them. The repaired Horizon proofs for M06, M16-M21 and M24
are merged with foundation-only closures after a successful 15,697-job
aggregate build. The [post-merge audit](docs/progress/2026-09-20-horizon-reland-reconciliation.md)
records the current compiled inventory and preserved helper-review holds.
The earlier independent 11,975-job skeleton reproduction remains in the
[completion receipt](docs/progress/2026-09-20-skeleton-completion.md).
The skeleton task is complete; further work is owner-proof maintenance.
Among the 84 active milestones, 43 proofs are closed, M90 is relative,
and 40 remain admitted. Current owner assignments are in [milestones.md](milestones.md).
This is not a completed mathematical proof of either Poincare proposition.

This is one project. Start with the short [handoff guide](docs/skeleton-handoff.md)
and [ordered milestone/file index](blueprint/generated/work-items.md).
Every active milestone has a numbered proof entry, with its definitions and
statements in the ordinary `PoincareMT` directories. Later proof owners may use
earlier skeleton files but must not modify them. Existing helper semantic-review
holds remain explicit proof-maintenance work.

## Reviewer entry points

| File | Purpose |
| --- | --- |
| [GOAL.md](GOAL.md) | Complete, maintained instruction for the active goal |
| [AGENTS.md](AGENTS.md) | Operational rules and current phase boundary |
| [MEMORY.md](MEMORY.md) | Latest handoff and next actions |
| [project.json](project.json) | Recorded project phase, pins, and build scope |
| [Architecture](docs/architecture.md) | Existing and planned files, ownership, import direction |
| [Statuses](docs/status.md) | Document, review, build, and proof status meanings |
| [GitHub setup](docs/github-setup.md) | Step-by-step private repository login and creation |
| [Tooling](docs/tooling.md) | Pinned Lean environment and verified LSP/LeanSearch workflows |
| [Blueprint](blueprint/README.md) | Active 90-node register, source reconciliation, and review gate |
| [References](references/README.md) | Source hierarchy, archival status, and provenance |
| [Preparation report](docs/progress/2026-09-10-preparation.md) | Initial preparation, checks, and independent agent review |
| [GitHub report](docs/progress/2026-09-10-private-github.md) | Completed private repository creation and baseline synchronization |
| [Startup report](docs/progress/2026-09-10-startup.md) | Source archive, tool checks, and reviewed endpoint definitions |
| [Metric checkpoint](docs/progress/2026-09-10-metric-interface.md) | Explicit metric data, generated interfaces, and strengthened audit |
| [Dependency checkpoint](docs/progress/2026-09-10-dependency-outline.md) | Provisional DAG, source findings, and supporting obligations |
| [Curvature checkpoint](docs/progress/2026-09-10-curvature-interface.md) | Explicit curvature evaluations, contractions, and first-slot antisymmetry proofs |
| [Koszul checkpoint](docs/progress/2026-09-10-koszul.md) | Local Koszul identity and pointwise connection uniqueness proofs |
| [Regularity checkpoint](docs/progress/2026-09-10-connection-regularity.md) | Reviewed local regularity obligation, relative application proof, and compiled admission audit |
| [Ricci-flow checkpoint](docs/progress/2026-09-10-ricci-flow-interface.md) | Curvature connection independence and the ordinary Ricci-flow definition |
| [Local-flow checkpoint](docs/progress/2026-09-10-local-flow-milestone.md) | Accepted M03 statements, explicit proof obligations, and typed component assembly |
| [Declaration reviews](reviews/declarations.json) | Actual declaration identities, content hashes, and status axes |

The package pins Lean **4.33.1** and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. See the
[pin decision](docs/decisions/0003-toolchain-and-local-state.md) and
[tooling instructions](docs/tooling.md). With the pinned toolchain and dependency
cache available, run `tools/lean-env.sh lake --no-cache build` through the shared
resource lease when working on the collaboration server. The wrapper defaults
to one Lean worker. Archived sources and rights are tracked in the reference
manifest; the published archive check verifies 149 payloads. Hosted Actions
at the restoration checkpoint could not start because of an account billing
or spending-limit restriction; local validation is recorded separately.

The private remote is
[Mapher06/Poincare-MorganTian](https://github.com/Mapher06/Poincare-MorganTian).
Its ownership, private visibility, and initial push have been verified. See
`MEMORY.md` and `project.json` for the recorded checkpoint.

Existing neighboring projects are read-only research inputs, not dependencies.
All project-authored material is in English. No license for original project
material has yet been selected; see [licensing](docs/licensing.md).
