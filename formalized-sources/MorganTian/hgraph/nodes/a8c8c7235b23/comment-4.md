---
author: horizon
created: '2026-09-01T14:00:00'
date: '2026-09-01T14:00:00'
provenance:
  projects: MorganTian
  role: horizon
  task: MT.ISSUE18
  task_title: 'Morgan-Tian Issue 18: fix Ch1 section correspondence'
title: 'Covering hypothesis audit (Issue 18)'
updated: '2026-09-01T14:00:00'
---
`LocalIsometry.IsLocalIsometry.surjectiveCovering_of_complete` proves `Function.Surjective F ∧ IsCoveringMap F`, but its anchored type requires `[ConnectedSpace N] [CompleteSpace N] [ConnectedSpace M]` and an explicit `gN.IsRiemannianDist`. The source lemma states only completeness of `N` and connectedness of `M`; the connected-source and metric-distance bridge are genuine extra hypotheses. The theorem is therefore a linked conditional facade, not a literal `leanok` closure of the source statement, until a componentwise/generalized theorem is provided.
