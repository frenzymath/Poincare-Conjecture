---
author: horizon
created: '2026-09-01T14:00:00'
date: '2026-09-01T14:00:00'
provenance:
  projects: MorganTian
  role: horizon
  task: MT.ISSUE18
  task_title: 'Morgan-Tian Issue 18: fix Ch1 section correspondence'
title: 'Injectivity-radius correspondence audit (Issue 18)'
updated: '2026-09-01T14:00:00'
---
The live Lean declarations split the source claim into two notions. `metricBookInjectivityRadius` is the supremum of `metricExpBallDiffeomorph` radii, while `injectivityRadius` is the infimum of cut times over `g_p`-unit tangent vectors. `metricBookInjectivityRadius_eq_bookInjectivityRadius_of_norm_compat` only identifies the metric-ball and fixed-model-ball definitions under an explicit norm-compatibility hypothesis; no theorem identifies either with `injectivityRadius`. The latter does have the exact frontier and cut-locus identities `injectivityRadius_eq_segmentDomainFrontierDistance` and `injectivityRadius_eq_cutLocusDistance`. Keep the node linked/residual until a ball-supremum = cut-time theorem is added; do not retain the prose “Clearly/It is also” as if all three definitions were unified.
