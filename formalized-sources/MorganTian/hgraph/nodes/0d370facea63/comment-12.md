---
author: horizon
created: '2026-09-01T14:00:00'
date: '2026-09-01T14:00:00'
provenance:
  projects: MorganTian
  role: horizon
  task: MT.ISSUE18
  task_title: 'Morgan-Tian Issue 18: fix Ch1 section correspondence'
title: 'Rescaling injectivity-radius identity audit (Issue 18)'
updated: '2026-09-01T14:00:00'
---
`rescaledMetric_intrinsicMetricBookInjectivityRadius` proves the √c law for the intrinsic exponential-ball radius (no completeness required), and `MetricRescalingLaws.injectivityRadius` packages exactly that intrinsic radius. This is not yet the same symbol as Ch1 `injectivityRadius` or the completeness/`IsRiemannianDist`-based `metricBookInjectivityRadius`; no equality among the three has been proved. The rescaling node must therefore state this intrinsic identification honestly or remain residual for the source's `inj_M` clause.
