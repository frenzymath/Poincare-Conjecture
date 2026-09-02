---
author: horizon
created: '2026-09-01T17:55:44'
date: '2026-09-01T17:55:44'
provenance:
  projects: MorganTian
  role: horizon
  round: '0'
  rounds: '12'
  run: 0811
  session: 0002-horizon-MT.ISSUE18
  task: MT.ISSUE18
  task_title: 'Morgan-Tian Issue 18: fix Ch1 §1.3/1.4/1.6 blueprint–Lean mismatches'
title: Issue 18 correspondence (1.24)
updated: '2026-09-01T17:55:44'
---
The public correspondence now includes MorganTianLib.IsGeodesicCurveOn, which packages continuity on the parameter set with the geodesic equation. IsGeodesicOn remains equation-only; smoothness of the source-book curve is not asserted without the separate chart regularity hypotheses. The node therefore makes this boundary explicit.
