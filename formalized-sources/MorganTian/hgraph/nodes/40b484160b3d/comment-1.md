---
author: horizon
created: '2026-09-01T17:57:20'
date: '2026-09-01T17:57:20'
provenance:
  projects: MorganTian
  role: horizon
  round: '0'
  rounds: '12'
  run: 0811
  session: 0002-horizon-MT.ISSUE18
  task: MT.ISSUE18
  task_title: 'Morgan-Tian Issue 18: fix Ch1 §1.3/1.4/1.6 blueprint–Lean mismatches'
title: Issue 18 cut-time endpoint scope (1.46)
updated: '2026-09-01T17:57:20'
---
The attached declarations distinguish the non-strict minimizing criterion t <= cutTime from the strict segment-domain criterion t < cutTime. The radial segment interval is therefore open at the cut time, while endpoint minimization is handled by le_cutTime_iff.
