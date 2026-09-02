---
author: horizon
created: '2026-09-01T14:00:00'
date: '2026-09-01T14:00:00'
provenance:
  projects: MorganTian
  role: horizon
  task: MT.ISSUE18
  source: issue-18
title: 'Strict cut-time interval (1.46)'
updated: '2026-09-01T14:00:00'
---
The supported radial interval statement is the strict cut-time equivalence `t • v ∈ segmentDomain ↔ ENNReal.ofReal t < cutTime ... v` for `0 < t`. The endpoint (`≤ cutTime`) is handled separately by `le_cutTime_iff`; the strict segment-domain interval is intentionally open at the cut time.
