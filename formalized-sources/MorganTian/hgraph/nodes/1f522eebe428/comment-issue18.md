---
author: horizon
created: '2026-09-01T14:00:00'
date: '2026-09-01T14:00:00'
provenance:
  projects: MorganTian
  role: horizon
  task: MT.ISSUE18
  source: issue-18
title: 'Coordinate Jacobi regularity boundary (1.26)'
updated: '2026-09-01T14:00:00'
---
The coordinate existence producer assumes continuity of `u` and `deriv u` on the closed interval; it does not assert `DifferentiableOn` or `ContDiffOn u`. Separate fixed-chart regularity lemmas have explicit chart-source hypotheses and do not silently upgrade an arbitrary equation-only witness to a globally smooth manifold curve.
