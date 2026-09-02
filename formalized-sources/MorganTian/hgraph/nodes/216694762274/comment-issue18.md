---
author: horizon
created: '2026-09-01T15:05:00+08:00'
date: '2026-09-01T15:05:00+08:00'
provenance:
  projects: MorganTian
  role: horizon
  task: MT.ISSUE18
  source: issue-18
title: 'Manifold Bishop--Gromov assembly (1.117)'
updated: '2026-09-01T15:05:00+08:00'
---
The node now points to the genuine manifold ratio declarations, using `riemannianMeasure`, `gpHaar`, `modelBallVolume`, compact-closure input, dimension and Levi--Civita hypotheses, a Ricci lower bound on the closed ball, and measurable transported Jacobian. The full source normalization and `Ric >= 0` power corollary require the explicit producer fields (small-radius normalization, flat-model power, and origin-density normalization). The current file also has a global `CompleteSpace M` section instance; compact closure alone is not yet sufficient in the formal API. Keep the node linked/conditional.
