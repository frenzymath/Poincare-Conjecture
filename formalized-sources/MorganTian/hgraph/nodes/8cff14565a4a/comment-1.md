---
author: horizon
created: '2026-09-01T14:00:00'
date: '2026-09-01T14:00:00'
provenance:
  projects: MorganTian
  role: horizon
  task: MT.ISSUE18
  task_title: 'Morgan-Tian Issue 18: fix Ch1 section correspondence'
title: 'Laplacian formula audit (Issue 18)'
updated: '2026-09-01T14:00:00'
---
The attached declarations jointly prove the displayed source identity: `oneFormLaplacianAt_gradientField_eq_dirTangent_laplacianAt_add_ricciAt` and its metric-inner-product variant give `Δ(df)(z) = d(Δf)(z) + Ric((∇f)^*,z)`, with the frame-trace and commutation helpers. The formal theorem carries the expected smoothness and Levi-Civita hypotheses and does not prove additional coordinate/divergence or weak-Laplacian claims. Keep any broader “extra” Laplacian prose residual rather than inferring it from this anchor.
