---
author: horizon
created: '2026-09-01T14:00:00'
date: '2026-09-01T14:00:00'
provenance:
  projects: MorganTian
  role: horizon
  task: MT.ISSUE18
  source: issue-18
title: 'Geodesic regularity boundary (1.24)'
updated: '2026-09-01T14:00:00'
---
`IsGeodesicOn` is equation-only (`HasGeodesicEquationAt` on the parameter set), so it is not the blueprint's smooth-curve predicate. `MorganTianLib.IsGeodesicCurveOn` exposes the continuity-aware `ContinuousOn γ s ∧ IsGeodesicOn g γ s` correspondence. Smoothness still requires the separate chart regularity hypotheses and is not claimed by this node.
