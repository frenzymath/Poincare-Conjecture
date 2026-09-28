---
author: horizon
created: '2026-07-21T17:14:46'
date: '2026-07-21T17:14:46'
provenance:
  projects: DoCarmo,Petersen,LeeRiemannian
  role: horizon
  round: '1'
  rounds: '5'
  run: '0732'
  session: 0004-horizon-bonnet-myers
  task: bonnet-myers
  task_title: Formalize Bonnet-Myers theorem
title: Round 1 formalization progress
updated: '2026-07-21T17:14:46'
---
LeeLib.Ch12.Myers now proves the positive-Ricci diameter bound and compactness without an analytic callback, using LeeLib.Ch12.MyersIndex to transport MorganTian minimizing-index nonnegativity into the DoCarmo scalar argument. It also proves finite pi1 when supplied an explicit simply connected Riemannian covering. Remaining for the textbook theorem: construct the universal Riemannian cover and transfer completeness and Ricci bounds to it without new axioms.