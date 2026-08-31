---
author: Ezreal88
created: '2026-07-30T11:15:07Z'
date: '2026-07-30T11:15:07Z'
label: def:dc-ch3-3-3
lean_comment: '**1. $C^r$ vs differentiable.** Same issue as `def:dc-ch3-3-1` #1.
  do Carmo says "differentiable," the Lean uses `ContMDiffOn ... r` ($C^r$). Affects
  `IsParametrizedSurfaceOfOrder`, `IsExtendedParametrizedSurfaceOfOrder`, and `IsVectorFieldAlong`.
  Replace with `MDifferentiableOn` or justify the upgrade.


  **2. Vertex angle on $M$ not defined.** `IsNonPiAngle` handles only $\mathbb{R}^2$
  vectors. The manifold-level vertex angle of a piecewise differentiable curve in
  $M$ is not defined. For Hopf-Rinow this is not blocking (corner rigidity uses length,
  not angle). Add `-- TODO:


  […truncated…]'
lean_verdict: bad
mark: problem
maths_comment: '**1. $C^r$ vs differentiable.** Same issue as `def:dc-ch3-3-1` #1.
  do Carmo says "differentiable," the Lean uses `ContMDiffOn ... r` ($C^r$). Affects
  `IsParametrizedSurfaceOfOrder`, `IsExtendedParametrizedSurfaceOfOrder`, and `IsVectorFieldAlong`.
  Replace with `MDifferentiableOn` or justify the upgrade.


  **2. Vertex angle on $M$ not defined.** `IsNonPiAngle` handles only $\mathbb{R}^2$
  vectors. The manifold-level vertex angle of a piecewise differentiable curve in
  $M$ is not defined. For Hopf-Rinow this is not blocking (corner rigidity uses length,
  not angle). Add `-- TODO:


  […truncated…]'
maths_verdict: bad
role: human-reviewer
scope: statement-correspondence
source: https://github.com/frenzymath/Poincare-Conjecture/issues/9
updated: '2026-07-30T11:15:07Z'
---
**def:dc-ch3-3-3**

**1. $C^r$ vs differentiable.** Same issue as `def:dc-ch3-3-1` #1. do Carmo says "differentiable," the Lean uses `ContMDiffOn ... r` ($C^r$). Affects `IsParametrizedSurfaceOfOrder`, `IsExtendedParametrizedSurfaceOfOrder`, and `IsVectorFieldAlong`. Replace with `MDifferentiableOn` or justify the upgrade.

**2. Vertex angle on $M$ not defined.** `IsNonPiAngle` handles only $\mathbb{R}^2$ vectors. The manifold-level vertex angle of a piecewise differentiable curve in $M$ is not defined. For Hopf-Rinow this is not blocking (corner rigidity uses length, not angle). Add `-- TODO:

[…truncated…]
