---
author: Lightmarey
blueprint_number: '1.96'
created: '2026-08-23T15:59:02Z'
date: '2026-08-23T15:59:02Z'
label: thm:sectional-curvature-comparison
lean_comment: '## Nodes 1.96 and 1.101: independent adjudication requested


  I am not reporting nodes 1.96 and 1.101 as definite errors, but their correspondence
  is not a simple strengthening or weakening.


  For both nodes, the Lean statements introduce global completeness and global-exponential-map
  infrastructure that are absent from the source theorem. On the other hand, their
  curvature assumptions are localized along the selected radial geodesic, whereas
  the source states global sectional- or Ricci-curvature bounds. Thus neither set
  of hypotheses simply implies the other.


  Their conclusions are also expressed differently:


  - the source uses Gaussian polar-coordinate tensors $g_{ij}$, t


  […truncated…]'
lean_verdict: bad
mark: partial
maths_comment: independent adjudication requested — hypothesis/conclusion packaging
  differs
maths_verdict: good
role: human-reviewer
scope: statement-correspondence
source: https://github.com/frenzymath/Poincare-Conjecture/issues/16
updated: '2026-08-23T15:59:02Z'
---
**1.96 thm:sectional-curvature-comparison**

## Nodes 1.96 and 1.101: independent adjudication requested

I am not reporting nodes 1.96 and 1.101 as definite errors, but their correspondence is not a simple strengthening or weakening.

For both nodes, the Lean statements introduce global completeness and global-exponential-map infrastructure that are absent from the source theorem. On the other hand, their curvature assumptions are localized along the selected radial geodesic, whereas the source states global sectional- or Ricci-curvature bounds. Thus neither set of hypotheses simply implies the other.

Their conclusions are also expressed differently:

- the source uses Gaussian polar-coordinate tensors $g_{ij}$, t

[…truncated…]
