---
author: wanxuy4-lab
blueprint_number: '1.41'
created: '2026-08-30T05:47:39Z'
date: '2026-08-30T05:47:39Z'
lean_comment: Lean assumes `0<t₀<1`, `v≠0`, and completeness, while the prose states
  only `t₀<1`. The present Lean theorem does not cover the constant minimizing-geodesic
  case.
lean_verdict: bad
mark: partial
maths_comment: Partial statement-level correspondence; see lean_comment.
maths_verdict: good
role: human-reviewer
scope: statement-correspondence
source: https://github.com/frenzymath/Poincare-Conjecture/issues/18
updated: '2026-08-30T05:47:39Z'
---
**1.41 Exponential map is a local diffeomorphism**

Lean assumes `0<t₀<1`, `v≠0`, and completeness, while the prose states only `t₀<1`. The present Lean theorem does not cover the constant minimizing-geodesic case.
