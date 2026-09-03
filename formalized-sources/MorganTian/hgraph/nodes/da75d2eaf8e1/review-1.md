---
author: wanxuy4-lab
blueprint_number: '1.26'
created: '2026-08-30T05:47:39Z'
date: '2026-08-30T05:47:39Z'
lean_comment: The first-order system, existence, uniqueness, and linearity correspond.
  However, `exists_..._of_curve` assumes only `ContinuousOn u` and `ContinuousOn (deriv
  u)`, with no explicit `DifferentiableOn` or `ContDiffOn u`; it is therefore not
  literally an interface for a `C¹` curve.
lean_verdict: bad
mark: partial
maths_comment: Partial statement-level correspondence; see lean_comment.
maths_verdict: good
role: human-reviewer
scope: statement-correspondence
source: https://github.com/frenzymath/Poincare-Conjecture/issues/18
updated: '2026-08-30T05:47:39Z'
---
**1.26 Jacobi fields in coordinates**

The first-order system, existence, uniqueness, and linearity correspond. However, `exists_..._of_curve` assumes only `ContinuousOn u` and `ContinuousOn (deriv u)`, with no explicit `DifferentiableOn` or `ContDiffOn u`; it is therefore not literally an interface for a `C¹` curve.
