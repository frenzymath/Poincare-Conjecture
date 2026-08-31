---
author: Ezreal88
created: '2026-07-30T11:15:07Z'
date: '2026-07-30T11:15:07Z'
label: lem:dc-ch3-3-4
lean_comment: '**1. `c` maps into `E`, not `M`.** The theorem is about chart readings,
  not about surfaces on the manifold.


  **2. `D/∂v`, `D/∂u` are not defined.** The book uses intrinsic covariant derivatives;
  the Lean uses Christoffel symbols in coordinates.


  **3. No bridge lemma.** The equivalence between chart computation and manifold covariant
  derivative is not stated.'
lean_verdict: bad
mark: partial
maths_comment: See lean_comment / issue body.
maths_verdict: good
role: human-reviewer
scope: statement-correspondence
source: https://github.com/frenzymath/Poincare-Conjecture/issues/9
updated: '2026-07-30T11:15:07Z'
---
**lem:dc-ch3-3-4**

**1. `c` maps into `E`, not `M`.** The theorem is about chart readings, not about surfaces on the manifold.

**2. `D/∂v`, `D/∂u` are not defined.** The book uses intrinsic covariant derivatives; the Lean uses Christoffel symbols in coordinates.

**3. No bridge lemma.** The equivalence between chart computation and manifold covariant derivative is not stated.
