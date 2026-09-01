---
author: Lightmarey
blueprint_number: '1.117'
created: '2026-08-23T15:59:02Z'
date: '2026-08-23T15:59:02Z'
label: thm:bishop-gromov
lean_comment: "## 1.117: the mapped declarations do not state manifold Bishop-Gromov\n\
  \nThe blueprint statement for node 1.117 assumes, in geometric terms,\n\n- a Riemannian\
  \ manifold $(M,g)$;\n- a point $p\\in M$;\n- compact closure of \\(B(p,R)\\);\n\
  - ${Ric}\\ge -(n-1)k$ on $B(p,R)$;\n\nand concludes that\n\n$$\nr\\longmapsto\n\\\
  frac{{Vol}B(p,r)}\n     {{Vol}B_{H_k^n}(q_k,r)}\n$$\n\nis non-increasing, tends\
  \ to \\(1\\) as \\(r\\to0\\), and yields the usual \\(k=0\\) consequence.\n\nThe\
  \ mapped declarations\n\n```lean\nbishop_gromov_ball\nbishop_gromov_ball_ratio\n\
  ```\n\ndo not have this statement. They concern an arbitrary measurable density\
  \ `ρ : E → ℝ` and assume directly that, in every unit direction, the polar-density\
  \ rati\n\n[…truncated…]"
lean_verdict: bad
mark: problem
maths_comment: "## 1.117: the mapped declarations do not state manifold Bishop-Gromov\n\
  \nThe blueprint statement for node 1.117 assumes, in geometric terms,\n\n- a Riemannian\
  \ manifold $(M,g)$;\n- a point $p\\in M$;\n- compact closure of \\(B(p,R)\\);\n\
  - ${Ric}\\ge -(n-1)k$ on $B(p,R)$;\n\nand concludes that\n\n$$\nr\\longmapsto\n\\\
  frac{{Vol}B(p,r)}\n     {{Vol}B_{H_k^n}(q_k,r)}\n$$\n\nis non-increasing, tends\
  \ to \\(1\\) as \\(r\\to0\\), and yields the usual \\(k=0\\) consequence.\n\nThe\
  \ mapped declarations\n\n```lean\nbishop_gromov_ball\nbishop_gromov_ball_ratio\n\
  ```\n\ndo not have this statement. They concern an arbitrary measurable density\
  \ `ρ : E → ℝ` and assume directly that, in every unit direction, the polar-density\
  \ rati\n\n[…truncated…]"
maths_verdict: bad
role: human-reviewer
scope: statement-correspondence
source: https://github.com/frenzymath/Poincare-Conjecture/issues/16
updated: '2026-08-23T15:59:02Z'
---
**1.117 thm:bishop-gromov**

## 1.117: the mapped declarations do not state manifold Bishop-Gromov

The blueprint statement for node 1.117 assumes, in geometric terms,

- a Riemannian manifold $(M,g)$;
- a point $p\in M$;
- compact closure of \(B(p,R)\);
- ${Ric}\ge -(n-1)k$ on $B(p,R)$;

and concludes that

$$
r\longmapsto
\frac{{Vol}B(p,r)}
     {{Vol}B_{H_k^n}(q_k,r)}
$$

is non-increasing, tends to \(1\) as \(r\to0\), and yields the usual \(k=0\) consequence.

The mapped declarations

```lean
bishop_gromov_ball
bishop_gromov_ball_ratio
```

do not have this statement. They concern an arbitrary measurable density `ρ : E → ℝ` and assume directly that, in every unit direction, the polar-density rati

[…truncated…]
