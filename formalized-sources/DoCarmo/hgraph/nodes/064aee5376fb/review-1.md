---
author: Ezreal88
created: '2026-07-30T11:15:07Z'
date: '2026-07-30T11:15:07Z'
label: def:dc-ch3-3-1
lean_comment: "**1. `ContMDiffOn ... 1` (C¹) should be `MDifferentiableOn` (differentiable).**\
  \ do Carmo says \"differentiable,\" not \"C¹.\" Replace `ContMDiffOn \U0001D4D8\
  (ℝ, ℝ) I 1` with `MDifferentiableOn \U0001D4D8(ℝ, ℝ) I`.\n\n**2. Vertex is not defined.**\
  \ do Carmo names the partition points as vertices. Add:\n\n```lean\ndef IsPiecewiseDifferentiableCurve.vertexAt\
  \ {c : ℝ → M} {a b : ℝ}\n    (h : IsPiecewiseDifferentiableCurve (I := I) c a b)\
  \ (i : ℕ) : M :=\n  let ⟨_, _, τ, _, _, _, _, _⟩ := h.2\n  c (τ i)\n```\n\n**3.\
  \ Vertex angle — deferred.** Not used in the Hopf-Rinow proof chain. Add `-- TODO:\
  \ define vertex angl\n\n[…truncated…]"
lean_verdict: bad
mark: problem
maths_comment: "**1. `ContMDiffOn ... 1` (C¹) should be `MDifferentiableOn` (differentiable).**\
  \ do Carmo says \"differentiable,\" not \"C¹.\" Replace `ContMDiffOn \U0001D4D8\
  (ℝ, ℝ) I 1` with `MDifferentiableOn \U0001D4D8(ℝ, ℝ) I`.\n\n**2. Vertex is not defined.**\
  \ do Carmo names the partition points as vertices. Add:\n\n```lean\ndef IsPiecewiseDifferentiableCurve.vertexAt\
  \ {c : ℝ → M} {a b : ℝ}\n    (h : IsPiecewiseDifferentiableCurve (I := I) c a b)\
  \ (i : ℕ) : M :=\n  let ⟨_, _, τ, _, _, _, _, _⟩ := h.2\n  c (τ i)\n```\n\n**3.\
  \ Vertex angle — deferred.** Not used in the Hopf-Rinow proof chain. Add `-- TODO:\
  \ define vertex angl\n\n[…truncated…]"
maths_verdict: bad
role: human-reviewer
scope: statement-correspondence
source: https://github.com/frenzymath/Poincare-Conjecture/issues/9
updated: '2026-07-30T11:15:07Z'
---
**def:dc-ch3-3-1**

**1. `ContMDiffOn ... 1` (C¹) should be `MDifferentiableOn` (differentiable).** do Carmo says "differentiable," not "C¹." Replace `ContMDiffOn 𝓘(ℝ, ℝ) I 1` with `MDifferentiableOn 𝓘(ℝ, ℝ) I`.

**2. Vertex is not defined.** do Carmo names the partition points as vertices. Add:

```lean
def IsPiecewiseDifferentiableCurve.vertexAt {c : ℝ → M} {a b : ℝ}
    (h : IsPiecewiseDifferentiableCurve (I := I) c a b) (i : ℕ) : M :=
  let ⟨_, _, τ, _, _, _, _, _⟩ := h.2
  c (τ i)
```

**3. Vertex angle — deferred.** Not used in the Hopf-Rinow proof chain. Add `-- TODO: define vertex angl

[…truncated…]
