---
author: Lightmarey
blueprint_number: '1.115'
created: '2026-08-23T15:59:02Z'
date: '2026-08-23T15:59:02Z'
label: lem:model-ball-volume
lean_comment: "## 1.115: model-ball volume and density\n\nThe current definition is\n\
  \n```lean\ndef modelBallVolume (k : ℝ) (r : ℝ) : ℝ≥0∞ :=\n  ∫⁻ x in ball (0 : E)\
  \ r,\n    ENNReal.ofReal\n      ((snK k ‖x‖ / ‖x‖) ^ (finrank ℝ E - 1)) ∂μ\n```\n\
  \nThus `modelBallVolume` is defined directly as an integral on an abstract finite-dimensional\
  \ normed space. The formalization does not construct the model Riemannian manifold\
  \ \\(H_k^n\\), its Riemannian measure, or its metric ball, and it does not prove\
  \ an identification of the form\n\n$$\n{Vol}_{H_k^n}(B(q_k,r))=\n\\int_{B(0,r)}\n\
  \\left(\\frac{{sn}_k(|v|)}{|v|}\\right)^{n-1}dv.\n$$\n\nConsequently, `modelBallVolume_eq`\
  \ correctly proves a polar-coordinate identity for th\n\n[…truncated…]"
lean_verdict: bad
mark: problem
maths_comment: "## 1.115: model-ball volume and density\n\nThe current definition\
  \ is\n\n```lean\ndef modelBallVolume (k : ℝ) (r : ℝ) : ℝ≥0∞ :=\n  ∫⁻ x in ball (0\
  \ : E) r,\n    ENNReal.ofReal\n      ((snK k ‖x‖ / ‖x‖) ^ (finrank ℝ E - 1)) ∂μ\n\
  ```\n\nThus `modelBallVolume` is defined directly as an integral on an abstract\
  \ finite-dimensional normed space. The formalization does not construct the model\
  \ Riemannian manifold \\(H_k^n\\), its Riemannian measure, or its metric ball, and\
  \ it does not prove an identification of the form\n\n$$\n{Vol}_{H_k^n}(B(q_k,r))=\n\
  \\int_{B(0,r)}\n\\left(\\frac{{sn}_k(|v|)}{|v|}\\right)^{n-1}dv.\n$$\n\nConsequently,\
  \ `modelBallVolume_eq` correctly proves a polar-coordinate identity for th\n\n[…truncated…]"
maths_verdict: bad
role: human-reviewer
scope: statement-correspondence
source: https://github.com/frenzymath/Poincare-Conjecture/issues/16
updated: '2026-08-23T15:59:02Z'
---
**1.115 lem:model-ball-volume**

## 1.115: model-ball volume and density

The current definition is

```lean
def modelBallVolume (k : ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in ball (0 : E) r,
    ENNReal.ofReal
      ((snK k ‖x‖ / ‖x‖) ^ (finrank ℝ E - 1)) ∂μ
```

Thus `modelBallVolume` is defined directly as an integral on an abstract finite-dimensional normed space. The formalization does not construct the model Riemannian manifold \(H_k^n\), its Riemannian measure, or its metric ball, and it does not prove an identification of the form

$$
{Vol}_{H_k^n}(B(q_k,r))=
\int_{B(0,r)}
\left(\frac{{sn}_k(|v|)}{|v|}\right)^{n-1}dv.
$$

Consequently, `modelBallVolume_eq` correctly proves a polar-coordinate identity for th

[…truncated…]
