---
author: JxChen24
created: '2026-07-22T15:09:23Z'
date: '2026-07-22T15:09:23Z'
label: lem:dc-ch9-2-4-symmetry-manifold
lean_comment: 'lem:dc-ch9-2-4-symmetry-manifold`. It does carry a heavy hypothesis
  load (a chart selector, both slice windows in one chart source), so it''s not that
  nothing is missing.

  - **The proposed wrapper wouldn''t help.** It typechecks — I tried it — but it''s
  a definitional re-wrap: `covariant_sndFDeriv_symm_of_eventually` already takes `c
  : ℝ × ℝ → E` fully generally, so instantiating `c := fun q => extChartAt I α (s
  q)` is pure unificat'
lean_verdict: bad
mark: problem
maths_comment: 'lem:dc-ch9-2-4-symmetry-manifold`. It does carry a heavy hypothesis
  load (a chart selector, both slice windows in one chart source), so it''s not that
  nothing is missing.

  - **The proposed wrapper wouldn''t help.** It typechecks — I tried it — but it''s
  a definitional re-wrap: `covariant_sndFDeriv_symm_of_eventually` already takes `c
  : ℝ × ℝ → E` fully generally, so instantiating `c := fun q => extChartAt I α (s
  q)` is pure unificat'
maths_verdict: bad
role: human-reviewer
scope: statement-correspondence
source: https://github.com/frenzymath/Poincare-Conjecture/issues/6
title: 'issue #6: lem:dc-ch9-2-4-symmetry-manifold'
updated: '2026-07-22T15:09:23Z'
---
**lem:dc-ch9-2-4-symmetry-manifold** — from issue #6: Issue on Hopf-Rinow Formalization #2

lem:dc-ch9-2-4-symmetry-manifold`. It does carry a heavy hypothesis load (a chart selector, both slice windows in one chart source), so it's not that nothing is missing.
- **The proposed wrapper wouldn't help.** It typechecks — I tried it — but it's a definitional re-wrap: `covariant_sndFDeriv_symm_of_eventually` already takes `c : ℝ × ℝ → E` fully generally, so instantiating `c := fun q => extChartAt I α (s q)` is pure unificat
