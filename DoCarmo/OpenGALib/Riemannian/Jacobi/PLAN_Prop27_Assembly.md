# Assembly plan: closing do Carmo Ch5 Prop 2.7 (|J(t)|² Taylor expansion) at the manifold level

## ✅ DONE (run 0158 s0002) — prop:dc-ch5-2-7 + cor:dc-ch5-2-10 CLOSED (frame form), axiom-clean

The C∞ frame instantiation landed and both nodes are `\leanok`:
- `JacobiFrameSmooth.lean`: `exists_contDiffOn_parallelOrthoFrame` (C∞ parallel orthonormal
  frame on an interval interior via the linear-ODE C∞ bootstrap on `ė=−Γ(u̇,e)`),
  `contDiffOn_infty_chartChristoffelContractionRight` (frame ODE coeff C∞),
  `exists_chartOrthonormalBasis_at` (orthonormal frame at a general chart point → t=0 interior).
- `JacobiTaylorManifold.lean`: `contDiffOn_infty_jacobiCoefOp` (frame curvature A C∞),
  `norm_sq_jacobi_frame_isLittleO` (= prop:2-7 frame form: `|J|²_g = ⟨w,w⟩t² − (1/3)⟨R(v,w)v,w⟩t⁴
  + o(t⁴)` for `J = Σ Fᵢ eᵢ`, `F` solving `F''=−A F`, via transfer to `EuclideanSpace ℝ (Fin n)`
  + the analytic core `norm_sq_jacobi_isLittleO_local`), `norm_jacobi_frame_isLittleO`
  (= cor:2-10, the `√` step under `|w|=1`, one-sided `𝓝[>]0`).
- Blueprint node `lem:dc-ch5-2-7-frame-smooth` (C∞ frame + coeff) added, `\leanok`.

**KEY simplification** vs the plan below: prop:2-7 is stated in **frame/coordinate form** taking the
frame Jacobi coefficients `F, V` as HYPOTHESES (as do Carmo's `J` is given), so it needs NO ODE
existence at an interior base point — the two-sided Taylor works because `F` is given on an open
interval around 0. The `expMapGlobal`/`CompleteSpace` reconciliation is entirely avoided.

## Residuals

- `cor:dc-ch5-2-9`: `⟨R(v,w)v,w⟩ = K(p,σ)` (sectional-curvature identification of the coefficient).
  Needs the bridge `chartMetricInner(chartCurvatureOp)(w)(w)` ↔ intrinsic `sectionalCurvature` at
  `p` (via `curvatureFormAt_chartFrame` + `wedgeSq=1` normalization; template in
  DoCarmoCh4SectionalPair). ~80–150 lines, separate curvature-identification task.
- A fully **manifold-existence** prop:2-7 (bundling "there IS a Jacobi field J with J(0)=0,
  DJ(0)=w along the exp geodesic, and |J|² expands"): needs the geodesic chart curve C∞
  (`exists_contDiffOn_infty_extChartAt_expMap_ball` ∘ `t↦tv` — ~40 lines, NOT built) + a two-sided
  frame ODE solution with `F(0)=0` at the INTERIOR point 0. The LinearODE engine
  (`exists_isJacobiPairOn`) only sets data at the LEFT endpoint; an interior-base-point existence
  (forward + backward solve glued via `exists_hasDerivWithinAt_glue`, needs a backward existence
  lemma) is the missing piece. The frame-form nodes above sidestep this.

---

## (Original plan, for the manifold-existence route)

Status after run 0155 s0010 (LEHENG.5): the **analytic core is done and axiom-clean**. What
remains is the *parallel-orthonormal-frame C∞ instantiation* that feeds the core with genuine
manifold Jacobi data. This is a multi-file, index-algebra-heavy assembly (~400–600 lines).

## Available (verified, committed)

- `norm_sq_jacobi_isLittleO_local` (JacobiTaylorExpansion.lean) — the target core.
  Hypotheses: `s` open convex ∋ 0, `ContDiffOn ℝ ∞ f s`, `ContDiffOn ℝ ∞ A s`,
  `∀t∈s, HasDerivAt f (v t) t`, `∀t∈s, HasDerivAt v (-(A t)(f t)) t`, `f 0 = 0`.
  Conclusion: `⟨f t,f t⟩ - (⟨v0,v0⟩t² - (1/3)⟨v0,A0 v0⟩t⁴) =o[𝓝 0] t⁴`.
- `sqrt_isLittleO_of_sq_isLittleO` (= lem:dc-ch5-2-10-sqrt) — the √ step for cor:2-10.
- `contDiff{,On}_infty_of_hasDerivAt_clm_apply` (ODESmoothness.lean) — ODE C∞ bootstrap
  `Y'=B(t)Y`, `B` C∞ ⟹ `Y` C∞ (global + open-set).
- `contDiffOn_infty_chartCurvatureOp` (JacobiCurvatureSmooth.lean) — `chartCurvatureOp g α u` is
  C∞ on open `s` when `u` is C∞ into the chart interior. **This discharges the `A` used below.**
- Frame reduction (FrameReduction.lean, all \leanok): `frameJacobiComponent` gives the scalar
  system `f_j'' + Σ_i f_i a_ij = 0`; `chartMetricInner_frameCombination_left` the orthonormal
  extraction; `covariantDerivCoord{,2}_frameCombination`.
- Parallel orthonormal frame on `Icc`: `exists_parallelOrthoFrame_self` (ParallelFrame.lean),
  but only `HasDerivWithinAt`/C¹ — see gap (2) below.
- exp smoothness on a ball (no completeness): `exists_contDiffOn_infty_extChartAt_expMap_ball`
  (CInftyBall.lean). Jacobi field = exp differential: `expDifferential_eq_jacobiField`
  (ExpDifferential.lean, uses `globalGeodesic`/`expMapGlobal`, `[CompleteSpace M]`).

## Remaining pieces (in dependency order)

1. **Geodesic chart reading is C∞ near 0.** `u(t) = extChartAt I p (exp_p(t v))` is `ContDiffOn ℝ ∞`
   on the open interval `{t : ‖t v‖ < ρ}` (compose `exists_contDiffOn_infty_extChartAt_expMap_ball`
   with the C∞ affine `t ↦ t•v`, `ContDiffOn.comp` + `MapsTo`). Then `hmem` (u into interior target)
   holds on a possibly-smaller open interval. Feeds `contDiffOn_infty_chartCurvatureOp` → `A` C∞.
   CAUTION: exp-ball uses local `expMap` + `[T2Space (TangentBundle I M)]`; the Jacobi field of
   `expDifferential_eq_jacobiField` uses `expMapGlobal` + `[CompleteSpace M]`. Reconcile via
   `expMap = expMapGlobal` while the geodesic stays in the chart at p (see GlobalExp.lean), OR
   redo the Jacobi field along the local `expMap` geodesic on the open interval.

2. **Parallel orthonormal frame `e_i(t)` is C∞ on the open interval.** The existing frame is on
   `Icc` with within-derivatives; upgrade to an open interval with two-sided `HasDerivAt` and then
   apply `contDiffOn_infty_of_hasDerivAt_clm_apply` to the parallel-transport ODE
   `deriv (e_i) t = -Γ(u t)(u̇ t, e_i t)` (coefficient `B(t) = -chartChristoffel contraction`, C∞
   once `u` is C∞ — analogous to `contDiffOn_infty_chartCurvatureOp`). Orthonormality is preserved
   (parallel transport is an isometry: `chartMetricInner_const_of_parallelSol`).

3. **Vector packaging.** Take `Efr := EuclideanSpace ℝ (Fin n)` (n = finrank). Set
   `f(t) = (f_i(t))_i` the frame coefficients of `J`, `v(t) = (f_i'(t))`, and `A(t)` the matrix
   `(a_ij(t)) = (⟨R(u̇,e_i)u̇,e_j⟩)` as a CLM on `Efr`. `frameJacobiComponent` gives `f'' = -A f`
   componentwise ⟹ the vector ODE `f'=v`, `v'=-Af`. C∞ of `f` from `J` C∞ (exp) + `e_i` C∞ (step 2)
   via the orthonormal extraction; C∞ of `A` from step 1 + step 2.

4. **`|J(t)|²_g = ‖f(t)‖²`.** Orthonormal expansion: `|J|²_g = Σ_i f_i² = ‖f‖²_Euclidean`
   (`frameExpansion` / `chartMetricInner_frameCombination_left` with `J = Σ f_i e_i`).

5. **`A(0)` identification.** `⟨v0, A0 v0⟩ = Σ_ij w_i w_j a_ij(0) = ⟨R(v, J'(0))v, J'(0)⟩
   = ⟨R(v,w)v,w⟩` where `w = J'(0)` (`sum_jacobiCoef_quadratic` + frame expansion of `w`).

6. **Assemble** → apply `norm_sq_jacobi_isLittleO_local` → `prop:dc-ch5-2-7`. Then:
   - `cor:dc-ch5-2-9`: `⟨R(v,w)v,w⟩ = sectionalCurvature (curvatureFormAt g p) v w` for `|v|=|w|=1`,
     `⟨v,w⟩=0` (wedgeSq = 1; template in DoCarmoCh4SectionalPair.lean:103–107). Substitute into (3).
   - `cor:dc-ch5-2-10`: apply `sqrt_isLittleO_of_sq_isLittleO` with `c = (1/3)K`, using `|J| = √|J|²`.

## Notes

- The whole expansion is at `t → 0`, so everything is needed only on an open interval around 0.
- `ex:dc-ch5-3-3` (S^n antipodal conjugate, mult n−1) is blocked on `ex:dc-ch5-2-3` (the explicit
  constant-curvature Jacobi solution `J = (sin t) w`), a separate sub-task; Ch6 supplies the S^n
  curvature=1 fact.
