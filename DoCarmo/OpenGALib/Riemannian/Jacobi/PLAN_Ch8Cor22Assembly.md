# Plan: do Carmo Ch8 `cor:dc-ch8-2-2` / `cor:dc-ch8-2-3` — φ_t-free manifold assembly

> **UPDATE run 0161 s0010 — GAP A + the norm core of GAP C are DONE via a cleaner route.**
> `JacobiConstCurvatureNorm.lean` (axiom-clean, lib green 3338) makes the frame-transfer lift
> (GAP A1/A2 below) UNNECESSARY for the isometry claim. Instead of transferring `J` through an
> `ẽ = i`-transport frame, we prove the **intrinsic norm formula**
> `metricInner_jacobiField_eq_of_constantCurvature`:
> `|J(t)|² = t² a² + h(t)² (|Z|² − a²)`, `a = ⟨DJ(0),γ'(0)⟩`, `Z = DJ(0)`,
> which is manifold-independent, and its corollary
> `metricInner_jacobiField_transfer_of_constantCurvature`: two same-`K₀` manifolds with matching
> `⟨DJ(0),γ'(0)⟩` and `|DJ(0)|²` have `|J̃(t)| = |J(t)|`. Since a linear isometry `i` with
> `i(γ'(0)) = γ̃'(0)` preserves both invariants, `J̃` need only be produced by
> `exists_isJacobiFieldAlongOn` with `DJ̃(0) = i(DJ(0))` — no frame transfer, no chart lift.
> Sign-uniform (`isJacobiFieldAlongOn_of_constantCurvature` takes an abstract `h`, `h''+K₀h=0`).
>
> **Remaining for `cor:2-2`/`cor:2-3`:** only **GAP B1** (invert `d exp_p` on the normal nbhd) and
> **GAP D** (assemble `DCIsLocalIsometryAt` + `df_p = i` from `expDifferential_eq_jacobiField` on both
> sides + surjectivity of `Z ↦ J(ℓ)` = `d exp_p` iso). GAP C's norm-preservation is now a one-liner
> from `metricInner_jacobiField_transfer_of_constantCurvature`.
>
> **Lean gotcha (recorded):** `TangentSpace I x` is a semireducible def of `E`, so `rw`/`simp` of
> `g.metricInner_{add,smul}_left/right` FAIL on `E`-typed sums. Do all bilinear expansion inside
> `TangentSpace`-typed private helpers and bridge to the `E`-typed goal with `exact`/`.trans`.
> `smul_smul` also won't fire after `set velt : E := mfderiv …` (keeps the `TangentSpace`-smul
> instance) — give the helper the `p • (r • V)` shape directly.

Status after run 0161 s0008. The **chart-level analytic heart is complete**; the residual is
the **manifold assembly**, doable chart-locally, `φ_t`-free (both spaces share the same constant
curvature `K₀`, so the curvature-match is automatic — see `jacobiFrameTransfer_isConstantCurvature`).

## Atoms already landed (all `\leanok`, axiom-clean)

- `jacobiFrameTransfer` / `jacobiFrameTransfer_isConstantCurvature`
  (`JacobiFrameTransfer*.lean`) — the CHART frame transfer: `∑ yᵢ eᵢ` Jacobi ⟹ `∑ yᵢ ẽᵢ` Jacobi
  on the second manifold, same scalar coeffs, matching discharged from `IsConstantCurvature`.
- `exists_velocitySeededParallelOrthoFrame` (`VelocitySeededFrame.lean`) — **step 1**: a parallel
  ON frame `e` along `γ` in chart `α` with `e n₀ t = deriv u t` (= `γ'`) for all `t`.
- `eq_sum_chartMetricInner_smul_of_orthonormal` (`VelocitySeededFrame.lean`) — **step 2a**:
  `v = ∑ᵢ ⟨v, eᵢ⟩ eᵢ` in a chart-ON frame; turns a frame-read field into its coeffs `yᵢ = ⟨J, eᵢ⟩`.
- `IsJacobiFieldOn.chartJacobiEquation` (`VelocitySeededFrame.lean`) — **step 2b**: the chart
  Jacobi pair system ⟹ the second-order form `∇(∇J) t + chartCurvatureEndo(u̇)(J t) = 0` (interior
  `t`) — exactly the `hjac` shape `jacobiFrameTransfer_isConstantCurvature` consumes.
- `expDifferential_eq_jacobiField` (`ExpDifferential.lean`, `cor:dc-ch5-2-5`) — `d(exp_p)_v(Z) =
  Y_Z(1)`, chart-`ζ` reading, with the Jacobi field `Y_Z` (`Y_Z(0)=0`, `∇Y_Z(0)=Z`).
- `DCIsLocalIsometryAt` (`DoCarmoCh1.lean`) — target: `∃ U ∈ 𝓝 p, ∀ q∈U, ∀ u v, ⟨u,v⟩_q =
  ⟨df_q u, df_q v⟩`.

## Remaining sub-steps (the manifold assembly)

### (A) Manifold Jacobi transfer in constant curvature — the heart
Statement to build (both `γ` on `M`, `γ̃` on `M̃`, unit-speed, `IsConstantCurvature K₀` on both,
chart readings `u, ū`; `i` a linear isometry with `ẽ = i`-transport of `e`, same index `n₀`, so
`ẽ n₀ = γ̃'`):
- Given manifold `IsJacobiFieldAlongOn g γ J DJ 0 ℓ` with `J 0 = 0`, produce
  `IsJacobiFieldAlongOn g' γ̃ J̃ DJ̃ 0 ℓ` with `J̃ 0 = 0`, `DJ̃ 0 = i (DJ 0)`, and `|J̃ t| = |J t|`.
- Coeffs `yᵢ(t) = chartMetricInner g α (u t) (chartVectorRep γ α J t) (eᵢ t)`; by 2a,
  `chartVectorRep γ α J = fun t => ∑ᵢ yᵢ t • eᵢ t` (funext).
- `hjac` at interior `t` from `IsJacobiFieldOn.chartJacobiEquation` (extract the chart
  `IsJacobiFieldOn` from `IsJacobiFieldAlongOn` at `t₀`).
- Apply `jacobiFrameTransfer_isConstantCurvature` ⟹ `∑ yᵢ ẽᵢ` solves the `M̃` chart 2nd-order eq.
- `|J̃ t|² = ∑ yᵢ² = |J t|²` by orthonormality of `ẽ` and `e` (2a backward + `horth`).

**GAP A1 (analytic): smoothness of the coeffs `yᵢ`.** `jacobiFrameTransfer` needs `hf` (`yᵢ`
diff'able near `t`), `hf2` (`deriv yᵢ` diff'able at `t`), `he` (`eᵢ` diff'able). `yᵢ = ⟨J, eᵢ⟩`
is a product; `eᵢ` diff'able from the parallel ODE (`HasDerivWithinAt` ⟹ interior `HasDerivAt`);
`J` chart reading is `C¹` from `IsJacobiFieldOn.hasDerivWithinAt_fst`, and `C²` because `DJ` is
`C¹` (`hasDerivWithinAt_snd`). Assemble `hf/hf2` from these. Model on `JacobiFrameSmooth.lean`
(`exists_contDiffOn_parallelOrthoFrame`) and `JacobiTaylorManifold.lean`.

**GAP A2 (lift): chart solution `∑ yᵢ ẽᵢ` ⟹ manifold `IsJacobiFieldAlongOn J̃`.** Define
`J̃ t := (tangentCoordChange I' α' (γ̃ t))⁻¹` of `∑ yᵢ t • ẽᵢ t` (invert `chartVectorRep`), and
`DJ̃` from `∇(∑ yᵢ ẽᵢ)`. Verify the pair system `IsJacobiFieldOn g' α' ū (chartVectorRep γ̃ α' J̃)
(chartVectorRep γ̃ α' DJ̃)`. The 2nd-order eq + the parallel-frame first-order structure gives both
pair equations (mirror `isJacobiFieldOn_of_constantCurvature` / `frameJacobiComponent`).
Alternatively: build `J̃` directly as the frame combination and use `exists_isJacobiFieldAlongOn`
+ uniqueness (`IsJacobiFieldAlongOn.eqOn_of_initial`) to identify it with `∑ yᵢ ẽᵢ`.

### (B) exp-differential both sides
`J t = (d exp_p)_{tγ'(0)}(t J'(0))`, `J̃ t = (d exp_{p̃})_{tγ̃'(0)}(t J̃'(0))` via
`expDifferential_eq_jacobiField`. With `f = exp_{p̃} ∘ i ∘ exp_p⁻¹`, get
`df_q (J ℓ) = J̃ ℓ = (d exp_{p̃}) ∘ i ∘ (d exp_p)⁻¹ (J ℓ)`.
**GAP B1: invert `d exp_p` on the normal nbhd.** `exp_p` is a diffeo on `V` (normal nbhd), so
`(d exp_p)_v` is a linear iso; extract the inverse. Look at `Exponential/TotallyNormalDiffeo.lean`,
`GlobalExp.lean`, and the pole/normal-nbhd infra used for `hadamardDiffeomorphOfNonpos`.

### (C) `df_q` is a linear isometry
Every `v ∈ T_qM` is `J ℓ` for the Jacobi field with `J'(0) = (d exp_p)⁻¹(v)` (surjectivity of
`J'(0) ↦ J(ℓ)`, = `d exp_p` iso). Then `|df_q v| = |J̃ ℓ| = |J ℓ| = |v|` (from A). A linear
norm-preserving map preserves the inner product (polarization / `inner_map_polarization`).

### (D) `DCIsLocalIsometryAt f p` and `df_p = i`
- `df_p = i`: at `q = p` (`ℓ → 0`), `d exp_p` at `0` is the identity, so `df_p = i` (state as
  `mfderiv I I' f p = i` or chart-reading `HasFDerivAt`, mirror `hasFDerivAt_chartReading_expMapGlobal`).
- `DCIsLocalIsometryAt`: take `U = V`; `∀ q ∈ V, ∀ u v, ⟨u,v⟩_q = ⟨df_q u, df_q v⟩` is (C) +
  metric-preservation from inner-product preservation. `f` is `C∞` on `V` (composite of
  `exp`/`i`/`exp⁻¹`), so `mfderiv` is the honest differential.

## `cor:dc-ch8-2-3` (single `M`, points `p, q`)
Same as `cor:2-2` with `M̃ = M`, `p̃ = q`, `i` the isometry `T_pM → T_qM` sending `{eⱼ}` to
`{fⱼ}` (both ON bases). Should be a thin specialization once `cor:2-2` lands.

## Blueprint wiring
`cor:dc-ch8-2-2` / `cor:dc-ch8-2-3` currently bare; `\uses` already list
`lem:dc-ch8-2-1-velocity-frame`. On landing (A)-(D), tag both `\lean{}`/`\leanok`. The general
`thm:dc-ch8-2-1` stays `\notready` (needs `φ_t` + cross-manifold curvature-naturality, a separate
new file) — only the same-`K₀` corollaries are unblocked.
