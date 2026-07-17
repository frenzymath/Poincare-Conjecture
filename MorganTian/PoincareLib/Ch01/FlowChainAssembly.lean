import PoincareLib.Ch01.FlowStepPartition
import PoincareLib.Ch01.JunctionStep
import PoincareLib.Ch01.JacobiRestriction
import PoincareLib.Ch01.FlowComposition

/-!
# Poincaré Ch. 1, §1.4 — assembling the geodesic-flow derivative chain

This file carries out **rung 3** of the flow-derivative gluing for the
differential of the exponential map (`lem:exponential-differential-jacobi`): it
interleaves the within-chart flow steps and the chart junctions of a compact
geodesic `γ = γ_v : [0,1] → M` into a single composed map, strictly
differentiable at the initial chart state, whose derivative transports the
Jacobi variational pair of *every* manifold Jacobi field along `γ` from time `0`
to time `1`.

The finite partition `0 = τ_0 ≤ τ_1 ≤ ⋯` with `τ_m = 1` for `m ≥ n`, per-piece
flow-step data `(flowEnd i, Dstep i)`, and both-sided chart membership at every
boundary come from `exists_geodesic_flowstep_partition` (`FlowStepPartition`);
the chart-junction links come from `exists_geodesic_junction_step`
(`JunctionStep`). Rather than interleave flow steps and junctions as separate
links with a parity index, we combine each piece into a single link

  `g i = stateTransition (β i) (β (i+1)) ∘ (flow step i)`,

which carries the chart-`β i` state at `τ i` directly to the chart-`β (i+1)`
state at `τ (i+1)`; the composed chain then has one link per piece and is
consumed by `hasStrictFDerivAt_comp_chain'` (`FlowComposition`). Degenerate
pieces, where the partition boundaries coincide (`τ i = τ (i+1)`, which can only
happen once `γ` has reached time `1`), use the identity for the flow part — a
manifold Jacobi field restricts to a *nondegenerate* subinterval only
(`IsJacobiFieldAlongOn.mono` needs `a' < b'`), so the flow-step transport is
invoked exactly on the nondegenerate pieces.

* `exists_geodesic_jacobiTransport_chain` — the assembled strict derivative of
  the geodesic-flow endpoint chain along `γ`, transporting the Jacobi variational
  pair from time `0` to time `1`.

Blueprint: `lem:exponential-differential-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The assembled geodesic-flow derivative chain.** Let `γ` be a
geodesic on an open set `U ⊇ [0,1]`. Then there are a starting chart `α ∋ γ 0`, a
terminal chart `ζ ∋ γ 1`, a map `F₀ : E × E → E × E` and a continuous linear map
`D₀` such that:

* `F₀` is strictly differentiable at the chart-`α` state `(φ_α(γ 0), u̇^α(0))` of
  `γ`, with derivative `D₀`;
* `F₀` carries that state to the chart-`ζ` state `(φ_ζ(γ 1), u̇^ζ(1))`;
* `D₀` transports the chart-`α` Jacobi variational pair of *every* manifold
  Jacobi field `(J, DJ)` along `γ` on `[0,1]` to the chart-`ζ` pair of the same
  field at time `1`.

`F₀` is the composite of the within-chart geodesic-flow endpoint maps and the
chart junctions along a finite chart/flow-step partition of `[0,1]`, and `D₀` is
the composite of their derivatives. Evaluated on the initial variational pair
`(0, Z)` of the Jacobi field `Y_Z` (Lemma's `Y_Z(0) = 0`, `∇_X Y_Z(0) = Z`), the
first component of `D₀ (0, Z)` is the chart reading of `Y_Z(1)` — the coordinate
content of `d(exp_p)_v(Z) = Y_Z(1)`.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem exists_geodesic_jacobiTransport_chain
    (g : RiemannianMetric I M) {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hsub : Icc (0 : ℝ) 1 ⊆ U) (hgeo : IsGeodesicOn (I := I) g γ U)
    (hcont : ContinuousOn γ U) :
    ∃ (α ζ : M) (F₀ : E × E → E × E) (D₀ : (E × E) →L[ℝ] E × E),
      γ 0 ∈ (chartAt H α).source ∧ γ 1 ∈ (chartAt H ζ).source ∧
      HasStrictFDerivAt F₀ D₀
          (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0) ∧
        F₀ (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0)
          = (extChartAt I ζ (γ 1), deriv (fun s => extChartAt I ζ (γ s)) 1) ∧
        (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ 0 1 →
          D₀ (jacobiVarPair (I := I) g α γ J DJ 0)
            = jacobiVarPair (I := I) g ζ γ J DJ 1) := by
  classical
  obtain ⟨τ, β, n, flowEnd, Dstep, Wnb, mwin, hτ0, hτn, hmono, hτIcc, hsrcL, hsrcR,
    hpiece⟩ := exists_geodesic_flowstep_partition (I := I) g hU hsub hgeo hcont
  have hτ1 : τ n = 1 := hτn n le_rfl
  -- continuity of `γ` at every partition time
  have hcontAt : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ t := fun t ht =>
    hcont.continuousAt (hU.mem_nhds (hsub ht))
  -- the chart-junction link at every boundary `τ (i+1)`
  have hjuncdata : ∀ i, ∃ Dtr : (E × E) →L[ℝ] E × E,
      HasStrictFDerivAt (stateTransition (I := I) (β i) (β (i + 1))) Dtr
          (extChartAt I (β i) (γ (τ (i + 1))),
            deriv (fun t => extChartAt I (β i) (γ t)) (τ (i + 1))) ∧
        stateTransition (I := I) (β i) (β (i + 1))
            (extChartAt I (β i) (γ (τ (i + 1))),
              deriv (fun t => extChartAt I (β i) (γ t)) (τ (i + 1)))
          = (extChartAt I (β (i + 1)) (γ (τ (i + 1))),
              deriv (fun t => extChartAt I (β (i + 1)) (γ t)) (τ (i + 1))) ∧
        (∀ J DJ : ℝ → E,
          Dtr (jacobiVarPair (I := I) g (β i) γ J DJ (τ (i + 1)))
            = jacobiVarPair (I := I) g (β (i + 1)) γ J DJ (τ (i + 1))) := fun i =>
    exists_geodesic_junction_step (I := I) g hgeo (hsub (hτIcc (i + 1)))
      (hcontAt (τ (i + 1)) (hτIcc (i + 1))) (hsrcR i) (hsrcL (i + 1))
  choose Dtr hjunc using hjuncdata
  -- the chain: state, combined map, combined derivative
  set x : ℕ → E × E := fun i =>
    (extChartAt I (β i) (γ (τ i)), deriv (fun s => extChartAt I (β i) (γ s)) (τ i)) with hxdef
  -- the flow part of piece `i`: identity on a degenerate piece, else `flowEnd i`
  set flowPart : ℕ → (E × E → E × E) := fun i =>
    if τ i = τ (i + 1) then id else flowEnd i with hflowPartdef
  set flowDeriv : ℕ → ((E × E) →L[ℝ] E × E) := fun i =>
    if τ i = τ (i + 1) then ContinuousLinearMap.id ℝ (E × E) else Dstep i with hflowDerivdef
  set f : ℕ → (E × E → E × E) := fun i =>
    stateTransition (I := I) (β i) (β (i + 1)) ∘ flowPart i with hfdef
  set L : ℕ → ((E × E) →L[ℝ] E × E) := fun i => (Dtr i).comp (flowDeriv i) with hLdef
  -- the flow part maps the chart state at `τ i` to the chart state at `τ (i+1)`
  have hfpt : ∀ i, flowPart i (x i)
      = (extChartAt I (β i) (γ (τ (i + 1))),
          deriv (fun s => extChartAt I (β i) (γ s)) (τ (i + 1))) := by
    intro i
    simp only [hflowPartdef]
    split_ifs with h
    · simp only [id_eq, hxdef]; rw [h]
    · exact (hpiece i).2.1
  -- the flow part is strictly differentiable at `x i`
  have hflowstrict : ∀ i, HasStrictFDerivAt (flowPart i) (flowDeriv i) (x i) := by
    intro i
    simp only [hflowPartdef, hflowDerivdef]
    split_ifs with h
    · exact hasStrictFDerivAt_id (x i)
    · exact (hpiece i).1
  -- link strict differentiability
  have hf : ∀ i < n, HasStrictFDerivAt (f i) (L i) (x i) := by
    intro i _
    have hg : HasStrictFDerivAt (stateTransition (I := I) (β i) (β (i + 1))) (Dtr i)
        (flowPart i (x i)) := by
      rw [hfpt i]; exact (hjunc i).1
    exact hg.comp (x i) (hflowstrict i)
  -- link base-point chaining
  have hstep : ∀ i < n, f i (x i) = x (i + 1) := by
    intro i _
    show stateTransition (I := I) (β i) (β (i + 1)) (flowPart i (x i)) = x (i + 1)
    rw [hfpt i]
    exact (hjunc i).2.1
  -- assemble the strict derivative
  obtain ⟨F₀, D₀, hderiv, hbase, htrans⟩ :=
    hasStrictFDerivAt_comp_chain' (n := n) f L x hf hstep
  refine ⟨β 0, β n, F₀, D₀, ?_, ?_, ?_, ?_, ?_⟩
  · -- γ 0 ∈ source (β 0)
    have := hsrcL 0; rwa [hτ0] at this
  · -- γ 1 ∈ source (β n)
    have := hsrcL n; rwa [hτ1] at this
  · -- strict derivative at the initial state
    have hx0 : x 0
        = (extChartAt I (β 0) (γ 0), deriv (fun s => extChartAt I (β 0) (γ s)) 0) := by
      simp only [hxdef, hτ0]
    rw [← hx0]; exact hderiv
  · -- endpoint identity
    have hx0 : x 0
        = (extChartAt I (β 0) (γ 0), deriv (fun s => extChartAt I (β 0) (γ s)) 0) := by
      simp only [hxdef, hτ0]
    have hxn : x n
        = (extChartAt I (β n) (γ 1), deriv (fun s => extChartAt I (β n) (γ s)) 1) := by
      simp only [hxdef, hτ1]
    rw [← hx0, ← hxn]; exact hbase
  · -- the Jacobi variational-pair transport
    intro J DJ hJ
    -- the marked-vector family: the chart-`β i` variational pair at `τ i`
    set p : ℕ → E × E := fun i => jacobiVarPair (I := I) g (β i) γ J DJ (τ i) with hpdef
    have hchain : ∀ i < n, L i (p i) = p (i + 1) := by
      intro i _
      simp only [hLdef, ContinuousLinearMap.comp_apply]
      -- the flow derivative transports the pair from `τ i` to `τ (i+1)` in chart `β i`
      have hflowp : flowDeriv i (p i)
          = jacobiVarPair (I := I) g (β i) γ J DJ (τ (i + 1)) := by
        simp only [hflowDerivdef, hpdef]
        split_ifs with h
        · simp only [ContinuousLinearMap.id_apply]; rw [h]
        · have hlt : τ i < τ (i + 1) := lt_of_le_of_ne (hmono (Nat.le_succ i)) h
          exact (hpiece i).2.2.1 J DJ
            (hJ.mono (hτIcc i).1 hlt (hτIcc (i + 1)).2)
      rw [hflowp]
      exact (hjunc i).2.2 J DJ
    have := htrans p hchain
    simpa only [hpdef, hτ0, hτ1] using this

/-- **Math.** **The assembled chain on a Jacobi field vanishing at the start.**
Specialization of `exists_geodesic_jacobiTransport_chain` to a manifold Jacobi
field `(J, DJ)` whose chart reading vanishes at time `0` (`J^α(0) = 0`, in
particular whenever `J 0 = 0`). Then the initial Jacobi variational pair is
`(0, DJ^α(0))` (`jacobiVarPair_of_left_eq_zero`), so the composed derivative `D₀`
sends `(0, DJ^α(0))` to the chart-`ζ` variational pair of the field at time `1`,
whose first component is the chart reading of `J(1)`.

For the Jacobi field `Y_Z` of `lem:exponential-differential-jacobi`, where
`Y_Z(0) = 0` and `∇_X Y_Z(0) = Z`, the datum `(0, DJ^α(0))` is exactly the
initial vector `(0, Z)` read in the starting chart, so this is the chart-level
form of `d(exp_p)_v(Z) = Y_Z(1)` — the object rung 4 identifies with
`mfderiv (exp_p) v (Z)`.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem exists_geodesic_jacobiTransport_chain_initialZero
    (g : RiemannianMetric I M) {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hsub : Icc (0 : ℝ) 1 ⊆ U) (hgeo : IsGeodesicOn (I := I) g γ U)
    (hcont : ContinuousOn γ U) :
    ∃ (α ζ : M) (F₀ : E × E → E × E) (D₀ : (E × E) →L[ℝ] E × E),
      γ 0 ∈ (chartAt H α).source ∧ γ 1 ∈ (chartAt H ζ).source ∧
      HasStrictFDerivAt F₀ D₀
          (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0) ∧
        F₀ (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0)
          = (extChartAt I ζ (γ 1), deriv (fun s => extChartAt I ζ (γ s)) 1) ∧
        (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ 0 1 →
          chartVectorRep (I := I) γ α J 0 = 0 →
          D₀ (0, chartVectorRep (I := I) γ α DJ 0)
            = jacobiVarPair (I := I) g ζ γ J DJ 1) := by
  obtain ⟨α, ζ, F₀, D₀, hα, hζ, hderiv, hbase, htrans⟩ :=
    exists_geodesic_jacobiTransport_chain (I := I) g hU hsub hgeo hcont
  refine ⟨α, ζ, F₀, D₀, hα, hζ, hderiv, hbase, ?_⟩
  intro J DJ hJ hJ0
  have hpair := htrans J DJ hJ
  rwa [jacobiVarPair_of_left_eq_zero (I := I) g α γ J DJ 0 hJ0] at hpair

end PoincareLib

end
