import OpenGALib.Riemannian.Jacobi.FlowStepPartitionContDiff
import OpenGALib.Riemannian.Jacobi.FlowChainNbhd

/-!
# The geodesic-flow chain is `C^∞` and computes nearby geodesic endpoints

This is the `C^∞` companion of `exists_geodesic_jacobiTransport_chain_nbhd`
(`FlowChainNbhd.lean`). For the **global smoothness** of `exp_p` (do Carmo Ch. 7,
Hadamard) one needs the composed chart-chain map `F₀` — which computes the time-`1`
geodesic endpoint from the initial chart state — to be `C^∞`, together with its
neighbourhood endpoint semantics. The strict-derivative version instead tracks the
Jacobi variational transport, which is unnecessary here.

Because `ContDiffAt` composes natively (`ContDiffAt.comp`), the composition engine is a
short induction (`contDiffAt_comp_chain_nbhd`) rather than the bespoke derivative-gluing
machinery of the C¹ chain. The two building blocks assembled here are:

* `contDiffAt_stateTransition` — the chart-junction state transition
  `(x, w) ↦ (τ(x), (Dτ)(x) w)` is `C^∞` at every state over the chart overlap (`τ` is
  `C^∞`, so its position part and the fibre-application of `Dτ` are `C^∞`);
* the `C^∞` per-piece flow-step endpoint maps of `exists_geodesic_flowstep_partition_contDiff`.

`exists_geodesic_contDiff_chain_nbhd` composes them along a compact geodesic `γ` and
exposes both the `C^∞` regularity of `F₀` at `γ`'s initial chart state and the endpoint
semantics: for every geodesic `c` whose initial state is near that of `γ`, `F₀` reads off
`c`'s chart state at time `1`. Fed `c = γ_{v'}`, the endpoint is `φ_ζ(exp_p v')` — the form
in which the smoothness of `exp_p` is read.

Blueprint: `thm:dc-ch7-3-1`, `lem:dc-ch7-3-2`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic

/-! ### The abstract `C^∞` composition engine -/

section CompChain

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Eng.** The `k`-fold left composite `f (k-1) ∘ ⋯ ∘ f 0` of a family of maps. -/
private def compChainCD (f : ℕ → F → F) : ℕ → F → F
  | 0 => id
  | k + 1 => f k ∘ compChainCD f k

/-- **Math.** **`C^∞` composition engine.** A finite chain of maps `f 0, …, f (n-1)`,
each `C^∞` at a base point `x i` with the base points chaining (`f i (x i) = x (i+1)`),
composes to a map `F₀` that is `C^∞` at `x 0`, sends `x 0` to `x n`, and, on a
neighbourhood `W₀`, has orbit semantics: every `z ∈ W₀` has an orbit `orb` with
`orb 0 = z`, `orb (i+1) = f i (orb i)` (each `orb i ∈ W i`), and `F₀ z = orb n`.

The `C^∞` analogue of `hasStrictFDerivAt_comp_chain_nbhd`; native `ContDiffAt.comp`
replaces the bespoke derivative gluing. -/
theorem contDiffAt_comp_chain_nbhd {n : ℕ} (f : ℕ → F → F) (x : ℕ → F) (W : ℕ → Set F)
    (hf : ∀ i < n, ContDiffAt ℝ ∞ (f i) (x i))
    (hstep : ∀ i < n, f i (x i) = x (i + 1))
    (hW : ∀ i < n, W i ∈ 𝓝 (x i)) :
    ∃ (F₀ : F → F) (W₀ : Set F),
      ContDiffAt ℝ ∞ F₀ (x 0) ∧ F₀ (x 0) = x n ∧ W₀ ∈ 𝓝 (x 0) ∧
      (∀ z ∈ W₀, ∃ orb : ℕ → F, orb 0 = z ∧
        (∀ i < n, orb i ∈ W i ∧ f i (orb i) = orb (i + 1)) ∧ F₀ z = orb n) := by
  classical
  have hcore : ∀ k, k ≤ n →
      ContDiffAt ℝ ∞ (compChainCD f k) (x 0) ∧ compChainCD f k (x 0) = x k := by
    intro k
    induction k with
    | zero => intro _; exact ⟨contDiffAt_id, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨hcd, hbase⟩ := ih (Nat.le_of_succ_le hk)
      have houter : ContDiffAt ℝ ∞ (f k) (compChainCD f k (x 0)) := by
        rw [hbase]; exact hf k hk
      refine ⟨houter.comp (x 0) hcd, ?_⟩
      show f k (compChainCD f k (x 0)) = x (k + 1)
      rw [hbase]; exact hstep k hk
  set W₀ : Set F := ⋂ i : Fin n, (compChainCD f (i : ℕ)) ⁻¹' (W (i : ℕ)) with hW₀def
  have hW₀ : W₀ ∈ 𝓝 (x 0) := by
    rw [hW₀def]
    refine Filter.iInter_mem.2 (fun i => ?_)
    have hi : (i : ℕ) < n := i.2
    have hcont : ContinuousAt (compChainCD f (i : ℕ)) (x 0) :=
      ((hcore (i : ℕ) hi.le).1).continuousAt
    exact hcont.preimage_mem_nhds (by rw [(hcore (i : ℕ) hi.le).2]; exact hW (i : ℕ) hi)
  refine ⟨compChainCD f n, W₀, (hcore n le_rfl).1, (hcore n le_rfl).2, hW₀, ?_⟩
  intro z hz
  refine ⟨fun i => compChainCD f i z, rfl, fun i hi => ⟨?_, rfl⟩, rfl⟩
  have hz' : z ∈ ⋂ i : Fin n, (compChainCD f (i : ℕ)) ⁻¹' (W (i : ℕ)) := by
    rw [hW₀def] at hz; exact hz
  exact Set.mem_iInter.1 hz' ⟨i, hi⟩

end CompChain

/-! ### The chart-junction state transition is `C^∞` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **The chart-junction state transition is `C^∞`.** At a common foot `x` of
the charts at `β` and `β'` and any velocity `udot`, the state transition
`(x, w) ↦ (τ(x), (Dτ)(x) w)` is `C^∞` at the `β`-state `(φ_β(x), udot)`. The position
part is `C^∞` since `τ = chartTransition β β'` is; the velocity part
`z ↦ (Dτ)(z.1) z.2` is `C^∞` since `z.1 ↦ (Dτ)(z.1)` is (`τ` is `C^∞`, so its Fréchet
derivative is `C^∞`) and continuous-linear application is `C^∞`. -/
theorem contDiffAt_stateTransition (β β' : M) {x : M}
    (hxβ : x ∈ (chartAt H β).source) (hxβ' : x ∈ (chartAt H β').source) (udot : E) :
    ContDiffAt ℝ ∞ (stateTransition (I := I) β β') (extChartAt I β x, udot) := by
  set y : E := extChartAt I β x with hy_def
  have hy : y ∈ chartTransitionSource (I := I) (M := M) β β' :=
    extChartAt_mem_chartTransitionSource (I := I) hxβ hxβ'
  have hφc : ContDiffAt ℝ ∞ (chartTransition (I := I) β β') y :=
    contDiffAt_chartTransition (I := I) hy
  have hfst : ContDiffAt ℝ ∞ (Prod.fst : E × E → E) (y, udot) := contDiffAt_fst
  have hsnd : ContDiffAt ℝ ∞ (Prod.snd : E × E → E) (y, udot) := contDiffAt_snd
  -- position component: `z ↦ τ(z.1)`
  have hpos := hφc.comp (y, udot) hfst
  -- the Fréchet derivative of `τ` is `C^∞` at `y`, so `z ↦ (Dτ)(z.1)` is `C^∞`
  have hdφ : ContDiffAt ℝ ∞ (fderiv ℝ (chartTransition (I := I) β β')) y :=
    hφc.fderiv_right (by simp)
  have hvel1 := hdφ.comp (y, udot) hfst
  -- velocity component: `z ↦ (Dτ)(z.1) z.2`
  have hvel := hvel1.clm_apply hsnd
  show ContDiffAt ℝ ∞ (fun z : E × E =>
    (chartTransition (I := I) β β' z.1,
      fderiv ℝ (chartTransition (I := I) β β') z.1 z.2)) (y, udot)
  exact ContDiffAt.prodMk hpos hvel

/-! ### The `C^∞` geodesic-flow chain -/

variable [SigmaCompactSpace M] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
/-- **Math.** **The geodesic-flow chain is `C^∞` and computes nearby geodesic endpoints.**
Let `γ` be a geodesic on an open set `U ⊇ [0,1]`. Then there are a starting chart `α ∋ γ 0`,
a terminal chart `ζ ∋ γ 1`, a map `F₀ : E × E → E × E` that is `C^∞` at the chart-`α` state
of `γ` at time `0`, sends that state to the chart-`ζ` state at time `1`, and a neighbourhood
`W₀` of the initial state on which `F₀` has geodesic-endpoint semantics:

for every `z ∈ W₀` and every geodesic `c : ℝ → M` defined on all of `ℝ` whose foot at time
`0` lies in the source of the chart at `α` and whose chart-`α` state at time `0` is `z`,
`F₀ z = (φ_ζ (c 1), (φ_ζ ∘ c)' (1))`.

So `F₀`, read in charts, *is* the `C^∞` time-one geodesic endpoint map on a neighbourhood
of `γ`'s initial state — the regularity that globalizes the smoothness of `exp_p`.

The `C^∞` companion of `exists_geodesic_jacobiTransport_chain_nbhd`.

Blueprint: `thm:dc-ch7-3-1`. -/
theorem exists_geodesic_contDiff_chain_nbhd
    (g : RiemannianMetric I M) {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hsub : Icc (0 : ℝ) 1 ⊆ U) (hgeo : IsGeodesicOn (I := I) g γ U)
    (hcont : ContinuousOn γ U) :
    ∃ (α ζ : M) (F₀ : E × E → E × E) (W₀ : Set (E × E)),
      γ 0 ∈ (chartAt H α).source ∧ γ 1 ∈ (chartAt H ζ).source ∧
      ContDiffAt ℝ ∞ F₀
          (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0) ∧
        F₀ (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0)
          = (extChartAt I ζ (γ 1), deriv (fun s => extChartAt I ζ (γ s)) 1) ∧
        W₀ ∈ 𝓝 (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0) ∧
        (∀ z ∈ W₀, ∀ c : ℝ → M, Continuous c → IsGeodesic (I := I) g c →
          c 0 ∈ (chartAt H α).source →
          (extChartAt I α (c 0), deriv (fun t => extChartAt I α (c t)) 0) = z →
          F₀ z = (extChartAt I ζ (c 1), deriv (fun t => extChartAt I ζ (c t)) 1) ∧
            c 1 ∈ (chartAt H ζ).source) := by
  classical
  obtain ⟨τ, β, n, flowEnd, Wnb, mwin, hτ0, hτn, hmono, hτIcc, hsrcL, hsrcR, hpiece⟩ :=
    exists_geodesic_flowstep_partition_contDiff (I := I) g hU hsub hgeo hcont
  have hτ1 : τ n = 1 := hτn n le_rfl
  have hcontAt : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ t := fun t ht =>
    hcont.continuousAt (hU.mem_nhds (hsub ht))
  set x : ℕ → E × E := fun i =>
    (extChartAt I (β i) (γ (τ i)), deriv (fun s => extChartAt I (β i) (γ s)) (τ i)) with hxdef
  set flowPart : ℕ → (E × E → E × E) := fun i =>
    if τ i = τ (i + 1) then id else flowEnd i with hflowPartdef
  set f : ℕ → (E × E → E × E) := fun i =>
    stateTransition (I := I) (β i) (β (i + 1)) ∘ flowPart i with hfdef
  -- the flow part maps the chart state at `τ i` to the chart state at `τ (i+1)`
  have hfpt : ∀ i, flowPart i (x i)
      = (extChartAt I (β i) (γ (τ (i + 1))),
          deriv (fun s => extChartAt I (β i) (γ s)) (τ (i + 1))) := by
    intro i
    simp only [hflowPartdef]
    split_ifs with h
    · simp only [id_eq, hxdef]; rw [h]
    · exact (hpiece i).2.1
  have hflowcd : ∀ i, ContDiffAt ℝ ∞ (flowPart i) (x i) := by
    intro i
    simp only [hflowPartdef]
    split_ifs with h
    · exact contDiffAt_id
    · exact (hpiece i).1
  -- the chart junction carries `γ`'s chart state onward at every boundary (mirrors the
  -- strict chain's `hjuncdata`; the extra Jacobi/derivative data is discarded)
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
  -- the chart junction is `C^∞` at the flowed state
  have hjunccd : ∀ i, ContDiffAt ℝ ∞ (stateTransition (I := I) (β i) (β (i + 1)))
      (flowPart i (x i)) := by
    intro i
    rw [hfpt i]
    exact contDiffAt_stateTransition (I := I) (β i) (β (i + 1)) (hsrcR i) (hsrcL (i + 1)) _
  have hf : ∀ i < n, ContDiffAt ℝ ∞ (f i) (x i) := by
    intro i _
    exact (hjunccd i).comp (x i) (hflowcd i)
  have hstep : ∀ i < n, f i (x i) = x (i + 1) := by
    intro i _
    show stateTransition (I := I) (β i) (β (i + 1)) (flowPart i (x i)) = x (i + 1)
    rw [hfpt i]
    exact (hjunc i).2.1
  -- **the shrunk windows**: also require the flowed foot to land in the *next* chart
  set foot : ℕ → (E × E → M) := fun i q => (extChartAt I (β i)).symm q.1 with hfootdef
  set W : ℕ → Set (E × E) := fun i =>
    Wnb i ∩ (flowPart i) ⁻¹' ((foot i) ⁻¹' (chartAt H (β (i + 1))).source) with hWdef
  have hW : ∀ i, W i ∈ 𝓝 (x i) := by
    intro i
    refine Filter.inter_mem ((hpiece i).2.2.2.2.1) ?_
    refine ((hflowcd i).continuousAt).preimage_mem_nhds ?_
    rw [hfpt i]
    have hsrcE : γ (τ (i + 1)) ∈ (extChartAt I (β i)).source := by
      rw [extChartAt_source]; exact hsrcR i
    have hfootcont : ContinuousAt (foot i)
        (extChartAt I (β i) (γ (τ (i + 1))),
          deriv (fun s => extChartAt I (β i) (γ s)) (τ (i + 1))) :=
      (continuousAt_extChartAt_symm' (I := I) hsrcE).comp_of_eq continuousAt_fst rfl
    refine hfootcont.preimage_mem_nhds ?_
    have hfooty : foot i
        (extChartAt I (β i) (γ (τ (i + 1))),
          deriv (fun s => extChartAt I (β i) (γ s)) (τ (i + 1)))
        = γ (τ (i + 1)) := (extChartAt I (β i)).left_inv hsrcE
    rw [hfooty]
    exact (chartAt H (β (i + 1))).open_source.mem_nhds (hsrcL (i + 1))
  -- assemble the chain with neighbourhood semantics
  obtain ⟨F₀, W₀, hcd, hbase, hW₀, horbit⟩ :=
    contDiffAt_comp_chain_nbhd (n := n) f x W hf hstep (fun i _ => hW i)
  have hx0 : x 0
      = (extChartAt I (β 0) (γ 0), deriv (fun s => extChartAt I (β 0) (γ s)) 0) := by
    simp only [hxdef, hτ0]
  have hxn : x n
      = (extChartAt I (β n) (γ 1), deriv (fun s => extChartAt I (β n) (γ s)) 1) := by
    simp only [hxdef, hτ1]
  refine ⟨β 0, β n, F₀, W₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hsrcL 0; rwa [hτ0] at this
  · have := hsrcL n; rwa [hτ1] at this
  · rw [← hx0]; exact hcd
  · rw [← hx0, ← hxn]; exact hbase
  · rw [← hx0]; exact hW₀
  · -- **the nearby-state endpoint semantics**: the orbit induction
    intro z hz c hccont hcgeo hc0src hcz
    obtain ⟨orb, horb0, horbstep, horbend⟩ := horbit z hz
    have hcgeoOn : IsGeodesicOn (I := I) g c univ := fun t _ => hcgeo t
    -- along the orbit, `orb i` is the chart-`β i` state of `c` at `τ i`
    have key : ∀ i ≤ n,
        orb i = (extChartAt I (β i) (c (τ i)),
            deriv (fun t => extChartAt I (β i) (c t)) (τ i)) ∧
          c (τ i) ∈ (chartAt H (β i)).source := by
      intro i
      induction i with
      | zero =>
        intro _
        refine ⟨?_, ?_⟩
        · rw [horb0, ← hcz, hτ0]
        · rw [hτ0]; exact hc0src
      | succ i ih =>
        intro hi
        have hi' : i < n := hi
        obtain ⟨ihstate, ihsrc⟩ := ih (Nat.le_of_succ_le hi)
        obtain ⟨horbW, horbf⟩ := horbstep i hi'
        have hflowc : flowPart i (orb i)
              = (extChartAt I (β i) (c (τ (i + 1))),
                  deriv (fun t => extChartAt I (β i) (c t)) (τ (i + 1))) ∧
            c (τ (i + 1)) ∈ (chartAt H (β i)).source := by
          by_cases hdeg : τ i = τ (i + 1)
          · refine ⟨?_, ?_⟩
            · have : flowPart i (orb i) = orb i := by
                simp only [hflowPartdef]; rw [if_pos hdeg]; rfl
              rw [this, ihstate, hdeg]
            · rw [← hdeg]; exact ihsrc
          · have hflowEq : flowPart i (orb i) = flowEnd i (orb i) := by
              simp only [hflowPartdef]; rw [if_neg hdeg]
            obtain ⟨c', hc'geo, hc'cont, hc'src, hc'state, hc'end⟩ :=
              (hpiece i).2.2.2.2.2 (orb i) horbW.1
            have hmpos : 0 < mwin i := (hpiece i).2.2.1
            have hτiS : τ i ∈ Ioo (τ i - mwin i) (τ i + mwin i) :=
              ⟨by linarith, by linarith⟩
            have hτi1S : τ (i + 1) ∈ Ioo (τ i - mwin i) (τ i + mwin i) :=
              (hpiece i).2.2.2.1
            have hstateEq : (extChartAt I (β i) (c' (τ i)),
                deriv (fun t => extChartAt I (β i) (c' t)) (τ i))
                = (extChartAt I (β i) (c (τ i)),
                    deriv (fun t => extChartAt I (β i) (c t)) (τ i)) := by
              rw [hc'state, ihstate]
            have hfst := congrArg Prod.fst hstateEq
            have hsnd := congrArg Prod.snd hstateEq
            simp only at hfst hsnd
            have hcsrcE : c (τ i) ∈ (extChartAt I (β i)).source := by
              rw [extChartAt_source]; exact ihsrc
            have hc'srcE : c' (τ i) ∈ (extChartAt I (β i)).source := by
              rw [extChartAt_source]; exact hc'src (τ i) hτiS
            have hpos : c (τ i) = c' (τ i) :=
              (extChartAt I (β i)).injOn hcsrcE hc'srcE hfst.symm
            have hceq : Set.EqOn c c' (Ioo (τ i - mwin i) (τ i + mwin i)) :=
              IsGeodesicOn.eqOn_of_deriv_chartReading_eq (β := β i) isOpen_Ioo
                isPreconnected_Ioo (fun t _ => hcgeo t) hc'geo
                hccont.continuousOn hc'cont hτiS hpos ihsrc hsnd.symm
            have hcc' : c (τ (i + 1)) = c' (τ (i + 1)) := hceq hτi1S
            have hev : (fun t => extChartAt I (β i) (c t))
                =ᶠ[𝓝 (τ (i + 1))] (fun t => extChartAt I (β i) (c' t)) := by
              filter_upwards [isOpen_Ioo.mem_nhds hτi1S] with t ht
              rw [hceq ht]
            refine ⟨?_, ?_⟩
            · rw [hflowEq, hc'end, hcc', hev.deriv_eq]
            · rw [hcc']; exact hc'src (τ (i + 1)) hτi1S
        obtain ⟨hflowstate, hfootsrc⟩ := hflowc
        have hnextsrc : c (τ (i + 1)) ∈ (chartAt H (β (i + 1))).source := by
          have hmem : foot i (flowPart i (orb i)) ∈ (chartAt H (β (i + 1))).source :=
            horbW.2
          rw [hflowstate] at hmem
          have hfootc : foot i
              (extChartAt I (β i) (c (τ (i + 1))),
                deriv (fun t => extChartAt I (β i) (c t)) (τ (i + 1)))
              = c (τ (i + 1)) :=
            (extChartAt I (β i)).left_inv (by rw [extChartAt_source]; exact hfootsrc)
          rwa [hfootc] at hmem
        refine ⟨?_, hnextsrc⟩
        rw [← horbf]
        show stateTransition (I := I) (β i) (β (i + 1)) (flowPart i (orb i)) = _
        rw [hflowstate]
        exact stateTransition_chartState (I := I) g hcgeoOn (mem_univ (τ (i + 1)))
          hccont.continuousAt hfootsrc hnextsrc
    obtain ⟨hkeyn, hkeynsrc⟩ := key n le_rfl
    rw [hτ1] at hkeynsrc
    exact ⟨by rw [horbend, hkeyn, hτ1], hkeynsrc⟩

end Riemannian.Jacobi

end
