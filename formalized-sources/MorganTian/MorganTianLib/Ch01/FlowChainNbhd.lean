import MorganTianLib.Ch01.FlowChainAssembly
import MorganTianLib.Ch01.GeodesicOfState

/-!
# Poincaré Ch. 1, §1.4 — the flow chain computes *nearby* geodesic endpoints

`exists_geodesic_jacobiTransport_chain` (`FlowChainAssembly`) builds, along a
compact geodesic `γ : [0,1] → M`, a composed map `F₀` strictly differentiable at
the initial chart state of `γ`, whose derivative `D₀` transports the Jacobi
variational pair from time `0` to time `1`. Its endpoint identity, however, pins
`F₀` down at the **single** state of `γ`:

  `F₀ (chart-α state of γ at 0) = (chart-ζ state of γ at 1)`.

That is not enough to read `d(exp_p)_v` off `D₀`: the differential of `exp_p` is a
derivative *in `v`*, hence a statement about a whole neighbourhood of `v`. We need
`F₀` to compute the time-`1` endpoint of the geodesic emanating from **every**
initial state near that of `γ`.

This file supplies exactly that (**rung 4**, step 1–2). `exists_geodesic_flowstep_partition`
already exports, per piece `i`, a neighbourhood `Wnb i` of the chart-`β i` state of
`γ` at `τ i` on which `flowEnd i` is the time-`τ (i+1)` chart state of a *local*
geodesic emanating from the given state; `hasStrictFDerivAt_comp_chain_nbhd` already
intersects those into a single `W₀ ∈ 𝓝` of the initial state and exposes the **orbit**
of each nearby `z`. Two things were still missing, and are done here.

* **Shrinking the windows.** The chart junction `stateTransition (β i) (β (i+1))`
  reads a state at `τ (i+1)` only when the foot lies in *both* chart sources. For the
  reference geodesic `γ` that is the partition's `hsrcR`/`hsrcL`; for a *nearby*
  geodesic it is not automatic. We shrink `Wnb i` to
  `W i = Wnb i ∩ (flowPart i)⁻¹' (foot⁻¹' (chartAt (β (i+1))).source)`, still a
  neighbourhood of the base state because `flowPart i` is continuous there (it is
  strictly differentiable), the chart inverse is continuous at the image point, and
  `γ (τ (i+1))` does lie in the open set `(chartAt (β (i+1))).source`.

* **The orbit induction, by uniqueness rather than gluing.** Each piece hands back
  its *own* local geodesic. Instead of gluing them along an sSup walk, we let a single
  *global* geodesic `c` — supplied by the caller, and on a complete manifold produced by
  `exists_geodesic_chartState` — absorb them all: on the piece's open time window the
  local geodesic and `c` share a chart state, so DoCarmoLib's intrinsic uniqueness
  (`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) identifies them there. The induction
  `orb i = (chart-β i state of c at τ i)` then runs link by link, the junctions being
  served by `stateTransition_chartState`, which quantifies over an arbitrary geodesic.

* `exists_geodesic_jacobiTransport_chain_nbhd` — the chain, plus: for every `z` in a
  neighbourhood `W₀` of `γ`'s initial chart-`α` state and **every** global geodesic `c`
  whose chart-`α` state at time `0` is `z`, `F₀ z` is the chart-`ζ` state of `c` at
  time `1`.

Fed the geodesic `c = γ_{v+sZ}` (which starts at `p = γ 0`, so the chart hypothesis
`c 0 ∈ (chartAt H α).source` is free), the endpoint reads `φ_ζ (exp_p (v + sZ))` —
the form in which rung 4 differentiates in `v`.

Note the theorem needs **no** completeness hypothesis: `c` is universally quantified,
so only *uniqueness* of geodesics is used, never their existence. Completeness enters
only at the call site, where Hopf–Rinow produces `c`.

Blueprint: `lem:exponential-differential-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M]

/-- **Math.** **The geodesic-flow chain computes nearby geodesic endpoints.**
Let `γ` be a geodesic on an open set `U ⊇ [0,1]`. Then, besides all the data of
`exists_geodesic_jacobiTransport_chain` (a starting chart `α ∋ γ 0`, a terminal chart
`ζ ∋ γ 1`, a map `F₀` strictly differentiable at the chart-`α` state of `γ` at time `0`
with derivative `D₀`, carrying it to the chart-`ζ` state at time `1`, and transporting
every manifold Jacobi variational pair from `0` to `1`), there is a neighbourhood `W₀`
of that initial state on which `F₀` has *geodesic endpoint semantics*:

for every `z ∈ W₀` and every geodesic `c : ℝ → M` defined on all of `ℝ` whose foot at
time `0` lies in the source of the chart at `α` and whose chart-`α` state at time `0`
is `z`, one has

  `F₀ z = (φ_ζ (c 1), (φ_ζ ∘ c)' (1))`.

So `F₀`, read in charts, *is* the time-one geodesic endpoint map on a neighbourhood of
`γ`'s initial state — which is what makes `D₀` a derivative of `exp_p`, and not merely a
transport along the single geodesic `γ`.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem exists_geodesic_jacobiTransport_chain_nbhd
    (g : RiemannianMetric I M) {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hsub : Icc (0 : ℝ) 1 ⊆ U) (hgeo : IsGeodesicOn (I := I) g γ U)
    (hcont : ContinuousOn γ U) :
    ∃ (α ζ : M) (F₀ : E × E → E × E) (D₀ : (E × E) →L[ℝ] E × E) (W₀ : Set (E × E)),
      γ 0 ∈ (chartAt H α).source ∧ γ 1 ∈ (chartAt H ζ).source ∧
      HasStrictFDerivAt F₀ D₀
          (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0) ∧
        F₀ (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0)
          = (extChartAt I ζ (γ 1), deriv (fun s => extChartAt I ζ (γ s)) 1) ∧
        W₀ ∈ 𝓝 (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0) ∧
        (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ 0 1 →
          D₀ (jacobiVarPair (I := I) g α γ J DJ 0)
            = jacobiVarPair (I := I) g ζ γ J DJ 1) ∧
        (∀ z ∈ W₀, ∀ c : ℝ → M, Continuous c → IsGeodesic (I := I) g c →
          c 0 ∈ (chartAt H α).source →
          (extChartAt I α (c 0), deriv (fun t => extChartAt I α (c t)) 0) = z →
          F₀ z = (extChartAt I ζ (c 1), deriv (fun t => extChartAt I ζ (c t)) 1)) := by
  classical
  obtain ⟨τ, β, n, flowEnd, Dstep, Wnb, mwin, hτ0, hτn, hmono, hτIcc, hsrcL, hsrcR,
    hpiece⟩ := exists_geodesic_flowstep_partition (I := I) g hU hsub hgeo hcont
  have hτ1 : τ n = 1 := hτn n le_rfl
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
  set x : ℕ → E × E := fun i =>
    (extChartAt I (β i) (γ (τ i)), deriv (fun s => extChartAt I (β i) (γ s)) (τ i)) with hxdef
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
  have hflowstrict : ∀ i, HasStrictFDerivAt (flowPart i) (flowDeriv i) (x i) := by
    intro i
    simp only [hflowPartdef, hflowDerivdef]
    split_ifs with h
    · exact hasStrictFDerivAt_id (x i)
    · exact (hpiece i).1
  have hf : ∀ i < n, HasStrictFDerivAt (f i) (L i) (x i) := by
    intro i _
    have hg : HasStrictFDerivAt (stateTransition (I := I) (β i) (β (i + 1))) (Dtr i)
        (flowPart i (x i)) := by
      rw [hfpt i]; exact (hjunc i).1
    exact hg.comp (x i) (hflowstrict i)
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
    refine Filter.inter_mem ((hpiece i).2.2.2.2.2.1) ?_
    refine ((hflowstrict i).continuousAt).preimage_mem_nhds ?_
    rw [hfpt i]
    -- the chart inverse is continuous at `φ_{β i} (γ (τ (i+1)))` and sends it to `γ (τ (i+1))`
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
  obtain ⟨F₀, D₀, W₀, hderiv, hbase, hW₀, htrans, horbit⟩ :=
    hasStrictFDerivAt_comp_chain_nbhd (n := n) f L x W hf hstep (fun i _ => hW i)
  have hx0 : x 0
      = (extChartAt I (β 0) (γ 0), deriv (fun s => extChartAt I (β 0) (γ s)) 0) := by
    simp only [hxdef, hτ0]
  have hxn : x n
      = (extChartAt I (β n) (γ 1), deriv (fun s => extChartAt I (β n) (γ s)) 1) := by
    simp only [hxdef, hτ1]
  refine ⟨β 0, β n, F₀, D₀, W₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hsrcL 0; rwa [hτ0] at this
  · have := hsrcL n; rwa [hτ1] at this
  · rw [← hx0]; exact hderiv
  · rw [← hx0, ← hxn]; exact hbase
  · rw [← hx0]; exact hW₀
  · -- the Jacobi variational-pair transport (as in `exists_geodesic_jacobiTransport_chain`)
    intro J DJ hJ
    set p : ℕ → E × E := fun i => jacobiVarPair (I := I) g (β i) γ J DJ (τ i) with hpdef
    have hchain : ∀ i < n, L i (p i) = p (i + 1) := by
      intro i _
      simp only [hLdef, ContinuousLinearMap.comp_apply]
      have hflowp : flowDeriv i (p i)
          = jacobiVarPair (I := I) g (β i) γ J DJ (τ (i + 1)) := by
        simp only [hflowDerivdef, hpdef]
        split_ifs with h
        · simp only [ContinuousLinearMap.id_apply]; rw [h]
        · have hlt : τ i < τ (i + 1) := lt_of_le_of_ne (hmono (Nat.le_succ i)) h
          exact (hpiece i).2.2.1 J DJ (hJ.mono (hτIcc i).1 hlt (hτIcc (i + 1)).2)
      rw [hflowp]
      exact (hjunc i).2.2 J DJ
    have := htrans p hchain
    simpa only [hpdef, hτ0, hτ1] using this
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
        -- the flow part of piece `i`, applied to `orb i`, is `c`'s chart state at `τ (i+1)`
        have hflowc : flowPart i (orb i)
              = (extChartAt I (β i) (c (τ (i + 1))),
                  deriv (fun t => extChartAt I (β i) (c t)) (τ (i + 1))) ∧
            c (τ (i + 1)) ∈ (chartAt H (β i)).source := by
          by_cases hdeg : τ i = τ (i + 1)
          · -- degenerate piece: the flow part is the identity
            refine ⟨?_, ?_⟩
            · have : flowPart i (orb i) = orb i := by
                simp only [hflowPartdef]; rw [if_pos hdeg]; rfl
              rw [this, ihstate, hdeg]
            · rw [← hdeg]; exact ihsrc
          · -- nondegenerate piece: use the piece's local geodesic, then uniqueness
            have hflowEq : flowPart i (orb i) = flowEnd i (orb i) := by
              simp only [hflowPartdef]; rw [if_neg hdeg]
            obtain ⟨c', hc'geo, hc'cont, hc'src, hc'state, hc'end⟩ :=
              (hpiece i).2.2.2.2.2.2 (orb i) horbW.1
            have hmpos : 0 < mwin i := (hpiece i).2.2.2.1
            have hτiS : τ i ∈ Ioo (τ i - mwin i) (τ i + mwin i) :=
              ⟨by linarith, by linarith⟩
            have hτi1S : τ (i + 1) ∈ Ioo (τ i - mwin i) (τ i + mwin i) :=
              (hpiece i).2.2.2.2.1
            -- `c` and the piece's local geodesic `c'` share a chart-`β i` state at `τ i`
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
            -- intrinsic uniqueness identifies them on the piece's open time window
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
        -- the shrunk window says the flowed foot lies in the *next* chart source too
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
        -- the junction transports `c`'s chart state, since both feet are in both sources
        refine ⟨?_, hnextsrc⟩
        rw [← horbf]
        show stateTransition (I := I) (β i) (β (i + 1)) (flowPart i (orb i)) = _
        rw [hflowstate]
        exact stateTransition_chartState (I := I) g hcgeoOn (mem_univ (τ (i + 1)))
          hccont.continuousAt hfootsrc hnextsrc
    obtain ⟨hkeyn, _⟩ := key n le_rfl
    rw [horbend, hkeyn, hτ1]

end MorganTianLib

end
