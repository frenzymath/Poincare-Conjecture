import PoincareLib.Ch02.GeodesicContinuousDependence
import PoincareLib.Ch02.GeodesicLimits

/-!
# Morgan–Tian Ch. 2 — limits of minimizing geodesics (tangent-bundle version)

Blueprint `lem:limit-of-minimizing-geodesics`.  Let `(M, g)` be a complete
Riemannian manifold (ambient distance = the Riemannian distance of `g`), let
`I ⊆ ℝ` be an interval containing `0`, and let `In k ⊆ ℝ` be windows exhausting
`I` (every compact subset of `I` lies in `In k` for all large `k`).  Suppose the
`γs k : ℝ → M` are **unit-speed minimizing geodesics**: each is a geodesic of `g`
(`IsGeodesic`, continuous) with unit conserved speed (`speedSq g (γs k) 0 = 1`)
and minimizing on its window (`IsMinGeodesicOn (γs k) (In k)`), and the initial
points `γs k 0` converge to `p`.  Then, after passing to a subsequence, the
`γs k` converge to a unit-speed minimizing geodesic `γ : ℝ → M` with `γ 0 = p`,
*uniformly on every compact time interval*, and their initial data converge in
the tangent bundle: `(γs k 0, γs k '(0)) → (γ 0, γ'(0))`.

The engine is `lem:geodesic-continuous-dependence`
(`GeodesicContinuousDependence.lean`).  The one genuinely new ingredient is
**Step 1**: extract a convergent subsequence of initial *velocities*.  The chart
velocities `ξ k = (φ_p ∘ γs k)'(0)` are bounded — the conserved unit speed
controls them through the local coordinate-norm/Gram estimate
`exists_sq_norm_deriv_le_speedSq` (`‖ξ k‖² ≤ c · speedSq g (γs k) 0 = c`) once
`γs k 0` is near `p` — so Bolzano–Weierstrass on a closed ball of the
finite-dimensional model `E` (`IsCompact.tendsto_subseq`) yields a subsequence
`ξ (φ ·) → x`.  The geodesic `γ` with initial chart velocity `x` at `p`
(`exists_globalGeodesic_initial`) is then the limit: the convergence invariant
`Riemannian.Geodesic.ConvAt g γ (γs ∘ φ) 0` holds at time `0` by construction,
and the continuous-dependence machinery propagates it (`convAt_of_convAt_zero`,
`tendsto_apply_of_convAt_zero`, `tendstoUniformlyOn_of_convAt_zero`).  Minimality
of `γ` on `I` passes to the limit from `IsMinGeodesicOn (γs (φ ·)) (In (φ ·))`
by continuity of the distance and pointwise convergence.

Only the ambient formulation with *global* geodesics `γs k : ℝ → M` is used here;
the blueprint's preliminary extension of window-geodesics to global ones (its
appeal to `lem:geodesic-continuous-dependence`(1)) is folded into the hypotheses.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.1–2.2.
-/

open Set Filter Metric Riemannian Riemannian.Geodesic Riemannian.Exponential
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]

/-- **Math.** **Limits of minimizing geodesics, tangent-bundle version**
(blueprint `lem:limit-of-minimizing-geodesics`).  On a complete Riemannian
manifold, a sequence of unit-speed minimizing geodesics `γs k` on windows `In k`
exhausting an interval `I ∋ 0`, with initial points converging to `p`,
subconverges to a unit-speed minimizing geodesic `γ` on `I` with `γ 0 = p`:
uniformly on every compact interval `[-T, T]`, and in the tangent bundle at time
`0` (the invariant `ConvAt g γ (γs ∘ φ) 0`, i.e. `(γs k 0, γs k '(0)) → (p,
γ'(0))`). -/
theorem exists_isMinGeodesicOn_convAt_of_tendsto (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M]
    {I₀ : Set ℝ} (hI₀ : I₀.OrdConnected)
    {In : ℕ → Set ℝ} {γs : ℕ → ℝ → M}
    (hgeo : ∀ k, IsGeodesic (I := I) g (γs k)) (hc : ∀ k, Continuous (γs k))
    (hspeed : ∀ k, speedSq (I := I) g (γs k) 0 = 1)
    (hmin : ∀ k, IsMinGeodesicOn (γs k) (In k))
    (hexh : ∀ J : Set ℝ, IsCompact J → J ⊆ I₀ → ∀ᶠ k in atTop, J ⊆ In k)
    {p : M} (hp : Tendsto (fun k => γs k 0) atTop (𝓝 p)) :
    ∃ (φ : ℕ → ℕ) (γ : ℝ → M),
      StrictMono φ ∧ IsGeodesic (I := I) g γ ∧ Continuous γ ∧ γ 0 = p ∧
      IsMinGeodesicOn γ I₀ ∧
      ConvAt (I := I) g γ (fun j => γs (φ j)) 0 ∧
      ∀ T : ℝ, TendstoUniformlyOn (fun j => γs (φ j)) γ atTop (Icc (-T) T) := by
  classical
  -- Local coordinate-velocity bound near `p` (constant `c`, neighbourhood `V`).
  obtain ⟨c, V, hcpos, hVnhds, -, hbound⟩ :=
    exists_sq_norm_deriv_le_speedSq (I := I) g p
  -- Eventually `γs k 0` lies in the chart source of `p` and reads into `V`.
  have hsrcEv : ∀ᶠ k in atTop, γs k 0 ∈ (chartAt H p).source :=
    hp.eventually ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
  have hVEv : ∀ᶠ k in atTop, extChartAt I p (γs k 0) ∈ V :=
    ((continuousAt_extChartAt p).tendsto.comp hp).eventually hVnhds
  -- Step 1a: the chart velocities `ξ k = (φ_p ∘ γs k)'(0)` are eventually `≤ √c`.
  have hboundEv : ∀ᶠ k in atTop,
      ‖deriv (fun τ => extChartAt I p (γs k τ)) 0‖ ≤ Real.sqrt c := by
    filter_upwards [hsrcEv, hVEv] with k hsrc hVmem
    have hHD : HasDerivAt (fun τ => extChartAt I p (γs k τ))
        (deriv (fun τ => extChartAt I p (γs k τ)) 0) 0 :=
      ((hgeo k).hasGeodesicEquationAt 0).hasDerivAt_extChartAt_deriv
        (hc k).continuousAt hsrc
    have hb := hbound (hc k).continuousAt hsrc hVmem hHD
    rw [hspeed k, mul_one] at hb
    have hsq := Real.sqrt_le_sqrt hb
    rwa [Real.sqrt_sq (norm_nonneg _)] at hsq
  rw [eventually_atTop] at hboundEv
  obtain ⟨N, hN⟩ := hboundEv
  -- Step 1b: Bolzano–Weierstrass on the closed `√c`-ball of the model `E`.
  have hKcpt : IsCompact (Metric.closedBall (0 : E) (Real.sqrt c)) :=
    isCompact_closedBall _ _
  have hmemK : ∀ j : ℕ,
      deriv (fun τ => extChartAt I p (γs (j + N) τ)) 0 ∈
        Metric.closedBall (0 : E) (Real.sqrt c) := fun j =>
    mem_closedBall_zero_iff.mpr (hN (j + N) (Nat.le_add_left N j))
  obtain ⟨x, -, ψ, hψ, hconv⟩ := hKcpt.tendsto_subseq hmemK
  -- The reindexing subsequence `φ = ψ · + N`.
  have hφmono : StrictMono (fun j => ψ j + N) := fun _ _ hab =>
    Nat.add_lt_add_right (hψ hab) N
  have hφat : Tendsto (fun j => ψ j + N) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_add_right (ψ j) N) hψ.tendsto_atTop
  have hφpos : Tendsto (fun j => γs (ψ j + N) 0) atTop (𝓝 p) := hp.comp hφat
  -- Step 2: the candidate limit geodesic `γ` with initial chart velocity `x`.
  obtain ⟨γ, hγ0, hγHD, hγcont, hγgeo⟩ :=
    exists_globalGeodesic_initial (I := I) g hg p x
  set γs' : ℕ → ℝ → M := fun j => γs (ψ j + N) with hγs'
  have hgeoφ : ∀ n, IsGeodesic (I := I) g (γs' n) := fun n => hgeo (ψ n + N)
  have hcφ : ∀ n, Continuous (γs' n) := fun n => hc (ψ n + N)
  -- Step 3: the convergence invariant holds at time `0`.
  have hConv : ConvAt (I := I) g γ γs' 0 := by
    refine ⟨?_, ?_⟩
    · show Tendsto (fun n => γs (ψ n + N) 0) atTop (𝓝 (γ 0))
      rw [hγ0]; exact hφpos
    · show Tendsto (fun n => deriv (fun τ => extChartAt I (γ 0) (γs (ψ n + N) τ)) 0)
        atTop (𝓝 (deriv (fun τ => extChartAt I (γ 0) (γ τ)) 0))
      simp only [hγ0]
      rw [hγHD.deriv]
      exact hconv
  -- Step 5: minimality of `γ` on `I₀` passes to the limit.
  have hγmin : IsMinGeodesicOn γ I₀ := by
    intro s hs t ht
    have hsP : Tendsto (fun n => γs' n s) atTop (𝓝 (γ s)) :=
      tendsto_apply_of_convAt_zero (I := I) g hγgeo hγcont hgeoφ hcφ hConv s
    have htP : Tendsto (fun n => γs' n t) atTop (𝓝 (γ t)) :=
      tendsto_apply_of_convAt_zero (I := I) g hγgeo hγcont hgeoφ hcφ hConv t
    have hdist : Tendsto (fun n => dist (γs' n s) (γs' n t)) atTop
        (𝓝 (dist (γ s) (γ t))) := hsP.dist htP
    -- The endpoints eventually lie in a common window, where the distance is `|s - t|`.
    have hsmem : min s t ∈ I₀ := by
      rcases le_total s t with h | h
      · rwa [min_eq_left h]
      · rwa [min_eq_right h]
    have htmem : max s t ∈ I₀ := by
      rcases le_total s t with h | h
      · rwa [max_eq_right h]
      · rwa [max_eq_left h]
    have hJsub : Icc (min s t) (max s t) ⊆ I₀ := hI₀.out hsmem htmem
    have hev : ∀ᶠ n in atTop, Icc (min s t) (max s t) ⊆ In (ψ n + N) :=
      hφat.eventually (hexh _ isCompact_Icc hJsub)
    have hconst : ∀ᶠ n in atTop, dist (γs' n s) (γs' n t) = |s - t| := by
      filter_upwards [hev] with n hn
      exact hmin (ψ n + N) (hn ⟨min_le_left s t, le_max_left s t⟩)
        (hn ⟨min_le_right s t, le_max_right s t⟩)
    have hconstT : Tendsto (fun n => dist (γs' n s) (γs' n t)) atTop (𝓝 |s - t|) :=
      Tendsto.congr' (hconst.mono fun n h => h.symm) tendsto_const_nhds
    exact tendsto_nhds_unique hdist hconstT
  -- Step 4: assemble, with uniform convergence from `tendstoUniformlyOn_of_convAt_zero`.
  refine ⟨fun j => ψ j + N, γ, hφmono, hγgeo, hγcont, hγ0, hγmin, hConv, fun T => ?_⟩
  exact tendstoUniformlyOn_of_convAt_zero (I := I) g hg hγcont hγgeo hcφ hgeoφ hConv T

end PoincareLib

end
