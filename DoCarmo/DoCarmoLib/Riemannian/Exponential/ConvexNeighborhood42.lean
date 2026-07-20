import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhoodStrict

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Convex neighborhoods (do Carmo Ch. 3, §4, Proposition 4.2)

`ConvexNeighborhoodStrict.lean` proves the **strict** form of do Carmo's Lemma 4.1
(`exists_forall_geodesic_tangent_stays_strictly_outside_ball`): a geodesic read off the
geodesic-spray flow `Z`, tangent (`∂F/∂t(0) = 0`, the Gauss lemma) to the geodesic sphere,
stays *strictly* outside the ball in a punctured neighborhood of its base point.

That statement is phrased in terms of the *flow reading* `s ↦ φ_p⁻¹((Z (y, T⁻¹•w)(sT))₁)`
of the strict lemma's own flow `Z`. do Carmo's convex-neighborhood proof needs to apply it to
an **arbitrary** intrinsic geodesic `σ` — in particular the joining geodesic supplied by the
totally-normal neighborhood theorem (`thm:dc-ch3-3-7`), re-based at the interior point where the
distance from `p` to `σ` attains its maximum. The bridge is the **readback**
(`IsGeodesicOn.eq_uniform_flow_readback`): every continuous intrinsic geodesic whose initial
position and chart-`p` velocity are admissible for `Z` *is computed by `Z`*, so its radial
functional coincides with the strict lemma's near `0`. Since the readback consumes only the
generic flow clauses `hflow` (not a specific construction of `Z`), it applies verbatim to the
strict lemma's own `Z`.

This file:

* `exists_forall_intrinsic_geodesic_tangent_strictly_outside_ball` — **the intrinsic strict
  separation** (`lem:dc-ch3-4-2-rebase`): for any continuous intrinsic geodesic `σ` through a base
  point reading into the neighborhood `V`, with admissible nonzero chart velocity, if the radial
  functional `F(s) = |exp_p⁻¹(σ s)|²_p` is tangent at `0` (`deriv F 0 = 0`) then `F 0 < F s` for
  every `s ≠ 0` near `0`. This is the strict lemma re-expressed for genuine intrinsic geodesics,
  the form the convex-neighborhood contradiction consumes.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **Intrinsic strict separation** (do Carmo Ch. 3, §4; the re-based form of the
strict Lemma 4.1). For any `p ∈ M` there are a `C²` exponential inverse `finv`, an open
neighborhood `V` of `φ_p(p)` inside the chart target, and radii `0 < r`, `0 < T < ε`, such that:
for **every** continuous intrinsic geodesic `σ` on an open interval `(-a, a)` (`a > 0`) whose
base point `σ 0` reads into `V` (`φ_p(σ 0) ∈ V`, and `σ 0` lies in the chart at `p`), with
nonzero admissible chart velocity `w = (φ_p ∘ σ)'(0) ≠ 0`
(`(φ_p(σ 0), T⁻¹•w)` in the flow's ball of initial conditions), the radial functional
`F(s) = ⟨exp_p⁻¹(σ s), exp_p⁻¹(σ s)⟩_p` obeys the strict second-derivative dichotomy: if `σ` is
tangent to the geodesic sphere at `0` (`deriv F 0 = 0`, the Gauss lemma), then `F 0 < F s` for
every `s ≠ 0` near `0`.

The proof feeds `σ` into the **readback** `IsGeodesicOn.eq_uniform_flow_readback` for the strict
lemma's own flow `Z`: on the overlap window `σ` coincides with the flow reading
`s ↦ φ_p⁻¹((Z (φ_p(σ 0), T⁻¹•w)(sT))₁)`, so `F` coincides near `0` with the strict lemma's radial
functional and the tangency and strict-separation transfer across the equality. -/
theorem exists_forall_intrinsic_geodesic_tangent_strictly_outside_ball [T2Space M]
    (g : RiemannianMetric I M) (p : M) :
    ∃ (finv : E → E) (V : Set E) (r ε T : ℝ),
      IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      finv (extChartAt I p p) = 0 ∧ 0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∃ εL : ℝ, 0 < εL ∧ ∀ w : E, ‖w‖ < εL →
        finv (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) ∧
      ∀ (σ : ℝ → M) (a : ℝ) (w : E), 0 < a →
        IsGeodesicOn (I := I) g σ (Ioo (-a) a) →
        ContinuousOn σ (Ioo (-a) a) →
        σ 0 ∈ (chartAt H p).source →
        extChartAt I p (σ 0) ∈ V →
        w ≠ 0 →
        ((extChartAt I p (σ 0), T⁻¹ • w) : E × E) ∈
          closedBall ((extChartAt I p p, (0 : E)) : E × E) r →
        HasDerivAt (fun τ : ℝ => extChartAt I p (σ τ)) w 0 →
        deriv (fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
            (finv (extChartAt I p (σ s))) (finv (extChartAt I p (σ s)))) 0 = 0 →
        ∀ᶠ s in 𝓝[≠] (0 : ℝ),
          chartMetricInner (I := I) g p (extChartAt I p p)
              (finv (extChartAt I p (σ 0))) (finv (extChartAt I p (σ 0)))
            < chartMetricInner (I := I) g p (extChartAt I p p)
              (finv (extChartAt I p (σ s))) (finv (extChartAt I p (σ s))) := by
  obtain ⟨finv, V, r, ε, T, Z, hVopen, hpV, hVsub, hf0, hr, hε, hT, hTε, hflow,
      hleftinv, hstrict⟩ :=
    exists_forall_geodesic_tangent_stays_strictly_outside_ball (I := I) g p
  refine ⟨finv, V, r, ε, T, hVopen, hpV, hVsub, hf0, hr, hε, hT, hTε, hleftinv, ?_⟩
  intro σ a w ha hσ hσc hσsrc hσV hwne hmem hσv htang
  -- the base point reads back through the chart
  have hσsrc' : σ 0 ∈ (extChartAt I p).source := by
    rw [extChartAt_source]; exact hσsrc
  have hσ0 : σ 0 = (extChartAt I p).symm (extChartAt I p (σ 0)) :=
    ((extChartAt I p).left_inv hσsrc').symm
  -- readback: `σ` is computed by the strict lemma's own flow near `0`
  have hEq :
      EqOn σ (fun s : ℝ => (extChartAt I p).symm
          ((Z ((extChartAt I p (σ 0), T⁻¹ • w) : E × E) (s * T)).1))
        (Ioo (-(min a (ε / T))) (min a (ε / T))) :=
    hσ.eq_uniform_flow_readback hT hTε hflow hmem ha hσc hσ0 hσv
  have hεT : 0 < ε / T := div_pos (hT.trans hTε) hT
  have hbpos : 0 < min a (ε / T) := lt_min ha hεT
  have hJnhds : Ioo (-(min a (ε / T))) (min a (ε / T)) ∈ 𝓝 (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hbpos, hbpos⟩
  -- on the window, the intrinsic reading coincides with the strict-lemma flow reading
  set RD : ℝ → E := fun s : ℝ => extChartAt I p ((extChartAt I p).symm
    ((Z ((extChartAt I p (σ 0), T⁻¹ • w) : E × E) (s * T)).1)) with hRDdef
  have hchartEq : (fun s : ℝ => extChartAt I p (σ s)) =ᶠ[𝓝 (0 : ℝ)] RD := by
    filter_upwards [hJnhds] with s hs
    simp only [hRDdef]
    exact congrArg (extChartAt I p) (hEq hs)
  -- the intrinsic and flow-reading radial functionals agree near `0`
  set Fσ : ℝ → ℝ := fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
    (finv (extChartAt I p (σ s))) (finv (extChartAt I p (σ s))) with hFσdef
  set Fstrict : ℝ → ℝ := fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
    (finv (RD s)) (finv (RD s)) with hFstrictdef
  have hFEq : Fσ =ᶠ[𝓝 (0 : ℝ)] Fstrict := by
    filter_upwards [hchartEq] with s hs
    simp only [hFσdef, hFstrictdef]
    rw [hs]
  -- transfer the tangency hypothesis to the strict-lemma functional
  have htang' : deriv Fstrict 0 = 0 := by
    rw [← hFEq.deriv_eq]; exact htang
  -- apply the strict separation of the flow reading
  have hsep : ∀ᶠ s in 𝓝[≠] (0 : ℝ), Fstrict 0 < Fstrict s :=
    hstrict (extChartAt I p (σ 0)) w hσV hwne hmem htang'
  -- transfer the conclusion back to the intrinsic functional
  have hFEq' : Fσ =ᶠ[𝓝[≠] (0 : ℝ)] Fstrict := hFEq.filter_mono nhdsWithin_le_nhds
  have hF0 : Fσ 0 = Fstrict 0 := hFEq.eq_of_nhds
  filter_upwards [hsep, hFEq'] with s hsep_s hEq_s
  show Fσ 0 < Fσ s
  rw [hF0, hEq_s]; exact hsep_s

/-- **Math.** **No interior local maximum of the radial distance** (do Carmo Ch. 3, §4; the
directly-consumable form of the strict Lemma 4.1). With the package of
`exists_forall_intrinsic_geodesic_tangent_strictly_outside_ball`, for every admissible continuous
intrinsic geodesic `σ` (base reading into `V`, nonzero admissible velocity) the radial functional
`F(s) = ⟨exp_p⁻¹(σ s), exp_p⁻¹(σ s)⟩_p` has **no** local maximum at the base point `0`.

This is the exclusion do Carmo's convex-neighborhood contradiction rests on: at an interior point
where the distance from `p` to a joining geodesic attained a maximum, `F` would have a local
maximum, which this rules out. The proof: a local maximum forces `deriv F 0 = 0` (Fermat,
`IsLocalMax.deriv_eq_zero`), which by
`exists_forall_intrinsic_geodesic_tangent_strictly_outside_ball` gives the *strict* separation
`F 0 < F s` for `s ≠ 0` near `0`; but a local maximum gives `F s ≤ F 0` nearby, contradicting the
strict inequality on the (nontrivial) punctured neighborhood. -/
theorem exists_forall_intrinsic_geodesic_not_isLocalMax_radial [T2Space M]
    (g : RiemannianMetric I M) (p : M) :
    ∃ (finv : E → E) (V : Set E) (r ε T : ℝ),
      IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      finv (extChartAt I p p) = 0 ∧ 0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∃ εL : ℝ, 0 < εL ∧ ∀ w : E, ‖w‖ < εL →
        finv (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) ∧
      ∀ (σ : ℝ → M) (a : ℝ) (w : E), 0 < a →
        IsGeodesicOn (I := I) g σ (Ioo (-a) a) →
        ContinuousOn σ (Ioo (-a) a) →
        σ 0 ∈ (chartAt H p).source →
        extChartAt I p (σ 0) ∈ V →
        w ≠ 0 →
        ((extChartAt I p (σ 0), T⁻¹ • w) : E × E) ∈
          closedBall ((extChartAt I p p, (0 : E)) : E × E) r →
        HasDerivAt (fun τ : ℝ => extChartAt I p (σ τ)) w 0 →
        ¬ IsLocalMax (fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
            (finv (extChartAt I p (σ s))) (finv (extChartAt I p (σ s)))) 0 := by
  obtain ⟨finv, V, r, ε, T, hVopen, hpV, hVsub, hf0, hr, hε, hT, hTε, hleftinv, hmain⟩ :=
    exists_forall_intrinsic_geodesic_tangent_strictly_outside_ball (I := I) g p
  refine ⟨finv, V, r, ε, T, hVopen, hpV, hVsub, hf0, hr, hε, hT, hTε, hleftinv, ?_⟩
  intro σ a w ha hσ hσc hσsrc hσV hwne hmem hσv hmax
  set F : ℝ → ℝ := fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
    (finv (extChartAt I p (σ s))) (finv (extChartAt I p (σ s))) with hFdef
  -- Fermat: an interior local maximum forces a critical point
  have htang : deriv F 0 = 0 := hmax.deriv_eq_zero
  -- the strict separation from the tangency
  have hsep : ∀ᶠ s in 𝓝[≠] (0 : ℝ), F 0 < F s :=
    hmain σ a w ha hσ hσc hσsrc hσV hwne hmem hσv htang
  -- a local maximum gives the reverse (non-strict) inequality nearby
  have hle : ∀ᶠ s in 𝓝[≠] (0 : ℝ), F s ≤ F 0 :=
    hmax.filter_mono nhdsWithin_le_nhds
  -- the two are contradictory on the (nontrivial) punctured neighborhood
  have hfalse : ∀ᶠ s in 𝓝[≠] (0 : ℝ), False := by
    filter_upwards [hsep, hle] with s hs1 hs2
    exact absurd hs1 (not_lt.mpr hs2)
  obtain ⟨s, hs⟩ := hfalse.exists
  exact hs

section StronglyConvex

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [I.Boundaryless] [T2Space (TangentBundle I M')]

/-- **Math.** **Strongly convex set** (do Carmo Ch. 3, §4). A set `S ⊆ M` is *strongly convex*
if any two points `q₁, q₂` of the closure `closure S` are joined by a **minimizing** geodesic
`γ : [0,1] → M` (constant-speed, realizing the distance `dist q₁ q₂` proportionally to arc length)
whose open-arc interior `γ '' (0,1)` lies in `S`, and this joining geodesic is **unique** among such
competitors. The minimizing clause `dist (γ s) (γ t) = |s - t| * dist q₁ q₂` is the house idiom of
`Riemannian.Geodesic.exists_minimizing_geodesic`; the interior is the open-arc image (do Carmo's
"interior of the arc"), not the topological `interior`; uniqueness is pointwise `Set.EqOn` on
`[0,1]`. do Carmo's Proposition 4.2 is that small geodesic balls `Metric.ball p β` are strongly
convex. -/
def StronglyConvex (g : RiemannianMetric I M') (S : Set M') : Prop :=
  ∀ q₁ ∈ closure S, ∀ q₂ ∈ closure S,
    ∃ γ : ℝ → M',
      γ 0 = q₁ ∧ γ 1 = q₂ ∧
      IsGeodesicOn (I := I) g γ (Set.Icc 0 1) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist q₁ q₂) ∧
      γ '' Set.Ioo (0 : ℝ) 1 ⊆ S ∧
      (∀ γ' : ℝ → M', γ' 0 = q₁ → γ' 1 = q₂ →
        IsGeodesicOn (I := I) g γ' (Set.Icc 0 1) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          dist (γ' s) (γ' t) = |s - t| * dist q₁ q₂) →
        γ' '' Set.Ioo (0 : ℝ) 1 ⊆ S →
        Set.EqOn γ' γ (Set.Icc 0 1))

end StronglyConvex

end Exponential

end Riemannian

end
