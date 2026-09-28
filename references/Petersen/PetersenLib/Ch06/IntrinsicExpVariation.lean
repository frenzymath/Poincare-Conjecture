import PetersenLib.Ch06.ExpIntrinsicBridge
import PetersenLib.Ch06.ExpVariation
import PetersenLib.Ch01.ArcLength
import PetersenLib.Ch05.UniformInjectivityRadius
-- `geodesicMaximalCurve_zero` is filed here, not in `Ch05/GeodesicCompleteness.lean`
import PetersenLib.Ch05.IsometryUniqueness

/-!
# The intrinsic exponential variation, and the chart reading of a field along a curve

Two pieces of infrastructure for §6.2–§6.3, both feeding the joint-smoothness gap that separates
this project from Bonnet–Synge (Lem. 6.3.1).

* `intrinsicExpVariation` — the exponential variation `\bar c(s,t) = \exp_{c(t)}(sV(t))` built on
  the **intrinsic** exponential `geodesicMaximalCurve g q v 1` rather than on the chart-anchored
  `PetersenLib.expMap`.  `Ch06/ExpIntrinsicBridge.lean` explains at length why the distinction is
  forced: `expMap`'s domain is anchored to `chartAt H q`, an arbitrary per-point choice, so its
  chart-escape radius has no locally uniform lower bound in `q` and a single `δ` serving every
  basepoint `c t` is unobtainable *in principle*.  The slab hypothesis `hf` of
  `secondVariationEnergy` (Thm. 6.1.4) must therefore be discharged intrinsically; the two agree
  near the origin by `expMap_eq_geodesicMaximalCurve_of_small`, which is how
  `Ch06/ExpVariation.lean`'s two pointwise results carry across.

* `IsVectorFieldAlong.contMDiffOn_chartFiberCoord` — the chart reading `t ↦ \hat V(t)` of a field
  along a curve is smooth.  This **activates `IsVectorFieldAlong`** (`Ch01/ArcLength.lean`), which
  until now was dead code: it had no uses anywhere in the tree outside its own file, and nothing
  derived the chart reading from it, which is the only thing one ever wants it for.

## Why the second lemma is three lines

`Exponential.chartFiberCoord_contMDiffOn` (`Riemannian/Geodesic/Equation.lean`) already says
the fibre coordinate `p ↦ (\text{triv}_x p).2` is `C^∞` on `geodesicChartDomain x`, and
`IsVectorFieldAlong c V J` is by definition smoothness of the section `t ↦ ⟨c t, V t⟩`.  So the
chart reading is a composition, and the only side condition is that the section lands in the
chart domain — which `mem_geodesicChartDomain_of_proj` reduces to `c t ∈ (chartAt H x).source`,
since `geodesicChartDomain x` is *by definition* the preimage of the chart source under the
projection (`trivializationAt_source_eq`).  The models match on the nose: `I.tangent` is
`I.prod 𝓘(ℝ, E)`, which is the target model `IsVectorFieldAlong` is stated with.
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Geodesic PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]

/-- **Math.** Petersen §6.1: the **intrinsic exponential variation** of a field `V` along a curve
`c`,

$$\bar c(s,t) = \exp_{c(t)}\big(sV(t)\big),$$

with `exp` the intrinsic (moving-foot) exponential `geodesicMaximalCurve g q v 1`.

This is `Ch06/ExpVariation.lean`'s `expVariation` with the chart-anchored `PetersenLib.expMap`
replaced by the intrinsic exponential.  The replacement is not cosmetic — see the module
docstring and `Ch06/ExpIntrinsicBridge.lean`: only the intrinsic form can carry a slab statement,
because `expMap`'s domain has no locally uniform radius in the basepoint. -/
def intrinsicExpVariation (g : RiemannianMetric I M) (c : ℝ → M) (V : ∀ t, TangentSpace I (c t)) :
    ℝ → ℝ → M :=
  fun s t => geodesicMaximalCurve (I := I) g (c t) ((s • V t : TangentSpace I (c t))) 1

/-- **Math.** The intrinsic exponential variation is a variation **of `c`**: at `s = 0` the
exponential is evaluated at the zero vector, and the maximal geodesic with zero initial velocity
is constant, so `\bar c(0, t) = c(t)`. -/
@[simp] theorem intrinsicExpVariation_zero (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) : intrinsicExpVariation (I := I) g c V 0 = c := by
  funext t
  show geodesicMaximalCurve (I := I) g (c t) (((0 : ℝ) • V t : TangentSpace I (c t))) 1 = c t
  rw [zero_smul]
  exact geodesicMaximalCurve_zero (I := I) g (c t) 1

/-- **Math.** The variation field of the intrinsic exponential variation is the
prescribed field `V`.  At a fixed time, sufficiently small vectors stay in the
region where the chart exponential and intrinsic maximal geodesic agree; the
pointwise identity for `expVariation` then transfers through eventual equality. -/
theorem variationField_intrinsicExpVariation (g : RiemannianMetric I M)
    [SigmaCompactSpace M] [LocallyCompactSpace M]
    (c : ℝ → M) (V : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    variationField (I := I) (intrinsicExpVariation (I := I) g c V) t = V t := by
  obtain ⟨ρ, hρ, hbridge⟩ := expMap_eq_geodesicMaximalCurve_of_small (I := I) g (c t)
  let w : ℝ → E := fun s => @HSMul.hSMul ℝ E E _ s (V t)
  have hw : Continuous w := continuous_id.smul continuous_const
  have hopen : IsOpen {s : ℝ | ‖w s‖ < ρ} :=
    isOpen_lt hw.norm continuous_const
  have hmem : (0 : ℝ) ∈ {s : ℝ | ‖w s‖ < ρ} := by
    simpa [w] using hρ
  have hev : (fun s => intrinsicExpVariation (I := I) g c V s t) =ᶠ[𝓝 0]
      (fun s => expVariation (I := I) g c V s t) := by
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact (hbridge (w s) hs).symm
  have hevchart :
      (fun s => extChartAt I (c t) (intrinsicExpVariation (I := I) g c V s t)) =ᶠ[𝓝 0]
        (fun s => extChartAt I (c t) (expVariation (I := I) g c V s t)) :=
    hev.fun_comp (extChartAt I (c t))
  rw [variationField_eq, intrinsicExpVariation_zero, hevchart.deriv_eq]
  simpa [variationField_eq, expVariation_zero] using
    variationField_expVariation (I := I) g c V t

/-- **Math.** **The chart reading of a smooth field along a curve is smooth.**  If `V` is a vector
field along `c` on `J` (`IsVectorFieldAlong`, i.e. the section `t ↦ ⟨c t, V t⟩` is `C^∞` on `J`)
and `c` maps `J` into the chart at `x`, then the chart-`x` fibre coordinate
`t ↦ \hat V(t) = (\text{triv}_x⟨c t, V t⟩)_2` is `C^∞` on `J`.

This is the lemma that makes `IsVectorFieldAlong` usable: reading a field along a curve in a
chart is the only thing one ever does with it, and nothing in the tree did it before — the
predicate had no uses outside its own defining file.

**Proof.**  `chartFiberCoord_contMDiffOn` gives smoothness of the fibre coordinate on
`geodesicChartDomain x`; compose with the section, whose `MapsTo` side condition is
`mem_geodesicChartDomain_of_proj` applied to `hsrc` (the chart domain of the bundle *is* the
preimage of the chart source under the projection). -/
theorem IsVectorFieldAlong.contMDiffOn_chartFiberCoord {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {J : Set ℝ}
    (hV : IsVectorFieldAlong (I := I) c V J) (x : M)
    (hsrc : ∀ t ∈ J, c t ∈ (chartAt H x).source) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (fun t => chartFiberCoord (I := I) x (⟨c t, V t⟩ : TangentBundle I M)) J :=
  (chartFiberCoord_contMDiffOn (I := I) x).comp hV fun t ht =>
    mem_geodesicChartDomain_of_proj (I := I) (hsrc t ht)

/-- **Math.** **The chart fibre coordinate is linear in the fibre**, in the `•` instance:
`\widehat{sv} = s\hat v`.  The trivialization is fibrewise a continuous *linear* map, so this is
`ContinuousLinearMap.map_smul` once the raw second component is rewritten into that linear map
(`Bundle.Trivialization.continuousLinearMapAt_apply_of_mem`, which needs the foot in the
trivialization's base set).

This is what turns the `s`-dependence of `intrinsicExpVariation` — where `s` sits *inside* the
fibre, as `s • V t` — into an `s` sitting outside, in the chart coordinate `s • \hat V(t)`.  That
is the form in which the pair map's joint `C^∞`-ness can consume it, so this lemma is exactly the
hinge of the slab argument. -/
theorem chartFiberCoord_smul (x q : M) (hq : q ∈ (chartAt H x).source) (s : ℝ)
    (v : TangentSpace I q) :
    chartFiberCoord (I := I) x (⟨q, (s • v : TangentSpace I q)⟩ : TangentBundle I M)
      = s • chartFiberCoord (I := I) x (⟨q, v⟩ : TangentBundle I M) := by
  set e := trivializationAt E (TangentSpace I) x with hedef
  -- the trivialization's base set *is* the chart source, so `hq` is the membership wanted
  have hq' : q ∈ e.baseSet := by
    rw [hedef, TangentBundle.trivializationAt_baseSet]; exact hq
  show (e ⟨q, (s • v : TangentSpace I q)⟩).2 = s • (e ⟨q, v⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hq',
      ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hq']
  exact ContinuousLinearMap.map_smul _ _ _

/-- **Math.** The intrinsic exponential variation is jointly `C^∞` on a
neighbourhood of every point `(0,t)` where the base curve and the field along
it are smooth.  Locally, the moving-base exponential is the endpoint of the
smooth chart geodesic flow; the open flow ball supplies a whole neighbourhood,
not merely pointwise smoothness at the zero section. -/
theorem exists_intrinsicExpVariation_contMDiffOn_nhds
    (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {J : Set ℝ} {t : ℝ}
    (hJopen : IsOpen J) (ht : t ∈ J)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c J)
    (hV : IsVectorFieldAlong (I := I) c V J) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ ((0 : ℝ), t) ∈ U ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (Function.uncurry (intrinsicExpVariation (I := I) g c V)) U := by
  classical
  let p : M := c t
  obtain ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, hG, -⟩ :=
    exists_pairMap_contDiffOn_infty (I := I) g p
  let z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E)
  let S : Set (E × E) := {x : E × E |
    ((x.1, T⁻¹ • x.2) : E × E) ∈ Metric.ball z₀ r}
  let K : Set ℝ := J ∩ c ⁻¹' (chartAt H p).source
  let u : ℝ → E := fun τ => extChartAt I p (c τ)
  let w : ℝ → E := fun τ => chartFiberCoord (I := I) p
    (⟨c τ, V τ⟩ : TangentBundle I M)
  let x : ℝ × ℝ → E × E := fun z => (u z.2, z.1 • w z.2)
  have hKopen : IsOpen K := by
    exact hc.continuousOn.isOpen_inter_preimage hJopen (chartAt H p).open_source
  have htK : t ∈ K := by
    refine ⟨ht, ?_⟩
    change c t ∈ (chartAt H (c t)).source
    exact mem_chart_source H (c t)
  have hsrc : ∀ τ ∈ K, c τ ∈ (chartAt H p).source := fun τ hτ => hτ.2
  have hu : ContDiffOn ℝ ∞ u K := by
    apply contDiffOn_extChartAt_comp (hc.mono inter_subset_left)
    intro τ hτ
    rw [extChartAt_source]
    exact hsrc τ hτ
  have hVK : IsVectorFieldAlong (I := I) c V K := hV.mono inter_subset_left
  have hwM : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ w K := by
    exact hVK.contMDiffOn_chartFiberCoord p hsrc
  have hw : ContDiffOn ℝ ∞ w K := contMDiffOn_iff_contDiffOn.mp hwM
  have hx : ContDiffOn ℝ ∞ x ((Set.univ : Set ℝ) ×ˢ K) := by
    have hx₁ : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => u z.2)
        ((Set.univ : Set ℝ) ×ˢ K) :=
      hu.comp contDiff_snd.contDiffOn (fun z hz => hz.2)
    have hx₂ : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => z.1 • w z.2)
        ((Set.univ : Set ℝ) ×ˢ K) := by
      have hwcomp : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => w z.2)
          ((Set.univ : Set ℝ) ×ˢ K) :=
        hw.comp contDiff_snd.contDiffOn (fun (_z : ℝ × ℝ) hz => hz.2)
      exact contDiff_fst.contDiffOn.smul hwcomp
    exact hx₁.prodMk hx₂
  have hSopen : IsOpen S := by
    exact Metric.isOpen_ball.preimage
      (continuous_fst.prodMk (continuous_snd.const_smul T⁻¹))
  let D : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ K
  let U : Set (ℝ × ℝ) := D ∩ x ⁻¹' S
  have hDopen : IsOpen D := isOpen_univ.prod hKopen
  have hUopen : IsOpen U := by
    exact hx.continuousOn.isOpen_inter_preimage hDopen hSopen
  have hx0 : x ((0 : ℝ), t) = z₀ := by
    simp [x, u, w, z₀, p]
  have h0S : x ((0 : ℝ), t) ∈ S := by
    rw [hx0]
    show ((z₀.1, T⁻¹ • z₀.2) : E × E) ∈ Metric.ball z₀ r
    simp [z₀, Metric.mem_ball, hr]
  have h0U : ((0 : ℝ), t) ∈ U := ⟨⟨Set.mem_univ _, htK⟩, h0S⟩
  let G : E × E → E × E := fun y =>
    ((y.1 : E), (Z ((y.1, T⁻¹ • y.2) : E × E) T).1)
  have hGS : ContDiffOn ℝ ∞ G S := by
    simpa [G, S, z₀] using hG
  have hGU : ContDiffOn ℝ ∞ (fun z => G (x z)) U :=
    hGS.comp (hx.mono inter_subset_left) (fun z hz => hz.2)
  have hendpoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (fun z : ℝ × ℝ => (G (x z)).2) U :=
    contMDiffOn_iff_contDiffOn.mpr hGU.snd
  have hTIcc : T ∈ Icc (-ε) ε := ⟨by linarith, hTε.le⟩
  have htgt : MapsTo (fun z : ℝ × ℝ => (G (x z)).2) U (extChartAt I p).target := by
    intro z hz
    have hmem : ((x z).1, T⁻¹ • (x z).2) ∈ Metric.closedBall z₀ r :=
      Metric.ball_subset_closedBall hz.2
    exact ((hflow _ (by simpa [z₀] using hmem)).2.2 T hTIcc).1
  have hsurface : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (fun z : ℝ × ℝ => (extChartAt I p).symm ((G (x z)).2)) U :=
    (contMDiffOn_extChartAt_symm p).comp hendpoint htgt
  refine ⟨U, hUopen, h0U, hsurface.congr ?_⟩
  intro z hz
  rcases z with ⟨s, τ⟩
  have hτK : τ ∈ K := hz.1.2
  have hqsrc : c τ ∈ (chartAt H p).source := hsrc τ hτK
  have hcoord : (x (s, τ)).2 = chartFiberCoord (I := I) p
      (⟨c τ, (s • V τ : TangentSpace I (c τ))⟩ : TangentBundle I M) := by
    exact (chartFiberCoord_smul (I := I) p (c τ) hqsrc s (V τ)).symm
  have hcoord' : s • w τ = chartFiberCoord (I := I) p
      (⟨c τ, (s • V τ : TangentSpace I (c τ))⟩ : TangentBundle I M) := by
    simpa [x] using hcoord
  have hmem : ((extChartAt I p (c τ),
      T⁻¹ • chartFiberCoord (I := I) p
        (⟨c τ, (s • V τ : TangentSpace I (c τ))⟩ : TangentBundle I M)) : E × E)
      ∈ Metric.closedBall z₀ r := by
    have hm := Metric.ball_subset_closedBall hz.2
    simpa [x, u, hcoord'] using hm
  have hivp := isGeodesicWithInitialOn_flow_window (I := I) g p hT hTε hflow
    hqsrc (s • V τ : TangentSpace I (c τ)) (by simpa [z₀] using hmem)
  have h0J : (0 : ℝ) ∈ Ioo (-(ε / T)) (ε / T) := by
    have : 0 < ε / T := div_pos hε hT
    exact ⟨by linarith, this⟩
  have h1J : (1 : ℝ) ∈ Ioo (-(ε / T)) (ε / T) := by
    have hone : (1 : ℝ) < ε / T := (one_lt_div hT).mpr hTε
    exact ⟨by linarith, hone⟩
  have heq := geodesicMaximalCurve_eqOn (I := I) g isOpen_Ioo ordConnected_Ioo h0J hivp h1J
  show intrinsicExpVariation (I := I) g c V s τ =
    (extChartAt I p).symm ((G (x (s, τ))).2)
  simpa [intrinsicExpVariation, G, x, u, hcoord'] using heq

/-- **Math.** Compact-time form of
`exists_intrinsicExpVariation_contMDiffOn_nhds`: over a compact interval in an
open set on which the base curve and field are smooth, one parameter width
works uniformly and the variation is `C^∞` on an open slab with a little room
past both time endpoints. -/
theorem exists_intrinsicExpVariation_contMDiffOn_slab
    (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {J : Set ℝ} {p₁ p₂ : ℝ}
    (hJopen : IsOpen J) (h12 : p₁ < p₂) (hsub : Icc p₁ p₂ ⊆ J)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c J)
    (hV : IsVectorFieldAlong (I := I) c V J) :
    ∃ (δ a b : ℝ), 0 < δ ∧ Icc p₁ p₂ ⊆ Ioo a b ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (Function.uncurry (intrinsicExpVariation (I := I) g c V))
        (Ioo (-δ) δ ×ˢ Ioo a b) := by
  classical
  choose U hUopen hUmem hUsmooth using fun τ : Icc p₁ p₂ =>
    exists_intrinsicExpVariation_contMDiffOn_nhds (I := I) g hJopen
      (hsub τ.2) hc hV
  let O : Set (ℝ × ℝ) := ⋃ τ : Icc p₁ p₂, U τ
  have hOopen : IsOpen O := isOpen_iUnion fun τ => hUopen τ
  have hOsmooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
      (Function.uncurry (intrinsicExpVariation (I := I) g c V)) O := by
    exact ContMDiffOn.iUnion_of_isOpen hUsmooth hUopen
  have hzero : ({0} : Set ℝ) ×ˢ Icc p₁ p₂ ⊆ O := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    simp only [Set.mem_singleton_iff] at hs
    subst s
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hUmem ⟨t, ht⟩⟩
  obtain ⟨us, vt, husopen, hvtopen, hzero_us, hIcc_vt, hprod⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := (0 : ℝ))) isCompact_Icc hOopen hzero
  have h0us : (0 : ℝ) ∈ us := hzero_us rfl
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.mp husopen 0 h0us
  obtain ⟨η, hη, hηsub⟩ :=
    isCompact_Icc.exists_thickening_subset_open hvtopen hIcc_vt
  let a : ℝ := p₁ - η / 2
  let b : ℝ := p₂ + η / 2
  have hη2 : 0 < η / 2 := half_pos hη
  have htime : Ioo a b ⊆ vt := by
    rintro t ⟨htl, htr⟩
    apply hηsub
    rw [Metric.mem_thickening_iff]
    by_cases hleft : t < p₁
    · refine ⟨p₁, left_mem_Icc.mpr h12.le, ?_⟩
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      dsimp [a] at htl
      linarith [hη2]
    by_cases hright : p₂ < t
    · refine ⟨p₂, right_mem_Icc.mpr h12.le, ?_⟩
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      dsimp [b] at htr
      linarith [hη2]
    · refine ⟨t, ⟨not_lt.mp hleft, not_lt.mp hright⟩, ?_⟩
      simpa using hη
  have hIcc_ab : Icc p₁ p₂ ⊆ Ioo a b := by
    rintro t ⟨htl, htr⟩
    dsimp [a, b]
    constructor <;> linarith
  have hparam : Ioo (-δ) δ ⊆ us := by
    intro s hs
    apply hδball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact hs
  refine ⟨δ, a, b, hδ, hIcc_ab, hOsmooth.mono ?_⟩
  intro z hz
  exact hprod ⟨hparam hz.1, htime hz.2⟩

end PetersenLib

end
