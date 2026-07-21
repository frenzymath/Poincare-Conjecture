import PetersenLib.Ch06.ConnectionAlongCurve

/-!
# Petersen Ch. 6, §6.1 — parallel fields on the WHOLE interval (Thm. 6.1.3, global form)

`Ch06/ConnectionAlongCurve` proves Petersen's Theorem 6.1.3
(`thm:pet-ch6-parallel-field-existence-uniqueness`, p. 252) in a **chart-local** form: the
relevant piece of the curve is assumed to lie in the source of a *single* chart `α`, and the
continuity/boundedness of the parallel-transport ODE coefficient are taken as hypotheses.  This
file removes the chart restriction and proves the theorem **globally in the interval**, which is
the actual content of Petersen's statement: *for `t₀ ∈ I` and `v ∈ T_{c(t₀)}M` there is a unique
parallel field `V` defined on ALL of `I` with `V(t₀) = v`.*  Global existence is exactly what
distinguishes the **linear** parallel-transport ODE from the nonlinear geodesic equation, whose
solutions only exist locally; a curve of any length leaves every chart, so the single-chart form
does not say this.

## What is proved

* `parallelField_existence_uniqueness_global` — **Theorem 6.1.3**, global form.  For `c` of class
  `C²` on a compact `[a,b]`, `t₀ ∈ (a,b)` and `v ∈ T_{c(t₀)}M`, there is a field parallel along
  `c` on the whole of `(a,b)` with `V(t₀) = v`, unique among such.  No chart hypothesis.  Split
  into `exists_isParallelSolOn_Ioo` (existence) and `isParallelSolOn_eqOn_Ioo` (uniqueness).
* `parallelField_existence_uniqueness_interval` — the same on an **arbitrary bounded open
  interval**, assuming `c` is `C²` only on `(a,b)` itself (no regularity at the endpoints), by
  exhausting `(a,b)` with compact subintervals.  This is Petersen's hypothesis verbatim.
* `exists_parallelOrthonormalFrameOn_Ioo` — parallel-transport every vector of an orthonormal
  seed frame and use metric compatibility to prove that all Gram products remain constant on
  the interval.

## Route

Petersen's `I` is an arbitrary interval, so the proof is the standard chart-cover walk.

* `exists_lebesgue_chart` — compactness of `c([a,b])` plus a Lebesgue number give a `δ > 0` such
  that every `δ`-window of `c` lies in *one* chart source.  (Ch. 5's
  `ConstantSpeedApproximation` runs the same chart-cover + Lebesgue-number + polygon-gluing
  argument for its chart polygons.)
* `exists_isParallelSolOn_chart` / `isParallelSolOn_chart_eqOn` — Theorem 6.1.3 on one such
  window, discharging *all* hypotheses of the chart-local theorem: the ODE coefficient's
  continuity comes from smoothness of the chart Christoffel symbols
  (`chartChristoffel_contDiffOn_interior`) via the new
  `chartChristoffelContractionRight_eq_sum`, which exhibits the coefficient as a finite sum of
  continuously-varying scalar multiples of *constant* continuous linear maps — this is what
  upgrades the pointwise continuity of Ch. 5's `continuousOn_chartChristoffelContraction_comp`
  to continuity in the **operator norm**, which is what the vendored linear-ODE engine wants;
  the uniform bound `K` is then compactness (`IsCompact.exists_bound_of_continuousOn`).
* `exists_glue_isParallelSolOn` — splicing two solutions at a junction inside their overlap.
  Soundness of gluing *across charts* is `covariantDerivCoord_transfer` (§6.1): it is what makes
  "parallel" chart-independent, and it is used here through
  `differentiableAt_chartFieldRep_transfer` and `derivAlongCurve_eq_zero_iff`.
* `exists_extend_right` / `exists_extend_left` — one walk step each; the induction in
  `exists_isParallelSolOn_Ioo` walks the window `(t₀ − nδ/2, t₀ + nδ/2)` outward until it
  exhausts `(a,b)`.
* Uniqueness is chart-local uniqueness plus connectedness of `(a,b)`: agreement at one point of a
  `δ`-window propagates to the whole window, so the agreement locus and its complement are both
  open.

## Conventions

Like `Ch06/ConnectionAlongCurve`, this file lives on the **chart-Christoffel side** of the
project (Petersen's Ch. 5 world), not on the abstract `AffineConnection`/Koszul side of Ch. 2.
`IsParallelSolAt` / `IsParallelSolOn` bundle Petersen's `V̇ = 0` with the regularity he leaves
implicit; both clauses are read in the moving-foot chart and so are manifestly chart-free.

## What is deferred

* **Unbounded intervals.** `a`, `b` are real, so `I` is a bounded open interval.  Petersen's `I`
  may also be a half-line or `ℝ`; that case needs exactly the exhaustion of
  `exists_isParallelSolOn_Ioo_of_openHyp` re-run over a cofinal family of compacts (`[t₀−n,
  t₀+n]` instead of `[Aₙ, Bₙ]`), with the same coherence-by-uniqueness argument.  It is routine
  and adds no new mathematics, so it is not done here.
* **Endpoints.** Parallelism is concluded on the open `(a,b)`, because `derivAlongCurve` is
  defined with the two-sided `deriv`, which is not the right notion at an endpoint.  This matches
  `Ch06/ConnectionAlongCurve` and is a faithful reading of Petersen, whose ODE argument is
  interior.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff NNReal

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The parallel-transport ODE coefficient is continuous in the operator norm -/

/-- **Math.** The parallel-transport ODE coefficient `w ↦ Γ_α(v, w)(y)` written out in the
coordinate frame: a finite sum of scalar multiples of the **constant** rank-one continuous linear
maps `w ↦ w^j e_k`, the scalars being `Γ^k_{ij}(y) v^i`.  Continuity of `Γ` in `(v, y)` for the
*operator norm* — which is what the vendored linear-ODE engine requires — follows from this,
whereas Ch. 5's `continuousOn_chartChristoffelContraction_comp` only gives it pointwise in `w`. -/
theorem chartChristoffelContractionRight_eq_sum (g : RiemannianMetric I M) (α : M) (v y : E) :
    chartChristoffelContractionRight (I := I) g α v y
      = ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) g α i j k y * Geodesic.chartCoord (E := E) i v) •
              (Geodesic.chartCoordFunctional (E := E) j).smulRight
                (Module.finBasis ℝ E k) := by
  ext w
  simp only [chartChristoffelContractionRight_apply, Geodesic.chartChristoffelContraction_def,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  rfl

/-- **Math.** Petersen §6.1 (p. 252): **continuity of the parallel-transport ODE coefficient**
`t ↦ Γ_α(u̇(t), ·)(u(t))` in the operator norm, along a continuous family of base points `y` and
velocities `v` mapping into the chart target.  This is hypothesis `hcont` of the chart-local
Theorem 6.1.3 (`exists_isParallelAlong`), which that theorem takes on faith. -/
theorem continuousOn_chartChristoffelContractionRight_comp [I.Boundaryless] {X : Type*}
    [TopologicalSpace X] (g : RiemannianMetric I M) (α : M) {y v : X → E} {S : Set X}
    (hy : ContinuousOn y S) (hv : ContinuousOn v S)
    (hmem : ∀ x ∈ S, y x ∈ (extChartAt I α).target) :
    ContinuousOn (fun x => chartChristoffelContractionRight (I := I) g α (v x) (y x)) S := by
  simp only [chartChristoffelContractionRight_eq_sum]
  have hmem' : ∀ x ∈ S, y x ∈ interior (extChartAt I α).target := fun x hx =>
    extChartAt_target_subset_interior_of_boundaryless (I := I) α (hmem x hx)
  refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun i _ =>
    continuousOn_finsetSum _ fun j _ => ContinuousOn.smul ?_ continuousOn_const
  exact ((chartChristoffel_contDiffOn_interior (I := I) g α i j k).continuousOn.comp hy hmem').mul
    ((Geodesic.chartCoordFunctional (E := E) i).continuous.comp_continuousOn hv)

/-- **Math.** Petersen §6.1 (p. 249): **chart-change covariance of the regularity of a field
along `c`** — if the chart-`β` reading of `V` is differentiable at `t₀`, so is its chart-`α`
reading, for any other chart `α` around `c t₀`.  The two readings differ by the `τ`-dependent
isomorphism `Dτ(u_β(τ))`, which is itself differentiable because the transition map is `C²`.
This is the companion of `covariantDerivCoord_transfer` at the level of regularity, and is what
lets the chart-free `IsParallelSolAt` below talk to the chart-local Theorem 6.1.3. -/
theorem differentiableAt_chartFieldRep_transfer [I.Boundaryless] {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (β α : M) {t₀ : ℝ}
    (hc : ContinuousAt c t₀)
    (hsrcβ : c t₀ ∈ (chartAt H β).source)
    (hsrcα : c t₀ ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I β (c τ)) t₀)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c β V) t₀) :
    DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t₀ := by
  classical
  set ux : ℝ → E := fun τ => extChartAt I β (c τ) with hux
  set Vx : ℝ → E := chartFieldRep (I := I) c β V with hVx
  set tm : E → E := chartTransition (M := M) I β α with htm
  set y₀ : E := extChartAt I β (c t₀) with hy₀
  have hxx : c t₀ ∈ (extChartAt I β).source := by rwa [extChartAt_source]
  have hxα : c t₀ ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hev : ∀ᶠ τ in 𝓝 t₀, c τ ∈ (extChartAt I β).source ∩ (extChartAt I α).source :=
    hc.eventually_mem
      (((isOpen_extChartAt_source (I := I) β).inter
        (isOpen_extChartAt_source (I := I) α)).mem_nhds ⟨hxx, hxα⟩)
  have hdom : y₀ ∈ chartTransitionDomain (M := M) I β α := mem_chartTransitionDomain hxx hxα
  have hτ2 : ContDiffAt ℝ 2 tm y₀ := (contDiffAt_chartTransition hdom).of_le (by decide)
  have hτfd : DifferentiableAt ℝ (fderiv ℝ tm) y₀ :=
    (hτ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA' : HasDerivAt (fun τ => fderiv ℝ tm (ux τ))
      (fderiv ℝ (fderiv ℝ tm) y₀ (deriv ux t₀)) t₀ :=
    hτfd.hasFDerivAt.comp_hasDerivAt t₀ hu.hasDerivAt
  have hVα_eq : chartFieldRep (I := I) c α V =ᶠ[𝓝 t₀] fun τ => fderiv ℝ tm (ux τ) (Vx τ) := by
    filter_upwards [hev] with τ hτ
    rw [fderiv_chartTransition hτ.1 hτ.2]
    exact (tangentCoordChange_comp
      ⟨⟨mem_extChartAt_source (I := I) (c τ), hτ.1⟩, hτ.2⟩).symm
  exact ((hA'.clm_apply hV.hasDerivAt).congr_of_eventuallyEq hVα_eq).differentiableAt

/-- **Math.** Petersen §6.1 (p. 249): `V̇(t)` depends only on the **germ of `V` at `t`** — both
the coordinate derivative and the Christoffel correction are local.  This is what makes the
piecewise gluing below produce a genuinely parallel field. -/
theorem derivAlongCurve_congr (g : RiemannianMetric I M) (c : ℝ → M)
    {V W : ∀ t, TangentSpace I (c t)} {t : ℝ} (h : ∀ᶠ s in 𝓝 t, V s = W s) :
    derivAlongCurve (I := I) g c V t = derivAlongCurve (I := I) g c W t := by
  have hrep : chartFieldRep (I := I) c (c t) V =ᶠ[𝓝 t] chartFieldRep (I := I) c (c t) W := by
    filter_upwards [h] with s hs
    simp only [chartFieldRep_apply, hs]
  rw [derivAlongCurve_def, derivAlongCurve_def, hrep.deriv_eq, h.self_of_nhds]

/-- **Math.** Petersen §6.1 (p. 252): `V` is a **regular parallel field along `c` at the time
`t`** — its moving-foot chart reading is differentiable at `t` and its covariant derivative
`V̇(t)` vanishes.  The differentiability clause is not automatic: `derivAlongCurve` is built from
`deriv`, which is junk `0` off the differentiability locus, so `V̇ ≡ 0` alone does not force
regularity (Petersen leaves smoothness of fields implicit).  Both clauses are stated in the
moving-foot chart, hence are manifestly chart-free. -/
def IsParallelSolAt (g : RiemannianMetric I M) (c : ℝ → M) (V : ∀ t, TangentSpace I (c t))
    (t : ℝ) : Prop :=
  DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t ∧
    derivAlongCurve (I := I) g c V t = 0

/-- **Math.** Petersen §6.1 (p. 252): `V` is a regular parallel field along `c` on the time set
`J`.  This is `def:pet-ch6-parallel-field` localized to `J` (with the regularity Petersen leaves
implicit made explicit); `IsParallelAlong g c V ↔ IsParallelSolOn g c univ V` up to that
regularity clause. -/
def IsParallelSolOn (g : RiemannianMetric I M) (c : ℝ → M) (J : Set ℝ)
    (V : ∀ t, TangentSpace I (c t)) : Prop :=
  ∀ t ∈ J, IsParallelSolAt (I := I) g c V t

theorem IsParallelSolOn.mono {g : RiemannianMetric I M} {c : ℝ → M} {J J' : Set ℝ}
    {V : ∀ t, TangentSpace I (c t)} (h : IsParallelSolOn (I := I) g c J V) (hsub : J' ⊆ J) :
    IsParallelSolOn (I := I) g c J' V := fun t ht => h t (hsub ht)

/-- **Math.** Being a regular parallel field at `t` depends only on the germ of `V` at `t`.
This is what makes the chart-piece **gluing** below legitimate. -/
theorem IsParallelSolAt.congr {g : RiemannianMetric I M} {c : ℝ → M}
    {V W : ∀ t, TangentSpace I (c t)} {t : ℝ} (h : IsParallelSolAt (I := I) g c V t)
    (hev : ∀ᶠ s in 𝓝 t, V s = W s) : IsParallelSolAt (I := I) g c W t := by
  refine ⟨h.1.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [hev] with s hs
    simp only [chartFieldRep_apply, hs]
  · rw [← derivAlongCurve_congr (I := I) g c hev]; exact h.2

/-- **Math.** Petersen §6.1 (p. 252), the gluing step of Theorem 6.1.3: two parallel fields
`V₁`, `V₂` along `c`, defined on overlapping open time sets `J₁`, `J₂` and **agreeing on an open
overlap `O`** around a junction time `τ`, splice to a single parallel field, equal to `V₁` left of
`τ` and to `V₂` right of `τ`.  Parallelism of the splice is a germ condition
(`IsParallelSolAt.congr`), and at the junction itself the splice has the germ of `V₁` precisely
because the two agree on the whole of `O`. -/
theorem exists_glue_isParallelSolOn (g : RiemannianMetric I M) (c : ℝ → M)
    {V₁ V₂ : ∀ t, TangentSpace I (c t)} {J₁ J₂ O : Set ℝ} {τ : ℝ}
    (hO : IsOpen O) (hIio : IsParallelSolOn (I := I) g c J₁ V₁)
    (hV₂ : IsParallelSolOn (I := I) g c J₂ V₂)
    (hτO : τ ∈ O) (hO₁ : O ⊆ J₁) (heq : ∀ t ∈ O, V₁ t = V₂ t) :
    ∃ V : ∀ t, TangentSpace I (c t),
      (∀ t, t ≤ τ → V t = V₁ t) ∧ (∀ t, τ ≤ t → V t = V₂ t) ∧
      IsParallelSolOn (I := I) g c ((J₁ ∩ Iio τ) ∪ O ∪ (J₂ ∩ Ioi τ)) V := by
  classical
  refine ⟨fun t => if t ≤ τ then V₁ t else V₂ t, fun t ht => by simp [ht], fun t ht => ?_, ?_⟩
  · rcases eq_or_lt_of_le ht with h | h
    · subst h; simp [heq _ hτO]
    · simp [not_le.mpr h]
  · rintro t ((⟨ht₁, htlt⟩ | htO) | ⟨ht₂, htgt⟩)
    · refine (hIio t ht₁).congr ?_
      filter_upwards [isOpen_Iio.mem_nhds htlt] with s hs
      simp only [mem_Iio] at hs
      simp [le_of_lt hs]
    · refine (hIio t (hO₁ htO)).congr ?_
      filter_upwards [hO.mem_nhds htO] with s hs
      by_cases h : s ≤ τ
      · simp [h]
      · simp [h, heq s hs]
    · refine (hV₂ t ht₂).congr ?_
      filter_upwards [isOpen_Ioi.mem_nhds htgt] with s hs
      simp only [mem_Ioi] at hs
      simp [not_le.mpr hs]

section Chart

variable [I.Boundaryless]

/-- **Math.** Petersen §6.1: the **chart reading of a `Cⁿ` curve is `Cⁿ`** — for any chart `α`
around `c t`, `τ ↦ φ_α(c τ)` is `Cⁿ` at `t`.  This discharges hypothesis `hu` of the chart-local
Theorem 6.1.3 from a single intrinsic smoothness assumption on `c`. -/
theorem contDiffAt_extChartAt_comp {c : ℝ → M} {t : ℝ} {n : WithTop ℕ∞} (hn : n ≤ ∞) (α : M)
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) I n c t) (hsrc : c t ∈ (chartAt H α).source) :
    ContDiffAt ℝ n (fun τ => extChartAt I α (c τ)) t := by
  have h1 : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) (c t) :=
    (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).contMDiffAt
      ((chartAt H α).open_source.mem_nhds hsrc)
  exact contMDiffAt_iff_contDiffAt.mp ((h1.of_le hn).comp t hc)

/-- Continuity and a uniform operator-norm bound for the parallel-transport ODE coefficient
over a compact time interval whose curve piece lies in one chart. -/
theorem continuousOn_and_exists_bound_coeff (g : RiemannianMetric I M) {c : ℝ → M} (α : M)
    {p q : ℝ}
    (hcM : ∀ t ∈ Icc p q, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (hsrc : ∀ t ∈ Icc p q, c t ∈ (chartAt H α).source) :
    ContinuousOn (fun t => chartChristoffelContractionRight (I := I) g α
        (deriv (fun τ => extChartAt I α (c τ)) t) (extChartAt I α (c t))) (Icc p q) ∧
      ∃ K : NNReal, ∀ t ∈ Icc p q, ‖chartChristoffelContractionRight (I := I) g α
        (deriv (fun τ => extChartAt I α (c τ)) t) (extChartAt I α (c t))‖₊ ≤ K := by
  set u : ℝ → E := fun τ => extChartAt I α (c τ) with hu_def
  have h2n : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
  have hu2 : ∀ t ∈ Icc p q, ContDiffAt ℝ 2 u t := fun t ht =>
    contDiffAt_extChartAt_comp h2n α (hcM t ht) (hsrc t ht)
  have hy : ContinuousOn u (Icc p q) := fun t ht => ((hu2 t ht).continuousAt).continuousWithinAt
  have hv : ContinuousOn (deriv u) (Icc p q) := fun t ht =>
    (((hu2 t ht).derivWithin (m := 0) (by norm_num)).continuousAt).continuousWithinAt
  have hmem : ∀ t ∈ Icc p q, u t ∈ (extChartAt I α).target := fun t ht =>
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc t ht)
  have hcont := continuousOn_chartChristoffelContractionRight_comp (I := I) g α hy hv hmem
  refine ⟨hcont, ?_⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨Real.toNNReal C, fun t ht => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact le_max_of_le_left (hC t ht)

/-- Theorem 6.1.3 on **one chart piece**: existence with prescribed value at an interior time
`τ`, on the whole open interval `Ioo p q`, provided the compact piece `c '' Icc p q` lies in the
source of the single chart `α`.  All the hypotheses of the chart-local
`exists_isParallelAlong` are discharged here from `C²`-ness of `c` and compactness. -/
theorem exists_isParallelSolOn_chart (g : RiemannianMetric I M) {c : ℝ → M} (α : M)
    {p q τ : ℝ} (hτ : τ ∈ Ioo p q)
    (hcM : ∀ t ∈ Icc p q, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (hsrc : ∀ t ∈ Icc p q, c t ∈ (chartAt H α).source)
    (w : TangentSpace I (c τ)) :
    ∃ V : ∀ t, TangentSpace I (c t), V τ = w ∧ IsParallelSolOn (I := I) g c (Ioo p q) V := by
  have h2n : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
  have h12 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hsub : Ioo p q ⊆ Icc p q := Ioo_subset_Icc_self
  have hc : ∀ t ∈ Ioo p q, ContinuousAt c t := fun t ht => (hcM t (hsub ht)).continuousAt
  have hsrc' : ∀ t ∈ Ioo p q, c t ∈ (chartAt H α).source := fun t ht => hsrc t (hsub ht)
  have hu : ∀ t ∈ Ioo p q, DifferentiableAt ℝ (fun s => extChartAt I α (c s)) t := fun t ht =>
    (contDiffAt_extChartAt_comp h2n α (hcM t (hsub ht)) (hsrc t (hsub ht))).differentiableAt h12
  obtain ⟨hcont, K, hK⟩ := continuousOn_and_exists_bound_coeff (I := I) g α hcM hsrc
  obtain ⟨V, hVd, hVp, hVτ⟩ := exists_isParallelAlong (I := I) g α hτ hc hsrc' hu hcont hK w
  refine ⟨V, hVτ, fun t ht => ⟨?_, hVp t ht⟩⟩
  exact differentiableAt_chartFieldRep_transfer (I := I) α (c t) (hc t ht) (hsrc' t ht)
    (mem_chart_source H (c t)) (hu t ht) (hVd t ht)

/-- Theorem 6.1.3 on **one chart piece**, uniqueness half. -/
theorem isParallelSolOn_chart_eqOn (g : RiemannianMetric I M) {c : ℝ → M} (α : M)
    {V W : ∀ t, TangentSpace I (c t)} {p q τ : ℝ} (hτ : τ ∈ Ioo p q)
    (hcM : ∀ t ∈ Icc p q, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (hsrc : ∀ t ∈ Icc p q, c t ∈ (chartAt H α).source)
    (hV : IsParallelSolOn (I := I) g c (Ioo p q) V)
    (hW : IsParallelSolOn (I := I) g c (Ioo p q) W)
    (h0 : V τ = W τ) :
    ∀ t ∈ Ioo p q, V t = W t := by
  have h2n : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
  have h12 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hsub : Ioo p q ⊆ Icc p q := Ioo_subset_Icc_self
  have hc : ∀ t ∈ Ioo p q, ContinuousAt c t := fun t ht => (hcM t (hsub ht)).continuousAt
  have hsrc' : ∀ t ∈ Ioo p q, c t ∈ (chartAt H α).source := fun t ht => hsrc t (hsub ht)
  have hu : ∀ t ∈ Ioo p q, DifferentiableAt ℝ (fun s => extChartAt I α (c s)) t := fun t ht =>
    (contDiffAt_extChartAt_comp h2n α (hcM t (hsub ht)) (hsrc t (hsub ht))).differentiableAt h12
  obtain ⟨-, K, hK⟩ := continuousOn_and_exists_bound_coeff (I := I) g α hcM hsrc
  have hufoot : ∀ t ∈ Ioo p q, DifferentiableAt ℝ (fun s => extChartAt I (c t) (c s)) t :=
    fun t ht => (contDiffAt_extChartAt_comp h2n (c t) (hcM t (hsub ht))
      (mem_chart_source H (c t))).differentiableAt h12
  have htrans : ∀ (X : ∀ t, TangentSpace I (c t)), IsParallelSolOn (I := I) g c (Ioo p q) X →
      ∀ t ∈ Ioo p q, DifferentiableAt ℝ (chartFieldRep (I := I) c α X) t := by
    intro X hX t ht
    exact differentiableAt_chartFieldRep_transfer (I := I) (c t) α (hc t ht)
      (mem_chart_source H (c t)) (hsrc' t ht) (hufoot t ht) (hX t ht).1
  exact isParallelAlong_eqOn (I := I) g α hτ hc hsrc' hu hK (htrans V hV) (htrans W hW)
    (fun t ht => (hV t ht).2) (fun t ht => (hW t ht).2) h0

/-! ### The chart cover of a compact curve piece -/

/-- **Math.** Petersen §6.1 (p. 252), the covering step of Theorem 6.1.3: a **Lebesgue number**
for the chart cover of a compact curve piece.  There is a `δ > 0` such that for every time
`t ∈ [a,b]` the whole `δ`-window of `c` around `t` lies in the source of a *single* chart.  This
is what cuts `[a,b]` into pieces on which the chart-local Theorem 6.1.3 applies, and is the same
compactness step Petersen's Ch. 5 uses for its chart polygons. -/
theorem exists_lebesgue_chart (c : ℝ → M) {a b : ℝ}
    (hc : ∀ t ∈ Icc a b, ContinuousAt c t) :
    ∃ δ > 0, ∀ t ∈ Icc a b, ∃ α : M, ∀ s : ℝ, |s - t| < δ → c s ∈ (chartAt H α).source := by
  classical
  have hUopen : ∀ α : M, IsOpen (interior (c ⁻¹' (chartAt H α).source)) :=
    fun _ => isOpen_interior
  have hcov : Icc a b ⊆ ⋃ α : M, interior (c ⁻¹' (chartAt H α).source) := by
    intro t ht
    refine mem_iUnion.mpr ⟨c t, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact (hc t ht).preimage_mem_nhds
      ((chartAt H (c t)).open_source.mem_nhds (mem_chart_source H (c t)))
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hUopen hcov
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨α, hα⟩ := h t ht
  refine ⟨α, fun s hs => ?_⟩
  have hmem : s ∈ interior (c ⁻¹' (chartAt H α).source) :=
    hα (by rwa [Metric.mem_ball, Real.dist_eq])
  have hmem' : s ∈ c ⁻¹' (chartAt H α).source := interior_subset hmem
  exact hmem'

/-! ### Extending a parallel field by one chart piece -/

/-- **Math.** Petersen §6.1 (p. 252), the **walk step** of Theorem 6.1.3, to the right: a
parallel field on `(L, R)` through `t₀` extends to a parallel field on `(L, min b (R + δ/2))`,
keeping its value at `t₀`.  The new piece is solved in the single chart around `c R` supplied by
the Lebesgue number `δ`, and is spliced to the old field at a junction `τ` strictly inside the
overlap, where chart-local uniqueness forces the two to agree. -/
theorem exists_extend_right (g : RiemannianMetric I M) {c : ℝ → M} {a b t₀ δ L R : ℝ}
    (hδ : 0 < δ)
    (hleb : ∀ t ∈ Icc a b, ∃ α : M, ∀ s : ℝ, |s - t| < δ → c s ∈ (chartAt H α).source)
    (hcM : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (haL : a ≤ L) (hLt₀ : L < t₀) (ht₀R : t₀ < R) (hRb : R ≤ b)
    {V : ∀ t, TangentSpace I (c t)} (hV : IsParallelSolOn (I := I) g c (Ioo L R) V) :
    ∃ V' : ∀ t, TangentSpace I (c t), V' t₀ = V t₀ ∧
      IsParallelSolOn (I := I) g c (Ioo L (min b (R + δ / 2))) V' := by
  have hat₀ : a < t₀ := lt_of_le_of_lt haL hLt₀
  have hRab : R ∈ Icc a b := ⟨le_of_lt (lt_trans hat₀ ht₀R), hRb⟩
  obtain ⟨α, hα⟩ := hleb R hRab
  set p : ℝ := max a (R - 3 * δ / 4) with hp
  set q : ℝ := min b (R + 3 * δ / 4) with hq
  set τ : ℝ := max t₀ (R - δ / 4) with hτdef
  have hap : a ≤ p := le_max_left _ _
  have hqb : q ≤ b := min_le_left _ _
  have hpR : R - 3 * δ / 4 ≤ p := le_max_right _ _
  have hRq : q ≤ R + 3 * δ / 4 := min_le_right _ _
  have hsrcpq : ∀ t ∈ Icc p q, c t ∈ (chartAt H α).source := by
    intro t ht
    refine hα t (abs_lt.mpr ⟨?_, ?_⟩) <;> [linarith [ht.1]; linarith [ht.2]]
  have hcMpq : ∀ t ∈ Icc p q, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t := fun t ht =>
    hcM t (Icc_subset_Icc hap hqb ht)
  have hτt₀ : t₀ ≤ τ := le_max_left _ _
  have hτ4 : R - δ / 4 ≤ τ := le_max_right _ _
  have hτR : τ < R := max_lt ht₀R (by linarith)
  have hLτ : L < τ := lt_of_lt_of_le hLt₀ hτt₀
  have hpτ : p < τ := max_lt (lt_of_lt_of_le hat₀ hτt₀) (by linarith)
  have hτq : τ < q := lt_min (lt_of_lt_of_le hτR hRb) (by linarith)
  obtain ⟨W, hWτ, hWsol⟩ :=
    exists_isParallelSolOn_chart (I := I) g α ⟨hpτ, hτq⟩ hcMpq hsrcpq (V τ)
  set x : ℝ := max L p with hxdef
  set y : ℝ := min R q with hydef
  have hxτ : x < τ := max_lt hLτ hpτ
  have hτy : τ < y := lt_min hτR hτq
  have hxy_pq : Icc x y ⊆ Icc p q := Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
  have hxy_LR : Ioo x y ⊆ Ioo L R := Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hxy_pq' : Ioo x y ⊆ Ioo p q := Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have heq : ∀ t ∈ Ioo x y, V t = W t :=
    isParallelSolOn_chart_eqOn (I := I) g α ⟨hxτ, hτy⟩
      (fun t ht => hcMpq t (hxy_pq ht)) (fun t ht => hsrcpq t (hxy_pq ht))
      (hV.mono hxy_LR) (hWsol.mono hxy_pq') hWτ.symm
  obtain ⟨V', hV'l, -, hV'sol⟩ := exists_glue_isParallelSolOn (I := I) g c
    (J₁ := Ioo L R) (J₂ := Ioo p q) (O := Ioo x y) (τ := τ) isOpen_Ioo hV hWsol
    ⟨hxτ, hτy⟩ hxy_LR heq
  refine ⟨V', hV'l t₀ hτt₀, hV'sol.mono ?_⟩
  rintro t ⟨htL, htR⟩
  rcases lt_trichotomy t τ with h | h | h
  · exact Or.inl (Or.inl ⟨⟨htL, lt_trans h hτR⟩, h⟩)
  · exact Or.inl (Or.inr (by rw [h]; exact ⟨hxτ, hτy⟩))
  · have h1 : t < b := lt_of_lt_of_le htR (min_le_left _ _)
    have h2 : t < R + δ / 2 := lt_of_lt_of_le htR (min_le_right _ _)
    exact Or.inr ⟨⟨lt_trans hpτ h, lt_min h1 (by linarith)⟩, h⟩

/-- **Math.** Petersen §6.1 (p. 252), the **walk step** of Theorem 6.1.3, to the left; the mirror
image of `exists_extend_right`, solved in the chart around `c L`. -/
theorem exists_extend_left (g : RiemannianMetric I M) {c : ℝ → M} {a b t₀ δ L R : ℝ}
    (hδ : 0 < δ)
    (hleb : ∀ t ∈ Icc a b, ∃ α : M, ∀ s : ℝ, |s - t| < δ → c s ∈ (chartAt H α).source)
    (hcM : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (haL : a ≤ L) (hLt₀ : L < t₀) (ht₀R : t₀ < R) (hRb : R ≤ b)
    {V : ∀ t, TangentSpace I (c t)} (hV : IsParallelSolOn (I := I) g c (Ioo L R) V) :
    ∃ V' : ∀ t, TangentSpace I (c t), V' t₀ = V t₀ ∧
      IsParallelSolOn (I := I) g c (Ioo (max a (L - δ / 2)) R) V' := by
  have ht₀b : t₀ < b := lt_of_lt_of_le ht₀R hRb
  have hLab : L ∈ Icc a b := ⟨haL, le_of_lt (lt_trans hLt₀ ht₀b)⟩
  obtain ⟨α, hα⟩ := hleb L hLab
  set p : ℝ := max a (L - 3 * δ / 4) with hp
  set q : ℝ := min b (L + 3 * δ / 4) with hq
  set τ : ℝ := min t₀ (L + δ / 4) with hτdef
  have hap : a ≤ p := le_max_left _ _
  have hqb : q ≤ b := min_le_left _ _
  have hpL : L - 3 * δ / 4 ≤ p := le_max_right _ _
  have hLq : q ≤ L + 3 * δ / 4 := min_le_right _ _
  have hsrcpq : ∀ t ∈ Icc p q, c t ∈ (chartAt H α).source := by
    intro t ht
    refine hα t (abs_lt.mpr ⟨?_, ?_⟩) <;> [linarith [ht.1]; linarith [ht.2]]
  have hcMpq : ∀ t ∈ Icc p q, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t := fun t ht =>
    hcM t (Icc_subset_Icc hap hqb ht)
  have hτt₀ : τ ≤ t₀ := min_le_left _ _
  have hτ4 : τ ≤ L + δ / 4 := min_le_right _ _
  have hLτ : L < τ := lt_min hLt₀ (by linarith)
  have hτR : τ < R := lt_of_le_of_lt hτt₀ ht₀R
  have hpτ : p < τ := max_lt (lt_of_le_of_lt haL hLτ) (by linarith)
  have hτq : τ < q := lt_min (lt_of_le_of_lt hτt₀ ht₀b) (by linarith)
  obtain ⟨W, hWτ, hWsol⟩ :=
    exists_isParallelSolOn_chart (I := I) g α ⟨hpτ, hτq⟩ hcMpq hsrcpq (V τ)
  set x : ℝ := max L p with hxdef
  set y : ℝ := min R q with hydef
  have hxτ : x < τ := max_lt hLτ hpτ
  have hτy : τ < y := lt_min hτR hτq
  have hxy_pq : Icc x y ⊆ Icc p q := Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
  have hxy_LR : Ioo x y ⊆ Ioo L R := Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hxy_pq' : Ioo x y ⊆ Ioo p q := Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have heq : ∀ t ∈ Ioo x y, W t = V t :=
    isParallelSolOn_chart_eqOn (I := I) g α ⟨hxτ, hτy⟩
      (fun t ht => hcMpq t (hxy_pq ht)) (fun t ht => hsrcpq t (hxy_pq ht))
      (hWsol.mono hxy_pq') (hV.mono hxy_LR) hWτ
  obtain ⟨V', -, hV'r, hV'sol⟩ := exists_glue_isParallelSolOn (I := I) g c
    (J₁ := Ioo p q) (J₂ := Ioo L R) (O := Ioo x y) (τ := τ) isOpen_Ioo hWsol hV
    ⟨hxτ, hτy⟩ hxy_pq' heq
  refine ⟨V', hV'r t₀ hτt₀, hV'sol.mono ?_⟩
  rintro t ⟨htL, htR⟩
  have h1 : a < t := lt_of_le_of_lt (le_max_left _ _) htL
  have h2 : L - δ / 2 < t := lt_of_le_of_lt (le_max_right _ _) htL
  rcases lt_trichotomy t τ with h | h | h
  · exact Or.inl (Or.inl ⟨⟨max_lt h1 (by linarith), lt_trans h hτq⟩, h⟩)
  · exact Or.inl (Or.inr (by rw [h]; exact ⟨hxτ, hτy⟩))
  · exact Or.inr ⟨⟨lt_trans hLτ h, htR⟩, h⟩

/-! ### Global existence -/

private theorem min_min_add {b X δ : ℝ} (hδ : 0 < δ) :
    min b (min b X + δ / 2) = min b (X + δ / 2) := by
  rcases le_total X b with h | h
  · rw [min_eq_right h]
  · rw [min_eq_left h, min_eq_left (by linarith : b ≤ b + δ / 2),
      min_eq_left (by linarith : b ≤ X + δ / 2)]

private theorem max_max_sub {a Y δ : ℝ} (hδ : 0 < δ) :
    max a (max a Y - δ / 2) = max a (Y - δ / 2) := by
  rcases le_total a Y with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, max_eq_left (by linarith : a - δ / 2 ≤ a),
      max_eq_left (by linarith : Y - δ / 2 ≤ a)]

/-- **Math.** Petersen §6.1 (pp. 252–253), `thm:pet-ch6-parallel-field-existence-uniqueness`
— **Theorem 6.1.3, existence, GLOBAL in the interval**.  For a `C²` curve `c` on a compact time
interval `[a,b]`, a time `t₀ ∈ (a,b)` and `v ∈ T_{c(t₀)}M`, there is a field `V` parallel along
`c` on **all of `(a,b)`** with `V(t₀) = v`.

This is the point of Theorem 6.1.3: the parallel-transport equation is *linear*, so solutions do
not blow up and extend across the whole interval — unlike the nonlinear geodesic equation.  No
single chart is assumed: `c([a,b])` is covered by chart sources, a Lebesgue number `δ`
(`exists_lebesgue_chart`) cuts `[a,b]` into `δ`-windows each inside one chart, the chart-local
Theorem 6.1.3 (`exists_isParallelSolOn_chart`) solves on each, and chart-local uniqueness glues
consecutive pieces (`exists_extend_right`, `exists_extend_left`).  The induction below walks the
window `(max a (t₀ - (n+1)δ/2), min b (t₀ + (n+1)δ/2))` outward from `t₀` until it exhausts
`(a,b)`.  That the glued field really is parallel *across* a junction is exactly the
chart-independence of `V̇` (`covariantDerivCoord_transfer`, §6.1). -/
theorem exists_isParallelSolOn_Ioo (g : RiemannianMetric I M) {c : ℝ → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hcM : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (v : TangentSpace I (c t₀)) :
    ∃ V : ∀ t, TangentSpace I (c t), V t₀ = v ∧ IsParallelSolOn (I := I) g c (Ioo a b) V := by
  obtain ⟨hat₀, ht₀b⟩ := ht₀
  have ht₀ab : t₀ ∈ Icc a b := ⟨hat₀.le, ht₀b.le⟩
  obtain ⟨δ, hδ, hleb⟩ := exists_lebesgue_chart (H := H) c (fun t ht => (hcM t ht).continuousAt)
  have key : ∀ n : ℕ, ∃ V : ∀ t, TangentSpace I (c t), V t₀ = v ∧
      IsParallelSolOn (I := I) g c
        (Ioo (max a (t₀ - ((n : ℝ) + 1) * (δ / 2))) (min b (t₀ + ((n : ℝ) + 1) * (δ / 2)))) V := by
    have hδ2 : 0 < δ / 2 := by linarith
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_add, one_mul]
      obtain ⟨α, hα⟩ := hleb t₀ ht₀ab
      have hap : a ≤ max a (t₀ - δ / 2) := le_max_left _ _
      have hqb : min b (t₀ + δ / 2) ≤ b := min_le_left _ _
      have hL : t₀ - δ / 2 ≤ max a (t₀ - δ / 2) := le_max_right _ _
      have hR : min b (t₀ + δ / 2) ≤ t₀ + δ / 2 := min_le_right _ _
      have hLt₀ : max a (t₀ - δ / 2) < t₀ := max_lt hat₀ (by linarith)
      have ht₀R : t₀ < min b (t₀ + δ / 2) := lt_min ht₀b (by linarith)
      have hsrc : ∀ t ∈ Icc (max a (t₀ - δ / 2)) (min b (t₀ + δ / 2)),
          c t ∈ (chartAt H α).source := by
        intro t ht
        refine hα t (abs_lt.mpr ⟨?_, ?_⟩) <;> [linarith [ht.1]; linarith [ht.2]]
      exact exists_isParallelSolOn_chart (I := I) g α ⟨hLt₀, ht₀R⟩
        (fun t ht => hcM t (Icc_subset_Icc hap hqb ht)) hsrc v
    | succ n ih =>
      obtain ⟨V, hVt₀, hVsol⟩ := ih
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      set L : ℝ := max a (t₀ - ((n : ℝ) + 1) * (δ / 2)) with hLdef
      set R : ℝ := min b (t₀ + ((n : ℝ) + 1) * (δ / 2)) with hRdef
      have haL : a ≤ L := le_max_left _ _
      have hRb : R ≤ b := min_le_left _ _
      have hLt₀ : L < t₀ := max_lt hat₀ (by nlinarith)
      have ht₀R : t₀ < R := lt_min ht₀b (by nlinarith)
      obtain ⟨V₁, hV₁t₀, hV₁sol⟩ :=
        exists_extend_right (I := I) g hδ hleb hcM haL hLt₀ ht₀R hRb hVsol
      set R₁ : ℝ := min b (R + δ / 2) with hR₁def
      have hR₁b : R₁ ≤ b := min_le_left _ _
      have ht₀R₁ : t₀ < R₁ := lt_min ht₀b (by linarith)
      obtain ⟨V₂, hV₂t₀, hV₂sol⟩ :=
        exists_extend_left (I := I) g hδ hleb hcM haL hLt₀ ht₀R₁ hR₁b hV₁sol
      have hmin : R₁ = min b (t₀ + ((n : ℝ) + 1 + 1) * (δ / 2)) := by
        rw [hR₁def, hRdef, min_min_add hδ]; ring_nf
      have hmax : max a (L - δ / 2) = max a (t₀ - ((n : ℝ) + 1 + 1) * (δ / 2)) := by
        rw [hLdef, max_max_sub hδ]; ring_nf
      refine ⟨V₂, by rw [hV₂t₀, hV₁t₀, hVt₀], ?_⟩
      push_cast
      rw [← hmax, ← hmin]
      exact hV₂sol
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / (δ / 2))
  obtain ⟨V, hVt₀, hVsol⟩ := key N
  have hδ2 : 0 < δ / 2 := by linarith
  rw [div_lt_iff₀ hδ2] at hN
  have hN1 : b - a < ((N : ℝ) + 1) * (δ / 2) := by nlinarith
  rw [max_eq_left (by linarith : t₀ - ((N : ℝ) + 1) * (δ / 2) ≤ a),
    min_eq_left (by linarith : b ≤ t₀ + ((N : ℝ) + 1) * (δ / 2))] at hVsol
  exact ⟨V, hVt₀, hVsol⟩

/-! ### Global uniqueness -/

/-- **Math.** Petersen §6.1 (p. 252), `thm:pet-ch6-parallel-field-existence-uniqueness`
— **Theorem 6.1.3, uniqueness, GLOBAL in the interval**.  Two fields parallel along `c` on all of
`(a,b)` that agree at one time `t₀` agree throughout `(a,b)`.

Proof: chart-local uniqueness (`isParallelSolOn_chart_eqOn`) says that on each `δ`-window
agreement at *one* point propagates to *every* point of the window; so both the agreement locus
and its complement are open in `(a,b)`, and `(a,b)` is connected. -/
theorem isParallelSolOn_eqOn_Ioo (g : RiemannianMetric I M) {c : ℝ → M}
    {V W : ∀ t, TangentSpace I (c t)} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hcM : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (hV : IsParallelSolOn (I := I) g c (Ioo a b) V)
    (hW : IsParallelSolOn (I := I) g c (Ioo a b) W)
    (h0 : V t₀ = W t₀) :
    ∀ t ∈ Ioo a b, V t = W t := by
  classical
  obtain ⟨δ, hδ, hleb⟩ := exists_lebesgue_chart (H := H) c (fun t ht => (hcM t ht).continuousAt)
  -- On a `δ`-window, agreement at one time propagates to the whole window.
  have hlocal : ∀ t₁ ∈ Ioo a b, ∃ p q : ℝ, t₁ ∈ Ioo p q ∧ Ioo p q ⊆ Ioo a b ∧
      ∀ s₁ ∈ Ioo p q, V s₁ = W s₁ → ∀ s₂ ∈ Ioo p q, V s₂ = W s₂ := by
    intro t₁ ht₁
    obtain ⟨α, hα⟩ := hleb t₁ ⟨ht₁.1.le, ht₁.2.le⟩
    have hap : a ≤ max a (t₁ - δ / 2) := le_max_left _ _
    have hqb : min b (t₁ + δ / 2) ≤ b := min_le_left _ _
    have hL : t₁ - δ / 2 ≤ max a (t₁ - δ / 2) := le_max_right _ _
    have hR : min b (t₁ + δ / 2) ≤ t₁ + δ / 2 := min_le_right _ _
    have hsub : Ioo (max a (t₁ - δ / 2)) (min b (t₁ + δ / 2)) ⊆ Ioo a b :=
      Ioo_subset_Ioo hap hqb
    have hsrc : ∀ t ∈ Icc (max a (t₁ - δ / 2)) (min b (t₁ + δ / 2)),
        c t ∈ (chartAt H α).source := by
      intro t ht
      refine hα t (abs_lt.mpr ⟨?_, ?_⟩) <;> [linarith [ht.1]; linarith [ht.2]]
    refine ⟨max a (t₁ - δ / 2), min b (t₁ + δ / 2),
      ⟨max_lt ht₁.1 (by linarith), lt_min ht₁.2 (by linarith)⟩, hsub, fun s₁ hs₁ heq => ?_⟩
    exact isParallelSolOn_chart_eqOn (I := I) g α hs₁
      (fun t ht => hcM t (Icc_subset_Icc hap hqb ht)) hsrc (hV.mono hsub) (hW.mono hsub) heq
  -- The agreement locus and its complement are both open, and `Ioo a b` is connected.
  set U : Set ℝ := {t | ∃ p q : ℝ, t ∈ Ioo p q ∧ ∀ s ∈ Ioo p q, s ∈ Ioo a b → V s = W s} with hU
  set N : Set ℝ := {t | ∃ p q : ℝ, t ∈ Ioo p q ∧ ∀ s ∈ Ioo p q, s ∈ Ioo a b → V s ≠ W s} with hN
  have hUopen : IsOpen U := by
    refine isOpen_iff_mem_nhds.mpr fun t ⟨p, q, htpq, hpq⟩ => ?_
    exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds htpq) fun s hs => ⟨p, q, hs, hpq⟩
  have hNopen : IsOpen N := by
    refine isOpen_iff_mem_nhds.mpr fun t ⟨p, q, htpq, hpq⟩ => ?_
    exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds htpq) fun s hs => ⟨p, q, hs, hpq⟩
  have hcover : Ioo a b ⊆ U ∪ N := by
    intro t₁ ht₁
    obtain ⟨p, q, htpq, hpqsub, hprop⟩ := hlocal t₁ ht₁
    by_cases h : ∃ s ∈ Ioo p q, V s = W s
    · obtain ⟨s, hs, hsw⟩ := h
      exact Or.inl ⟨p, q, htpq, fun s' hs' _ => hprop s hs hsw s' hs'⟩
    · push Not at h
      exact Or.inr ⟨p, q, htpq, fun s' hs' _ => h s' hs'⟩
  have hUne : (Ioo a b ∩ U).Nonempty := by
    obtain ⟨p, q, htpq, -, hprop⟩ := hlocal t₀ ht₀
    exact ⟨t₀, ht₀, p, q, htpq, fun s' hs' _ => hprop t₀ htpq h0 s' hs'⟩
  have hdisj : ¬ (Ioo a b ∩ (U ∩ N)).Nonempty := by
    rintro ⟨t, ht, ⟨p, q, htpq, hpq⟩, ⟨p', q', htpq', hpq'⟩⟩
    exact hpq' t htpq' ht (hpq t htpq ht)
  have hNempty : ¬ (Ioo a b ∩ N).Nonempty := fun hne =>
    hdisj (isPreconnected_Ioo U N hUopen hNopen hcover hUne hne)
  intro t ht
  rcases hcover ht with h | h
  · obtain ⟨p, q, htpq, hpq⟩ := h
    exact hpq t htpq ht
  · exact absurd ⟨t, ht, h⟩ hNempty

/-! ### Theorem 6.1.3, global form -/

/-- **Math.** Petersen §6.1 (p. 252), `thm:pet-ch6-parallel-field-existence-uniqueness`
— **Theorem 6.1.3**, in its global form: *"if `t₀ ∈ I` and `v ∈ T_{c(t₀)}M`, then there is a
unique parallel field `V` defined on all of `I` with `V(t₀) = v`."*

Here `I = (a,b)`, `c` is `C²` on the compact closure `[a,b]`, and — unlike the chart-local
`parallelField_existence_uniqueness` of `Ch06/ConnectionAlongCurve` — **no chart hypothesis is
made**: the curve may leave every chart, and does so as soon as `I` is long.  Global existence on
the whole of `I` is the whole point of the theorem, and is what separates the *linear*
parallel-transport equation from the nonlinear geodesic equation, whose solutions only exist
locally.

Uniqueness is stated as `EqOn` on `(a,b)` rather than as `∃!` because a field along `c` is
unconstrained off the interval.  The regularity clause inside `IsParallelSolOn` is not removable:
`derivAlongCurve` is defined through `deriv`, junk `0` off the differentiability locus, so
`V̇ ≡ 0` alone does not force `V` to be `C¹` (Petersen leaves the smoothness of his fields
implicit). -/
theorem parallelField_existence_uniqueness_global (g : RiemannianMetric I M) {c : ℝ → M}
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hcM : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (v : TangentSpace I (c t₀)) :
    ∃ V : ∀ t, TangentSpace I (c t),
      IsParallelSolOn (I := I) g c (Ioo a b) V ∧ V t₀ = v ∧
      ∀ W : ∀ t, TangentSpace I (c t), IsParallelSolOn (I := I) g c (Ioo a b) W → W t₀ = v →
        ∀ t ∈ Ioo a b, W t = V t := by
  obtain ⟨V, hVt₀, hVsol⟩ := exists_isParallelSolOn_Ioo (I := I) g ht₀ hcM v
  exact ⟨V, hVsol, hVt₀, fun W hWsol hWt₀ =>
    isParallelSolOn_eqOn_Ioo (I := I) g ht₀ hcM hWsol hVsol (by rw [hWt₀, hVt₀])⟩

/-! ### Petersen's hypothesis verbatim: `c` smooth on the open interval only -/

/-- **Math.** Petersen §6.1 (p. 252), **Theorem 6.1.3 with Petersen's hypothesis verbatim**:
`c` is only assumed `C²` on the *open* interval `I = (a,b)` — no regularity at the endpoints,
which may well be points where `c` degenerates or leaves the manifold.

`(a,b)` is exhausted by the compact subintervals `[Aₙ, Bₙ] ⊆ (a,b)` with `Aₙ ↓ a`, `Bₙ ↑ b`, all
containing `t₀`.  `exists_isParallelSolOn_Ioo` solves on each, global uniqueness on the smaller
window forces the solutions to cohere, and the coherent limit is the field on all of `(a,b)`. -/
theorem exists_isParallelSolOn_Ioo_of_openHyp (g : RiemannianMetric I M) {c : ℝ → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hcM : ∀ t ∈ Ioo a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (v : TangentSpace I (c t₀)) :
    ∃ V : ∀ t, TangentSpace I (c t), V t₀ = v ∧ IsParallelSolOn (I := I) g c (Ioo a b) V := by
  classical
  obtain ⟨hat₀, ht₀b⟩ := ht₀
  have hpa : (0 : ℝ) < t₀ - a := by linarith
  have hpb : (0 : ℝ) < b - t₀ := by linarith
  set A : ℕ → ℝ := fun n => a + (t₀ - a) / ((n : ℝ) + 2) with hAdef
  set B : ℕ → ℝ := fun n => b - (b - t₀) / ((n : ℝ) + 2) with hBdef
  have hn2 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hAa : ∀ n, a < A n := fun n => by
    have := div_pos hpa (hn2 n); simp only [hAdef]; linarith
  have hAt₀ : ∀ n, A n < t₀ := fun n => by
    have h : (t₀ - a) / ((n : ℝ) + 2) < t₀ - a := by
      rw [div_lt_iff₀ (hn2 n)]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simp only [hAdef]; linarith
  have hBb : ∀ n, B n < b := fun n => by
    have := div_pos hpb (hn2 n); simp only [hBdef]; linarith
  have ht₀B : ∀ n, t₀ < B n := fun n => by
    have h : (b - t₀) / ((n : ℝ) + 2) < b - t₀ := by
      rw [div_lt_iff₀ (hn2 n)]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simp only [hBdef]; linarith
  have hsubIcc : ∀ n, Icc (A n) (B n) ⊆ Ioo a b := fun n =>
    fun t ht => ⟨lt_of_lt_of_le (hAa n) ht.1, lt_of_le_of_lt ht.2 (hBb n)⟩
  have hmono : ∀ m n : ℕ, m ≤ n → Ioo (A m) (B m) ⊆ Ioo (A n) (B n) := by
    intro m n hmn
    have hcast : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
    refine Ioo_subset_Ioo ?_ ?_
    · simp only [hAdef]
      have : (t₀ - a) / ((n : ℝ) + 2) ≤ (t₀ - a) / ((m : ℝ) + 2) := by gcongr
      linarith
    · simp only [hBdef]
      have : (b - t₀) / ((n : ℝ) + 2) ≤ (b - t₀) / ((m : ℝ) + 2) := by gcongr
      linarith
  -- every time of `(a,b)` is caught by some window
  have hcatch : ∀ t ∈ Ioo a b, ∃ n : ℕ, t ∈ Ioo (A n) (B n) := by
    rintro t ⟨hta, htb⟩
    obtain ⟨N, hN⟩ := exists_nat_gt (max ((t₀ - a) / (t - a)) ((b - t₀) / (b - t)))
    have hNa : (t₀ - a) / (t - a) < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
    have hNb : (b - t₀) / (b - t) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
    refine ⟨N, ?_, ?_⟩
    · have h1 : (t₀ - a) / ((N : ℝ) + 2) < t - a := by
        rw [div_lt_iff₀ (hn2 N), ← div_lt_iff₀' (by linarith : (0 : ℝ) < t - a)]
        linarith
      simp only [hAdef]; linarith
    · have h1 : (b - t₀) / ((N : ℝ) + 2) < b - t := by
        rw [div_lt_iff₀ (hn2 N), ← div_lt_iff₀' (by linarith : (0 : ℝ) < b - t)]
        linarith
      simp only [hBdef]; linarith
  -- solve on every window
  choose Vs hVs0 hVs using fun n : ℕ =>
    exists_isParallelSolOn_Ioo (I := I) g (⟨hAt₀ n, ht₀B n⟩ : t₀ ∈ Ioo (A n) (B n))
      (fun t ht => hcM t (hsubIcc n ht)) v
  -- windows cohere, by global uniqueness on the smaller one
  have hcoh : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Ioo (A m) (B m), Vs n t = Vs m t := fun m n hmn =>
    isParallelSolOn_eqOn_Ioo (I := I) g ⟨hAt₀ m, ht₀B m⟩
      (fun t ht => hcM t (hsubIcc m ht)) ((hVs n).mono (hmono m n hmn)) (hVs m)
      (by rw [hVs0 n, hVs0 m])
  refine ⟨fun t => if h : ∃ n : ℕ, t ∈ Ioo (A n) (B n) then Vs (Nat.find h) t else Vs 0 t, ?_, ?_⟩
  · have h0 : ∃ n : ℕ, t₀ ∈ Ioo (A n) (B n) := ⟨0, hAt₀ 0, ht₀B 0⟩
    exact (dif_pos h0).trans (hVs0 _)
  · have key : ∀ (n : ℕ), ∀ t ∈ Ioo (A n) (B n),
        (if h : ∃ m : ℕ, t ∈ Ioo (A m) (B m) then Vs (Nat.find h) t else Vs 0 t) = Vs n t := by
      intro n t ht
      have h : ∃ m : ℕ, t ∈ Ioo (A m) (B m) := ⟨n, ht⟩
      rw [dif_pos h]
      exact (hcoh (Nat.find h) n (Nat.find_le ht) t (Nat.find_spec h)).symm
    intro t ht
    obtain ⟨n, hn⟩ := hcatch t ht
    refine (hVs n t hn).congr ?_
    filter_upwards [isOpen_Ioo.mem_nhds hn] with s hs using (key n s hs).symm

/-- **Math.** Petersen §6.1 (p. 252), `thm:pet-ch6-parallel-field-existence-uniqueness`
— **Theorem 6.1.3 on an arbitrary bounded open interval**, with Petersen's hypothesis verbatim:
`c` is `C²` on `I = (a,b)` only.  For `t₀ ∈ I` and `v ∈ T_{c(t₀)}M` there is a unique parallel
field `V` along `c` defined on all of `I` with `V(t₀) = v`. -/
theorem parallelField_existence_uniqueness_interval (g : RiemannianMetric I M) {c : ℝ → M}
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hcM : ∀ t ∈ Ioo a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (v : TangentSpace I (c t₀)) :
    ∃ V : ∀ t, TangentSpace I (c t),
      IsParallelSolOn (I := I) g c (Ioo a b) V ∧ V t₀ = v ∧
      ∀ W : ∀ t, TangentSpace I (c t), IsParallelSolOn (I := I) g c (Ioo a b) W → W t₀ = v →
        ∀ t ∈ Ioo a b, W t = V t := by
  obtain ⟨V, hVt₀, hVsol⟩ := exists_isParallelSolOn_Ioo_of_openHyp (I := I) g ht₀ hcM v
  refine ⟨V, hVsol, hVt₀, fun W hWsol hWt₀ t ht => ?_⟩
  -- uniqueness is local, so the interior hypothesis suffices: work on a compact window at `t`
  obtain ⟨ε, hε, hsub⟩ : ∃ ε > 0, Icc (min t t₀ - ε) (max t t₀ + ε) ⊆ Ioo a b := by
    refine ⟨min (min t t₀ - a) (b - max t t₀) / 2, by
      have h1 : a < min t t₀ := lt_min ht.1 ht₀.1
      have h2 : max t t₀ < b := max_lt ht.2 ht₀.2
      positivity, fun s hs => ?_⟩
    have h1 : a < min t t₀ := lt_min ht.1 ht₀.1
    have h2 : max t t₀ < b := max_lt ht.2 ht₀.2
    have h3 : min (min t t₀ - a) (b - max t t₀) ≤ min t t₀ - a := min_le_left _ _
    have h4 : min (min t t₀ - a) (b - max t t₀) ≤ b - max t t₀ := min_le_right _ _
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmem : ∀ s, s ∈ Ioo (min t t₀ - ε) (max t t₀ + ε) → s ∈ Ioo a b := fun s hs =>
    hsub ⟨hs.1.le, hs.2.le⟩
  have ht₀win : t₀ ∈ Ioo (min t t₀ - ε) (max t t₀ + ε) :=
    ⟨by linarith [min_le_right t t₀], by linarith [le_max_right t t₀]⟩
  refine isParallelSolOn_eqOn_Ioo (I := I) g ht₀win
    (fun s hs => hcM s (hsub hs)) (fun s hs => hWsol s (hmem s hs))
    (fun s hs => hVsol s (hmem s hs)) (by rw [hWt₀, hVt₀]) t
    ⟨by linarith [min_le_left t t₀], by linarith [le_max_left t t₀]⟩

/-! ### Parallel orthonormal frames -/

/-- **Math.** An orthonormal frame at one point of a `C²` curve extends to a
parallel orthonormal frame on the whole bounded open interval.  Existence is
Theorem 6.1.3 applied to every seed vector.  Metric compatibility says that the
inner product of any two transported fields has zero derivative; connectedness
of the interval then makes every Gram entry constant. -/
theorem exists_parallelOrthonormalFrameOn_Ioo
    (g : RiemannianMetric I M) {c : ℝ → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hcM : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 c t)
    (e₀ : Fin (Module.finrank ℝ E) → TangentSpace I (c t₀))
    (horth₀ : ∀ i j, g.metricInner (c t₀) (e₀ i) (e₀ j) =
      if i = j then (1 : ℝ) else 0) :
    ∃ e : Fin (Module.finrank ℝ E) → (∀ t, TangentSpace I (c t)),
      (∀ i, e i t₀ = e₀ i) ∧
      (∀ i, IsParallelSolOn (I := I) g c (Ioo a b) (e i)) ∧
      (∀ t ∈ Ioo a b, ∀ i j,
        g.metricInner (c t) (e i t) (e j t) = if i = j then (1 : ℝ) else 0) := by
  classical
  have h2n : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
  have hcIcc : ∀ t ∈ Ioo a b, t ∈ Icc a b := fun t ht =>
    ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  choose e heSol he0 _ using fun i : Fin (Module.finrank ℝ E) =>
    parallelField_existence_uniqueness_interval (I := I) g ht₀
      (fun s hs => hcM s (hcIcc s hs)) (e₀ i)
  refine ⟨e, (fun i => he0 i), heSol, ?_⟩
  intro t ht i j
  let φ : ℝ → ℝ := fun s => g.inner (c s) (e i s) (e j s)
  have hpair : ∀ s ∈ Ioo a b, HasDerivAt φ 0 s := by
    intro s hs
    have hct : ContinuousAt c s := (hcM s (hcIcc s hs)).continuousAt
    have hsrc : c s ∈ (chartAt H (c s)).source := mem_chart_source H (c s)
    have hu : DifferentiableAt ℝ (fun r => extChartAt I (c s) (c r)) s := by
      exact ((contDiffAt_extChartAt_comp (I := I) h2n (c s)
        (hcM s (hcIcc s hs)) hsrc).differentiableAt (by norm_num))
    have hG : ∀ k l, DifferentiableAt ℝ (chartGramOnE (I := I) g (c s) k l)
        (extChartAt I (c s) (c s)) := by
      intro k l
      exact ((chartGramOnE_contDiffOn (I := I) g (c s) k l).contDiffAt
        (extChartAt_target_mem_nhds' (I := I) ((extChartAt I (c s)).map_source (by
          rw [extChartAt_source]
          exact hsrc)))).differentiableAt (by norm_num)
    have hprod := hasDerivAt_inner_eq_zero_of_isParallelAlong (I := I) g (c s)
      hct hsrc hu (heSol i s hs).1 (heSol j s hs).1 hG
      (heSol i s hs).2 (heSol j s hs).2
    simpa [φ] using hprod
  have hconst : φ t = φ t₀ :=
    (convex_iff_ordConnected.mpr Set.ordConnected_Ioo).is_const_of_fderivWithin_eq_zero
      (fun s hs => (hpair s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [fderivWithin_of_isOpen isOpen_Ioo hs]
        simpa only [ContinuousLinearMap.toSpanSingleton_zero] using
          (hpair s hs).hasFDerivAt.fderiv)
      ht ht₀
  change φ t = if i = j then (1 : ℝ) else 0
  rw [hconst]
  change g.metricInner (c t₀) (e i t₀) (e j t₀) = if i = j then (1 : ℝ) else 0
  rw [he0 i, he0 j, horth₀]

end Chart

end PetersenLib

end
