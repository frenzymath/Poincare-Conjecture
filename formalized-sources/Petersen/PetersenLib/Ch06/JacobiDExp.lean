import PetersenLib.Ch06.VariationTransfers
import PetersenLib.Riemannian.Jacobi.ChartCurvatureVector
import PetersenLib.Ch05.NormalCoordinatesRate
import PetersenLib.Riemannian.Exponential.RayGeodesic

/-!
# Petersen Ch. 6, §6.1 — Jacobi fields and the differential of `exp_p`

Petersen §6.1 (p. 254), `rem:pet-ch6-jacobi-dexp-relation`: the Jacobi fields along a geodesic
`c(t) = exp_p(t v)` that vanish at `p` are exactly the variation fields of the **geodesic
variation** `c̄(s,t) = exp_p(t(v + s w))`.  Differentiating in `s` at `0`, the chain rule gives
`J(t) = D\exp_p|_{tv}(t w)`, so `D\exp_p` is nonsingular at `t_0 v` iff every prescribed
`J(t_0)` is realized by such a Jacobi field.

The mathematical core is the classical fact — Petersen's `def:pet-ch6-jacobi-field` — that **the
variation field of a family of geodesics is a Jacobi field**.  This project already carries that
computation in coordinates: `Jacobi.chart_geodesic_family_jacobi`
(`Riemannian/Jacobi/ChartCurvatureVector.lean`) is Morgan–Tian's derivation of the Jacobi
equation `∇_t∇_t Y + ℛ(Y, ∂_t u)∂_t u = 0` from a chart family `u` of geodesics, and
`Ch06/JacobiChartBridge.lean`'s `isJacobiFieldAlongOn_Ioo_of_isJacobiFieldOn` transports a chart
pair solution back to Petersen's chart-free `IsJacobiFieldAlong`.  The velocity-transfer
dictionary of `Ch06/VariationTransfers.lean` (`variationField_eq_tangentCoordChange`) then names
the transported field as `variationField c̄`.

## Why the fixed basepoint makes this reachable

Unlike §6.3's Bonnet–Synge variation `exp_{c(t)}(sV(t))` — whose basepoint *moves* and whose
chart-escape radius has no locally uniform lower bound — the D-`exp` variation has a **fixed
basepoint** `p`.  Its joint smoothness on a slab is therefore immediate from
`Exponential.exists_contDiffOn_infty_extChartAt_expMap_ball` (the chart reading of `exp_p` is
`C^∞` on a ball), with none of the moving-foot uniform-radius machinery.  The base geodesic and
all nearby rays stay in the single chart at `p` for small time, so one fixed chart `α = p`
suffices and the whole `JacobiChartBridge` dictionary applies.

## Main results

* `isJacobiFieldAlong_variationField_of_geodesicFamily` — **the general fact**: the variation
  field of a family of geodesics (a variation `f` whose coordinate reading in one chart is `C³`
  on an open slab, staying in the chart, with every `t`-line a geodesic) is a Jacobi field along
  the base curve on the open time interval.  This is the manifold form of
  `Jacobi.chart_geodesic_family_jacobi`.
* `jacobiField_dexp_relation` — Petersen's remark: the specialization to `c̄(s,t) = exp_p(t(v+sw))`.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor PetersenLib.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  [T2Space (TangentBundle I M)]

/-! ### The `covDerivAlong` of a family, restricted to the base slice, is `covariantDerivCoord` -/

/-- **Eng.** The Jacobi engine's covariant derivative `covDerivAlong (chartChristoffelBilin g α)`
of a 2-parameter field `Y` in the time direction `(0,1)`, evaluated on the base slice `s = 0`, is
the coordinate covariant derivative `covariantDerivCoord g α` of the slice curve.  Both are
`deriv + Γ`; the only content is that the surface partial `∂_t Y = fderiv Y · (0,1)` restricted to
the slice is the slice's plain `t`-derivative (`Jacobi.hasDerivAt_comp_snd`), and that
`chartChristoffelBilin` is `chartChristoffelContraction` (`chartChristoffelBilin_apply`). -/
theorem covDerivAlong_snd_slice_eq_covariantDerivCoord (g : RiemannianMetric I M) (α : M)
    (c Y : ℝ × ℝ → E) {τ : ℝ} (hc : DifferentiableAt ℝ c (0, τ))
    (hY : DifferentiableAt ℝ Y (0, τ)) :
    covDerivAlong (chartChristoffelBilin (I := I) g α) c Y ((0, 1) : ℝ × ℝ) (0, τ)
      = covariantDerivCoord (I := I) g α (fun r => c (0, r)) (fun r => Y (0, r)) τ := by
  rw [covDerivAlong_def, covariantDerivCoord_def, chartChristoffelBilin_apply]
  rw [(Jacobi.hasDerivAt_comp_snd hc.hasFDerivAt).deriv,
    (Jacobi.hasDerivAt_comp_snd hY.hasFDerivAt).deriv]

/-- **Eng.** The geodesic hypothesis `hgeo` of
`isJacobiFieldAlongOn_variationField_of_geodesicFamily` — the Jacobi engine's
`covDerivAlong Γ c (∂_t c) (0,1)` — is definitionally the second-variation machinery's
`mixedPartialCoord g α c q (0,1) (0,1)`.  Both are `∂_t∂_t c + Γ(∂_t c, ∂_t c)(c)`; this is the
bridge that lets a caller supply the geodesic hypothesis through
`mixedPartialCoord_snd_snd_eq_zero_of_isGeodesic` (i.e. from `curveAcceleration = 0`). -/
theorem covDerivAlong_snd_snd_eq_mixedPartialCoord (g : RiemannianMetric I M) (α : M)
    (c : ℝ × ℝ → E) (q : ℝ × ℝ) :
    covDerivAlong (chartChristoffelBilin (I := I) g α) c
        (fun r => fderiv ℝ c r ((0, 1) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) q
      = mixedPartialCoord (I := I) g α c q ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
  rw [covDerivAlong_def, mixedPartialCoord_def, chartChristoffelBilin_apply]

/-! ### Smoothness of the `s = 0` slice -/

/-- **Eng.** The `s = 0` slice `r ↦ h(0,r)` of a `C^n` map on an open slab
`Ioo (-δ) δ ×ˢ Ioo a b` is `C^n` on `Ioo a b` — composition with the smooth line
`r ↦ (0, r)`, which maps `Ioo a b` into the slab since `0 ∈ Ioo (-δ) δ`. -/
theorem contDiffOn_slice_zero {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {h : ℝ × ℝ → G} {n : WithTop ℕ∞} {δ a b : ℝ} (hδ : 0 < δ)
    (hh : ContDiffOn ℝ n h (Ioo (-δ) δ ×ˢ Ioo a b)) :
    ContDiffOn ℝ n (fun r => h (0, r)) (Ioo a b) :=
  hh.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun r hr => ⟨⟨neg_lt_zero.mpr hδ, hδ⟩, hr⟩)

/-! ### The coordinate Jacobi equation for a family of geodesics -/

/-- **Math.** Morgan–Tian's Jacobi equation for the variation field of a chart family of
geodesics, transported into the `covariantDerivCoord`/`chartCurvature` vocabulary of the pair
system.  Given a `C³` chart family `c` on an open slab, staying in the chart target interior, all
of whose `t`-lines are geodesics (`hgeo`, the coordinate geodesic equation
`covDerivAlong Γ c (∂_t c) (0,1) = 0`), the coordinate variation field `Jα = ∂_s c(0,·)` satisfies
`∇∇Jα = −ℛ(Jα, ċ)ċ` along the base curve `u = c(0,·)`.

This is `Jacobi.chart_geodesic_family_jacobi` (Morgan–Tian's computation) with its two
`covDerivAlong … (0,1)` layers rewritten on the `s = 0` slice as `covariantDerivCoord` via
`covDerivAlong_snd_slice_eq_covariantDerivCoord`. -/
theorem covariantDerivCoord_snd_variationField_eq_neg_chartCurvature
    (g : RiemannianMetric I M) (α : M) {c : ℝ × ℝ → E} {δ a b t : ℝ}
    (hδ : 0 < δ) (ht : t ∈ Ioo a b)
    (hc : ContDiffOn ℝ 3 c (Ioo (-δ) δ ×ˢ Ioo a b))
    (hmem : ∀ q ∈ Ioo (-δ) δ ×ˢ Ioo a b, c q ∈ interior (extChartAt I α).target)
    (hgeo : ∀ q ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      covDerivAlong (chartChristoffelBilin (I := I) g α) c
        (fun r => fderiv ℝ c r ((0, 1) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) q = 0) :
    covariantDerivCoord (I := I) g α (fun r => c (0, r))
        (fun r => covariantDerivCoord (I := I) g α (fun r' => c (0, r'))
          (fun r' => fderiv ℝ c (0, r') ((1, 0) : ℝ × ℝ)) r) t
      = -(chartCurvature (I := I) g α (c (0, t)) (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ))
          (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))) := by
  set S : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Ioo a b with hSdef
  have hSopen : IsOpen S := isOpen_Ioo.prod isOpen_Ioo
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hpt : ((0 : ℝ), t) ∈ S := ⟨h0mem, ht⟩
  -- the intermediate field `∂_s c` and the first covariant derivative field `Y`
  set Ds : ℝ × ℝ → E := fun r => fderiv ℝ c r ((1, 0) : ℝ × ℝ) with hDsdef
  set Y : ℝ × ℝ → E := fun q =>
    covDerivAlong (chartChristoffelBilin (I := I) g α) c Ds ((0, 1) : ℝ × ℝ) q with hYdef
  -- smoothness scaffolding
  have hc2 : ContDiffOn ℝ 2 (fderiv ℝ c) S := hc.fderiv_of_isOpen hSopen (by norm_num)
  have hDs_cd : ContDiffOn ℝ 2 Ds S := hc2.clm_apply contDiffOn_const
  have hDt_cd : ContDiffOn ℝ 2 (fun q => fderiv ℝ c q ((0, 1) : ℝ × ℝ)) S :=
    hc2.clm_apply contDiffOn_const
  have hmemtgt : ∀ q ∈ S, c q ∈ (extChartAt I α).target := fun q hq => interior_subset (hmem q hq)
  -- `Y` is `C¹`: the `fderiv (∂_s c)` layer is `C¹`, the Christoffel layer `C²`
  have hYlin : ContDiffOn ℝ 1 (fun q => fderiv ℝ Ds q ((0, 1) : ℝ × ℝ)) S :=
    (hDs_cd.fderiv_of_isOpen hSopen (by norm_num)).clm_apply contDiffOn_const
  have hYchr : ContDiffOn ℝ 1
      (fun q => Geodesic.chartChristoffelContraction (I := I) g α
        (fderiv ℝ c q ((0, 1) : ℝ × ℝ)) (Ds q) (c q)) S :=
    contDiffOn_chartChristoffelContraction_comp (I := I) g α (by decide)
      (hc.of_le (by decide)) (hDt_cd.of_le (by decide)) (hDs_cd.of_le (by decide)) hmemtgt
  have hY_cd : ContDiffOn ℝ 1 Y S := by
    have hEq : Y = fun q => fderiv ℝ Ds q ((0, 1) : ℝ × ℝ)
        + Geodesic.chartChristoffelContraction (I := I) g α
            (fderiv ℝ c q ((0, 1) : ℝ × ℝ)) (Ds q) (c q) := by
      funext q
      simp only [hYdef, covDerivAlong_def, chartChristoffelBilin_apply]
    rw [hEq]; exact hYlin.add hYchr
  -- differentiability facts at slab points
  have hcdiff : ∀ q ∈ S, DifferentiableAt ℝ c q := fun q hq =>
    (hc.contDiffAt (hSopen.mem_nhds hq)).differentiableAt (by norm_num)
  have hDsdiff : ∀ q ∈ S, DifferentiableAt ℝ Ds q := fun q hq =>
    (hDs_cd.contDiffAt (hSopen.mem_nhds hq)).differentiableAt (by norm_num)
  have hYdiff : DifferentiableAt ℝ Y (0, t) :=
    (hY_cd.contDiffAt (hSopen.mem_nhds hpt)).differentiableAt (by norm_num)
  -- the germ identity: `Y(0,·) = DJα` near `t`
  have hYslice : (fun r => Y (0, r)) =ᶠ[𝓝 t]
      fun r => covariantDerivCoord (I := I) g α (fun r' => c (0, r')) (fun r' => Ds (0, r')) r := by
    filter_upwards [(isOpen_Ioo (a := a) (b := b)).mem_nhds ht] with r hr
    exact covDerivAlong_snd_slice_eq_covariantDerivCoord (I := I) g α c Ds
      (hcdiff (0, r) ⟨h0mem, hr⟩) (hDsdiff (0, r) ⟨h0mem, hr⟩)
  -- apply Morgan–Tian
  have hgeo' : ∀ᶠ q in 𝓝 ((0 : ℝ), t),
      covDerivAlong (chartChristoffelBilin (I := I) g α) c
        (fun r => fderiv ℝ c r ((0, 1) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) q = 0 := by
    filter_upwards [hSopen.mem_nhds hpt] with q hq using hgeo q hq
  have hjac := chart_geodesic_family_jacobi (I := I) g α (u := c) (p := ((0 : ℝ), t))
    (ds := ((1, 0) : ℝ × ℝ)) (dt := ((0, 1) : ℝ × ℝ))
    (hc.contDiffAt (hSopen.mem_nhds hpt)) (hmem (0, t) hpt) hgeo'
  -- translate the two `covDerivAlong` layers on the slice
  rw [show covDerivAlong (chartChristoffelBilin (I := I) g α) c
      (fun r => covDerivAlong (chartChristoffelBilin (I := I) g α) c
        (fun r' => fderiv ℝ c r' ((1, 0) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) r)
      ((0, 1) : ℝ × ℝ) (0, t)
      = covariantDerivCoord (I := I) g α (fun r => c (0, r)) (fun r => Y (0, r)) t from
    covDerivAlong_snd_slice_eq_covariantDerivCoord (I := I) g α c Y
      (hcdiff (0, t) hpt) hYdiff] at hjac
  rw [covariantDerivCoord_congr (I := I) g α _ hYslice] at hjac
  -- `hjac : covariantDerivCoord … DJα t + chartCurvature … = 0`
  linear_combination (norm := (rw [hDsdef]; abel_nf)) hjac


/-- **Eng.** `derivAlongCurve` depends only on the **germ** of the field at `t`: it is built from
`deriv (chartFieldRep …)` and the pointwise value `V t`, both local. -/
theorem derivAlongCurve_congr_nhds (g : RiemannianMetric I M) (c : ℝ → M)
    {V W : ∀ t, TangentSpace I (c t)} {t : ℝ} (h : ∀ᶠ τ in 𝓝 t, V τ = W τ) :
    derivAlongCurve (I := I) g c V t = derivAlongCurve (I := I) g c W t := by
  have hrep : chartFieldRep (I := I) c (c t) V =ᶠ[𝓝 t] chartFieldRep (I := I) c (c t) W := by
    filter_upwards [h] with τ hτ
    simp only [chartFieldRep_apply, hτ]
  rw [derivAlongCurve_def, derivAlongCurve_def, hrep.deriv_eq, h.self_of_nhds]

/-- **Eng.** The Jacobi operator `jacobiEquation` depends only on the germ of the field at `t`:
its second covariant derivative is `derivAlongCurve` twice, and both applications are local. -/
theorem jacobiEquation_congr_nhds (g : RiemannianMetric I M) (c : ℝ → M)
    {V W : ∀ t, TangentSpace I (c t)} {t : ℝ} (h : ∀ᶠ τ in 𝓝 t, V τ = W τ) :
    jacobiEquation (I := I) g c V t = jacobiEquation (I := I) g c W t := by
  have hd : ∀ᶠ τ in 𝓝 t,
      derivAlongCurve (I := I) g c V τ = derivAlongCurve (I := I) g c W τ := by
    filter_upwards [eventually_eventually_nhds.mpr h] with τ hτ
      using derivAlongCurve_congr_nhds g c hτ
  rw [jacobiEquation_def, jacobiEquation_def, derivAlongCurve_congr_nhds g c hd, h.self_of_nhds]

/-! ### The variation field of a family of geodesics is a Jacobi field -/

/-- **Math.** Petersen §6.1, `def:pet-ch6-jacobi-field`: **the variation field of a family of
geodesics is a Jacobi field**.  If a variation `f : ℝ → ℝ → M` has a `C³` reading `c = φ_α ∘ f`
in one chart on an open slab `Ioo (-δ) δ ×ˢ Ioo a b`, stays in that chart, and every `t`-line is
a geodesic (the coordinate geodesic equation `hgeo`), then its variation field
`variationField f` solves Petersen's Jacobi equation `J̈ + R(J, ċ)ċ = 0` along the base curve
`f 0` on `Ioo a b`.

This is the manifold form of `Jacobi.chart_geodesic_family_jacobi`: the coordinate Jacobi
equation (`covariantDerivCoord_snd_variationField_eq_neg_chartCurvature`) packages into a
`Jacobi.IsJacobiFieldOn` pair, `isJacobiFieldAlongOn_Ioo_of_isJacobiFieldOn` transports it to the
manifold, and `variationField_eq_tangentCoordChange` names the transported field. -/
theorem isJacobiFieldAlongOn_variationField_of_geodesicFamily (g : RiemannianMetric I M) (α : M)
    {f : ℝ → ℝ → M} {δ a b : ℝ} (hδ : 0 < δ)
    (hc : ContDiffOn ℝ 3 (fun q : ℝ × ℝ => extChartAt I α (f q.1 q.2)) (Ioo (-δ) δ ×ˢ Ioo a b))
    (hsrc : ∀ q ∈ Ioo (-δ) δ ×ˢ Ioo a b, Function.uncurry f q ∈ (extChartAt I α).source)
    (hmem : ∀ q ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      extChartAt I α (f q.1 q.2) ∈ interior (extChartAt I α).target)
    (hgeo : ∀ q ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      covDerivAlong (chartChristoffelBilin (I := I) g α)
        (fun r : ℝ × ℝ => extChartAt I α (f r.1 r.2))
        (fun r : ℝ × ℝ => fderiv ℝ (fun r' : ℝ × ℝ => extChartAt I α (f r'.1 r'.2)) r
          ((0, 1) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) q = 0) :
    IsJacobiFieldAlongOn (I := I) g (f 0) (variationField (I := I) f) (Ioo a b) := by
  set c : ℝ × ℝ → E := fun q : ℝ × ℝ => extChartAt I α (f q.1 q.2) with hcdef
  set S : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Ioo a b with hSdef
  have hSopen : IsOpen S := isOpen_Ioo.prod isOpen_Ioo
  have hIoo : IsOpen (Ioo a b) := isOpen_Ioo
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  -- abbreviations for the chart pair
  set u : ℝ → E := fun r => c (0, r) with hudef
  set Jα : ℝ → E := fun r => fderiv ℝ c (0, r) ((1, 0) : ℝ × ℝ) with hJαdef
  set DJα : ℝ → E := fun r => covariantDerivCoord (I := I) g α u Jα r with hDJαdef
  -- smoothness scaffolding on `Ioo a b`
  have hu_cd : ContDiffOn ℝ 3 u (Ioo a b) := contDiffOn_slice_zero hδ hc
  have hc2 : ContDiffOn ℝ 2 (fderiv ℝ c) S := hc.fderiv_of_isOpen hSopen (by norm_num)
  have hJα_cd : ContDiffOn ℝ 2 Jα (Ioo a b) :=
    contDiffOn_slice_zero hδ (hc2.clm_apply contDiffOn_const)
  have hderivU : ContDiffOn ℝ 2 (deriv u) (Ioo a b) := hu_cd.deriv_of_isOpen hIoo le_rfl
  have hderivJα : ContDiffOn ℝ 1 (deriv Jα) (Ioo a b) := hJα_cd.deriv_of_isOpen hIoo le_rfl
  have humem : ∀ r ∈ Ioo a b, u r ∈ (extChartAt I α).target := fun r hr =>
    interior_subset (hmem (0, r) ⟨h0mem, hr⟩)
  have hΓ_cd : ContDiffOn ℝ 1 (fun r => Geodesic.chartChristoffelContraction (I := I) g α
      (deriv u r) (Jα r) (u r)) (Ioo a b) :=
    contDiffOn_chartChristoffelContraction_comp (I := I) g α (by decide)
      (hu_cd.of_le (by decide)) (hderivU.of_le (by decide)) (hJα_cd.of_le (by decide)) humem
  have hDJα_eq : DJα = fun r => deriv Jα r
      + Geodesic.chartChristoffelContraction (I := I) g α (deriv u r) (Jα r) (u r) := by
    funext r; simp only [hDJαdef, covariantDerivCoord_def]
  have hDJα_cd : ContDiffOn ℝ 1 DJα (Ioo a b) := by rw [hDJα_eq]; exact hderivJα.add hΓ_cd
  -- the slice-derivative identity `deriv u r = ∂_t c(0,r)`
  have hcdiff : ∀ q ∈ S, DifferentiableAt ℝ c q := fun q hq =>
    (hc.contDiffAt (hSopen.mem_nhds hq)).differentiableAt (by norm_num)
  have hderivU_eq : ∀ r ∈ Ioo a b, deriv u r = fderiv ℝ c (0, r) ((0, 1) : ℝ × ℝ) := by
    intro r hr
    exact (Jacobi.hasDerivAt_comp_snd (hcdiff (0, r) ⟨h0mem, hr⟩).hasFDerivAt).deriv
  -- work pointwise on `Ioo a b`
  intro t ht
  obtain ⟨a', haa', ha't⟩ := exists_between ht.1
  obtain ⟨b', htb', hb'b⟩ := exists_between ht.2
  have hsub : Icc a' b' ⊆ Ioo a b := fun r hr =>
    ⟨lt_of_lt_of_le haa' hr.1, lt_of_le_of_lt hr.2 hb'b⟩
  -- the chart pair is a Jacobi field on `[a', b']`
  have hpair : Jacobi.IsJacobiFieldOn (I := I) g α u Jα DJα a' b' := by
    refine ⟨?_, ?_⟩
    · intro r hr
      have hrIoo := hsub hr
      have hJαd : DifferentiableAt ℝ Jα r :=
        (hJα_cd.contDiffAt (hIoo.mem_nhds hrIoo)).differentiableAt (by norm_num)
      have hval : DJα r - Geodesic.chartChristoffelContraction (I := I) g α
          (deriv u r) (Jα r) (u r) = deriv Jα r := by
        rw [hDJαdef]; simp only [covariantDerivCoord_def]; abel
      rw [hval]
      exact hJαd.hasDerivAt.hasDerivWithinAt
    · intro r hr
      have hrIoo := hsub hr
      have hDJαd : DifferentiableAt ℝ DJα r :=
        (hDJα_cd.contDiffAt (hIoo.mem_nhds hrIoo)).differentiableAt (by norm_num)
      have hjeq := covariantDerivCoord_snd_variationField_eq_neg_chartCurvature (I := I) g α
        (c := c) hδ hrIoo hc hmem hgeo
      -- rewrite the curvature arguments into `u r`, `Jα r`, `deriv u r`
      rw [← hderivU_eq r hrIoo] at hjeq
      -- `hjeq : covariantDerivCoord g α u DJα r = -chartCurvature (u r) (Jα r) (deriv u r) (deriv u r)`
      have hval : -(chartCurvature (I := I) g α (u r) (Jα r) (deriv u r) (deriv u r))
          - Geodesic.chartChristoffelContraction (I := I) g α (deriv u r) (DJα r) (u r)
          = deriv DJα r := by
        have h1 : covariantDerivCoord (I := I) g α u DJα r = deriv DJα r
            + Geodesic.chartChristoffelContraction (I := I) g α (deriv u r) (DJα r) (u r) :=
          covariantDerivCoord_def (I := I) g α u DJα r
        rw [h1] at hjeq
        exact (eq_sub_of_add_eq hjeq).symm
      rw [hval]
      exact hDJαd.hasDerivAt.hasDerivWithinAt
  -- transport the pair to a manifold Jacobi field along `f 0`
  have hcAt : ∀ τ ∈ Icc a' b', ContinuousAt (f 0) τ := by
    intro τ hτ
    have hτIoo := hsub hτ
    refine continuousAt_of_chartReading (I := I) α ?_ ?_
    · filter_upwards [hIoo.mem_nhds hτIoo] with σ hσ
      exact hsrc (0, σ) ⟨h0mem, hσ⟩
    · exact ((Jacobi.hasDerivAt_comp_snd (hcdiff (0, τ) ⟨h0mem, hτIoo⟩).hasFDerivAt)).continuousAt
  have hsrc' : ∀ τ ∈ Icc a' b', f 0 τ ∈ (chartAt H α).source := fun τ hτ => by
    rw [← extChartAt_source (I := I) α]; exact hsrc (0, τ) ⟨h0mem, hsub hτ⟩
  have hu' : ∀ τ ∈ Icc a' b', DifferentiableAt ℝ (fun σ => extChartAt I α (f 0 σ)) τ := by
    intro τ hτ
    exact (Jacobi.hasDerivAt_comp_snd (hcdiff (0, τ) ⟨h0mem, hsub hτ⟩).hasFDerivAt).differentiableAt
  have hjac := isJacobiFieldAlongOn_Ioo_of_isJacobiFieldOn (I := I) g α hcAt hsrc' hu' hpair
  -- identify the transported field with `variationField f` near `t`
  have htab' : t ∈ Ioo a' b' := ⟨ha't, htb'⟩
  have heq : ∀ᶠ τ in 𝓝 t, variationField (I := I) f τ
      = (tangentCoordChange I α (f 0 τ) (f 0 τ) (Jα τ) : TangentSpace I (f 0 τ)) := by
    filter_upwards [hIoo.mem_nhds ht] with τ hτ
    exact variationField_eq_tangentCoordChange (I := I) α hδ hτ hcdef
      (hcdiff (0, τ) ⟨h0mem, hτ⟩) (fun q hq => hsrc q hq)
  rw [jacobiEquation_congr_nhds g (f 0) heq]
  exact hjac t htab'

/-! ### From geodesic transversal-time lines to the coordinate geodesic hypothesis -/

/-- **Math.** The geodesic hypothesis `hgeo` of
`isJacobiFieldAlongOn_variationField_of_geodesicFamily` from the *intrinsic* statement that
**every time-line of the family is a geodesic**.  If a variation `f` has a `C²` chart reading on
an open slab `Ioo (-δ) δ ×ˢ Ioo a b`, stays in the chart, and each line `τ ↦ f s τ`
(`s ∈ Ioo (-δ) δ`) has vanishing `curveAcceleration` on `Ioo a b`, then the coordinate geodesic
equation `covDerivAlong Γ c (∂_t c) (0,1) = 0` holds at every slab point.

`mixedPartialCoord_snd_snd_eq_zero_of_isGeodesic` only handles the *base* line `s = 0`; the
general point `q = (s₀, τ)` is re-based to `s = 0` by translating the family in `s`
(`mixedPartialCoord_comp_const_add`, the same shrunken-slab `δ' = δ - |s₀|` argument as
`firstVariationOfEnergyAt`), which turns the line `τ ↦ f s₀ τ` into the base line of the shifted
family. -/
theorem covDerivAlong_snd_snd_eq_zero_of_geodesicLines (g : RiemannianMetric I M) (α : M)
    {f : ℝ → ℝ → M} {δ a b : ℝ} (_hδ : 0 < δ)
    (hc : ContDiffOn ℝ 2 (fun q : ℝ × ℝ => extChartAt I α (f q.1 q.2)) (Ioo (-δ) δ ×ˢ Ioo a b))
    (hsrc : ∀ q ∈ Ioo (-δ) δ ×ˢ Ioo a b, Function.uncurry f q ∈ (extChartAt I α).source)
    (hline : ∀ s ∈ Ioo (-δ) δ, ∀ τ ∈ Ioo a b,
      curveAcceleration (I := I) g (fun τ' => f s τ') τ = 0) :
    ∀ q ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      covDerivAlong (chartChristoffelBilin (I := I) g α)
        (fun r : ℝ × ℝ => extChartAt I α (f r.1 r.2))
        (fun r : ℝ × ℝ => fderiv ℝ (fun r' : ℝ × ℝ => extChartAt I α (f r'.1 r'.2)) r
          ((0, 1) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) q = 0 := by
  rintro ⟨s₀, τ⟩ ⟨hs₀, hτ⟩
  rw [covDerivAlong_snd_snd_eq_mixedPartialCoord (I := I) g α
    (fun r : ℝ × ℝ => extChartAt I α (f r.1 r.2)) (s₀, τ)]
  have hs₀abs : |s₀| < δ := abs_lt.mpr ⟨hs₀.1, hs₀.2⟩
  set δ' : ℝ := δ - |s₀| with hδ'def
  have hδ' : 0 < δ' := by rw [hδ'def]; linarith
  set fs : ℝ → ℝ → M := fun σ τ' => f (s₀ + σ) τ' with hfsdef
  -- the translation `r ↦ (s₀, 0) + r` maps the shrunken slab into the original slab
  have hmaps' : MapsTo (fun r : ℝ × ℝ => ((s₀, 0) + r : ℝ × ℝ)) (Ioo (-δ') δ' ×ˢ Ioo a b)
      (Ioo (-δ) δ ×ˢ Ioo a b) := by
    rintro ⟨σ, τ'⟩ ⟨hσ, hτ'⟩
    have hσabs : |σ| < δ' := abs_lt.mpr ⟨hσ.1, hσ.2⟩
    have hsum : |s₀ + σ| < δ :=
      calc |s₀ + σ| ≤ |s₀| + |σ| := abs_add_le s₀ σ
        _ < |s₀| + δ' := by linarith
        _ = δ := by rw [hδ'def]; ring
    refine ⟨?_, ?_⟩
    · show s₀ + σ ∈ Ioo (-δ) δ
      exact abs_lt.mp hsum
    · show (0 : ℝ) + τ' ∈ Ioo a b
      rw [zero_add]; exact hτ'
  -- the shifted family's chart reading is the original's, precomposed with the translation
  have hcshift : (fun r : ℝ × ℝ => extChartAt I α (fs r.1 r.2))
      = fun r : ℝ × ℝ =>
        (fun r'' : ℝ × ℝ => extChartAt I α (f r''.1 r''.2)) ((s₀, 0) + r) := by
    funext r
    simp only [hfsdef, Prod.fst_add, Prod.snd_add, zero_add]
  -- re-base the mixed partial from `(s₀, τ)` to the base line of the shifted family
  have hshift : mixedPartialCoord (I := I) g α (fun r : ℝ × ℝ => extChartAt I α (f r.1 r.2))
        (s₀, τ) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
      = mixedPartialCoord (I := I) g α (fun r : ℝ × ℝ => extChartAt I α (fs r.1 r.2))
        (0, τ) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
    rw [hcshift, mixedPartialCoord_comp_const_add (I := I) g α
      (c := fun r'' : ℝ × ℝ => extChartAt I α (f r''.1 r''.2)) (s₀, 0) (0, τ) (0, 1) (0, 1)]
    congr 1
    simp
  rw [hshift]
  -- smoothness of the shifted family on the shrunken slab
  have hc' : ContDiffOn ℝ 2 (fun r : ℝ × ℝ => extChartAt I α (fs r.1 r.2))
      (Ioo (-δ') δ' ×ˢ Ioo a b) := by
    rw [hcshift]
    exact hc.comp (contDiff_const.add contDiff_id).contDiffOn hmaps'
  -- source membership of the shifted family
  have hsrc' : ∀ r ∈ Ioo (-δ') δ' ×ˢ Ioo a b,
      Function.uncurry fs r ∈ (extChartAt I α).source := by
    rintro ⟨σ, τ'⟩ hr
    have h := hsrc ((s₀, 0) + (σ, τ')) (hmaps' hr)
    simpa only [hfsdef, Prod.mk_add_mk, zero_add, Function.uncurry] using h
  -- the base line of the shifted family is `τ ↦ f s₀ τ`, a geodesic
  have hgeo0 : curveAcceleration (I := I) g (fs 0) τ = 0 := by
    have h := hline s₀ hs₀ τ hτ
    have hfs0 : fs 0 = fun τ' => f s₀ τ' := by funext τ'; simp only [hfsdef, add_zero]
    rw [hfs0]; exact h
  exact mixedPartialCoord_snd_snd_eq_zero_of_isGeodesic (I := I) (f := fs) g α hδ' hτ rfl
    hc' hsrc' hgeo0

/-! ### Petersen's `D exp_p` remark -/

/-- **Math.** Petersen §6.1 (p. 254), `rem:pet-ch6-jacobi-dexp-relation`.  For the geodesic
variation `c̄(s,t) = exp_p(t·(v + s·w))` (with `w = J(0)`), the variation field
`J(t) = ∂c̄/∂s(0,t) = D exp_p|_{tv}(tw)` is a **Jacobi field** along the base geodesic
`t ↦ exp_p(t·v)`, with `J(0) = 0`.  This is the specialization of
`isJacobiFieldAlongOn_variationField_of_geodesicFamily` to the exponential variation, at the
fixed basepoint `α = p`.

The statement is local, as Petersen's remark is: it produces a normal radius `ρ` and, for every
`v` with `‖v‖ < ρ` and every `w`, a time window `Ioo (-β) β` on which the variation field solves
the Jacobi equation.  The window is honest — the exponential rays `t ↦ exp_p(t·(v+s·w))` are
geodesics only while they stay in the normal ball at `p`
(`Exponential.exists_isGeodesicOn_expMap_ray`), and their chart reading is `C^∞` there
(`Exponential.exists_contDiffOn_infty_extChartAt_expMap_ball`).  The base curve is written as the
`s = 0` slice of the variation, definitionally `t ↦ exp_p(t·v)`. -/
theorem jacobiField_dexp_relation (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v w : E, ‖v‖ < ρ → ∃ β : ℝ, 0 < β ∧
      IsJacobiFieldAlongOn (I := I) g
          ((fun s t : ℝ => expMap (I := I) g p ((t • (v + s • w) : E) : TangentSpace I p)) 0)
          (variationField (I := I)
            (fun s t : ℝ => expMap (I := I) g p ((t • (v + s • w) : E) : TangentSpace I p)))
          (Ioo (-β) β)
        ∧ variationField (I := I)
            (fun s t : ℝ => expMap (I := I) g p ((t • (v + s • w) : E) : TangentSpace I p)) 0
          = 0 := by
  obtain ⟨ρs, hρs, _hdom_s, hsrc_s, hcd⟩ :=
    Exponential.exists_contDiffOn_infty_extChartAt_expMap_ball (I := I) g p
  obtain ⟨ρr, br, hρr, hbr, _hadm, hray⟩ :=
    Exponential.exists_isGeodesicOn_expMap_ray (I := I) g p
  refine ⟨min ρs ρr, lt_min hρs hρr, ?_⟩
  intro v w hv
  have hvs : ‖v‖ < ρs := lt_of_lt_of_le hv (min_le_left _ _)
  have hvr : ‖v‖ < ρr := lt_of_lt_of_le hv (min_le_right _ _)
  -- the constants of the window
  set δ : ℝ := (ρr - ‖v‖) / (2 * (‖w‖ + 1)) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; apply div_pos (by linarith) (by positivity)
  set β : ℝ := min br (ρs / ρr) with hβdef
  have hβ : 0 < β := lt_min (lt_trans one_pos hbr) (div_pos hρs hρr)
  -- `‖v + s·w‖ < ρr` for `|s| < δ`
  have hnb : ∀ s : ℝ, |s| < δ → ‖v + s • w‖ < ρr := by
    intro s hs
    have hw1 : (‖w‖ + 1 : ℝ) ≠ 0 := by positivity
    have hδmul : δ * (‖w‖ + 1) = (ρr - ‖v‖) / 2 := by rw [hδdef]; field_simp
    have hbnd : ‖v + s • w‖ ≤ ‖v‖ + |s| * ‖w‖ :=
      calc ‖v + s • w‖ ≤ ‖v‖ + ‖s • w‖ := norm_add_le _ _
        _ = ‖v‖ + |s| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
    have hsw : |s| * ‖w‖ < (ρr - ‖v‖) / 2 :=
      calc |s| * ‖w‖ ≤ |s| * (‖w‖ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
        _ < δ * (‖w‖ + 1) := mul_lt_mul_of_pos_right hs (by positivity)
        _ = (ρr - ‖v‖) / 2 := hδmul
    linarith
  -- `β * ρr ≤ ρs`
  have hβρr : β * ρr ≤ ρs :=
    calc β * ρr ≤ (ρs / ρr) * ρr := mul_le_mul_of_nonneg_right (min_le_right _ _) hρr.le
      _ = ρs := div_mul_cancel₀ ρs hρr.ne'
  -- the inner-vector norm bound on the slab
  have hsb : ∀ q : ℝ × ℝ, q ∈ Ioo (-δ) δ ×ˢ Ioo (-β) β →
      ‖(q.2 • (v + q.1 • w) : E)‖ < ρs := by
    intro q hq
    have hq1 : |q.1| < δ := abs_lt.mpr ⟨hq.1.1, hq.1.2⟩
    have hq2 : |q.2| < β := abs_lt.mpr ⟨hq.2.1, hq.2.2⟩
    have hur : ‖v + q.1 • w‖ < ρr := hnb q.1 hq1
    calc ‖(q.2 • (v + q.1 • w) : E)‖
        = |q.2| * ‖v + q.1 • w‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ < β * ρr := mul_lt_mul'' hq2 hur (abs_nonneg _) (norm_nonneg _)
      _ ≤ ρs := hβρr
  set f : ℝ → ℝ → M :=
    fun s t : ℝ => expMap (I := I) g p ((t • (v + s • w) : E) : TangentSpace I p) with hfdef
  -- smoothness of the family's chart reading
  set ι : ℝ × ℝ → E := fun q : ℝ × ℝ => (q.2 • (v + q.1 • w) : E) with hιdef
  have hι : ContDiff ℝ ∞ ι := by
    rw [hιdef]
    exact contDiff_snd.smul (contDiff_const.add (contDiff_fst.smul contDiff_const))
  have hmaps : MapsTo ι (Ioo (-δ) δ ×ˢ Ioo (-β) β) (Metric.ball (0 : E) ρs) := by
    intro q hq
    simp only [mem_ball_zero_iff, hιdef]
    exact hsb q hq
  have hc : ContDiffOn ℝ 3 (fun q : ℝ × ℝ => extChartAt I p (f q.1 q.2))
      (Ioo (-δ) δ ×ˢ Ioo (-β) β) := by
    have hcomp : ContDiffOn ℝ ∞
        ((fun x : E => extChartAt I p (expMap (I := I) g p (x : TangentSpace I p))) ∘ ι)
        (Ioo (-δ) δ ×ˢ Ioo (-β) β) := hcd.comp hι.contDiffOn hmaps
    refine (hcomp.of_le (by norm_cast)).congr (fun q _hq => ?_)
    simp only [hfdef, Function.comp_apply, hιdef]
  -- source membership
  have hsrc : ∀ q ∈ Ioo (-δ) δ ×ˢ Ioo (-β) β,
      Function.uncurry f q ∈ (extChartAt I p).source := by
    intro q hq
    show f q.1 q.2 ∈ (extChartAt I p).source
    simp only [hfdef]
    rw [extChartAt_source]
    exact hsrc_s (q.2 • (v + q.1 • w)) (hsb q hq)
  -- interior-of-target membership
  have hmem : ∀ q ∈ Ioo (-δ) δ ×ˢ Ioo (-β) β,
      extChartAt I p (f q.1 q.2) ∈ interior (extChartAt I p).target := by
    intro q hq
    apply extChartAt_target_subset_interior_of_boundaryless (I := I) p
    apply (extChartAt I p).map_source
    simp only [hfdef]
    rw [extChartAt_source]
    exact hsrc_s (q.2 • (v + q.1 • w)) (hsb q hq)
  -- every time-line of the family is a geodesic
  have hline : ∀ s ∈ Ioo (-δ) δ, ∀ τ ∈ Ioo (-β) β,
      curveAcceleration (I := I) g (fun τ' => f s τ') τ = 0 := by
    intro s hs τ hτ
    have hsabs : |s| < δ := abs_lt.mpr ⟨hs.1, hs.2⟩
    have hur : ‖v + s • w‖ < ρr := hnb s hsabs
    have hτbr : |τ| < br := lt_of_lt_of_le (abs_lt.mpr ⟨hτ.1, hτ.2⟩) (min_le_left _ _)
    have hτmem : τ ∈ Ioo (-br) br := abs_lt.mp hτbr
    have hgeo := (hray (v + s • w) hur).2.2.2
    have hHGE := hgeo.hasGeodesicEquationAt hτmem
    have hacc := ((hasGeodesicEquationAt_iff_curveAcceleration (I := I) g
      (fun τ' : ℝ => expMap (I := I) g p ((τ' • (v + s • w) : E) : TangentSpace I p)) τ).mp hHGE).2
    simpa only [hfdef] using hacc
  -- the family is a family of geodesics ⇒ its variation field is a Jacobi field
  have hjac := isJacobiFieldAlongOn_variationField_of_geodesicFamily (I := I) g p hδ hc hsrc hmem
    (covDerivAlong_snd_snd_eq_zero_of_geodesicLines (I := I) g p hδ (hc.of_le (by norm_num))
      hsrc hline)
  refine ⟨β, hβ, hjac, ?_⟩
  -- `J(0) = 0`: the transversal `s ↦ f s 0` is the constant curve `p`
  have hf00 : ∀ s : ℝ, f s 0 = f 0 0 := by
    intro s
    simp only [hfdef, zero_smul, expMap_zero]
  rw [variationField_eq]
  have hconst : (fun s : ℝ => extChartAt I (f 0 0) (f s 0))
      = fun _ : ℝ => extChartAt I (f 0 0) (f 0 0) := by
    funext s; rw [hf00 s]
  rw [hconst, deriv_const']

end PetersenLib

end
