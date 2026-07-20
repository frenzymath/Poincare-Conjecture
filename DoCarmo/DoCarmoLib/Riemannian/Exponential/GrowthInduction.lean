import DoCarmoLib.Riemannian.Exponential.CornerRigidity
import DoCarmoLib.Riemannian.Exponential.RayGeodesic
import DoCarmoLib.Riemannian.Exponential.NormalBallEDist
import DoCarmoLib.Riemannian.Geodesic.Completeness
import DoCarmoLib.Riemannian.Geodesic.IntrinsicUniqueness

/-!
# The growth induction: minimizing geodesics out of a geodesically complete point

do Carmo, *Riemannian Geometry*, Ch. 7, proof of Theorem 2.8, a) ⟹ f): if every
tangent vector at `p` generates a geodesic defined on all of `ℝ`, then every
`q ∈ M` is joined to `p` by a minimizing geodesic.

The proof is do Carmo's geodesic-sphere growth induction. Let `r = d(p, q)`.

* **First step.** A small geodesic sphere `S_δ(p)` carries a point
  `x₁ = exp_p z` closest to `q`, and `d(p, q) = δ + d(x₁, q)`
  (`exists_normalSphere_min_edist`). Let `γ` be the global unit-speed geodesic
  through `p` in the direction of `z`; by uniqueness its initial segment is
  the radial geodesic to `x₁`, so `d(γ δ, q) = r - δ`.
* **The set `A`.** `A = {s ∈ [δ, r] | d(γ s, q) = r - s}` is closed and
  contains `δ`; for `s₀ ∈ A` the triangle inequality squeezes
  `d(p, γ s) = s` and `d(γ s, q) = r - s` for ALL `s ∈ [0, s₀]`
  (`γ` is `1`-Lipschitz and `d(p, ·)` cannot grow faster than arclength).
* **Pushing the supremum** (`exists_add_mem_of_lt` below): if
  `s₀ = sup A < r`, run the sphere step at `x = γ s₀`: a small sphere
  `S_{δ'}(x)` carries `x' = exp_x z'` with `d(x, q) = δ' + d(x', q)`. The
  broken curve (`γ` up to `x`, then the radial segment to `x'`) realizes the
  distance between its endpoints, so **corner rigidity**
  (`eq_neg_of_forall_edist_expMap_eq`, do Carmo Ch. 3, Cor. 3.9) forces the
  radial direction `u₂ = z'/δ'` to be the negative of the incoming direction
  `u₁ = -γ'(s₀)`; intrinsic uniqueness then glues: `γ(s₀ + η) = exp_x(η u₂)`,
  whence `d(γ(s₀ + δ'), q) = r - (s₀ + δ')` and `s₀ + δ' ∈ A` — contradiction.
* Hence `sup A = r`, i.e. `d(γ r, q) = 0`, i.e. `γ r = q`, and `γ|[0,r]` is
  minimizing (`d(p, γ s) = s` for all `s ∈ [0, r]`).

The main statement is `exists_minimizing_geodesic_of_forall_geodesic`; the
Hopf–Rinow facade (`Geodesic/HopfRinow.lean`) consumes it for
d) ⟹ f) (`exists_minimizing_geodesic`) and, through the properness argument,
for d) ⟹ b) ⟹ c).
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff


namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
variable [T2Space (TangentBundle I M')]

/-! ## Helper lemmas: initial speed, unit-speed Lipschitz bound, uniqueness -/

omit [T2Space (TangentBundle I M')] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The squared speed of a curve satisfying the geodesic equation at
time `τ`, expressed through any chart velocity at the foot: if the chart-`γ τ`
reading of `γ` has derivative `u` at `τ`, then
`⟨γ'(τ), γ'(τ)⟩_g = ⟨u, u⟩_{G(φ(γ τ))}`. -/
theorem speedSq_eq_chartMetricInner_of_hasDerivAt {g : RiemannianMetric I M'}
    {γ : ℝ → M'} {τ : ℝ} {u : E}
    (hγ : HasGeodesicEquationAt (I := I) g γ τ) (hcont : ContinuousAt γ τ)
    (hv : HasDerivAt (fun s => extChartAt I (γ τ) (γ s)) u τ) :
    speedSq (I := I) g γ τ
      = chartMetricInner (I := I) g (γ τ) (extChartAt I (γ τ) (γ τ)) u u := by
  have h := hγ.speedSq_eq_chartMetricInner (t := τ) hcont
    (mem_chart_source H (γ τ))
  have hderiv : deriv (chartLocalCurve (I := I) γ τ) τ = u := hv.deriv
  rw [h, hderiv]
  rfl

omit [T2Space (TangentBundle I M')] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** A continuous global geodesic with unit initial chart speed is
`1`-Lipschitz: `d(γ a, γ b) ≤ b - a` (do Carmo Ch. 7, proof of Thm 2.8). -/
theorem IsGeodesic.dist_le_of_speedSq_one (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) {γ : ℝ → M'}
    (hγ : IsGeodesic (I := I) g γ) (hcont : Continuous γ)
    (hspeed : speedSq (I := I) g γ 0 = 1)
    {a b : ℝ} (hab : a ≤ b) :
    dist (γ a) (γ b) ≤ b - a := by
  have h := IsGeodesicOn.dist_le (I := I) g hg (s := univ)
    (hγ.isGeodesicOn univ) isOpen_univ isPreconnected_univ
    hcont.continuousOn (mem_univ a) (mem_univ b) hab
  have hsp : speedSq (I := I) g γ a = 1 := by
    rw [← hspeed]
    exact IsGeodesicOn.speedSq_eq (hγ.isGeodesicOn univ) isOpen_univ
      isPreconnected_univ hcont.continuousOn (mem_univ a) (mem_univ 0)
  rw [hsp, Real.sqrt_one, one_mul] at h
  exact h

omit [T2Space (TangentBundle I M')] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Uniqueness of intrinsic geodesics, `HasDerivAt` form: two
continuous geodesics on an open preconnected time set which share their
position at `t₀` and their chart-`β` velocity (as an actual derivative)
coincide on the whole time set. -/
theorem IsGeodesicOn.eqOn_of_hasDerivAt_chartReading
    {g : RiemannianMetric I M'} {γ₁ γ₂ : ℝ → M'} {s : Set ℝ} {t₀ : ℝ} {β : M'}
    {u : E}
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (h₁ : IsGeodesicOn (I := I) g γ₁ s) (h₂ : IsGeodesicOn (I := I) g γ₂ s)
    (hc₁ : ContinuousOn γ₁ s) (hc₂ : ContinuousOn γ₂ s)
    (ht₀ : t₀ ∈ s) (heq0 : γ₁ t₀ = γ₂ t₀)
    (hβ : γ₁ t₀ ∈ (chartAt H β).source)
    (hv₁ : HasDerivAt (fun τ => extChartAt I β (γ₁ τ)) u t₀)
    (hv₂ : HasDerivAt (fun τ => extChartAt I β (γ₂ τ)) u t₀) :
    Set.EqOn γ₁ γ₂ s := by
  refine IsGeodesicOn.eqOn_of_deriv_chartReading_eq (I := I) hs hconn h₁ h₂
    hc₁ hc₂ ht₀ heq0 hβ ?_
  show deriv (fun τ => extChartAt I β (γ₁ τ)) t₀
    = deriv (fun τ => extChartAt I β (γ₂ τ)) t₀
  rw [hv₁.deriv, hv₂.deriv]

/-! ## The sup-pushing step -/

omit [InnerProductSpace ℝ E] in
/-- **Math.** **The growth step of the Hopf–Rinow induction** (do Carmo Ch. 7,
proof of Theorem 2.8, the interior case): let `γ` be a continuous unit-speed
global geodesic with `d(γ 0, γ s) = s` and `d(γ s, q) = r - s` for all
`s ∈ [0, s₀]`, where `0 < s₀ < r`. Then the equality persists a little
further: there is `δ' > 0` with `s₀ + δ' ≤ r` and
`d(γ (s₀ + δ'), q) = r - (s₀ + δ')`.

Proof: run the geodesic-sphere step at `x = γ s₀`: a small sphere `S_{δ'}(x)`
carries `x' = exp_x z'` with `d(x, q) = δ' + d(x', q)`
(`exists_normalSphere_min_edist`). The broken curve through `x` — `γ`
backwards, then the radial segment to `x'` — realizes the distance between
its endpoints (`d(γ(s₀-η), exp_x(η u₂)) = 2η` for small `η`, by the triangle
squeeze against `d(·, q)`), so corner rigidity
(`eq_neg_of_forall_edist_expMap_eq`, do Carmo Ch. 3, Cor. 3.9) forces
`u₂ = -u₁`, i.e. the radial direction continues `γ'(s₀)`; intrinsic
uniqueness (`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) then identifies
`γ(s₀ + η) = exp_x(η u₂)`, and the sphere decomposition transfers the
distance equality to `s₀ + δ'`. -/
theorem exists_add_mem_of_lt (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist)
    {γ : ℝ → M'} (hγ : IsGeodesic (I := I) g γ) (hcont : Continuous γ)
    (hspeed : speedSq (I := I) g γ 0 = 1)
    {q : M'} {r s₀ : ℝ} (hs₀pos : 0 < s₀) (hs₀r : s₀ < r)
    (hup : ∀ s ∈ Icc (0 : ℝ) s₀, dist (γ 0) (γ s) = s ∧ dist (γ s) q = r - s) :
    ∃ δ' : ℝ, 0 < δ' ∧ s₀ + δ' ≤ r ∧
      dist (γ (s₀ + δ')) q = r - (s₀ + δ') := by
  classical
  set x : M' := γ s₀ with hxdef
  have hxq : dist x q = r - s₀ := (hup s₀ ⟨hs₀pos.le, le_refl _⟩).2
  have hrs₀ : 0 < r - s₀ := by linarith
  -- the geodesic-sphere and normal-ball data at `x`
  obtain ⟨ε', c', hε', hc', hdom', hstep'⟩ :=
    exists_normalSphere_min_edist (I := I) g hg x
  obtain ⟨ρ', b', hρ', hb', hadm', hray'⟩ :=
    exists_isGeodesicOn_expMap_ray (I := I) g x
  obtain ⟨εD, δD, hεD, hδD, hdomD, hsrcD, hinjD, hopenD, hedistD, hescD⟩ :=
    exists_edist_expMap_ball (I := I) g hg x
  have hb'0 : (0 : ℝ) < b' := lt_trans one_pos hb'
  have hsqrtc' : 0 < Real.sqrt c' := Real.sqrt_pos.mpr hc'
  -- choice of the step radius `δ'`
  set m : ℝ := min ε' (min ρ' εD) with hmdef
  have hm : 0 < m := lt_min hε' (lt_min hρ' hεD)
  set δ' : ℝ := min ((r - s₀) / 2) (m / (2 * Real.sqrt c')) with hδ'def
  have hδ' : 0 < δ' := lt_min (by linarith) (by positivity)
  have hδ'r2 : δ' ≤ (r - s₀) / 2 := min_le_left _ _
  have hδ'r : δ' ≤ r - s₀ := by linarith
  have hcδ'm : Real.sqrt c' * δ' < m := by
    have h1 : δ' ≤ m / (2 * Real.sqrt c') := min_le_right _ _
    have h2 : Real.sqrt c' * δ' ≤ m / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt c')] at h1
      linarith [h1]
    linarith
  have hcδ'ε' : Real.sqrt c' * δ' < ε' := hcδ'm.trans_le (min_le_left _ _)
  have hcδ'ρ' : Real.sqrt c' * δ' < ρ' :=
    hcδ'm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hcδ'εD : Real.sqrt c' * δ' < εD :=
    hcδ'm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  -- the sphere-minimum point `x' = exp_x z'`
  have hδ'edist : ENNReal.ofReal δ' ≤ edist x q := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (by linarith [hxq])
  obtain ⟨z', hz'c, hz'ε', hz'gram, hz'dist, hz'decomp, -⟩ :=
    hstep' q δ' hδ' hcδ'ε' hδ'edist
  have hz'ρ' : ‖z'‖ < ρ' := hz'c.trans_lt hcδ'ρ'
  -- the radial ray `τ t = exp_x (t z')`
  obtain ⟨hτ0, hτv, hτcont, hτgeo⟩ := hray' z' hz'ρ'
  set τ : ℝ → M' := fun t : ℝ =>
    expMap (I := I) g x ((t • z' : E) : TangentSpace I x) with hτdef
  set x' : M' := expMap (I := I) g x (z' : TangentSpace I x) with hx'def
  have hτ1 : τ 1 = x' := by
    show expMap (I := I) g x ((_ : E) : TangentSpace I x) = _
    rw [one_smul]
  -- ℝ-valued distance forms of the sphere-minimum facts
  have hQnonneg : ∀ v : E,
      0 ≤ chartMetricInner (I := I) g x (extChartAt I x x) v v := fun v =>
    chartMetricInner_self_nonneg_of_mem_target (I := I) g x
      (mem_extChartAt_target x) v
  have hz'sq : chartMetricInner (I := I) g x (extChartAt I x x) z' z'
      = δ' ^ 2 := by
    have h := Real.sq_sqrt (hQnonneg z')
    rw [hz'gram] at h
    linarith [h]
  have hxx' : dist x x' = δ' := by
    have h := hz'dist
    rw [edist_dist] at h
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg hδ'.le).mp h
  have hx'q : dist x' q = r - s₀ - δ' := by
    have h := hz'decomp
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_add hδ'.le dist_nonneg] at h
    have h2 := (ENNReal.ofReal_eq_ofReal_iff dist_nonneg
      (by positivity : (0 : ℝ) ≤ δ' + dist x' q)).mp h
    rw [hxq] at h2
    linarith
  -- the incoming chart velocity `w` of `γ` at `s₀`, and `u₁ = -w`
  obtain ⟨w, aγ, hw, -, -, -⟩ := hγ s₀
  have hwsq : chartMetricInner (I := I) g x (extChartAt I x x) w w = 1 := by
    have h := speedSq_eq_chartMetricInner_of_hasDerivAt (I := I)
      (hγ s₀) hcont.continuousAt hw
    have hsp : speedSq (I := I) g γ s₀ = 1 := by
      rw [← hspeed]
      exact IsGeodesicOn.speedSq_eq (hγ.isGeodesicOn univ) isOpen_univ
        isPreconnected_univ hcont.continuousOn (mem_univ s₀) (mem_univ 0)
    rw [hsp] at h
    exact h.symm
  set u₁ : E := -w with hu₁def
  set u₂ : E := δ'⁻¹ • z' with hu₂def
  have hu₁unit : chartMetricInner (I := I) g x (extChartAt I x x) u₁ u₁ = 1 := by
    rw [hu₁def, show (-w : E) = (-1 : ℝ) • w by module,
      chartMetricInner_smul_left, chartMetricInner_smul_right, hwsq]
    ring
  have hu₂unit : chartMetricInner (I := I) g x (extChartAt I x x) u₂ u₂ = 1 := by
    rw [hu₂def, chartMetricInner_smul_left, chartMetricInner_smul_right, hz'sq]
    field_simp
  -- speed of the ray `τ`: `speedSq τ = δ'²` on `(-b', b')`
  have hτspeed0 : speedSq (I := I) g τ 0 = δ' ^ 2 := by
    have h0mem : (0 : ℝ) ∈ Ioo (-b') b' := ⟨by linarith, hb'0⟩
    have hτv' : HasDerivAt (fun s => extChartAt I (τ 0) (τ s)) z' 0 := by
      rw [hτ0]
      exact hτv
    have h := speedSq_eq_chartMetricInner_of_hasDerivAt (I := I)
      (hτgeo 0 h0mem) ((hτcont 0 h0mem).continuousAt
        (Ioo_mem_nhds h0mem.1 h0mem.2)) hτv'
    rw [h]
    have hpos : τ 0 = x := hτ0
    rw [hpos, hz'sq]
  have hτspeed : ∀ t ∈ Ioo (-b') b', speedSq (I := I) g τ t = δ' ^ 2 := by
    intro t ht
    rw [← hτspeed0]
    exact IsGeodesicOn.speedSq_eq hτgeo isOpen_Ioo (isPreconnected_Ioo)
      hτcont ht ⟨by linarith, hb'0⟩
  -- Lipschitz bound along the ray
  have hτdist : ∀ a b : ℝ, a ∈ Ioo (-b') b' → b ∈ Ioo (-b') b' → a ≤ b →
      dist (τ a) (τ b) ≤ δ' * (b - a) := by
    intro a b ha hb hab
    have h := IsGeodesicOn.dist_le (I := I) g hg hτgeo isOpen_Ioo
      isPreconnected_Ioo hτcont ha hb hab
    rw [hτspeed a ha, Real.sqrt_sq hδ'.le] at h
    exact h
  -- the distance from `x` along the ray is the parameter (normal-ball exactness)
  have hxτ : ∀ η : ℝ, 0 ≤ η → η ≤ δ' → dist x (τ (η / δ')) = η := by
    intro η hη0 hηδ'
    have hvnorm : ‖((η / δ') • z' : E)‖ < εD := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (η / δ') * ‖z'‖ ≤ (η / δ') * (Real.sqrt c' * δ') := by
            apply mul_le_mul_of_nonneg_left hz'c (by positivity)
        _ = η * Real.sqrt c' := by field_simp
        _ ≤ δ' * Real.sqrt c' := by
            apply mul_le_mul_of_nonneg_right hηδ' (Real.sqrt_nonneg _)
        _ < εD := by rw [mul_comm]; exact hcδ'εD
    have h := hedistD ((η / δ') • z') hvnorm
    have hgram : Real.sqrt (chartMetricInner (I := I) g x (extChartAt I x x)
        ((η / δ') • z') ((η / δ') • z')) = η := by
      rw [chartMetricInner_smul_left, chartMetricInner_smul_right, hz'sq]
      rw [show η / δ' * (η / δ' * δ' ^ 2) = η ^ 2 by field_simp]
      exact Real.sqrt_sq hη0
    rw [hgram, edist_dist] at h
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg hη0).mp h
  -- backward geodesic `Cback` through `x` with chart velocity `λ u₁`
  set lam : ℝ := ρ' / (‖u₁‖ + 1) with hlamdef
  have hlam : 0 < lam := by positivity
  have hlamu₁ : ‖(lam • u₁ : E)‖ < ρ' := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam, hlamdef]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < ‖u₁‖ + 1)]
    nlinarith [norm_nonneg u₁, hρ']
  obtain ⟨hσ0, hσv, hσcont, hσgeo⟩ := hray' (lam • u₁) hlamu₁
  set σ : ℝ → M' := fun t : ℝ =>
    expMap (I := I) g x ((t • (lam • u₁) : E) : TangentSpace I x) with hσdef
  -- the rescaled backward reading of `γ`: `Cback t = γ (-lam t + s₀)`
  set Cback : ℝ → M' := fun t : ℝ => γ (-lam * t + s₀) with hCbackdef
  have hCbackgeo : IsGeodesicOn (I := I) g Cback univ := by
    have h := isGeodesicOn_comp_affine (I := I) (κ := -lam) (c := s₀)
      (hγ.isGeodesicOn univ)
    simpa only [Set.preimage_univ] using h
  have hCbackcont : Continuous Cback := by
    have hin : Continuous fun t : ℝ => -lam * t + s₀ := by fun_prop
    exact hcont.comp' hin
  have hCback0 : Cback 0 = x := by
    show γ (-lam * 0 + s₀) = γ s₀
    norm_num
  have hCbackv : HasDerivAt (fun t => extChartAt I x (Cback t)) (lam • u₁) 0 := by
    have hinner : HasDerivAt (fun t : ℝ => -lam * t + s₀) (-lam) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (-lam)).add_const s₀
    have hw' : HasDerivAt (chartLocalCurve (I := I) γ s₀) w (-lam * 0 + s₀) := by
      rw [show -lam * 0 + s₀ = s₀ by ring]
      exact hw
    have h := HasDerivAt.scomp (0 : ℝ) hw' hinner
    have hfun : (chartLocalCurve (I := I) γ s₀) ∘ (fun t : ℝ => -lam * t + s₀)
        = fun t => extChartAt I x (Cback t) := rfl
    rw [hfun] at h
    have hvec : ((-lam) • w : E) = lam • u₁ := by
      rw [hu₁def]; module
    rw [hvec] at h
    exact h
  -- uniqueness: the backward reading of `γ` is the `lam u₁`-ray
  have hback : Set.EqOn Cback σ (Ioo (-b') b') := by
    refine IsGeodesicOn.eqOn_of_hasDerivAt_chartReading (I := I)
      (u := lam • u₁) (β := x) isOpen_Ioo isPreconnected_Ioo
      (hCbackgeo.mono (subset_univ _)) hσgeo (hCbackcont.continuousOn) hσcont
      ⟨by linarith, hb'0⟩ (by rw [hCback0, hσ0]) ?_ ?_ ?_
    · rw [hCback0]; exact mem_chart_source H x
    · exact hCbackv
    · exact hσv
  -- hence `γ (s₀ - η) = exp_x (η u₁)` for `|η| < lam b'`
  have hbackpt : ∀ η : ℝ, |η| < lam * b' →
      γ (s₀ - η) = expMap (I := I) g x ((η • u₁ : E) : TangentSpace I x) := by
    intro η hη
    have hmem : η / lam ∈ Ioo (-b') b' := by
      rw [abs_lt] at hη
      constructor
      · rw [lt_div_iff₀ hlam]; linarith [hη.1]
      · rw [div_lt_iff₀ hlam]; linarith [hη.2]
    have h := hback hmem
    have h1 : Cback (η / lam) = γ (s₀ - η) := by
      show γ (-lam * (η / lam) + s₀) = γ (s₀ - η)
      congr 1
      field_simp
      ring
    have h2 : σ (η / lam) = expMap (I := I) g x ((η • u₁ : E) : TangentSpace I x) := by
      show expMap (I := I) g x (((η / lam) • (lam • u₁) : E) : TangentSpace I x) = _
      congr 1
      rw [smul_smul, div_mul_cancel₀ _ hlam.ne']
    rw [← h1, ← h2, h]
  -- the corner-rigidity hypothesis: the broken curve realizes the distance
  set η₀ : ℝ := min (lam * b') (min δ' s₀) with hη₀def
  have hη₀pos : 0 < η₀ := lt_min (by positivity) (lt_min hδ' hs₀pos)
  have hcorner : ∀ η : ℝ, 0 < η → η < η₀ →
      edist (expMap (I := I) g x ((η • u₁ : E) : TangentSpace I x))
          (expMap (I := I) g x ((η • u₂ : E) : TangentSpace I x))
        = ENNReal.ofReal (2 * η) := by
    intro η hη hηη₀
    have hηlam : |η| < lam * b' := by
      rw [abs_of_pos hη]
      exact hηη₀.trans_le (min_le_left _ _)
    have hηδ' : η ≤ δ' :=
      (hηη₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
    have hηs₀ : η ≤ s₀ :=
      (hηη₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
    -- the two legs
    have hleg1 : expMap (I := I) g x ((η • u₁ : E) : TangentSpace I x)
        = γ (s₀ - η) := (hbackpt η hηlam).symm
    have hleg2 : expMap (I := I) g x ((η • u₂ : E) : TangentSpace I x)
        = τ (η / δ') := by
      show _ = expMap (I := I) g x (((η / δ') • z' : E) : TangentSpace I x)
      congr 1
      rw [hu₂def, smul_smul, div_eq_mul_inv]
    -- distances of the legs to `q`
    have h1 : dist (γ (s₀ - η)) q = r - s₀ + η := by
      have h := (hup (s₀ - η) ⟨by linarith, by linarith⟩).2
      rw [h]; ring
    have hxleg : dist x (τ (η / δ')) = η := hxτ η hη.le hηδ'
    have h3 : dist (τ (η / δ')) x' ≤ δ' - η := by
      have hmem1 : η / δ' ∈ Ioo (-b') b' := by
        constructor
        · have : (0:ℝ) ≤ η / δ' := by positivity
          linarith
        · have h1 : η / δ' ≤ 1 := by rw [div_le_one hδ']; exact hηδ'
          exact h1.trans_lt hb'
      have hmem2 : (1 : ℝ) ∈ Ioo (-b') b' := ⟨by linarith, hb'⟩
      have h := hτdist (η / δ') 1 hmem1 hmem2 (by rw [div_le_one hδ']; exact hηδ')
      rw [hτ1] at h
      calc dist (τ (η / δ')) x' ≤ δ' * (1 - η / δ') := h
        _ = δ' - η := by field_simp
    have h5 : dist (τ (η / δ')) q = r - s₀ - η := by
      refine le_antisymm ?_ ?_
      · calc dist (τ (η / δ')) q ≤ dist (τ (η / δ')) x' + dist x' q :=
              dist_triangle _ _ _
          _ ≤ (δ' - η) + (r - s₀ - δ') := add_le_add h3 (le_of_eq hx'q)
          _ = r - s₀ - η := by ring
      · have h := dist_triangle x (τ (η / δ')) q
        rw [hxq, hxleg] at h
        linarith
    -- the squeeze
    have h6 : dist (γ (s₀ - η)) (τ (η / δ')) = 2 * η := by
      refine le_antisymm ?_ ?_
      · have hlip : dist (γ (s₀ - η)) x ≤ η := by
          have h := IsGeodesic.dist_le_of_speedSq_one (I := I) g hg hγ hcont
            hspeed (a := s₀ - η) (b := s₀) (by linarith)
          rw [← hxdef] at h
          calc dist (γ (s₀ - η)) x ≤ s₀ - (s₀ - η) := h
            _ = η := by ring
        calc dist (γ (s₀ - η)) (τ (η / δ'))
            ≤ dist (γ (s₀ - η)) x + dist x (τ (η / δ')) := dist_triangle _ _ _
          _ ≤ η + η := add_le_add hlip (le_of_eq hxleg)
          _ = 2 * η := by ring
      · have h := dist_triangle (γ (s₀ - η)) (τ (η / δ')) q
        rw [h1, h5] at h
        linarith
    rw [hleg1, hleg2, edist_dist, h6]
  -- corner rigidity: the radial direction continues `γ`
  have hu₂u₁ : u₂ = -u₁ :=
    eq_neg_of_forall_edist_expMap_eq (I := I) g hg x hu₁unit hu₂unit
      hη₀pos hcorner
  have hz'w : (z' : E) = δ' • w := by
    have h : u₂ = w := by rw [hu₂u₁, hu₁def, neg_neg]
    rw [hu₂def] at h
    calc (z' : E) = δ' • (δ'⁻¹ • z') := by
          rw [smul_smul, mul_inv_cancel₀ hδ'.ne', one_smul]
      _ = δ' • w := by rw [h]
  -- continuation: `γ (s₀ + δ' t) = τ t`, by uniqueness
  set Cfwd : ℝ → M' := fun t : ℝ => γ (δ' * t + s₀) with hCfwddef
  have hCfwdgeo : IsGeodesicOn (I := I) g Cfwd univ := by
    have h := isGeodesicOn_comp_affine (I := I) (κ := δ') (c := s₀)
      (hγ.isGeodesicOn univ)
    simpa only [Set.preimage_univ] using h
  have hCfwdcont : Continuous Cfwd := by
    have hin : Continuous fun t : ℝ => δ' * t + s₀ := by fun_prop
    exact hcont.comp' hin
  have hCfwd0 : Cfwd 0 = x := by
    show γ (δ' * 0 + s₀) = γ s₀
    norm_num
  have hCfwdv : HasDerivAt (fun t => extChartAt I x (Cfwd t)) z' 0 := by
    have hinner : HasDerivAt (fun t : ℝ => δ' * t + s₀) δ' 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul δ').add_const s₀
    have hw' : HasDerivAt (chartLocalCurve (I := I) γ s₀) w (δ' * 0 + s₀) := by
      rw [show δ' * 0 + s₀ = s₀ by ring]
      exact hw
    have h := HasDerivAt.scomp (0 : ℝ) hw' hinner
    have hfun : (chartLocalCurve (I := I) γ s₀) ∘ (fun t : ℝ => δ' * t + s₀)
        = fun t => extChartAt I x (Cfwd t) := rfl
    rw [hfun] at h
    rw [show (δ' • w : E) = z' from hz'w.symm] at h
    exact h
  have hfwd : Set.EqOn Cfwd τ (Ioo (-b') b') := by
    refine IsGeodesicOn.eqOn_of_hasDerivAt_chartReading (I := I)
      (u := z') (β := x) isOpen_Ioo isPreconnected_Ioo
      (hCfwdgeo.mono (subset_univ _)) hτgeo (hCfwdcont.continuousOn) hτcont
      ⟨by linarith, hb'0⟩ (by rw [hCfwd0, hτ0]) ?_ ?_ ?_
    · rw [hCfwd0]; exact mem_chart_source H x
    · exact hCfwdv
    · exact hτv
  -- conclude at `t = 1`
  have hγx' : γ (s₀ + δ') = x' := by
    have h := hfwd (show (1 : ℝ) ∈ Ioo (-b') b' from ⟨by linarith, hb'⟩)
    have h1 : Cfwd 1 = γ (s₀ + δ') := by
      show γ (δ' * 1 + s₀) = γ (s₀ + δ')
      congr 1
      ring
    rw [← h1, h, hτ1]
  exact ⟨δ', hδ', by linarith,
    by rw [hγx', hx'q]; ring⟩

/-! ## The growth induction -/

omit [InnerProductSpace ℝ E] in
/-- **Math.** **Minimizing geodesics out of a geodesically complete point**
(do Carmo Ch. 7, Theorem 2.8, a) ⟹ f)): if every tangent vector at `p`
generates a continuous geodesic defined on all of `ℝ`, then for every `q`
there is a continuous unit-speed global geodesic `γ` with `γ 0 = p`,
`γ (d(p,q)) = q`, along which `d(p, γ s) = s` and `d(γ s, q) = d(p,q) - s`
for all `s ∈ [0, d(p,q)]` — in particular `γ|[0, d(p,q)]` is minimizing.
The geodesic-sphere growth induction (see the module docstring). -/
theorem exists_minimizing_geodesic_of_forall_geodesic (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) (p : M')
    (hp : ∀ v : TangentSpace I p, ∃ γ : ℝ → M', γ 0 = p ∧
      HasDerivAt (fun s => extChartAt I p (γ s)) v 0 ∧ Continuous γ ∧
        IsGeodesic (I := I) g γ)
    (q : M') :
    ∃ γ : ℝ → M', γ 0 = p ∧ γ (dist p q) = q ∧ Continuous γ ∧
      IsGeodesic (I := I) g γ ∧
      (∃ u : E, HasDerivAt (fun s => extChartAt I p (γ s)) u 0 ∧
        chartMetricInner (I := I) g p (extChartAt I p p) u u ≤ 1) ∧
      (∀ a b : ℝ, a ≤ b → dist (γ a) (γ b) ≤ b - a) ∧
      ∀ s ∈ Icc (0 : ℝ) (dist p q),
        dist p (γ s) = s ∧ dist (γ s) q = dist p q - s := by
  classical
  rcases eq_or_ne p q with rfl | hpq
  · -- `p = q`: the zero-velocity global geodesic through `p` does the job
    obtain ⟨γ, h0, hv, hc, hgeo⟩ := hp 0
    have hzero : speedSq (I := I) g γ 0 = 0 := by
      have hvfoot : HasDerivAt (fun s => extChartAt I (γ 0) (γ s)) (0 : E) 0 := by
        rw [h0]
        exact hv
      have h := speedSq_eq_chartMetricInner_of_hasDerivAt (I := I)
        (hgeo 0) hc.continuousAt hvfoot
      rw [h, show (0 : E) = (0 : ℝ) • (0 : E) by simp,
        chartMetricInner_smul_left]
      ring
    have h00 : chartMetricInner (I := I) g p (extChartAt I p p)
        (0 : E) (0 : E) = 0 := by
      rw [show (0 : E) = (0 : ℝ) • (0 : E) by simp, chartMetricInner_smul_left]
      ring
    refine ⟨γ, h0, ?_, hc, hgeo, ⟨0, hv, by rw [h00]; norm_num⟩, ?_, ?_⟩
    · rw [dist_self]
      exact h0
    · intro a b hab
      have h := IsGeodesicOn.dist_le (I := I) g hg (s := univ)
        (hgeo.isGeodesicOn univ) isOpen_univ isPreconnected_univ
        hc.continuousOn (mem_univ a) (mem_univ b) hab
      have hsp : speedSq (I := I) g γ a = 0 := by
        rw [← hzero]
        exact IsGeodesicOn.speedSq_eq (hgeo.isGeodesicOn univ) isOpen_univ
          isPreconnected_univ hc.continuousOn (mem_univ a) (mem_univ 0)
      rw [hsp, Real.sqrt_zero, zero_mul] at h
      have := dist_nonneg (x := γ a) (y := γ b)
      linarith
    · intro s hs
      rw [dist_self] at hs
      have hs0 : s = 0 := le_antisymm hs.2 hs.1
      subst hs0
      rw [dist_self, h0, dist_self]
      exact ⟨rfl, by ring⟩
  · set r : ℝ := dist p q with hrdef
    have hr : 0 < r := dist_pos.mpr hpq
    -- the sphere-minimum and ray data at `p`
    obtain ⟨ε, c, hε, hc, hdom, hstep⟩ :=
      exists_normalSphere_min_edist (I := I) g hg p
    obtain ⟨ρp, bp, hρp, hbp, hadmp, hrayp⟩ :=
      exists_isGeodesicOn_expMap_ray (I := I) g p
    have hbp0 : (0 : ℝ) < bp := lt_trans one_pos hbp
    have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    -- the first-step radius `δ`
    set m : ℝ := min ε ρp with hmdef
    have hm : 0 < m := lt_min hε hρp
    set δ : ℝ := min (r / 2) (m / (2 * Real.sqrt c)) with hδdef
    have hδ : 0 < δ := lt_min (by linarith) (by positivity)
    have hδr2 : δ ≤ r / 2 := min_le_left _ _
    have hδr : δ ≤ r := by linarith
    have hcδm : Real.sqrt c * δ < m := by
      have h1 : δ ≤ m / (2 * Real.sqrt c) := min_le_right _ _
      have h2 : Real.sqrt c * δ ≤ m / 2 := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt c)] at h1
        linarith
      linarith
    have hcδε : Real.sqrt c * δ < ε := hcδm.trans_le (min_le_left _ _)
    have hcδρ : Real.sqrt c * δ < ρp := hcδm.trans_le (min_le_right _ _)
    have hδq : ENNReal.ofReal δ ≤ edist p q := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    obtain ⟨z, hzc, hzε, hzgram, hzdist, hzdecomp, -⟩ :=
      hstep q δ hδ hcδε hδq
    have hzρ : ‖z‖ < ρp := hzc.trans_lt hcδρ
    obtain ⟨hray0, hrayv, hraycont, hraygeo⟩ := hrayp z hzρ
    -- the squared `g_p`-length of `z`
    have hQnonneg : ∀ v : E,
        0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v := fun v =>
      chartMetricInner_self_nonneg_of_mem_target (I := I) g p
        (mem_extChartAt_target p) v
    have hzsq : chartMetricInner (I := I) g p (extChartAt I p p) z z
        = δ ^ 2 := by
      have h := Real.sq_sqrt (hQnonneg z)
      rw [hzgram] at h
      linarith
    -- the global geodesic through `(p, z)`, reparametrized to unit speed
    obtain ⟨γt, hγt0, hγtv, hγtc, hγtgeo⟩ := hp z
    set γ : ℝ → M' := fun s : ℝ => γt (δ⁻¹ * s) with hγdef
    have hγgeo : IsGeodesic (I := I) g γ := fun t =>
      hasGeodesicEquationAt_comp_mul_left (I := I) (hγtgeo (δ⁻¹ * t))
    have hγc : Continuous γ := by
      have hin : Continuous fun s : ℝ => δ⁻¹ * s := by fun_prop
      exact hγtc.comp' hin
    have hγ0 : γ 0 = p := by
      show γt (δ⁻¹ * 0) = p
      rw [mul_zero]
      exact hγt0
    have hγv : HasDerivAt (fun s => extChartAt I p (γ s)) (δ⁻¹ • z) 0 := by
      have hin : HasDerivAt (fun s : ℝ => δ⁻¹ * s) δ⁻¹ 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_mul δ⁻¹
      have hout : HasDerivAt (fun s => extChartAt I p (γt s)) z (δ⁻¹ * 0) := by
        rw [mul_zero]
        exact hγtv
      exact HasDerivAt.scomp (0 : ℝ) hout hin
    -- `γ` has unit speed
    have huu : chartMetricInner (I := I) g p (extChartAt I p p)
        (δ⁻¹ • z) (δ⁻¹ • z) = 1 := by
      rw [chartMetricInner_smul_left, chartMetricInner_smul_right, hzsq]
      field_simp
    have hspeed : speedSq (I := I) g γ 0 = 1 := by
      have hvfoot : HasDerivAt (fun s => extChartAt I (γ 0) (γ s)) (δ⁻¹ • z) 0 := by
        rw [hγ0]
        exact hγv
      have h := speedSq_eq_chartMetricInner_of_hasDerivAt (I := I)
        (hγgeo 0) hγc.continuousAt hvfoot
      rw [h, hγ0, huu]
    -- the uniqueness identification of the initial segment with the ray
    have heqray : Set.EqOn γt
        (fun t : ℝ => expMap (I := I) g p ((t • z : E) : TangentSpace I p))
        (Ioo (-bp) bp) := by
      refine IsGeodesicOn.eqOn_of_hasDerivAt_chartReading (I := I)
        (u := z) (β := p) isOpen_Ioo isPreconnected_Ioo
        ((hγtgeo.isGeodesicOn _).mono (subset_univ _)) hraygeo
        hγtc.continuousOn hraycont ⟨by linarith, hbp0⟩
        (by rw [hγt0]; exact hray0.symm) ?_ ?_ ?_
      · rw [hγt0]; exact mem_chart_source H p
      · exact hγtv
      · exact hrayv
    -- the first step lands on the sphere: `γ δ = exp_p z`
    have hγδ : γ δ = expMap (I := I) g p (z : TangentSpace I p) := by
      have h1 : γ δ = γt 1 := by
        show γt (δ⁻¹ * δ) = γt 1
        rw [inv_mul_cancel₀ hδ.ne']
      have h2 := heqray (show (1 : ℝ) ∈ Ioo (-bp) bp from ⟨by linarith, hbp⟩)
      rw [h1, h2]
      show expMap (I := I) g p (((1 : ℝ) • z : E) : TangentSpace I p) = _
      rw [one_smul]
    -- distance facts for the first step, in real form
    have hdγδ : dist (γ δ) q = r - δ := by
      have h := hzdecomp
      rw [edist_dist, edist_dist, ← ENNReal.ofReal_add hδ.le dist_nonneg] at h
      have h2 := (ENNReal.ofReal_eq_ofReal_iff dist_nonneg
        (by positivity : (0 : ℝ) ≤ δ + dist (expMap (I := I) g p
          (z : TangentSpace I p)) q)).mp h
      rw [hγδ]
      linarith
    -- the exhaustion set `A`
    set A : Set ℝ := Icc 0 r ∩ {s | dist (γ s) q = r - s} with hAdef
    have hAclosed : IsClosed A :=
      isClosed_Icc.inter (isClosed_eq (by fun_prop) (by fun_prop))
    have hδA : δ ∈ A := ⟨⟨hδ.le, hδr⟩, hdγδ⟩
    have hAne : A.Nonempty := ⟨δ, hδA⟩
    have hAbdd : BddAbove A := ⟨r, fun a ha => ha.1.2⟩
    set s₀ : ℝ := sSup A with hs₀def
    have hs₀A : s₀ ∈ A := hAclosed.csSup_mem hAne hAbdd
    have hδs₀ : δ ≤ s₀ := le_csSup hAbdd hδA
    have hs₀pos : 0 < s₀ := lt_of_lt_of_le hδ hδs₀
    have hs₀r : s₀ ≤ r := hs₀A.1.2
    -- the triangle squeeze below `s₀`
    have hupA : ∀ s ∈ Icc (0 : ℝ) s₀,
        dist p (γ s) = s ∧ dist (γ s) q = r - s := by
      intro s hs
      have hlip0 : dist p (γ s) ≤ s := by
        have h := IsGeodesic.dist_le_of_speedSq_one (I := I) g hg hγgeo hγc
          hspeed (a := 0) (b := s) hs.1
        rw [hγ0] at h
        linarith [h]
      have hlips₀ : dist (γ s) (γ s₀) ≤ s₀ - s :=
        IsGeodesic.dist_le_of_speedSq_one (I := I) g hg hγgeo hγc hspeed hs.2
      have hupper : dist (γ s) q ≤ r - s := by
        calc dist (γ s) q ≤ dist (γ s) (γ s₀) + dist (γ s₀) q :=
              dist_triangle _ _ _
          _ ≤ (s₀ - s) + (r - s₀) := add_le_add hlips₀ (le_of_eq hs₀A.2)
          _ = r - s := by ring
      have hlower : r - s ≤ dist (γ s) q := by
        have h := dist_triangle p (γ s) q
        rw [← hrdef] at h
        linarith
      have hdq : dist (γ s) q = r - s := le_antisymm hupper hlower
      refine ⟨?_, hdq⟩
      have h := dist_triangle p (γ s) q
      rw [← hrdef, hdq] at h
      have : s ≤ dist p (γ s) := by linarith
      linarith
    -- the supremum is `r`
    have hs₀eq : s₀ = r := by
      by_contra hne
      have hlt : s₀ < r := lt_of_le_of_ne hs₀r hne
      have hup' : ∀ s ∈ Icc (0 : ℝ) s₀,
          dist (γ 0) (γ s) = s ∧ dist (γ s) q = r - s := by
        intro s hs
        rw [hγ0]
        exact hupA s hs
      obtain ⟨δ'', hδ''pos, hδ''le, hδ''fact⟩ :=
        exists_add_mem_of_lt (I := I) g hg hγgeo hγc hspeed hs₀pos hlt hup'
      have hmem : s₀ + δ'' ∈ A :=
        ⟨⟨by linarith, hδ''le⟩, hδ''fact⟩
      have := le_csSup hAbdd hmem
      linarith
    -- conclusion
    have hγr : γ r = q := by
      have h := hs₀A.2
      rw [hs₀eq] at h
      have : dist (γ r) q = 0 := by rw [h]; ring
      exact dist_eq_zero.mp this
    exact ⟨γ, hγ0, hγr, hγc, hγgeo, ⟨δ⁻¹ • z, hγv, le_of_eq huu⟩,
      fun a b hab =>
        IsGeodesic.dist_le_of_speedSq_one (I := I) g hg hγgeo hγc hspeed hab,
      fun s hs => hupA s (by rw [hs₀eq]; exact hs)⟩

omit [InnerProductSpace ℝ E] in
/-- **Math.** do Carmo Ch. 7, Theorem 2.8, f), unit-interval form: under the
hypotheses of `exists_minimizing_geodesic_of_forall_geodesic`, the two points
are joined by a geodesic segment `γ : [0,1] → M` parametrized proportionally
to arc length with `d(γ s, γ t) = |s - t| · d(p, q)` — every subsegment is
minimizing. -/
theorem exists_minimizing_geodesic_unitInterval (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) (p : M')
    (hp : ∀ v : TangentSpace I p, ∃ γ : ℝ → M', γ 0 = p ∧
      HasDerivAt (fun s => extChartAt I p (γ s)) v 0 ∧ Continuous γ ∧
        IsGeodesic (I := I) g γ)
    (q : M') :
    ∃ γ : ℝ → M', γ 0 = p ∧ γ 1 = q ∧ Continuous γ ∧
      IsGeodesic (I := I) g γ ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist p q := by
  classical
  obtain ⟨γ, hγ0, hγr, hγc, hγgeo, -, hlip, hfacts⟩ :=
    exists_minimizing_geodesic_of_forall_geodesic (I := I) g hg p hp q
  set r : ℝ := dist p q with hrdef
  have hr0 : 0 ≤ r := dist_nonneg
  set γ' : ℝ → M' := fun t : ℝ => γ (r * t) with hγ'def
  have hγ'geo : IsGeodesic (I := I) g γ' := fun t =>
    hasGeodesicEquationAt_comp_mul_left (I := I) (hγgeo (r * t))
  have hγ'c : Continuous γ' := by
    have hin : Continuous fun t : ℝ => r * t := by fun_prop
    exact hγc.comp' hin
  have hγ'0 : γ' 0 = p := by
    show γ (r * 0) = p
    rw [mul_zero]
    exact hγ0
  have hγ'1 : γ' 1 = q := by
    show γ (r * 1) = q
    rw [mul_one]
    exact hγr
  -- proportional-to-arclength distances
  have hkey : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b →
      dist (γ' a) (γ' b) = (b - a) * r := by
    intro a ha b hb hab
    have hrab : r * a ≤ r * b := by nlinarith
    have hra : r * a ∈ Icc 0 r := ⟨mul_nonneg hr0 ha.1, by nlinarith [ha.2]⟩
    have hrb : r * b ∈ Icc 0 r := ⟨mul_nonneg hr0 hb.1, by nlinarith [hb.2]⟩
    obtain ⟨hpa, -⟩ := hfacts (r * a) hra
    obtain ⟨hpb, -⟩ := hfacts (r * b) hrb
    refine le_antisymm ?_ ?_
    · -- upper: the Lipschitz bound
      have h := hlip (r * a) (r * b) hrab
      calc dist (γ' a) (γ' b) = dist (γ (r * a)) (γ (r * b)) := rfl
        _ ≤ r * b - r * a := h
        _ = (b - a) * r := by ring
    · -- lower: `d(p, ·)` grows by exactly the arclength
      have h := dist_triangle p (γ (r * a)) (γ (r * b))
      rw [hpa, hpb] at h
      calc (b - a) * r = r * b - r * a := by ring
        _ ≤ dist (γ (r * a)) (γ (r * b)) := by linarith
        _ = dist (γ' a) (γ' b) := rfl
  refine ⟨γ', hγ'0, hγ'1, hγ'c, hγ'geo, ?_⟩
  intro s hs t ht
  rcases le_total s t with hst | hts
  · rw [hkey s hs t ht hst, abs_of_nonpos (by linarith : s - t ≤ 0)]
    ring
  · rw [dist_comm (γ' s) (γ' t), hkey t ht s hs hts,
      abs_of_nonneg (by linarith : 0 ≤ s - t)]

end Exponential

end Riemannian
