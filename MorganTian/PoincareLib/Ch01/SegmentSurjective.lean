/-
# Surjectivity of `exp_p` onto `M ∖ C_p`

`prop:exponential-diffeomorphism-cut-locus` (Morgan–Tian, Ch. 1, §1.5) asserts that
`exp_p : U_p → M ∖ C_p` is a diffeomorphism.  `Ch01/SegmentInjective.lean` supplied the
**injectivity** clause; this file supplies the **surjectivity** clause in its sharp, metric form:

  every `q ∉ C_p` is `exp_p(v)` for a `v ∈ U_p` with `|v|_g = d(p, q)`.

The argument is the book's.  By Hopf–Rinow (`exists_minimizing_geodesic_unitInterval`, available
on the complete manifold) there is a minimizing geodesic `γ : [0,1] → M` from `p` to `q`,
distance-realizing (`d(γ s, γ t) = |s−t|·d(p,q)`).  Its initial chart velocity `v` makes
`γ = globalGeodesic g hg p v` (`globalGeodesic_eq`), so `exp_p(v) = γ(1) = q`, and its constant
speed is the distance (`sqrt_speedSq_eq_dist_of_minimizing` fed the distance-realizing clause,
combined with `speedSq_globalGeodesic`): `√(g_p(v,v)) = d(p,q)`.

Membership `v ∈ U_p` is the strict inequality `1 < cutTime(v)`.  The distance identity gives
`IsMinimizingUpTo v 1`, hence `1 ≤ cutTime(v)` (`le_cutTime_iff`).  It cannot be `= 1`: if it were,
then writing `v = ℓ·u` with `u` the `g`-unit direction and `ℓ = |v|_g`, the cut time of `u` would
be exactly `ℓ` (`cutTime_smul`) and `q = γ_v(1) = γ_u(ℓ)` would be the cut point of `u`, i.e.
`q ∈ C_p` — excluded.  So `1 < cutTime(v)`, `v ∈ U_p`.

This closes gap **(ii)** of `prop:exponential-diffeomorphism-cut-locus`, and is the
surjectivity input `(a'2)` of `thm:bishop-gromov` (the geodesic ball is the `exp_p`-image of the
segment domain up to the null cut locus) and of `thm:volume-injectivity-radius`.

Blueprint: `prop:exponential-diffeomorphism-cut-locus` (surjectivity clause); `def:cut-locus`.
-/
import PoincareLib.Ch01.SegmentInjective
import PoincareLib.Ch01.ExpLocalDiffeo
import PoincareLib.Ch01.ConstantGeodesicJacobi
import OpenGALib.Riemannian.Geodesic.HopfRinow
import OpenGALib.Riemannian.Exponential.ConvexNeighborhoodHuniq

open Set Filter Riemannian Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]

/-- **Math.** **`0 ∈ U_p`.** The zero vector lies in the segment domain: its radial geodesic is
constant, hence minimizing for all time, so `cutTime(0) = ⊤ > 1`. -/
theorem zero_mem_segmentDomain (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    (0 : TangentSpace I p) ∈ segmentDomain (I := I) g hg p := by
  rw [segmentDomain, mem_setOf_eq]
  have hmin : IsMinimizingUpTo (I := I) g hg p (0 : TangentSpace I p) 2 := by
    rw [IsMinimizingUpTo, globalGeodesic_zero_vec g hg p]
    simp
  have h2 : (ENNReal.ofReal 2 : ℝ≥0∞) ≤ cutTime (I := I) g hg p (0 : TangentSpace I p) :=
    le_cutTime (I := I) g hg p (0 : TangentSpace I p) ⟨by norm_num, hmin⟩
  refine lt_of_lt_of_le ?_ h2
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by norm_num)

/-- **Math.** **A vector with cut time `1` lands on the cut locus.** If `v ≠ 0` and the radial
geodesic `γ_v` stops being minimizing exactly at parameter `1` (`cutTime(v) = 1`), then its
endpoint `γ_v(1) = exp_p(v)` is a cut point.

The witness is the `g`-unit direction `u = |v|_g⁻¹ · v`, whose cut time is `|v|_g`
(`cutTime_smul`) and whose radial geodesic reaches `γ_v(1)` at parameter `|v|_g`
(`globalGeodesic_smul`).  Stated with `v : TangentSpace I p` so that the scalar action `•` is the
tangent-space one throughout (see `[[metricinner-smul-needs-tangent-typed-vector]]`).

Blueprint: `def:cut-locus`. -/
theorem globalGeodesic_cutTime_one_mem_cutLocus (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) (p : M) {v : TangentSpace I p} (hv : v ≠ 0)
    (hcut : cutTime (I := I) g hg p v = 1) :
    globalGeodesic (I := I) g hg p v 1 ∈ cutLocus (I := I) g hg p := by
  set ℓ : ℝ := Real.sqrt (g.metricInner p v v) with hℓdef
  have hgvvpos : 0 < g.metricInner p v v := g.metricInner_self_pos p v hv
  have hℓpos : 0 < ℓ := by rw [hℓdef, Real.sqrt_pos]; exact hgvvpos
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓpos
  have hgvv : g.metricInner p v v = ℓ ^ 2 := by rw [hℓdef, Real.sq_sqrt hgvvpos.le]
  refine ⟨ℓ⁻¹ • v, ?_, ℓ, hℓpos.le, ?_, ?_⟩
  · -- the direction is a `g`-unit vector
    rw [g.metricInner_smul_left, g.metricInner_smul_right, hgvv]
    field_simp
  · -- its cut time is `ℓ = |v|_g`
    have hstep := cutTime_smul (I := I) g hg p v (c := ℓ⁻¹) (b := 1)
      (by positivity) (by norm_num) (by rw [hcut]; simp)
    rw [hstep]; congr 1; rw [one_div, inv_inv]
  · -- `γ_v(1) = γ_u(ℓ)`
    have hsmul : (ℓ • (ℓ⁻¹ • v) : TangentSpace I p) = v := by
      rw [← mul_smul, mul_inv_cancel₀ hℓne, one_smul]
    have hgs := congrFun (globalGeodesic_smul g hg p (ℓ⁻¹ • v) ℓ) 1
    rw [hsmul, mul_one] at hgs
    exact hgs

/-- **Math.** **Surjectivity of `exp_p` onto `M ∖ C_p`, metric form** — gap `(ii)` of
`prop:exponential-diffeomorphism-cut-locus`, and the surjectivity input `(a'2)` of
`thm:bishop-gromov` / `thm:volume-injectivity-radius`.

Every point `q` off the cut locus is the exponential image of a vector `v` in the segment domain
whose length is the distance `d(p, q)`. -/
theorem exists_mem_segmentDomain_expMapGlobal_eq (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [ConnectedSpace M] (p : M)
    {q : M} (hq : q ∉ cutLocus (I := I) g hg p) :
    ∃ v : TangentSpace I p, v ∈ segmentDomain (I := I) g hg p ∧
      expMapGlobal (I := I) g hg p v = q ∧
      Real.sqrt (g.metricInner p v v) = dist p q := by
  classical
  by_cases hpq : q = p
  · -- `q = p`: the zero vector works.
    rw [hpq]
    exact ⟨(0 : TangentSpace I p), zero_mem_segmentDomain g hg p,
      expMapGlobal_zero g hg p, by simp⟩
  · -- `q ≠ p`: Hopf–Rinow gives a minimizing geodesic; read off its initial velocity.
    have hp : ∀ v : TangentSpace I p, ∃ γ : ℝ → M, γ 0 = p ∧
        HasDerivAt (fun s => extChartAt I p (γ s)) v 0 ∧ Continuous γ ∧
          IsGeodesic (I := I) g γ := by
      intro v
      obtain ⟨γ, h0, hv, hc, hgeo⟩ := exists_global_geodesic (I := I) g hg p v
      exact ⟨γ, h0, hv, hc, hgeo⟩
    obtain ⟨γ, hγ0, hγ1, hγc, hγgeo, hdist⟩ :=
      exists_minimizing_geodesic_unitInterval (I := I) g hg p hp q
    -- initial chart velocity `v`
    obtain ⟨v, _a, hv, _, _, _⟩ := hγgeo 0
    have hvp : HasDerivAt (fun s => extChartAt I p (γ s)) v 0 := by
      have hrw : chartLocalCurve (I := I) γ 0 = fun s => extChartAt I p (γ s) := by
        funext s; simp only [chartLocalCurve_def, hγ0]
      rwa [hrw] at hv
    have hγeq : γ = globalGeodesic (I := I) g hg p v :=
      globalGeodesic_eq g hg hγgeo hγc hγ0 hvp
    -- `exp_p v = q`
    have hexp : expMapGlobal (I := I) g hg p v = q := by
      rw [expMapGlobal_def, ← hγeq]; exact hγ1
    -- `√(g_p(v,v)) = d(p, q)`
    have hsqrtspeed : Real.sqrt (speedSq (I := I) g γ 0) = dist p q := by
      refine sqrt_speedSq_eq_dist_of_minimizing (I := I) g hg
        (lo := -1) (hi := 2) (by norm_num) (by norm_num)
        (hγgeo.isGeodesicOn _) (hγc.continuousOn) hγ0 hγ1 ?_
      intro s hs t ht; exact hdist s hs t ht
    have hspeed : speedSq (I := I) g γ 0 = g.metricInner p v v := by
      rw [hγeq]; exact speedSq_globalGeodesic g hg p v
    have hnorm : Real.sqrt (g.metricInner p v v) = dist p q := by
      rw [← hspeed]; exact hsqrtspeed
    refine ⟨v, ?_, hexp, hnorm⟩
    -- `v ∈ U_p`, i.e. `1 < cutTime(v)`.
    -- distance identity gives `IsMinimizingUpTo v 1`, hence `1 ≤ cutTime v`.
    have hglob1 : globalGeodesic (I := I) g hg p v 1 = q := by
      rw [← expMapGlobal_def]; exact hexp
    have hmin1 : IsMinimizingUpTo (I := I) g hg p v 1 := by
      rw [IsMinimizingUpTo, hglob1, mul_one, hnorm]
    have hle1 : (1 : ℝ≥0∞) ≤ cutTime (I := I) g hg p v := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
      exact (le_cutTime_iff (I := I) g hg p v (by norm_num)).2 hmin1
    -- `v ≠ 0` since `|v|_g = d(p,q) > 0`.
    have hdpos : 0 < dist p q := dist_pos.mpr (fun h => hpq h.symm)
    have hvne : (v : TangentSpace I p) ≠ 0 := by
      intro h
      have hz : g.metricInner p v v = 0 := by rw [h]; exact g.metricInner_zero_left p 0
      rw [hz, Real.sqrt_zero] at hnorm
      exact hdpos.ne' hnorm.symm
    -- strictness: if `cutTime v = 1` then `q` would be the cut point of the unit direction.
    rw [segmentDomain, mem_setOf_eq]
    rcases lt_or_eq_of_le hle1 with hlt | heq
    · exact hlt
    · -- `cutTime v = 1`; then `q = γ_v(1)` is a cut point, contradicting `q ∉ C_p`.
      exfalso
      apply hq
      rw [← hglob1]
      exact globalGeodesic_cutTime_one_mem_cutLocus g hg p hvne heq.symm

end PoincareLib

end
