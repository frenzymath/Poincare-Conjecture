import MorganTianLib.Ch01.CutTimeMeasurable
import MorganTianLib.Ch01.MeasureNull
import MorganTianLib.Ch01.RadialNull

/-!
# Morgan–Tian Ch. 1, §1.5 — the cut locus has measure zero

The keystone of the volume theory, blueprint `lem:cut-locus-properties`(3):

  `riemannianMeasure_cutLocus_eq_zero` : `μ_g (C_p) = 0`.

Everything downstream that computes `Vol B(p,r)` in the exponential chart needs it: `exp_p` maps the
segment domain `U_p` *onto* `M ∖ C_p`, so the change of variables sees all of `B(p,r)` only up to
`C_p`, and the comparison estimates are worthless unless that discrepancy is null.

## The route, and why it is not the blueprint's

The blueprint derives nullity from `lem:localized-cut-locus`(4), whose proof appeals to **Sard's
theorem** ("the set of critical values has measure zero"). Mathlib has no general Sard theorem, and
even the equidimensional case it does have would only handle the *conjugate* cut points, leaving the
points joined to `p` by two minimizing geodesics untreated.

The argument formalized here needs no Sard, and treats both kinds of cut point at once. It rests on
a single observation:

  **the cut locus is the `exp_p`-image of a radial graph.**

Write `c(v)` for the cut time. The cut points are exactly the images `exp_p(c(u)·u)` of the *cut
vectors* — the radial boundary of the star-shaped domain `U_p`. Because the cut time rescales as
`c(λv) = c(v)/λ` (`cutTime_smul`), a vector `v ≠ 0` is a cut vector precisely when `c(v) = 1`; so the
set of cut vectors is a **level set of the cut time**, and each ray from the origin meets it at most
once — a cut point is reached *once* along each geodesic, by definition of the cut time.

A set meeting each ray at most once is Lebesgue-null (`addHaar_eq_zero_of_isRadialGraph`: polar
coordinates plus Fubini, the radial slices being singletons), it is measurable because the cut time
is (`measurable_cutTime`, from upper semicontinuity), and `exp_p` carries null sets to null sets
(`riemannianMeasure_expMapGlobal_image_eq_zero`). That is the whole proof.

Note what is *not* needed: continuity of the cut time, openness of `U_p`, the Klingenberg
dichotomy, conjugate points, or any curvature hypothesis. Lower semicontinuity of `c` — the hard
half, and the one that gives `U_p` open — is genuinely not used; measurability suffices.
-/

open MeasureTheory Measure Set Filter Metric Riemannian Riemannian.Geodesic
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

-- Diamond-free model-space block (see `ExpContinuity`): no standalone `[NormedSpace ℝ E]`.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

/-! ## The cut vectors -/

/-- **Math.** The **cut vectors** of `p`: the non-zero `v ∈ T_pM` whose radial geodesic `γ_v` stops
minimizing exactly at parameter `1`, i.e. `c(v) = 1`.

Equivalently — and this is the content of `cutLocus_subset_image_cutVectors` — these are the vectors
`c(u)·u` over the unit directions `u` of finite cut time: the radial boundary of the segment domain
`U_p = {v : c(v) > 1}`. Phrasing it as the level set `{c = 1}` rather than as a parameterised image
is what makes it visibly measurable. -/
def cutVectors (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) : Set E :=
  {v : E | v ≠ 0 ∧ cutTime (I := I) g hg p (v : TangentSpace I p) = 1}

/-- **Math.** The cut vectors form a measurable set: a level set of the measurable cut time, minus
the origin. -/
theorem measurableSet_cutVectors (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    MeasurableSet (cutVectors (I := I) g hg p) := by
  have h1 : MeasurableSet
      {v : E | cutTime (I := I) g hg p (v : TangentSpace I p) = 1} :=
    (measurable_cutTime (I := I) g hg p) (measurableSet_singleton (1 : ℝ≥0∞))
  have h2 : MeasurableSet {v : E | v ≠ 0} := (measurableSet_singleton (0 : E)).compl
  exact h2.inter h1

/-- **Math.** **The cut vectors form a radial graph**: each ray from the origin contains at most one
of them.

This is the defining property of a *cut*: along the ray `{t·u : t > 0}` the radial geodesic
minimizes up to the cut time and not past it, so exactly one point of the ray can have cut time `1`.
Formally, if `r₁·u` and `r₂·u` both have cut time `1`, then rescaling by `λ = r₂/r₁` gives
`1 = c(r₂·u) = c(λ·(r₁·u)) = c(r₁·u)/λ = 1/λ`, so `λ = 1`. -/
theorem isRadialGraph_cutVectors (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    IsRadialGraph (cutVectors (I := I) g hg p) := by
  intro u _ r₁ r₂ hr₁ hr₂ h₁ h₂
  -- `r₂ • u = (r₂/r₁) • (r₁ • u)`, and the cut time of the rescaled vector is `1/(r₂/r₁)`
  set lam : ℝ := r₂ / r₁ with hlam
  have hlampos : 0 < lam := div_pos hr₂ hr₁
  have hcut1 : cutTime (I := I) g hg p ((r₁ • u : E) : TangentSpace I p)
      = ENNReal.ofReal 1 := by rw [h₁.2, ENNReal.ofReal_one]
  have hscaled := cutTime_smul (I := I) g hg p ((r₁ • u : E) : TangentSpace I p)
    hlampos zero_le_one hcut1
  -- `r₂ • u = λ • (r₁ • u)`, transported at the `TangentSpace` scalar action
  have heq : ((r₂ • u : E) : TangentSpace I p)
      = (lam • ((r₁ • u : E) : TangentSpace I p) : TangentSpace I p) := by
    show (r₂ • u : E) = (lam • (r₁ • u) : E)
    rw [smul_smul, hlam, div_mul_cancel₀ r₂ (ne_of_gt hr₁)]
  have hres : cutTime (I := I) g hg p ((r₂ • u : E) : TangentSpace I p)
      = ENNReal.ofReal (1 / lam) := by rw [heq]; exact hscaled
  rw [h₂.2] at hres
  -- so `1 = ofReal (1/λ)`, forcing `λ = 1`, i.e. `r₁ = r₂`
  have hone : (1 : ℝ) / lam = 1 := by
    have h : ENNReal.ofReal (1 : ℝ) = ENNReal.ofReal (1 / lam) := by
      rw [ENNReal.ofReal_one]; exact hres
    exact ((ENNReal.ofReal_eq_ofReal_iff zero_le_one (by positivity)).1 h).symm
  rw [div_eq_one_iff_eq (ne_of_gt hlampos)] at hone
  rw [hlam, eq_comm, div_eq_one_iff_eq (ne_of_gt hr₁)] at hone
  exact hone.symm

/-! ## The cut locus is the image of the cut vectors -/

/-- **Math.** **Every cut point is the exponential of a cut vector** (or of the origin).

Unwinding `cutLocus`: a cut point is `γ_u(c) = exp_p(c·u)` for a `g`-unit `u` with `c(u) = c < ∞`.
If `c = 0` the "cut point" is `p = exp_p(0)`. If `c > 0` then `c(c·u) = c/c = 1` by `cutTime_smul`,
so `c·u` is a cut vector. -/
theorem cutLocus_subset_image_cutVectors (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) :
    cutLocus (I := I) g hg p
      ⊆ (fun w : E => expMapGlobal (I := I) g hg p w) ''
          (insert (0 : E) (cutVectors (I := I) g hg p)) := by
  rintro x ⟨u, hu, c, hc0, hcut, rfl⟩
  -- the cut point is `exp_p (c • u)`
  have hgeo : globalGeodesic (I := I) g hg p u c
      = expMapGlobal (I := I) g hg p ((c • u : TangentSpace I p)) :=
    globalGeodesic_eq_expMapGlobal_smul (I := I) g hg p u c
  rw [hgeo]
  rcases eq_or_lt_of_le hc0 with rfl | hcpos
  · -- degenerate case: the cut time vanishes, the "cut point" is `p` itself
    refine ⟨(0 : E), mem_insert _ _, ?_⟩
    show expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p)
      = expMapGlobal (I := I) g hg p ((0 • u : TangentSpace I p))
    congr 1
    exact (zero_smul ℝ u).symm
  · -- the honest case: `c • u` is a cut vector
    have hune : (u : E) ≠ 0 := by
      intro h
      have h0 : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 0 := by
        show (g.inner p) u u = 0
        rw [show (u : TangentSpace I p) = (0 : TangentSpace I p) from h]
        simp
      rw [h0] at hu
      exact zero_ne_one hu
    exact ⟨(c • u : E), mem_insert_of_mem _
      ⟨smul_ne_zero (ne_of_gt hcpos) hune,
        cutTime_smul_eq_one (I := I) g hg p hcpos hcut⟩, rfl⟩

/-! ## The cut locus is null -/

/-- **Math.** **The cut locus has measure zero** — blueprint `lem:cut-locus-properties`(3).

`C_p ⊆ exp_p(cut vectors ∪ {0})`; the cut vectors form a measurable radial graph, hence are
Lebesgue-null in `T_pM`, and the origin is a single point (Haar measure on a non-trivial space is
atomless). `exp_p` is differentiable in charts, so it sends this null set to a `μ_g`-null set. -/
theorem riemannianMeasure_cutLocus_eq_zero (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (μ : Measure E) [μ.IsAddHaarMeasure] (p : M) :
    riemannianMeasure (I := I) g μ (cutLocus (I := I) g hg p) = 0 := by
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ)
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  -- the cut vectors are null in `T_pM`
  have hcv : μ (cutVectors (I := I) g hg p) = 0 :=
    addHaar_eq_zero_of_isRadialGraph μ (measurableSet_cutVectors (I := I) g hg p)
      (fun h => h.1 rfl) (isRadialGraph_cutVectors (I := I) g hg p)
  -- adding the origin changes nothing: Haar measure on a non-trivial space has no atoms
  have hins : μ (insert (0 : E) (cutVectors (I := I) g hg p)) = 0 := by
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton (0 : E)) hcv
  -- push forward along `exp_p`, which sends null sets to null sets
  exact measure_mono_null (cutLocus_subset_image_cutVectors (I := I) g hg p)
    (riemannianMeasure_expMapGlobal_image_eq_zero μ g hg p hins)

end MorganTianLib

end
