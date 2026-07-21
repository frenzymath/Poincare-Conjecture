import PetersenLib.Ch06.Myers
import PetersenLib.Ch06.VelocityParallel
import PetersenLib.Ch06.IntrinsicExpVariation
import PetersenLib.Ch05.SegmentNotation
import PetersenLib.Ch05.HopfRinowTheorem
import PetersenLib.Ch05.DistanceGeodesics
import PetersenLib.Ch05.GeodesicSmoothness
import PetersenLib.Ch03.RicciCovariantDerivative
import PetersenLib.Ch03.ScalarFormulas
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# The Hopf–Rinow–Myers diameter bound (Petersen §6.3, Cor 6.3.2 / Thm 6.3.3)

This file proves the diameter-and-compactness content of Corollary 6.3.2 (Hopf–Rinow 1931 /
Myers 1932, `sec ≥ k > 0`) and Theorem 6.3.3 (Myers 1941, `Ric ≥ (n-1)k > 0`): a complete
manifold under the curvature bound has `Metric.diam ≤ π/√k` and is `CompactSpace`.  The curvature
bound is **genuinely consumed** (via `bonnetSynge_index_core` / `myers_index_core`); the only
hypothesis carried is the *technical* existence of the exponential variation — the same
slab-smoothness gap already carried, as a hypothesis, by the sanctioned-`\leanok` Lemma 6.3.1
(`bonnetSynge_longGeodesicsNotMinimizing`).  The diameter-and-compactness declarations are
axiom-clean.  The final compact-cover-to-finite-`π₁` implication is formalized in
`Ch06/MyersFundamentalGroup.lean`; constructing the universal Riemannian cover and transferring
the geometric hypotheses to it remain open, so the headline blueprint nodes remain incomplete.

**Unconditional (fully proved) ingredients.**

* `isLocalMin_deriv_deriv_nonneg` — the *converse second-derivative test* on `ℝ`: a function
  with a local minimum, `φ'(x)=0` and continuous at `x`, has `0 ≤ φ''(x)` (a mathlib gap).
* `riemannianDistance_sq_le_two_mul_len_mul_energyFunctional` — the **energy–distance inequality**
  `d(γ₀,γ_l)² ≤ 2 l · E(γ)` on `[0,l]`, from Cauchy–Schwarz and `d ≤ L`.
* `secondVariation_nonneg_of_energyMinimizer` — index-form nonnegativity of an energy minimizer.
* `riemannianDistance_lt_of_secondVariation_neg` — the **not-minimizing bridge** on the raw
  variation: a unit-speed geodesic admitting a proper variation with `d²E/ds²|₀ < 0` (plus the
  base facts `E=l/2`, `L=l`, first-variation differentiability) is **not** distance-realizing
  (`d < l`).  This is the step `Ch06/Myers.lean` records as "not provided here".

**The faithful wiring.**

* `IsBonnetSyngeVariation` / `IsMyersRicciVariation` — the variation-data bundles (regularity
  only: slab-smoothness, geodesic base, fixed endpoints, unit parallel ⟂ field, `sin(π·/l)·E`
  variation field, integrability); *no* curvature bound, *no* not-minimizing claim.  This is
  Lemma 6.3.1's hypothesis bundle, existentially quantified over segments.
* `riemannianDistance_lt_of_negSecondVar_unitSpeed` — packages the base-fact discharge and the
  bridge (shared by the sectional and Ricci wirings).
* `longGeodesic_notMinimizing_of_secBound` — `sec ≥ k` ⟹ `bonnetSynge_index_core` ⟹
  `d²E/ds² < 0` ⟹ `d < l`.
* `longGeodesic_notMinimizing_of_ricciBound` — the frame-sum Ricci analogue via
  `myers_index_core`.
* `diameterBound_of_notMinimizing` — the Hopf–Rinow-segment + Heine–Borel metric passage,
  taking the (now-derivable) not-minimizing input.
* `myersRicciDiameterBound_of_indexNonneg` — the global Myers assembly after reducing the
  remaining geometric input to the nonnegativity of the standard sine-field index expressions;
  no two-parameter variation or slab-smoothness data appears in this interface.
* `myersRicciDiameterBound_of_velocityFrameIndexNonneg` — additionally constructs the
  velocity-seeded parallel orthonormal frame, derives unit speed and the Ricci frame sum, and
  leaves only per-perpendicular-direction minimizing-index nonnegativity to the caller.
* `hopfRinowMyers_diameterBound` (6.3.2) / `myersRicciDiameterBound` (6.3.3) — the headline
  theorems: a genuine sectional / Ricci curvature bound plus `hvar` (technical variation and
  frame existence) imply `diam ≤ π/√k ∧ compact`.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval Real

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace PetersenLib

open PetersenLib.Jacobi

open PetersenLib.Tensor

/-! ## A converse second-derivative test (mathlib gap) -/

/-- **Math.** Converse second-derivative test on `ℝ`: if `φ` has a local minimum
at `x`, is differentiable there with `φ'(x) = 0`, and is continuous at `x`, then
its second derivative is nonnegative, `0 ≤ φ''(x)`.

Mathlib provides the forward direction (`isLocalMax_of_deriv_deriv_neg`:
`φ''(x) < 0 ∧ φ'(x) = 0 ⟹` local max) but not this converse.  Were `φ''(x) < 0`,
that lemma would make `x` a local *maximum* as well; a point that is both a local
min and a local max has `φ` locally constant, forcing `φ''(x) = 0`, a
contradiction. -/
theorem isLocalMin_deriv_deriv_nonneg {φ : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin φ x) (hderiv : deriv φ x = 0) (hcont : ContinuousAt φ x) :
    0 ≤ deriv (deriv φ) x := by
  by_contra h
  rw [not_le] at h
  have hmax : IsLocalMax φ x := isLocalMax_of_deriv_deriv_neg h hderiv hcont
  have heq : φ =ᶠ[𝓝 x] fun _ => φ x := by
    filter_upwards [hmin, hmax] with y hy1 hy2 using le_antisymm hy2 hy1
  have hd0 : deriv φ =ᶠ[𝓝 x] fun _ : ℝ => (0 : ℝ) := by simpa using heq.deriv
  have hxx : deriv (deriv φ) x = deriv (fun _ : ℝ => (0 : ℝ)) x := hd0.deriv_eq
  rw [hxx, deriv_const'] at h
  exact lt_irrefl 0 h

end PetersenLib

section MetricLayer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [LocallyCompactSpace M]
  [T2Space (TangentBundle I M)] [ConnectedSpace M]

namespace PetersenLib

/-! ## The energy–distance inequality -/

/-- **Math.** Distance is bounded by the length of any connecting piecewise-`C∞`
curve, on an arbitrary interval `[0,l]` (not just `[0,1]`): reparametrise
`γ` affinely to `[0,1]` (`isPiecewiseSmoothCurve_comp_mul_add`,
`curveLength_comp_mul_add`) and apply `riemannianDistance_le_curveLength`. -/
theorem riemannianDistance_le_curveLength_Icc0 (g : RiemannianMetric I M) {γ : ℝ → M}
    {l : ℝ} (hl : 0 < l) (hγ : IsPiecewiseSmoothCurve (I := I) γ 0 l) :
    riemannianDistance (I := I) g (γ 0) (γ l) ≤ curveLength (I := I) g γ 0 l := by
  have hη : IsPiecewiseSmoothCurve (I := I) (fun s => γ (l * s + 0)) 0 1 := by
    refine isPiecewiseSmoothCurve_comp_mul_add (I := I) hl ?_
    simpa using hγ
  have h0 : (fun s => γ (l * s + 0)) 0 = γ 0 := by simp
  have h1 : (fun s => γ (l * s + 0)) 1 = γ l := by simp
  have hd := riemannianDistance_le_curveLength (I := I) g hη h0 h1
  rw [curveLength_comp_mul_add (I := I) g γ hl.le 0 0 1] at hd
  simpa using hd

/-- **Math.** The **energy–distance inequality** `d(γ₀, γ_l)² ≤ 2 l · E(γ|₀ˡ)` for
a piecewise-`C∞` curve `γ` on `[0,l]`, `l > 0`.  Combine `d ≤ L`
(`riemannianDistance_le_curveLength_Icc0`) with Cauchy–Schwarz
`L² ≤ l · 2E` (`curveLength_sq_le_sub_mul_two_mul_energyFunctional`). -/
theorem riemannianDistance_sq_le_two_mul_len_mul_energyFunctional (g : RiemannianMetric I M)
    {γ : ℝ → M} {l : ℝ} (hl : 0 < l) (hγ : IsPiecewiseSmoothCurve (I := I) γ 0 l) :
    riemannianDistance (I := I) g (γ 0) (γ l) ^ 2
      ≤ 2 * l * energyFunctional (I := I) g γ 0 l := by
  have hd := riemannianDistance_le_curveLength_Icc0 (I := I) g hl hγ
  have hd0 : 0 ≤ riemannianDistance (I := I) g (γ 0) (γ l) :=
    riemannianDistance_nonneg (I := I) g _ _
  have hL0 : 0 ≤ curveLength (I := I) g γ 0 l := curveLength_nonneg (I := I) g γ hl.le
  have hCS := curveLength_sq_le_sub_mul_two_mul_energyFunctional (I := I) g hl.le hγ
  have hdsq : riemannianDistance (I := I) g (γ 0) (γ l) ^ 2
      ≤ curveLength (I := I) g γ 0 l ^ 2 := by
    exact pow_le_pow_left₀ hd0 hd 2
  calc riemannianDistance (I := I) g (γ 0) (γ l) ^ 2
      ≤ curveLength (I := I) g γ 0 l ^ 2 := hdsq
    _ ≤ (l - 0) * (2 * energyFunctional (I := I) g γ 0 l) := hCS
    _ = 2 * l * energyFunctional (I := I) g γ 0 l := by ring

/-! ## The index-form nonnegativity bridge -/

/-- **Math.** Petersen §6.3, the **not-minimizing bridge** (contrapositive form): if a
piecewise-`C∞` curve `σ` **minimizes energy** among curves with the same endpoints
on `[a,b]`, then along *every* proper variation the **second variation of energy is
nonnegative**, `0 ≤ d²E(σ_s)/ds²|₀`.

This is the classical statement that the index form of a minimizing geodesic is
positive semidefinite.  It closes the gap flagged in `Ch06/Myers.lean` ("the passage
from a negative second variation to *not minimizing* … is not provided here"):
contrapositively, a proper variation with `d²E/ds² < 0` (Bonnet–Synge 6.3.1,
Myers 6.3.3) forces `σ` **not** to be an energy minimizer, hence not
distance-minimizing.  Proof: `energyLocalMin_of_energyMinimizer` turns the minimizing
hypothesis into `IsLocalMin (E∘σ_·) 0`, and the converse second-derivative test
`isLocalMin_deriv_deriv_nonneg` concludes. -/
theorem secondVariation_nonneg_of_energyMinimizer (g : RiemannianMetric I M)
    {σ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hmin : ∀ c : ℝ → M, IsPiecewiseSmoothCurve (I := I) c a b → c a = σ a → c b = σ b →
      energyFunctional (I := I) g σ a b ≤ energyFunctional (I := I) g c a b)
    (V : CurveVariation (I := I) σ a b) (hV : IsProperVariation V)
    (hderiv : deriv (fun s => energyFunctional (I := I) g (V.curve s) a b) 0 = 0)
    (hcont : ContinuousAt (fun s => energyFunctional (I := I) g (V.curve s) a b) 0) :
    0 ≤ deriv (deriv (fun s => energyFunctional (I := I) g (V.curve s) a b)) 0 :=
  isLocalMin_deriv_deriv_nonneg
    (energyLocalMin_of_energyMinimizer (I := I) g hab hmin V hV) hderiv hcont

/-- **Math.** Petersen §6.3, the **not-minimizing bridge** in geometric form: a unit-speed
geodesic `c = f(0,·)` on `[0,l]` that admits a proper variation `f` with strictly negative
second variation of energy does **not** realize the distance between its endpoints,
`d(c(0), c(l)) < l`.

This is exactly the step `Ch06/Myers.lean` records as "not provided here".  Proof: were
`d(c(0),c(l)) = l` (minimizing), the energy–distance inequality would make every nearby curve
`f_s` have `E(f_s) ≥ l/2 = E(c)`, so `s = 0` is a local minimum of `s ↦ E(f_s)`; the converse
second-derivative test `isLocalMin_deriv_deriv_nonneg` then forces `d²E/ds²|₀ ≥ 0`,
contradicting `h2neg`.  The unit-speed base facts `E(c) = l/2`, `L(c) = l` and the first-variation
differentiability `hφ1` are inputs (routine consequences of `f(0,·)` being a unit-speed geodesic,
supplied by the caller); the strictly negative second variation `h2neg` is the Bonnet–Synge /
Myers output. -/
theorem riemannianDistance_lt_of_secondVariation_neg (g : RiemannianMetric I M)
    {f : ℝ → ℝ → M} {δ l : ℝ} (hδ : 0 < δ) (hl : 0 < l)
    (hslice : ∀ s ∈ Set.Ioo (-δ) δ, IsPiecewiseSmoothCurve (I := I) (f s) 0 l)
    (hfix₀ : ∀ s, f s 0 = f 0 0) (hfixl : ∀ s, f s l = f 0 l)
    (hlen0 : curveLength (I := I) g (f 0) 0 l = l)
    (hE0 : energyFunctional (I := I) g (f 0) 0 l = l / 2)
    (hφ1 : DifferentiableAt ℝ (fun s => energyFunctional (I := I) g (f s) 0 l) 0)
    (h2neg : deriv (deriv (fun s => energyFunctional (I := I) g (f s) 0 l)) 0 < 0) :
    riemannianDistance (I := I) g (f 0 0) (f 0 l) < l := by
  set φ := fun s => energyFunctional (I := I) g (f s) 0 l with hφdef
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  by_contra hcon
  rw [not_lt] at hcon
  -- `d ≤ L(c) = l`, so together with `hcon` the geodesic is distance-realizing
  have hle : riemannianDistance (I := I) g (f 0 0) (f 0 l) ≤ l := by
    have h := riemannianDistance_le_curveLength_Icc0 (I := I) g hl (hslice 0 h0mem)
    rwa [hlen0] at h
  have hdeq : riemannianDistance (I := I) g (f 0 0) (f 0 l) = l := le_antisymm hle hcon
  -- `s = 0` is a local minimum of the energy along the variation
  have hmin : IsLocalMin φ 0 := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
    show φ 0 ≤ φ s
    have hsq := riemannianDistance_sq_le_two_mul_len_mul_energyFunctional
      (I := I) g hl (hslice s hs)
    rw [hfix₀ s, hfixl s, hdeq] at hsq
    have hs2 : l / 2 ≤ energyFunctional (I := I) g (f s) 0 l := by nlinarith [hl]
    simpa only [hφdef, hE0] using hs2
  have hderiv0 : deriv φ 0 = 0 := hmin.deriv_eq_zero
  have hcont : ContinuousAt φ 0 := hφ1.continuousAt
  have hnn := isLocalMin_deriv_deriv_nonneg hmin hderiv0 hcont
  rw [hφdef] at hnn
  linarith [h2neg]

/-! ## The diameter bound (Cor 6.3.2 / Thm 6.3.3) -/

/-- **Math.** The distance `d(p,q)` of the ambient metric space is bounded by the
Riemannian distance of `g` (they in fact agree under `hg`; this `≤` half is all we
need).  This is the forward bridge extracted from
`completeManifold_allPointsJoinedBySegment`'s proof. -/
theorem dist_le_riemannianDistance (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p q : M) : dist p q ≤ riemannianDistance (I := I) g p q := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI hRM : IsRiemannianManifold I M := hg
  have hb : ENNReal.ofReal (dist p q)
      ≤ ENNReal.ofReal (riemannianDistance (I := I) g p q) := by
    calc ENNReal.ofReal (dist p q) = edist p q := (edist_dist p q).symm
      _ = Manifold.riemannianEDist I p q := IsRiemannianManifold.out (I := I) p q
      _ ≤ ENNReal.ofReal (riemannianDistance (I := I) g p q) :=
          riemannianEDist_le_ofReal_riemannianDistance (I := I) g p q
  exact (ENNReal.ofReal_le_ofReal_iff (riemannianDistance_nonneg (I := I) g p q)).mp hb

/-- **Math.** Petersen §6.3, the diameter + compactness **assembly** underlying Corollary 6.3.2
(Hopf–Rinow 1931 / Myers 1932) and Theorem 6.3.3 (Myers 1941).  A complete manifold in which
**no unit-speed distance-realizing segment is longer than `π/√k`** (the hypothesis `hBS`) has
`diam ≤ π/√k` and is compact.  This isolates the metric-topology passage — *from* the
not-minimizing input *to* the diameter/compactness conclusion — via Hopf–Rinow segments and
Heine–Borel; the geometric input `hBS` is discharged from `sec ≥ k` / `Ric ≥ (n-1)k` by the
faithful theorems below.  The separate topological implication from a compact simply connected
cover to finite `π₁` is `finite_fundamentalGroup_of_compact_simplyConnected_cover`. -/
theorem diameterBound_of_notMinimizing (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] {k : ℝ} (hk : 0 < k)
    (hBS : ∀ (σ : ℝ → M) (l : ℝ), π / Real.sqrt k < l →
      IsSegment (I := I) g σ 0 l →
      (∀ t ∈ Set.Icc (0:ℝ) l, curveLength (I := I) g σ 0 t = t) →
      riemannianDistance (I := I) g (σ 0) (σ l) < l) :
    Metric.diam (Set.univ : Set M) ≤ π / Real.sqrt k ∧ CompactSpace M := by
  have hC : (0 : ℝ) ≤ π / Real.sqrt k :=
    (div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)).le
  -- Hopf–Rinow: completeness upgrades to the Heine–Borel (proper) property
  haveI hProper : ProperSpace M := ((hopfRinowTheorem (I := I) g hg).out 3 2).mp ‹CompleteSpace M›
  -- every Riemannian distance is `≤ π/√k`: the realizing unit-speed segment cannot be longer
  have hrd : ∀ p q : M, riemannianDistance (I := I) g p q ≤ π / Real.sqrt k := by
    intro p q
    by_contra h
    rw [not_le] at h
    have hpq : p ≠ q := fun hpq => by
      rw [hpq, riemannianDistance_self (I := I) g q] at h
      exact absurd h (not_lt.mpr (div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)).le)
    obtain ⟨σ, hseg, hσ0, hσd⟩ :=
      completeManifold_exists_isSegment_unitSpeed (I := I) g hg p q
    have hunit : ∀ t ∈ Set.Icc (0:ℝ) (riemannianDistance (I := I) g p q),
        curveLength (I := I) g σ 0 t = t :=
      hseg.curveLength_eq_self_of_domain (I := I) g hσ0 hσd hpq
    have hlt := hBS σ (riemannianDistance (I := I) g p q) h hseg hunit
    rw [hσ0, hσd] at hlt
    exact lt_irrefl _ hlt
  have hdist : ∀ p q : M, dist p q ≤ π / Real.sqrt k := fun p q =>
    (dist_le_riemannianDistance (I := I) g hg p q).trans (hrd p q)
  refine ⟨Metric.diam_le_of_forall_dist_le hC (fun p _ q _ => hdist p q), ?_⟩
  -- bounded + proper ⟹ compact
  rw [Metric.compactSpace_iff_isBounded_univ]
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  refine (Metric.isBounded_iff_subset_closedBall x₀).mpr ⟨π / Real.sqrt k, fun y _ => ?_⟩
  rw [Metric.mem_closedBall, dist_comm]
  exact hdist x₀ y

/-- **Math.** Global-geodesic form of `diameterBound_of_notMinimizing`.  This
version exposes the continuity and geodesic properties of the particular
unit-speed minimizing segment constructed by Hopf--Rinow.  It is the useful
interface when the not-minimizing argument constructs fields or variations on
all of `ℝ`, rather than only on the segment interval. -/
theorem diameterBound_of_notMinimizing_global (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] {k : ℝ} (hk : 0 < k)
    (hBS : ∀ (σ : ℝ → M) (l : ℝ), π / Real.sqrt k < l →
      Continuous σ → Geodesic.IsGeodesic (I := I) g σ →
      IsSegment (I := I) g σ 0 l →
      (∀ t ∈ Set.Icc (0 : ℝ) l, curveLength (I := I) g σ 0 t = t) →
      riemannianDistance (I := I) g (σ 0) (σ l) < l) :
    Metric.diam (Set.univ : Set M) ≤ π / Real.sqrt k ∧ CompactSpace M := by
  have hC : (0 : ℝ) ≤ π / Real.sqrt k :=
    (div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)).le
  haveI hProper : ProperSpace M :=
    ((hopfRinowTheorem (I := I) g hg).out 3 2).mp ‹CompleteSpace M›
  have hrd : ∀ p q : M, riemannianDistance (I := I) g p q ≤ π / Real.sqrt k := by
    intro p q
    by_contra h
    rw [not_le] at h
    have hpq : p ≠ q := fun hpq => by
      rw [hpq, riemannianDistance_self (I := I) g q] at h
      exact absurd h (not_lt.mpr (div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)).le)
    obtain ⟨σ, hseg, hσ0, hσd, hσc, hσgeo⟩ :=
      completeManifold_exists_isSegment_unitSpeed_global (I := I) g hg p q
    have hunit : ∀ t ∈ Set.Icc (0 : ℝ) (riemannianDistance (I := I) g p q),
        curveLength (I := I) g σ 0 t = t :=
      hseg.curveLength_eq_self_of_domain (I := I) g hσ0 hσd hpq
    have hlt := hBS σ (riemannianDistance (I := I) g p q) h hσc hσgeo hseg hunit
    rw [hσ0, hσd] at hlt
    exact lt_irrefl _ hlt
  have hdist : ∀ p q : M, dist p q ≤ π / Real.sqrt k := fun p q =>
    (dist_le_riemannianDistance (I := I) g hg p q).trans (hrd p q)
  refine ⟨Metric.diam_le_of_forall_dist_le hC (fun p _ q _ => hdist p q), ?_⟩
  rw [Metric.compactSpace_iff_isBounded_univ]
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  refine (Metric.isBounded_iff_subset_closedBall x₀).mpr
    ⟨π / Real.sqrt k, fun y _ => ?_⟩
  rw [Metric.mem_closedBall, dist_comm]
  exact hdist x₀ y

/-- **Math.** A continuous global geodesic whose length on every initial
subsegment `[0,t] ⊆ [0,l]` equals `t`, for some `l > 0`, has unit velocity at
every time.  Geodesic speed is globally constant; evaluating the length at
`l` forces that constant to be one. -/
theorem globalSegment_curveVelocity_unit
    (g : RiemannianMetric I M) {σ : ℝ → M} {l : ℝ}
    (hl : 0 < l)
    (hσc : Continuous σ)
    (hσgeo : Geodesic.IsGeodesic (I := I) g σ)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) l,
      curveLength (I := I) g σ 0 t = t) :
    ∀ t, g.metricInner (σ t) (curveVelocity (I := I) σ t)
      (curveVelocity (I := I) σ t) = 1 := by
  have hconst : ∀ t, curveSpeedSq (I := I) g σ t = curveSpeedSq (I := I) g σ 0 := by
    intro t
    exact curveSpeedSq_eqOn_const (I := I) g isOpen_univ Set.ordConnected_univ
      hσc.continuousOn (hσgeo.isGeodesicOn univ) (mem_univ t) (mem_univ 0)
  have hlen : curveLength (I := I) g σ 0 l = l :=
    hunit l ⟨le_of_lt hl, le_rfl⟩
  rw [curveLength_def] at hlen
  have hfun : (fun t : ℝ => Real.sqrt (curveSpeedSq (I := I) g σ t)) =
      (fun _ : ℝ => Real.sqrt (curveSpeedSq (I := I) g σ 0)) := by
    funext t
    rw [hconst t]
  rw [hfun, intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hlen
  have hsqrt : Real.sqrt (curveSpeedSq (I := I) g σ 0) = 1 := by
    nlinarith
  have hsq : curveSpeedSq (I := I) g σ 0 = 1 := by
    have hnonneg := curveSpeedSq_nonneg (I := I) g σ 0
    nlinarith [Real.sq_sqrt hnonneg]
  have hsq' : ∀ t, curveSpeedSq (I := I) g σ t = 1 := by
    intro t
    rw [hconst t, hsq]
  intro t
  simpa only [curveSpeedSq_def, curveVelocity_def, RiemannianMetric.metricInner_apply]
    using hsq' t

/-- **Math.** Petersen's Myers diameter and compactness assembly with the
remaining minimizing-index input isolated in scalar form.  For every
hypothetical unit-speed minimizing geodesic of length `l > pi/sqrt(k)`, assume
there are `m > 0` curvature weights `kappa_i` whose sum is at least `m*k` and
whose standard sine-field index expressions are nonnegative.  The scalar Myers
inequality `myers_index_core` makes the sum of those same expressions strictly
negative, a contradiction.

Compared with `myersRicciDiameterBound_of_globalVariation`, this interface asks
for no exponential variation, joint slab smoothness, or second derivative of
energy.  A native minimizing-index theorem and a parallel Ricci frame are
exactly what remain to discharge `hindex`. -/
theorem myersRicciDiameterBound_of_indexNonneg
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {k : ℝ} (hk : 0 < k)
    (hindex : ∀ (σ : ℝ → M) (l : ℝ), 0 < l → π / Real.sqrt k < l →
      Continuous σ → Geodesic.IsGeodesic (I := I) g σ →
      IsSegment (I := I) g σ 0 l →
      (∀ t ∈ Set.Icc (0 : ℝ) l, curveLength (I := I) g σ 0 t = t) →
      ∃ (m : ℕ) (κ : Fin m → ℝ → ℝ),
        0 < m ∧
        (∀ i, IntervalIntegrable
          (fun t => Real.sin (π / l * t) ^ 2 * κ i t) volume 0 l) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) l, (m : ℝ) * k ≤ ∑ i, κ i t) ∧
        (∀ i, 0 ≤ (π / l) ^ 2 * (l / 2)
          - ∫ t in (0 : ℝ)..l, Real.sin (π / l * t) ^ 2 * κ i t)) :
    Metric.diam (Set.univ : Set M) ≤ π / Real.sqrt k ∧ CompactSpace M := by
  refine diameterBound_of_notMinimizing_global (I := I) g hg hk
    (fun σ l hlk hσc hσgeo hseg hunit => ?_)
  have hl : 0 < l := lt_trans (div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)) hlk
  obtain ⟨m, κ, hm, hint, hsum, hnonneg⟩ :=
    hindex σ l hl hlk hσc hσgeo hseg hunit
  have hs : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hneg := myers_index_core hl hk hlk (Finset.univ : Finset (Fin m)) hs
    (fun i _ => hint i) (fun t ht => by simpa using hsum t ht)
  have hnn : 0 ≤ ∑ i : Fin m,
      ((π / l) ^ 2 * (l / 2)
        - ∫ t in (0 : ℝ)..l, Real.sin (π / l * t) ^ 2 * κ i t) :=
    Finset.sum_nonneg fun i _ => hnonneg i
  exfalso
  linarith

set_option maxHeartbeats 2000000 in
/-- **Math.** Petersen's Myers diameter and compactness theorem with the
velocity-seeded parallel frame, unit-speed identity, and Ricci trace assembled
internally.  For each hypothetical long minimizing geodesic, the caller need
only prove that every standard sine field in the perpendicular frame has an
integrable curvature coefficient and nonnegative index expression.

Global `C²` geodesic regularity is supplied internally by
`IsGeodesic.contMDiffAt_two`. No two-parameter variation occurs in this
interface. -/
theorem myersRicciDiameterBound_of_velocityFrameIndexNonneg
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {k : ℝ} (hk : 0 < k)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hRic : HasRicciBoundedBelow g.leviCivita k)
    (hindex : ∀ (σ : ℝ → M) (l : ℝ), 0 < l → π / Real.sqrt k < l →
      Continuous σ → Geodesic.IsGeodesic (I := I) g σ →
      IsSegment (I := I) g σ 0 l →
      (∀ t ∈ Set.Icc (0 : ℝ) l, curveLength (I := I) g σ 0 t = t) →
      ∀ (e : Fin (Module.finrank ℝ E) → (∀ t, TangentSpace I (σ t)))
        (n₀ : Fin (Module.finrank ℝ E)),
        (∀ i, IsParallelSolOn (I := I) g σ (Ioo (-1) (l + 1)) (e i)) →
        (∀ t ∈ Ioo (-1) (l + 1), ∀ i j,
          g.metricInner (σ t) (e i t) (e j t) = if i = j then (1 : ℝ) else 0) →
        (∀ t ∈ Ioo (-1) (l + 1), e n₀ t = curveVelocity (I := I) σ t) →
        ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))).erase n₀,
          IntervalIntegrable
            (fun t => Real.sin (π / l * t) ^ 2 *
              sectionalCurvature (g.leviCivita) (σ t) (e i t)
                (curveVelocity (I := I) σ t)) volume 0 l ∧
          0 ≤ (π / l) ^ 2 * (l / 2) -
            ∫ t in (0 : ℝ)..l, Real.sin (π / l * t) ^ 2 *
              sectionalCurvature (g.leviCivita) (σ t) (e i t)
                (curveVelocity (I := I) σ t)) :
    Metric.diam (Set.univ : Set M) ≤ π / Real.sqrt k ∧ CompactSpace M := by
  refine diameterBound_of_notMinimizing_global (I := I) g hg hk
    (fun σ l hlk hσc hσgeo hseg hunit => ?_)
  have hl : 0 < l := lt_trans (div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)) hlk
  have hspeed := globalSegment_curveVelocity_unit (I := I) g hl hσc hσgeo hunit
  have ht₀ : (0 : ℝ) ∈ Ioo (-1) (l + 1) := by constructor <;> linarith
  have hcM : ∀ t ∈ Icc (-1) (l + 1), ContMDiffAt 𝓘(ℝ, ℝ) I 2 σ t :=
    fun t _ => IsGeodesic.contMDiffAt_two (I := I) g hσgeo hσc t
  obtain ⟨e, n₀, hepar, heorth, hevel⟩ :=
    exists_velocitySeededParallelOrthonormalFrameOn_Ioo (I := I) g ht₀ hcM
      hσc hσgeo (hspeed 0)
  let s : Finset (Fin (Module.finrank ℝ E)) := Finset.univ.erase n₀
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs0
    have hcard0 : s.card = 0 := by rw [hs0, Finset.card_empty]
    have hcard : s.card = Module.finrank ℝ E - 1 := by simp [s]
    omega
  have hidx := hindex σ l hl hlk hσc hσgeo hseg hunit e n₀ hepar heorth hevel
  have hneg := myers_index_core hl hk hlk s hs
    (fun i hi => (hidx i hi).1) (fun t ht => ?_)
  have hnonneg : 0 ≤ ∑ i ∈ s,
      ((π / l) ^ 2 * (l / 2) -
        ∫ u in (0 : ℝ)..l, Real.sin (π / l * u) ^ 2 *
          sectionalCurvature (g.leviCivita) (σ u) (e i u)
            (curveVelocity (I := I) σ u)) :=
    Finset.sum_nonneg fun i hi => (hidx i hi).2
  · exfalso
    linarith
  · have htIoo : t ∈ Ioo (-1) (l + 1) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨b, hbcoe⟩ := exists_orthonormalBasis_of_family (g := g) (p := σ t)
      (heorth t htIoo)
    have hb : ∀ i, b i = e i t := fun i => congrFun hbcoe i
    have hborth : ∀ i j, g.metricInner (σ t) (b i) (b j) =
        if i = j then (1 : ℝ) else 0 := by
      intro i j
      rw [hb i, hb j]
      exact heorth t htIoo i j
    have htrace := ricciCurvature_eq_sum_sectionalCurvature g.leviCivita (σ t)
      b hborth n₀
    have hcard : s.card = Module.finrank ℝ E - 1 := by simp [s]
    calc
      (s.card : ℝ) * k = ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * k *
          g.metricInner (σ t) (curveVelocity (I := I) σ t)
            (curveVelocity (I := I) σ t) := by rw [hspeed t, mul_one, hcard]
      _ ≤ RicciCurvature g.leviCivita.toAffineConnection (σ t)
          (curveVelocity (I := I) σ t) (curveVelocity (I := I) σ t) := hRic _ _
      _ = ∑ i ∈ s, sectionalCurvature g.leviCivita (σ t)
          (curveVelocity (I := I) σ t) (e i t) := by
            rw [← hevel t htIoo, ← hb n₀, htrace]
            exact Finset.sum_congr rfl fun i _ => by rw [hb i]
      _ = ∑ i ∈ s, sectionalCurvature g.leviCivita (σ t) (e i t)
          (curveVelocity (I := I) σ t) := by
            exact Finset.sum_congr rfl fun i _ =>
              sectionalCurvature_comm g.leviCivita (σ t)
                (curveVelocity (I := I) σ t) (e i t)

/-! ### Discharging the not-minimizing input from a curvature bound -/

/-- **Math.** Petersen §6.3, the **Bonnet–Synge variation data** for a unit-speed geodesic
segment `σ = f 0` on `[0,l]`: a proper variation `f` with fixed endpoints whose variation field
is `sin(π·/l)·E` for a unit parallel field `E ⟂ σ̇`, together with the smoothness and
integrability side conditions.  This is precisely the hypothesis bundle of Lemma 6.3.1
(`bonnetSynge_longGeodesicsNotMinimizing`), packaged so the diameter theorem can *assume the
technical existence of the variation* (the exponential-variation slab-smoothness of
`Ch06/ExpVariation.lean`) while genuinely **deriving** the not-minimizing conclusion from the
curvature bound.  Same honest scope as 6.3.1. -/
structure IsBonnetSyngeVariation (g : RiemannianMetric I M) (σ : ℝ → M) (l : ℝ)
    (f : ℝ → ℝ → M) (Efield : ∀ t, TangentSpace I (f 0 t)) (δ a b : ℝ) : Prop where
  base : f 0 = σ
  hδ : 0 < δ
  hsub : Set.Icc (0 : ℝ) l ⊆ Set.Ioo a b
  hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b)
  hgeo : ∀ t ∈ Set.Icc (0 : ℝ) l, curveAcceleration (I := I) g (f 0) t = 0
  hfix₀ : ∀ s, f s 0 = f 0 0
  hfixl : ∀ s, f s l = f 0 l
  hEpar : IsParallelAlong (I := I) g (f 0) Efield
  hEdiff : ∀ t, DifferentiableAt ℝ (chartFieldRep (I := I) (f 0) (f 0 t) Efield) t
  hEunit : ∀ t, g.metricInner (f 0 t) (Efield t) (Efield t) = 1
  hEperp : ∀ t, g.metricInner (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t) = 0
  hspeed : ∀ t, g.metricInner (f 0 t) (curveVelocity (I := I) (f 0) t)
    (curveVelocity (I := I) (f 0) t) = 1
  hVfield : variationField (I := I) f = fun t => Real.sin (π / l * t) • Efield t
  hint : IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 *
    sectionalCurvature (g.leviCivita) (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t))
    volume 0 l

/-- **Math.** Petersen §6.3, the **unit-speed not-minimizing bridge** in packaged form: a proper
variation `F` of a unit-speed base curve `F 0` (fixed endpoints, jointly smooth on the slab,
`|Ḟ₀| ≡ 1`) whose second variation of energy is strictly negative does not realize the distance
between its endpoints, `d(F 0 0, F 0 l) < l`.  This isolates the routine discharge shared by the
Bonnet–Synge (sectional) and Myers (Ricci) wirings: unit speed gives `E(F 0) = l/2` and
`L(F 0) = l`; `hasDerivAt_pieceEnergy_shift` gives first-variation differentiability; the slab
smoothness gives each slice piecewise-smooth; then `riemannianDistance_lt_of_secondVariation_neg`
concludes. -/
theorem riemannianDistance_lt_of_negSecondVar_unitSpeed_on_segment (g : RiemannianMetric I M)
    {F : ℝ → ℝ → M} {l δ a b : ℝ} (hl : 0 < l) (hδ : 0 < δ)
    (hsub : Set.Icc (0 : ℝ) l ⊆ Set.Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry F) (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b))
    (hfix₀ : ∀ s, F s 0 = F 0 0) (hfixl : ∀ s, F s l = F 0 l)
    (hspeed : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (F 0 t) (curveVelocity (I := I) (F 0) t)
        (curveVelocity (I := I) (F 0) t) = 1)
    (h2neg : deriv (deriv (fun s => energyFunctional (I := I) g (F s) 0 l)) 0 < 0) :
    riemannianDistance (I := I) g (F 0 0) (F 0 l) < l := by
  -- unit speed: `|Ḟ₀|² ≡ 1`
  have hcs1 : ∀ t ∈ Set.Icc (0 : ℝ) l, curveSpeedSq (I := I) g (F 0) t = 1 := by
    intro t ht
    have h := hspeed t ht
    rw [RiemannianMetric.metricInner_apply] at h
    simpa only [curveSpeedSq_def, curveVelocity_def] using h
  -- unit-speed base facts: `E(F 0) = l/2` and `L(F 0) = l`
  have hE0 : energyFunctional (I := I) g (F 0) 0 l = l / 2 := by
    rw [energyFunctional_def, intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))
      (fun t ht => hcs1 t (by simpa only [Set.uIcc_of_le hl.le] using ht)),
      intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one]
    ring
  have hlen0 : curveLength (I := I) g (F 0) 0 l = l := by
    rw [curveLength_def, intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))
        (fun t ht => by
          rw [hcs1 t (by simpa only [Set.uIcc_of_le hl.le] using ht)]
          exact Real.sqrt_one),
      intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one]
  -- first-variation differentiability, from the slab smoothness
  have hφ1 : DifferentiableAt ℝ (fun s => energyFunctional (I := I) g (F s) 0 l) 0 :=
    (hasDerivAt_pieceEnergy_shift (I := I) g (s₀ := 0) (by simpa using hδ) hl
      (hf.mono (Set.prod_mono subset_rfl hsub))).differentiableAt
  -- each variation slice is a piecewise-smooth curve on `[0,l]`
  have hslice : ∀ s ∈ Set.Ioo (-δ) δ, IsPiecewiseSmoothCurve (I := I) (F s) 0 l := by
    intro s hs
    have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (F s) (Set.Icc 0 l) :=
      hf.comp ((contDiff_prodMk_right s).contMDiff.contMDiffOn (s := Set.Icc 0 l))
        (fun t ht => ⟨hs, hsub ht⟩)
    exact ContMDiffOn.isPiecewiseSmoothCurve (I := I) hl.le hsm
  exact riemannianDistance_lt_of_secondVariation_neg (I := I) g hδ hl hslice hfix₀ hfixl
    hlen0 hE0 hφ1 h2neg

/-- **Math.** Compatibility wrapper for the original global unit-speed interface. -/
theorem riemannianDistance_lt_of_negSecondVar_unitSpeed (g : RiemannianMetric I M)
    {F : ℝ → ℝ → M} {l δ a b : ℝ} (hl : 0 < l) (hδ : 0 < δ)
    (hsub : Set.Icc (0 : ℝ) l ⊆ Set.Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry F) (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b))
    (hfix₀ : ∀ s, F s 0 = F 0 0) (hfixl : ∀ s, F s l = F 0 l)
    (hspeed : ∀ t, g.metricInner (F 0 t) (curveVelocity (I := I) (F 0) t)
      (curveVelocity (I := I) (F 0) t) = 1)
    (h2neg : deriv (deriv (fun s => energyFunctional (I := I) g (F s) 0 l)) 0 < 0) :
    riemannianDistance (I := I) g (F 0 0) (F 0 l) < l :=
  riemannianDistance_lt_of_negSecondVar_unitSpeed_on_segment (I := I) g hl hδ hsub hf
    hfix₀ hfixl (fun t _ => hspeed t) h2neg

/-- **Math.** The standard sine-field index expression is nonnegative along a
distance-realizing unit-speed segment, once a smooth proper variation realizing
that field is supplied.  Indeed, `bonnetSynge_secondVariation_eq` identifies the
expression with the second variation of energy.  If it were negative,
`riemannianDistance_lt_of_negSecondVar_unitSpeed` would make the endpoints
strictly closer than `l`, contradicting the segment equality and the assumed
unit-speed length normalization.

This is the minimizing-index half of the Bonnet--Myers argument.  Its only
remaining analytic input is the construction of `hbv`, namely joint slab
smoothness of the intrinsic exponential variation. -/
theorem bonnetSynge_index_nonneg_of_segment (g : RiemannianMetric I M)
    {σ : ℝ → M} {l : ℝ} (hl : 0 < l)
    (hseg : IsSegment (I := I) g σ 0 l)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) l, curveLength (I := I) g σ 0 t = t)
    {f : ℝ → ℝ → M} {Efield : ∀ t, TangentSpace I (f 0 t)} {δ a b : ℝ}
    (hbv : IsBonnetSyngeVariation (I := I) g σ l f Efield δ a b) :
    0 ≤ (π / l) ^ 2 * (l / 2)
      - ∫ t in (0 : ℝ)..l, Real.sin (π / l * t) ^ 2 *
          sectionalCurvature (g.leviCivita) (f 0 t) (Efield t)
            (curveVelocity (I := I) (f 0) t) := by
  have hsecond := bonnetSynge_secondVariation_eq (I := I) g hl hbv.hδ hbv.hsub hbv.hf
    hbv.hgeo hbv.hfix₀ hbv.hfixl hbv.hEpar hbv.hEdiff hbv.hEunit hbv.hEperp
    hbv.hspeed hbv.hVfield hbv.hint
  rw [← hsecond]
  by_contra hneg
  rw [not_le] at hneg
  have hlt := riemannianDistance_lt_of_negSecondVar_unitSpeed (I := I) g hl hbv.hδ hbv.hsub
    hbv.hf hbv.hfix₀ hbv.hfixl hbv.hspeed hneg
  rw [hbv.base] at hlt
  have hdist : riemannianDistance (I := I) g (σ 0) (σ l) = l := by
    rw [← hseg.2.1, hunit l (right_mem_Icc.mpr hl.le)]
  rw [hdist] at hlt
  exact (lt_irrefl l) hlt

/-- **Math.** Segment-local minimizing-index theorem.  Unlike
`bonnetSynge_index_nonneg_of_segment`, all field identities are required only
on `[0,l]`, which is enough both for the second-variation integral and for the
unit-speed minimizing contradiction. -/
theorem bonnetSynge_index_nonneg_of_segment_local (g : RiemannianMetric I M)
    {σ : ℝ → M} {l : ℝ} (hl : 0 < l)
    (hseg : IsSegment (I := I) g σ 0 l)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) l, curveLength (I := I) g σ 0 t = t)
    {f : ℝ → ℝ → M} {Efield : ∀ t, TangentSpace I (f 0 t)} {δ a b : ℝ}
    (hbase : f 0 = σ) (hδ : 0 < δ)
    (hsub : Set.Icc (0 : ℝ) l ⊆ Set.Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f)
      (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b))
    (hgeo : ∀ t ∈ Set.Icc (0 : ℝ) l, curveAcceleration (I := I) g (f 0) t = 0)
    (hfix₀ : ∀ s, f s 0 = f 0 0) (hfixl : ∀ s, f s l = f 0 l)
    (hEpar : ∀ t ∈ Set.Icc (0 : ℝ) l,
      derivAlongCurve (I := I) g (f 0) Efield t = 0)
    (hEdiff : ∀ t ∈ Set.Icc (0 : ℝ) l,
      DifferentiableAt ℝ (chartFieldRep (I := I) (f 0) (f 0 t) Efield) t)
    (hEunit : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (Efield t) (Efield t) = 1)
    (hEperp : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (Efield t) (curveVelocity (I := I) (f 0) t) = 0)
    (hspeed : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (curveVelocity (I := I) (f 0) t)
        (curveVelocity (I := I) (f 0) t) = 1)
    (hVfield : variationField (I := I) f = fun t => Real.sin (π / l * t) • Efield t)
    (hint : IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 *
      sectionalCurvature (g.leviCivita) (f 0 t) (Efield t)
        (curveVelocity (I := I) (f 0) t)) volume 0 l) :
    0 ≤ (π / l) ^ 2 * (l / 2)
      - ∫ t in (0 : ℝ)..l, Real.sin (π / l * t) ^ 2 *
          sectionalCurvature (g.leviCivita) (f 0 t) (Efield t)
            (curveVelocity (I := I) (f 0) t) := by
  have hsecond := bonnetSynge_secondVariation_eq_on_segment (I := I) g hl hδ hsub hf
    hgeo hfix₀ hfixl hEpar hEdiff hEunit hEperp hspeed hVfield hint
  rw [← hsecond]
  by_contra hneg
  rw [not_le] at hneg
  have hlt := riemannianDistance_lt_of_negSecondVar_unitSpeed_on_segment (I := I) g hl hδ
    hsub hf hfix₀ hfixl hspeed hneg
  rw [hbase] at hlt
  have hdist : riemannianDistance (I := I) g (σ 0) (σ l) = l := by
    rw [← hseg.2.1, hunit l (right_mem_Icc.mpr hl.le)]
  rw [hdist] at hlt
  exact (lt_irrefl l) hlt

/-- **Math.** Smooth scalar multiplication preserves smoothness of a field along a
curve.  In a tangent-bundle trivialization the fiber coordinate is the scalar
times the original fiber coordinate. -/
theorem IsVectorFieldAlong.smul {c : ℝ → M} {V : ∀ t, TangentSpace I (c t)}
    {w : ℝ → ℝ} {J : Set ℝ}
    (hV : IsVectorFieldAlong (I := I) c V J)
    (hw : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ w J) :
    IsVectorFieldAlong (I := I) c (fun t => w t • V t) J := by
  intro t ht
  let e := trivializationAt E (TangentSpace I) (c t)
  have heV : (⟨c t, V t⟩ : TangentBundle I M) ∈ e.source := by
    rw [Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (c t)
  have heW : (⟨c t, w t • V t⟩ : TangentBundle I M) ∈ e.source := heV
  have hiffV := e.contMDiffWithinAt_iff (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := ∞)
    (f := fun s : ℝ => (⟨c s, V s⟩ : TangentBundle I M)) (s := J) (x₀ := t) heV
  have hiffW := e.contMDiffWithinAt_iff (IM := 𝓘(ℝ, ℝ)) (IB := I) (n := ∞)
    (f := fun s : ℝ => (⟨c s, w s • V s⟩ : TangentBundle I M)) (s := J) (x₀ := t) heW
  have hparts := hiffV.mp (hV t ht)
  refine hiffW.mpr ⟨hparts.1, ?_⟩
  have hbase : c ⁻¹' e.baseSet ∈ 𝓝[J] t :=
    hparts.1.continuousWithinAt.preimage_mem_nhdsWithin
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (c t)))
  refine ((hw t ht).smul hparts.2).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hbase] with s hs
    change (e (⟨c s, w s • V s⟩ : TangentBundle I M)).2 =
      w s • (e (⟨c s, V s⟩ : TangentBundle I M)).2
    exact (e.linear ℝ hs).map_smul (w s) (V s)
  · change (e (⟨c t, w t • V t⟩ : TangentBundle I M)).2 =
      w t • (e (⟨c t, V t⟩ : TangentBundle I M)).2
    exact (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' (c t))).map_smul
      (w t) (V t)

/-- **Math.** Along a smooth geodesic, the sectional curvature of the plane
spanned by the velocity and a parallel orthonormal field is continuous on a
compact interval.  Around each time, read the curve, velocity, and field in
one fixed chart.  The geodesic equation makes the chart velocity continuous,
the parallel ODE makes the field reading continuous, and the chart curvature
operator and metric pairing are continuous in those data. -/
theorem continuousOn_sectionalCurvature_of_parallel
    (g : RiemannianMetric I M) {σ : ℝ → M} {Efield : ∀ t, TangentSpace I (σ t)}
    {a b A B : ℝ}
    (hσc : Continuous σ) (hσgeo : Geodesic.IsGeodesic (I := I) g σ)
    (hsubJ : Icc a b ⊆ Ioo A B)
    (hEpar : IsParallelSolOn (I := I) g σ (Ioo A B) Efield)
    (hEunit : ∀ t ∈ Icc a b, g.metricInner (σ t) (Efield t) (Efield t) = 1)
    (hEperp : ∀ t ∈ Icc a b,
      g.metricInner (σ t) (Efield t) (curveVelocity (I := I) σ t) = 0)
    (hspeed : ∀ t ∈ Icc a b,
      g.metricInner (σ t) (curveVelocity (I := I) σ t)
        (curveVelocity (I := I) σ t) = 1) :
    ContinuousOn (fun t => sectionalCurvature (g.leviCivita) (σ t) (Efield t)
      (curveVelocity (I := I) σ t)) (Icc a b) := by
  intro t ht
  have hnhds : σ ⁻¹' (chartAt H (σ t)).source ∈ 𝓝 t :=
    hσc.continuousAt.preimage_mem_nhds
      ((chartAt H (σ t)).open_source.mem_nhds (mem_chart_source H (σ t)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  set c := max a (t - ε / 2) with hc
  set d := min b (t + ε / 2) with hd
  have hsub : Icc c d ⊆ Icc a b :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsrc : ∀ τ ∈ Icc c d, σ τ ∈ (chartAt H (σ t)).source := by
    intro τ hτ
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : t - ε / 2 ≤ τ := le_trans (le_max_right _ _) hτ.1
    have h2 : τ ≤ t + ε / 2 := le_trans hτ.2 (min_le_right _ _)
    have habs : |τ - t| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have htcd : t ∈ Icc c d :=
    ⟨max_le ht.1 (by linarith), le_min ht.2 (by linarith)⟩
  have hnb : Icc c d ∈ 𝓝[Icc a b] t := by
    have hmem : Icc (t - ε / 2) (t + ε / 2) ∈ 𝓝 t :=
      Icc_mem_nhds (by linarith) (by linarith)
    have hinter := inter_mem_nhdsWithin (Icc a b) hmem
    rwa [Icc_inter_Icc] at hinter
  let α : M := σ t
  let u : ℝ → E := fun τ => extChartAt I α (σ τ)
  let W : ℝ → E := chartFieldRep (I := I) σ α Efield
  have hu_cont : ContinuousOn u (Icc c d) := by
    intro τ hτ
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc τ hτ)).comp
        hσc.continuousAt).continuousWithinAt
  have hu'_cont : ContinuousOn (deriv u) (Icc c d) := by
    intro τ hτ
    exact ((hσgeo τ).continuousAt_deriv_extChartAt hσc.continuousAt
      (hsrc τ hτ)).continuousWithinAt
  have hmem : ∀ τ ∈ Icc c d, u τ ∈ interior (extChartAt I α).target := by
    intro τ hτ
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc τ hτ))
  have hW_cont : ContinuousOn W (Icc c d) := by
    intro τ hτ
    have hστ := IsGeodesic.contMDiffAt_infty (I := I) g hσgeo hσc τ
    have hown : DifferentiableAt ℝ (fun r => extChartAt I (σ τ) (σ r)) τ :=
      (contDiffAt_extChartAt_comp (I := I) le_rfl (σ τ) hστ
        (mem_chart_source H (σ τ))).differentiableAt (by simp)
    exact (differentiableAt_chartFieldRep_transfer (I := I) (σ τ) α
      hσc.continuousAt (mem_chart_source H (σ τ)) (hsrc τ hτ) hown
      (hEpar τ (hsubJ (hsub hτ))).1).continuousAt.continuousWithinAt
  have hendo : ContinuousOn
      (fun τ => chartCurvatureEndo (I := I) g α (u τ) (deriv u τ))
      (Icc c d) :=
    continuousOn_chartCurvatureEndo_comp (I := I) g α hu_cont hu'_cont hmem
  have hmain : ContinuousOn (fun τ => chartMetricInner (I := I) g α (u τ)
      (chartCurvatureEndo (I := I) g α (u τ) (deriv u τ) (W τ)) (W τ))
      (Icc c d) :=
    continuousOn_chartMetricInner_comp (I := I) g α hu_cont
      (hendo.clm_apply hW_cont) hW_cont
      (fun τ hτ => (extChartAt I α).map_source
        (by rw [extChartAt_source]; exact hsrc τ hτ))
  have hlocal : ContinuousOn (fun τ => sectionalCurvature (g.leviCivita)
      (σ τ) (Efield τ) (curveVelocity (I := I) σ τ)) (Icc c d) := by
    refine hmain.congr fun τ hτ => ?_
    have hsrcE : σ τ ∈ (extChartAt I α).source := by
      rw [extChartAt_source]
      exact hsrc τ hτ
    have hστ := IsGeodesic.contMDiffAt_infty (I := I) g hσgeo hσc τ
    have hu_diff : DifferentiableAt ℝ (fun r => extChartAt I α (σ r)) τ :=
      (contDiffAt_extChartAt_comp (I := I) le_rfl α hστ
        (hsrc τ hτ)).differentiableAt (by simp)
    have hcurv := curvatureTensorAt_eq_chartCurvature_along (I := I)
      (V := Efield) g α hσc.continuousAt (hsrc τ hτ) hu_diff
    have hbiv : bivectorInnerProduct g (σ τ) (Efield τ)
        (curveVelocity (I := I) σ τ) (Efield τ)
        (curveVelocity (I := I) σ τ) = 1 := by
      rw [bivectorInnerProduct, hEunit τ (hsub hτ), hspeed τ (hsub hτ),
        hEperp τ (hsub hτ)]
      ring
    symm
    rw [chartMetricInner_eq_inner (I := I) g hsrcE,
      chartCurvatureEndo_apply, hcurv,
      tangentCoordChange_chartFieldRep (I := I) σ α Efield hsrcE]
    change curvatureTensorFourAt (g.leviCivita) (σ τ) (Efield τ)
        (curveVelocity (I := I) σ τ) (curveVelocity (I := I) σ τ) (Efield τ) = _
    rw [(isAlgCurvatureForm_curvatureTensorFourAt (g.leviCivita) (σ τ)).pairSwap,
      sectionalCurvature_eq_curvatureTensorFourAt, hbiv, div_one]
  exact (hlocal t htcd).mono_of_mem_nhdsWithin hnb

/-- **Math.** The standard sine-weighted sectional-curvature coefficient in
the Bonnet--Myers index form is interval-integrable.  This is immediate from
`continuousOn_sectionalCurvature_of_parallel` and continuity of the sine
factor on the compact time interval. -/
theorem intervalIntegrable_sine_sq_sectionalCurvature_of_parallel
    (g : RiemannianMetric I M) {σ : ℝ → M} {Efield : ∀ t, TangentSpace I (σ t)}
    {l : ℝ} (hl : 0 < l)
    (hσc : Continuous σ) (hσgeo : Geodesic.IsGeodesic (I := I) g σ)
    (hEpar : IsParallelSolOn (I := I) g σ (Ioo (-1) (l + 1)) Efield)
    (hEunit : ∀ t ∈ Ioo (-1) (l + 1),
      g.metricInner (σ t) (Efield t) (Efield t) = 1)
    (hEperp : ∀ t ∈ Ioo (-1) (l + 1),
      g.metricInner (σ t) (Efield t) (curveVelocity (I := I) σ t) = 0)
    (hspeed : ∀ t, g.metricInner (σ t) (curveVelocity (I := I) σ t)
      (curveVelocity (I := I) σ t) = 1) :
    IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 *
      sectionalCurvature (g.leviCivita) (σ t) (Efield t)
        (curveVelocity (I := I) σ t)) volume 0 l := by
  have hsub : Icc (0 : ℝ) l ⊆ Ioo (-1) (l + 1) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsec := continuousOn_sectionalCurvature_of_parallel (I := I) g hσc hσgeo
    hsub hEpar (fun t ht => hEunit t (hsub ht)) (fun t ht => hEperp t (hsub ht))
    (fun t _ => hspeed t)
  have hsin : ContinuousOn (fun t : ℝ => Real.sin (π / l * t) ^ 2) (Icc 0 l) :=
    (by fun_prop : Continuous fun t : ℝ => Real.sin (π / l * t) ^ 2).continuousOn
  exact (hsin.mul hsec).intervalIntegrable_of_Icc (μ := volume) hl.le

/-- **Math.** A parallel unit field perpendicular to a minimizing global
geodesic has nonnegative standard sine-field index.  The proper variation is
constructed internally as the intrinsic exponential of
`sin(πt/l) E(t)`: smoothness of the interval-parallel field gives a uniform
open slab, and the sine factor fixes both endpoints.

The curvature-weight integrability hypothesis is kept explicit; it is
independent of the former variation-existence callback and is the only
remaining analytic input in this interface. -/
theorem intrinsicSine_index_nonneg_of_segment
    (g : RiemannianMetric I M) {σ : ℝ → M} {l : ℝ} (hl : 0 < l)
    (hσc : Continuous σ) (hσgeo : Geodesic.IsGeodesic (I := I) g σ)
    (hseg : IsSegment (I := I) g σ 0 l)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) l, curveLength (I := I) g σ 0 t = t)
    {Efield : ∀ t, TangentSpace I (σ t)}
    (hEpar : IsParallelSolOn (I := I) g σ (Set.Ioo (-1) (l + 1)) Efield)
    (hEunit : ∀ t ∈ Set.Ioo (-1) (l + 1),
      g.metricInner (σ t) (Efield t) (Efield t) = 1)
    (hEperp : ∀ t ∈ Set.Ioo (-1) (l + 1),
      g.metricInner (σ t) (Efield t) (curveVelocity (I := I) σ t) = 0)
    (hint : IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 *
      sectionalCurvature (g.leviCivita) (σ t) (Efield t)
        (curveVelocity (I := I) σ t)) volume 0 l) :
    0 ≤ (π / l) ^ 2 * (l / 2)
      - ∫ t in (0 : ℝ)..l, Real.sin (π / l * t) ^ 2 *
          sectionalCurvature (g.leviCivita) (σ t) (Efield t)
            (curveVelocity (I := I) σ t) := by
  let J : Set ℝ := Set.Ioo (-1) (l + 1)
  have hJopen : IsOpen J := isOpen_Ioo
  have hsubJ : Set.Icc (0 : ℝ) l ⊆ J := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hσsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ σ J := by
    intro t ht
    exact (IsGeodesic.contMDiffAt_infty (I := I) g hσgeo hσc t).contMDiffWithinAt
  have hEsm : IsVectorFieldAlong (I := I) σ Efield J :=
    hEpar.isVectorFieldAlong_infty (I := I) g
      (fun t ht => IsGeodesic.contMDiffAt_infty (I := I) g hσgeo hσc t)
  let w : ℝ → ℝ := fun t => Real.sin (π / l * t)
  let W : ∀ t, TangentSpace I (σ t) := fun t => w t • Efield t
  have hwsm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ w J := by
    exact (by fun_prop : ContDiff ℝ ∞ w).contMDiff.contMDiffOn
  have hWsm : IsVectorFieldAlong (I := I) σ W J := by
    exact hEsm.smul hwsm
  obtain ⟨δ, a, b, hδ, hsub, hf⟩ :=
    exists_intrinsicExpVariation_contMDiffOn_slab (I := I) g hJopen hl hsubJ hσsm hWsm
  let f : ℝ → ℝ → M := intrinsicExpVariation (I := I) g σ W
  have hbase : f 0 = σ := by simp [f]
  let Ef : ∀ t, TangentSpace I (f 0 t) := fun t => by
    simpa [f] using Efield t
  have hzero : W 0 = 0 := by simp [W, w]
  have hmul : π / l * l = π := by field_simp
  have hlast : W l = 0 := by simp [W, w, hmul]
  have hfix₀ : ∀ s, f s 0 = f 0 0 := by
    intro s
    simp [f, intrinsicExpVariation, hzero, geodesicMaximalCurve_zero]
  have hfixl : ∀ s, f s l = f 0 l := by
    intro s
    simp [f, intrinsicExpVariation, hlast, geodesicMaximalCurve_zero]
  have hgeo : ∀ t ∈ Set.Icc (0 : ℝ) l,
      curveAcceleration (I := I) g (f 0) t = 0 := by
    intro t ht
    rw [hbase]
    exact IsGeodesic.curveAcceleration_eq_zero hσgeo t
  have hEpar' : ∀ t ∈ Set.Icc (0 : ℝ) l,
      derivAlongCurve (I := I) g (f 0) Ef t = 0 := by
    intro t ht
    rw [hbase]
    simpa [Ef] using (hEpar t (hsubJ ht)).2
  have hEdiff' : ∀ t ∈ Set.Icc (0 : ℝ) l,
      DifferentiableAt ℝ (chartFieldRep (I := I) (f 0) (f 0 t) Ef) t := by
    intro t ht
    rw [hbase]
    simpa [Ef] using (hEpar t (hsubJ ht)).1
  have hEunit' : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (Ef t) (Ef t) = 1 := by
    intro t ht
    rw [hbase]
    simpa [Ef] using hEunit t (hsubJ ht)
  have hEperp' : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (Ef t) (curveVelocity (I := I) (f 0) t) = 0 := by
    intro t ht
    rw [hbase]
    simpa [Ef] using hEperp t (hsubJ ht)
  have hspeedσ := globalSegment_curveVelocity_unit (I := I) g hl hσc hσgeo hunit
  have hspeed : ∀ t ∈ Set.Icc (0 : ℝ) l,
      g.metricInner (f 0 t) (curveVelocity (I := I) (f 0) t)
        (curveVelocity (I := I) (f 0) t) = 1 := by
    intro t ht
    rw [hbase]
    exact hspeedσ t
  have hVfield : variationField (I := I) f =
      fun t => Real.sin (π / l * t) • Ef t := by
    rw [hbase]
    funext t
    simpa [f, W, w, Ef] using
      variationField_intrinsicExpVariation (I := I) g σ W t
  have hint' : IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 *
      sectionalCurvature (g.leviCivita) (f 0 t) (Ef t)
        (curveVelocity (I := I) (f 0) t)) volume 0 l := by
    rw [hbase]
    simpa [Ef] using hint
  have hidx := bonnetSynge_index_nonneg_of_segment_local (I := I) g hl hseg hunit
    hbase hδ hsub hf hgeo hfix₀ hfixl hEpar' hEdiff' hEunit' hEperp' hspeed
    hVfield hint'
  rw [hbase] at hidx
  simpa [Ef] using hidx

set_option maxHeartbeats 2000000 in
/-- **Math.** Myers' diameter theorem with the intrinsic sine variations and
their minimizing-index inequalities constructed internally.  Compared with
`myersRicciDiameterBound_of_velocityFrameIndexNonneg`, the caller supplies only
integrability of the smooth sectional-curvature weights; index nonnegativity is
now derived from the distance-realizing segment. -/
theorem myersRicciDiameterBound_of_velocityFrameCurvatureIntegrable
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {k : ℝ} (hk : 0 < k)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hRic : HasRicciBoundedBelow g.leviCivita k)
    (hint : ∀ (σ : ℝ → M) (l : ℝ), 0 < l → π / Real.sqrt k < l →
      Continuous σ → Geodesic.IsGeodesic (I := I) g σ →
      IsSegment (I := I) g σ 0 l →
      (∀ t ∈ Set.Icc (0 : ℝ) l, curveLength (I := I) g σ 0 t = t) →
      ∀ (e : Fin (Module.finrank ℝ E) → (∀ t, TangentSpace I (σ t)))
        (n₀ : Fin (Module.finrank ℝ E)),
        (∀ i, IsParallelSolOn (I := I) g σ (Set.Ioo (-1) (l + 1)) (e i)) →
        (∀ t ∈ Set.Ioo (-1) (l + 1), ∀ i j,
          g.metricInner (σ t) (e i t) (e j t) = if i = j then (1 : ℝ) else 0) →
        (∀ t ∈ Set.Ioo (-1) (l + 1), e n₀ t = curveVelocity (I := I) σ t) →
        ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))).erase n₀,
          IntervalIntegrable
            (fun t => Real.sin (π / l * t) ^ 2 *
              sectionalCurvature (g.leviCivita) (σ t) (e i t)
                (curveVelocity (I := I) σ t)) volume 0 l) :
    Metric.diam (Set.univ : Set M) ≤ π / Real.sqrt k ∧ CompactSpace M := by
  apply myersRicciDiameterBound_of_velocityFrameIndexNonneg (I := I) g hg hk hdim hRic
  intro σ l hl hlk hσc hσgeo hseg hunit e n₀ hepar heorth hevel i hi
  have hi_ne : i ≠ n₀ := (Finset.mem_erase.mp hi).1
  have hEunit : ∀ t ∈ Set.Ioo (-1) (l + 1),
      g.metricInner (σ t) (e i t) (e i t) = 1 := by
    intro t ht
    simpa using heorth t ht i i
  have hEperp : ∀ t ∈ Set.Ioo (-1) (l + 1),
      g.metricInner (σ t) (e i t) (curveVelocity (I := I) σ t) = 0 := by
    intro t ht
    rw [← hevel t ht]
    simpa [hi_ne] using heorth t ht i n₀
  refine ⟨hint σ l hl hlk hσc hσgeo hseg hunit e n₀ hepar heorth hevel i hi, ?_⟩
  exact intrinsicSine_index_nonneg_of_segment (I := I) g hl hσc hσgeo hseg hunit
    (hepar i) hEunit hEperp
    (hint σ l hl hlk hσc hσgeo hseg hunit e n₀ hepar heorth hevel i hi)

set_option maxHeartbeats 2000000 in
/-- **Math.** Petersen §6.3, **Myers' theorem** in callback-free diameter and
compactness form.  On a complete connected Riemannian manifold of dimension at
least two, the lower bound `Ric ≥ (n - 1) k g`, with `k > 0`, implies
`diam M ≤ π / √k` and compactness.

The velocity-seeded parallel orthonormal frame, the intrinsic exponential
sine variations, their common smooth slabs, minimizing-index nonnegativity,
and integrability of the sectional-curvature weights are all constructed
internally. -/
theorem myersRicciDiameterBound_of_ricciLowerBound
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {k : ℝ} (hk : 0 < k)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hRic : HasRicciBoundedBelow g.leviCivita k) :
    Metric.diam (Set.univ : Set M) ≤ π / Real.sqrt k ∧ CompactSpace M := by
  apply myersRicciDiameterBound_of_velocityFrameCurvatureIntegrable (I := I)
    g hg hk hdim hRic
  intro σ l hl _ hσc hσgeo _ hunit e n₀ hepar heorth hevel i hi
  have hi_ne : i ≠ n₀ := (Finset.mem_erase.mp hi).1
  have hEunit : ∀ t ∈ Ioo (-1) (l + 1),
      g.metricInner (σ t) (e i t) (e i t) = 1 := by
    intro t ht
    simpa using heorth t ht i i
  have hEperp : ∀ t ∈ Ioo (-1) (l + 1),
      g.metricInner (σ t) (e i t) (curveVelocity (I := I) σ t) = 0 := by
    intro t ht
    rw [← hevel t ht]
    simpa [hi_ne] using heorth t ht i n₀
  have hspeed := globalSegment_curveVelocity_unit (I := I) g hl hσc hσgeo hunit
  exact intervalIntegrable_sine_sq_sectionalCurvature_of_parallel (I := I)
    g hl hσc hσgeo (hepar i) hEunit hEperp hspeed

/-- **Math.** Petersen §6.3, Lemma 6.3.1 → not distance-minimizing (geometric wiring).  Under
`sec ≥ k > 0`, given the technical Bonnet–Synge variation data for a unit-speed geodesic segment
`σ = f 0` of length `l > π/√k`, the endpoints are strictly closer than `l`:
`d(σ(0), σ(l)) < l`.  The negative second variation `d²E/ds²|₀ < 0` comes from
`bonnetSynge_longGeodesicsNotMinimizing` (which is where `sec ≥ k` enters, via
`bonnetSynge_index_core`); the passage to `d < l` is the packaged bridge
`riemannianDistance_lt_of_negSecondVar_unitSpeed`. -/
theorem longGeodesic_notMinimizing_of_secBound (g : RiemannianMetric I M)
    {σ : ℝ → M} {l k : ℝ} (hk : 0 < k) (hlk : π / Real.sqrt k < l)
    (hsec : HasSecBoundedBelow (g.leviCivita) k)
    {f : ℝ → ℝ → M} {Efield : ∀ t, TangentSpace I (f 0 t)} {δ a b : ℝ}
    (hbv : IsBonnetSyngeVariation (I := I) g σ l f Efield δ a b) :
    riemannianDistance (I := I) g (σ 0) (σ l) < l := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hl : 0 < l := lt_trans (div_pos Real.pi_pos hsk) hlk
  -- Lemma 6.3.1: the sin-weighted parallel field has strictly negative second variation
  have h2neg := bonnetSynge_longGeodesicsNotMinimizing (I := I) g hk hlk hbv.hδ hbv.hsub hbv.hf
    hbv.hgeo hbv.hfix₀ hbv.hfixl hbv.hEpar hbv.hEdiff hbv.hEunit hbv.hEperp hbv.hspeed hbv.hVfield
    (fun t => hsec (f 0 t)) hbv.hint
  have hlt := riemannianDistance_lt_of_negSecondVar_unitSpeed (I := I) g hl hbv.hδ hbv.hsub
    hbv.hf hbv.hfix₀ hbv.hfixl hbv.hspeed h2neg
  rwa [hbv.base] at hlt

/-- **Math.** Petersen §6.3, **Corollary 6.3.2** (Hopf–Rinow 1931 / Myers 1932).  A complete
manifold with `sec ≥ k > 0` has `diam ≤ π/√k` and is compact.  The curvature bound `hsec` enters
genuinely — through `bonnetSynge_index_core` inside `longGeodesic_notMinimizing_of_secBound` — so
this is **not** an "assume the conclusion" shell: the only thing carried is the *technical*
existence `hvar` of the exponential Bonnet–Synge variation (the slab-smoothness of
`Ch06/ExpVariation.lean`), exactly the gap already carried by Lemma 6.3.1
(`bonnetSynge_longGeodesicsNotMinimizing`).  Given `hvar`, `sec ≥ k` forces every unit-speed
geodesic longer than `π/√k` to stop minimizing (`d(endpoints) < l`), which contradicts its being
a distance-realizing segment; hence no distance exceeds `π/√k`.  The topological finite-`π₁`
step for an explicitly supplied compact simply connected cover is proved separately in
`Ch06/MyersFundamentalGroup.lean`. -/
theorem hopfRinowMyers_diameterBound (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] {k : ℝ} (hk : 0 < k)
    (hsec : HasSecBoundedBelow (g.leviCivita) k)
    (hvar : ∀ (σ : ℝ → M) (l : ℝ), 0 < l → π / Real.sqrt k < l →
      IsSegment (I := I) g σ 0 l →
      (∀ t ∈ Set.Icc (0:ℝ) l, curveLength (I := I) g σ 0 t = t) →
      ∃ (f : ℝ → ℝ → M) (Efield : ∀ t, TangentSpace I (f 0 t)) (δ a b : ℝ),
        IsBonnetSyngeVariation (I := I) g σ l f Efield δ a b) :
    Metric.diam (Set.univ : Set M) ≤ π / Real.sqrt k ∧ CompactSpace M := by
  refine diameterBound_of_notMinimizing (I := I) g hg hk (fun σ l hlk hseg hunit => ?_)
  have hl : 0 < l := lt_trans (div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)) hlk
  obtain ⟨f, Efield, δ, a, b, hbv⟩ := hvar σ l hl hlk hseg hunit
  exact longGeodesic_notMinimizing_of_secBound (I := I) g hk hlk hsec hbv

/-! ### Myers' theorem: the Ricci frame version (Thm 6.3.3) -/

/-- **Math.** Petersen §6.3, the **Myers–Ricci frame variation data** for a unit-speed geodesic
segment `σ` on `[0,l]`: a family of `m` proper variations `Vᵢ` with common base `Vᵢ 0 = σ`, each
carrying the Bonnet–Synge data for a unit parallel field `Eᵢ ⟂ σ̇` with variation field
`sin(π·/l)·Eᵢ`.  This structure is regularity-only: the cardinality and Ricci trace identity for
an orthonormal frame are supplied separately by `IsMyersRicciFrameVariation`, and the curvature
inequality by `HasRicciBoundedBelow`.  Same honest scope as Lemma 6.3.1 /
`myersRicci_secondVariation_neg`. -/
structure IsMyersRicciVariation (g : RiemannianMetric I M) (σ : ℝ → M) (l : ℝ) {m : ℕ}
    (V : Fin m → ℝ → ℝ → M) (Efield : ∀ i : Fin m, ∀ t, TangentSpace I (V i 0 t))
    (δ a b : ℝ) : Prop where
  base : ∀ i, V i 0 = σ
  hm : 1 ≤ m
  hδ : 0 < δ
  hsub : Set.Icc (0 : ℝ) l ⊆ Set.Ioo a b
  hf : ∀ i, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry (V i))
    (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b)
  hgeo : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) l, curveAcceleration (I := I) g (V i 0) t = 0
  hfix₀ : ∀ i, ∀ s, V i s 0 = V i 0 0
  hfixl : ∀ i, ∀ s, V i s l = V i 0 l
  hEpar : ∀ i, IsParallelAlong (I := I) g (V i 0) (Efield i)
  hEdiff : ∀ i, ∀ t,
    DifferentiableAt ℝ (chartFieldRep (I := I) (V i 0) (V i 0 t) (Efield i)) t
  hEunit : ∀ i, ∀ t, g.metricInner (V i 0 t) (Efield i t) (Efield i t) = 1
  hEperp : ∀ i, ∀ t,
    g.metricInner (V i 0 t) (Efield i t) (curveVelocity (I := I) (V i 0) t) = 0
  hspeed : ∀ i, ∀ t, g.metricInner (V i 0 t) (curveVelocity (I := I) (V i 0) t)
    (curveVelocity (I := I) (V i 0) t) = 1
  hVfield : ∀ i, variationField (I := I) (V i) = fun t => Real.sin (π / l * t) • Efield i t
  hint : ∀ i, IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 *
    sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t) (curveVelocity (I := I) (V i 0) t))
    volume 0 l

/-- **Math.** Every member of a Myers sine-frame variation has nonnegative
index expression along a distance-realizing unit-speed segment.  This is the
family form of `bonnetSynge_index_nonneg_of_segment`; each component of
`IsMyersRicciVariation` is exactly a Bonnet--Synge variation. -/
theorem IsMyersRicciVariation.index_nonneg_of_segment
    (g : RiemannianMetric I M) {σ : ℝ → M} {l : ℝ} {m : ℕ}
    {V : Fin m → ℝ → ℝ → M}
    {Efield : ∀ i : Fin m, ∀ t, TangentSpace I (V i 0 t)} {δ a b : ℝ}
    (hmv : IsMyersRicciVariation (I := I) g σ l V Efield δ a b)
    (hl : 0 < l) (hseg : IsSegment (I := I) g σ 0 l)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) l, curveLength (I := I) g σ 0 t = t) :
    ∀ i, 0 ≤ (π / l) ^ 2 * (l / 2)
      - ∫ t in (0 : ℝ)..l, Real.sin (π / l * t) ^ 2 *
          sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t)
            (curveVelocity (I := I) (V i 0) t) := by
  intro i
  let hbv : IsBonnetSyngeVariation (I := I) g σ l (V i) (Efield i) δ a b :=
    { base := hmv.base i
      hδ := hmv.hδ
      hsub := hmv.hsub
      hf := hmv.hf i
      hgeo := hmv.hgeo i
      hfix₀ := hmv.hfix₀ i
      hfixl := hmv.hfixl i
      hEpar := hmv.hEpar i
      hEdiff := hmv.hEdiff i
      hEunit := hmv.hEunit i
      hEperp := hmv.hEperp i
      hspeed := hmv.hspeed i
      hVfield := hmv.hVfield i
      hint := hmv.hint i }
  exact bonnetSynge_index_nonneg_of_segment (I := I) g hl hseg hunit hbv

/-- **Math.** The Myers variation data together with the two algebraic facts identifying its
family with the directions perpendicular to the geodesic velocity: it has `n-1` members and its
sectional-curvature sum is `Ric(σ̇,σ̇)`.  These are exactly the frame facts supplied by completing
the unit velocity to an orthonormal frame and parallel-transporting it.  Unlike a frame-sum lower
bound, `ricci_eq_sum` contains no curvature inequality; it lets `myersRicciDiameterBound` derive
that inequality from the separate global hypothesis `HasRicciBoundedBelow`. -/
structure IsMyersRicciFrameVariation (g : RiemannianMetric I M) (σ : ℝ → M) (l : ℝ) {m : ℕ}
    (V : Fin m → ℝ → ℝ → M) (Efield : ∀ i : Fin m, ∀ t, TangentSpace I (V i 0 t))
    (δ a b : ℝ) extends IsMyersRicciVariation (I := I) g σ l V Efield δ a b where
  card_eq : m = Module.finrank ℝ E - 1
  ricci_eq_sum : ∀ t ∈ Set.Icc (0 : ℝ) l,
    RicciCurvature g.leviCivita.toAffineConnection (σ t)
        (curveVelocity (I := I) σ t) (curveVelocity (I := I) σ t) =
      ∑ i, sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t)
        (curveVelocity (I := I) (V i 0) t)

/-- **Math.** Petersen §6.3, Theorem 6.3.3 → not distance-minimizing (Ricci frame wiring).  Given
the Myers frame variation data for a unit-speed geodesic segment `σ` of length `l > π/√k` and the
**Ricci lower bound in frame-sum form** `m·k ≤ ∑ᵢ sec(Eᵢ, σ̇)` on `[0,l]` (which equals
`Ric(σ̇,σ̇) ≥ (n-1)k` for the orthonormal frame with `m = n-1`), the endpoints are strictly closer
than `l`.  `myersRicci_secondVariation_neg` produces *some* `Vᵢ` with `d²E/ds²|₀ < 0` (this is
where the Ricci bound enters, via `myers_index_core`); that `Vᵢ` then fails to minimize by the
packaged bridge `riemannianDistance_lt_of_negSecondVar_unitSpeed`. -/
theorem longGeodesic_notMinimizing_of_ricciBound (g : RiemannianMetric I M)
    {σ : ℝ → M} {l k : ℝ} {m : ℕ} (hk : 0 < k) (hlk : π / Real.sqrt k < l)
    {V : Fin m → ℝ → ℝ → M} {Efield : ∀ i : Fin m, ∀ t, TangentSpace I (V i 0 t)} {δ a b : ℝ}
    (hmv : IsMyersRicciVariation (I := I) g σ l V Efield δ a b)
    (hRic : ∀ t ∈ Set.Icc (0:ℝ) l, (m : ℝ) * k ≤
      ∑ i, sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t)
        (curveVelocity (I := I) (V i 0) t)) :
    riemannianDistance (I := I) g (σ 0) (σ l) < l := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hl : 0 < l := lt_trans (div_pos Real.pi_pos hsk) hlk
  -- Myers' core: some perpendicular field has strictly negative second variation
  obtain ⟨i, h2neg⟩ := myersRicci_secondVariation_neg (I := I) g hmv.hm hk hlk V hmv.hδ hmv.hsub
    hmv.hf hmv.hgeo hmv.hfix₀ hmv.hfixl Efield hmv.hEpar hmv.hEdiff hmv.hEunit hmv.hEperp
    hmv.hspeed hmv.hVfield hmv.hint hRic
  have hlt := riemannianDistance_lt_of_negSecondVar_unitSpeed (I := I) g hl hmv.hδ hmv.hsub
    (hmv.hf i) (hmv.hfix₀ i) (hmv.hfixl i) (hmv.hspeed i) h2neg
  rwa [hmv.base i] at hlt

/-- **Math.** The frame-sum form of Petersen §6.3, Theorem 6.3.3: if every long unit-speed
distance-realizing segment carries Myers variation data whose sectional-curvature sum is bounded
below by `m·k`, then `diam ≤ π/√k` and the manifold is compact.  This is the low-level assembly
consumed by `myersRicciDiameterBound`; use that theorem for the genuine global Ricci hypothesis. -/
theorem myersRicciDiameterBound_of_frameSum (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] {k : ℝ} (hk : 0 < k)
    (hvar : ∀ (σ : ℝ → M) (l : ℝ), 0 < l → π / Real.sqrt k < l →
      IsSegment (I := I) g σ 0 l →
      (∀ t ∈ Set.Icc (0:ℝ) l, curveLength (I := I) g σ 0 t = t) →
      ∃ (m : ℕ) (V : Fin m → ℝ → ℝ → M)
        (Efield : ∀ i : Fin m, ∀ t, TangentSpace I (V i 0 t)) (δ a b : ℝ),
        IsMyersRicciVariation (I := I) g σ l V Efield δ a b ∧
        (∀ t ∈ Set.Icc (0:ℝ) l, (m : ℝ) * k ≤
          ∑ i, sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t)
            (curveVelocity (I := I) (V i 0) t))) :
    Metric.diam (Set.univ : Set M) ≤ π / Real.sqrt k ∧ CompactSpace M := by
  refine diameterBound_of_notMinimizing (I := I) g hg hk (fun σ l hlk hseg hunit => ?_)
  have hl : 0 < l := lt_trans (div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)) hlk
  obtain ⟨m, V, Efield, δ, a, b, hmv, hRic⟩ := hvar σ l hl hlk hseg hunit
  exact longGeodesic_notMinimizing_of_ricciBound (I := I) g hk hlk hmv hRic

/-- **Math.** Petersen §6.3, **Theorem 6.3.3** (Myers 1941).  A complete manifold with the
genuine global lower bound `Ric ≥ (n-1)k·g`, `k > 0`, has `diam ≤ π/√k` and is compact.

The curvature bound is the standalone hypothesis `hRic`; it is not bundled into the technical
variation assumption.  The latter supplies a proper exponential variation for each perpendicular
parallel frame member, together with the dimension and trace identities that identify the frame
sum with `Ric(σ̇,σ̇)`.  Unit speed and `hRic` therefore derive the exact frame-sum inequality used
by `myersRicci_secondVariation_neg`.  The remaining technical gap is construction and joint
slab-smoothness of those exponential variations.  The compact-cover finite-`π₁` implication is
proved separately in `Ch06/MyersFundamentalGroup.lean`. -/
theorem myersRicciDiameterBound (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] {k : ℝ} (hk : 0 < k)
    (hRic : HasRicciBoundedBelow g.leviCivita k)
    (hvar : ∀ (σ : ℝ → M) (l : ℝ), 0 < l → π / Real.sqrt k < l →
      IsSegment (I := I) g σ 0 l →
      (∀ t ∈ Set.Icc (0 : ℝ) l, curveLength (I := I) g σ 0 t = t) →
      ∃ (m : ℕ) (V : Fin m → ℝ → ℝ → M)
        (Efield : ∀ i : Fin m, ∀ t, TangentSpace I (V i 0 t)) (δ a b : ℝ),
        IsMyersRicciFrameVariation (I := I) g σ l V Efield δ a b) :
    Metric.diam (Set.univ : Set M) ≤ π / Real.sqrt k ∧ CompactSpace M := by
  apply myersRicciDiameterBound_of_frameSum (I := I) g hg hk
  intro σ l hl hlk hseg hunit
  obtain ⟨m, V, Efield, δ, a, b, hmv⟩ := hvar σ l hl hlk hseg hunit
  refine ⟨m, V, Efield, δ, a, b, hmv.toIsMyersRicciVariation, ?_⟩
  intro t ht
  let i : Fin m := ⟨0, hmv.hm⟩
  have hspeed : g.metricInner (σ t) (curveVelocity (I := I) σ t)
      (curveVelocity (I := I) σ t) = 1 := by
    have hspeed' := hmv.hspeed i t
    rw [hmv.base i] at hspeed'
    exact hspeed'
  have hcard : (m : ℝ) = ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
    exact_mod_cast hmv.card_eq
  calc
    (m : ℝ) * k = ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * k *
        g.metricInner (σ t) (curveVelocity (I := I) σ t)
          (curveVelocity (I := I) σ t) := by rw [hspeed, mul_one, hcard]
    _ ≤ RicciCurvature g.leviCivita.toAffineConnection (σ t)
        (curveVelocity (I := I) σ t) (curveVelocity (I := I) σ t) := hRic _ _
    _ = ∑ i, sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t)
        (curveVelocity (I := I) (V i 0) t) := hmv.ricci_eq_sum t ht

/-- **Math.** Petersen §6.3, Theorem 6.3.3, with an honest global-geodesic
variation interface.  Hopf--Rinow constructs the segment `σ` as a continuous
geodesic on all of `ℝ`; those facts are passed to `hvar`, so its global
parallel-field and unit-speed obligations are supported by the witness rather
than being demanded of an arbitrary interval-only `IsSegment`.

The explicit dimension hypothesis is essential: in dimension one the Ricci
lower bound `Ric ≥ (n-1)k` is vacuous, while the diameter and compactness
conclusion is false for the complete real line. -/
theorem myersRicciDiameterBound_of_globalVariation (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] {k : ℝ} (hk : 0 < k)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hRic : HasRicciBoundedBelow g.leviCivita k)
    (hvar : ∀ (σ : ℝ → M) (l : ℝ), 0 < l → π / Real.sqrt k < l →
      Continuous σ → Geodesic.IsGeodesic (I := I) g σ →
      IsSegment (I := I) g σ 0 l →
      (∀ t ∈ Set.Icc (0 : ℝ) l, curveLength (I := I) g σ 0 t = t) →
      ∃ (m : ℕ) (V : Fin m → ℝ → ℝ → M)
        (Efield : ∀ i : Fin m, ∀ t, TangentSpace I (V i 0 t)) (δ a b : ℝ),
        IsMyersRicciFrameVariation (I := I) g σ l V Efield δ a b) :
    Metric.diam (Set.univ : Set M) ≤ π / Real.sqrt k ∧ CompactSpace M := by
  refine diameterBound_of_notMinimizing_global (I := I) g hg hk
    (fun σ l hlk hσc hσgeo hseg hunit => ?_)
  have hl : 0 < l := lt_trans (div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)) hlk
  obtain ⟨m, V, Efield, δ, a, b, hmv⟩ :=
    hvar σ l hl hlk hσc hσgeo hseg hunit
  have hmpos : 0 < m := by
    rw [hmv.card_eq]
    omega
  have hsum : ∀ t ∈ Set.Icc (0 : ℝ) l, (m : ℝ) * k ≤
      ∑ i, sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t)
        (curveVelocity (I := I) (V i 0) t) := by
    intro t ht
    let i : Fin m := ⟨0, hmpos⟩
    have hspeed : g.metricInner (σ t) (curveVelocity (I := I) σ t)
        (curveVelocity (I := I) σ t) = 1 := by
      have hspeed' := hmv.hspeed i t
      rw [hmv.base i] at hspeed'
      exact hspeed'
    have hcard : (m : ℝ) = ((Module.finrank ℝ E - 1 : ℕ) : ℝ) := by
      exact_mod_cast hmv.card_eq
    calc
      (m : ℝ) * k = ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * k *
          g.metricInner (σ t) (curveVelocity (I := I) σ t)
            (curveVelocity (I := I) σ t) := by rw [hspeed, mul_one, hcard]
      _ ≤ RicciCurvature g.leviCivita.toAffineConnection (σ t)
          (curveVelocity (I := I) σ t) (curveVelocity (I := I) σ t) := hRic _ _
      _ = ∑ i, sectionalCurvature (g.leviCivita) (V i 0 t) (Efield i t)
          (curveVelocity (I := I) (V i 0) t) := hmv.ricci_eq_sum t ht
  exact longGeodesic_notMinimizing_of_ricciBound (I := I) g hk hlk
    hmv.toIsMyersRicciVariation hsum

end PetersenLib

end MetricLayer
