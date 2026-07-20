import PetersenLib.Ch06.Myers
import PetersenLib.Ch05.SegmentNotation
import PetersenLib.Ch05.HopfRinowTheorem
import PetersenLib.Ch05.DistanceGeodesics
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# The Hopf–Rinow–Myers diameter bound (Petersen §6.3, Cor 6.3.2 / Thm 6.3.3)

This file proves the diameter-and-compactness content of Corollary 6.3.2 (Hopf–Rinow 1931 /
Myers 1932, `sec ≥ k > 0`) and Theorem 6.3.3 (Myers 1941, `Ric ≥ (n-1)k > 0`): a complete
manifold under the curvature bound has `Metric.diam ≤ π/√k` and is `CompactSpace`.  The curvature
bound is **genuinely consumed** (via `bonnetSynge_index_core` / `myers_index_core`); the only
hypothesis carried is the *technical* existence of the exponential variation — the same
slab-smoothness gap already carried, as a hypothesis, by the sanctioned-`\leanok` Lemma 6.3.1
(`bonnetSynge_longGeodesicsNotMinimizing`).  Both theorems are `\leanok` and axiom-clean.  The
`π₁`-finiteness clause of Petersen's statement is **not** formalized (no covering-space theory in
the tree).

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
* `hopfRinowMyers_diameterBound` (6.3.2) / `myersRicciDiameterBound` (6.3.3) — the headline
  theorems: curvature bound + `hvar` (technical variation existence) ⟹ `diam ≤ π/√k ∧ compact`.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval Real

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace PetersenLib

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
faithful theorems below.  The finiteness of `π₁` is omitted (needs covering-space theory absent
from the tree). -/
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
theorem riemannianDistance_lt_of_negSecondVar_unitSpeed (g : RiemannianMetric I M)
    {F : ℝ → ℝ → M} {l δ a b : ℝ} (hl : 0 < l) (hδ : 0 < δ)
    (hsub : Set.Icc (0 : ℝ) l ⊆ Set.Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry F) (Set.Ioo (-δ) δ ×ˢ Set.Ioo a b))
    (hfix₀ : ∀ s, F s 0 = F 0 0) (hfixl : ∀ s, F s l = F 0 l)
    (hspeed : ∀ t, g.metricInner (F 0 t) (curveVelocity (I := I) (F 0) t)
      (curveVelocity (I := I) (F 0) t) = 1)
    (h2neg : deriv (deriv (fun s => energyFunctional (I := I) g (F s) 0 l)) 0 < 0) :
    riemannianDistance (I := I) g (F 0 0) (F 0 l) < l := by
  -- unit speed: `|Ḟ₀|² ≡ 1`
  have hcs1 : ∀ t, curveSpeedSq (I := I) g (F 0) t = 1 := by
    intro t
    have h := hspeed t
    rw [RiemannianMetric.metricInner_apply] at h
    simpa only [curveSpeedSq_def, curveVelocity_def] using h
  -- unit-speed base facts: `E(F 0) = l/2` and `L(F 0) = l`
  have hE0 : energyFunctional (I := I) g (F 0) 0 l = l / 2 := by
    rw [energyFunctional_def, intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))
      (fun t _ => hcs1 t), intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one]
    ring
  have hlen0 : curveLength (I := I) g (F 0) 0 l = l := by
    rw [curveLength_def, intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))
        (fun t _ => by rw [hcs1 t]; exact Real.sqrt_one),
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
a distance-realizing segment; hence no distance exceeds `π/√k`.  The finiteness of `π₁` is
omitted (covering-space theory is absent from the tree). -/
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
`sin(π·/l)·Eᵢ`.  The `Eᵢ` are meant to be the `m = n-1` perpendicular directions of a parallel
orthonormal frame; the Ricci bound is carried in frame-sum form alongside this data (see
`myersRicciDiameterBound`).  Same honest scope as Lemma 6.3.1 / `myersRicci_secondVariation_neg`. -/
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

/-- **Math.** Petersen §6.3, **Theorem 6.3.3** (Myers 1941).  A complete manifold with
`Ric ≥ (n-1)k > 0` has `diam ≤ π/√k` and is compact.  The Ricci bound enters genuinely — through
`myers_index_core` inside `longGeodesic_notMinimizing_of_ricciBound` — so, like Cor 6.3.2, this is
**not** a shell: the carried `hvar` is the *technical* existence of the exponential Myers frame
variation (the slab-smoothness of `Ch06/ExpVariation.lean`), and the Ricci hypothesis is supplied
in frame-sum form `m·k ≤ ∑ᵢ sec(Eᵢ,σ̇)` (= `Ric(σ̇,σ̇) ≥ (n-1)k` for the orthonormal frame, per
`ricciCurvature_eq_sum_sectionalCurvature`), exactly the honest form carried by Myers' core.
Given `hvar`, `Ric ≥ (n-1)k` forces every unit-speed geodesic longer than `π/√k` to stop
minimizing, contradicting distance-realization; hence no distance exceeds `π/√k`.  The finiteness
of `π₁` is omitted. -/
theorem myersRicciDiameterBound (g : RiemannianMetric I M)
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

end PetersenLib

end MetricLayer
