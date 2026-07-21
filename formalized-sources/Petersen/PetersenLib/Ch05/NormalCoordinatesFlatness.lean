import PetersenLib.Ch05.GaussLemma
import PetersenLib.Riemannian.Exponential.C2Ball

/-!
# Petersen Ch. 5, §5.5 — first-order flatness of exponential coordinates (jet form)

Petersen's Lemma 5.5.7 states that in exponential coordinates around `p` the metric
reads `g_ij = δ_ij + O(r²)`.  Its *content* — the part every downstream result in
§5.5–§5.6 actually consumes — is the **1-jet** of the metric at the origin:

* `g_ij(0) = g_p`  (`expGram_zero`), and
* `∂_k g_ij(0) = 0`  (`expCoordinates_fderiv_gram_zero`).

This file provides exactly that, packaged as `expCoordinates_jetFlatness`.

## The route

Petersen differentiates the Gauss identity `Σ_j g_ij(x) x^j = δ_ij x^j` **twice** and
then symmetrizes over the three index permutations.  We replace the second
differentiation by the *ray-homogeneity already present in the Gauss lemma's own
universal quantifier*: testing `gaussLemma` at `x = t • v` against `t • v` gives
`t · expGram (t•v) v w = t · g_p(v, w)`, so for `t ≠ 0` the Gram is **constant along
each ray** (`expGram_radial_const`).  Differentiating that constancy at `t = 0` costs
only **one** derivative of `g`, which the packaged `C²` regularity of the chart
reading of `exp_p` supplies.  Petersen's three-permutation trick then survives
verbatim as a basis-free trilinear polarization (`fderivGram_vanish_of_symm`) — no
`Fin n` index gymnastics anywhere.

## What this file does NOT provide

* **NOT** the literal `O(r²)` rate of Lemma 5.5.7, i.e. **not**
  `PetersenLib.expCoordinates_firstOrderFlatness`.  The rate is strictly stronger than
  the jet proved here (`O(r²)` ⇒ the jet, not conversely).  Obtaining it needs a
  second-order Taylor bound on `x ↦ expGram x a b`, hence `C²` of the Gram, hence `C³`
  of the chart reading of `exp_p`.  The strongest packaged regularity on disk is `C²`
  (`Exponential.exists_contDiffOn_two_extChartAt_expMap_ball`), which yields only `C¹`
  of the Gram — enough for the jet, and so only `o(r)`, not `O(r²)`.
  (`Exponential.exists_pairMap_contDiffOn_infty` does carry `C^∞`, but it is stated for
  the abstract geodesic flow and is never bridged to `expMap`; building that bridge is
  the missing step.)
* **NOT** a literal `δ_ij`.  `expGram g p 0 = g.metricInner p`, and the chart
  coordinates come from an arbitrary `Module.finBasis ℝ E`, whose ambient inner product
  is unrelated to `g_p`.  Petersen's `δ_ij` presupposes a `g_p`-orthonormal frame; the
  basis-free `= g.metricInner p` is the faithful rendering, matching the precedent
  already set by `radialIsometryCondition` / `gaussLemma` in `Ch05/GaussLemma.lean`.

## Blueprint nodes

* `lem:pet-ch5-normal-coords-jet` — `expCoordinates_jetFlatness`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ### Exponential coordinates and the metric read in them -/

/-- The chart reading of `exp_p` as a map `E → E`: `w ↦ φ_p(exp_p w)`.  This is the
coordinate system Petersen calls *exponential (normal) coordinates* at `p`. -/
def expChart (g : RiemannianMetric I M) (p : M) : E → E :=
  fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))

/-- The metric in exponential coordinates: the chart Gram at `exp_p x`, pulled back
along `D(expChart)_x`.  In Petersen's notation `expGram g p x a b = g_ij(x) aⁱ bʲ`. -/
def expGram (g : RiemannianMetric I M) (p : M) (x a b : E) : ℝ :=
  chartMetricInner (I := I) g p (expChart (I := I) g p x)
    (fderiv ℝ (expChart (I := I) g p) x a)
    (fderiv ℝ (expChart (I := I) g p) x b)

/-! ### Bilinearity and symmetry of `expGram` in its vector slots -/

/-- **Math.** `expGram x · ·` is homogeneous in its first vector slot. -/
theorem expGram_smul_left (g : RiemannianMetric I M) (p : M) (x : E) (t : ℝ) (a b : E) :
    expGram (I := I) g p x (t • a) b = t * expGram (I := I) g p x a b := by
  unfold expGram
  rw [map_smul, chartMetricInner_smul_left]

/-- **Math.** `expGram x · ·` is homogeneous in its second vector slot. -/
theorem expGram_smul_right (g : RiemannianMetric I M) (p : M) (x : E) (t : ℝ) (a b : E) :
    expGram (I := I) g p x a (t • b) = t * expGram (I := I) g p x a b := by
  unfold expGram
  rw [map_smul, chartMetricInner_smul_right]

/-- **Math.** `expGram x · ·` is additive in its first vector slot. -/
theorem expGram_add_left (g : RiemannianMetric I M) (p : M) (x a a' b : E) :
    expGram (I := I) g p x (a + a') b
      = expGram (I := I) g p x a b + expGram (I := I) g p x a' b := by
  unfold expGram
  rw [map_add, chartMetricInner_add_left]

/-- **Math.** `expGram x · ·` is additive in its second vector slot. -/
theorem expGram_add_right (g : RiemannianMetric I M) (p : M) (x a b b' : E) :
    expGram (I := I) g p x a (b + b')
      = expGram (I := I) g p x a b + expGram (I := I) g p x a b' := by
  unfold expGram
  rw [map_add, chartMetricInner_add_right]

/-- **Math.** `expGram x · ·` is symmetric: `g_ij = g_ji`. -/
theorem expGram_symm (g : RiemannianMetric I M) (p : M) (x a b : E) :
    expGram (I := I) g p x a b = expGram (I := I) g p x b a :=
  chartMetricInner_symm (I := I) g p _ _ _

/-! ### The value at the origin: `g_ij(0) = g_p` -/

/-- **Math.** Petersen Ch. 5, Lemma 5.5.7, first half: at the origin of exponential
coordinates the metric *is* the intrinsic inner product `g_p`, since `D(exp_p)_0 = id`.
This is Petersen's `g_ij|_p = δ_ij` read in a basis-free way (see the module docstring
on why `g_p`, not a literal `δ_ij`, is the faithful rendering). -/
theorem expGram_zero (g : RiemannianMetric I M) (p : M) (a b : E) :
    expGram (I := I) g p 0 a b = g.metricInner p a b := by
  obtain ⟨ρ, hρ, _hdom, _hsrc, hd⟩ :=
    Exponential.exists_hasStrictFDerivAt_extChartAt_expMap (I := I) g p
  have hfd : fderiv ℝ (expChart (I := I) g p) 0 = ContinuousLinearMap.id ℝ E :=
    hd.hasFDerivAt.fderiv
  have h0 : expChart (I := I) g p (0 : E) = extChartAt I p p := by
    show extChartAt I p (expMap (I := I) g p (0 : TangentSpace I p)) = extChartAt I p p
    rw [expMap_zero]
  unfold expGram
  rw [hfd, h0]
  simp only [ContinuousLinearMap.coe_id', id_eq]
  have h := chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) a b
  rwa [trivializationAt_symm_self, trivializationAt_symm_self] at h

/-! ### Differentiability of the Gram in exponential coordinates -/

/-- **Math.** On a ball around the origin on which the chart reading of `exp_p` is `C²`,
the coordinate metric `x ↦ g_ij(x) aⁱ bʲ` is differentiable.  This is the regularity
input to the vanishing of `∂_k g_ij(0)`: one derivative of `g` costs two of `exp`. -/
theorem expGram_differentiableAt_ball (g : RiemannianMetric I M) (p : M) (a b : E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ ball (0 : E) ρ,
      DifferentiableAt ℝ (fun x : E => expGram (I := I) g p x a b) x := by
  obtain ⟨ρ, hρ, _hdom, hsrc, hC2⟩ :=
    Exponential.exists_contDiffOn_two_extChartAt_expMap_ball (I := I) g p
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  have hxb : ‖x‖ < ρ := by simpa using hx
  -- the source → target bridge for the chart at `p`
  have htgt : expChart (I := I) g p x ∈ (extChartAt I p).target := by
    refine (extChartAt I p).map_source ?_
    rw [extChartAt_source]
    exact hsrc x hxb
  -- `expChart` is `C²` at `x`, so both it and its derivative are differentiable there
  have hat : ContDiffAt ℝ 2 (expChart (I := I) g p) x :=
    hC2.contDiffAt (isOpen_ball.mem_nhds hx)
  have hE : DifferentiableAt ℝ (expChart (I := I) g p) x := hat.differentiableAt (by norm_num)
  have hDE : DifferentiableAt ℝ (fun y => fderiv ℝ (expChart (I := I) g p) y) x :=
    (hat.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- the Gram entries are differentiable along `expChart`
  have hGram : ∀ i j, DifferentiableAt ℝ
      (fun y : E => chartGramOnE (I := I) g p i j (expChart (I := I) g p y)) x := by
    intro i j
    exact (((chartGramOnE_contDiffOn (I := I) g p i j).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds htgt)).differentiableAt (by norm_num)).comp x hE
  -- the coordinates of the pushed-forward vectors are differentiable
  have hcoord : ∀ (i : Fin (Module.finrank ℝ E)) (c : E), DifferentiableAt ℝ
      (fun y : E => Geodesic.chartCoord (E := E) i (fderiv ℝ (expChart (I := I) g p) y c)) x := by
    intro i c
    have hev : DifferentiableAt ℝ
        (fun y : E => fderiv ℝ (expChart (I := I) g p) y c) x :=
      ((ContinuousLinearMap.apply ℝ E c).differentiableAt).comp x hDE
    have := ((Geodesic.chartCoordFunctional (E := E) i).differentiableAt).comp x hev
    simpa using this
  -- assemble: the Gram is a finite double sum of products of the above
  unfold expGram
  simp only [chartMetricInner_def]
  exact DifferentiableAt.fun_sum fun i _ =>
    DifferentiableAt.fun_sum fun j _ => ((hGram i j).mul (hcoord i a)).mul (hcoord j b)

/-- **Math.** The coordinate metric is differentiable at the origin — the only point at
which we need it in order to read off the 1-jet. -/
theorem expGram_differentiableAt_zero (g : RiemannianMetric I M) (p : M) (a b : E) :
    DifferentiableAt ℝ (fun x : E => expGram (I := I) g p x a b) 0 := by
  obtain ⟨ρ, hρ, hdiff⟩ := expGram_differentiableAt_ball (I := I) g p a b
  exact hdiff 0 (by simpa using hρ)

/-! ### The radial constancy supplied by the Gauss lemma -/

/-- **Math.** The **scaling trick** replacing Petersen's second differentiation.  Testing
the Gauss lemma at the point `t • v` against the radial vector `t • v` itself gives
`t · expGram (t•v) v w = t · g_p(v, w)`; cancelling `t ≠ 0` shows the Gram, evaluated on
the radial direction `v`, is **constant along the whole ray** `t ↦ t • v` — not merely
first-order constant.  This is where the Gauss lemma's universal quantifier over the
base point does the work of one extra derivative. -/
theorem expGram_radial_const (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (v w : E) (t : ℝ), t ≠ 0 → ‖t • v‖ < ρ →
      expGram (I := I) g p (t • v) v w = g.metricInner p v w := by
  obtain ⟨ρ, hρ, _hdom, _hsrc, hgauss⟩ := gaussLemma (I := I) g p
  refine ⟨ρ, hρ, fun v w t ht htv => ?_⟩
  -- Gauss at the base point `t • v`, tested against the radial vector `t • v`
  have h : expGram (I := I) g p (t • v) (t • v) w = g.metricInner p (t • v) w :=
    hgauss (t • v) w htv
  -- the `TangentSpace I p` smul and the `E` smul agree only up to defeq: restate with `exact`
  have hsm : g.metricInner p ((t • v : E) : TangentSpace I p) (w : TangentSpace I p)
      = t * g.metricInner p (v : TangentSpace I p) (w : TangentSpace I p) :=
    g.metricInner_smul_left p t (v : TangentSpace I p) (w : TangentSpace I p)
  rw [expGram_smul_left, hsm] at h
  exact mul_left_cancel₀ ht h

/-- **Math.** The *diagonal* directional derivative vanishes: differentiating the radial
constancy of `expGram · v w` at `t = 0` gives `∂_v g(v, w)|_0 = 0`.  Only one derivative
of the Gram is used, which the `C²` chart reading of `exp_p` supplies. -/
theorem expGram_fderiv_radial_zero (g : RiemannianMetric I M) (p : M) (v w : E) :
    fderiv ℝ (fun x : E => expGram (I := I) g p x v w) 0 v = 0 := by
  obtain ⟨ρ, hρ, hconst⟩ := expGram_radial_const (I := I) g p
  have hF : DifferentiableAt ℝ (fun x : E => expGram (I := I) g p x v w) 0 :=
    expGram_differentiableAt_zero (I := I) g p v w
  -- the ray `t ↦ t • v` has velocity `v` at `t = 0`
  have hcurve : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  -- chain rule along the ray
  have hcomp : HasDerivAt (fun t : ℝ => expGram (I := I) g p (t • v) v w)
      (fderiv ℝ (fun x : E => expGram (I := I) g p x v w) 0 v) 0 := by
    have h0 : ((fun t : ℝ => t • v) 0) = (0 : E) := by simp
    have hfd : HasFDerivAt (fun x : E => expGram (I := I) g p x v w)
        (fderiv ℝ (fun x : E => expGram (I := I) g p x v w) 0) ((fun t : ℝ => t • v) 0) := by
      rw [h0]; exact hF.hasFDerivAt
    exact hfd.comp_hasDerivAt 0 hcurve
  -- but that composite is constant near `0`, so its derivative there is `0`
  have hnhds : {t : ℝ | ‖t • v‖ < ρ} ∈ nhds (0 : ℝ) := by
    refine (isOpen_lt (by fun_prop) continuous_const).mem_nhds ?_
    simpa using hρ
  have hEq : (fun t : ℝ => expGram (I := I) g p (t • v) v w)
      =ᶠ[nhds (0 : ℝ)] fun _ => g.metricInner p v w := by
    filter_upwards [hnhds] with t ht
    rcases eq_or_ne t 0 with rfl | ht0
    · simpa using expGram_zero (I := I) g p v w
    · exact hconst v w t ht0 ht
  have hzero : HasDerivAt (fun t : ℝ => expGram (I := I) g p (t • v) v w) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (g.metricInner p v w)).congr_of_eventuallyEq hEq
  exact hcomp.unique hzero

/-! ### Petersen's three-permutation symmetrization, basis-free -/

/-- **Math.** Petersen's `2 ∂_k g_ij = ∂_k g_ij + ∂_i g_jk + ∂_j g_ki - ... = 0` trick, in
basis-free form.  A trilinear-in-the-relevant-slots, symmetric-in-the-last-two form that
vanishes on the diagonal `D v v w = 0` vanishes identically: diagonal vanishing plus
additivity forces antisymmetry in the first two slots (`D a b w = - D b a w`), and
chaining that against the last-two symmetry around the three cyclic permutations closes
the loop with a sign, forcing `D a b c = 0`. -/
theorem fderivGram_vanish_of_symm {F : Type*} [AddCommGroup F] (D : F → F → F → ℝ)
    (hadd1 : ∀ u u' a b, D (u + u') a b = D u a b + D u' a b)
    (hadd2 : ∀ u a a' b, D u (a + a') b = D u a b + D u a' b)
    (hsymm : ∀ u a b, D u a b = D u b a)
    (hdiag : ∀ v w, D v v w = 0) :
    ∀ a b c, D a b c = 0 := by
  -- polarizing the diagonal identity gives antisymmetry in the first two slots
  have star : ∀ a b w, D a b w = - D b a w := by
    intro a b w
    have h := hdiag (a + b) w
    rw [hadd1, hadd2, hadd2, hdiag, hdiag] at h
    linarith
  intro a b c
  have h1 : D a b c = - D b a c := star a b c
  have h2 : D b a c = D b c a := hsymm b a c
  have h3 : D b c a = - D c b a := star b c a
  have h4 : D c b a = D c a b := hsymm c b a
  have h5 : D c a b = - D a c b := star c a b
  have h6 : D a c b = D a b c := (hsymm a b c).symm
  linarith

/-! ### The 1-jet of the metric in exponential coordinates -/

/-- **Math.** Petersen Ch. 5, Lemma 5.5.7, second half: **all** first partials of the
metric vanish at the origin of exponential coordinates, `∂_k g_ij|_p = 0`. -/
theorem expCoordinates_fderiv_gram_zero (g : RiemannianMetric I M) (p : M) (u a b : E) :
    fderiv ℝ (fun x : E => expGram (I := I) g p x a b) 0 u = 0 := by
  refine fderivGram_vanish_of_symm
    (fun u a b => fderiv ℝ (fun x : E => expGram (I := I) g p x a b) 0 u) ?_ ?_ ?_ ?_ u a b
  · -- linear in the direction `u`: `fderiv` is a continuous linear map
    intro u u' a b
    exact (fderiv ℝ (fun x : E => expGram (I := I) g p x a b) 0).map_add u u'
  · -- additive in the first vector slot: additivity of `expGram` plus `fderiv_add`
    intro u a a' b
    show fderiv ℝ (fun x : E => expGram (I := I) g p x (a + a') b) 0 u
        = fderiv ℝ (fun x : E => expGram (I := I) g p x a b) 0 u
          + fderiv ℝ (fun x : E => expGram (I := I) g p x a' b) 0 u
    have hfun : (fun x : E => expGram (I := I) g p x (a + a') b)
        = fun x : E => expGram (I := I) g p x a b + expGram (I := I) g p x a' b :=
      funext fun x => expGram_add_left (I := I) g p x a a' b
    rw [hfun, fderiv_fun_add (expGram_differentiableAt_zero (I := I) g p a b)
      (expGram_differentiableAt_zero (I := I) g p a' b)]
    rfl
  · -- symmetric in the two vector slots
    intro u a b
    show fderiv ℝ (fun x : E => expGram (I := I) g p x a b) 0 u
        = fderiv ℝ (fun x : E => expGram (I := I) g p x b a) 0 u
    have hfun : (fun x : E => expGram (I := I) g p x a b)
        = fun x : E => expGram (I := I) g p x b a :=
      funext fun x => expGram_symm (I := I) g p x a b
    rw [hfun]
  · -- the diagonal case is the differentiated radial constancy
    intro v w
    exact expGram_fderiv_radial_zero (I := I) g p v w

/-- **Math.** Petersen Ch. 5, **Lemma 5.5.7, jet form**: in exponential coordinates around
`p` the metric agrees with `g_p` *to first order* at the origin —

* `g_ij(0) = g_p`, and
* `∂_k g_ij(0) = 0`.

This is the content Petersen's `g_ij = δ_ij + O(r²)` is used for downstream.  It is
strictly weaker than that statement: it gives `o(r)`, not the `O(r²)` rate (see the module
docstring — the rate needs `C³` of the chart reading of `exp_p`, which is not on disk).

The differentiability conjunct is included deliberately: `fderiv` is junk-valued (`0`) at
points of non-differentiability, so the vanishing of the derivative would be vacuous
without it.  Here it is genuine — the metric really is differentiable at the origin, and
its derivative there really is zero. -/
theorem expCoordinates_jetFlatness (g : RiemannianMetric I M) (p : M) :
    (∀ a b : E, expGram (I := I) g p 0 a b = g.metricInner p a b) ∧
    (∀ a b : E, DifferentiableAt ℝ (fun x : E => expGram (I := I) g p x a b) 0) ∧
    (∀ u a b : E, fderiv ℝ (fun x : E => expGram (I := I) g p x a b) 0 u = 0) :=
  ⟨expGram_zero (I := I) g p,
   fun a b => expGram_differentiableAt_zero (I := I) g p a b,
   fun u a b => expCoordinates_fderiv_gram_zero (I := I) g p u a b⟩

end PetersenLib

end
