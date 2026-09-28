import PetersenLib.Ch06.SecondVariation
import PetersenLib.Ch06.ThirdPartials
import PetersenLib.Ch06.CurvatureContinuity

/-!
# Petersen Ch. 6, §6.1 — the curvature identification in Synge's second variation

`Ch06/SecondVariation.lean` differentiates the energy twice and lands

$$E''(0) = \int_{t_1}^{t_2}\Big\langle \frac{D}{\partial s}\frac{D}{\partial s}
    \frac{\partial c}{\partial t}, \frac{\partial c}{\partial t}\Big\rangle
  + \Big|\frac{D}{\partial s}\frac{\partial c}{\partial t}\Big|^2\,dt .$$

That is the whole *analysis*. What Petersen's Thm. 6.1.4
(`thm:pet-ch6-synge-second-variation`, pp. 255–256) states is the *identified* form, in
which the first integrand is traded for curvature plus a total `t`-derivative:

$$\frac{d^2E}{ds^2}\Big|_{0}
  = \Big[\Big\langle \frac{D}{\partial s}\frac{\partial c}{\partial s},
      \frac{\partial c}{\partial t}\Big\rangle\Big]_{t_1}^{t_2}
    + \int_{t_1}^{t_2}\Big(\Big|\frac{D}{\partial t}\frac{\partial c}{\partial s}\Big|^2
      - g\big(R(V,\dot c)\dot c, V\big)\Big)\,dt ,\qquad V=\frac{\partial c}{\partial s}.$$

This file supplies that identification. It is the *algebra* of Thm. 6.1.4, and it is what
this chapter's §6.3 (Bonnet–Synge, Myers, Synge) actually consumes.

## The route, and why the curvature stays in the chart

The chain is
$$\frac{D}{\partial s}\frac{D}{\partial s}\frac{\partial c}{\partial t}
  \overset{(1)}{=} \frac{D}{\partial s}\frac{D}{\partial t}\frac{\partial c}{\partial s}
  \overset{(2)}{=} \frac{D}{\partial t}\frac{D}{\partial s}\frac{\partial c}{\partial s}
    - R^{\text{chart}}\Big(\frac{\partial c}{\partial s},\frac{\partial c}{\partial t}\Big)
      \frac{\partial c}{\partial s},$$
then pair with `∂ₜc` and use metric compatibility plus the geodesic hypothesis to turn
`⟨D_tD_s∂ₛc, ∂ₜc⟩` into `∂ₜ⟨D_s∂ₛc, ∂ₜc⟩`.

* **(1) is the symmetry lemma**, `mixedPartialCoord_symm` — off-diagonal, needing only
  `ContDiffAt ℝ 2`.  It is applied *under* the outer `D/∂s`, so it is needed as an
  equality of **functions of `s`** near `s₀`, not merely at `s₀`; that is what
  `EventuallyEq.deriv_eq` consumes.  This is why the hypothesis is `ContDiffAt ℝ 2` on a
  *neighbourhood* rather than at the point.
* **(2) is do Carmo's Ch. 4 Lemma 4.1 = Petersen's Lemma 6.1.2**, available as
  `Jacobi.surface_covariant_commutator_of_eventually`.

**The curvature is left as `chartCurvatureContraction2` in this file.**  The *particular*
bridge `chartCurvatureContraction2_eq_neg_curvatureTensorAt` is diagonal — it fires only when
the chart centre *is* the evaluation point — whereas here the foot `c(0,t)` moves along the
curve while the chart `α` stays fixed.  The *commutator* engine, by contrast, is off-diagonal:
its `α` is a free variable and its only side condition is
`f(s₀,t₀) ∈ interior (extChartAt I α).target`.  So the identification below holds in one fixed
chart along the whole curve.

**The moving-foot cost is now zero, and the abstract form goes UNDER the integral.**  An
earlier version of this note said the diagonality was a property of the available API and that
the abstract-tensor form could only be recovered pointwise "outside the integral".  That is no
longer true: `Ch06/CurvatureChartBridgeMoving.lean` supplies the off-diagonal bridge, and
`Ch06/SyngeAbstractCurvature.lean` uses it to state Thm. 6.1.4 with Petersen's abstract `R`
at the moving foot, under the integral —
`secondVariationEnergy_chart_curvatureTensorAt`, which is the form the blueprint's
`thm:pet-ch6-synge-second-variation` actually states.  This file is left phrased in the chart
curvature because that is what its own proof most directly produces; the abstract form is a
one-`rw` consequence.

## Sign bookkeeping

do Carmo's convention is the negative of Petersen's, and the commutator engine states
`D_tD_sV − D_sD_tV = R^{chart}(∂ₛf, ∂ₜf)V`.  Hence `D_sD_t∂ₛc = D_tD_s∂ₛc − R^{chart}(…)`,
and the curvature enters Petersen's formula with the minus sign his statement shows.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ### The `t`-slice bridge

`Ch06/SecondVariation.lean` has `covariantDerivCoord_fst_slice_eq_mixedPartialCoord`, the
`s`-slice identification `D_s(∂ₜc) = ∂²c/∂s∂t`.  The commutator engine needs the *other*
slice as well. -/

/-- **Math.** The covariant `t`-derivative of the field `∂ₛc` along a `t`-slice **is** the
coordinate mixed partial `∂²c/∂t∂s`.

The `t`-slice twin of `covariantDerivCoord_fst_slice_eq_mixedPartialCoord`; same proof with
`Jacobi.hasDerivAt_comp_snd` for `Jacobi.hasDerivAt_comp_fst`. -/
theorem covariantDerivCoord_snd_slice_eq_mixedPartialCoord_gen
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s t₀ : ℝ} (w : ℝ × ℝ) (hc : ContDiffAt ℝ 2 c (s, t₀)) :
    covariantDerivCoord (I := I) g α (fun t => c (s, t))
        (fun t => fderiv ℝ c (s, t) w) t₀
      = mixedPartialCoord (I := I) g α c (s, t₀) ((0, 1) : ℝ × ℝ) w := by
  have hfd2 : ContDiffAt ℝ 1 (fderiv ℝ c) (s, t₀) := hc.fderiv_right (m := 1) (by norm_num)
  have hgw : DifferentiableAt ℝ (fun y => fderiv ℝ c y w) (s, t₀) :=
    (hfd2.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hu : HasDerivAt (fun t => c (s, t)) (fderiv ℝ c (s, t₀) ((0, 1) : ℝ × ℝ)) t₀ :=
    Jacobi.hasDerivAt_comp_snd (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hW : HasDerivAt (fun t => fderiv ℝ c (s, t) w)
      (fderiv ℝ (fun y => fderiv ℝ c y w) (s, t₀) ((0, 1) : ℝ × ℝ)) t₀ :=
    Jacobi.hasDerivAt_comp_snd hgw.hasFDerivAt
  rw [covariantDerivCoord_def, mixedPartialCoord_def, hu.deriv, hW.deriv]

/-- The `w = (1,0)` case of `covariantDerivCoord_snd_slice_eq_mixedPartialCoord_gen`:
`D_t(∂ₛc) = ∂²c/∂t∂s`, the side of the symmetry lemma the commutator engine wants. -/
theorem covariantDerivCoord_snd_slice_eq_mixedPartialCoord
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s t₀ : ℝ} (hc : ContDiffAt ℝ 2 c (s, t₀)) :
    covariantDerivCoord (I := I) g α (fun t => c (s, t))
        (fun t => fderiv ℝ c (s, t) ((1, 0) : ℝ × ℝ)) t₀
      = mixedPartialCoord (I := I) g α c (s, t₀) ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) :=
  covariantDerivCoord_snd_slice_eq_mixedPartialCoord_gen (I := I) g α _ hc

/-- **Math.** `surfaceCovariantDerivS g α c (∂ₜc) = ∂²c/∂s∂t` — the vendored surface
operator and Ch. 5's coordinate mixed partial name the same object.  Restating
`covariantDerivCoord_fst_slice_eq_mixedPartialCoord` in the vocabulary the commutator
engine speaks. -/
theorem surfaceCovariantDerivS_fderivSnd_eq_mixedPartialCoord
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {p : ℝ × ℝ} (hc : ContDiffAt ℝ 2 c p) :
    Jacobi.surfaceCovariantDerivS (I := I) g α c
        (fun q => fderiv ℝ c q ((0, 1) : ℝ × ℝ)) p
      = mixedPartialCoord (I := I) g α c p ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
  obtain ⟨s, t⟩ := p
  exact covariantDerivCoord_fst_slice_eq_mixedPartialCoord (I := I) g α hc

/-- **Math.** `surfaceCovariantDerivT g α c (∂ₛc) = ∂²c/∂t∂s`, the `t`-slice twin of
`surfaceCovariantDerivS_fderivSnd_eq_mixedPartialCoord`. -/
theorem surfaceCovariantDerivT_fderivFst_eq_mixedPartialCoord
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {p : ℝ × ℝ} (hc : ContDiffAt ℝ 2 c p) :
    Jacobi.surfaceCovariantDerivT (I := I) g α c
        (fun q => fderiv ℝ c q ((1, 0) : ℝ × ℝ)) p
      = mixedPartialCoord (I := I) g α c p ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) := by
  obtain ⟨s, t⟩ := p
  exact covariantDerivCoord_snd_slice_eq_mixedPartialCoord (I := I) g α hc

/-- **Math.** Petersen §6.1, the **symmetry lemma in surface form**:
`D_s(∂ₜc) = D_t(∂ₛc)`.  Both sides are `∂²c/∂s∂t` read through different slices, so this
is `mixedPartialCoord_symm` conjugated by the two bridges above. -/
theorem surfaceCovariantDerivS_fderivSnd_eq_surfaceCovariantDerivT_fderivFst
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {p : ℝ × ℝ} (hc : ContDiffAt ℝ 2 c p) :
    Jacobi.surfaceCovariantDerivS (I := I) g α c
        (fun q => fderiv ℝ c q ((0, 1) : ℝ × ℝ)) p
      = Jacobi.surfaceCovariantDerivT (I := I) g α c
        (fun q => fderiv ℝ c q ((1, 0) : ℝ × ℝ)) p := by
  rw [surfaceCovariantDerivS_fderivSnd_eq_mixedPartialCoord (I := I) g α hc,
    surfaceCovariantDerivT_fderivFst_eq_mixedPartialCoord (I := I) g α hc,
    mixedPartialCoord_symm (I := I) g α hc]

/-! ### The curvature identification -/

/-- **Math.** The coordinate covariant derivative along a curve only sees the field
*near* the point: replacing the field by one agreeing with it on a neighbourhood leaves
`D/dt` unchanged.  Immediate from the definition (`deriv V t + Γ(u̇, V t)(u t)`), since
`deriv` is a germ invariant and the `Γ`-term needs only the value at `t`. -/
theorem covariantDerivCoord_congr_field (g : RiemannianMetric I M) (α : M)
    (u : ℝ → E) {V W : ℝ → E} {t : ℝ} (h : V =ᶠ[nhds t] W) :
    covariantDerivCoord (I := I) g α u V t = covariantDerivCoord (I := I) g α u W t := by
  rw [covariantDerivCoord_def, covariantDerivCoord_def, h.deriv_eq, h.self_of_nhds]

/-- **Math.** Petersen §6.1, the **curvature identification** at the heart of Thm. 6.1.4:
$$\frac{D}{\partial s}\frac{D}{\partial s}\frac{\partial c}{\partial t}
  = \frac{D}{\partial t}\frac{D}{\partial s}\frac{\partial c}{\partial s}
    - R^{\text{chart}}\Big(\frac{\partial c}{\partial s},\frac{\partial c}{\partial t}\Big)
      \frac{\partial c}{\partial s}.$$

The left side is exactly the first integrand of `hasDerivAt_deriv_windowEnergy_chart`; the
right side is a total `t`-derivative (once paired with `∂ₜc` along a geodesic) plus
curvature — which is what Petersen's statement displays.

**Proof.** The symmetry lemma rewrites the *inner* `D_s∂ₜc` as `D_t∂ₛc`; since it sits
under an outer `D/∂s`, it is needed as an equality of functions of `s` near `s₀`, supplied
by `ContDiffAt.eventually` and consumed by `covariantDerivCoord_congr_field`.  Then do
Carmo's Ch. 4 Lemma 4.1 (`Jacobi.surface_covariant_commutator_of_eventually`, = Petersen's
Lemma 6.1.2) commutes `D_s` past `D_t` at the cost of the chart curvature.

`α` is free: the commutator engine is **off-diagonal**, needing only that the foot lies in
the chart target's interior, so this holds in one fixed chart along the whole curve. -/
theorem covariantDerivCoord_mixedPartial_fst_eq_sub_chartCurvature
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t₀ : ℝ} (hc : ContDiffAt ℝ 3 c (s₀, t₀))
    (hmem : c (s₀, t₀) ∈ interior (extChartAt I α).target) :
    covariantDerivCoord (I := I) g α (fun s => c (s, t₀))
        (fun s => mixedPartialCoord (I := I) g α c (s, t₀)
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) s₀
      = Jacobi.surfaceCovariantDerivT (I := I) g α c
          (Jacobi.surfaceCovariantDerivS (I := I) g α c
            (fun q => fderiv ℝ c q ((1, 0) : ℝ × ℝ))) (s₀, t₀)
        - Jacobi.chartCurvatureContraction2 (I := I) g α
            (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ))
            (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))
            (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ)) (c (s₀, t₀)) := by
  classical
  -- `c` is `C³`, hence `C²`, on a whole neighbourhood of the base point
  have hev3 : ∀ᶠ q in nhds (s₀, t₀), ContDiffAt ℝ 3 c q := hc.eventually (by norm_num)
  have hev2 : ∀ᶠ q in nhds (s₀, t₀), ContDiffAt ℝ 2 c q := by
    filter_upwards [hev3] with q hq using hq.of_le (by norm_num)
  -- STEP 1 (symmetry, under the outer `D/∂s`): `D_s∂ₜc = D_t∂ₛc` near the base point
  have hslice : Tendsto (fun σ : ℝ => (σ, t₀)) (nhds s₀) (nhds (s₀, t₀)) :=
    (continuous_id.prodMk continuous_const).tendsto s₀
  have hsym : (fun σ : ℝ => mixedPartialCoord (I := I) g α c (σ, t₀)
        ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
      =ᶠ[nhds s₀] (fun σ : ℝ => Jacobi.surfaceCovariantDerivT (I := I) g α c
        (fun q => fderiv ℝ c q ((1, 0) : ℝ × ℝ)) (σ, t₀)) := by
    filter_upwards [hslice.eventually hev2] with σ hσ
    exact (surfaceCovariantDerivS_fderivSnd_eq_mixedPartialCoord (I := I) g α hσ).symm.trans
      (surfaceCovariantDerivS_fderivSnd_eq_surfaceCovariantDerivT_fderivFst (I := I) g α hσ)
  rw [covariantDerivCoord_congr_field (I := I) g α _ hsym]
  -- the left side is now `D_s (D_t ∂ₛc)`, i.e. `surfaceCovariantDerivS` of the `T`-partial
  show Jacobi.surfaceCovariantDerivS (I := I) g α c
      (Jacobi.surfaceCovariantDerivT (I := I) g α c
        (fun q => fderiv ℝ c q ((1, 0) : ℝ × ℝ))) (s₀, t₀) = _
  -- STEP 2 (Lemma 6.1.2): commute `D_s` past `D_t` at the cost of the chart curvature
  have hfd : ∀ᶠ q in nhds (s₀, t₀), HasFDerivAt c (fderiv ℝ c q) q := by
    filter_upwards [hev3] with q hq using (hq.differentiableAt (by norm_num)).hasFDerivAt
  have hfd2 : HasFDerivAt (fderiv ℝ c) (fderiv ℝ (fderiv ℝ c) (s₀, t₀)) (s₀, t₀) :=
    ((hc.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hV : ∀ᶠ q in nhds (s₀, t₀), HasFDerivAt (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ))
      (fderiv ℝ (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ)) q) q := by
    filter_upwards [hev3] with q hq
    exact ((((hq.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hV2 : HasFDerivAt (fderiv ℝ (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ)))
      (fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ))) (s₀, t₀)) (s₀, t₀) := by
    have h1 : ContDiffAt ℝ 2 (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ)) (s₀, t₀) :=
      (hc.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
    exact ((h1.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hcomm := Jacobi.surface_covariant_commutator_of_eventually (I := I) g α c
    (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ)) (fderiv ℝ c)
    (fderiv ℝ (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ)))
    (fderiv ℝ (fderiv ℝ c) (s₀, t₀))
    (fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ))) (s₀, t₀))
    s₀ t₀ hfd hfd2 hV hV2 hmem
  rw [← hcomm]
  abel

/-! ### The pairing step: metric compatibility along the `t`-slice

With the identification in hand, pairing against `∂ₜc` and using the geodesic hypothesis
turns the non-curvature half into a total `t`-derivative — the step that will later feed
the fundamental theorem of calculus and produce Petersen's boundary term. -/

/-- **Math.** `D_s` along an `s`-slice, in the generality of an arbitrary vector slot `w`.
`covariantDerivCoord_fst_slice_eq_mixedPartialCoord` is the `w = (0,1)` case; the `w =
(1,0)` case is `D_s∂ₛc`, the transversal acceleration carrying Petersen's boundary term. -/
theorem covariantDerivCoord_fst_slice_eq_mixedPartialCoord_gen
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t : ℝ} (w : ℝ × ℝ) (hc : ContDiffAt ℝ 2 c (s₀, t)) :
    covariantDerivCoord (I := I) g α (fun s => c (s, t))
        (fun s => fderiv ℝ c (s, t) w) s₀
      = mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) w := by
  have hfd2 : ContDiffAt ℝ 1 (fderiv ℝ c) (s₀, t) := hc.fderiv_right (m := 1) (by norm_num)
  have hgw : DifferentiableAt ℝ (fun y => fderiv ℝ c y w) (s₀, t) :=
    (hfd2.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hu : HasDerivAt (fun s => c (s, t)) (fderiv ℝ c (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hW : HasDerivAt (fun s => fderiv ℝ c (s, t) w)
      (fderiv ℝ (fun y => fderiv ℝ c y w) (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst hgw.hasFDerivAt
  rw [covariantDerivCoord_def, mixedPartialCoord_def, hu.deriv, hW.deriv]

/-- **Math.** `surfaceCovariantDerivS g α c (∂ₛc) = ∂²c/∂s∂s`, the **transversal
acceleration** `D_s∂ₛc`.  This is the field whose pairing with `∂ₜc` is Petersen's boundary
term in Thm. 6.1.4, and the field that vanishes for a *proper* variation. -/
theorem surfaceCovariantDerivS_fderivFst_eq_mixedPartialCoord
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {p : ℝ × ℝ} (hc : ContDiffAt ℝ 2 c p) :
    Jacobi.surfaceCovariantDerivS (I := I) g α c
        (fun q => fderiv ℝ c q ((1, 0) : ℝ × ℝ)) p
      = mixedPartialCoord (I := I) g α c p ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) := by
  obtain ⟨s, t⟩ := p
  exact covariantDerivCoord_fst_slice_eq_mixedPartialCoord_gen (I := I) g α _ hc

/-- **Math.** The coordinate mixed partial is **differentiable along a `t`-slice**.

The `t`-slice twin of `hasDerivAt_mixedPartialCoord_fst_slice`, and the one genuinely
analytic side condition of the pairing lemma below: the metric product-rule engine needs
`t ↦ D_s∂ₛc` to be differentiable at all, and `D_s∂ₛc` carries a Christoffel contraction
whose base point `c(s₀,t)` *moves* with `t`.  `Jacobi.hasDerivAt_chartChristoffelContraction_along`
is the Leibniz rule for that moving base; the pure-derivative half is what costs `C³`.
Only differentiability is claimed — the derivative's value is never needed, and stating it
would drag in `baseDerivChristoffelContraction`. -/
theorem differentiableAt_mixedPartialCoord_snd_slice (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t₀ : ℝ} (v w : ℝ × ℝ) (hc : ContDiffAt ℝ 3 c (s₀, t₀))
    (hmem : c (s₀, t₀) ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (fun t => mixedPartialCoord (I := I) g α c (s₀, t) v w) t₀ := by
  have hfd2 : ContDiffAt ℝ 2 (fderiv ℝ c) (s₀, t₀) := hc.fderiv_right (m := 2) (by norm_num)
  have hgv : ContDiffAt ℝ 2 (fun y => fderiv ℝ c y v) (s₀, t₀) := hfd2.clm_apply contDiffAt_const
  have hgw : ContDiffAt ℝ 2 (fun y => fderiv ℝ c y w) (s₀, t₀) := hfd2.clm_apply contDiffAt_const
  -- the pure third-derivative summand
  have hH : DifferentiableAt ℝ
      (fun y => fderiv ℝ (fun z => fderiv ℝ c z w) y v) (s₀, t₀) :=
    ((hgw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hfirst : HasDerivAt
      (fun t : ℝ => fderiv ℝ (fun z => fderiv ℝ c z w) (s₀, t) v)
      (fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ c z w) y v) (s₀, t₀)
        ((0, 1) : ℝ × ℝ)) t₀ :=
    Jacobi.hasDerivAt_comp_snd hH.hasFDerivAt
  -- the Christoffel summand, via the moving-base Leibniz rule
  have ha : HasDerivAt (fun t => fderiv ℝ c (s₀, t) v)
      (fderiv ℝ (fun y => fderiv ℝ c y v) (s₀, t₀) ((0, 1) : ℝ × ℝ)) t₀ :=
    Jacobi.hasDerivAt_comp_snd (hgv.differentiableAt (by norm_num)).hasFDerivAt
  have hb : HasDerivAt (fun t => fderiv ℝ c (s₀, t) w)
      (fderiv ℝ (fun y => fderiv ℝ c y w) (s₀, t₀) ((0, 1) : ℝ × ℝ)) t₀ :=
    Jacobi.hasDerivAt_comp_snd (hgw.differentiableAt (by norm_num)).hasFDerivAt
  have hu : HasDerivAt (fun t => c (s₀, t)) (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ)) t₀ :=
    Jacobi.hasDerivAt_comp_snd (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hsecond := Jacobi.hasDerivAt_chartChristoffelContraction_along (I := I) g α
    (fun t => fderiv ℝ c (s₀, t) v) (fun t => fderiv ℝ c (s₀, t) w)
    (fun t => c (s₀, t)) _ _ _ ha hb hu hmem
  have hfun : (fun t : ℝ => mixedPartialCoord (I := I) g α c (s₀, t) v w) =
      (fun t : ℝ => fderiv ℝ (fun z => fderiv ℝ c z w) (s₀, t) v) +
      fun t : ℝ => Geodesic.chartChristoffelContraction (I := I) g α
        (fderiv ℝ c (s₀, t) v) (fderiv ℝ c (s₀, t) w) (c (s₀, t)) := by
    funext t
    rfl
  rw [hfun]
  exact (hfirst.add hsecond).differentiableAt

/-- **Math.** Petersen §6.1, **metric compatibility along the `t`-slice** — the pairing
step of Thm. 6.1.4:
$$\frac{\partial}{\partial t}\Big\langle \frac{D}{\partial s}\frac{\partial c}{\partial s},
  \frac{\partial c}{\partial t}\Big\rangle
  = \Big\langle \frac{D}{\partial t}\frac{D}{\partial s}\frac{\partial c}{\partial s},
    \frac{\partial c}{\partial t}\Big\rangle
  + \Big\langle \frac{D}{\partial s}\frac{\partial c}{\partial s},
    \frac{D}{\partial t}\frac{\partial c}{\partial t}\Big\rangle .$$

The `t`-direction twin of `hasDerivAt_chartPairing_slice_ss`.  Along a **geodesic** the
second term dies (`D_t∂ₜc = 0`), leaving `⟨D_tD_s∂ₛc, ∂ₜc⟩` as an exact `t`-derivative —
which is precisely how Petersen's boundary term `[⟨D_s∂ₛc, ∂ₜc⟩]` is born. -/
theorem hasDerivAt_chartPairing_slice_ts (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t₀ : ℝ} (hc : ContDiffAt ℝ 3 c (s₀, t₀))
    (hmem : c (s₀, t₀) ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun t : ℝ => chartMetricInner (I := I) g α (c (s₀, t))
        (mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
        (fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ)))
      (chartMetricInner (I := I) g α (c (s₀, t₀))
          (covariantDerivCoord (I := I) g α (fun t => c (s₀, t))
            (fun t => mixedPartialCoord (I := I) g α c (s₀, t)
              ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ)) t₀)
          (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))
        + chartMetricInner (I := I) g α (c (s₀, t₀))
            (mixedPartialCoord (I := I) g α c (s₀, t₀) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
            (mixedPartialCoord (I := I) g α c (s₀, t₀)
              ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))) t₀ := by
  classical
  have hmem' : c (s₀, t₀) ∈ (extChartAt I α).target := interior_subset hmem
  have hc2 : ContDiffAt ℝ 2 c (s₀, t₀) := hc.of_le (by norm_num)
  have hfd2 : ContDiffAt ℝ 1 (fderiv ℝ c) (s₀, t₀) := hc2.fderiv_right (m := 1) (by norm_num)
  -- the three curves along the `t`-slice
  have hu : HasDerivAt (fun t => c (s₀, t)) (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ)) t₀ :=
    Jacobi.hasDerivAt_comp_snd (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hW : HasDerivAt (fun t => fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ))
      (fderiv ℝ (fun y => fderiv ℝ c y ((0, 1) : ℝ × ℝ)) (s₀, t₀) ((0, 1) : ℝ × ℝ)) t₀ :=
    Jacobi.hasDerivAt_comp_snd
      ((hfd2.clm_apply contDiffAt_const).differentiableAt (by norm_num)).hasFDerivAt
  have hV := differentiableAt_mixedPartialCoord_snd_slice (I := I) g α
    ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) hc hmem
  -- side conditions at the base point, from chart-target membership
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (c (s₀, t₀)) := fun i j =>
    ((chartGramOnE_contDiffOn (I := I) g α i j).contDiffAt
      (extChartAt_target_mem_nhds' (I := I) hmem')).differentiableAt (by norm_num)
  have hbase : (extChartAt I α).symm (c (s₀, t₀))
      ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I α).map_target hmem'
  -- the metric-compatibility engine
  have key := hasDerivAt_chartMetricInner_along (I := I) g α
    (fun t => c (s₀, t))
    (fun t => mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
    (fun t => fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ)) (t := t₀)
    hu.differentiableAt hV hW.differentiableAt hG hbase
  refine key.congr_deriv ?_
  rw [covariantDerivCoord_snd_slice_eq_mixedPartialCoord_gen (I := I) g α _ hc2]

/-! ### The integrand identity of Theorem 6.1.4

Everything above now composes into the single pointwise identity that Petersen's Thm. 6.1.4
rests on. -/

/-- **Math.** Petersen Thm. 6.1.4 (`thm:pet-ch6-synge-second-variation`), **the integrand
identity**.  Along a geodesic `t ↦ c(s₀,t)` (i.e. where `D_t∂ₜc = 0`),
$$\frac{\partial}{\partial t}\Big\langle \frac{D}{\partial s}\frac{\partial c}{\partial s},
    \frac{\partial c}{\partial t}\Big\rangle
  = \Big\langle \frac{D}{\partial s}\frac{D}{\partial s}\frac{\partial c}{\partial t},
      \frac{\partial c}{\partial t}\Big\rangle
    + \Big\langle R^{\text{chart}}\Big(\frac{\partial c}{\partial s},
        \frac{\partial c}{\partial t}\Big)\frac{\partial c}{\partial s},
      \frac{\partial c}{\partial t}\Big\rangle .$$

Read right-to-left this says: **the first integrand of `hasDerivAt_deriv_windowEnergy_chart`
equals a total `t`-derivative minus a curvature term.**  That is exactly the trade Petersen
performs — the total derivative integrates to his boundary term
`[⟨D_s∂ₛc, ∂ₜc⟩]_{t_1}^{t_2}` by the fundamental theorem of calculus, and the curvature term
becomes his `−g(R(V,ċ)ċ, V)` after the pair symmetries of `R`.  With
`hasDerivAt_deriv_windowEnergy_chart` supplying `E''(0)`, this is the whole content of
Thm. 6.1.4 bar the FTC bookkeeping.

**Proof.** `hasDerivAt_chartPairing_slice_ts` differentiates the pairing; the geodesic
hypothesis kills its `⟨D_s∂ₛc, D_t∂ₜc⟩` term; and
`covariantDerivCoord_mixedPartial_fst_eq_sub_chartCurvature` trades the surviving
`D_tD_s∂ₛc` for `D_sD_s∂ₜc` plus curvature.

`α` is free — no diagonal constraint anywhere — so this holds in one fixed chart at every
`t` along the curve, which is what an integral over `t` needs. -/
theorem hasDerivAt_chartPairing_transversalAccel_of_geodesic
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t₀ : ℝ} (hc : ContDiffAt ℝ 3 c (s₀, t₀))
    (hmem : c (s₀, t₀) ∈ interior (extChartAt I α).target)
    (hgeo : mixedPartialCoord (I := I) g α c (s₀, t₀)
      ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) = 0) :
    HasDerivAt (fun t : ℝ => chartMetricInner (I := I) g α (c (s₀, t))
        (mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
        (fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ)))
      (chartMetricInner (I := I) g α (c (s₀, t₀))
          (covariantDerivCoord (I := I) g α (fun s => c (s, t₀))
            (fun s => mixedPartialCoord (I := I) g α c (s, t₀)
              ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) s₀)
          (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))
        + chartMetricInner (I := I) g α (c (s₀, t₀))
            (Jacobi.chartCurvatureContraction2 (I := I) g α
              (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ))
              (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))
              (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ)) (c (s₀, t₀)))
            (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))) t₀ := by
  classical
  have hc2 : ContDiffAt ℝ 2 c (s₀, t₀) := hc.of_le (by norm_num)
  -- differentiate the pairing along the `t`-slice, then kill the geodesic term
  have h := hasDerivAt_chartPairing_slice_ts (I := I) g α hc hmem
  rw [hgeo, chartMetricInner_zero_right, add_zero] at h
  refine h.congr_deriv ?_
  -- `D_tD_s∂ₛc` in the commutator engine's vocabulary
  have hev3 : ∀ᶠ q in nhds (s₀, t₀), ContDiffAt ℝ 3 c q := hc.eventually (by norm_num)
  have hslice : Tendsto (fun τ : ℝ => (s₀, τ)) (nhds t₀) (nhds (s₀, t₀)) :=
    (continuous_const.prodMk continuous_id).tendsto t₀
  have hfield : (fun τ : ℝ => mixedPartialCoord (I := I) g α c (s₀, τ)
        ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
      =ᶠ[nhds t₀] (fun τ : ℝ => Jacobi.surfaceCovariantDerivS (I := I) g α c
        (fun q => fderiv ℝ c q ((1, 0) : ℝ × ℝ)) (s₀, τ)) := by
    filter_upwards [hslice.eventually hev3] with τ hτ
    exact (surfaceCovariantDerivS_fderivFst_eq_mixedPartialCoord (I := I) g α
      (hτ.of_le (by norm_num))).symm
  rw [covariantDerivCoord_congr_field (I := I) g α _ hfield]
  -- the `t`-slice covariant derivative of `D_s∂ₛc` *is* the surface operator `D_tD_s∂ₛc`
  rw [show covariantDerivCoord (I := I) g α (fun t => c (s₀, t))
        (fun τ => Jacobi.surfaceCovariantDerivS (I := I) g α c
          (fun q => fderiv ℝ c q ((1, 0) : ℝ × ℝ)) (s₀, τ)) t₀
      = Jacobi.surfaceCovariantDerivT (I := I) g α c
          (Jacobi.surfaceCovariantDerivS (I := I) g α c
            (fun q => fderiv ℝ c q ((1, 0) : ℝ × ℝ))) (s₀, t₀) from rfl]
  -- now trade `D_tD_s∂ₛc` for `D_sD_s∂ₜc` plus curvature
  have hid := covariantDerivCoord_mixedPartial_fst_eq_sub_chartCurvature (I := I) g α hc hmem
  rw [show Jacobi.surfaceCovariantDerivT (I := I) g α c
        (Jacobi.surfaceCovariantDerivS (I := I) g α c
          (fun q => fderiv ℝ c q ((1, 0) : ℝ × ℝ))) (s₀, t₀)
      = covariantDerivCoord (I := I) g α (fun s => c (s, t₀))
          (fun s => mixedPartialCoord (I := I) g α c (s, t₀)
            ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) s₀
        + Jacobi.chartCurvatureContraction2 (I := I) g α
            (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ))
            (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))
            (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ)) (c (s₀, t₀)) by rw [hid]; abel,
    chartMetricInner_add_left]

/-- **Math.** Petersen Thm. 6.1.4, **the integrand identity in Petersen's own curvature
tensor**.  At a point where the chart is centred at the foot, the identity of
`hasDerivAt_chartPairing_transversalAccel_of_geodesic` reads
$$\frac{\partial}{\partial t}g\Big(\frac{D}{\partial s}\frac{\partial c}{\partial s},
    \frac{\partial c}{\partial t}\Big)
  = g\Big(\frac{D}{\partial s}\frac{D}{\partial s}\frac{\partial c}{\partial t},
      \frac{\partial c}{\partial t}\Big)
    - g\Big(R\Big(\frac{\partial c}{\partial s},\frac{\partial c}{\partial t}\Big)
        \frac{\partial c}{\partial s}, \frac{\partial c}{\partial t}\Big),$$
with `R` Ch. 3's Koszul `curvatureTensorAt` — exactly the identity Petersen's proof of
Thm. 6.1.4 displays.

The sign flip against the chart-level form is `chartCurvatureContraction2 = −curvatureTensorAt`:
do Carmo's convention, which the coordinate commutator engine speaks, is the negative of
Petersen's.

The hypothesis `hbase` pins the chart centre to the foot.  This costs nothing here: the
statement is pointwise in `t`, so one reads the surface in the chart at the very point of
evaluation.

**`hbase` is a convenience, not a necessity.**  An earlier version of this note said it was
forced "because Ch. 3's coordinate curvature formula — and hence the bridge — is diagonal".
That is no longer true: see
`hasDerivAt_chartPairing_transversalAccel_of_geodesic_curvatureTensorAt_of_mem` in
`Ch06/SyngeAbstractCurvature.lean`, which replaces `hbase` by plain chart membership and so
survives an integral over `t` in one fixed chart. -/
theorem hasDerivAt_chartPairing_transversalAccel_of_geodesic_curvatureTensorAt
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t₀ : ℝ} (hc : ContDiffAt ℝ 3 c (s₀, t₀))
    (hbase : c (s₀, t₀) = extChartAt I α α)
    (hgeo : mixedPartialCoord (I := I) g α c (s₀, t₀)
      ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) = 0) :
    HasDerivAt (fun t : ℝ => chartMetricInner (I := I) g α (c (s₀, t))
        (mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
        (fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ)))
      (chartMetricInner (I := I) g α (c (s₀, t₀))
          (covariantDerivCoord (I := I) g α (fun s => c (s, t₀))
            (fun s => mixedPartialCoord (I := I) g α c (s, t₀)
              ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) s₀)
          (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))
        - chartMetricInner (I := I) g α (c (s₀, t₀))
            (curvatureTensorAt (g.leviCivita).toAffineConnection α
              (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ))
              (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))
              (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ)))
            (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))) t₀ := by
  have hmem : c (s₀, t₀) ∈ interior (extChartAt I α).target := by
    rw [hbase]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
      (mem_extChartAt_target (I := I) α)
  have h := hasDerivAt_chartPairing_transversalAccel_of_geodesic (I := I) g α hc hmem hgeo
  refine h.congr_deriv ?_
  rw [hbase, chartCurvatureContraction2_eq_neg_curvatureTensorAt (I := I) g α]
  rw [show ∀ a b : E, chartMetricInner (I := I) g α (extChartAt I α α) (-a) b
      = -chartMetricInner (I := I) g α (extChartAt I α α) a b from fun a b => by
    simpa using chartMetricInner_smul_left (I := I) g α (extChartAt I α α) (-1 : ℝ) a b]
  ring

/-! ### Theorem 6.1.4 itself

The integrand identity is a statement about a *single* `t`.  To integrate it over `[t₁,t₂]`
and apply the fundamental theorem of calculus one needs it at the **endpoints** too, and the
`E''` engine (`hasDerivAt_deriv_windowEnergy_chart`) only supplies `ContDiffOn` on the slab
`Ioo (-δ) δ ×ˢ Icc t₁ t₂`, which gives no `ContDiffAt` at `t = t₁, t₂`.  The fix is to
hypothesise smoothness on an **open** `t`-window `Ioo a b ⊇ Icc t₁ t₂`: the slab
`Ioo (-δ) δ ×ˢ Ioo a b` is then open, so `ContDiffAt` holds at *every* `(0,t)` with
`t ∈ Icc t₁ t₂`, while the engine's `Icc`-hypotheses follow by monotonicity.  The openness
pays a second dividend: all the `fderivWithin`/almost-everywhere gymnastics of
`Ch06/SecondVariation.lean` collapse, because on an open set `fderivWithin = fderiv`. -/

/-- **Math.** On an **open** subset of the chart target the coordinate mixed partial
`p ↦ ∂²c/∂v∂w (p)` is smooth whenever `c` is.

Both summands of `mixedPartialCoord` are: the pure second-derivative term
`fderiv (fderiv c · w) · v` is smooth because `fderiv` of a `C^∞` map on an open set is
again `C^∞` (`ContDiffOn.fderiv_of_isOpen` — the openness is what removes the
`fderivWithin`), and the Christoffel term is
`contDiffOn_chartChristoffelContraction_comp` applied to three smooth slots. -/
theorem contDiffOn_mixedPartialCoord_of_isOpen (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {S : Set (ℝ × ℝ)} (hS : IsOpen S) (hc : ContDiffOn ℝ ∞ c S)
    (hmem : ∀ p ∈ S, c p ∈ (extChartAt I α).target) (v w : ℝ × ℝ) :
    ContDiffOn ℝ ∞ (fun p => mixedPartialCoord (I := I) g α c p v w) S := by
  have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by simp
  have hFD : ContDiffOn ℝ ∞ (fderiv ℝ c) S := hc.fderiv_of_isOpen hS hle
  have hDv : ContDiffOn ℝ ∞ (fun p => fderiv ℝ c p v) S := hFD.clm_apply contDiffOn_const
  have hDw : ContDiffOn ℝ ∞ (fun p => fderiv ℝ c p w) S := hFD.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (fun q => fderiv ℝ c q w) p v) S :=
    (hDw.fderiv_of_isOpen hS hle).clm_apply contDiffOn_const
  simp only [mixedPartialCoord_def]
  exact h2.add
    (contDiffOn_chartChristoffelContraction_comp (I := I) g α le_rfl hc hDv hDw hmem)

/-- **Math.** The field `t ↦ D_s(∂²c/∂s∂t)|_{s₀}` — the first integrand of
`hasDerivAt_deriv_windowEnergy_chart` before pairing — is **continuous along the `s₀`-slice**.

`covariantDerivCoord g α u V s₀ = V̇(s₀) + Γ(u̇(s₀), V(s₀))(u(s₀))`, so along the slice it is
the restriction to the line `t ↦ (s₀,t)` of a function of *both* variables: the `s`-partial
`fderiv (∂²c/∂s∂t) p (1,0)` plus a Christoffel contraction.  On an open slab the first is
continuous by `contDiffOn_mixedPartialCoord_of_isOpen` followed by
`ContDiffOn.fderiv_of_isOpen`, and the second by
`continuousOn_chartChristoffelContraction_comp`; the slice map is continuous, so the
composite is. -/
theorem continuousOn_covariantDerivCoord_mixedPartial_slice (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {S : Set (ℝ × ℝ)} (hS : IsOpen S) (hc : ContDiffOn ℝ ∞ c S)
    (hmem : ∀ p ∈ S, c p ∈ (extChartAt I α).target) {s₀ : ℝ} {T : Set ℝ}
    (hT : ∀ t ∈ T, (s₀, t) ∈ S) :
    ContinuousOn (fun t : ℝ => covariantDerivCoord (I := I) g α (fun s => c (s, t))
      (fun s => mixedPartialCoord (I := I) g α c (s, t)
        ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) s₀) T := by
  classical
  have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by simp
  have hFD : ContDiffOn ℝ ∞ (fderiv ℝ c) S := hc.fderiv_of_isOpen hS hle
  have hDs : ContDiffOn ℝ ∞ (fun p => fderiv ℝ c p ((1, 0) : ℝ × ℝ)) S :=
    hFD.clm_apply contDiffOn_const
  have hM1 : ContDiffOn ℝ ∞
      (fun p => mixedPartialCoord (I := I) g α c p ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) S :=
    contDiffOn_mixedPartialCoord_of_isOpen (I := I) g α hS hc hmem _ _
  -- the two-variable field whose slice is the claim
  have hW : ContinuousOn (fun p =>
      fderiv ℝ (fun q => mixedPartialCoord (I := I) g α c q
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) p ((1, 0) : ℝ × ℝ)
        + Geodesic.chartChristoffelContraction (I := I) g α
            (fderiv ℝ c p ((1, 0) : ℝ × ℝ))
            (mixedPartialCoord (I := I) g α c p ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
            (c p)) S :=
    ((hM1.fderiv_of_isOpen hS hle).clm_apply contDiffOn_const).continuousOn.add
      (continuousOn_chartChristoffelContraction_comp (I := I) g α hc.continuousOn
        hDs.continuousOn hM1.continuousOn hmem)
  have hslice : ContinuousOn (fun t : ℝ => ((s₀, t) : ℝ × ℝ)) T :=
    (continuous_const.prodMk continuous_id).continuousOn
  refine (hW.comp hslice (fun t ht => hT t ht)).congr (fun t ht => ?_)
  have hp : (s₀, t) ∈ S := hT t ht
  have hcAt : ContDiffAt ℝ ∞ c (s₀, t) := hc.contDiffAt (hS.mem_nhds hp)
  have hu : HasDerivAt (fun s => c (s, t)) (fderiv ℝ c (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst
      (hcAt.differentiableAt (by simp)).hasFDerivAt
  have hV : HasDerivAt (fun s => mixedPartialCoord (I := I) g α c (s, t)
        ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
      (fderiv ℝ (fun q => mixedPartialCoord (I := I) g α c q
        ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) (s₀, t) ((1, 0) : ℝ × ℝ)) s₀ :=
    Jacobi.hasDerivAt_comp_fst
      (((hM1.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt)
  simp only [Function.comp_apply]
  rw [covariantDerivCoord_def, hu.deriv, hV.deriv]

/-- **Math.** **Petersen Theorem 6.1.4** (`thm:pet-ch6-synge-second-variation`, pp. 255–256),
**Synge's second variation of energy**, in chart form.  For a variation `c(s,t)` whose central
curve `t ↦ c(0,t)` is a geodesic,
$$\frac{d^2E}{ds^2}\Big|_{0}
  = \Big[\Big\langle \frac{D}{\partial s}\frac{\partial c}{\partial s},
      \frac{\partial c}{\partial t}\Big\rangle\Big]_{t_1}^{t_2}
    + \int_{t_1}^{t_2}\Big(\Big|\frac{D}{\partial s}\frac{\partial c}{\partial t}\Big|^2
      - \Big\langle R^{\text{chart}}\Big(\frac{\partial c}{\partial s},
          \frac{\partial c}{\partial t}\Big)\frac{\partial c}{\partial s},
        \frac{\partial c}{\partial t}\Big\rangle\Big)\,dt .$$

The smoothness window in `t` is the **open** interval `Ioo a b ⊇ Icc t₁ t₂`; this is not
cosmetic.  The `E''` engine hands back an integral over the closed window, and the
fundamental theorem of calculus needs the boundary term at `t₁` and `t₂` — so the pointwise
integrand identity must be available *at the endpoints*, which a `ContDiffOn` on
`… ×ˢ Icc t₁ t₂` never gives.  Widening to an open `t`-window costs nothing (`E''` is
unchanged, by `ContDiffOn.mono`) and supplies `ContDiffAt` at every `t ∈ [t₁,t₂]`.

The curvature is Petersen's, up to do Carmo's sign, and is phrased here in the chart because
that is what this proof directly produces.  For the same theorem with Ch. 3's abstract
`curvatureTensorAt` at the moving foot **under the integral** — the form the blueprint states
— see `secondVariationEnergy_chart_curvatureTensorAt` in `Ch06/SyngeAbstractCurvature.lean`.
(An earlier note here claimed the chart form was forced because the bridge is diagonal; that
ceased to be true once `Ch06/CurvatureChartBridgeMoving.lean` landed.)

**Proof.** `hasDerivAt_deriv_windowEnergy_chart` gives
`E''(0) = ∫ ⟨D_sD_s∂ₜc, ∂ₜc⟩ + |D_s∂ₜc|²`.  Adding and subtracting the curvature pairing
splits the integrand as `(⟨D_sD_s∂ₜc,∂ₜc⟩ + ⟨R,∂ₜc⟩) + (|D_s∂ₜc|² − ⟨R,∂ₜc⟩)`;
`hasDerivAt_chartPairing_transversalAccel_of_geodesic` identifies the first bracket as the
`t`-derivative of `⟨D_s∂ₛc, ∂ₜc⟩`, so the fundamental theorem of calculus turns its integral
into Petersen's boundary term.  All the integrability side conditions are continuity of the
chart composites, available because the slab is open. -/
theorem secondVariationEnergy_chart (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {δ a b t₁ t₂ : ℝ} (hδ : 0 < δ) (h12 : t₁ < t₂)
    (hsub : Icc t₁ t₂ ⊆ Ioo a b)
    (hc : ContDiffOn ℝ ∞ c (Ioo (-δ) δ ×ˢ Ioo a b))
    (hmem : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b, c p ∈ (extChartAt I α).target)
    (hgeo : ∀ t ∈ Icc t₁ t₂,
      mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) = 0) :
    deriv (deriv (fun s : ℝ => ∫ t in t₁..t₂, (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t))) 0
      = chartMetricInner (I := I) g α (c (0, t₂))
          (mixedPartialCoord (I := I) g α c (0, t₂) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
          (fderiv ℝ c (0, t₂) ((0, 1) : ℝ × ℝ))
        - chartMetricInner (I := I) g α (c (0, t₁))
            (mixedPartialCoord (I := I) g α c (0, t₁) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
            (fderiv ℝ c (0, t₁) ((0, 1) : ℝ × ℝ))
        + ∫ t in t₁..t₂, (chartMetricInner (I := I) g α (c (0, t))
              (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
              (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
            - chartMetricInner (I := I) g α (c (0, t))
                (Jacobi.chartCurvatureContraction2 (I := I) g α
                  (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ))
                  (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
                  (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (c (0, t)))
                (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))) := by
  classical
  set S : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Ioo a b with hSdef
  have hSopen : IsOpen S := isOpen_Ioo.prod isOpen_Ioo
  have hline : ∀ t ∈ Icc t₁ t₂, ((0 : ℝ), t) ∈ S :=
    fun t ht => ⟨⟨neg_lt_zero.mpr hδ, hδ⟩, hsub ht⟩
  have hmemT : ∀ t ∈ Icc t₁ t₂, c (0, t) ∈ (extChartAt I α).target :=
    fun t ht => hmem _ (hline t ht)
  have hint : ∀ t ∈ Icc t₁ t₂, c (0, t) ∈ interior (extChartAt I α).target := fun t ht =>
    extChartAt_target_subset_interior_of_boundaryless (I := I) α (hmemT t ht)
  -- STEP 1: the `E''` engine, on the closed sub-slab
  have hE := (hasDerivAt_deriv_windowEnergy_chart (I := I) g α hδ h12
    (hc.mono (Set.prod_mono subset_rfl hsub))
    (fun p hp => hmem p ⟨hp.1, hsub hp.2⟩)).deriv
  rw [hE]
  -- continuity toolkit along the central line
  have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by simp
  have hslice : ContinuousOn (fun t : ℝ => ((0 : ℝ), t)) (Icc t₁ t₂) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hcont_c : ContinuousOn (fun t : ℝ => c (0, t)) (Icc t₁ t₂) :=
    hc.continuousOn.comp hslice hline
  have hFD : ContDiffOn ℝ ∞ (fderiv ℝ c) S := hc.fderiv_of_isOpen hSopen hle
  have hcont_d : ∀ w : ℝ × ℝ, ContinuousOn (fun t : ℝ => fderiv ℝ c (0, t) w) (Icc t₁ t₂) :=
    fun w => (hFD.clm_apply contDiffOn_const).continuousOn.comp hslice hline
  have hcont_MP : ∀ v w : ℝ × ℝ,
      ContinuousOn (fun t : ℝ => mixedPartialCoord (I := I) g α c (0, t) v w) (Icc t₁ t₂) :=
    fun v w => (contDiffOn_mixedPartialCoord_of_isOpen (I := I) g α hSopen hc hmem v
      w).continuousOn.comp hslice hline
  have hcont_cov := continuousOn_covariantDerivCoord_mixedPartial_slice (I := I) g α hSopen hc
    hmem (s₀ := (0 : ℝ)) (T := Icc t₁ t₂) hline
  -- the three integrands: `A` (the engine's first), `B` (the engine's second), `K` (curvature)
  have hA : ContinuousOn (fun t : ℝ => chartMetricInner (I := I) g α (c (0, t))
      (covariantDerivCoord (I := I) g α (fun s => c (s, t))
        (fun s => mixedPartialCoord (I := I) g α c (s, t)
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) 0)
      (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))) (Icc t₁ t₂) :=
    continuousOn_chartMetricInner_comp (I := I) g α hcont_c hcont_cov
      (hcont_d ((0, 1) : ℝ × ℝ)) hmemT
  have hB : ContinuousOn (fun t : ℝ => chartMetricInner (I := I) g α (c (0, t))
      (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
      (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)))
      (Icc t₁ t₂) :=
    continuousOn_chartMetricInner_comp (I := I) g α hcont_c
      (hcont_MP ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
      (hcont_MP ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) hmemT
  have hK : ContinuousOn (fun t : ℝ => chartMetricInner (I := I) g α (c (0, t))
      (Jacobi.chartCurvatureContraction2 (I := I) g α
        (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (c (0, t)))
      (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))) (Icc t₁ t₂) :=
    continuousOn_chartMetricInner_comp (I := I) g α hcont_c
      (continuousOn_chartCurvatureContraction2_comp (I := I) g α hcont_c
        (hcont_d ((1, 0) : ℝ × ℝ)) (hcont_d ((0, 1) : ℝ × ℝ))
        (hcont_d ((1, 0) : ℝ × ℝ)) hmemT)
      (hcont_d ((0, 1) : ℝ × ℝ)) hmemT
  -- the two halves of the split integrand, in `fun`-form, and their integrability
  have hAK : ContinuousOn (fun t : ℝ => chartMetricInner (I := I) g α (c (0, t))
        (covariantDerivCoord (I := I) g α (fun s => c (s, t))
          (fun s => mixedPartialCoord (I := I) g α c (s, t)
            ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) 0)
        (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
      + chartMetricInner (I := I) g α (c (0, t))
          (Jacobi.chartCurvatureContraction2 (I := I) g α
            (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
            (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (c (0, t)))
          (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))) (Icc t₁ t₂) := hA.add hK
  have hAK_int := hAK.intervalIntegrable_of_Icc (μ := volume) h12.le
  have hBK_int := (hB.sub hK).intervalIntegrable_of_Icc (μ := volume) h12.le
  -- STEP 2: the fundamental theorem of calculus on the exact part
  have hFTC : (∫ t in t₁..t₂, (chartMetricInner (I := I) g α (c (0, t))
        (covariantDerivCoord (I := I) g α (fun s => c (s, t))
          (fun s => mixedPartialCoord (I := I) g α c (s, t)
            ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) 0)
        (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
      + chartMetricInner (I := I) g α (c (0, t))
          (Jacobi.chartCurvatureContraction2 (I := I) g α
            (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
            (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (c (0, t)))
          (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))))
      = chartMetricInner (I := I) g α (c (0, t₂))
          (mixedPartialCoord (I := I) g α c (0, t₂) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
          (fderiv ℝ c (0, t₂) ((0, 1) : ℝ × ℝ))
        - chartMetricInner (I := I) g α (c (0, t₁))
            (mixedPartialCoord (I := I) g α c (0, t₁) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
            (fderiv ℝ c (0, t₁) ((0, 1) : ℝ × ℝ)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => chartMetricInner (I := I) g α (c (0, t))
        (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
        (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)))
      (fun t ht => ?_) hAK_int
    rw [Set.uIcc_of_le h12.le] at ht
    exact hasDerivAt_chartPairing_transversalAccel_of_geodesic (I := I) g α
      ((hc.contDiffAt (hSopen.mem_nhds (hline t ht))).of_le (by norm_cast))
      (hint t ht) (hgeo t ht)
  -- STEP 3: split the engine's integrand and substitute
  rw [show (∫ t in t₁..t₂, (chartMetricInner (I := I) g α (c (0, t))
        (covariantDerivCoord (I := I) g α (fun s => c (s, t))
          (fun s => mixedPartialCoord (I := I) g α c (s, t)
            ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) 0)
        (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
      + chartMetricInner (I := I) g α (c (0, t))
          (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
          (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))))
      = ∫ t in t₁..t₂, ((chartMetricInner (I := I) g α (c (0, t))
            (covariantDerivCoord (I := I) g α (fun s => c (s, t))
              (fun s => mixedPartialCoord (I := I) g α c (s, t)
                ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) 0)
            (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
          + chartMetricInner (I := I) g α (c (0, t))
              (Jacobi.chartCurvatureContraction2 (I := I) g α
                (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
                (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (c (0, t)))
              (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)))
        + (chartMetricInner (I := I) g α (c (0, t))
              (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
              (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
            - chartMetricInner (I := I) g α (c (0, t))
                (Jacobi.chartCurvatureContraction2 (I := I) g α
                  (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
                  (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (c (0, t)))
                (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)))) from
    intervalIntegral.integral_congr (fun t _ => by ring)]
  have hsplit := intervalIntegral.integral_add hAK_int hBK_int
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit, hFTC]

end PetersenLib

end
