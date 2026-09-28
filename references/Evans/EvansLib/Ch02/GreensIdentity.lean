import EvansLib.Ch02.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Evans, Ch. 2 §2.2 — Integration by parts in coordinate form

Groundwork for the mean-value property `thm:mean-value-formulas-laplace`, the one step of
§2.2 that `MeanValue.lean` still takes as a hypothesis
(`HasBallMeanValueProperty`) rather than deriving from harmonicity.

## Why this file exists

Evans proves the mean-value formula from Green's identity on a ball, i.e. from the
divergence theorem. Mathlib has no divergence theorem on a ball — its
`MeasureTheory.Integral.DivergenceTheorem` is stated for *boxes* (`Set.Icc` products), and
its only harmonic mean-value theorem (`HarmonicOnNhd.circleAverage_eq`) is complex-analytic
and so lives in dimension 2 only. Neither reaches Evans' setting.

The route taken here avoids surface measure entirely. Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` is a *line-derivative* integration by
parts valid on any finite-dimensional real normed space carrying a Haar measure, with no
box, no order structure and no boundary term — the boundary term is killed by integrability
rather than by a surface integral. Notably it is proved from the one-dimensional statement
by a Fubini argument and imports neither `DivergenceTheorem` nor `BoxIntegral`, so building
on it does not smuggle in the very theorem mathlib lacks.

Applying it in direction `eᵢ = EuclideanSpace.single i 1` reproduces integration by parts
for EvansLib's `partialDeriv`, because `partialDeriv i f x` is *definitionally*
`fderiv ℝ f x (EuclideanSpace.single i 1)` (`Ch01.Multiindex`, where `partialDeriv_apply`
is `rfl`). The mathlib lemma therefore accepts `partialDeriv` clothing as a bare term, with
no `unfold`/`show`/`simp` massaging.

## Main results

* `integral_mul_partialDeriv_eq_neg` — `∫ f · ∂ᵢg = -∫ (∂ᵢf) · g`.
* `integral_mul_partialDeriv_iterate_two_comm` — `∫ f · ∂ᵢ²g = ∫ (∂ᵢ²f) · g`: two
  applications of the above move both derivatives off `g` and onto `f`, the two sign flips
  cancelling.
* `integral_mul_laplacian_eq_integral_laplacian_mul` — Green's second identity
  `∫ u · Δw = ∫ (Δu) · w` when the smooth compactly supported test function `w`
  is supported where `u` is `C²`.
* `integral_mul_laplacian_eq_zero_of_harmonicOnNhd` — the resulting weak identity
  `∫ u · Δw = 0` for harmonic `u`.

The weak identity is the analytic input for the squared-radius radial test functions used next
toward the ball mean-value property.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.2.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- **Integration by parts, one coordinate.** `∫ f · ∂ᵢg = -∫ (∂ᵢf) · g`.

This is mathlib's line-derivative integration by parts in the direction `eᵢ`. The
hypotheses are exactly mathlib's: the three products are integrable, and each factor is
differentiable on the *other* factor's `tsupport` — no compact support and no
differentiability is required of either function on its own. -/
theorem integral_mul_partialDeriv_eq_neg (i : Fin n)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf'g : Integrable (fun y ↦ partialDeriv i f y * g y) volume)
    (hfg' : Integrable (fun y ↦ f y * partialDeriv i g y) volume)
    (hfg : Integrable (fun y ↦ f y * g y) volume)
    (hf : ∀ y ∈ tsupport g, DifferentiableAt ℝ f y)
    (hg : ∀ y ∈ tsupport f, DifferentiableAt ℝ g y) :
    ∫ y, f y * partialDeriv i g y = -∫ y, partialDeriv i f y * g y :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := EuclideanSpace.single i 1) hf'g hfg' hfg hf hg

/-- **Both derivatives move across.** `∫ f · ∂ᵢ²g = ∫ (∂ᵢ²f) · g`.

Two applications of `integral_mul_partialDeriv_eq_neg`: the first moves one `∂ᵢ` off `g`
onto `f`, the second moves the remaining one, and the two sign flips cancel. Only eight
side conditions are needed rather than ten — the second application's "`f · ∂ᵢg`
integrable" slot is literally `a1`, already supplied for the first. -/
theorem integral_mul_partialDeriv_iterate_two_comm (i : Fin n)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (a1 : Integrable (fun y ↦ partialDeriv i f y * partialDeriv i g y) volume)
    (a2 : Integrable (fun y ↦ f y * partialDeriv i (partialDeriv i g) y) volume)
    (a3 : Integrable (fun y ↦ f y * partialDeriv i g y) volume)
    (a4 : ∀ y ∈ tsupport (partialDeriv i g), DifferentiableAt ℝ f y)
    (a5 : ∀ y ∈ tsupport f, DifferentiableAt ℝ (partialDeriv i g) y)
    (b1 : Integrable (fun y ↦ partialDeriv i (partialDeriv i f) y * g y) volume)
    (b3 : Integrable (fun y ↦ partialDeriv i f y * g y) volume)
    (b4 : ∀ y ∈ tsupport g, DifferentiableAt ℝ (partialDeriv i f) y)
    (b5 : ∀ y ∈ tsupport (partialDeriv i f), DifferentiableAt ℝ g y) :
    ∫ y, f y * (partialDeriv i)^[2] g y = ∫ y, (partialDeriv i)^[2] f y * g y := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  rw [integral_mul_partialDeriv_eq_neg i a1 a2 a3 a4 a5,
    integral_mul_partialDeriv_eq_neg i b1 a1 b3 b4 b5, neg_neg]

/-! ## Compact-support infrastructure -/

/-- Taking a partial derivative does not enlarge topological support.  Outside
`tsupport f`, the function is identically zero on a neighborhood, so its Fréchet
derivative (and hence every coordinate derivative) vanishes there. -/
lemma tsupport_partialDeriv_subset (i : Fin n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    tsupport (partialDeriv i f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxf
  have hzero : f =ᶠ[nhds x] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxf] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  apply hx
  rw [partialDeriv_apply, hzero.fderiv_eq]
  simp

/-- A product is globally continuous when its first factor is continuous on an
open set containing the topological support of its globally continuous second
factor.  On the complementary open set the product is identically zero. -/
lemma continuous_mul_of_continuousOn_of_tsupport_subset
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : Continuous g)
    (hgU : tsupport g ⊆ U) :
    Continuous (fun x ↦ f x * g x) := by
  apply continuousOn_univ.mp
  have hcover : U ∪ (tsupport g)ᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ tsupport g
    · exact Or.inl (hgU hx)
    · exact Or.inr hx
  rw [← hcover]
  apply ContinuousOn.union_of_isOpen (hf.mul hg.continuousOn)
  · refine (continuousOn_const : ContinuousOn
      (fun _ : EuclideanSpace ℝ (Fin n) ↦ (0 : ℝ)) (tsupport g)ᶜ).congr ?_
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  · exact hU
  · exact (isClosed_tsupport g).isOpen_compl

/-- The continuous product from
`continuous_mul_of_continuousOn_of_tsupport_subset` is integrable when its
second factor has compact support. -/
lemma integrable_mul_of_continuousOn_of_tsupport_subset
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    Integrable (fun x ↦ f x * g x) volume := by
  have hcont := continuous_mul_of_continuousOn_of_tsupport_subset hU hf hg hgU
  change Integrable (f * g) volume
  exact hcont.integrable_of_hasCompactSupport hgc.mul_left

/-! ## Coordinate Green identity with compactly supported test functions -/

/-- Two coordinate derivatives can be moved from a smooth compactly supported
test function `w` onto a function `u` which is only `C²` on an open
neighborhood of `tsupport w`.  All integrability and differentiability side
conditions of `integral_mul_partialDeriv_iterate_two_comm` are discharged from
these geometric hypotheses. -/
theorem integral_mul_partialDeriv_iterate_two_comm_of_tsupport (i : Fin n)
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hw : ContDiff ℝ ∞ w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    ∫ y, u y * (partialDeriv i)^[2] w y =
      ∫ y, (partialDeriv i)^[2] u y * w y := by
  have hwi : ContDiff ℝ ∞ (partialDeriv i w) := partialDeriv_contDiff hw i
  have hwii : ContDiff ℝ ∞ (partialDeriv i (partialDeriv i w)) :=
    partialDeriv_contDiff hwi i
  have hui : ContDiffOn ℝ 1 (partialDeriv i u) U := by
    exact ((hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const)
  have huii : ContinuousOn (partialDeriv i (partialDeriv i u)) U := by
    exact (((hui.fderiv_of_isOpen hU (m := 0) (by norm_num)).clm_apply
      contDiffOn_const).continuousOn)
  have hwiU : tsupport (partialDeriv i w) ⊆ U :=
    (tsupport_partialDeriv_subset i).trans hwU
  have hwiiU : tsupport (partialDeriv i (partialDeriv i w)) ⊆ U :=
    (tsupport_partialDeriv_subset i).trans hwiU
  have hwic : HasCompactSupport (partialDeriv i w) :=
    hwc.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialDeriv_subset i)
  have hwiic : HasCompactSupport (partialDeriv i (partialDeriv i w)) :=
    hwic.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialDeriv_subset i)
  apply integral_mul_partialDeriv_iterate_two_comm i
  · exact integrable_mul_of_continuousOn_of_tsupport_subset hU hui.continuousOn
      hwi.continuous hwic hwiU
  · exact integrable_mul_of_continuousOn_of_tsupport_subset hU hu.continuousOn
      hwii.continuous hwiic hwiiU
  · exact integrable_mul_of_continuousOn_of_tsupport_subset hU hu.continuousOn
      hwi.continuous hwic hwiU
  · intro y hy
    exact (hu y (hwiU hy)).contDiffAt (hU.mem_nhds (hwiU hy)) |>.differentiableAt
      (by norm_num)
  · intro y _
    exact hwi.differentiable (by norm_num) y
  · exact integrable_mul_of_continuousOn_of_tsupport_subset hU huii
      hw.continuous hwc hwU
  · exact integrable_mul_of_continuousOn_of_tsupport_subset hU hui.continuousOn
      hw.continuous hwc hwU
  · intro y hy
    exact (hui y (hwU hy)).contDiffAt (hU.mem_nhds (hwU hy)) |>.differentiableAt
      (by norm_num)
  · intro y _
    exact hw.differentiable (by norm_num) y

/-- **Green's second identity in coordinate form.**  Sum the preceding
one-coordinate identities over the standard basis. -/
theorem integral_mul_sum_partialDeriv_iterate_two_comm_of_tsupport
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hw : ContDiff ℝ ∞ w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    ∫ y, u y * ∑ i, (partialDeriv i)^[2] w y =
      ∫ y, (∑ i, (partialDeriv i)^[2] u y) * w y := by
  classical
  have hleft (i : Fin n) :
      Integrable (fun y ↦ u y * (partialDeriv i)^[2] w y) volume := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    have hwi := partialDeriv_contDiff hw i
    have hwii := partialDeriv_contDiff hwi i
    have hwiU : tsupport (partialDeriv i w) ⊆ U :=
      (tsupport_partialDeriv_subset i).trans hwU
    have hwiiU : tsupport (partialDeriv i (partialDeriv i w)) ⊆ U :=
      (tsupport_partialDeriv_subset i).trans hwiU
    have hwic : HasCompactSupport (partialDeriv i w) :=
      hwc.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialDeriv_subset i)
    have hwiic : HasCompactSupport (partialDeriv i (partialDeriv i w)) :=
      hwic.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialDeriv_subset i)
    exact integrable_mul_of_continuousOn_of_tsupport_subset hU hu.continuousOn
      hwii.continuous hwiic hwiiU
  have hright (i : Fin n) :
      Integrable (fun y ↦ (partialDeriv i)^[2] u y * w y) volume := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    have hui : ContDiffOn ℝ 1 (partialDeriv i u) U := by
      exact ((hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const)
    have huii : ContinuousOn (partialDeriv i (partialDeriv i u)) U := by
      exact (((hui.fderiv_of_isOpen hU (m := 0) (by norm_num)).clm_apply
        contDiffOn_const).continuousOn)
    exact integrable_mul_of_continuousOn_of_tsupport_subset hU huii
      hw.continuous hwc hwU
  calc
    ∫ y, u y * ∑ i, (partialDeriv i)^[2] w y =
        ∫ y, ∑ i, u y * (partialDeriv i)^[2] w y := by simp only [Finset.mul_sum]
    _ = ∑ i, ∫ y, u y * (partialDeriv i)^[2] w y := by
      exact integral_finsetSum Finset.univ (fun i _ ↦ hleft i)
    _ = ∑ i, ∫ y, (partialDeriv i)^[2] u y * w y := by
      exact Finset.sum_congr rfl fun i _ ↦
        integral_mul_partialDeriv_iterate_two_comm_of_tsupport i hU hu hw hwc hwU
    _ = ∫ y, ∑ i, (partialDeriv i)^[2] u y * w y := by
      exact (integral_finsetSum Finset.univ (fun i _ ↦ hright i)).symm
    _ = ∫ y, (∑ i, (partialDeriv i)^[2] u y) * w y := by
      simp only [Finset.sum_mul]

/-- **Green's second identity for compactly supported test functions.**  If `u`
is `C²` on an open neighborhood of the support of a smooth compactly supported
test function `w`, then
`\int u Δw = \int (Δu) w`.

Unlike the boundary form of Green's identity, this statement needs no surface
measure or divergence theorem: it follows by coordinate integration by parts
on the whole Euclidean space. -/
theorem integral_mul_laplacian_eq_integral_laplacian_mul
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hw : ContDiff ℝ ∞ w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    ∫ y, u y * Δ w y = ∫ y, Δ u y * w y := by
  calc
    ∫ y, u y * Δ w y = ∫ y, u y * ∑ i, (partialDeriv i)^[2] w y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [laplacian_eq_sum_partialDeriv_iterate_two
        (hw.contDiffAt.of_le (WithTop.coe_le_coe.mpr
          (show (2 : ℕ∞) ≤ ⊤ from le_top)))]
    _ = ∫ y, (∑ i, (partialDeriv i)^[2] u y) * w y :=
      integral_mul_sum_partialDeriv_iterate_two_comm_of_tsupport hU hu hw hwc hwU
    _ = ∫ y, Δ u y * w y := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ tsupport w
      · have huy : ContDiffAt ℝ 2 u y :=
          (hu y (hwU hy)).contDiffAt (hU.mem_nhds (hwU hy))
        rw [← laplacian_eq_sum_partialDeriv_iterate_two huy]
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]

/-- A harmonic function annihilates the Laplacian of every smooth compactly
supported test function whose support lies in its harmonicity domain.  This is
the weak Green identity used by the radial-test-function route to the ball
mean-value property. -/
theorem integral_mul_laplacian_eq_zero_of_harmonicOnNhd
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : IsOpen U) (hu : HarmonicOnNhd u U) (hw : ContDiff ℝ ∞ w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    ∫ y, u y * Δ w y = 0 := by
  rw [integral_mul_laplacian_eq_integral_laplacian_mul hU hu.contDiffOn hw hwc hwU]
  calc
    ∫ y, Δ u y * w y =
        ∫ _ : EuclideanSpace ℝ (Fin n), (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ tsupport w
      · have hlu : Δ u y = 0 := by
          simpa using (hu y (hwU hy)).2.eq_of_nhds
        rw [hlu, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    _ = 0 := by simp

end EvansLib
