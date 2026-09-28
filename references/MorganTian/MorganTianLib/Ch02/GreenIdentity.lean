import MorganTianLib.Ch01.LaplacianDivergence
import MorganTianLib.Ch01.RiemannianMeasure
import MorganTianLib.Ch02.TraceCommutation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Morgan--Tian Ch. 2 -- Green's identity for compactly supported tests

This file proves the compact-support Green identity for the Riemannian
Laplacian.  The local analytic input is integration by parts along the fixed
coordinate basis of the model space; a smooth partition of unity then reduces
the manifold statement to test functions supported in one chart.
-/

open MeasureTheory Set Filter Matrix Riemannian Riemannian.Tensor
open scoped ContDiff Manifold Topology Bundle Matrix

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ## Coordinate integration by parts -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Math.** A coordinate derivative does not enlarge topological support. -/
lemma tsupport_partialDeriv_subset (a : Fin (Module.finrank ℝ E))
    {f : E → ℝ} :
    tsupport (partialDeriv (E := E) a f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxf
  have hzero : f =ᶠ[nhds x] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxf] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  apply hx
  unfold partialDeriv
  rw [hzero.fderiv_eq]
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Math.** Multiplication by a globally smooth function supported in `U` extends a
function smooth only on the open set `U` to a globally smooth product. -/
lemma contDiff_mul_of_contDiffOn_of_tsupport_subset
    {U : Set E} {f g : E → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiff ℝ ∞ g) (hgU : tsupport g ⊆ U) :
    ContDiff ℝ ∞ (fun x ↦ f x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact ((hf x hx).contDiffAt (hU.mem_nhds hx)).mul hg.contDiffAt
  · have hxg : x ∉ tsupport g := fun hxg ↦ hx (hgU hxg)
    have hzero : (fun y ↦ f y * g y) =ᶠ[nhds x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hxg] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

omit [FiniteDimensional ℝ E] in
/-- **Math.** The preceding product is integrable when the supported factor has compact
support. -/
lemma integrable_mul_of_contDiffOn_of_compactSupport
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {U : Set E} {f g : E → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) :
    Integrable (fun x ↦ f x * g x) mu := by
  have hcont := contDiff_mul_of_contDiffOn_of_tsupport_subset hU hf hg hgU
  change Integrable (f * g) mu
  exact hcont.continuous.integrable_of_hasCompactSupport hgc.mul_left

/-- **Math.** Integration by parts in the coordinate direction selected by the fixed
finite-dimensional basis. -/
theorem integral_mul_partialDeriv_eq_neg (mu : Measure E) [mu.IsAddHaarMeasure]
    (a : Fin (Module.finrank ℝ E)) {f g : E → ℝ}
    (hf'g : Integrable (fun y ↦ partialDeriv (E := E) a f y * g y) mu)
    (hfg' : Integrable (fun y ↦ f y * partialDeriv (E := E) a g y) mu)
    (hfg : Integrable (fun y ↦ f y * g y) mu)
    (hf : ∀ y ∈ tsupport g, DifferentiableAt ℝ f y)
    (hg : ∀ y ∈ tsupport f, DifferentiableAt ℝ g y) :
    ∫ y, f y * partialDeriv (E := E) a g y ∂mu =
      -∫ y, partialDeriv (E := E) a f y * g y ∂mu :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := (Module.finBasis ℝ E) a) hf'g hfg' hfg hf hg

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Math.** A coordinate derivative of a smooth function is smooth. -/
lemma contDiff_partialDeriv (a : Fin (Module.finrank ℝ E))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (partialDeriv (E := E) a f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Math.** A coordinate derivative preserves smoothness on an open set. -/
lemma contDiffOn_partialDeriv (a : Fin (Module.finrank ℝ E))
    {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) a f) U := by
  exact ((hf.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply contDiffOn_const)

/-- **Math.** The coordinate flux with coefficient matrix `q`:
`F_a(v) = Σ_b q_ab ∂_b v`. -/
def coordinateFlux (q : Fin (Module.finrank ℝ E) →
    Fin (Module.finrank ℝ E) → E → ℝ) (v : E → ℝ)
    (a : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ b, q a b y * partialDeriv (E := E) b v y

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Math.** A chart-local coefficient times a globally smooth supported test
function gives a globally smooth coordinate flux. -/
lemma contDiff_coordinateFlux_of_compactSupport
    {U : Set E} (hU : IsOpen U)
    {q : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ}
    (hq : ∀ a b, ContDiffOn ℝ ∞ (q a b) U)
    {w : E → ℝ} (hw : ContDiff ℝ ∞ w) (hwU : tsupport w ⊆ U)
    (a : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (coordinateFlux q w a) := by
  unfold coordinateFlux
  exact ContDiff.sum fun b _ ↦
    contDiff_mul_of_contDiffOn_of_tsupport_subset hU (hq a b)
      (contDiff_partialDeriv b hw) ((tsupport_partialDeriv_subset b).trans hwU)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Math.** The coordinate flux of `w` has topological support contained in
the topological support of `w`. -/
lemma tsupport_coordinateFlux_subset
    (q : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ)
    (w : E → ℝ) (a : Fin (Module.finrank ℝ E)) :
    tsupport (coordinateFlux q w a) ⊆ tsupport w := by
  apply closure_minimal _ (isClosed_tsupport w)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxw
  apply hx
  unfold coordinateFlux
  apply Finset.sum_eq_zero
  intro b _
  have hxb : x ∉ tsupport (partialDeriv (E := E) b w) :=
    fun hxb ↦ hxw (tsupport_partialDeriv_subset b hxb)
  rw [image_eq_zero_of_notMem_tsupport hxb, mul_zero]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Math.** A coordinate flux is smooth on an open set when its coefficients
and input function are smooth there. -/
lemma contDiffOn_coordinateFlux
    {U : Set E}
    {q : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ}
    (hq : ∀ a b, ContDiffOn ℝ ∞ (q a b) U)
    {v : E → ℝ} (hv : ContDiffOn ℝ ∞ v U)
    (hU : IsOpen U) (a : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (coordinateFlux q v a) U := by
  unfold coordinateFlux
  exact ContDiffOn.sum fun b _ ↦
    (hq a b).mul (contDiffOn_partialDeriv b hU hv)

/-- **Math.** The inverse-Gram Green pairing is symmetric in coordinate form.
This is the local analytic heart of Green's identity. -/
theorem integral_mul_coordinateDivergence_comm
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {U : Set E} (hU : IsOpen U)
    {q : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ}
    (hq : ∀ a b, ContDiffOn ℝ ∞ (q a b) U)
    (hqsymm : ∀ y ∈ U, ∀ a b, q a b y = q b a y)
    {u w : E → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ U) :
    ∫ y, u y * ∑ a, partialDeriv (E := E) a (coordinateFlux q w a) y ∂mu =
      ∫ y, w y * ∑ a, partialDeriv (E := E) a (coordinateFlux q u a) y ∂mu := by
  classical
  have hFw (a : Fin (Module.finrank ℝ E)) :
      ContDiff ℝ ∞ (coordinateFlux q w a) :=
    contDiff_coordinateFlux_of_compactSupport hU hq hw hwU a
  have hFwU (a : Fin (Module.finrank ℝ E)) :
      tsupport (coordinateFlux q w a) ⊆ U :=
    (tsupport_coordinateFlux_subset q w a).trans hwU
  have hFwc (a : Fin (Module.finrank ℝ E)) :
      HasCompactSupport (coordinateFlux q w a) :=
    hwc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_coordinateFlux_subset q w a)
  have hdFw (a : Fin (Module.finrank ℝ E)) :
      ContDiff ℝ ∞ (partialDeriv (E := E) a (coordinateFlux q w a)) :=
    contDiff_partialDeriv a (hFw a)
  have hdFwU (a : Fin (Module.finrank ℝ E)) :
      tsupport (partialDeriv (E := E) a (coordinateFlux q w a)) ⊆ U :=
    (tsupport_partialDeriv_subset a).trans (hFwU a)
  have hdFwc (a : Fin (Module.finrank ℝ E)) :
      HasCompactSupport (partialDeriv (E := E) a (coordinateFlux q w a)) :=
    (hFwc a).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_partialDeriv_subset a)
  have hdu (a : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞ (partialDeriv (E := E) a u) U :=
    contDiffOn_partialDeriv a hU hu
  have hdw (a : Fin (Module.finrank ℝ E)) :
      ContDiff ℝ ∞ (partialDeriv (E := E) a w) :=
    contDiff_partialDeriv a hw
  have hdwU (a : Fin (Module.finrank ℝ E)) :
      tsupport (partialDeriv (E := E) a w) ⊆ U :=
    (tsupport_partialDeriv_subset a).trans hwU
  have hdwc (a : Fin (Module.finrank ℝ E)) :
      HasCompactSupport (partialDeriv (E := E) a w) :=
    hwc.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialDeriv_subset a)
  have hFu (a : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞ (coordinateFlux q u a) U :=
    contDiffOn_coordinateFlux hq hu hU a
  have hdFu (a : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞ (partialDeriv (E := E) a (coordinateFlux q u a)) U :=
    contDiffOn_partialDeriv a hU (hFu a)

  have hInt_du_Fw (a : Fin (Module.finrank ℝ E)) :
      Integrable (fun y ↦ partialDeriv (E := E) a u y * coordinateFlux q w a y) mu :=
    integrable_mul_of_contDiffOn_of_compactSupport mu hU (hdu a) (hFw a)
      (hFwc a) (hFwU a)
  have hInt_u_dFw (a : Fin (Module.finrank ℝ E)) :
      Integrable (fun y ↦ u y * partialDeriv (E := E) a (coordinateFlux q w a) y) mu :=
    integrable_mul_of_contDiffOn_of_compactSupport mu hU hu (hdFw a)
      (hdFwc a) (hdFwU a)
  have hInt_u_Fw (a : Fin (Module.finrank ℝ E)) :
      Integrable (fun y ↦ u y * coordinateFlux q w a y) mu :=
    integrable_mul_of_contDiffOn_of_compactSupport mu hU hu (hFw a)
      (hFwc a) (hFwU a)
  have hInt_dw_Fu (a : Fin (Module.finrank ℝ E)) :
      Integrable (fun y ↦ partialDeriv (E := E) a w y * coordinateFlux q u a y) mu := by
    simpa only [mul_comm] using
      integrable_mul_of_contDiffOn_of_compactSupport mu hU (hFu a) (hdw a)
        (hdwc a) (hdwU a)
  have hInt_w_dFu (a : Fin (Module.finrank ℝ E)) :
      Integrable (fun y ↦ w y * partialDeriv (E := E) a (coordinateFlux q u a) y) mu := by
    simpa only [mul_comm] using
      integrable_mul_of_contDiffOn_of_compactSupport mu hU (hdFu a) hw hwc hwU
  have hInt_w_Fu (a : Fin (Module.finrank ℝ E)) :
      Integrable (fun y ↦ w y * coordinateFlux q u a y) mu := by
    simpa only [mul_comm] using
      integrable_mul_of_contDiffOn_of_compactSupport mu hU (hFu a) hw hwc hwU

  have hleft (a : Fin (Module.finrank ℝ E)) :
      (∫ y, u y * partialDeriv (E := E) a (coordinateFlux q w a) y ∂mu) =
        -∫ y, partialDeriv (E := E) a u y * coordinateFlux q w a y ∂mu := by
    apply integral_mul_partialDeriv_eq_neg mu a
    · exact hInt_du_Fw a
    · exact hInt_u_dFw a
    · exact hInt_u_Fw a
    · intro y hy
      exact ((hu y (hFwU a hy)).contDiffAt (hU.mem_nhds (hFwU a hy))).differentiableAt
        (by simp)
    · intro y _
      exact (hFw a).differentiable (by simp) y
  have hright (a : Fin (Module.finrank ℝ E)) :
      (∫ y, w y * partialDeriv (E := E) a (coordinateFlux q u a) y ∂mu) =
        -∫ y, partialDeriv (E := E) a w y * coordinateFlux q u a y ∂mu := by
    apply integral_mul_partialDeriv_eq_neg mu a
    · exact hInt_dw_Fu a
    · exact hInt_w_dFu a
    · exact hInt_w_Fu a
    · intro y _
      exact hw.differentiable (by simp) y
    · intro y hy
      exact ((hFu a y (hwU hy)).contDiffAt (hU.mem_nhds (hwU hy))).differentiableAt
        (by simp)

  have hpair : (fun y ↦ ∑ a, partialDeriv (E := E) a u y * coordinateFlux q w a y) =
      fun y ↦ ∑ a, partialDeriv (E := E) a w y * coordinateFlux q u a y := by
    funext y
    by_cases hy : y ∈ U
    · unfold coordinateFlux
      calc
        ∑ a, partialDeriv (E := E) a u y *
              ∑ b, q a b y * partialDeriv (E := E) b w y =
            ∑ a, ∑ b, partialDeriv (E := E) a u y * q a b y *
              partialDeriv (E := E) b w y := by
                apply Finset.sum_congr rfl
                intro a _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro b _
                ring
        _ = ∑ b, ∑ a, partialDeriv (E := E) a u y * q a b y *
              partialDeriv (E := E) b w y := Finset.sum_comm
        _ = ∑ b, ∑ a, partialDeriv (E := E) b w y * q b a y *
              partialDeriv (E := E) a u y := by
                apply Finset.sum_congr rfl
                intro b _
                apply Finset.sum_congr rfl
                intro a _
                rw [hqsymm y hy a b]
                ring
        _ = ∑ b, partialDeriv (E := E) b w y *
              ∑ a, q b a y * partialDeriv (E := E) a u y := by
                apply Finset.sum_congr rfl
                intro b _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro a _
                ring
    · have hzero : ∀ a, partialDeriv (E := E) a w y = 0 := by
        intro a
        have hya : y ∉ tsupport (partialDeriv (E := E) a w) :=
          fun hya ↦ hy (hdwU a hya)
        exact image_eq_zero_of_notMem_tsupport hya
      simp only [coordinateFlux, hzero, mul_zero, Finset.sum_const_zero,
        zero_mul]

  calc
    ∫ y, u y * ∑ a, partialDeriv (E := E) a (coordinateFlux q w a) y ∂mu =
        ∫ y, ∑ a, u y * partialDeriv (E := E) a (coordinateFlux q w a) y ∂mu := by
          congr 1
          funext y
          rw [Finset.mul_sum]
    _ = ∑ a, ∫ y, u y * partialDeriv (E := E) a (coordinateFlux q w a) y ∂mu :=
      integral_finsetSum Finset.univ (fun a _ ↦ hInt_u_dFw a)
    _ = ∑ a, -∫ y, partialDeriv (E := E) a u y * coordinateFlux q w a y ∂mu :=
      Finset.sum_congr rfl fun a _ ↦ hleft a
    _ = -∑ a, ∫ y, partialDeriv (E := E) a u y * coordinateFlux q w a y ∂mu := by
      rw [Finset.sum_neg_distrib]
    _ = -∫ y, ∑ a, partialDeriv (E := E) a u y * coordinateFlux q w a y ∂mu := by
      rw [integral_finsetSum Finset.univ (fun a _ ↦ hInt_du_Fw a)]
    _ = -∫ y, ∑ a, partialDeriv (E := E) a w y * coordinateFlux q u a y ∂mu := by
      rw [hpair]
    _ = -∑ a, ∫ y, partialDeriv (E := E) a w y * coordinateFlux q u a y ∂mu := by
      rw [integral_finsetSum Finset.univ (fun a _ ↦ hInt_dw_Fu a)]
    _ = ∑ a, -∫ y, partialDeriv (E := E) a w y * coordinateFlux q u a y ∂mu := by
      rw [Finset.sum_neg_distrib]
    _ = ∑ a, ∫ y, w y * partialDeriv (E := E) a (coordinateFlux q u a) y ∂mu :=
      Finset.sum_congr rfl fun a _ ↦ (hright a).symm
    _ = ∫ y, ∑ a, w y * partialDeriv (E := E) a (coordinateFlux q u a) y ∂mu :=
      (integral_finsetSum Finset.univ (fun a _ ↦ hInt_w_dFu a)).symm
    _ = ∫ y, w y * ∑ a, partialDeriv (E := E) a (coordinateFlux q u a) y ∂mu := by
      congr 1
      funext y
      rw [Finset.mul_sum]

/-- **Math.** Skew form of the coordinate Green identity: the integral of
`u div(q grad w) - w div(q grad u)` vanishes. -/
theorem integral_coordinateGreen_eq_zero
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {U : Set E} (hU : IsOpen U)
    {q : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ}
    (hq : ∀ a b, ContDiffOn ℝ ∞ (q a b) U)
    (hqsymm : ∀ y ∈ U, ∀ a b, q a b y = q b a y)
    {u w : E → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ U) :
    ∫ y, (u y * ∑ a, partialDeriv (E := E) a (coordinateFlux q w a) y) -
      w y * ∑ a, partialDeriv (E := E) a (coordinateFlux q u a) y ∂mu = 0 := by
  classical
  have hFw (a : Fin (Module.finrank ℝ E)) :
      ContDiff ℝ ∞ (coordinateFlux q w a) :=
    contDiff_coordinateFlux_of_compactSupport hU hq hw hwU a
  have hFwU (a : Fin (Module.finrank ℝ E)) :
      tsupport (coordinateFlux q w a) ⊆ U :=
    (tsupport_coordinateFlux_subset q w a).trans hwU
  have hFwc (a : Fin (Module.finrank ℝ E)) :
      HasCompactSupport (coordinateFlux q w a) :=
    hwc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_coordinateFlux_subset q w a)
  have hdFw (a : Fin (Module.finrank ℝ E)) :
      ContDiff ℝ ∞ (partialDeriv (E := E) a (coordinateFlux q w a)) :=
    contDiff_partialDeriv a (hFw a)
  have hdFwU (a : Fin (Module.finrank ℝ E)) :
      tsupport (partialDeriv (E := E) a (coordinateFlux q w a)) ⊆ U :=
    (tsupport_partialDeriv_subset a).trans (hFwU a)
  have hdFwc (a : Fin (Module.finrank ℝ E)) :
      HasCompactSupport (partialDeriv (E := E) a (coordinateFlux q w a)) :=
    (hFwc a).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_partialDeriv_subset a)
  have hFu (a : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞ (coordinateFlux q u a) U :=
    contDiffOn_coordinateFlux hq hu hU a
  have hdFu (a : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞ (partialDeriv (E := E) a (coordinateFlux q u a)) U :=
    contDiffOn_partialDeriv a hU (hFu a)
  have hIntA (a : Fin (Module.finrank ℝ E)) : Integrable
      (fun y ↦ u y * partialDeriv (E := E) a (coordinateFlux q w a) y) mu :=
    integrable_mul_of_contDiffOn_of_compactSupport mu hU hu (hdFw a)
      (hdFwc a) (hdFwU a)
  have hIntB (a : Fin (Module.finrank ℝ E)) : Integrable
      (fun y ↦ w y * partialDeriv (E := E) a (coordinateFlux q u a) y) mu := by
    simpa only [mul_comm] using
      integrable_mul_of_contDiffOn_of_compactSupport mu hU (hdFu a) hw hwc hwU
  have hA : Integrable
      (fun y ↦ u y * ∑ a, partialDeriv (E := E) a (coordinateFlux q w a) y) mu := by
    simpa only [Finset.mul_sum] using
      integrable_finsetSum Finset.univ (fun a _ ↦ hIntA a)
  have hB : Integrable
      (fun y ↦ w y * ∑ a, partialDeriv (E := E) a (coordinateFlux q u a) y) mu := by
    simpa only [Finset.mul_sum] using
      integrable_finsetSum Finset.univ (fun a _ ↦ hIntB a)
  rw [integral_sub hA hB,
    integral_mul_coordinateDivergence_comm mu hU hq hqsymm hu hw hwc hwU,
    sub_self]

/-! ## Compactly supported chart pullbacks -/

variable {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NeZero (Module.finrank ℝ V)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- **Math.** Pull a function back through a chart inverse on the chart target
and extend it by zero to the whole model space. -/
def chartPullback (a : M) (f : M → ℝ) : V → ℝ :=
  let U : TopologicalSpace.Opens V :=
    ⟨(extChartAt I a).target, isOpen_extChartAt_target (I := I) a⟩
  Function.extend Subtype.val
    (fun y : U ↦ f ((extChartAt I a).symm y)) 0

omit [FiniteDimensional ℝ V] [NeZero (Module.finrank ℝ V)]
  [IsManifold I ∞ M] [T2Space M] in
@[simp] theorem chartPullback_apply (a : M) (f : M → ℝ) {y : V}
    (hy : y ∈ (extChartAt I a).target) :
    chartPullback (I := I) a f y = f ((extChartAt I a).symm y) := by
  let U : TopologicalSpace.Opens V :=
    ⟨(extChartAt I a).target, isOpen_extChartAt_target (I := I) a⟩
  change Function.extend Subtype.val
    (fun z : U ↦ f ((extChartAt I a).symm z)) 0 y = _
  exact Function.Injective.extend_apply Subtype.val_injective _ _ ⟨y, hy⟩

omit [FiniteDimensional ℝ V] [NeZero (Module.finrank ℝ V)]
  [IsManifold I ∞ M] [T2Space M] in
@[simp] theorem chartPullback_eq_zero (a : M) (f : M → ℝ) {y : V}
    (hy : y ∉ (extChartAt I a).target) :
    chartPullback (I := I) a f y = 0 := by
  let U : TopologicalSpace.Opens V :=
    ⟨(extChartAt I a).target, isOpen_extChartAt_target (I := I) a⟩
  change Function.extend Subtype.val
    (fun z : U ↦ f ((extChartAt I a).symm z)) 0 y = 0
  exact Function.extend_val_apply' hy

omit [FiniteDimensional ℝ V] [NeZero (Module.finrank ℝ V)]
  [IsManifold I ∞ M] [I.Boundaryless] in
/-- **Math.** Compact support strictly inside the chart source remains compact
after transport to the chart-target subtype. -/
lemma hasCompactSupport_chartTarget (a : M) {f : M → ℝ}
    (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ (extChartAt I a).source) :
    HasCompactSupport
      (fun y : (extChartAt I a).target ↦ f ((extChartAt I a).symm y)) := by
  let e := extChartAt I a
  let fS : e.source → ℝ := fun x ↦ f x
  let K : Set e.source := {x | (x : M) ∈ tsupport f}
  have hKimg : Subtype.val '' K = tsupport f := by
    apply Set.Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact hz
    · intro x hx
      exact ⟨⟨x, hfU hx⟩, hx, rfl⟩
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff, hKimg]
    exact hfc.isCompact
  have hfSc : HasCompactSupport fS := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro x hx
    exact subset_closure hx
  let home : e.source ≃ₜ e.target :=
    { toEquiv := e.toEquiv
      continuous_toFun := (continuousOn_extChartAt (I := I) a).restrict.subtype_mk _
      continuous_invFun :=
        (continuousOn_extChartAt_symm (I := I) a).restrict.subtype_mk _ }
  have hfTc := hfSc.comp_homeomorph home.symm
  have heq : (fun y : e.target ↦ f (e.symm y)) = fS ∘ home.symm := rfl
  rw [heq]
  exact hfTc

omit [FiniteDimensional ℝ V] [NeZero (Module.finrank ℝ V)] [T2Space M] in
/-- **Math.** The chart-target restriction of a smooth manifold function is
smooth as a function on the open model-space subtype. -/
lemma contMDiff_chartTarget (a : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    let U : TopologicalSpace.Opens V :=
      ⟨(extChartAt I a).target, isOpen_extChartAt_target (I := I) a⟩
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℝ) ∞
      (fun y : U ↦ f ((extChartAt I a).symm y)) := by
  dsimp only
  let U : TopologicalSpace.Opens V :=
    ⟨(extChartAt I a).target, isOpen_extChartAt_target (I := I) a⟩
  change ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℝ) ∞
    (fun y : U ↦ f ((extChartAt I a).symm y))
  intro y
  change ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, ℝ) ∞
    (fun y : U ↦ (f ∘ (extChartAt I a).symm) y) y
  rw [contMDiffAt_subtype_iff]
  exact (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm a) y y.property).contMDiffAt
    ((isOpen_extChartAt_target (I := I) a).mem_nhds y.property)

omit [FiniteDimensional ℝ V] [NeZero (Module.finrank ℝ V)] in
/-- **Math.** The zero-extended chart pullback of a smooth compactly supported
function supported in the chart source is globally smooth. -/
theorem contDiff_chartPullback (a : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ (extChartAt I a).source) :
    ContDiff ℝ ∞ (chartPullback (I := I) a f) := by
  let U : TopologicalSpace.Opens V :=
    ⟨(extChartAt I a).target, isOpen_extChartAt_target (I := I) a⟩
  change ContDiff ℝ ∞ (Function.extend Subtype.val
    (fun y : U ↦ f ((extChartAt I a).symm y)) 0)
  exact (ContMDiff.extend_zero (hasCompactSupport_chartTarget a hfc hfU)
    (contMDiff_chartTarget a hf)).contDiff

omit [FiniteDimensional ℝ V] [NeZero (Module.finrank ℝ V)]
  [IsManifold I ∞ M] in
/-- **Math.** The zero-extended chart pullback has compact support. -/
theorem hasCompactSupport_chartPullback (a : M) {f : M → ℝ}
    (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ (extChartAt I a).source) :
    HasCompactSupport (chartPullback (I := I) a f) := by
  let U : TopologicalSpace.Opens V :=
    ⟨(extChartAt I a).target, isOpen_extChartAt_target (I := I) a⟩
  change HasCompactSupport (Function.extend Subtype.val
    (fun y : U ↦ f ((extChartAt I a).symm y)) 0)
  exact (hasCompactSupport_chartTarget a hfc hfU).extend_zero continuous_subtype_val

omit [FiniteDimensional ℝ V] [NeZero (Module.finrank ℝ V)]
  [IsManifold I ∞ M] in
/-- **Math.** The zero-extended chart pullback is supported in the chart target. -/
theorem tsupport_chartPullback_subset (a : M) {f : M → ℝ}
    (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ (extChartAt I a).source) :
    tsupport (chartPullback (I := I) a f) ⊆ (extChartAt I a).target := by
  let U : TopologicalSpace.Opens V :=
    ⟨(extChartAt I a).target, isOpen_extChartAt_target (I := I) a⟩
  change tsupport (Function.extend Subtype.val
    (fun y : U ↦ f ((extChartAt I a).symm y)) 0) ⊆ _
  refine ((hasCompactSupport_chartTarget a hfc hfU).tsupport_extend_zero_subset
    continuous_subtype_val).trans ?_
  rintro _ ⟨y, _, rfl⟩
  exact y.property

/-! ## The chart density and inverse metric -/

omit [NeZero (Module.finrank ℝ V)] [I.Boundaryless] [T2Space M] in
/-- **Math.** The Riemannian chart volume density is smooth on the chart target. -/
theorem contDiffOn_chartVolumeDensity (g : RiemannianMetric I M) (a : M) :
    ContDiffOn ℝ ∞ (chartVolumeDensity (I := I) g a)
      (extChartAt I a).target := by
  have hmat : ContDiffOn ℝ ∞
      (fun y : V ↦ (fun i j ↦ chartGramOnE (I := I) g a i j y))
      (extChartAt I a).target := by
    rw [contDiffOn_pi]
    intro i
    rw [contDiffOn_pi]
    intro j
    exact chartGramOnE_contDiffOn (I := I) g a i j
  have hdet : ContDiffOn ℝ ∞
      (fun y : V ↦ Matrix.det (fun i j ↦ chartGramOnE (I := I) g a i j y))
      (extChartAt I a).target :=
    (contDiff_det.of_le (show (∞ : WithTop ℕ∞) ≤ ⊤ from le_top)).contDiffOn.comp
      hmat (fun _ _ ↦ mem_univ _)
  change ContDiffOn ℝ ∞
    (fun y : V ↦ Real.sqrt (Matrix.det (fun i j ↦
      chartGramOnE (I := I) g a i j y))) (extChartAt I a).target
  refine hdet.sqrt ?_
  intro y hy
  change (Riemannian.Tensor.chartGramMatrix (I := I) g a
    ((extChartAt I a).symm y)).det ≠ 0
  exact ne_of_gt (chartGramMatrix_det_pos (I := I) g a (by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I a).map_target hy))

omit [NeZero (Module.finrank ℝ V)] [I.Boundaryless] [T2Space M] in
/-- **Math.** The inverse chart Gram matrix is symmetric on the chart target. -/
theorem chartInvGramOnE_symm (g : RiemannianMetric I M) (a : M)
    {y : V} (hy : y ∈ (extChartAt I a).target)
    (i j : Fin (Module.finrank ℝ V)) :
    chartInvGramOnE (I := I) g a i j y =
      chartInvGramOnE (I := I) g a j i y := by
  have hx : (extChartAt I a).symm y ∈
      (trivializationAt V (TangentSpace I) a).baseSet := by
    have hs : (extChartAt I a).symm y ∈ (extChartAt I a).source :=
      (extChartAt I a).map_target hy
    rw [extChartAt_source] at hs
    exact hs
  have hpos : (chartGramMatrix (I := I) g a
      ((extChartAt I a).symm y)).PosDef :=
    chartGramMatrix_posDef (I := I) g a hx
  have hinv : (chartInvGramMatrix (I := I) g a
      ((extChartAt I a).symm y)).PosDef := by
    have := hpos.inv
    rwa [chartInvGramMatrix]
  simpa only [chartInvGramOnE_def, star_trivial] using
    hinv.isHermitian.apply j i

/-- **Math.** The coefficient `sqrt(det g) g^{ij}` in the coordinate
divergence form of the Laplacian. -/
def greenChartCoeff (g : RiemannianMetric I M) (a : M)
    (i j : Fin (Module.finrank ℝ V)) (y : V) : ℝ :=
  chartInvGramOnE (I := I) g a i j y * chartVolumeDensity (I := I) g a y

omit [NeZero (Module.finrank ℝ V)] [I.Boundaryless] [T2Space M] in
/-- **Math.** The weighted inverse-metric coefficients are smooth on the chart target. -/
theorem contDiffOn_greenChartCoeff (g : RiemannianMetric I M) (a : M)
    (i j : Fin (Module.finrank ℝ V)) :
    ContDiffOn ℝ ∞ (greenChartCoeff (I := I) g a i j)
      (extChartAt I a).target :=
  (chartInvGramOnE_contDiffOn (I := I) g a i j).mul
    (contDiffOn_chartVolumeDensity g a)

omit [NeZero (Module.finrank ℝ V)] [I.Boundaryless] [T2Space M] in
/-- **Math.** The weighted inverse-metric coefficient matrix is symmetric. -/
theorem greenChartCoeff_symm (g : RiemannianMetric I M) (a : M)
    {y : V} (hy : y ∈ (extChartAt I a).target)
    (i j : Fin (Module.finrank ℝ V)) :
    greenChartCoeff (I := I) g a i j y = greenChartCoeff (I := I) g a j i y := by
  unfold greenChartCoeff
  rw [chartInvGramOnE_symm g a hy i j]

/-- **Math.** Multiplying the chart formula for the Laplacian by the volume
density gives the coordinate divergence of `sqrt(det g) g^{-1} df`. -/
theorem chartVolumeDensity_mul_laplacianAt_eq_divergence
    [SigmaCompactSpace M]
    (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (a : M)
    {y : V} (hy : y ∈ (extChartAt I a).target) :
    chartVolumeDensity (I := I) g a y *
        laplacianAt g g.leviCivitaConnection f ((extChartAt I a).symm y) =
      ∑ i, partialDeriv (E := V) i
        (coordinateFlux (greenChartCoeff (I := I) g a)
          (f ∘ (extChartAt I a).symm) i) y := by
  have hp : (extChartAt I a).symm y ∈ (chartAt H a).source := by
    rw [← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I a).map_target hy
  have hdpos : 0 < chartVolumeDensity (I := I) g a y := by
    exact Real.sqrt_pos.mpr (chartGramMatrix_det_pos (I := I) g a (by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hp))
  have h := laplacianAt_eq_chart_divergence g hf hp
  rw [(extChartAt I a).right_inv hy] at h
  change laplacianAt g g.leviCivitaConnection f ((extChartAt I a).symm y) =
    (chartVolumeDensity (I := I) g a y)⁻¹ *
      ∑ i, partialDeriv (E := V) i
        (coordinateFlux (greenChartCoeff (I := I) g a)
          (f ∘ (extChartAt I a).symm) i) y at h
  rw [h, ← mul_assoc, mul_inv_cancel₀
    (ne_of_gt hdpos), one_mul]

omit [NeZero (Module.finrank ℝ V)] [IsManifold I ∞ M] [T2Space M] in
/-- **Math.** Inside a chart target, replacing a chart pullback by its
zero-extension does not change the coordinate divergence. -/
theorem coordinateDivergence_chartPullback_eq
    (q : Fin (Module.finrank ℝ V) → Fin (Module.finrank ℝ V) → V → ℝ)
    (a : M) (f : M → ℝ) {y : V} (hy : y ∈ (extChartAt I a).target) :
    ∑ i, partialDeriv (E := V) i
        (coordinateFlux q (chartPullback (I := I) a f) i) y =
      ∑ i, partialDeriv (E := V) i
        (coordinateFlux q (f ∘ (extChartAt I a).symm) i) y := by
  classical
  have hpartial (z : V) (hz : z ∈ (extChartAt I a).target)
      (j : Fin (Module.finrank ℝ V)) :
      partialDeriv (E := V) j (chartPullback (I := I) a f) z =
        partialDeriv (E := V) j (f ∘ (extChartAt I a).symm) z := by
    have heq : chartPullback (I := I) a f =ᶠ[nhds z]
        f ∘ (extChartAt I a).symm := by
      filter_upwards [(isOpen_extChartAt_target (I := I) a).mem_nhds hz] with w hw
      exact chartPullback_apply a f hw
    unfold partialDeriv
    rw [heq.fderiv_eq]
  apply Finset.sum_congr rfl
  intro i _
  have hflux : coordinateFlux q (chartPullback (I := I) a f) i =ᶠ[nhds y]
      coordinateFlux q (f ∘ (extChartAt I a).symm) i := by
    filter_upwards [(isOpen_extChartAt_target (I := I) a).mem_nhds hy] with z hz
    unfold coordinateFlux
    apply Finset.sum_congr rfl
    intro j _
    rw [hpartial z hz j]
  unfold partialDeriv
  rw [hflux.fderiv_eq]

/-! ## Integrating in one chart -/

omit [T2Space M] in
/-- **Math.** On a chart source, the global Riemannian measure agrees with the
measure obtained directly from that chart. -/
theorem restrict_riemannianMeasure_eq_restrict_chartMeasure
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (mu : Measure V) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (a : M) :
    (riemannianMeasure (I := I) g mu).restrict (extChartAt I a).source =
      (chartMeasure (I := I) g mu a).restrict (extChartAt I a).source := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  have ht : MeasurableSet (s ∩ (extChartAt I a).source) :=
    hs.inter (isOpen_extChartAt_source (I := I) a).measurableSet
  rw [riemannianMeasure_apply_chart mu g a ht inter_subset_right,
    chartMeasure_apply mu g a ht]

omit [T2Space M] in
/-- **Math.** A compactly supported integral whose support lies in one chart is
the Haar integral of its zero-extended chart pullback times `sqrt(det g)`. -/
theorem integral_riemannianMeasure_eq_integral_chartPullback
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (mu : Measure V) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (a : M) {F : M → ℝ}
    (hF : Continuous F)
    (hFU : tsupport F ⊆ (extChartAt I a).source) :
    (∫ x, F x ∂(riemannianMeasure (I := I) g mu)) =
      ∫ y, chartVolumeDensity (I := I) g a y * chartPullback (I := I) a F y ∂mu := by
  have htarget : MeasurableSet (extChartAt I a).target :=
    (isOpen_extChartAt_target (I := I) a).measurableSet
  have hzero : ∀ x ∈ (Set.univ : Set M) \ (extChartAt I a).source, F x = 0 := by
    intro x hx
    by_contra hne
    exact hx.2 (hFU (subset_closure hne))
  have hrestrict (nu : Measure M) :
      (∫ x, F x ∂nu) = ∫ x in (extChartAt I a).source, F x ∂nu := by
    simpa only [Measure.restrict_univ, setIntegral_univ] using
      (MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (s := (extChartAt I a).source) (t := Set.univ) MeasurableSet.univ
        (subset_univ _) hzero (μ := nu))
  calc
    (∫ x, F x ∂(riemannianMeasure (I := I) g mu)) =
        ∫ x in (extChartAt I a).source, F x
          ∂(riemannianMeasure (I := I) g mu) := hrestrict _
    _ = ∫ x in (extChartAt I a).source, F x
          ∂(chartMeasure (I := I) g mu a) := by
        rw [restrict_riemannianMeasure_eq_restrict_chartMeasure mu g a]
    _ = ∫ x, F x ∂(chartMeasure (I := I) g mu a) := (hrestrict _).symm
    _ = ∫ y, F ((extChartAt I a).symm y)
          ∂((mu.restrict (extChartAt I a).target).withDensity
            (fun y ↦ ENNReal.ofReal (chartVolumeDensity (I := I) g a y))) := by
        have hae : AEMeasurable (extChartAt I a).symm
            (mu.restrict (extChartAt I a).target) :=
          (continuousOn_extChartAt_symm (I := I) a).aemeasurable htarget
        have hae' : AEMeasurable (extChartAt I a).symm
            ((mu.restrict (extChartAt I a).target).withDensity
              (fun y ↦ ENNReal.ofReal (chartVolumeDensity (I := I) g a y))) :=
          hae.mono' (withDensity_absolutelyContinuous _ _)
        rw [chartMeasure, integral_map hae'
          hF.stronglyMeasurable.aestronglyMeasurable]
    _ = ∫ y in (extChartAt I a).target,
          chartVolumeDensity (I := I) g a y * F ((extChartAt I a).symm y) ∂mu := by
        have hdens : AEMeasurable
            (fun y ↦ ENNReal.ofReal (chartVolumeDensity (I := I) g a y))
            (mu.restrict (extChartAt I a).target) :=
          (ENNReal.continuous_ofReal.comp_continuousOn
            (contDiffOn_chartVolumeDensity g a).continuousOn).aemeasurable htarget
        rw [integral_withDensity_eq_integral_toReal_smul₀ hdens (by simp)]
        change (∫ y in (extChartAt I a).target,
          (ENNReal.ofReal (chartVolumeDensity (I := I) g a y)).toReal •
            F ((extChartAt I a).symm y) ∂mu) = _
        apply MeasureTheory.setIntegral_congr_fun htarget
        intro y _
        change (ENNReal.ofReal (chartVolumeDensity (I := I) g a y)).toReal *
          F ((extChartAt I a).symm y) =
            chartVolumeDensity (I := I) g a y * F ((extChartAt I a).symm y)
        rw [ENNReal.toReal_ofReal (chartVolumeDensity_nonneg g a y)]
    _ = ∫ y in (extChartAt I a).target,
          chartVolumeDensity (I := I) g a y * chartPullback (I := I) a F y ∂mu := by
        apply MeasureTheory.setIntegral_congr_fun htarget
        intro y hy
        change chartVolumeDensity (I := I) g a y * F ((extChartAt I a).symm y) =
          chartVolumeDensity (I := I) g a y * chartPullback (I := I) a F y
        rw [chartPullback_apply a F hy]
    _ = ∫ y, chartVolumeDensity (I := I) g a y *
          chartPullback (I := I) a F y ∂mu := by
        symm
        have h := MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (f := fun y ↦ chartVolumeDensity (I := I) g a y *
            chartPullback (I := I) a F y)
          (s := (extChartAt I a).target) (t := Set.univ) (μ := mu)
          MeasurableSet.univ (subset_univ _) (fun y hy ↦ by
            change chartVolumeDensity (I := I) g a y *
              chartPullback (I := I) a F y = 0
            rw [chartPullback_eq_zero a F hy.2, mul_zero])
        simpa only [setIntegral_univ] using h

/-- **Math.** A smooth compactly supported function supported in one chart is
integrable for the Riemannian measure. -/
theorem integrable_riemannianMeasure_of_tsupport_subset_chart
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (mu : Measure V) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (a : M) {F : M → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F) (hFc : HasCompactSupport F)
    (hFa : tsupport F ⊆ (extChartAt I a).source) :
    Integrable F (riemannianMeasure (I := I) g mu) := by
  have htarget : MeasurableSet (extChartAt I a).target :=
    (isOpen_extChartAt_target (I := I) a).measurableSet
  have hFp : ContDiff ℝ ∞ (chartPullback (I := I) a F) :=
    contDiff_chartPullback a hF hFc hFa
  have hFpc : HasCompactSupport (chartPullback (I := I) a F) :=
    hasCompactSupport_chartPullback a hFc hFa
  have hFpU : tsupport (chartPullback (I := I) a F) ⊆
      (extChartAt I a).target :=
    tsupport_chartPullback_subset a hFc hFa
  have hcoord : Integrable (fun y ↦ chartVolumeDensity (I := I) g a y *
      chartPullback (I := I) a F y) mu := by
    have hcont := contDiff_mul_of_contDiffOn_of_tsupport_subset
      (isOpen_extChartAt_target (I := I) a)
      (contDiffOn_chartVolumeDensity g a) hFp hFpU
    exact hcont.continuous.integrable_of_hasCompactSupport hFpc.mul_left
  have hdens : AEMeasurable
      (fun y ↦ ENNReal.ofReal (chartVolumeDensity (I := I) g a y))
      (mu.restrict (extChartAt I a).target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (contDiffOn_chartVolumeDensity g a).continuousOn).aemeasurable htarget
  have hweighted : Integrable
      (fun y ↦
        (ENNReal.ofReal (chartVolumeDensity (I := I) g a y)).toReal •
          F ((extChartAt I a).symm y))
      (mu.restrict (extChartAt I a).target) := by
    apply hcoord.restrict.congr
    filter_upwards [ae_restrict_mem htarget] with y hy
    rw [ENNReal.toReal_ofReal (chartVolumeDensity_nonneg g a y),
      chartPullback_apply a F hy]
    rfl
  have hcomp : Integrable (F ∘ (extChartAt I a).symm)
      ((mu.restrict (extChartAt I a).target).withDensity
        (fun y ↦ ENNReal.ofReal (chartVolumeDensity (I := I) g a y))) :=
    (integrable_withDensity_iff_integrable_smul₀' hdens (by simp)).2 hweighted
  have hae : AEMeasurable (extChartAt I a).symm
      (mu.restrict (extChartAt I a).target) :=
    (continuousOn_extChartAt_symm (I := I) a).aemeasurable htarget
  have hae' : AEMeasurable (extChartAt I a).symm
      ((mu.restrict (extChartAt I a).target).withDensity
        (fun y ↦ ENNReal.ofReal (chartVolumeDensity (I := I) g a y))) :=
    hae.mono' (withDensity_absolutelyContinuous _ _)
  have hchart : Integrable F (chartMeasure (I := I) g mu a) := by
    rw [chartMeasure]
    exact (integrable_map_measure
      hF.continuous.stronglyMeasurable.aestronglyMeasurable hae').2 hcomp
  rw [← integrableOn_iff_integrable_of_support_subset
    ((subset_tsupport F).trans hFa)]
  change Integrable F
    ((riemannianMeasure (I := I) g mu).restrict (extChartAt I a).source)
  rw [restrict_riemannianMeasure_eq_restrict_chartMeasure mu g a]
  exact hchart.restrict

omit [FiniteDimensional ℝ V] [NeZero (Module.finrank ℝ V)]
  [I.Boundaryless] [T2Space M] in
/-- **Math.** The Hessian is linear in a finite sum of smooth functions. -/
theorem hessian_finsetSum_function (nabla : AffineConnection I M)
    [SigmaCompactSpace M]
    {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i))
    (X Y : SmoothVectorField I M) (p : M) :
    hessian nabla (fun q ↦ ∑ i ∈ s, f i q) X Y p =
      ∑ i ∈ s, hessian nabla (f i) X Y p := by
  classical
  have hY : Y.dir (fun q ↦ ∑ i ∈ s, f i q) =
      fun q ↦ ∑ i ∈ s, Y.dir (f i) q :=
    funext fun q ↦ dir_sum Y hf q
  have hYsmooth : ∀ i ∈ s,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (Y.dir (f i)) :=
    fun i hi ↦ Y.dir_contMDiff (hf i hi)
  unfold hessian
  rw [hY, dir_sum X hYsmooth p, dir_sum (nabla.cov X Y) hf p,
    Finset.sum_sub_distrib]

omit [NeZero (Module.finrank ℝ V)] [I.Boundaryless] in
/-- **Math.** The Laplacian is linear in a finite sum of smooth functions. -/
theorem laplacianAt_finsetSum_function
    [SigmaCompactSpace M]
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i)) (p : M) :
    laplacianAt g nabla (fun q ↦ ∑ i ∈ s, f i q) p =
      ∑ i ∈ s, laplacianAt g nabla (f i) p := by
  classical
  unfold laplacianAt hessianAt
  simp_rw [hessian_finsetSum_function nabla s hf]
  rw [Finset.sum_comm]

omit [NeZero (Module.finrank ℝ V)] [I.Boundaryless] in
/-- **Math.** The Laplacian of the zero function vanishes. -/
theorem laplacianAt_zero [SigmaCompactSpace M] (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) :
    laplacianAt g nabla (fun _ ↦ (0 : ℝ)) p = 0 := by
  have hdir_zero (X : SmoothVectorField I M) (q : M) :
      X.dir (fun _ ↦ (0 : ℝ)) q = 0 := by
    show mfderiv I 𝓘(ℝ, ℝ) (fun _ ↦ (0 : ℝ)) q (X q) = 0
    rw [mfderiv_const]
    rfl
  have hhessian_zero (X Y : SmoothVectorField I M) (q : M) :
      hessian nabla (fun _ ↦ (0 : ℝ)) X Y q = 0 := by
    unfold hessian
    have hY : Y.dir (fun _ ↦ (0 : ℝ)) = fun _ ↦ 0 :=
      funext fun r ↦ hdir_zero Y r
    rw [hY, hdir_zero X q, hdir_zero (nabla.cov X Y) q, sub_zero]
  unfold laplacianAt hessianAt
  exact Finset.sum_eq_zero fun i _ ↦ hhessian_zero _ _ p

omit [NeZero (Module.finrank ℝ V)] [I.Boundaryless] in
/-- **Math.** The Laplacian is germ-local, so it does not enlarge
topological support. -/
theorem tsupport_laplacianAt_subset [SigmaCompactSpace M]
    (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (f : M → ℝ) :
    tsupport (laplacianAt g nabla f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxf
  have hzero : f =ᶠ[nhds x] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxf] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  apply hx
  rw [laplacianAt_congr_of_eventuallyEq g nabla hzero,
    laplacianAt_zero g nabla x]

omit [NeZero (Module.finrank ℝ V)] [I.Boundaryless] in
/-- **Math.** The Green integrand is supported where its test-function
argument is supported. -/
theorem tsupport_greenIntegrand_subset [SigmaCompactSpace M]
    (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (u ψ : M → ℝ) :
    tsupport (fun x ↦ u x * laplacianAt g nabla ψ x -
      ψ x * laplacianAt g nabla u x) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxψ
  have hxΔψ : x ∉ tsupport (laplacianAt g nabla ψ) :=
    fun hxΔψ ↦ hxψ (tsupport_laplacianAt_subset g nabla ψ hxΔψ)
  apply hx
  rw [image_eq_zero_of_notMem_tsupport hxΔψ,
    image_eq_zero_of_notMem_tsupport hxψ]
  ring

/-- **Math.** Green's identity for a test function whose compact support lies
in one chart source. -/
theorem green_identity_of_tsupport_subset_chart
    [CompleteSpace V] [SigmaCompactSpace M]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (mu : Measure V) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (a : M) {u ψ : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ)
    (hψc : HasCompactSupport ψ)
    (hψa : tsupport ψ ⊆ (extChartAt I a).source) :
    ∫ x, (u x * laplacianAt g g.leviCivitaConnection ψ x -
      ψ x * laplacianAt g g.leviCivitaConnection u x)
        ∂(riemannianMeasure (I := I) g mu) = 0 := by
  classical
  let F : M → ℝ := fun x ↦
    u x * laplacianAt g g.leviCivitaConnection ψ x -
      ψ x * laplacianAt g g.leviCivitaConnection u x
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q ↦ g.koszulDualSection_dual X Y W q)
  have hΔu : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (laplacianAt g g.leviCivitaConnection u) :=
    contMDiff_laplacianAt g hLC hu
  have hΔψ : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (laplacianAt g g.leviCivitaConnection ψ) :=
    contMDiff_laplacianAt g hLC hψ
  have hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F :=
    (hu.mul hΔψ).sub (hψ.mul hΔu)
  have hFU : tsupport F ⊆ tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxψ
    have hzero : ψ =ᶠ[nhds x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hxψ] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hψx : ψ x = 0 := hzero.self_of_nhds
    have hΔψx : laplacianAt g g.leviCivitaConnection ψ x = 0 := by
      rw [laplacianAt_congr_of_eventuallyEq g g.leviCivitaConnection hzero]
      have hdir_zero (X : SmoothVectorField I M) (q : M) :
          X.dir (fun _ ↦ (0 : ℝ)) q = 0 := by
        show mfderiv I 𝓘(ℝ, ℝ) (fun _ ↦ (0 : ℝ)) q (X q) = 0
        rw [mfderiv_const]
        rfl
      have hhessian_zero (X Y : SmoothVectorField I M) (q : M) :
          hessian g.leviCivitaConnection (fun _ ↦ (0 : ℝ)) X Y q = 0 := by
        unfold hessian
        have hY : Y.dir (fun _ ↦ (0 : ℝ)) = fun _ ↦ 0 :=
          funext fun r ↦ hdir_zero Y r
        rw [hY, hdir_zero X q, hdir_zero (g.leviCivitaConnection.cov X Y) q,
          sub_zero]
      unfold laplacianAt
      exact Finset.sum_eq_zero fun i _ ↦ hhessian_zero _ _ x
    apply hx
    simp only [F, hψx, hΔψx, mul_zero, zero_mul, sub_zero]
  have huC : ContDiffOn ℝ ∞ (u ∘ (extChartAt I a).symm)
      (extChartAt I a).target := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hu.comp_contMDiffOn (contMDiffOn_extChartAt_symm a)
  have hψC : ContDiff ℝ ∞ (chartPullback (I := I) a ψ) :=
    contDiff_chartPullback a hψ hψc hψa
  have hψCc : HasCompactSupport (chartPullback (I := I) a ψ) :=
    hasCompactSupport_chartPullback a hψc hψa
  have hψCU : tsupport (chartPullback (I := I) a ψ) ⊆
      (extChartAt I a).target :=
    tsupport_chartPullback_subset a hψc hψa
  change ∫ x, F x ∂(riemannianMeasure (I := I) g mu) = 0
  rw [integral_riemannianMeasure_eq_integral_chartPullback mu g a
    hF.continuous (hFU.trans hψa)]
  calc
    ∫ y, chartVolumeDensity (I := I) g a y *
        chartPullback (I := I) a F y ∂mu =
        ∫ y, ((u ∘ (extChartAt I a).symm) y *
            ∑ i, partialDeriv (E := V) i
              (coordinateFlux (greenChartCoeff (I := I) g a)
                (chartPullback (I := I) a ψ) i) y) -
          chartPullback (I := I) a ψ y *
            ∑ i, partialDeriv (E := V) i
              (coordinateFlux (greenChartCoeff (I := I) g a)
                (u ∘ (extChartAt I a).symm) i) y ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ (extChartAt I a).target
      · have hψdiv := chartVolumeDensity_mul_laplacianAt_eq_divergence
          g hψ a hy
        rw [← coordinateDivergence_chartPullback_eq
          (greenChartCoeff (I := I) g a) a ψ hy] at hψdiv
        have hudiv := chartVolumeDensity_mul_laplacianAt_eq_divergence
          g hu a hy
        rw [chartPullback_apply a F hy, chartPullback_apply a ψ hy]
        change chartVolumeDensity (I := I) g a y *
            (u ((extChartAt I a).symm y) *
                laplacianAt g g.leviCivitaConnection ψ ((extChartAt I a).symm y) -
              ψ ((extChartAt I a).symm y) *
                laplacianAt g g.leviCivitaConnection u ((extChartAt I a).symm y)) = _
        calc
          _ = u ((extChartAt I a).symm y) *
                (chartVolumeDensity (I := I) g a y *
                  laplacianAt g g.leviCivitaConnection ψ ((extChartAt I a).symm y)) -
              ψ ((extChartAt I a).symm y) *
                (chartVolumeDensity (I := I) g a y *
                  laplacianAt g g.leviCivitaConnection u ((extChartAt I a).symm y)) := by
                    ring
          _ = _ := by
            rw [hψdiv, hudiv]
            rfl
      · have hdivzero : ∀ i, partialDeriv (E := V) i
            (coordinateFlux (greenChartCoeff (I := I) g a)
              (chartPullback (I := I) a ψ) i) y = 0 := by
          intro i
          apply image_eq_zero_of_notMem_tsupport
          intro hy'
          exact hy (hψCU ((tsupport_partialDeriv_subset i).trans
            (tsupport_coordinateFlux_subset
              (greenChartCoeff (I := I) g a)
              (chartPullback (I := I) a ψ) i) hy'))
        rw [chartPullback_eq_zero a F hy, chartPullback_eq_zero a ψ hy]
        simp only [mul_zero, zero_mul, hdivzero, Finset.sum_const_zero, sub_zero]
    _ = 0 := integral_coordinateGreen_eq_zero mu
      (isOpen_extChartAt_target (I := I) a)
      (contDiffOn_greenChartCoeff g a)
      (fun y hy i j ↦ greenChartCoeff_symm g a hy i j)
      huC hψC hψCc hψCU

/-- **Math.** Green's identity on an open Riemannian domain:
∫ (u Δψ - ψ Δu) dvol = 0 for every smooth compactly supported test
function ψ.

Here the manifold type M represents the open domain Ω itself. Thus u and ψ
are functions on Ω; applying the theorem to an open subset of an ambient
manifold uses that open-set subtype and requires no extension of u outside
Ω. -/
theorem green_identity_compact_support
    [CompleteSpace V] [SigmaCompactSpace M]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (mu : Measure V) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) {u ψ : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, (u x * laplacianAt g g.leviCivitaConnection ψ x -
      ψ x * laplacianAt g g.leviCivitaConnection u x)
        ∂(riemannianMeasure (I := I) g mu) = 0 := by
  classical
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      (I := I) M
  let Aset : Set M :=
    {i | (Function.support (ρ i) ∩ tsupport ψ).Nonempty}
  have hAfin : Aset.Finite := by
    dsimp only [Aset]
    exact ρ.locallyFinite.finite_nonempty_inter_compact hψc.isCompact
  let A : Finset M := hAfin.toFinset
  let φ : M → M → ℝ := fun i x ↦ ρ i x * ψ x
  have hmemA {i : M} :
      i ∈ A ↔ (Function.support (ρ i) ∩ tsupport ψ).Nonempty := by
    simp only [A, Aset, Set.Finite.mem_toFinset, mem_setOf_eq]
  have hfinsupport_subset (x : M) (hx : ψ x ≠ 0) :
      ρ.finsupport x ⊆ A := by
    intro i hi
    rw [hmemA]
    have hiρ : ρ i x ≠ 0 := by
      simpa [Function.mem_support] using hi
    exact ⟨x, hiρ, subset_closure hx⟩
  have hψsum : ψ = fun x ↦ ∑ i ∈ A, φ i x := by
    funext x
    by_cases hx : ψ x = 0
    · simp [φ, hx]
    · have hsum := ρ.sum_finsupport'
        (x₀ := x) (by simp) (hfinsupport_subset x hx)
      calc
        ψ x = 1 * ψ x := (one_mul _).symm
        _ = (∑ i ∈ A, ρ i x) * ψ x := by rw [hsum]
        _ = ∑ i ∈ A, φ i x := by
          rw [Finset.sum_mul]
  have hφ (i : M) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i) := by
    dsimp only [φ]
    exact (ρ i).contMDiff.mul hψ
  have hφc (i : M) : HasCompactSupport (φ i) := by
    dsimp only [φ]
    exact hψc.mul_left
  have hφchart (i : M) :
      tsupport (φ i) ⊆ (extChartAt I i).source := by
    refine (tsupport_mul_subset_left (f := fun x ↦ ρ i x) (g := ψ)).trans ?_
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hρ i
  let G : M → M → ℝ := fun i x ↦
    u x * laplacianAt g g.leviCivitaConnection (φ i) x -
      φ i x * laplacianAt g g.leviCivitaConnection u x
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q ↦ g.koszulDualSection_dual X Y W q)
  have hΔu : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (laplacianAt g g.leviCivitaConnection u) :=
    contMDiff_laplacianAt g hLC hu
  have hGsmooth (i : M) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (G i) := by
    have hΔφ : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (laplacianAt g g.leviCivitaConnection (φ i)) :=
      contMDiff_laplacianAt g hLC (hφ i)
    exact (hu.mul hΔφ).sub ((hφ i).mul hΔu)
  have hGsupport (i : M) : tsupport (G i) ⊆ tsupport (φ i) := by
    simpa only [G] using
      tsupport_greenIntegrand_subset g g.leviCivitaConnection u (φ i)
  have hGc (i : M) : HasCompactSupport (G i) :=
    (hφc i).of_isClosed_subset (isClosed_tsupport _) (hGsupport i)
  have hGint (i : M) :
      Integrable (G i) (riemannianMeasure (I := I) g mu) :=
    integrable_riemannianMeasure_of_tsupport_subset_chart
      mu g i (hGsmooth i) (hGc i) ((hGsupport i).trans (hφchart i))
  have hGzero (i : M) :
      ∫ x, G i x ∂(riemannianMeasure (I := I) g mu) = 0 := by
    dsimp only [G]
    exact green_identity_of_tsupport_subset_chart
      mu g i hu (hφ i) (hφc i) (hφchart i)
  have hΔψsum (x : M) :
      laplacianAt g g.leviCivitaConnection ψ x =
        ∑ i ∈ A, laplacianAt g g.leviCivitaConnection (φ i) x := by
    rw [hψsum]
    exact laplacianAt_finsetSum_function
      g g.leviCivitaConnection A (fun i _ ↦ hφ i) x
  have hGsum : (fun x ↦
      u x * laplacianAt g g.leviCivitaConnection ψ x -
        ψ x * laplacianAt g g.leviCivitaConnection u x) =
      fun x ↦ ∑ i ∈ A, G i x := by
    funext x
    rw [hΔψsum x, congrFun hψsum x]
    dsimp only [G]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  rw [hGsum, integral_finsetSum A (fun i _ ↦ hGint i)]
  exact Finset.sum_eq_zero fun i _ ↦ hGzero i

end MorganTianLib

end
