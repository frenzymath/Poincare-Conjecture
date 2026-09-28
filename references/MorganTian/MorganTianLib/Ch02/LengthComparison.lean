import MorganTianLib.Ch01.ComparisonMinimizing
import MorganTianLib.Ch01.CutLocusFacades
import DoCarmoLib.Riemannian.Manifold.ExpandingMap
import DoCarmoLib.Riemannian.Jacobi.CartanMFDerivBridge

/-!
# Morgan-Tian Ch. 2 - local input for length comparison

The nonnegative-curvature specialization of the radial comparison theorem says
that the differential of the exponential map does not increase metric norm at
points reached by a minimizing radial geodesic. Integrating this estimate along
appropriate tangent-space paths is the local analytic step toward Toponogov
length comparison.
-/

open Bundle Manifold MeasureTheory Set Riemannian
open scoped ContDiff Manifold

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** A map contracts the differential metric on `s` when every tangent vector
has image norm at most its source norm. -/
def DCShrinksMetricOn (gM : RiemannianMetric I M) (gN : RiemannianMetric I' M')
    (f : M → M') (s : Set M) : Prop :=
  ∀ p ∈ s, ∀ v : TangentSpace I p,
    gN.metricInner (f p) (mfderiv I I' f p v) (mfderiv I I' f p v) ≤
      gM.metricInner p v v

/-- **Math.** The fibre-enorm form of differential metric contraction. -/
theorem DCShrinksMetricOn.enorm_mfderiv_le {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {f : M → M'} {s : Set M}
    (hshrink : DCShrinksMetricOn gM gN f s) {p : M} (hp : p ∈ s)
    (v : TangentSpace I p) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨gM.toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
      ⟨gN.toRiemannianMetric⟩
    ‖mfderiv I I' f p v‖ₑ ≤ ‖v‖ₑ := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨gM.toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  rw [enorm_tangent_eq_sqrt_metricInner gN (f p) (mfderiv I I' f p v),
    enorm_tangent_eq_sqrt_metricInner gM p v]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hshrink p hp v))

/-- **Math.** A smooth map whose differential contracts the metric on a curve's image
does not increase that curve's Riemannian length. -/
theorem DCShrinksMetricOn.pathELength_comp_le {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {f : M → M'} {s : Set M}
    (hshrink : DCShrinksMetricOn gM gN f s)
    (hf : ContMDiff I I' 1 f) {c : ℝ → M} {a b : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b))
    (hmem : MapsTo c (Icc a b) s) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨gM.toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
      ⟨gN.toRiemannianMetric⟩
    pathELength I' (f ∘ c) a b ≤ pathELength I c a b := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨gM.toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Ioo,
    pathELength_eq_lintegral_mfderiv_Ioo]
  refine lintegral_mono_ae ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall fun t ht => ?_)
  have hct : MDifferentiableAt 𝓘(ℝ, ℝ) I c t :=
    ((hc t (Ioo_subset_Icc_self ht)).contMDiffAt
      (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  have hchain : mfderiv 𝓘(ℝ, ℝ) I' (f ∘ c) t 1 =
      mfderiv I I' f (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1) :=
    DCVelocity_comp t (hf.mdifferentiable one_ne_zero (c t)) hct
  rw [hchain]
  exact hshrink.enorm_mfderiv_le
    (hmem (Ioo_subset_Icc_self ht)) (mfderiv 𝓘(ℝ, ℝ) I c t 1)

/-- **Math.** Endpoint distance after a differential metric contraction is bounded by
the source curve length. -/
theorem DCShrinksMetricOn.riemannianEDist_comp_le_pathELength
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'}
    {f : M → M'} {s : Set M} (hshrink : DCShrinksMetricOn gM gN f s)
    (hf : ContMDiff I I' 1 f) {c : ℝ → M} {a b : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b))
    (hmem : MapsTo c (Icc a b) s) (hab : a ≤ b) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨gM.toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
      ⟨gN.toRiemannianMetric⟩
    riemannianEDist I' (f (c a)) (f (c b)) ≤ pathELength I c a b := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨gM.toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 (f ∘ c) (Icc a b) :=
    hf.comp_contMDiffOn hc
  exact (riemannianEDist_le_pathELength hcomp rfl rfl hab).trans
    (hshrink.pathELength_comp_le hf hc hmem)

end Riemannian

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [T2Space (TangentBundle I M)]

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The constant metric on the tangent model whose inner product is
`g` at the fixed base point `p`. -/
noncomputable def tangentSpaceMetricAt (g : RiemannianMetric I M) (p : M) :
    RiemannianMetric 𝓘(ℝ, E) E where
  inner _ := g.inner p
  symm _ v w := g.symm p v w
  pos _ v hv := g.pos p v hv
  isVonNBounded _ := g.isVonNBounded p
  contMDiff := by
    intro x
    rw [Bundle.contMDiffAt_section]
    convert! contMDiffAt_const (c := g.inner p)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

@[simp]
theorem tangentSpaceMetricAt_apply (g : RiemannianMetric I M) (p : M)
    (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) :
    (tangentSpaceMetricAt g p).metricInner x v w = g.metricInner p v w :=
  rfl

/-- **Math.** The squared tangent length of a radial chord is given by the
bilinear law of cosines. -/
theorem metricInner_radial_chord_self (g : RiemannianMetric I M) (p : M)
    (r s : ℝ) (u v : TangentSpace I p) :
    g.metricInner p (r • u - s • v) (r • u - s • v) =
      r ^ 2 * g.metricInner p u u + s ^ 2 * g.metricInner p v v -
        2 * r * s * g.metricInner p u v := by
  change (g.inner p) (r • u - s • v) (r • u - s • v) =
    r ^ 2 * (g.inner p) u u + s ^ 2 * (g.inner p) v v -
      2 * r * s * (g.inner p) u v
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
  rw [g.symm p v u]
  ring

/-- **Math.** Along a minimizing radial geodesic in nonnegative sectional curvature,
the differential of `exp_p` is nonexpanding for the metrics at `p` and at the
image point. -/
theorem expDifferential_metricInner_le_of_nonneg_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {r r₀ : ℝ} (hr : 0 < r) (hrr₀ : r < r₀)
    {u : E} (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hmin : ∀ s ∈ Ioo (0 : ℝ) r₀,
      s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s))
    (hsec : ∀ s ∈ Ioo (0 : ℝ) r₀,
      ∀ w₁ w₂ : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s),
        0 ≤ sectionalCurvatureAt g g.leviCivitaConnection
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s) w₁ w₂) :
    ∃ (ζ : M) (D : E →L[ℝ] E),
      expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p) ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D (r • u) ∧
      ∀ Z : E,
        chartMetricInner (I := I) g ζ
            (extChartAt I ζ (expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p)))
            (D Z) (D Z)
          ≤ g.metricInner p (Z : TangentSpace I p) (Z : TangentSpace I p) := by
  obtain ⟨ζ, D, hmem, hD, hbound⟩ :=
    expDifferential_metricInner_le_of_minimizing (I := I) g hg p
      (k := 0) (r := r) (r₀ := r₀) (by positivity) hr hrr₀ hu hmin (by
        intro s hs w₁ w₂
        simpa using hsec s hs w₁ w₂)
  refine ⟨ζ, D, hmem, hD, fun Z => ?_⟩
  simpa [snK_zero_left, ne_of_gt hr] using hbound Z

/-- **Math.** The intrinsic differential form of the nonnegative-curvature exponential
contraction estimate. -/
theorem metricInner_mfderiv_expMapGlobal_le_of_nonneg_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {r r₀ : ℝ} (hr : 0 < r) (hrr₀ : r < r₀)
    {u : E} (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hmin : ∀ s ∈ Ioo (0 : ℝ) r₀,
      s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s))
    (hsec : ∀ s ∈ Ioo (0 : ℝ) r₀,
      ∀ w₁ w₂ : TangentSpace I (globalGeodesic (I := I) g hg p
        (u : TangentSpace I p) s),
        0 ≤ sectionalCurvatureAt g g.leviCivitaConnection
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s) w₁ w₂) :
    ∀ Z : E,
      g.metricInner (expMapGlobal (I := I) g hg p (r • u))
          (mfderiv 𝓘(ℝ, E) I (fun v : E => expMapGlobal (I := I) g hg p v)
            (r • u) Z)
          (mfderiv 𝓘(ℝ, E) I (fun v : E => expMapGlobal (I := I) g hg p v)
            (r • u) Z)
        ≤ g.metricInner p (Z : TangentSpace I p) (Z : TangentSpace I p) := by
  obtain ⟨ζ, D, hmem, hD, hbound⟩ :=
    expDifferential_metricInner_le_of_nonneg_of_minimizing
      (I := I) g hg p hr hrr₀ hu hmin hsec
  intro Z
  have hbridge :=
    Riemannian.Jacobi.chartMetricInner_expDifferential_eq_metricInner_mfderiv
      g hg p (r • u) hmem hD Z Z
  calc
    g.metricInner
        (expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p))
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapGlobal (I := I) g hg p w) (r • u) Z)
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => expMapGlobal (I := I) g hg p w) (r • u) Z) =
      chartMetricInner (I := I) g ζ
        (extChartAt I ζ
          (expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p)))
        (D Z) (D Z) := hbridge.symm
    _ ≤ g.metricInner p (Z : TangentSpace I p) (Z : TangentSpace I p) :=
      hbound Z

/-- **Math.** A tangent vector lies in the strict minimizing comparison domain
at `p` if it is zero, or if it lies strictly inside a minimizing radial segment
along which every sectional curvature is nonnegative. -/
def IsNonnegMinimizingExpPoint (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) (v : E) : Prop :=
  v = 0 ∨
    ∃ (r r₀ : ℝ) (u : E),
      0 < r ∧ r < r₀ ∧ v = r • u ∧
      g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1 ∧
      (∀ s ∈ Ioo (0 : ℝ) r₀,
        s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)) ∧
      ∀ s ∈ Ioo (0 : ℝ) r₀,
        ∀ w₁ w₂ : TangentSpace I
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s),
          0 ≤ sectionalCurvatureAt g g.leviCivitaConnection
            (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s) w₁ w₂

/-- **Math.** Under global nonnegative sectional curvature, every vector strictly
inside its radial cut time belongs to the minimizing comparison domain. -/
theorem isNonnegMinimizingExpPoint_of_mem_segmentDomain
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M)
    (hsec : ∀ q : M, ∀ w₁ w₂ : TangentSpace I q,
      0 ≤ sectionalCurvatureAt g g.leviCivitaConnection q w₁ w₂)
    {v : E} (hv : (v : TangentSpace I p) ∈ segmentDomain (I := I) g hg p) :
    IsNonnegMinimizingExpPoint (I := I) g hg p v := by
  by_cases hv0 : (v : TangentSpace I p) = 0
  · exact Or.inl hv0
  right
  set r : ℝ := Real.sqrt (g.metricInner p (v : TangentSpace I p) v) with hr_def
  have hr : 0 < r := Real.sqrt_pos.2 (g.metricInner_self_pos p _ hv0)
  set u : E := r⁻¹ • v with hu_def
  have hvdecomp : (v : E) = r • u := by
    show v = r • (r⁻¹ • v)
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hvdecomp_tangent :
      (v : TangentSpace I p) = r • (u : TangentSpace I p) := by
    exact hvdecomp
  have huunit :
      g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1 := by
    have hrsq : r ^ 2 = g.metricInner p (v : TangentSpace I p) v := by
      dsimp [r]
      exact Real.sq_sqrt (g.metricInner_self_nonneg p _)
    have key : ∀ z : TangentSpace I p,
        g.metricInner p (r⁻¹ • z) (r⁻¹ • z) =
          (r⁻¹ * r⁻¹) * g.metricInner p z z := by
      intro z
      rw [g.metricInner_smul_left, g.metricInner_smul_right]
      ring
    calc
      g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) =
          (r⁻¹ * r⁻¹) * g.metricInner p (v : TangentSpace I p) v := key _
      _ = 1 := by
        rw [← hrsq]
        field_simp
  have hcut : ENNReal.ofReal r <
      cutTime (I := I) g hg p (u : TangentSpace I p) := by
    apply (smul_mem_segmentDomain_iff_lt_cutTime (I := I) g hg p hr).1
    change (r • (u : TangentSpace I p)) ∈ segmentDomain (I := I) g hg p
    rw [← hvdecomp_tangent]
    exact hv
  rw [cutTime, lt_iSup_iff] at hcut
  obtain ⟨r₀, hcut⟩ := hcut
  rw [lt_iSup_iff] at hcut
  obtain ⟨hr₀mem, hrr₀⟩ := hcut
  have hrr₀' : r < r₀ :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr.le).1 hrr₀
  refine ⟨r, r₀, u, hr, hrr₀', hvdecomp, huunit, ?_, ?_⟩
  · intro s hs
    have hmin := IsMinimizingUpTo.mono (I := I) g hg p
      (u : TangentSpace I p) hr₀mem.2 hs.1.le hs.2.le
    rw [IsMinimizingUpTo, huunit, Real.sqrt_one, one_mul] at hmin
    exact hmin.ge
  · intro s hs w₁ w₂
    exact hsec _ w₁ w₂

/-- **Math.** On any set of strict minimizing comparison points, the
exponential map contracts the constant tangent metric `g_p` into `g`. -/
theorem expMapGlobal_dcShrinksMetricOn_of_nonneg_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (s : Set E)
    (hs : ∀ v ∈ s, IsNonnegMinimizingExpPoint (I := I) g hg p v) :
    Riemannian.DCShrinksMetricOn (tangentSpaceMetricAt g p) g
      (fun v : E => expMapGlobal (I := I) g hg p v) s := by
  intro v hv Z
  rcases hs v hv with hv0 | ⟨r, r₀, u, hr, hrr₀, hvru, hu, hmin, hsec⟩
  · subst v
    have hzero :
        mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) 0 Z = Z :=
      Riemannian.Jacobi.mfderiv_expMapGlobal_zero_apply g hg p Z
    have hpoint : (fun w : E => expMapGlobal (I := I) g hg p w) 0 = p :=
      expMapGlobal_zero g hg p
    rw [hzero, hpoint]
    rfl
  · subst v
    exact metricInner_mfderiv_expMapGlobal_le_of_nonneg_of_minimizing
      (I := I) g hg p hr hrr₀ hu hmin hsec Z

/-- **Math.** With nonnegative sectional curvature, the exponential map
contracts the fixed tangent metric throughout the strict segment domain. -/
theorem expMapGlobal_dcShrinksMetricOn_segmentDomain_of_nonneg
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M)
    (hsec : ∀ q : M, ∀ w₁ w₂ : TangentSpace I q,
      0 ≤ sectionalCurvatureAt g g.leviCivitaConnection q w₁ w₂) :
    Riemannian.DCShrinksMetricOn (tangentSpaceMetricAt g p) g
      (fun v : E => expMapGlobal (I := I) g hg p v)
      (segmentDomain (I := I) g hg p) := by
  exact expMapGlobal_dcShrinksMetricOn_of_nonneg_of_minimizing
    (I := I) g hg p _ fun _ hv =>
      isNonnegMinimizingExpPoint_of_mem_segmentDomain (I := I) g hg p hsec hv

/-- **Math.** A `C¹` tangent-space path contained in the strict minimizing
comparison domain has exponential image of no greater Riemannian length. -/
theorem pathELength_expMapGlobal_le_of_nonneg_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (s : Set E)
    (hs : ∀ v ∈ s, IsNonnegMinimizingExpPoint (I := I) g hg p v)
    {c : ℝ → E} {a b : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b))
    (hmem : MapsTo c (Icc a b) s) :
    letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨(tangentSpaceMetricAt g p).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    pathELength I
        ((fun v : E => expMapGlobal (I := I) g hg p v) ∘ c) a b ≤
      pathELength 𝓘(ℝ, E) c a b := by
  have hexp : ContMDiff 𝓘(ℝ, E) I 1
      (fun v : E => expMapGlobal (I := I) g hg p v) :=
    (Riemannian.Exponential.contMDiff_expMapGlobal g hg p).of_le (by norm_num)
  exact (expMapGlobal_dcShrinksMetricOn_of_nonneg_of_minimizing
    (I := I) g hg p s hs).pathELength_comp_le hexp hc hmem

/-- **Math.** The Riemannian distance between the exponential images of a
comparison-domain path's endpoints is bounded by its tangent-space length. -/
theorem riemannianEDist_expMapGlobal_le_pathELength_of_nonneg_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (s : Set E)
    (hs : ∀ v ∈ s, IsNonnegMinimizingExpPoint (I := I) g hg p v)
    {c : ℝ → E} {a b : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Icc a b))
    (hmem : MapsTo c (Icc a b) s) (hab : a ≤ b) :
    letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨(tangentSpaceMetricAt g p).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    riemannianEDist I
        (expMapGlobal (I := I) g hg p (c a))
        (expMapGlobal (I := I) g hg p (c b)) ≤
      pathELength 𝓘(ℝ, E) c a b := by
  have hexp : ContMDiff 𝓘(ℝ, E) I 1
      (fun v : E => expMapGlobal (I := I) g hg p v) :=
    (Riemannian.Exponential.contMDiff_expMapGlobal g hg p).of_le (by norm_num)
  exact (expMapGlobal_dcShrinksMetricOn_of_nonneg_of_minimizing
    (I := I) g hg p s hs).riemannianEDist_comp_le_pathELength
      hexp hc hmem hab

/-- **Math.** If the affine tangent chord from `v` to `w` remains inside the
strict segment domain, its exponential image joins `exp_p(v)` to `exp_p(w)`
without increasing length. -/
theorem riemannianEDist_expMapGlobal_le_affineChord_of_nonneg
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M)
    (hsec : ∀ q : M, ∀ z₁ z₂ : TangentSpace I q,
      0 ≤ sectionalCurvatureAt g g.leviCivitaConnection q z₁ z₂)
    (v w : E)
    (hsegment : MapsTo (fun t : ℝ => (1 - t) • v + t • w) (Icc (0 : ℝ) 1)
      (segmentDomain (I := I) g hg p)) :
    letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨(tangentSpaceMetricAt g p).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    riemannianEDist I
        (expMapGlobal (I := I) g hg p v)
        (expMapGlobal (I := I) g hg p w) ≤
      pathELength 𝓘(ℝ, E) (fun t : ℝ => (1 - t) • v + t • w) 0 1 := by
  have hdiff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      (fun t : ℝ => (1 - t) • v + t • w) (Icc (0 : ℝ) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    fun_prop
  have hexp : ContMDiff 𝓘(ℝ, E) I 1
      (fun z : E => expMapGlobal (I := I) g hg p z) :=
    (Riemannian.Exponential.contMDiff_expMapGlobal g hg p).of_le (by norm_num)
  simpa using (expMapGlobal_dcShrinksMetricOn_segmentDomain_of_nonneg
    (I := I) g hg p hsec).riemannianEDist_comp_le_pathELength
      hexp hdiff hsegment (by norm_num)

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The affine chord in a fixed tangent metric has constant speed, so its
length is the square root of the metric inner product of its endpoint difference. -/
theorem pathELength_affineChord_tangentSpaceMetricAt
    (g : RiemannianMetric I M) (p : M) (v w : E) :
    letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨(tangentSpaceMetricAt g p).toRiemannianMetric⟩
    pathELength 𝓘(ℝ, E) (fun t : ℝ => (1 - t) • v + t • w) 0 1 =
      ENNReal.ofReal (Real.sqrt (g.metricInner p
        ((w - v : E) : TangentSpace I p) ((w - v : E) : TangentSpace I p))) := by
  letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨(tangentSpaceMetricAt g p).toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  have hderiv : ∀ t : ℝ,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => (1 - t) • v + t • w) t 1 = w - v := by
    intro t
    rw [mfderiv_eq_fderiv]
    change (fderiv ℝ (fun t : ℝ => (1 - t) • v + t • w) t) (1 : ℝ) = (w - v : E)
    rw [fderiv_apply_one_eq_deriv]
    have h : HasDerivAt (fun t : ℝ => (1 - t) • v + t • w) (-v + w) t := by
      convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const v).add
        ((hasDerivAt_id t).smul_const w) using 1
      · funext y
        simp
      · rw [zero_sub, neg_one_smul, one_smul]
    calc
      deriv (fun t : ℝ => (1 - t) • v + t • w) t = -v + w := h.deriv
      _ = w - v := by abel
  calc
    ∫⁻ t in Ioo (0 : ℝ) 1,
        ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun t : ℝ => (1 - t) • v + t • w) t 1‖ₑ =
        ∫⁻ _ in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt (g.metricInner p
            ((w - v : E) : TangentSpace I p) ((w - v : E) : TangentSpace I p))) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp
      rw [Riemannian.enorm_tangent_eq_sqrt_metricInner
        (tangentSpaceMetricAt g p) ((1 - t) • v + t • w), hderiv t]
      rfl
    _ = ENNReal.ofReal (Real.sqrt (g.metricInner p
        ((w - v : E) : TangentSpace I p) ((w - v : E) : TangentSpace I p))) := by
      simp [Real.volume_Ioo]

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The local nonnegative-curvature affine-chord estimate in explicit
tangent-metric form. The segment-domain hypothesis is retained because the global
cut-locus and hinge arguments are separate parts of length comparison. -/
theorem riemannianEDist_expMapGlobal_le_affineChord_metricInner_of_nonneg
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M)
    (hsec : ∀ q : M, ∀ z₁ z₂ : TangentSpace I q,
      0 ≤ sectionalCurvatureAt g g.leviCivitaConnection q z₁ z₂)
    (v w : E)
    (hsegment : MapsTo (fun t : ℝ => (1 - t) • v + t • w) (Icc (0 : ℝ) 1)
      (segmentDomain (I := I) g hg p)) :
    letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨(tangentSpaceMetricAt g p).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    riemannianEDist I
        (expMapGlobal (I := I) g hg p v)
        (expMapGlobal (I := I) g hg p w) ≤
      ENNReal.ofReal (Real.sqrt (g.metricInner p
        ((w - v : E) : TangentSpace I p) ((w - v : E) : TangentSpace I p))) := by
  letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨(tangentSpaceMetricAt g p).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  calc
    riemannianEDist I
        (expMapGlobal (I := I) g hg p v)
        (expMapGlobal (I := I) g hg p w) ≤
        pathELength 𝓘(ℝ, E) (fun t : ℝ => (1 - t) • v + t • w) 0 1 :=
      riemannianEDist_expMapGlobal_le_affineChord_of_nonneg
        (I := I) g hg p hsec v w hsegment
    _ = ENNReal.ofReal (Real.sqrt (g.metricInner p
        ((w - v : E) : TangentSpace I p) ((w - v : E) : TangentSpace I p))) :=
      pathELength_affineChord_tangentSpaceMetricAt (I := I) g p v w

end MorganTianLib

end
