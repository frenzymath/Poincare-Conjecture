import PetersenLib.Ch05.EuclideanSegments
import PetersenLib.Ch05.Geodesics

/-!
# Petersen Ch. 5, §5.2–§5.3 — the flat metric on an open subset of a Euclidean space

Petersen's Ch. 5 examples repeatedly use *open subsets of `ℝⁿ` with the flat
metric* — most prominently the punctured plane `ℝ² − {0}` (Examples 5.2.7 and
5.3.7), an incomplete manifold in which not every pair of points is joined by a
segment.  Neither Mathlib nor `PetersenLib` carried a Riemannian metric on an
open subset of an inner product space (Mathlib's `Riemannian/Basic.lean` and
`VectorBundle/Riemannian.lean` never mention `TopologicalSpace.Opens`), so this
file builds it.

For `s : TopologicalSpace.Opens F` with `F` a real inner product space, the
`ChartedSpace F s` structure supplied by Mathlib uses the *restricted identity*
charts (`TopologicalSpace.Opens.chartAt_eq`), so:

* `extChartAt_opens_apply` — every extended chart on `s` is the coercion
  `s → F`;
* `coordChange_opens` — every tangent-bundle chart transition on `s` is the
  identity `1 : F →L[ℝ] F`;
* `opensFlatMetric F s : RiemannianMetric 𝓘(ℝ, F) s` — hence the constant
  section `x ↦ ⟪·, ·⟫` really is a `C^∞` Riemannian metric on `s`, the *flat
  metric*, obtained by porting Mathlib's `riemannianMetricVectorSpace` across
  the three `Opens` analogues of its model-space `@[simp]` lemmas.

The point of the flat metric is that it is *computed by the ambient Euclidean
geometry*, and this file supplies the three transfer lemmas that make that
usable:

* `curveSpeedSq_transfer`, `curveLength_transfer` — the intrinsic speed and
  length of `γ : ℝ → s` equal the ambient speed and length of `fun r => (γ r : F)`;
* `isPiecewiseSmoothCurve_transfer` — piecewise smoothness passes to the ambient
  curve.

Finally, the Christoffel symbols of the flat metric vanish in every chart:

* `chartBasisVecFiber_opens`, `chartGramOnE_opensFlatMetric`,
  `chartChristoffel_opensFlatMetric` (`Γ ≡ 0`).

**What this file does NOT provide.**  It says nothing about geodesics of
`opensFlatMetric` (`chartChristoffel_opensFlatMetric` is the coefficient
computation only; converting it into `IsGeodesic` statements about straight
lines is separate work), nothing about completeness, and nothing about
non-flat metrics — in particular it gives no route to the sphere or hyperbolic
examples, whose Gram matrices are non-constant in the stereographic chart.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §5.2–§5.3.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Bornology TopologicalSpace Set
open scoped ContDiff Manifold Topology

namespace PetersenLib

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ## Charts on an open subset are restricted identities -/

/-- **Math.** The chart of an open subset `s ⊆ F` at any point has source all of
`s`: Mathlib's charted-space structure on `s` restricts the single identity
chart of `F` (`TopologicalSpace.Opens.chartAt_eq`). -/
theorem chartAt_opens_source (s : Opens F) (x : s) : (chartAt F x).source = univ := by
  simp [TopologicalSpace.Opens.chartAt_eq]

/-- **Math.** Every extended chart on an open subset `s ⊆ F` is the inclusion
`s ↪ F`: the charts are restrictions of the identity chart of `F`. -/
theorem extChartAt_opens_apply (s : Opens F) (x : s) (y : s) :
    (extChartAt 𝓘(ℝ, F) x) y = (y : F) := by
  simp [extChartAt, TopologicalSpace.Opens.chartAt_eq]

/-- **Math.** The inverse of an extended chart on an open subset `s ⊆ F` is the
identity on `s`: for `y ∈ s`, the point `(extChartAt 𝓘(ℝ, F) x).symm y : s` has
underlying vector `y`. -/
theorem extChartAt_opens_symm_coe (s : Opens F) (x : s) (y : F) (hy : y ∈ s) :
    (((extChartAt 𝓘(ℝ, F) x).symm y : s) : F) = y := by
  have := OpenPartialHomeomorph.subtypeRestr_symm_apply (e := OpenPartialHomeomorph.refl F)
    (U := s) ⟨x⟩ (y := y) ?_
  · simpa [extChartAt, TopologicalSpace.Opens.chartAt_eq] using this
  · simpa [extChartAt, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_def] using hy

/-- **Math.** Every tangent-bundle chart transition of an open subset `s ⊆ F` is
the identity: the transition map between two extended charts on `s` agrees with
`id` on the open neighbourhood `s` of the base point, so its Fréchet derivative
is `1 : F →L[ℝ] F`.  This is what makes `s` *flat by construction*. -/
theorem coordChange_opens (s : Opens F) (b b' : s) (z : s) :
    (tangentBundleCore 𝓘(ℝ, F) s).coordChange (achart F b) (achart F b') z = 1 := by
  rw [tangentBundleCore_coordChange_achart]
  have hrange : range (𝓘(ℝ, F) : ModelWithCorners ℝ F F) = univ := by simp
  rw [hrange, fderivWithin_univ]
  rw [extChartAt_opens_apply s b z]
  have heq : ((extChartAt 𝓘(ℝ, F) b') ∘ (extChartAt 𝓘(ℝ, F) b).symm)
      =ᶠ[𝓝 (z : F)] id := by
    filter_upwards [(s.2).mem_nhds z.2] with y hy
    show (extChartAt 𝓘(ℝ, F) b') ((extChartAt 𝓘(ℝ, F) b).symm y) = y
    rw [extChartAt_opens_apply]
    exact extChartAt_opens_symm_coe s b y hy
  rw [heq.fderiv_eq, fderiv_id]
  rfl

/-- **Math.** The inverse trivialization of `Ts` at any two points of an open
subset `s ⊆ F` is the identity `1 : F →L[ℝ] F` (`coordChange_opens`). -/
@[simp high, mfld_simps]
theorem symmL_opens (s : Opens F) (b b' : s) :
    (trivializationAt F (TangentSpace 𝓘(ℝ, F)) b).symmL ℝ b' = (1 : F →L[ℝ] F) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (I := 𝓘(ℝ, F)) (b₀ := b) (b := b')
      (by rw [chartAt_opens_source]; trivial),
    coordChange_opens]

/-- **Math.** The trivialization of `Ts` at any two points of an open subset
`s ⊆ F` is the identity `1 : F →L[ℝ] F` (`coordChange_opens`). -/
@[simp high, mfld_simps]
theorem continuousLinearMapAt_opens (s : Opens F) (b b' : s) :
    (trivializationAt F (TangentSpace 𝓘(ℝ, F)) b).continuousLinearMapAt ℝ b'
      = (1 : F →L[ℝ] F) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := 𝓘(ℝ, F))
      (b₀ := b) (b := b') (by rw [chartAt_opens_source]; trivial),
    coordChange_opens]

/-- **Math.** The tangent bundle of an open subset `s ⊆ F` is trivialized over
all of `s` by a single chart. -/
@[simp high, mfld_simps]
theorem trivializationAt_baseSet_opens (s : Opens F) (b : s) :
    (trivializationAt F (TangentSpace 𝓘(ℝ, F)) b).baseSet = univ := by
  rw [TangentBundle.trivializationAt_baseSet, chartAt_opens_source]

/-! ## The flat metric on an open subset -/

variable (F) in
set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Petersen §5.2–§5.3 (the ambient setting of Examples 5.2.7 and
5.3.7): the **flat metric** on an open subset `s` of a real inner product space
`F`, giving each tangent space `T_x s = F` the ambient inner product,
`g_x(v, w) = ⟪v, w⟫`.  This is the restriction of `innerProductSpaceMetric F`
to `s`; smoothness of the section holds because, by `coordChange_opens`, the
tangent bundle of `s` is trivialized by the identity, so the metric section is
literally the constant `innerSL ℝ` in bundle coordinates.  (Proof adapted from
Mathlib's `riemannianMetricVectorSpace`.) -/
def opensFlatMetric (s : Opens F) :
    RiemannianMetric 𝓘(ℝ, F) s where
  inner x := (innerSL ℝ (E := F) : F →L[ℝ] F →L[ℝ] ℝ)
  symm x v w := real_inner_comm _ _
  pos x v hv := real_inner_self_pos.2 hv
  isVonNBounded x := by
    change IsVonNBounded ℝ {v : F | (inner ℝ v v : ℝ) < 1}
    have h : Metric.ball (0 : F) 1 = {v : F | (inner ℝ v v : ℝ) < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
        RCLike.re_to_real, Set.mem_setOf_eq]
      conv_lhs => rw [show (1 : ℝ) = √1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← h]
    exact NormedSpace.isVonNBounded_ball ℝ F 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := innerSL ℝ)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

/-- **Math.** The flat metric on an open subset pairs tangent vectors by the
ambient inner product. -/
@[simp]
theorem opensFlatMetric_apply (s : Opens F) (x : s) (v w : TangentSpace 𝓘(ℝ, F) x) :
    (opensFlatMetric F s).metricInner x v w = @inner ℝ F _ v w :=
  rfl

/-! ## Transfer of speed, length and regularity to the ambient space -/

variable [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)]

/-- **Math.** **Speed transfer.** The intrinsic squared speed of a curve
`γ : ℝ → s` in `(s, opensFlatMetric)` equals the ambient squared speed of
`fun r => (γ r : F)` in `(F, innerProductSpaceMetric)`: by
`extChartAt_opens_apply` both chart-local readings *are* the ambient curve, and
both metrics pair by the ambient inner product. -/
theorem curveSpeedSq_transfer (s : Opens F) (γ : ℝ → s) (t : ℝ) :
    curveSpeedSq (I := 𝓘(ℝ, F)) (opensFlatMetric F s) γ t
      = curveSpeedSq (I := 𝓘(ℝ, F)) (innerProductSpaceMetric F)
          (fun r => (γ r : F)) t := by
  rw [curveSpeedSq_def, curveSpeedSq_def]
  have h1 : Geodesic.chartLocalCurve (I := 𝓘(ℝ, F)) γ t = fun r => (γ r : F) := by
    funext r
    exact extChartAt_opens_apply s (γ t) (γ r)
  have h2 : Geodesic.chartLocalCurve (I := 𝓘(ℝ, F)) (fun r => (γ r : F)) t
      = fun r => (γ r : F) := by
    funext r
    simp [Geodesic.chartLocalCurve]
  rw [h1, h2]
  rfl

/-- **Math.** **Length transfer.** The intrinsic Petersen length of a curve in
`(s, opensFlatMetric)` equals the ambient Euclidean length of the underlying
curve in `F`: integrate `curveSpeedSq_transfer`. -/
theorem curveLength_transfer (s : Opens F) (γ : ℝ → s) (a b : ℝ) :
    curveLength (I := 𝓘(ℝ, F)) (opensFlatMetric F s) γ a b
      = curveLength (I := 𝓘(ℝ, F)) (innerProductSpaceMetric F)
          (fun r => (γ r : F)) a b := by
  simp only [curveLength_def, curveSpeedSq_transfer]

/-- **Math.** **Regularity transfer.** A piecewise `C^∞` curve into an open
subset `s ⊆ F` is a piecewise `C^∞` curve into `F`: compose with the smooth
inclusion `s ↪ F`, keeping the same partition. -/
theorem isPiecewiseSmoothCurve_transfer (s : Opens F) {γ : ℝ → s} {a b : ℝ}
    (h : IsPiecewiseSmoothCurve (I := 𝓘(ℝ, F)) γ a b) :
    IsPiecewiseSmoothCurve (I := 𝓘(ℝ, F)) (fun r => (γ r : F)) a b := by
  obtain ⟨hcont, n, u, hmono, hu0, hun, hsm⟩ := h
  exact ⟨continuous_subtype_val.comp_continuousOn hcont, n, u, hmono, hu0, hun,
    fun i => contMDiff_subtype_val.comp_contMDiffOn (hsm i)⟩

/-! ## Chords are no longer than curves: the ambient lower bound

For an open subset of `ℝⁿ` these are the workhorses of the Ch. 5 examples: the
intrinsic length of a curve staying inside `s` is at least the ambient Euclidean
distance of its endpoints — an *open* subset can only make curves longer, never
shorter, since it has fewer of them. -/

section Euclidean

variable {n : ℕ} [NeZero n]

/-- **Math.** **Chord bound.** For a piecewise `C^∞` curve `γ : [0, 1] → s`
inside an open subset `s ⊆ ℝⁿ` carrying the flat metric, the ambient Euclidean
chord `‖x − y‖` between its endpoints is at most the intrinsic length of `γ`:
transfer the length to the ambient curve (`curveLength_transfer`) and apply the
Euclidean distance formula `riemannianDistance_euclideanMetric`. -/
theorem norm_sub_le_curveLength_opensFlatMetric
    (s : Opens (EuclideanSpace ℝ (Fin n))) {γ : ℝ → s} {x y : s}
    (hγ : IsPiecewiseSmoothCurve (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) γ 0 1)
    (h0 : γ 0 = x) (h1 : γ 1 = y) :
    ‖(x : EuclideanSpace ℝ (Fin n)) - (y : EuclideanSpace ℝ (Fin n))‖
      ≤ curveLength (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (opensFlatMetric (EuclideanSpace ℝ (Fin n)) s) γ 0 1 := by
  rw [curveLength_transfer]
  have hamb := riemannianDistance_le_curveLength
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (euclideanMetric n)
    (isPiecewiseSmoothCurve_transfer s hγ)
    (show ((γ 0 : s) : EuclideanSpace ℝ (Fin n)) = (x : EuclideanSpace ℝ (Fin n)) by rw [h0])
    (show ((γ 1 : s) : EuclideanSpace ℝ (Fin n)) = (y : EuclideanSpace ℝ (Fin n)) by rw [h1])
  rwa [riemannianDistance_euclideanMetric] at hamb

/-- **Math.** **Ambient lower bound for the intrinsic distance.** If `x, y` in an
open `s ⊆ ℝⁿ` are joined by *some* piecewise `C^∞` curve inside `s` (so that
Petersen's `Ω_{x,y}` is nonempty and the infimum is not the junk value
`sInf ∅ = 0`), then `‖x − y‖ ≤ |xy|_s`: every competitor is bounded below by the
chord (`norm_sub_le_curveLength_opensFlatMetric`). -/
theorem norm_sub_le_riemannianDistance_opensFlatMetric
    (s : Opens (EuclideanSpace ℝ (Fin n))) (x y : s)
    (hne : ∃ γ : ℝ → s, IsPiecewiseSmoothCurve (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) γ 0 1 ∧
      γ 0 = x ∧ γ 1 = y) :
    ‖(x : EuclideanSpace ℝ (Fin n)) - (y : EuclideanSpace ℝ (Fin n))‖
      ≤ riemannianDistance (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (opensFlatMetric (EuclideanSpace ℝ (Fin n)) s) x y := by
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := hne
  rw [riemannianDistance]
  refine le_csInf ⟨_, σ, hσ, hσ0, hσ1, rfl⟩ ?_
  rintro L ⟨γ, hpw, h0, h1, rfl⟩
  exact norm_sub_le_curveLength_opensFlatMetric s hpw h0 h1

end Euclidean

/-! ## The flat metric is flat: vanishing Christoffel symbols -/

open Geodesic Tensor

/-- **Math.** The chart basis vector fields of an open subset `s ⊆ F` are the
constant model basis vectors: the trivialization of `Ts` is the identity
(`symmL_opens`), so no chart transition ever bends them. -/
theorem chartBasisVecFiber_opens (s : Opens F) (a : s) (i : Fin (Module.finrank ℝ F)) (b : s) :
    chartBasisVecFiber (I := 𝓘(ℝ, F)) a i b = (Module.finBasis ℝ F) i := by
  rw [Tensor.chartBasisVecFiber]
  have := symmL_opens s a b
  have h2 : (trivializationAt F (TangentSpace 𝓘(ℝ, F)) a).symm (b : s)
      = fun v => (trivializationAt F (TangentSpace 𝓘(ℝ, F)) a).symmL ℝ (b : s) v := by
    funext v
    rw [Trivialization.symmL_apply]
  rw [h2, this]
  rfl

/-- **Math.** The chart Gram matrix function of the flat metric on an open
subset is **constant**: it pairs the constant model basis vectors
(`chartBasisVecFiber_opens`) by the constant ambient inner product. -/
theorem chartGramOnE_opensFlatMetric (s : Opens F) (a : s)
    (i j : Fin (Module.finrank ℝ F)) :
    chartGramOnE (I := 𝓘(ℝ, F)) (opensFlatMetric F s) a i j
      = fun _ => (inner ℝ ((Module.finBasis ℝ F) i) ((Module.finBasis ℝ F) j) : ℝ) := by
  funext y
  rw [chartGramOnE_def, Tensor.chartGramMatrix_apply, chartBasisVecFiber_opens,
    chartBasisVecFiber_opens]
  rfl

/-- **Math.** **The flat metric on an open subset is flat**: all its Christoffel
symbols vanish, `Γᵏ_{ij} ≡ 0`.  Indeed the Christoffel symbols are built from
first partial derivatives of the Gram coefficients, and those coefficients are
constant (`chartGramOnE_opensFlatMetric`).  This is the coefficient computation
behind Petersen's Example 5.2.7 (the geodesics of `ℝ² − {0}` are the straight
lines it contains). -/
theorem chartChristoffel_opensFlatMetric (s : Opens F) (a : s)
    (i j k : Fin (Module.finrank ℝ F)) (y : F) :
    chartChristoffel (I := 𝓘(ℝ, F)) (opensFlatMetric F s) a i j k y = 0 := by
  rw [chartChristoffel_def]
  have hzero : ∀ (m n : Fin (Module.finrank ℝ F)) (p : Fin (Module.finrank ℝ F)),
      partialDeriv (E := F) p (chartGramOnE (I := 𝓘(ℝ, F)) (opensFlatMetric F s) a m n) y = 0 := by
    intro m n p
    rw [partialDeriv, chartGramOnE_opensFlatMetric]
    simp
  simp [hzero]

end PetersenLib
