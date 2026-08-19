import MorganTianLib.Ch03.RicciFlow.MetricVariation
import MorganTianLib.Ch03.RicciFlow.MetricCoordinateVariation
import MorganTianLib.Ch01.MatrixCalculus
import Topping.RicciFlow.Basic
import Topping.Riemannian.CovariantTensor
import Topping.Riemannian.Einstein

/-!
# Deformation of geometric quantities

Topping's Chapter 2 §3 differentiates the Riemannian invariants of a smooth
family of metrics `g_t` in the direction `h := ∂g_t/∂t`. This module fixes the
predicates that say "`h` is the time derivative of the family" and "`Π` is the
time derivative of the Levi-Civita connection", and proves the formulas that
follow from those definitions by algebra rather than by analysis:

* `IsMetricVariationOn g h J` — `h` is `∂_tg` on `J`, as a pointwise bilinear
  form on each tangent space, stated with a within-derivative so that closed and
  half-open time intervals both work;
* `variation_levi_civita` — the Koszul-type formula
  `⟨Π(X,Y),Z⟩ = ½[(∇_Yh)(X,Z) + (∇_Xh)(Y,Z) - (∇_Zh)(X,Y)]`, stated as the
  characterization of `Π` (`IsConnectionVariation`) and shown to determine `Π`
  uniquely, which is the content of Topping's proposition;
* `variation_trace` — `∂_t(tr α) = -⟨h,α⟩ + tr(∂_tα)`, the formula that makes
  every later trace computation possible: the metric used by the trace is itself
  moving, and that is where the `-⟨h,α⟩` comes from.

The analytic input (existence of `Π`, smoothness of the family) belongs to
MorganTian's Ricci-flow core by the ownership split; here the statements are
conditional on that input, which is how the book's §3 reads: it computes
derivatives assuming the family is smooth.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### The variation of a family of metrics -/

/-- **Math.** `h` is the time derivative `∂g_t/∂t` of the family `g` on `J`:
for every time in `J` and every pair of tangent vectors, `h t` computes the
derivative of `t ↦ g_t(x,y)`. Tangent vectors are held fixed, which is legitimate
because the tangent spaces do not move with `t`.

This is `MorganTianLib.IsMetricVariationOn`, not a second copy of it: the notion
belongs to the lower layer that owns the Ricci-flow core (conversations
I-0442/I-0495), and Topping's chapter 2 consumes it. The alias keeps the name
Topping's blueprint refers to while there is exactly one definition. -/
abbrev IsMetricVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ) (J : Set ℝ) :
    Prop :=
  MorganTianLib.IsMetricVariationOn g h J

/-- **Math.** Under Ricci flow the variation of the metric is `-2Ric`: the flow
equation says exactly that `h = -2Ric(g)` is a metric variation. -/
theorem isMetricVariationOn_of_isRicciFlowOn {g : ℝ → RiemannianMetric I M}
    {J : Set ℝ} (hflow : Topping.IsRicciFlowOn g J) :
    IsMetricVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y) J :=
  fun t ht p x y => hflow t ht p x y

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The variation of a family of metrics is unique where it exists:
two variations of the same family agree at every time of a set on which the
derivative is determined. Proved in the lower layer. -/
theorem isMetricVariationOn_unique {g : ℝ → RiemannianMetric I M}
    {h h' : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ} {J : Set ℝ}
    (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hh : IsMetricVariationOn g h J) (hh' : IsMetricVariationOn g h' J) :
    ∀ t ∈ J, ∀ (p : M) (x y : TangentSpace I p), h t p x y = h' t p x y :=
  MorganTianLib.isMetricVariationOn_unique hJ hh hh'

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A metric variation is symmetric, being the derivative of a family
of symmetric forms. Proved in the lower layer. -/
theorem isMetricVariationOn_symm {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ} {J : Set ℝ}
    (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hh : IsMetricVariationOn g h J) :
    ∀ t ∈ J, ∀ (p : M) (x y : TangentSpace I p), h t p x y = h t p y x :=
  MorganTianLib.isMetricVariationOn_symm hJ hh

/-! ### The variation of the Levi-Civita connection -/

/-- **Math.** `Pi` is the variation `∂_t(∇_XY)` of the Levi-Civita connection of
the family in the direction `h`, characterized by Topping's Koszul-type formula
`⟨Π(X,Y),Z⟩ = ½[(∇_Yh)(X,Z) + (∇_Xh)(Y,Z) - (∇_Zh)(X,Y)]`.

The three covariant derivatives are taken with the metric at time `t`, and `h t`
is regarded as a covariant `2`-tensor field through `covTensorOfBilin`. -/
def covTensorOfBilin
    (b : ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ) :
    CovTensorField I M 2 :=
  fun Y p => b p (Y 0 p) (Y 1 p)

/-- **Math.** Topping's characterization of the connection variation `Π`. -/
def IsConnectionVariation (g : RiemannianMetric I M)
    (h : ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (Pi : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M) : Prop :=
  ∀ (X Y Z : SmoothVectorField I M) (p : M),
    g.metricInner p (Pi X Y p) (Z p) =
      (1 / 2 : ℝ) *
        (covDerivAlong g.leviCivitaConnection Y (covTensorOfBilin h)
            (fun i => if i = 0 then X else Z) p
          + covDerivAlong g.leviCivitaConnection X (covTensorOfBilin h)
            (fun i => if i = 0 then Y else Z) p
          - covDerivAlong g.leviCivitaConnection Z (covTensorOfBilin h)
            (fun i => if i = 0 then X else Y) p)

omit [I.Boundaryless] in
/-- **Math.** The connection variation is uniquely determined by Topping's
formula: two vector fields with the same inner product against every `Z` are
equal, by nondegeneracy of the metric. This is the substance of the proposition
-- the formula does not merely constrain `Π`, it defines it. -/
theorem isConnectionVariation_unique (g : RiemannianMetric I M)
    {h : ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {Pi Pi' : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M}
    (hPi : IsConnectionVariation g h Pi)
    (hPi' : IsConnectionVariation g h Pi') :
    ∀ (X Y : SmoothVectorField I M) (p : M), Pi X Y p = Pi' X Y p := by
  intro X Y p
  refine (g.metricInner_eq_iff_eq p _ _).mp ?_
  intro z
  obtain ⟨Z, hZ⟩ := Riemannian.exists_smoothVectorField_eq p z
  rw [← hZ, hPi X Y Z p, hPi' X Y Z p]

/-! ### The variation of a trace

Topping's `∂_t(tr α) = -⟨h,α⟩ + tr(∂_tα)`. The `-⟨h,α⟩` term is the whole point:
the trace is taken with the metric, and the metric is moving. In an orthonormal
frame for `g_t` the trace of a `2`-tensor `α` is `Σᵢ α(eᵢ,eᵢ)`, but the frame is
only orthonormal at the one time `t`; differentiating the metric-dependence of
the frame produces exactly `-⟨h,α⟩`. -/

/-- **Math.** The pointwise inner product `⟨h,α⟩` of two symmetric `2`-tensors at
`p`, i.e. the full metric contraction `g^{ik}g^{jl}h_{ij}α_{kl}`, computed in an
orthonormal basis. -/
def bilinInnerAt (g : RiemannianMetric I M) (p : M)
    (a b : TangentSpace I p → TangentSpace I p → ℝ) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, ∑ j, a (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
    b (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      (stdOrthonormalBasis ℝ (TangentSpace I p) j)

/-- **Math.** The metric trace of a pointwise bilinear form, `tr_g α = Σᵢ α(eᵢ,eᵢ)`
in a `g_p`-orthonormal basis. -/
def bilinTraceAt (g : RiemannianMetric I M) (p : M)
    (a : TangentSpace I p → TangentSpace I p → ℝ) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, a (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    (stdOrthonormalBasis ℝ (TangentSpace I p) i)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** `⟨h,g⟩ = tr h`: contracting a symmetric `2`-tensor against the
metric is the same as tracing it. This is the special case of the trace variation
that identifies the `-⟨h,α⟩` term when `α = g`. -/
theorem bilinInnerAt_metric (g : RiemannianMetric I M) (p : M)
    (a : TangentSpace I p → TangentSpace I p → ℝ) :
    bilinInnerAt g p a (fun v w => g.metricInner p v w) = bilinTraceAt g p a := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hite : ∀ i j, g.metricInner p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      (stdOrthonormalBasis ℝ (TangentSpace I p) j) = if i = j then 1 else 0 := by
    intro i j
    have h := orthonormal_iff_ite.mp
      (stdOrthonormalBasis ℝ (TangentSpace I p)).orthonormal i j
    exact h
  simp only [bilinInnerAt, bilinTraceAt, hite]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]

/-- **Math.** Topping's variation of a trace, `∂_t(tr α) = -⟨h,α⟩ + tr(∂_tα)`,
stated as a predicate on the family `α` and its derivative `da`: the derivative of
`t ↦ tr_{g_t}(α_t)` is `-⟨h,α⟩ + tr(∂_tα)`. -/
def HasTraceVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (a da : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ p : M,
    HasDerivWithinAt (fun s => bilinTraceAt (g s) p (a s p))
      (-bilinInnerAt (g t) p (h t p) (a t p) + bilinTraceAt (g t) p (da t p)) J t

/-! ### The variation of the volume form

`∂_t dV = ½(tr h) dV`. The volume density is `√det g` in a chart, so its
logarithmic derivative is `½ tr_g(∂_tg) = ½ tr h`; the statement below is the
logarithmic form, which is what the book's proof and every later use need. -/

/-- **Math.** The Riemannian volume density `sqrt(det(g_ij))` at `p`, computed
in the chart frame based at `alpha`.  The definition is used only when `p` lies
in the base set of that frame. -/
def chartVolumeDensityAt (g : RiemannianMetric I M) (alpha p : M) : ℝ :=
  Real.sqrt
    (Riemannian.Tensor.chartGramMatrix (I := I) g alpha p).det

/-- **Math.** The coordinate volume density at `p` in the distinguished chart
based at `p` itself. This is a pointwise chart representative of the volume form;
it is not the global Riemannian measure. -/
def selfChartVolumeDensityAt (g : RiemannianMetric I M) (p : M) : ℝ :=
  chartVolumeDensityAt g p p

/-- **Math.** The coordinate expression `g^{ij} h_ji` for the metric trace of
`h` in the chart frame based at `alpha`. -/
def chartBilinTraceAt (g : RiemannianMetric I M) (alpha p : M)
    (h : TangentSpace I p → TangentSpace I p → ℝ) : ℝ :=
  let H : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => h
      (Tensor.chartBasisVecFiber (I := I) alpha i p)
      (Tensor.chartBasisVecFiber (I := I) alpha j p)
  (Riemannian.Tensor.chartInvGramMatrix (I := I) g alpha p * H).trace

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Contracting a genuine bilinear form with the inverse chart Gram
matrix computes its intrinsic metric trace. The proof constructs the
metric-dual endomorphism and compares its matrices in the chart basis and in a
metric-orthonormal basis. -/
theorem chartBilinTraceAt_eq_bilinTraceAt
    (g : RiemannianMetric I M) (alpha p : M)
    (hp : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet)
    (β : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ) :
    chartBilinTraceAt g alpha p (fun x y => β x y) =
      bilinTraceAt g p (fun x y => β x y) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let φ : TangentSpace I p →ₗ[ℝ] (TangentSpace I p →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ)
      (E := TangentSpace I p) (F' := ℝ)).toLinearMap.comp β.flip
  let A : TangentSpace I p →ₗ[ℝ] TangentSpace I p :=
    (g.metricToDualEquiv p).symm.toLinearMap.comp φ
  let b := Riemannian.Tensor.chartBasisFamily (I := I) alpha hp
  let G := Riemannian.Tensor.chartGramMatrix (I := I) g alpha p
  let Hm : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => β (b i) (b j)
  have hA (x y : TangentSpace I p) :
      g.metricInner p (A x) y = β y x := by
    rw [← g.metricToDual_apply]
    have heq := (g.metricToDualEquiv p).apply_symm_apply (φ x)
    exact congrArg (fun f : TangentSpace I p →L[ℝ] ℝ => f y) heq
  have hGA : G * LinearMap.toMatrix b b A = Hm := by
    ext i j
    simp only [Matrix.mul_apply, G, Hm, LinearMap.toMatrix_apply,
      Riemannian.Tensor.chartGramMatrix_apply,
      ← Riemannian.Tensor.chartBasisFamily_apply (I := I) alpha hp]
    calc
      (∑ k, g.metricInner p (b i) (b k) * (b.repr (A (b j))) k) =
          g.metricInner p (b i)
            (∑ k, (b.repr (A (b j))) k • b k) := by
        change (∑ k, (g.inner p (b i)) (b k) * (b.repr (A (b j))) k) =
          (g.inner p (b i)) (∑ k, (b.repr (A (b j))) k • b k)
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [map_smul]
        simp only [smul_eq_mul]
        ring
      _ = g.metricInner p (b i) (A (b j)) := by rw [b.sum_repr]
      _ = g.metricInner p (A (b j)) (b i) := g.metricInner_comm _ _ _
      _ = β (b i) (b j) := hA _ _
  have hInvH :
      Riemannian.Tensor.chartInvGramMatrix (I := I) g alpha p * Hm =
        LinearMap.toMatrix b b A := by
    rw [← hGA, ← Matrix.mul_assoc]
    change (Riemannian.Tensor.chartInvGramMatrix (I := I) g alpha p *
      Riemannian.Tensor.chartGramMatrix (I := I) g alpha p) *
        LinearMap.toMatrix b b A = LinearMap.toMatrix b b A
    rw [Riemannian.Tensor.chartInvGramMatrix_mul_chartGramMatrix
      (I := I) g alpha hp, one_mul]
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have htrace :
      (LinearMap.trace ℝ (TangentSpace I p)) A =
        ∑ i, β (e i) (e i) := by
    calc
      (LinearMap.trace ℝ (TangentSpace I p)) A =
          ∑ i, g.metricInner p (e i) (A (e i)) := by
            rw [LinearMap.trace_eq_sum_inner A e]
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = ∑ i, g.metricInner p (A (e i)) (e i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact g.metricInner_comm _ _ _
      _ = ∑ i, β (e i) (e i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hA _ _
  calc
    chartBilinTraceAt g alpha p (fun x y => β x y) =
        (Riemannian.Tensor.chartInvGramMatrix (I := I) g alpha p * Hm).trace := by
      simp only [chartBilinTraceAt, Hm, b,
        Riemannian.Tensor.chartBasisFamily_apply (I := I) alpha hp]
    _ = (LinearMap.toMatrix b b A).trace := congrArg Matrix.trace hInvH
    _ = (LinearMap.trace ℝ (TangentSpace I p)) A :=
      (LinearMap.trace_eq_matrix_trace ℝ b A).symm
    _ = ∑ i, β (e i) (e i) := htrace
    _ = bilinTraceAt g p (fun x y => β x y) := by rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The genuine local producer for variation of the volume element:
if `h = partial_t g`, then in every fixed chart frame

`partial_t sqrt(det(g_ij)) = (1/2) tr_g(h) sqrt(det(g_ij))`.

The proof differentiates the full Gram matrix, applies Jacobi's determinant
formula, and then differentiates the square root. -/
theorem hasDerivWithinAt_chartVolumeDensityAt
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hh : IsMetricVariationOn g h J)
    {t : ℝ} (ht : t ∈ J) (alpha p : M)
    (hp : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet) :
    HasDerivWithinAt (fun s => chartVolumeDensityAt (g s) alpha p)
      ((1 / 2 : ℝ) * chartBilinTraceAt (g t) alpha p (h t p) *
        chartVolumeDensityAt (g t) alpha p) J t := by
  classical
  let G : ℝ → (Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ) :=
    fun s i j => (g s).metricInner p
      (Tensor.chartBasisVecFiber (I := I) alpha i p)
      (Tensor.chartBasisVecFiber (I := I) alpha j p)
  let H : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => h t p
      (Tensor.chartBasisVecFiber (I := I) alpha i p)
      (Tensor.chartBasisVecFiber (I := I) alpha j p)
  let HM : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => H i j
  have hG : HasDerivWithinAt G H J t := by
    simpa only [G, H, Riemannian.Tensor.chartGramMatrix_apply,
      ← RiemannianMetric.metricInner_apply] using
      (MorganTianLib.hasDerivWithinAt_chartGramMatrix hh ht alpha p)
  have hdet : HasDerivWithinAt (fun s => Matrix.det (G s))
      (MorganTianLib.detCMM.linearDeriv (G t) H) J t :=
    (MorganTianLib.hasFDerivAt_det (G t)).comp_hasDerivWithinAt t hG
  have hGramEq (s : ℝ) : (G s : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) =
      Riemannian.Tensor.chartGramMatrix (I := I) (g s) alpha p := by
    ext i j
    simp only [G, Riemannian.Tensor.chartGramMatrix_apply,
      ← RiemannianMetric.metricInner_apply]
  have hdetPos : 0 < Matrix.det (G t) := by
    rw [hGramEq t]
    exact Riemannian.Tensor.chartGramMatrix_det_pos (I := I) (g t) alpha hp
  have hunit : IsUnit (Matrix.det (G t)) :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hdetPos)
  have hjacobi : MorganTianLib.detCMM.linearDeriv (G t) H =
      Matrix.det (G t) * (((G t)⁻¹ : Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ) *
          HM).trace := by
    simpa only [HM, H, smul_eq_mul] using
      (MorganTianLib.detCMM_linearDeriv_eq_smul_trace
        (G t : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) HM hunit)
  have hsqrt :=
    (Real.hasDerivAt_sqrt (ne_of_gt hdetPos)).comp_hasDerivWithinAt t hdet
  have hcoeff :
      1 / (2 * Real.sqrt (Matrix.det (G t))) *
          MorganTianLib.detCMM.linearDeriv (G t) H =
        (1 / 2 : ℝ) * (((G t)⁻¹ : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) *
            HM).trace *
            Real.sqrt (Matrix.det (G t)) := by
    rw [hjacobi]
    let s := Real.sqrt (Matrix.det (G t))
    have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdetPos)
    have hsq : s * s = Matrix.det (G t) := Real.mul_self_sqrt hdetPos.le
    change 1 / (2 * s) *
        (Matrix.det (G t) * (((G t)⁻¹ : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) *
            HM).trace) =
      (1 / 2 : ℝ) * (((G t)⁻¹ : Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ) *
          HM).trace * s
    rw [← hsq]
    field_simp [hs]
  have hvolume (s : ℝ) : chartVolumeDensityAt (g s) alpha p =
      Real.sqrt (Matrix.det (G s)) := by
    rw [chartVolumeDensityAt, hGramEq s]
  have htrace : chartBilinTraceAt (g t) alpha p (h t p) =
      (((G t)⁻¹ : Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ) * HM).trace := by
    simp only [chartBilinTraceAt, HM, H,
      Riemannian.Tensor.chartInvGramMatrix, ← hGramEq t]
  simp only [hvolume, htrace]
  convert hsqrt.congr_deriv hcoeff using 1
  · rfl
  · rfl
  · funext s
    rfl

/-- **Math.** `∂_t dV = ½(tr h)dV`, in the logarithmic form appropriate to a
density: the derivative of the volume density `v t p` is `½(tr h)` times itself.
-/
def HasVolumeFormVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (v : ℝ → M → ℝ) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ p : M,
    HasDerivWithinAt (fun s => v s p)
      ((1 / 2 : ℝ) * bilinTraceAt (g t) p (h t p) * v t p) J t

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Genuine pointwise producer for variation of the volume density of
an arbitrary metric variation. Uniqueness of within-derivatives is exactly what
turns the pointwise derivative `h` into a bilinear form at every time in `J`. -/
theorem hasVolumeFormVariationOn_selfChart
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hJ : ∀ t ∈ J, UniqueDiffWithinAt ℝ J t)
    (hh : IsMetricVariationOn g h J) :
    HasVolumeFormVariationOn g h
      (fun t p => selfChartVolumeDensityAt (g t) p) J := by
  intro t ht p
  have hp : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [Riemannian.trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source (I := I)]
    exact mem_extChartAt_source p
  let β : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (h t p)
      (MorganTianLib.isMetricVariationOn_add_left hJ hh t ht p)
      (fun c x y => by
        simpa only [smul_eq_mul] using
          MorganTianLib.isMetricVariationOn_smul_left hJ hh t ht p c x y)
      (MorganTianLib.isMetricVariationOn_add_right hJ hh t ht p)
      (fun c x y => by
        simpa only [smul_eq_mul] using
          MorganTianLib.isMetricVariationOn_smul_right hJ hh t ht p c x y)
  have htrace :
      chartBilinTraceAt (g t) p p (h t p) =
        bilinTraceAt (g t) p (h t p) := by
    change chartBilinTraceAt (g t) p p (fun x y => β x y) =
      bilinTraceAt (g t) p (fun x y => β x y)
    exact chartBilinTraceAt_eq_bilinTraceAt (g t) p p hp β
  have hderiv := hasDerivWithinAt_chartVolumeDensityAt hh ht p p hp
  simpa only [selfChartVolumeDensityAt, htrace] using hderiv

/-- **Math.** Under Ricci flow the trace of the metric variation is `-2R`, so the
volume form evolves by `∂_tdV = -R\,dV`: the trace of `h = -2Ric` is `-2` times
the scalar curvature. -/
theorem bilinTraceAt_neg_two_ricci (g : RiemannianMetric I M) (p : M) :
    bilinTraceAt g p (fun x y => -2 * ricciTensorAt g p x y) =
      -2 * scalarCurvatureAt g p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [bilinTraceAt, ← Finset.mul_sum,
    scalarCurvatureAt_eq_trace g p,
    Riemannian.bilinTrace_eq_sum _ (stdOrthonormalBasis ℝ (TangentSpace I p))]

/-- **Math.** In the self-based chart, the coordinate contraction of `-2 Ric`
is its intrinsic metric trace. -/
theorem chartBilinTraceAt_neg_two_ricci_self
    (g : RiemannianMetric I M) (p : M) :
    chartBilinTraceAt g p p (fun x y => -2 * ricciTensorAt g p x y) =
      bilinTraceAt g p (fun x y => -2 * ricciTensorAt g p x y) := by
  have hp : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [Riemannian.trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source (I := I)]
    exact mem_extChartAt_source p
  change chartBilinTraceAt g p p
      (fun x y => (((-2 : ℝ) • ricciTensorAt g p) x) y) =
    bilinTraceAt g p
      (fun x y => (((-2 : ℝ) • ricciTensorAt g p) x) y)
  exact chartBilinTraceAt_eq_bilinTraceAt g p p hp
    ((-2 : ℝ) • ricciTensorAt g p)

/-- **Math.** Unconditional Ricci-flow producer for pointwise volume-form
variation in the self-based chart. Unlike the generic producer, this needs no
uniqueness hypothesis on `J`, because `-2 Ric` is already a genuine bilinear
form rather than one reconstructed from within-derivatives. -/
theorem hasVolumeFormVariationOn_selfChart_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) :
    HasVolumeFormVariationOn g
      (fun t p x y => -2 * ricciTensorAt (g t) p x y)
      (fun t p => selfChartVolumeDensityAt (g t) p) J := by
  intro t ht p
  have hp : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [Riemannian.trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source (I := I)]
    exact mem_extChartAt_source p
  have hderiv := hasDerivWithinAt_chartVolumeDensityAt
    (isMetricVariationOn_of_isRicciFlowOn hflow) ht p p hp
  simpa only [selfChartVolumeDensityAt,
    chartBilinTraceAt_neg_two_ricci_self] using hderiv

/-- **Math.** The self-chart volume density under Ricci flow satisfies the
pointwise evolution equation `∂ₜρ = -R ρ`. -/
theorem hasDerivWithinAt_selfChartVolumeDensityAt_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) {t : ℝ} (ht : t ∈ J) (p : M) :
    HasDerivWithinAt (fun s => selfChartVolumeDensityAt (g s) p)
      (-scalarCurvatureAt (g t) p * selfChartVolumeDensityAt (g t) p) J t := by
  have hv := hasVolumeFormVariationOn_selfChart_of_isRicciFlowOn hflow t ht p
  rw [bilinTraceAt_neg_two_ricci] at hv
  convert hv using 1
  ring

#print axioms Topping.hasDerivWithinAt_chartVolumeDensityAt
#print axioms Topping.hasVolumeFormVariationOn_selfChart
#print axioms Topping.hasVolumeFormVariationOn_selfChart_of_isRicciFlowOn
#print axioms Topping.hasDerivWithinAt_selfChartVolumeDensityAt_of_isRicciFlowOn

end Topping

end
