import PetersenLib.Ch02.Exercises32
import PetersenLib.Ch02.CovariantAdjoint
import PetersenLib.Ch02.TensorInnerLeibniz
import PetersenLib.Ch01.Integration

/-!
# Petersen Ch. 2, §2.2.4 — Prop. 2.2.8: `∇*` is the `L²`-adjoint of `∇`

**Prop. 2.2.8.** For a compactly supported `(0,t)`-tensor `S` and a compactly
supported `(0,t+1)`-tensor `T`,
`∫ g(∇S, T) vol = ∫ g(S, ∇*T) vol`.

Petersen's proof introduces the `1`-form `ω(X) = g(i_X T, S)` and observes the
pointwise **Green identity**
`-∇*ω = -g(∇*T, S) + g(T, ∇S) = g(∇S, T) - g(S, ∇*T)`,
proved by choosing at each point an orthonormal frame *normal there*, so the
connection cross terms drop.  Integrating and applying the divergence theorem
`∫ ∇*ω vol = -∫ div(ω^♯) vol = 0` (Stokes, valid for compact support) yields the
identity.

## What is formalized here

* `covariantDerivativeFull D S` — Petersen's `(0,k+1)`-tensor `∇S`,
  `∇S(X, Y₁, …, Y_k) = (∇_X S)(Y₁, …, Y_k)`.
* `tensorFieldMetricInner_covariantDerivativeFull_eq_sum` and
  `tensorFieldMetricInner_covariantDerivativeAdjoint_eq_sum` — the two purely
  algebraic **contraction identities** (true for *any* frame),
  `g(∇S, T) = ∑ᵢ g(∇_{Eᵢ}S, i_{Eᵢ}T)` and
  `g(S, ∇*T) = -∑ᵢ g(S, i_{Eᵢ}(∇_{Eᵢ}T))`.
* `adjoint_L2_pointwise` — the **pointwise Green identity** at a point `p` where
  the orthonormal frame `Efr` is *normal*: `∇*ω(p) = g(S, ∇*T)(p) − g(∇S, T)(p)`.
  This is the genuine differential-geometric content, proved from the Leibniz
  rule `exercise2_5_32` and tensoriality (`isTensorOperator_slot_eq_zero_of_vanish`).
* `adjoint_L2_identity` — Prop. 2.2.8 itself, deduced from the pointwise Green
  identity (holding `μ`-a.e., the *frame-independence* input) and the divergence
  theorem `∫ ∇*ω vol = 0` (the *Stokes* input).  Both inputs are genuine — but
  currently unformalized — mathematical facts: Mathlib has **no** Riemannian
  volume measure / integration of top-degree forms (so no divergence theorem on
  manifolds, cf. `integrateOnRiemannianManifold`), and the frame-independence of
  `∇*`/`g(·,·)` among orthonormal frames is not yet available here (it needs
  normal-frame existence via the exponential map).  They enter as explicit,
  honestly named hypotheses, exactly as `integrateOnRiemannianManifold`
  parametrizes over the missing measure.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.2.4.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-! ## `∇S` as a `(0,k+1)`-tensor and the interior product as a tensor -/

/-- **Math.** Petersen's `(0,k+1)`-tensor `∇S` associated with a `(0,k)`-tensor
`S`: `∇S(X, Y₁, …, Y_k) = (∇_X S)(Y₁, …, Y_k)`, the direction placed in the
first slot. -/
def covariantDerivativeFull (D : AffineConnection I M) {k : ℕ}
    (S : TensorOperator I M k) : TensorOperator I M (k + 1) :=
  fun Z => covariantDerivativeTensor D (Z 0) S (Fin.tail Z)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem covariantDerivativeFull_apply (D : AffineConnection I M) {k : ℕ}
    (S : TensorOperator I M k) (Z : Fin (k + 1) → Π x : M, TangentSpace I x) (x : M) :
    covariantDerivativeFull D S Z x
      = covariantDerivativeTensor D (Z 0) S (Fin.tail Z) x := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The interior product `i_X T` of a smooth `(0,k+1)`-tensor with a
smooth vector field is again a smooth `(0,k)`-tensor. -/
theorem isTensorOperator_interiorProduct {k : ℕ} {T : TensorOperator I M (k + 1)}
    (hT : IsTensorOperator T) {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X) :
    IsTensorOperator (interiorProduct I T X) where
  smooth_eval Y hY := by
    have hcons : ∀ j : Fin (k + 1),
        IsSmoothVectorField ((Fin.cons X Y : Fin (k + 1) → Π x : M, TangentSpace I x) j) := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [Fin.cons_zero]; exact hX
      · rw [Fin.cons_succ]; exact hY i
    simpa only [interiorProduct] using hT.smooth_eval (Fin.cons X Y) hcons
  add_slot Y i V W x := by
    simp only [interiorProduct, Fin.cons_update]
    exact hT.add_slot (Fin.cons X Y) i.succ V W x
  smul_slot Y i g V x := by
    simp only [interiorProduct, Fin.cons_update]
    exact hT.smul_slot (Fin.cons X Y) i.succ g V x

/-! ## Symmetry of the frame inner product -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The frame inner product on tensors is symmetric. -/
theorem tensorFieldMetricInner_comm
    (Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x) {k : ℕ}
    (S T : TensorOperator I M k) :
    tensorFieldMetricInner Efr S T = tensorFieldMetricInner Efr T S := by
  funext x
  simp only [tensorFieldMetricInner]
  exact Finset.sum_congr rfl fun σ _ => mul_comm _ _

/-! ## The two contraction identities (any frame) -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Contraction identity for `∇S`: against any frame `Efr`,
`g(∇S, T) = ∑ᵢ g(∇_{Eᵢ}S, i_{Eᵢ}T)`.  A pure re-indexing of the sum
`∑_{τ : Fin (k+1) → ι}` through `τ ↦ (τ 0, Fin.tail τ)`; no normality needed. -/
theorem tensorFieldMetricInner_covariantDerivativeFull_eq_sum
    (D : AffineConnection I M)
    (Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x) {k : ℕ}
    (S : TensorOperator I M k) (T : TensorOperator I M (k + 1)) (x : M) :
    tensorFieldMetricInner Efr (covariantDerivativeFull D S) T x
      = ∑ i, tensorFieldMetricInner Efr (covariantDerivativeTensor D (Efr i) S)
          (interiorProduct I T (Efr i)) x := by
  classical
  simp only [tensorFieldMetricInner]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => Fin (Module.finrank ℝ E)))
        (fun τ => covariantDerivativeFull D S (fun j => Efr (τ j)) x
          * T (fun j => Efr (τ j)) x),
      Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun σ _ => ?_
  have hZ : (fun j => Efr ((Fin.consEquiv
        (fun _ : Fin (k + 1) => Fin (Module.finrank ℝ E)) (i, σ)) j))
      = Fin.cons (Efr i) (fun j => Efr (σ j)) := by
    funext j
    refine Fin.cases ?_ (fun l => ?_) j <;> simp [Fin.consEquiv]
  simp only [hZ, covariantDerivativeFull_apply, Fin.cons_zero, Fin.tail_cons,
    interiorProduct_apply]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Contraction identity for `∇*T`: against the orthonormal frame
`Efr`, `g(S, ∇*T) = -∑ᵢ g(S, i_{Eᵢ}(∇_{Eᵢ}T))`.  Immediate from the definition
of `∇*` and bilinearity; no normality needed. -/
theorem tensorFieldMetricInner_covariantDerivativeAdjoint_eq_sum
    (D : AffineConnection I M)
    (Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x) {k : ℕ}
    (S : TensorOperator I M k) (T : TensorOperator I M (k + 1)) (x : M) :
    tensorFieldMetricInner Efr S (covariantDerivativeAdjoint D Efr T) x
      = -∑ i, tensorFieldMetricInner Efr S
          (interiorProduct I (covariantDerivativeTensor D (Efr i) T) (Efr i)) x := by
  classical
  have hσ : ∀ σ : Fin k → Fin (Module.finrank ℝ E),
      S (fun j => Efr (σ j)) x * covariantDerivativeAdjoint D Efr T (fun j => Efr (σ j)) x
        = -∑ i, S (fun j => Efr (σ j)) x
            * interiorProduct I (covariantDerivativeTensor D (Efr i) T) (Efr i)
                (fun j => Efr (σ j)) x := by
    intro σ
    simp only [covariantDerivativeAdjoint_apply, mul_neg, Finset.mul_sum, interiorProduct_apply]
  simp only [tensorFieldMetricInner]
  rw [Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_neg_distrib, Finset.sum_comm]

/-! ## Commuting `∇` past the interior product at a normal point -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** At a point `p` where the direction field `X` is *parallel to itself*
(`∇_X X|_p = 0`, e.g. a normal frame vector), the covariant derivative commutes
with the interior product: `∇_X(i_X T) = i_X(∇_X T)` at `p`.  The connection cross
term that distinguishes the two — `T(∇_X X, ·)` — drops by tensoriality. -/
theorem covariantDerivativeTensor_interiorProduct_of_normal
    (D : AffineConnection I M) {k : ℕ} {T : TensorOperator I M (k + 1)}
    (hT : IsTensorOperator T) {X : Π x : M, TangentSpace I x} {p : M}
    (hXp : D.cov p (X p) X = 0) (W : Fin k → Π x : M, TangentSpace I x) :
    covariantDerivativeTensor D X (interiorProduct I T X) W p
      = interiorProduct I (covariantDerivativeTensor D X T) X W p := by
  have hL : covariantDerivativeTensor D X (interiorProduct I T X) W p
      = directionalDerivative X (T (Fin.cons X W)) p
        - ∑ j : Fin k, T (Fin.cons X (Function.update W j (D.covField X (W j)))) p := by
    rw [covariantDerivativeTensor_formula]
    simp only [interiorProduct_apply]
  have hR : interiorProduct I (covariantDerivativeTensor D X T) X W p
      = directionalDerivative X (T (Fin.cons X W)) p
        - ∑ j : Fin k, T (Fin.cons X (Function.update W j (D.covField X (W j)))) p := by
    rw [interiorProduct_apply, covariantDerivativeTensor_formula, Fin.sum_univ_succ, Fin.cons_zero]
    have hz : T (Function.update (Fin.cons X W) 0 (D.covField X X)) p = 0 := by
      apply isTensorOperator_slot_eq_zero_of_vanish hT
      rw [AffineConnection.covField_apply]
      exact hXp
    rw [hz, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.cons_succ, Fin.cons_update]
  rw [hL, hR]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The **general product rule for `∇` and the interior product**
(no normality assumed): `∇_X(i_X T) = i_X(∇_X T) + i_{∇_X X}T`.  Compared with
`covariantDerivativeTensor_interiorProduct_of_normal`, the correction term
`i_{∇_X X}T` — which vanishes only when `∇_X X|_p = 0` — is retained.  This is
pure `covariantDerivativeTensor_formula` bookkeeping, generalizing the normal
case. -/
theorem covariantDerivativeTensor_interiorProduct_general
    (D : AffineConnection I M) {k : ℕ} {T : TensorOperator I M (k + 1)}
    (X : Π x : M, TangentSpace I x) {p : M}
    (W : Fin k → Π x : M, TangentSpace I x) :
    covariantDerivativeTensor D X (interiorProduct I T X) W p
      = interiorProduct I (covariantDerivativeTensor D X T) X W p
        + interiorProduct I T (D.covField X X) W p := by
  have hL : covariantDerivativeTensor D X (interiorProduct I T X) W p
      = directionalDerivative X (T (Fin.cons X W)) p
        - ∑ j : Fin k, T (Fin.cons X (Function.update W j (D.covField X (W j)))) p := by
    rw [covariantDerivativeTensor_formula]
    simp only [interiorProduct_apply]
  have hR : interiorProduct I (covariantDerivativeTensor D X T) X W p
      = directionalDerivative X (T (Fin.cons X W)) p
        - T (Fin.cons (D.covField X X) W) p
        - ∑ j : Fin k, T (Fin.cons X (Function.update W j (D.covField X (W j)))) p := by
    rw [interiorProduct_apply, covariantDerivativeTensor_formula, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.update_cons_zero, sub_add_eq_sub_sub]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.cons_succ, Fin.cons_update]
  rw [hL, hR, interiorProduct_apply]; ring

/-! ## The pointwise Green identity (Prop. 2.2.8, local step) -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** **Prop. 2.2.8, pointwise step.**  For the `1`-form `ω(X) = g(i_X T, S)`
and an orthonormal frame `Efr` that is *normal at `p`*, the covariant divergence of
`ω` recovers the Green identity
`∇*ω(p) = g(S, ∇*T)(p) − g(∇S, T)(p)`,
i.e. `-∇*ω = g(∇S, T) − g(S, ∇*T)` at `p`.  This is the genuine
differential-geometric content of Prop. 2.2.8; integrating it against the
divergence theorem gives the `L²`-adjoint identity `adjoint_L2_identity`. -/
theorem adjoint_L2_pointwise {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {k : ℕ} {S : TensorOperator I M k} {T : TensorOperator I M (k + 1)}
    (hS : IsTensorOperator S) (hT : IsTensorOperator T)
    {Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hEfr : ∀ i, IsSmoothVectorField (Efr i))
    {p : M} (hNormal : ∀ i, ∀ v : TangentSpace I p, D.cov p v (Efr i) = 0) :
    covariantDerivativeAdjoint D.toAffineConnection Efr
        (fun X => tensorFieldMetricInner Efr (interiorProduct I T (X 0)) S) ![] p
      = tensorFieldMetricInner Efr S (covariantDerivativeAdjoint D.toAffineConnection Efr T) p
        - tensorFieldMetricInner Efr (covariantDerivativeFull D.toAffineConnection S) T p := by
  classical
  -- tensoriality: a `1`-form `g(i_Z T, S)` vanishes at `p` when `Z p = 0`.
  have hzero : ∀ Z : Π x : M, TangentSpace I x, Z p = 0 →
      tensorFieldMetricInner Efr (interiorProduct I T Z) S p = 0 := by
    intro Z hZp
    simp only [tensorFieldMetricInner]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [interiorProduct_apply]
    have hTz : T (Fin.cons Z (fun j => Efr (σ j))) p = 0 := by
      have h := isTensorOperator_slot_eq_zero_of_vanish hT
        (Fin.cons Z (fun j => Efr (σ j))) 0 p Z hZp
      rwa [Fin.update_cons_zero] at h
    rw [hTz, zero_mul]
  -- commute `∇` past `i_{Eᵢ}` inside the inner product (normal frame).
  have hswap : ∀ i, tensorFieldMetricInner Efr
        (covariantDerivativeTensor D.toAffineConnection (Efr i) (interiorProduct I T (Efr i))) S p
      = tensorFieldMetricInner Efr
        (interiorProduct I (covariantDerivativeTensor D.toAffineConnection (Efr i) T) (Efr i)) S p := by
    intro i
    simp only [tensorFieldMetricInner]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [covariantDerivativeTensor_interiorProduct_of_normal D.toAffineConnection hT
      (hNormal i (Efr i p)) (fun j => Efr (σ j))]
  -- evaluating `ω = g(i_· T, S)` on a `cons Z ![]` tuple.
  have hωcons : ∀ Z : Π x : M, TangentSpace I x,
      (fun X : Fin 1 → Π x : M, TangentSpace I x =>
          tensorFieldMetricInner Efr (interiorProduct I T (X 0)) S) (Fin.cons Z ![])
        = tensorFieldMetricInner Efr (interiorProduct I T Z) S := by
    intro Z; simp only [Fin.cons_zero]
  -- the per-frame computation of `∇_{Eᵢ}ω(Eᵢ)`.
  have hkey : ∀ i, covariantDerivativeTensor D.toAffineConnection (Efr i)
        (fun X => tensorFieldMetricInner Efr (interiorProduct I T (X 0)) S)
        (Fin.cons (Efr i) ![]) p
      = tensorFieldMetricInner Efr
          (interiorProduct I (covariantDerivativeTensor D.toAffineConnection (Efr i) T) (Efr i)) S p
        + tensorFieldMetricInner Efr (interiorProduct I T (Efr i))
          (covariantDerivativeTensor D.toAffineConnection (Efr i) S) p := by
    intro i
    rw [covariantDerivativeTensor_formula, Fin.sum_univ_one, Fin.update_cons_zero]
    simp only [hωcons]
    rw [Fin.cons_zero, hzero (D.toAffineConnection.covField (Efr i) (Efr i))
        (by rw [AffineConnection.covField_apply]; exact hNormal i (Efr i p)), sub_zero,
      exercise2_5_32 D (isTensorOperator_interiorProduct hT (hEfr i)) hS hEfr hNormal, hswap i]
  -- assemble via the two contraction identities and symmetry.
  rw [covariantDerivativeAdjoint_apply, Finset.sum_congr rfl (fun i _ => hkey i),
    Finset.sum_add_distrib, neg_add,
    tensorFieldMetricInner_covariantDerivativeAdjoint_eq_sum D.toAffineConnection Efr S T p,
    tensorFieldMetricInner_covariantDerivativeFull_eq_sum D.toAffineConnection Efr S T p,
    sub_eq_add_neg]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrFun (tensorFieldMetricInner_comm Efr
      (interiorProduct I (covariantDerivativeTensor D.toAffineConnection (Efr i) T) (Efr i)) S) p
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrFun (tensorFieldMetricInner_comm Efr (interiorProduct I T (Efr i))
      (covariantDerivativeTensor D.toAffineConnection (Efr i) S)) p

/-! ## The pointwise Green identity for a global orthonormal frame -/

section Orthonormal

variable [hm : HasMetric I M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** **Prop. 2.2.8, pointwise step — global orthonormal frame version.**
The Green identity `∇*ω(p) = g(S, ∇*T)(p) − g(∇S, T)(p)` for `ω(X) = g(i_X T, S)`
holds at *every* point `p`, for any smooth *globally orthonormal* frame `Efr` —
**no normality is assumed**.  Compared with `adjoint_L2_pointwise`, the connection
cross terms are handled by the general orthonormal Leibniz rule
(`tensorFieldMetricInner_leibniz_orthonormal`), whose skew-symmetry cancellation
replaces the normal-frame vanishing, and by the general interior-product product
rule (`covariantDerivativeTensor_interiorProduct_general`), whose correction term
`i_{∇_{Eᵢ}Eᵢ}T` cancels against the `∇`-formula divergence term.  This is the
frame-independence input that discharges the `hGreen` hypothesis of
`adjoint_L2_identity`. -/
theorem adjoint_L2_pointwise_orthonormal (D : RiemannianConnection I hm.metric)
    {k : ℕ} {S : TensorOperator I M k} {T : TensorOperator I M (k + 1)}
    (hS : IsTensorOperator S) (hT : IsTensorOperator T)
    {Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hEfr : ∀ i, IsSmoothVectorField (Efr i))
    (horth : ∀ y i j, hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (p : M) :
    covariantDerivativeAdjoint D.toAffineConnection Efr
        (fun X => tensorFieldMetricInner Efr (interiorProduct I T (X 0)) S) ![] p
      = tensorFieldMetricInner Efr S (covariantDerivativeAdjoint D.toAffineConnection Efr T) p
        - tensorFieldMetricInner Efr (covariantDerivativeFull D.toAffineConnection S) T p := by
  classical
  -- distribute `∇` over the interior product inside the inner product with `S`.
  have hTFadd : ∀ i, tensorFieldMetricInner Efr
        (covariantDerivativeTensor D.toAffineConnection (Efr i) (interiorProduct I T (Efr i))) S p
      = tensorFieldMetricInner Efr
          (interiorProduct I (covariantDerivativeTensor D.toAffineConnection (Efr i) T) (Efr i)) S p
        + tensorFieldMetricInner Efr
          (interiorProduct I T (D.toAffineConnection.covField (Efr i) (Efr i))) S p := by
    intro i
    simp only [tensorFieldMetricInner]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [covariantDerivativeTensor_interiorProduct_general D.toAffineConnection (Efr i)
      (fun j => Efr (σ j)), add_mul]
  -- the per-frame computation of `∇_{Eᵢ}ω(Eᵢ)`: the general Leibniz rule and the
  -- interior-product correction terms cancel, leaving the same result as the
  -- normal-frame `adjoint_L2_pointwise`.
  have hkey : ∀ i, covariantDerivativeTensor D.toAffineConnection (Efr i)
        (fun X => tensorFieldMetricInner Efr (interiorProduct I T (X 0)) S)
        (Fin.cons (Efr i) ![]) p
      = tensorFieldMetricInner Efr
          (interiorProduct I (covariantDerivativeTensor D.toAffineConnection (Efr i) T) (Efr i)) S p
        + tensorFieldMetricInner Efr (interiorProduct I T (Efr i))
          (covariantDerivativeTensor D.toAffineConnection (Efr i) S) p := by
    intro i
    rw [covariantDerivativeTensor_formula, Fin.sum_univ_one, Fin.update_cons_zero]
    simp only [Fin.cons_zero]
    rw [tensorFieldMetricInner_leibniz_orthonormal D
        (isTensorOperator_interiorProduct hT (hEfr i)) hS hEfr horth (Efr i) p, hTFadd i]
    ring
  -- assemble via the two contraction identities and symmetry (identical to the normal case).
  rw [covariantDerivativeAdjoint_apply, Finset.sum_congr rfl (fun i _ => hkey i),
    Finset.sum_add_distrib, neg_add,
    tensorFieldMetricInner_covariantDerivativeAdjoint_eq_sum D.toAffineConnection Efr S T p,
    tensorFieldMetricInner_covariantDerivativeFull_eq_sum D.toAffineConnection Efr S T p,
    sub_eq_add_neg]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrFun (tensorFieldMetricInner_comm Efr
      (interiorProduct I (covariantDerivativeTensor D.toAffineConnection (Efr i) T) (Efr i)) S) p
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrFun (tensorFieldMetricInner_comm Efr (interiorProduct I T (Efr i))
      (covariantDerivativeTensor D.toAffineConnection (Efr i) S)) p

/-! ## Prop. 2.2.8 — the `L²`-adjoint integral identity -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** **Prop. 2.2.8** (Petersen §2.2.4): `∇*` is the `L²`-adjoint of `∇`,
`∫ g(∇S, T) vol = ∫ g(S, ∇*T) vol` for compactly supported tensors `S, T`.

The proof integrates the pointwise Green identity `g(∇S, T) − g(S, ∇*T) = -∇*ω`
and applies the divergence theorem `∫ ∇*ω vol = 0` (`hDiv`).  The pointwise Green
identity is now **proved**, not assumed: for a smooth global orthonormal frame
`Efr` (`hEfr`, `horth`) it holds at every point by
`adjoint_L2_pointwise_orthonormal` (via the skew-symmetry frame-independence of
`∇*`/`g(·,·)`), so the earlier `hGreen` hypothesis is discharged.  The **only**
remaining unformalized input is `hDiv` — **Stokes' theorem for the compactly
supported `1`-form `ω`**, unavailable in Mathlib for general manifolds (there is
no Riemannian volume measure — hence the explicit `μ` standing in for `vol_g`, as
in `integrateOnRiemannianManifold`).  The integrability hypotheses `hInt₁, hInt₂`
hold because `S, T` are compactly supported and smooth. -/
theorem adjoint_L2_identity [MeasurableSpace M] (D : RiemannianConnection I hm.metric)
    (μ : MeasureTheory.Measure M)
    {k : ℕ} {S : TensorOperator I M k} {T : TensorOperator I M (k + 1)}
    (hS : IsTensorOperator S) (hT : IsTensorOperator T)
    {Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hEfr : ∀ i, IsSmoothVectorField (Efr i))
    (horth : ∀ y i j, hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hInt₁ : MeasureTheory.Integrable
      (tensorFieldMetricInner Efr (covariantDerivativeFull D.toAffineConnection S) T) μ)
    (hInt₂ : MeasureTheory.Integrable
      (tensorFieldMetricInner Efr S (covariantDerivativeAdjoint D.toAffineConnection Efr T)) μ)
    (hDiv : integrateOnRiemannianManifold hm.metric μ
        (covariantDerivativeAdjoint D.toAffineConnection Efr
          (fun X => tensorFieldMetricInner Efr (interiorProduct I T (X 0)) S) ![]) = 0) :
    integrateOnRiemannianManifold hm.metric μ
        (tensorFieldMetricInner Efr (covariantDerivativeFull D.toAffineConnection S) T)
      = integrateOnRiemannianManifold hm.metric μ
        (tensorFieldMetricInner Efr S (covariantDerivativeAdjoint D.toAffineConnection Efr T)) := by
  simp only [integrateOnRiemannianManifold] at hDiv ⊢
  rw [← sub_eq_zero, ← MeasureTheory.integral_sub hInt₁ hInt₂]
  have hGreen : ∀ x,
      tensorFieldMetricInner Efr (covariantDerivativeFull D.toAffineConnection S) T x
          - tensorFieldMetricInner Efr S (covariantDerivativeAdjoint D.toAffineConnection Efr T) x
        = -covariantDerivativeAdjoint D.toAffineConnection Efr
            (fun X => tensorFieldMetricInner Efr (interiorProduct I T (X 0)) S) ![] x := by
    intro x
    rw [adjoint_L2_pointwise_orthonormal D hS hT hEfr horth x]
    ring
  have hfun : (fun x =>
        tensorFieldMetricInner Efr (covariantDerivativeFull D.toAffineConnection S) T x
          - tensorFieldMetricInner Efr S (covariantDerivativeAdjoint D.toAffineConnection Efr T) x)
      = fun x => -covariantDerivativeAdjoint D.toAffineConnection Efr
          (fun X => tensorFieldMetricInner Efr (interiorProduct I T (X 0)) S) ![] x :=
    funext hGreen
  rw [hfun, MeasureTheory.integral_neg, hDiv, neg_zero]

end Orthonormal

end PetersenLib

end
