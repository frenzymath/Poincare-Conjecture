import Topping.Riemannian.StarProduct
import Topping.Riemannian.Variation

/-!
# Variation of the curvature quantities

The remaining first-variation statements of Topping's Chapter 2 §3, expressed in
the vocabulary of `CovariantTensor` and `StarProduct`:

* `HasVectorFieldVariationOn` — `∂_t∇_XV = Π(X,V) + ∇_X(∂_tV)` for a
  time-dependent vector field, the product rule for the connection;
* `HasCovDerivVariationStarOn` — `∂_t∇A - ∇(∂_tA) = A*∇h`, again with the star
  product existentially quantified, since `A*∇h` names a class of tensors;
* `HasCurvatureOperatorVariationOn` — `∂_tR(X,Y)W = (∇_YΠ)(X,W) - (∇_XΠ)(Y,W)`,
  where `∇Π` is the covariant derivative of the vector-valued `Π`;
* `HasRiemannVariationOn` — the full component formula for `∂_t\Rm`;
* `HasDivergenceOneFormVariationOn` and `HasDivergenceGravitationVariationOn` —
  the variations of `δω` and `δG(T)`.

These are statements, not derivations: each says "the time derivative of *this*
quantity is *that* expression". Deriving them from `IsMetricVariationOn` plus
joint smoothness is the analytic work MorganTian Ch3 owns under the split of
conversations I-0441/I-0442.
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

/-! ### Variation of a covariant derivative of a vector field -/

/-- **Math.** `∂_t∇_XV = Π(X,V) + ∇_X(∂_tV)`: differentiating `∇_XV` in `t`
picks up the variation of the connection applied to `V`, plus the connection
applied to the variation of `V`. Stated after pairing against a tangent vector,
so that the two sides are real numbers and the derivative is an honest scalar
derivative. -/
def HasVectorFieldVariationOn (g : ℝ → RiemannianMetric I M)
    (Pi : ℝ → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M)
    (V dV : ℝ → SmoothVectorField I M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ (X : SmoothVectorField I M) (p : M) (z : TangentSpace I p),
    HasDerivWithinAt
      (fun s => (g t).metricInner p
        (((g s).leviCivitaConnection.cov X (V s)) p) z)
      ((g t).metricInner p (Pi t X (V t) p) z +
        (g t).metricInner p
          (((g t).leviCivitaConnection.cov X (dV t)) p) z) J t

/-! ### Variation of covariant derivatives of a tensor -/

/-- **Math.** `∂_t∇A - ∇(∂_tA) = A*∇h`: the failure of `∂_t` to commute with `∇`
is a star product of `A` with `∇h`, hence involves no derivative of `A` beyond
those already present. The star factor is existentially quantified, which is what
the notation `A*∇h` means. For a `t`-independent `A` take `dA = 0` and the second
term drops, recovering the first displayed formula of the remark. -/
def HasCovDerivVariationStarOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    {k : ℕ} (A dA : ℝ → CovTensorField I M k) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∃ C : CovTensorField I M (k + 1),
    IsStarProduct (g t) (A t)
        (covDeriv (g t).leviCivitaConnection (covTensorOfBilin (h t))) C ∧
      ∀ (Y : Fin (k + 1) → SmoothVectorField I M) (p : M),
        HasDerivWithinAt
          (fun s => covDeriv (g s).leviCivitaConnection (A s) Y p)
          (covDeriv (g t).leviCivitaConnection (dA t) Y p + C Y p) J t

/-! ### Variation of the curvature operator and the Riemann tensor -/

/-- **Math.** The covariant derivative of the connection variation `Π`, a
vector-valued `2`-tensor: `(∇_ZΠ)(X,W) = ∇_Z(Π(X,W)) - Π(∇_ZX,W) - Π(X,∇_ZW)`. -/
def covDerivConnectionVariation (g : RiemannianMetric I M)
    (Pi : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M)
    (Z X W : SmoothVectorField I M) : SmoothVectorField I M :=
  g.leviCivitaConnection.cov Z (Pi X W)
    - Pi (g.leviCivitaConnection.cov Z X) W
    - Pi X (g.leviCivitaConnection.cov Z W)

/-- **Math.** `∂_tR(X,Y)W = (∇_YΠ)(X,W) - (∇_XΠ)(Y,W)`: the variation of the
curvature operator is the antisymmetrized covariant derivative of the connection
variation. Paired against a tangent vector, with the metric held at time `t`. -/
def HasCurvatureOperatorVariationOn (g : ℝ → RiemannianMetric I M)
    (Pi : ℝ → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M)
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ (X Y W : SmoothVectorField I M) (p : M) (z : TangentSpace I p),
    HasDerivWithinAt
      (fun s => (g t).metricInner p (curvatureOperator (g s) X Y W p) z)
      ((g t).metricInner p
          (covDerivConnectionVariation (g t) (Pi t) Y X W p) z
        - (g t).metricInner p
          (covDerivConnectionVariation (g t) (Pi t) X Y W p) z) J t

/-- **Math.** Topping's component formula for the variation of the Riemann
tensor,
`∂_t\Rm(X,Y,W,Z) = ½[h(R(X,Y)W,Z) - h(R(X,Y)Z,W)]
+ ½[∇²_{Y,W}h(X,Z) - ∇²_{X,W}h(Y,Z) + ∇²_{X,Z}h(Y,W) - ∇²_{Y,Z}h(X,W)]`.

The four second-covariant-derivative terms use `secondCovDerivAlong` on the
`2`-tensor `h`, and the two `h`-of-curvature terms feed the curvature operator's
value into `h`. -/
def HasRiemannVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ) (J : Set ℝ) :
    Prop :=
  ∀ t ∈ J, ∀ (X Y W Z : SmoothVectorField I M) (p : M),
    HasDerivWithinAt
      (fun s => riemannCurvatureAt (g s) p (X p) (Y p) (W p) (Z p))
      ((1 / 2 : ℝ) *
          (h t p (curvatureOperator (g t) X Y W p) (Z p)
            - h t p (curvatureOperator (g t) X Y Z p) (W p))
        + (1 / 2 : ℝ) *
          (secondCovDerivAlong (g t).leviCivitaConnection Y W
              (covTensorOfBilin (h t)) (fun i => if i = 0 then X else Z) p
            - secondCovDerivAlong (g t).leviCivitaConnection X W
              (covTensorOfBilin (h t)) (fun i => if i = 0 then Y else Z) p
            + secondCovDerivAlong (g t).leviCivitaConnection X Z
              (covTensorOfBilin (h t)) (fun i => if i = 0 then Y else W) p
            - secondCovDerivAlong (g t).leviCivitaConnection Y Z
              (covTensorOfBilin (h t)) (fun i => if i = 0 then X else W) p))
      J t

/-! ### Variation of divergences -/

/-- **Math.** The pointwise metric contraction `⟨α,β⟩` of two covariant
`1`-tensor fields (one-forms) at `p`, i.e. `g^{ij}α_iβ_j`, computed over an
orthonormal basis. -/
def oneFormInnerAt (g : RiemannianMetric I M)
    (a b : CovTensorField I M 1) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, a (fun _ => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)) p *
    b (fun _ => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)) p

/-- **Math.** A covariant `1`-tensor field, evaluated at `p`, read as a function
on `T_pM`; this is the covector whose metric dual `ω^\#` the formulas below use.

Note this is only a *function*, not a linear functional: `CovTensorField I M 1` is
an arbitrary map on tuples of vector fields, and nothing in that type forces
`v ↦ ω(v)` to be linear. Genuine one-forms are linear, and `IsPointwiseLinear`
below names that property where it is needed — it is a hypothesis, not a
consequence of the type. -/
def oneFormCovec (_g : RiemannianMetric I M) (om : CovTensorField I M 1)
    (p : M) : TangentSpace I p → ℝ :=
  fun v => om (fun _ => MorganTianLib.extendVector p v) p

/-- **Math.** A covariant `1`-tensor field is *pointwise linear* at `p` when its
evaluation on a tangent vector is linear in that vector. This is what tensoriality
gives for an honest one-form, and it is exactly the hypothesis under which the
metric dual deserves its name. -/
def IsPointwiseLinear (g : RiemannianMetric I M) (om : CovTensorField I M 1)
    (p : M) : Prop :=
  (∀ v w : TangentSpace I p, oneFormCovec g om p (v + w)
      = oneFormCovec g om p v + oneFormCovec g om p w)
    ∧ ∀ (c : ℝ) (v : TangentSpace I p),
        oneFormCovec g om p (c • v) = c * oneFormCovec g om p v

/-- **Math.** The metric dual `ω^\#` of a one-form, defined by the orthonormal
basis expansion `ω^\# = Σᵢ ω(eᵢ)eᵢ`. Its characterizing property
`⟨ω^\#,v⟩ = ω(v)` holds under pointwise linearity — see
`metricInner_oneFormSharp`, which is where that hypothesis is discharged. -/
def oneFormSharp (g : RiemannianMetric I M) (om : CovTensorField I M 1) (p : M) :
    TangentSpace I p :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, oneFormCovec g om p (stdOrthonormalBasis ℝ (TangentSpace I p) i) •
    (stdOrthonormalBasis ℝ (TangentSpace I p) i : TangentSpace I p)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** **The metric dual really is the metric dual:**
`⟨ω^\#,v⟩ = ω(v)` for every tangent vector, given pointwise linearity of `ω`.

Expanding `v` in the orthonormal basis and using linearity on both sides reduces
this to the orthonormal expansion `Σᵢ⟨eᵢ,v⟩ω(eᵢ) = ω(v)`. Linearity is genuinely
needed and is genuinely a hypothesis: for a non-linear `CovTensorField I M 1` the
identity is false, since the left side is linear in `v` by construction and the
right side is not. -/
theorem metricInner_oneFormSharp (g : RiemannianMetric I M)
    (om : CovTensorField I M 1) (p : M) (hlin : IsPointwiseLinear g om p)
    (v : TangentSpace I p) :
    g.metricInner p (oneFormSharp g om p) v = oneFormCovec g om p v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  classical
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  -- Linearity over a finite sum of scalar multiples, from the two clauses.
  have hsum : ∀ (s : Finset (Fin (Module.finrank ℝ (TangentSpace I p))))
      (c : Fin (Module.finrank ℝ (TangentSpace I p)) → ℝ),
      oneFormCovec g om p (∑ i ∈ s, c i • (e i : TangentSpace I p))
        = ∑ i ∈ s, c i * oneFormCovec g om p (e i) := by
    intro s c
    induction s using Finset.induction_on with
    | empty =>
        have hz : oneFormCovec g om p (0 : TangentSpace I p) = 0 := by
          have h := hlin.2 0 (0 : TangentSpace I p)
          rw [zero_smul, zero_mul] at h
          exact h
        simpa using hz
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, hlin.1, hlin.2, ih, Finset.sum_insert ha]
  -- The left side: pull the sum and the scalars out of the metric.
  have hleft : g.metricInner p (oneFormSharp g om p) v
      = ∑ i, oneFormCovec g om p (e i) * inner ℝ (e i : TangentSpace I p) v := by
    rw [oneFormSharp, ← he]
    rw [show g.metricInner p
        (∑ i, oneFormCovec g om p (e i) • (e i : TangentSpace I p)) v
        = inner ℝ (∑ i, oneFormCovec g om p (e i) • (e i : TangentSpace I p)) v from
      rfl]
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
  -- The right side: expand `v` over the basis, then use linearity.
  rw [hleft]
  have hright : oneFormCovec g om p v
      = ∑ i, inner ℝ (e i : TangentSpace I p) v * oneFormCovec g om p (e i) := by
    conv_lhs => rw [show v
      = ∑ i, inner ℝ (e i : TangentSpace I p) v • (e i : TangentSpace I p) from
      (e.sum_repr' v).symm]
    rw [hsum]
  rw [hright]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Math.** The covariant derivative `∇ω` of a one-form, read as a pointwise
bilinear form so that it can be contracted against `h`. -/
def covDerivOneFormBilin (g : RiemannianMetric I M)
    (om : CovTensorField I M 1) (p : M) :
    TangentSpace I p → TangentSpace I p → ℝ :=
  fun v w => covDerivAlong g.leviCivitaConnection
    (MorganTianLib.extendVector p v) om
    (fun _ => MorganTianLib.extendVector p w) p

/-- **Math.** `∂_tδω = δ(∂_tω) + ⟨h,∇ω⟩ - ⟨δG(h),ω⟩` for a time-dependent
`1`-form `ω`, represented as a covariant `1`-tensor field. Note `δω` is a scalar
(rank `0`), `δG(h)` is a one-form, and the last term is the one-form
contraction. -/
def HasDivergenceOneFormVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (om dom : ℝ → CovTensorField I M 1) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ (Y : Fin 0 → SmoothVectorField I M) (p : M),
    HasDerivWithinAt
      (fun s => divergence (g s) (g s).leviCivitaConnection (om s) Y p)
      (divergence (g t) (g t).leviCivitaConnection (dom t) Y p
        + bilinInnerAt (g t) p (h t p) (covDerivOneFormBilin (g t) (om t) p)
        - oneFormInnerAt (g t)
            (divergence (g t) (g t).leviCivitaConnection
              (gravitationTensor (g t) (covTensorOfBilin (h t))))
            (om t) p) J t

/-- **Math.** `(∂_tδG(T))Z = -T((δG(h))^\#,Z) + ⟨h,∇T(·,·;Z) - ½∇_ZT⟩` for a
`t`-independent symmetric `2`-tensor `T`.

The first term feeds the metric dual of the one-form `δG(h)` into `T`; the second
contracts `h` against the bilinear form `(v,w) ↦ ∇T(v,w;Z) - ½(∇_ZT)(v,w)`, where
`∇T(v,w;Z)` is `∇T` with the derivative in the slot `v` and `Z` in the last tensor
slot -- Topping's `∇T(·,·;Z)`. -/
def HasDivergenceGravitationVariationOn (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (T : CovTensorField I M 2) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ (Z : SmoothVectorField I M) (p : M),
    HasDerivWithinAt
      (fun s => divergence (g s) (g s).leviCivitaConnection
        (gravitationTensor (g s) T) (fun _ => Z) p)
      (-T (fun i => if i = 0 then
              MorganTianLib.extendVector p
                (oneFormSharp (g t) (divergence (g t)
                  (g t).leviCivitaConnection
                  (gravitationTensor (g t) (covTensorOfBilin (h t)))) p)
            else Z) p
        + bilinInnerAt (g t) p (h t p)
          (fun v w =>
            covDerivAlong (g t).leviCivitaConnection
                (MorganTianLib.extendVector p v) T
                (fun i => if i = 0 then MorganTianLib.extendVector p w else Z) p
              - (1 / 2 : ℝ) * covDerivAlong (g t).leviCivitaConnection Z T
                (fun i => MorganTianLib.extendVector p (if i = 0 then v else w))
                p)) J t

end Topping

end
