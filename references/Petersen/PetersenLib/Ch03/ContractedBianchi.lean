import PetersenLib.Ch03.RicciCovariantDerivative

/-!
# Petersen Ch. 3, §3.1.5 — Prop. 3.1.5: the contracted Bianchi identity

The divergence adjoint `∇*T` of a `(0,2)`-tensor field
(`divergenceAdjoint`, Petersen's notation
`(∇*T)(w) = −∑ᵢ (∇_{eᵢ}T)(eᵢ, w)` in a `g`-orthonormal basis), and

**Prop. 3.1.5 (the contracted Bianchi identity)**:
`d(tr Ric) = d(scal) = −2·∇*Ric`  (`contractedBianchiIdentity`).

## Proof

For the frame `Fᵢ = extendTangentVector p (eᵢ)` of a `g`-orthonormal basis of
`T_pM`, trace–derivative commutation (twice) and the second Bianchi identity
at the `(0,4)` level give

`d(scal)(w) = ∑ᵢ (∇_w Ric)(Fᵢ,Fᵢ) = ∑ᵢⱼ (∇_w R)(Fⱼ,Fᵢ,Fᵢ,Fⱼ)
 = 2·∑ᵢⱼ (∇_{Fᵢ}R)(Fⱼ,w,Fᵢ,Fⱼ) = 2·∑ᵢ (∇_{Fᵢ}Ric)(w,Fᵢ) = −2·(∇*Ric)(w)`,

using the antisymmetries of `∇R` and the symmetry of `∇Ric`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.5.
-/

open Bundle Set Function Finset Filter
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {g : RiemannianMetric I M}

/-! ## The divergence adjoint of a `(0,2)`-tensor -/

/-- The **covariant derivative of a `(0,2)`-tensor field** evaluated on
tangent vectors, through the canonical smooth extensions:
`(∇_v T)(x, y) = D_v(T(X̃, Ỹ)) − T(∇_v X̃, y) − T(x, ∇_v Ỹ)` where `X̃, Ỹ`
extend `x, y`. For a tensorial `T` (e.g. `Ric`) this is independent of the
extension. -/
def covariantDerivativeTwoTensorAt (D : AffineConnection I M)
    (T : Π q : M, TangentSpace I q → TangentSpace I q → ℝ) (p : M)
    (v x y : TangentSpace I p) : ℝ :=
  dirTangent (fun q => T q (extendTangentVector p x q)
      (extendTangentVector p y q)) v
    - T p (D.cov p v (⇑(extendTangentVector p x))) y
    - T p x (D.cov p v (⇑(extendTangentVector p y)))

/-- **Math.** The **divergence adjoint** `∇*T` of a `(0,2)`-tensor field
(Petersen §3.1.5): the `(0,1)`-tensor
`(∇*T)(w) = −∑ᵢ (∇_{eᵢ}T)(eᵢ, w)` in a `g`-orthonormal basis `e₁, …, eₙ` of
`T_pM` (for bilinear tensorial `T` the value does not depend on the choice of
orthonormal basis). -/
def divergenceAdjoint (D : RiemannianConnection I g)
    (T : Π q : M, TangentSpace I q → TangentSpace I q → ℝ) (p : M)
    (w : TangentSpace I p) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩;
  -∑ i, covariantDerivativeTwoTensorAt D.toAffineConnection T p
    (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    (stdOrthonormalBasis ℝ (TangentSpace I p) i) w

/-! ## The Bianchi contraction -/

/-- Summed second Bianchi identity: the full curvature-derivative contraction
reduces to (twice) the Ricci-type contraction. -/
private theorem sum_sum_cdc4_bianchi (D : RiemannianConnection I g)
    {F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hF : ∀ i, IsSmoothVectorField (F i))
    {W : Π x : M, TangentSpace I x} (hW : IsSmoothVectorField W) (p : M) :
    ∑ i, ∑ j, covariantDerivativeCurvatureFour D W (F j) (F i) (F i) (F j) p
      = 2 * ∑ i, ∑ j,
          covariantDerivativeCurvatureFour D (F i) (F j) W (F i) (F j) p := by
  classical
  -- sum of the second Bianchi identities over the frame
  have hsplit : ∀ f₁ f₂ f₃ : Fin (Module.finrank ℝ E)
        → Fin (Module.finrank ℝ E) → ℝ,
      (∑ i, ∑ j, (f₁ i j + f₂ i j + f₃ i j))
        = (∑ i, ∑ j, f₁ i j) + (∑ i, ∑ j, f₂ i j) + ∑ i, ∑ j, f₃ i j := by
    intro f₁ f₂ f₃
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hS0 : (∑ i, ∑ j, covariantDerivativeCurvatureFour D W (F j) (F i)
          (F i) (F j) p)
        + (∑ i, ∑ j, covariantDerivativeCurvatureFour D (F j) (F i) W
            (F i) (F j) p)
        + ∑ i, ∑ j, covariantDerivativeCurvatureFour D (F i) W (F j)
            (F i) (F j) p = 0 := by
    rw [← hsplit]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    exact covariantDerivativeCurvatureFour_secondBianchi D hW (hF j) (hF i)
      (hF i) (hF j) p
  -- middle term: relabel `i ↔ j`, then antisymmetry in the last pair
  have hT2 : ∑ i, ∑ j, covariantDerivativeCurvatureFour D (F j) (F i) W
        (F i) (F j) p
      = -∑ i, ∑ j, covariantDerivativeCurvatureFour D (F i) (F j) W
          (F i) (F j) p := by
    have hswap : ∑ i, ∑ j, covariantDerivativeCurvatureFour D (F j) (F i) W
          (F i) (F j) p
        = ∑ i, ∑ j, covariantDerivativeCurvatureFour D (F i) (F j) W
            (F j) (F i) p := Finset.sum_comm
    rw [hswap, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact covariantDerivativeCurvatureFour_antisymm₃₄ D (hF i) (hF j) hW
      (hF j) (hF i) p
  -- last term: antisymmetry in the first pair
  have hT3 : ∑ i, ∑ j, covariantDerivativeCurvatureFour D (F i) W (F j)
        (F i) (F j) p
      = -∑ i, ∑ j, covariantDerivativeCurvatureFour D (F i) (F j) W
          (F i) (F j) p := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact covariantDerivativeCurvatureFour_antisymm₁₂ D hW (hF j) (hF i)
      (hF j) p
  linarith [hS0, hT2, hT3]

/-! ## Prop. 3.1.5 — the contracted Bianchi identity -/

/-- **Math.** **Prop. 3.1.5 — the contracted Bianchi identity** (Petersen
§3.1.5): on any Riemannian manifold,
`d(tr Ric) = d(scal) = −2·∇*Ric`, evaluated here at `w ∈ T_pM`:
`d(scal)(w) = −2·(∇*Ric)(w)`. -/
theorem contractedBianchiIdentity (D : RiemannianConnection I g) (p : M)
    (w : TangentSpace I p) :
    dirTangent (scalarCurvature D) w
      = -2 * divergenceAdjoint D
          (fun q => RicciCurvature D.toAffineConnection q) p w := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  set F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x :=
    fun i => ⇑(extendTangentVector p (e i)) with hFdef
  have hF : ∀ i, IsSmoothVectorField (F i) :=
    fun i => (extendTangentVector p (e i)).smooth
  set W : Π x : M, TangentSpace I x := ⇑(extendTangentVector p w) with hWdef
  have hW : IsSmoothVectorField W := (extendTangentVector p w).smooth
  have hWp : W p = w := extendTangentVector_apply p w
  have hFp : ∀ i, F i p = e i := fun i => extendTangentVector_apply p (e i)
  have horth : ∀ i j, g.metricInner p (F i p) (F j p)
      = if i = j then 1 else 0 := by
    intro i j
    rw [hFp i, hFp j]
    exact orthonormal_iff_ite.mp e.orthonormal i j
  -- step 0: `d(scal)(w)` through the extension of `w`
  have h0 : dirTangent (scalarCurvature D) w
      = directionalDerivative W (scalarCurvature D) p := by
    rw [← hWp]
    rfl
  -- step 1: trace–derivative commutation for `scal`
  have h1 : directionalDerivative W (scalarCurvature D) p
      = ∑ i, covariantDerivativeRicci D W (F i) (F i) p :=
    directionalDerivative_scalarCurvature_eq_sum D hF W horth
  -- step 2: trace–derivative commutation for `Ric`, per frame index
  have h2 : ∑ i, covariantDerivativeRicci D W (F i) (F i) p
      = ∑ i, ∑ j, covariantDerivativeCurvatureFour D W (F j) (F i)
          (F i) (F j) p :=
    Finset.sum_congr rfl fun i _ =>
      covariantDerivativeRicci_eq_sum_covariantDerivativeCurvatureFour D hF
        hW (hF i) (hF i) horth
  -- step 3: summed second Bianchi identity
  have h3 := sum_sum_cdc4_bianchi D hF hW p
  -- step 4: back to `∇Ric`, direction `Fᵢ`
  have h4 : ∀ i, ∑ j, covariantDerivativeCurvatureFour D (F i) (F j) W
        (F i) (F j) p
      = covariantDerivativeRicci D (F i) W (F i) p :=
    fun i => (covariantDerivativeRicci_eq_sum_covariantDerivativeCurvatureFour
      D hF (hF i) hW (hF i) horth).symm
  -- step 5: symmetry of `∇Ric` and the divergence adjoint
  have h5 : ∀ i, covariantDerivativeRicci D (F i) W (F i) p
      = covariantDerivativeRicci D (F i) (F i) W p :=
    fun i => covariantDerivativeRicci_comm D (F i) W (F i) p
  have h6 : ∀ i, covariantDerivativeRicci D (F i) (F i) W p
      = covariantDerivativeTwoTensorAt D.toAffineConnection
          (fun q => RicciCurvature D.toAffineConnection q) p (e i) (e i) w := by
    intro i
    rw [covariantDerivativeRicci_apply, covariantDerivativeTwoTensorAt]
    have hdir : directionalDerivative (F i)
          (fun q => RicciCurvature D.toAffineConnection q (F i q) (W q)) p
        = dirTangent (fun q => RicciCurvature D.toAffineConnection q
            (F i q) (W q)) (e i) := by
      rw [← hFp i]
      rfl
    have hcov1 : D.toAffineConnection.covField (F i) (F i) p
        = D.cov p (e i) (F i) := by
      rw [← hFp i]
      rfl
    have hcov2 : D.toAffineConnection.covField (F i) W p
        = D.cov p (e i) W := by
      rw [← hFp i]
      rfl
    rw [hdir, hcov1, hcov2, hFp i, hWp]
  have h7 : divergenceAdjoint D
        (fun q => RicciCurvature D.toAffineConnection q) p w
      = -∑ i, covariantDerivativeRicci D (F i) (F i) W p := by
    rw [divergenceAdjoint]
    congr 1
    exact Finset.sum_congr rfl fun i _ => (h6 i).symm
  rw [h0, h1, h2, h3, Finset.sum_congr rfl fun i _ => h4 i, h7]
  have hcomm : ∑ i, covariantDerivativeRicci D (F i) W (F i) p
      = ∑ i, covariantDerivativeRicci D (F i) (F i) W p :=
    Finset.sum_congr rfl fun i _ => h5 i
  rw [hcomm]
  ring

end PetersenLib
