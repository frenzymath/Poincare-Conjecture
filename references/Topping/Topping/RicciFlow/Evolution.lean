import Topping.MaximumPrinciple.ScalarCurvature
import Topping.Riemannian.StarProduct
import Topping.Riemannian.Variation

/-!
# Evolution of curvature under Ricci flow

Topping's Chapter 2 §5 states the three evolution equations of Ricci flow:
`∂_t\Rm = Δ\Rm + \Rm*\Rm`, `∂_t\Ric = Δ_{\mathcal L}\Ric`, and
`∂_tR = ΔR + 2|\Ric|^2`. This module states them.

The curvature equation is stated with the star product as an existential --
`∃ C, IsStarProduct g \Rm \Rm C ∧ ∂_t\Rm = Δ\Rm + C` -- because that is what
`\Rm*\Rm` means: some universal quadratic contraction of the curvature, with no
derivatives. Committing to one contraction would be a stronger and different
claim than the book's.

For the scalar equation the predicate already exists: `HasScalarCurvatureEvolutionOn`
in `Topping.MaximumPrinciple.ScalarCurvature`, agreed with TOP.CH03 in inbox
conversation I-0442 as the single shared statement of `∂_tR = ΔR + 2|\Ric|^2`.
This module records that Topping's Chapter 2 node and the maximum-principle
hypothesis are the same proposition, and derives what follows from the flow
equation alone.

By the ownership split of conversations I-0441/I-0442, MorganTian Ch3 owns
short-time existence, joint space-time smoothness, and the analytic derivation of
these equations from the flow; the statements below are Topping's Chapter 2
formulations of them.
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

/-! ### The curvature tensor as a covariant tensor field -/

/-- **Math.** The Riemann tensor of `g` as a covariant `4`-tensor field, in the
representation the Laplacian and star product act on. -/
def riemannTensorField (g : RiemannianMetric I M) : CovTensorField I M 4 :=
  fun Y p => riemannCurvatureAt g p (Y 0 p) (Y 1 p) (Y 2 p) (Y 3 p)

/-- **Math.** The Ricci tensor of `g` as a covariant `2`-tensor field. -/
def ricciTensorField (g : RiemannianMetric I M) : CovTensorField I M 2 :=
  fun Y p => ricciTensorAt g p (Y 0 p) (Y 1 p)

/-! ### Curvature evolution -/

/-- **Math.** Topping's curvature evolution `∂_t\Rm = Δ\Rm + \Rm*\Rm` on the time
set `J`. The quadratic term is existentially quantified over the class of star
products, which is exactly what the shorthand `\Rm*\Rm` asserts: the correction to
the heat equation is *some* universal contraction of `\Rm ⊗ \Rm`, uniform in
`t`. -/
def HasCurvatureEvolutionOn (g : ℝ → RiemannianMetric I M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∃ C : CovTensorField I M 4,
    IsStarProduct (g t) (riemannTensorField (g t)) (riemannTensorField (g t)) C ∧
      ∀ (Y : Fin 4 → SmoothVectorField I M) (p : M),
        HasDerivWithinAt (fun s => riemannTensorField (g s) Y p)
          (roughLaplacian (g t) (g t).leviCivitaConnection
              (riemannTensorField (g t)) Y p + C Y p) J t

set_option linter.unusedSectionVars false in
/-- **Math.** The heat-type reading of curvature evolution: the curvature
satisfies a heat equation up to a zeroth-order quadratic term. This is Topping's
remark that the evolution "has heat-type form", and it is literally the same
statement -- the point of the remark is that no derivatives appear in the
correction, which is built into `IsStarProduct`. -/
theorem hasCurvatureEvolutionOn_iff_heat_type (g : ℝ → RiemannianMetric I M)
    (J : Set ℝ) :
    HasCurvatureEvolutionOn g J ↔
      ∀ t ∈ J, ∃ C : CovTensorField I M 4,
        IsStarProduct (g t) (riemannTensorField (g t))
            (riemannTensorField (g t)) C ∧
          ∀ (Y : Fin 4 → SmoothVectorField I M) (p : M),
            HasDerivWithinAt (fun s => riemannTensorField (g s) Y p)
              (roughLaplacian (g t) (g t).leviCivitaConnection
                  (riemannTensorField (g t)) Y p + C Y p) J t :=
  Iff.rfl

/-! ### Ricci evolution and the Lichnerowicz Laplacian -/

/-- **Math.** Topping's Lichnerowicz Laplacian of a symmetric `2`-tensor,
`(Δ_{\mathcal L}h)(X,W) = (Δh)(X,W) - h(X,\Ric(W)) - h(W,\Ric(X))
+ 2\tr h(R(X,\cdot)W,\cdot)`.

The Ricci terms are expressed through the Ricci endomorphism, which is how
`h(X,\Ric(W))` is read: `\Ric(W)` is the vector metrically dual to the covector
`\Ric(W,\cdot)`. The curvature term is the trace over an orthonormal basis. -/
def lichnerowiczLaplacian (g : RiemannianMetric I M)
    (h : CovTensorField I M 2) : CovTensorField I M 2 :=
  fun Y p =>
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    roughLaplacian g g.leviCivitaConnection h Y p
      - h (fun i => if i = 0 then Y 0 else
            MorganTianLib.extendVector p (ricciEndomorphismAt g p (Y 1 p))) p
      - h (fun i => if i = 0 then Y 1 else
            MorganTianLib.extendVector p (ricciEndomorphismAt g p (Y 0 p))) p
      + 2 * ∑ i, h (fun j => if j = 0 then
            MorganTianLib.extendVector p
              (curvatureOperator g (Y 0)
                (MorganTianLib.extendVector p
                  (stdOrthonormalBasis ℝ (TangentSpace I p) i)) (Y 1) p)
          else MorganTianLib.extendVector p
            (stdOrthonormalBasis ℝ (TangentSpace I p) i)) p

/-- **Math.** Topping's Ricci evolution `∂_t\Ric = Δ_{\mathcal L}(\Ric)` on `J`. -/
def HasRicciEvolutionOn (g : ℝ → RiemannianMetric I M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ (Y : Fin 2 → SmoothVectorField I M) (p : M),
    HasDerivWithinAt (fun s => ricciTensorField (g s) Y p)
      (lichnerowiczLaplacian (g t) (ricciTensorField (g t)) Y p) J t

/-! ### Scalar evolution -/

/-- **Math.** Topping's scalar-curvature evolution `∂_tR = ΔR + 2|\Ric|^2` is the
predicate `HasScalarCurvatureEvolutionOn` already used by the maximum-principle
work: one statement, shared, as agreed in conversation I-0442. -/
theorem hasScalarCurvatureEvolutionOn_iff (g : ℝ → RiemannianMetric I M)
    (J : Set ℝ) :
    HasScalarCurvatureEvolutionOn g J ↔
      ∀ t ∈ J, ∀ p : M,
        HasDerivWithinAt (fun s => scalarCurvatureAt (g s) p)
          (metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p +
            2 * ricciNormSqAt (g t) p) J t :=
  Iff.rfl

/-- **Math.** Under scalar evolution the scalar curvature is nondecreasing in
time wherever it is spatially harmonic: `∂_tR = ΔR + 2|\Ric|^2 ≥ 0` when
`ΔR = 0`, since `|\Ric|^2 ≥ 0` by the trace decomposition. -/
theorem derivWithin_scalarCurvature_nonneg_of_harmonic
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hev : HasScalarCurvatureEvolutionOn g J) {t : ℝ} (ht : t ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t) {p : M}
    (hharm : metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p = 0) :
    0 ≤ derivWithin (fun s => scalarCurvatureAt (g s) p) J t := by
  rw [(hev t ht p).derivWithin hJ, hharm, zero_add]
  have hsq := scalarCurvatureAt_sq_div_finrank_le_ricciNormSqAt (g t) p
  have hn : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    have : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast this
  have hnn : 0 ≤ scalarCurvatureAt (g t) p ^ 2 / (Module.finrank ℝ E : ℝ) :=
    div_nonneg (sq_nonneg _) hn.le
  linarith

end Topping

end
